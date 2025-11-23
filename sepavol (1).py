
"""
Sepaval Secure (ECC + Schnorr NIZK) - Prototype for contest / secure usage

Features:
- ECC (SECP256k1 by default) scalar derived from Knight's tour + salt via HKDF-SHA256
- Schnorr-style non-interactive ZK (Fiat-Shamir) with domain separation
- Compressed point encoding for network transport
- Judge server (Flask) with register/challenge/prove endpoints (demo)
- Replay protection via single-use nonces and TTL
- Defensive checks and parameter explanations

NOTES:
- For production consider using ed25519/ristretto and audited libs
- Always run behind TLS, use strong RNG, and consider HSM for private keys
"""

import os
import time
import hmac
import hashlib
import secrets
import threading
from typing import Dict, Tuple
from base64 import urlsafe_b64encode, urlsafe_b64decode

from ecdsa import curves, ellipticcurve

# -------------------------
# Config (tune for contest)
# -------------------------
CURVE = curves.SECP256k1  # changeable: curves.NIST256p or others
G = CURVE.generator
ORDER = CURVE.order
CURVE_NAME = CURVE.name

# Challenge TTL (seconds)
CHALLENGE_TTL = 60  # valid for 60 seconds by default
# Max lifetime of a registered public key if you want to expire
REGISTRATION_TTL = 7 * 24 * 3600  # one week (example)

# -------------------------
# Knight's tour (canonical)
# -------------------------
MOVES = [(2,1),(2,-1),(-2,1),(-2,-1),(1,2),(1,-2),(-1,2),(-1,-2)]
def onboard(x,y): return 0 <= x < 8 and 0 <= y < 8

def warnsdorff_tour(start=(0,0)):
    board = [[-1]*8 for _ in range(8)]
    sx, sy = start
    pos = (sx, sy)
    board[sy][sx] = 0
    path = [pos]
    for step in range(1, 64):
        cx, cy = pos
        nbrs = []
        for dx, dy in MOVES:
            nx, ny = cx+dx, cy+dy
            if onboard(nx, ny) and board[ny][nx] == -1:
                degree = 0
                for dx2, dy2 in MOVES:
                    x2, y2 = nx+dx2, ny+dy2
                    if onboard(x2, y2) and board[y2][x2] == -1:
                        degree += 1
                nbrs.append(((nx, ny), degree))
        if not nbrs:
            return None
        mn = min(deg for (_, deg) in nbrs)
        candidates = [pos for (pos, deg) in nbrs if deg == mn]
        pos = secrets.choice(candidates)
        board[pos[1]][pos[0]] = step
        path.append(pos)
    return path

def generate_knight_path(max_attempts=300):
    for _ in range(max_attempts):
        start = (secrets.randbelow(8), secrets.randbelow(8))
        p = warnsdorff_tour(start)
        if p:
            return p
    raise RuntimeError("Failed to generate knight's tour")

def path_to_bytes(path, salt: bytes = None) -> bytes:
    """
    Canonical encoding: each square -> single byte in [0..63] as y*8 + x.
    We then append salt (must be random per user) and pass to HKDF.
    """
    b = bytes([y*8 + x for (x,y) in path])
    if salt:
        return b + salt
    return b

# -------------------------
# HKDF-SHA256 (extract+expand)
# -------------------------
def hkdf_extract(salt: bytes, ikm: bytes) -> bytes:
    return hmac.new(salt if salt else b'\x00'*32, ikm, hashlib.sha256).digest()

def hkdf_expand(prk: bytes, info: bytes, length: int) -> bytes:
    # simple HKDF expand (assumes length <= 255*hash_len)
    hash_len = 32
    n = (length + hash_len - 1) // hash_len
    okm = b''
    t = b''
    for i in range(1, n+1):
        t = hmac.new(prk, t + info + bytes([i]), hashlib.sha256).digest()
        okm += t
    return okm[:length]

def derive_scalar_from_path(path_bytes: bytes, salt: bytes, order: int = ORDER) -> int:
    """
    Derive a scalar in [1 .. order-1] from path_bytes using HKDF-SHA256.
    - salt: per-user random salt (e.g., 16-32 bytes) — must be stored with registration
    - we produce 48 bytes of OKM and reduce mod order to get uniform scalar
    """
    # Use a strong salt; prk = HMAC(salt, IKM)
    prk = hkdf_extract(salt, path_bytes)
    info = b"sepaval-derive-v1|" + CURVE_NAME.encode()
    okm = hkdf_expand(prk, info, 48)  # 384 bits output
    x = int.from_bytes(okm, 'big') % order
    if x == 0:
        x = 1
    return x

# -------------------------
# Point encoding (compressed)
# -------------------------
def point_to_bytes(P: ellipticcurve.Point) -> bytes:
    # compressed: 0x02/0x03 + X
    x = P.x()
    y = P.y()
    size = (ORDER.bit_length() + 7) // 8
    xb = x.to_bytes(size, 'big')
    prefix = b'\x03' if (y & 1) else b'\x02'
    return prefix + xb

def bytes_to_point(b: bytes) -> ellipticcurve.Point:
    prefix = b[0]
    xb = b[1:]
    x = int.from_bytes(xb, 'big')
    # recover y from curve equation: y^2 = x^3 + ax + b (mod p)
    curve = CURVE.curve
    p = curve.p()
    a = curve.a()
    bcoef = curve.b()
    rhs = (pow(x, 3, p) + a * x + bcoef) % p
    # modular sqrt (Tonelli-Shanks)
    y = modular_sqrt(rhs, p)
    if y is None:
        raise ValueError("Invalid point bytes")
    # choose correct parity
    if (y & 1) != (prefix & 1):
        y = (-y) % p
    return ellipticcurve.Point(curve, x, y)

def modular_sqrt(a, p):
    """Tonelli-Shanks for p % 4 == 3 quick path, else general (works for prime p)."""
    # This implementation assumes p is prime (safe for our curve)
    if a == 0:
        return 0
    if p % 4 == 3:
        r = pow(a, (p + 1)//4, p)
        if (r * r) % p == a % p:
            return r
        return None
    # general Tonelli-Shanks (not optimized)
    # find Q and S such that p-1 = Q * 2^S with Q odd
    q = p - 1
    s = 0
    while q % 2 == 0:
        q //= 2
        s += 1
    # find z a quadratic non-residue
    z = 2
    while pow(z, (p-1)//2, p) != p-1:
        z += 1
    m = s
    c = pow(z, q, p)
    t = pow(a, q, p)
    r = pow(a, (q+1)//2, p)
    while True:
        if t % p == 1:
            return r
        # find smallest i (0 < i < m) such that t^{2^i} == 1
        i = 1
        tt = (t * t) % p
        while i < m and tt != 1:
            tt = (tt * tt) % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m = i
        c = (b * b) % p
        t = (t * c) % p
        r = (r * b) % p

# -------------------------
# Hash-to-int helper (domain-separated)
# -------------------------
def H_bytes_to_int(*parts, domain=b"sepaval-v1") -> int:
    h = hashlib.sha256()
    h.update(domain)
    for part in parts:
        if isinstance(part, bytes):
            h.update(b'\x00' + len(part).to_bytes(2,'big') + part)
        elif isinstance(part, str):
            h.update(b'\x01' + len(part).to_bytes(2,'big') + part.encode())
        elif isinstance(part, int):
            size = (ORDER.bit_length() + 7) // 8
            h.update(b'\x02' + size.to_bytes(2,'big') + part.to_bytes(size,'big'))
        elif isinstance(part, (ellipticcurve.Point, ellipticcurve.PointJacobi)):
            if isinstance(part, ellipticcurve.PointJacobi):
                part = ellipticcurve.Point(part.curve(), part.x(), part.y())
            h.update(point_to_bytes(part))
        else:
            raise TypeError(f"Unsupported type {type(part)} in H_bytes_to_int")
    return int.from_bytes(h.digest(), 'big')


# -------------------------
# Sepaval ECC class
# -------------------------
class SepavalSecure:
    def __init__(self, curve=CURVE):
        self.curve = curve
        self.G = curve.generator
        self.order = curve.order
        self.name = curve.name

    def keygen_from_path(self, path, salt: bytes) -> Dict:
        """
        Accepts:
         - path: list of coordinates
         - salt: random bytes (store this with registration)
        Returns dict with x (private scalar) and Y point (public)
        """
        path_bytes = path_to_bytes(path, salt)
        x = derive_scalar_from_path(path_bytes, salt, self.order)
        Y = x * self.G
        return {'x': x, 'Y': Y, 'salt': salt, 'path_bytes_len': len(path_bytes)}

    def prove(self, secret_struct: Dict, context: bytes) -> Dict:
        """
        Schnorr NIZK (Fiat-Shamir):
         - r random in [1..order-1]
         - T = r*G (point)
         - c = H(domain || curve_name || Y || T || context) mod order
         - s = (r + c * x) mod order
        Returns proof: {'T': bytes(compressed), 's': int, 'c': int}
        """
        x = secret_struct['x']
        Y = secret_struct['Y']
        # fresh r
        r = secrets.randbelow(self.order - 1) + 1
        T = r * self.G
        c = H_bytes_to_int(self.name, Y, T, context, domain=b"sepaval-schnorr-v1") % self.order
        s = (r + c * x) % self.order
        proof = {'T': point_to_bytes(T), 's': s, 'c': c}
        return proof

    def verify(self, Y_bytes: bytes, proof: Dict, context: bytes) -> bool:
        """
        Verify: s*G == T + c*Y
        Accepts compressed point bytes for Y and T.
        """
        try:
            Y = bytes_to_point(Y_bytes)
            T = bytes_to_point(proof['T'])
        except Exception:
            return False
        s = int(proof['s'])
        # recompute c
        c_calc = H_bytes_to_int(self.name, Y, T, context, domain=b"sepaval-schnorr-v1") % self.order
        if c_calc != int(proof.get('c')):
            return False
        left = s * self.G
        right = T + (c_calc * Y)
        return left == right

# -------------------------
# Judge server (Flask) - simple demo
# -------------------------
# NOTE: For production use a real DB, TLS, rate limiting, and process isolation.
try:
    from flask import Flask, request, jsonify
    app = Flask(__name__)
    sep = SepavalSecure()
    # in-memory stores (contest use only)
    REGISTRY: Dict[str, Dict] = {}   # team_id -> {'Y': bytes, 'salt': bytes, 'registered_at': ts}
    CHALLENGES: Dict[str, Dict] = {} # nonce -> {'team_id', 'context', 'expires_at'}

    @app.route('/register', methods=['POST'])
    def register():
        """
        POST JSON: { "team_id": "teamA", "Y": "<base64url>", "salt": "<base64url>" }
        stores public key Y and salt
        """
        j = request.get_json()
        team = j.get('team_id')
        y_b64 = j.get('Y')
        salt_b64 = j.get('salt')
        if not team or not y_b64 or not salt_b64:
            return jsonify({'ok': False, 'error': 'missing fields'}), 400
        try:
            Yb = urlsafe_b64decode(y_b64.encode())
            salt = urlsafe_b64decode(salt_b64.encode())
            # basic validation: try decode point
            _ = bytes_to_point(Yb)
        except Exception as e:
            return jsonify({'ok': False, 'error': 'invalid Y or salt', 'why': str(e)}), 400
        REGISTRY[team] = {'Y': Yb, 'salt': salt, 'registered_at': int(time.time())}
        return jsonify({'ok': True})

    @app.route('/challenge/<team>', methods=['GET'])
    def challenge(team):
        """
        Generate one-time context for team (nonce)
        returns: { "context": "<base64url>", "nonce": "<nonce>" }
        """
        if team not in REGISTRY:
            return jsonify({'ok': False, 'error': 'unknown team'}), 404
        nonce = urlsafe_b64encode(secrets.token_bytes(12)).decode()
        timestamp = int(time.time())
        context = f"sepaval|{team}|{timestamp}|{nonce}".encode()
        CHALLENGES[nonce] = {'team': team, 'context': context, 'expires_at': timestamp + CHALLENGE_TTL}
        return jsonify({'ok': True, 'context': urlsafe_b64encode(context).decode(), 'nonce': nonce, 'ttl': CHALLENGE_TTL})

    @app.route('/prove', methods=['POST'])
    def prove():
        """
        POST JSON: { "team_id": "teamA", "nonce": "<nonce>", "proof": { "T": "<b64>", "s": int, "c": int } }
        """
        j = request.get_json()
        team = j.get('team_id')
        nonce = j.get('nonce')
        proof = j.get('proof')
        if not team or not nonce or not proof:
            return jsonify({'ok': False, 'error': 'missing fields'}), 400
        chal = CHALLENGES.get(nonce)
        if not chal or chal['team'] != team:
            return jsonify({'ok': False, 'error': 'invalid or used nonce'}), 400
        if int(time.time()) > chal['expires_at']:
            # remove expired
            CHALLENGES.pop(nonce, None)
            return jsonify({'ok': False, 'error': 'nonce expired'}), 400
        # verify
        reg = REGISTRY.get(team)
        if not reg:
            return jsonify({'ok': False, 'error': 'team not registered'}), 400
        Yb = reg['Y']
        context = chal['context']
        ok = sep.verify(Yb, {'T': urlsafe_b64decode(proof['T'].encode()), 's': int(proof['s']), 'c': int(proof['c'])}, context)
        # consume nonce (single-use)
        CHALLENGES.pop(nonce, None)
        return jsonify({'ok': ok})

    # small housekeeping thread to clear expired registrations/challenges periodically
    def cleanup_loop():
        while True:
            now = int(time.time())
            for k in list(CHALLENGES.keys()):
                if CHALLENGES[k]['expires_at'] < now:
                    CHALLENGES.pop(k, None)
            for team in list(REGISTRY.keys()):
                if REGISTRY[team]['registered_at'] + REGISTRATION_TTL < now:
                    REGISTRY.pop(team, None)
            time.sleep(30)
    t = threading.Thread(target=cleanup_loop, daemon=True)
    t.start()

except Exception as e:
    # Flask not available; server won't run but core libs still usable
    app = None
    # print warning when running
    SERVER_IMPORT_ERROR = e

# -------------------------
# CLI demo helpers
# -------------------------
def demo_cli():
    """
    Quick local demo:
      - generate a knight path
      - choose salt
      - keygen -> produce Y (public)
      - register to local judge (if running)
      - request challenge and produce proof and verify locally
    """
    print("Sepaval secure demo (curve = {})".format(CURVE_NAME))
    path = generate_knight_path()
    salt = secrets.token_bytes(16)
    sep = SepavalSecure()
    secret = sep.keygen_from_path(path, salt)
    Yb = point_to_bytes(secret['Y'])
    print("Public key (compressed, base64):", urlsafe_b64encode(Yb).decode())
    # local proof
    context = b"local-demo|" + secrets.token_bytes(8)
    proof = sep.prove(secret, context)
    ok = sep.verify(Yb, proof, context)
    print("Proof valid locally?:", ok)
    # show sizes
    print("Scalar size (bits):", ORDER.bit_length(), "bytes:", (ORDER.bit_length()+7)//8)

if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "runserver":
        if app is None:
            print("Flask not installed or failed to initialize server:", SERVER_IMPORT_ERROR)
            sys.exit(1)
        # run in debug=False for contest; bind to 0.0.0.0 for access in LAN (use TLS proxy in production)
        app.run(host="0.0.0.0", port=5000, debug=False)
    else:
        demo_cli()
