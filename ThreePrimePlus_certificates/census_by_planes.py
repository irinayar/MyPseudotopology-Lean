"""Independent exhaustive census of the close triples of the explicit window by plane enumeration (no continued fractions).

Block k: N = 2^k <= n < 2N (so floor(log2 n) = k and W(n) = Wk = (1+k)^2 log 2).  A triple (n,m,l) with diameter <= Wk has
|m - alpha n|, |l - beta n| <= delta_k := 1.15 Wk / N <= 1   (diameter -> delta, see the proof of Theorem (b)).
Transference lemma (pigeonhole version, TPPTransfer.lean): there is a nonzero integer h with h.z = 0, ||h||_inf <= M := ceil(sqrt(3n)) <= H_k := ceil(sqrt(6N)) (n >= 5, so that m, l <= n); its primitive part has the same properties
and |h.v| <= 2 M delta_k / n <= eta_k := 2 H_k delta_k / N.
Step A: enumerate EXACTLY all nonzero h in Z^3 with ||h||_inf <= H_k, |h.v| <= eta_k (rank-3 lattice in Z^4, LLL + Fincke-Pohst, rational arithmetic).
Step B: for each primitive h (up to sign) enumerate EXACTLY the points z of the plane lattice h^perp ∩ Z^3 with Q(z) <= 3.0001, where
Q(z) = (z_0/(2N))^2 + ((z_1 - alpha z_0)/delta_k)^2 + ((z_2 - beta z_0)/delta_k)^2   (every triple of the block has Q < 3).
Each candidate with N <= n < 2N is tested exactly (diameter <= Wk, then "no other period of the chains of 2,3,5 in the closed interval").
Usage: census_by_planes.py KMIN KMAX [A]    (A = window factor: diameter <= A W(n); default 1.  Blocks where delta_k > 1 are scanned directly.)"""
import sys, math, time
from fractions import Fraction
from decimal import Decimal, getcontext
KMIN, KMAX = int(sys.argv[1]), int(sys.argv[2])
AF = int(sys.argv[3]) if len(sys.argv) > 3 else 1
getcontext().prec = 160
L = {2: Decimal(2).ln(), 3: Decimal(3).ln(), 5: Decimal(5).ln()}
alpha_d, beta_d = (L[2] / L[3]).sqrt(), (L[2] / L[5]).sqrt()
SC = 10 ** 100
alpha_q, beta_q = Fraction(int(alpha_d * SC), SC), Fraction(int(beta_d * SC), SC)
v_d = [Decimal(1), alpha_d, beta_d]

def dot(a, b): return sum(x * y for x, y in zip(a, b))
def lll(B, delta=Fraction(99, 100)):
    n = len(B); B = [list(r) for r in B]
    def gs():
        Bs, mu = [], [[Fraction(0)] * n for _ in range(n)]
        for i in range(n):
            w = [Fraction(x) for x in B[i]]
            for j in range(i):
                mu[i][j] = dot(B[i], Bs[j]) / dot(Bs[j], Bs[j])
                w = [a - mu[i][j] * b for a, b in zip(w, Bs[j])]
            Bs.append(w)
        return Bs, mu
    Bs, mu = gs(); k = 1
    while k < n:
        for j in range(k - 1, -1, -1):
            q = round(mu[k][j])
            if q:
                B[k] = [a - q * b for a, b in zip(B[k], B[j])]; Bs, mu = gs()
        if dot(Bs[k], Bs[k]) >= (delta - mu[k][k - 1] ** 2) * dot(Bs[k - 1], Bs[k - 1]): k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]; Bs, mu = gs(); k = max(k - 1, 1)
    return B, Bs, mu

def enum_short(B, Bs, mu, R2, limit=5000000):
    n = len(B); nb = [dot(Bs[i], Bs[i]) for i in range(n)]; out = []
    def rec(i, ks, rest):
        if len(out) > limit: raise RuntimeError("enumeration limit")
        if i < 0:
            out.append(list(ks)); return
        c = -sum(ks[j] * mu[j][i] for j in range(i + 1, n)) if i < n - 1 else Fraction(0)
        rad2 = rest / nb[i]
        r = math.isqrt(int(rad2)) + 1 if rad2 > 0 else 0
        for k in range(math.floor(c - r - 1), math.ceil(c + r + 1) + 1):
            t = (k - c) ** 2 * nb[i]
            if t <= rest:
                ks[i] = k; rec(i - 1, ks, rest - t)
        ks[i] = 0
    rec(n - 1, [0] * n, R2)
    return out

def step_A(H, eta):
    """all nonzero h with ||h||_inf <= H and |h.v| <= eta."""
    Ws = int(4 * H / eta) + 1
    r = [int(round(Decimal(Ws) * x)) for x in v_d]
    basis = [[1, 0, 0, r[0]], [0, 1, 0, r[1]], [0, 0, 1, r[2]]]
    B, Bs, mu = lll(basis)
    # |last| <= Ws*eta + 1.5 H  (rounding) ; |h|_2^2 <= 3 H^2
    R2 = Fraction(3 * H * H) + (Fraction(Ws) * Fraction(eta) + Fraction(3 * H, 2) + 1) ** 2
    vecs = enum_short(B, Bs, mu, R2)
    out = set()
    for ks in vecs:
        h = [sum(ks[i] * B[i][j] for i in range(3)) for j in range(3)]
        if h == [0, 0, 0]: continue
        if max(abs(x) for x in h) > H: continue
        if math.gcd(math.gcd(abs(h[0]), abs(h[1])), abs(h[2])) != 1: continue
        hv = abs(Decimal(h[0]) + Decimal(h[1]) * alpha_d + Decimal(h[2]) * beta_d)
        if hv <= Decimal(eta) * Decimal("1.0000001"):
            out.add(tuple(h) if tuple(h) > tuple(-x for x in h) else tuple(-x for x in h))
    return sorted(out), len(vecs)

def plane_basis(h):
    K = 10 ** 6 * max(abs(x) for x in h) * 10 ** 6
    B, Bs, mu = lll([[1, 0, 0, K * h[0]], [0, 1, 0, K * h[1]], [0, 0, 1, K * h[2]]])
    ker = [r[:3] for r in B if r[3] == 0]
    assert len(ker) == 2, "kernel basis"
    return ker

def step_B(h, N, delta_q):
    b1, b2 = plane_basis(h)
    inv2N = Fraction(1, 2 * N)
    def form(x, y):
        ux = x[1] - alpha_q * x[0]; uy = y[1] - alpha_q * y[0]
        wx = x[2] - beta_q * x[0]; wy = y[2] - beta_q * y[0]
        return x[0] * y[0] * inv2N * inv2N + (ux * uy + wx * wy) / (delta_q * delta_q)
    G11, G12, G22 = form(b1, b1), form(b1, b2), form(b2, b2)
    # Gauss reduction on the Gram matrix
    while True:
        if G11 > G22:
            b1, b2 = b2, b1; G11, G22 = G22, G11
        m = round(G12 / G11)
        if m == 0 and G11 <= G22: break
        b2 = [b2[i] - m * b1[i] for i in range(3)]
        G22 = G22 - 2 * m * G12 + m * m * G11
        G12 = G12 - m * G11
    R = Fraction(30001, 10000)
    # enumeration: z = i b1 + j b2, Q = G11 i^2 + 2 G12 i j + G22 j^2 <= R
    Dd = G22 - G12 * G12 / G11            # Q(b2*) > 0
    jmax = math.isqrt(int(R / Dd)) + 2
    pts = []
    for j in range(-jmax, jmax + 1):
        c = -G12 * j / G11
        rest = R - j * j * Dd
        if rest < 0: continue
        r = math.isqrt(int(rest / G11)) + 2
        for i in range(math.floor(c - r), math.ceil(c + r) + 1):
            z = [i * b1[t] + j * b2[t] for t in range(3)]
            if z == [0, 0, 0]: continue
            pts.append(z)
    return pts

def periods_in_interval(lo, hi):
    cnt = 0
    for p in (2, 3, 5):
        eps = Decimal(10) ** -60   # the three periods of the triple sit exactly at j^2 log p; tolerance for rounding of the square roots
        a = (lo / L[p]).sqrt() - eps; b = (hi / L[p]).sqrt() + eps
        cnt += int(b.to_integral_value(rounding="ROUND_FLOOR")) - int(a.to_integral_value(rounding="ROUND_CEILING")) + 1
    return cnt

def brute_block(N, Wk):
    out = []
    Wf = float(Wk)
    al, be = float(alpha_d), float(beta_d)
    l2, l3, l5 = float(L[2]), float(L[3]), float(L[5])
    for n in range(N, 2 * N):
        d = 1.2 * Wf / n + 2
        m0, q0 = al * n, be * n
        a = n * n * l2
        for m in range(max(1, int(m0 - d)), int(m0 + d) + 1):
            x = m * m * l3
            if abs(x - a) > Wf + 1e-3: continue
            for l in range(max(1, int(q0 - d)), int(q0 + d) + 1):
                y = l * l * l5
                lo, hi = min(a, x, y), max(a, x, y)
                if hi - lo <= Wf + 1e-3:
                    A_, B_, C_ = Decimal(n * n) * L[2], Decimal(m * m) * L[3], Decimal(l * l) * L[5]
                    lo_d, hi_d = min(A_, B_, C_), max(A_, B_, C_)
                    if hi_d - lo_d <= Wk:
                        out.append((n, m, l, periods_in_interval(lo_d, hi_d) == 3, float(hi_d - lo_d)))
    return out

results = {}
t0 = time.time()
for k in range(KMIN, KMAX + 1):
    N = 2 ** k
    Wk = Decimal(1 + k) ** 2 * L[2] * AF
    delta = Fraction(115, 100) * Fraction(Wk) / N
    delta_d = Decimal(delta.numerator) / Decimal(delta.denominator)
    if delta > 1:
        found = brute_block(N, Wk)
        results[k] = found
        print("k=%2d N=2^%d  [direct scan, delta_k > 1]  triples with diameter <= A W: %d  close triples: %s   [%.0fs]" % (k, k, len(found), [(f[0], f[1], f[2]) for f in found if f[3]], time.time() - t0)); sys.stdout.flush()
        continue
    H = math.isqrt(6 * N) + 2             # >= ceil(sqrt(6N)) >= ceil(sqrt(3n)) = M for n < 2N (pigeonhole lemma, formalized in TPPTransfer.lean)
    eta = Fraction(2 * H) * delta / N       # |h.v| <= 2 M delta / n <= 2 H delta_k / N
    eta_f = Decimal(eta.numerator) / Decimal(eta.denominator)
    hs, nv = step_A(H, eta_f)
    cands = set(); npts = 0
    for h in hs:
        for z in step_B(h, N, delta):
            npts += 1
            n, m, l = z
            if n < 0: n, m, l = -n, -m, -l
            if N <= n < 2 * N and m >= 1 and l >= 1:
                cands.add((n, m, l))
    found = []
    for (n, m, l) in sorted(cands):
        a, b, c = Decimal(n * n) * L[2], Decimal(m * m) * L[3], Decimal(l * l) * L[5]
        lo, hi = min(a, b, c), max(a, b, c)
        if hi - lo <= Wk:
            between = periods_in_interval(lo, hi)
            found.append((n, m, l, between == 3, float(hi - lo)))
    results[k] = found
    print("k=%2d N=2^%d  h-vectors: %5d (lattice vectors %6d)  plane points: %6d  triples with diameter <= W: %d  close triples: %s   [%.0fs]" % (k, k, len(hs), nv, npts, len(found), [(f[0], f[1], f[2]) for f in found if f[3]], time.time() - t0)); sys.stdout.flush()
allclose = sorted((f[0], f[1], f[2]) for k in results for f in results[k] if f[3])
print("\nclose triples found (n,m,l):", allclose, " count:", len(allclose))
