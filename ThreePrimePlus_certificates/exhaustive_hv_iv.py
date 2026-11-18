"""Exhaustive enumeration of all integer h with ||h||_inf <= H = 2^k and |h.v| <= H^-2, k = KMIN..KMAX, with a fully interval-certified numerical part.

Same algorithm as exhaustive_hv_fast.py (carried LLL basis, exact Fincke-Pohst with R^2 = 10 H^2), but no floating or decimal arithmetic enters any decision:
  * v_i are rigorous integer-fixed-point intervals (P = 12000 fractional bits) from the series 2*atanh(1/m);
  * the integers r_i = round(W v_i), W = 2^(3k), are taken from the midpoints and checked at every scale to satisfy |W v_i - r_i| <= 0.5001 for the true v_i
    (this justifies the enumeration radius: squared norm <= 3H^2 + (2.5003 H)^2 < 10 H^2);
  * a lattice vector h with ||h|| <= H is KEPT whenever the rigorous lower bound of |h.v| times H^2 is <= 1 (so no vector with |h.v| H^2 <= 1 can be dropped).
Output: one line per kept vector, 'norm [h0, h1, h2]', sorted by norm (h and -h identified).  Usage: exhaustive_hv_iv.py KMIN KMAX"""
import sys, math, time
from fractions import Fraction
KMIN, KMAX = int(sys.argv[1]), int(sys.argv[2])
P = 12000
ONE = 1 << P
def atanh_inv(m):
    m2 = m * m; s = 0; k = 0; nterms = 0; den = m
    while True:
        term = ONE // ((2 * k + 1) * den)
        if term == 0: break
        s += term; nterms += 1; k += 1; den *= m2
    return s, s + nterms + 2
def ivdiv(a, b): return (a[0] * ONE) // b[1], -((-(a[1] * ONE)) // b[0])
def ivsqrt(a): return math.isqrt(a[0] * ONE), math.isqrt(a[1] * ONE) + 1
a2 = atanh_inv(3); a3 = atanh_inv(5); a5 = atanh_inv(9)
L2 = (2 * a2[0], 2 * a2[1]); L3 = (L2[0] + 2 * a3[0], L2[1] + 2 * a3[1]); L5 = (2 * L2[0] + 2 * a5[0], 2 * L2[1] + 2 * a5[1])
V = [(ONE, ONE), ivsqrt(ivdiv(L2, L3)), ivsqrt(ivdiv(L2, L5))]
def hv_lowabs(h):
    lo = hi = 0
    for x, (a, b) in zip(h, V):
        if x >= 0: lo += x * a; hi += x * b
        else: lo += x * b; hi += x * a
    if lo > 0: return lo
    if hi < 0: return -hi
    return 0

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

def enumerate_short(B, Bs, mu, R2, limit=2000000):
    n = len(B); nb = [dot(Bs[i], Bs[i]) for i in range(n)]; out = []
    def rec(i, ks, rest):
        if len(out) > limit: raise RuntimeError("limit")
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

U = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
found = {}
t0 = time.time()
for k in range(KMIN, KMAX + 1):
    H = 2 ** k; W = H ** 3
    r = [W]
    for i in (1, 2):
        ri = ((V[i][0] + V[i][1]) * W + ONE) // (2 * ONE)
        assert max(abs(V[i][0] * W - ri * ONE), abs(V[i][1] * W - ri * ONE)) * 10000 <= 5001 * ONE, ("slack violated", k, i)
        r.append(ri)
    rows = [[h[0], h[1], h[2], h[0] * r[0] + h[1] * r[1] + h[2] * r[2]] for h in U]
    B, Bs, mu = lll(rows)
    U = [row[:3] for row in B]
    vecs = enumerate_short(B, Bs, mu, Fraction(10 * H * H))
    cnt = 0
    for ks in vecs:
        h = [sum(ks[i] * B[i][j] for i in range(3)) for j in range(3)]
        if h == [0, 0, 0]: continue
        hinf = max(abs(x) for x in h)
        if hinf > H: continue
        if hv_lowabs(h) * H * H <= ONE:
            key = tuple(h) if tuple(h) > tuple(-x for x in h) else tuple(-x for x in h)
            if key not in found:
                found[key] = hinf; cnt += 1
    if k % 100 == 0 or k <= 3:
        print("k=%4d H=2^%d  lattice vectors enumerated: %7d   new kept h: %d   [%.0fs]" % (k, k, len(vecs), cnt, time.time() - t0)); sys.stdout.flush()
print("\nkept vectors (rigorous lower bound |h.v| H^2 <= 1 at their scale): %d" % len(found))
for h, hinf in sorted(found.items(), key=lambda kv: kv[1]):
    print("%d  %s" % (hinf, list(h)))
