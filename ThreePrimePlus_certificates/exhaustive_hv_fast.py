"""Faster exhaustive enumeration of all integer h with ||h||_inf <= H = 2^k and |h.v| <= H^-2, k = KMIN..KMAX (same claim as exhaustive_hv.py).

Difference: the reduced basis is carried from scale k to scale k+1 (the h-parts of the basis are a unimodular matrix U; the last coordinates are
recomputed from the new rounded values r_i = round(W v_i), W = 2^(3k), so the rows are a basis of the new lattice), then LLL-reduced again.
Everything else (R^2 = 10 H^2, exact Fincke-Pohst, exact filter) is as in exhaustive_hv.py, so the completeness argument is the same.
Usage: exhaustive_hv_fast.py KMIN KMAX   (output format as exhaustive_hv.py)"""
import sys, math, time
from fractions import Fraction
from decimal import Decimal, getcontext
KMIN, KMAX = int(sys.argv[1]), int(sys.argv[2])
getcontext().prec = int(3.0 * KMAX * 0.30103) + 400
L2, L3, L5 = Decimal(2).ln(), Decimal(3).ln(), Decimal(5).ln()
alpha, beta = (L2 / L3).sqrt(), (L2 / L5).sqrt()
v = [Decimal(1), alpha, beta]

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
    r = [int(round(Decimal(W) * x)) for x in v]
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
        hv = abs(Decimal(h[0]) + Decimal(h[1]) * alpha + Decimal(h[2]) * beta)
        if hv * H * H <= 1:
            key = tuple(h) if tuple(h) > tuple(-x for x in h) else tuple(-x for x in h)
            if key not in found:
                found[key] = (hinf, hv); cnt += 1
    if k % 50 == 0 or k <= 3:
        print("k=%4d H=2^%d  lattice vectors enumerated: %7d   new exceptional h: %d   [%.0fs]" % (k, k, len(vecs), cnt, time.time() - t0)); sys.stdout.flush()
rows = sorted(found.items(), key=lambda kv: kv[1][0])
print("\nexceptional vectors (|h.v| <= H^-2 at their scale), sorted by norm:  ||h||_inf, |h.v|, |h.v| ||h||^2, J, h")
for h, (hinf, hv) in rows:
    prod = hv * hinf * hinf
    J = float(-hv.ln() / Decimal(hinf).ln()) if hinf > 1 else float('nan')
    print("%d  %.3e  %.4f  %.3f  %s" % (hinf, float(hv), float(prod), J, list(h)))
