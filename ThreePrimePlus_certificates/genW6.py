"""Exact (Fincke-Pohst) certificate: no integer vector (a,b,c) with a != 0, max(|a|,|b|,|c|) <= W0 = KAPPA*e^(n/4),
and |a + b rho2 + c rho3| <= eps = e^(-n/2).  rho2 = Q1/Q2, rho3 = Q1/Q3 for the certified close triples.
Lattice vectors (T a, T b, T c, round(Lam T (a + b rho2 + c rho3 coefficients))) ; the rounding (truncation) error of the last
coordinate is <= 3 max|coords| (three truncated entries, each < 1).  Target region has squared norm <= R^2 with
R^2 = T^2 * 3 W0^2 + (Lam T eps + 3 W0)^2 ; every lattice vector in the region has norm <= R, so
enumerating all lattice vectors of norm <= R and finding none with a != 0 proves the claim.
"""
import sys, math, time
from decimal import Decimal, getcontext
from fractions import Fraction
from math import isqrt

triples = [(32,25,21),(34,27,22),(35,28,23),(38,30,25),(43,34,28),(44,35,29),(49,39,32),(50,40,33),(58,46,38),(64,51,42),(67,53,44),(73,58,48),(87,69,57),(93,74,61),(102,81,67),(116,92,76),(131,104,86),(137,109,90),(160,127,105),(166,132,109),(189,150,124),(195,155,128),(224,178,147),(253,201,166),(282,224,185),(326,259,214),(355,282,233),(384,305,252),(413,328,271),(739,587,485),(768,610,504),(1123,892,737),(2144,1703,1407),(2499,1985,1640),(2883,2290,1892),(3267,2595,2144),(5766,4580,3784),(39268,31191,25770)]
NMIN = int(sys.argv[1]); NMAX = int(sys.argv[2]); KAPPA = Fraction(sys.argv[3]) if len(sys.argv) > 3 else Fraction(1, 50)
C0 = Decimal(sys.argv[4]) if len(sys.argv) > 4 else Decimal("0.5")
TSCALE = 1000


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def lll(B, delta=Fraction(99, 100)):
    n = len(B)
    B = [list(r) for r in B]

    def gs():
        Bs, mu = [], [[Fraction(0)] * n for _ in range(n)]
        for i in range(n):
            w = [Fraction(x) for x in B[i]]
            for j in range(i):
                mu[i][j] = dot(B[i], Bs[j]) / dot(Bs[j], Bs[j])
                w = [a - mu[i][j] * b for a, b in zip(w, Bs[j])]
            Bs.append(w)
        return Bs, mu
    Bs, mu = gs()
    k = 1
    while k < n:
        for j in range(k - 1, -1, -1):
            q = round(mu[k][j])
            if q:
                B[k] = [a - q * b for a, b in zip(B[k], B[j])]
                Bs, mu = gs()
        if dot(Bs[k], Bs[k]) >= (delta - mu[k][k - 1] ** 2) * dot(Bs[k - 1], Bs[k - 1]):
            k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]
            Bs, mu = gs()
            k = max(k - 1, 1)
    return B, Bs, mu


def enumerate_short(B, Bs, mu, R2, limit=200000):
    """all integer coefficient vectors k with |sum k_i B_i|^2 <= R2 (Fincke-Pohst, exact)."""
    n = len(B)
    nb = [dot(Bs[i], Bs[i]) for i in range(n)]
    out = []

    def rec(i, ks, rest):
        if len(out) > limit:
            return
        if i < 0:
            out.append(list(ks)); return
        c = -sum(ks[j] * mu[j][i] for j in range(i + 1, n)) if i < n - 1 else Fraction(0)
        # (k_i - c)^2 * nb[i] <= rest
        rad2 = rest / nb[i]
        r = isqrt(int(rad2)) + 1 if rad2 > 0 else 0
        lo = math.floor(c - r - 1); hi = math.ceil(c + r + 1)
        for k in range(lo, hi + 1):
            t = (k - c) ** 2 * nb[i]
            if t <= rest:
                ks[i] = k
                rec(i - 1, ks, rest - t)
        ks[i] = 0
    rec(n - 1, [0] * n, R2)
    return out


print("     n   result (kappa = %s): lattice has no vector with a != 0 in the box  [time]" % KAPPA)
for (n, m, l) in triples:
    if n < NMIN or n > NMAX:
        continue
    t0 = time.time()
    getcontext().prec = int(0.9 * n / 2.3) + 300
    L = {2: Decimal(2).ln(), 3: Decimal(3).ln(), 5: Decimal(5).ln()}
    per = sorted([(Decimal(n * n) * L[2], 2), (Decimal(m * m) * L[3], 3), (Decimal(l * l) * L[5], 5)])
    x, y = per[1][0] - per[0][0], per[2][0] - per[0][0]
    r2, r3 = (-x).exp(), (-y).exp()
    tz = per[0][0].sqrt()
    eps = (-tz / 2).exp()
    Lam = int((Decimal(10) * eps) ** Decimal("-1.5")) + 1
    T = TSCALE
    basis = [[T, 0, 0, Lam * T], [0, T, 0, int(Lam * T * r2)], [0, 0, T, int(Lam * T * r3)]]
    B, Bs, mu = lll(basis)
    W0 = KAPPA * Fraction(int(((tz / 4).exp()) * 10 ** 6), 10 ** 6)
    s0 = Fraction(int(Lam * T * eps * 10 ** 6), 10 ** 6)
    R2 = Fraction(T) ** 2 * 3 * W0 ** 2 + (s0 + 3 * W0) ** 2
    vecs = enumerate_short(B, Bs, mu, R2)
    bad = []
    for ks in vecs:
        v = [sum(ks[i] * B[i][j] for i in range(3)) for j in range(4)]
        a = v[0] // T
        if v[0] % T == 0 and a != 0:
            W = max(abs(v[0]), abs(v[1]), abs(v[2])) // T
            bad.append((W, a, v[1] // T, v[2] // T))
    status = "CERTIFIED" if not bad else "NOT certified: vector with a != 0, max coord %s" % ("%.3e" % float(min(bad)[0]))
    print("%6d   t=%.4f  W0=%.4e   %s   (%d lattice vectors in the region)  [%.1fs]" % (n, float(tz), (Decimal(W0.numerator) / Decimal(W0.denominator)), status, len(vecs), time.time() - t0))
    sys.stdout.flush()
