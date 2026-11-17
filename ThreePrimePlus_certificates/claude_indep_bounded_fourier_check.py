# Independent re-check (Claude) of the bounded-Fourier prefix test of ThreePrimePlus-v2, Section 2.
# Own enumeration with high-precision Decimal logs; window Q3/Q1 <= 2^((1+floor(log2 n))^2), B=128.
from decimal import Decimal, getcontext
import math
getcontext().prec = 80
L2, L3, L5 = Decimal(2).ln(), Decimal(3).ln(), Decimal(5).ln()
LN = {2: L2, 3: L3, 5: L5}
B = 128
NMAX = 100000
def lg(p, j): return LN[p] * j * j
trip = []
for n in range(32, NMAX + 1):
    bits = (1 + n.bit_length() - 1) ** 2        # 1+floor(log2 n) = bit_length
    bits = n.bit_length() ** 2
    W = bits * L2
    base = lg(2, n)
    def rng(p):
        # all j with |j^2 ln p - base| <= W (a superset of what is needed)
        lo = ((base - W) / LN[p]); hi = ((base + W) / LN[p])
        a = int(lo.sqrt().to_integral_value(rounding='ROUND_FLOOR')) if lo > 0 else 1
        b = int(hi.sqrt().to_integral_value(rounding='ROUND_CEILING')) + 1
        return range(max(a, 1), b + 1)
    for m in rng(3):
        for l in rng(5):
            q = sorted([(lg(2, n), 2, n), (lg(3, m), 3, m), (lg(5, l), 5, l)])
            if q[2][0] - q[0][0] > W: continue
            # consecutive: every other period of every prime is outside [Q1,Q3]
            ok = True
            for p, j in ((2, n), (3, m), (5, l)):
                for jj in (j - 1, j + 1):
                    if jj >= 1 and q[0][0] <= lg(p, jj) <= q[2][0]: ok = False
            if not ok: continue
            nxt = min(lg(p, j + 1) for p, j in ((2, n), (3, m), (5, l)))
            trip.append((n, m, l, q, nxt))
print("close consecutive triples, n<=%d: %d" % (NMAX, len(trip)))
bad = 0
for n, m, l, q, nxt in trip:
    x = q[1][0] - q[0][0]; y = q[2][0] - q[0][0]
    r2 = (-x).exp(); r3 = (-y).exp()
    tau = (6 * B + 1) * (-(nxt - q[0][0])).exp()
    for a in range(1, B + 1):
        for b in range(-B, B + 1):
            s = a + b * r2
            c0 = -s / r3
            c = int(c0.to_integral_value())
            for cc in (c - 1, c, c + 1):
                if abs(cc) <= B and abs(s + cc * r3) < tau:
                    bad += 1; print("PASS", n, m, l, a, b, cc)
print("passing vectors:", bad)
print("largest:", max((t[0], t[1], t[2]) for t in trip))
print("all:", sorted((t[0], t[1], t[2]) for t in trip))
