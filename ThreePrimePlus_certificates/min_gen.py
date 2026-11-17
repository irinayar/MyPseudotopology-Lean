"""Smallest near-resonant vector at the close triples with small n, by brute force.
For each triple (n,m,l) with n <= NMAX, over all (b,c) with |b|,|c| <= WMAX the only candidate a is -round(b rho2 + c rho3);
a vector is near-resonant if a != 0, |a| <= WMAX and |a + b rho2 + c rho3| <= eps = e^(-t/2).  Prints, for each triple, the near-resonant
vectors found (all of them, sorted by max coordinate), each confirmed in 80-digit arithmetic.
Usage: min_gen.py NMAX WMAX"""
import sys, time
from decimal import Decimal, getcontext
triples = [(32,25,21),(34,27,22),(35,28,23),(38,30,25),(43,34,28),(44,35,29),(49,39,32),(50,40,33),(58,46,38)]
NMAX = int(sys.argv[1]); WMAX = int(sys.argv[2])
for (n, m, l) in triples:
    if n > NMAX:
        continue
    t0 = time.time()
    getcontext().prec = 80
    L = {2: Decimal(2).ln(), 3: Decimal(3).ln(), 5: Decimal(5).ln()}
    per = sorted([(Decimal(n * n) * L[2], 2), (Decimal(m * m) * L[3], 3), (Decimal(l * l) * L[5], 5)])
    x, y = per[1][0] - per[0][0], per[2][0] - per[0][0]
    r2d, r3d = (-x).exp(), (-y).exp()
    r2, r3 = float(r2d), float(r3d)
    tz = per[0][0].sqrt()
    eps = (-tz / 2).exp()
    epsf = float(eps)
    found = []
    for b in range(-WMAX, WMAX + 1):
        base = b * r2
        for c in range(-WMAX, WMAX + 1):
            s = base + c * r3
            a = -round(s)
            if a == 0 or abs(a) > WMAX:
                continue
            if abs(s + a) <= epsf * 1.0001 + 1e-12:
                v = Decimal(a) + b * r2d + c * r3d
                if abs(v) <= eps:
                    found.append((max(abs(a), abs(b), abs(c)), a, b, c))
    found.sort()
    # keep one of each +-pair
    seen = set(); uniq = []
    for f in found:
        key = (f[1], f[2], f[3]) if (f[1], f[2], f[3]) > (-f[1], -f[2], -f[3]) else (-f[1], -f[2], -f[3])
        if key not in seen:
            seen.add(key); uniq.append(f)
    print("n=%d t=%.3f eps=%.3e x=%.4f y=%.4f  near-resonant vectors (max<=%d), up to sign: %s  [%.0fs]" % (n, float(tz), epsf, float(x), float(y), WMAX, uniq[:6] if uniq else "none", time.time() - t0))
    sys.stdout.flush()
