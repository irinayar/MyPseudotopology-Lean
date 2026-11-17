"""Independent brute-force check of the lattice certificate for small n (no lattice reduction):
for each close triple with n <= NMAX and every (b,c) with |b|,|c| <= W, the only candidate a is the integer nearest
to -(b rho2 + c rho3); test a != 0, |a| <= W and |a + b rho2 + c rho3| <= eps = e^{-t/2}.
W = floor(0.02 e^{t/4}) (the statement of the Proposition).  Uses exact-enough Decimal arithmetic."""
import sys, math, time
from decimal import Decimal, getcontext
triples = [(32,25,21),(34,27,22),(35,28,23),(38,30,25),(43,34,28),(44,35,29),(49,39,32),(50,40,33),(58,46,38)]
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 50
for (n, m, l) in triples:
    if n > NMAX:
        continue
    t0 = time.time()
    getcontext().prec = 80
    L = {2: Decimal(2).ln(), 3: Decimal(3).ln(), 5: Decimal(5).ln()}
    per = sorted([(Decimal(n * n) * L[2], 2), (Decimal(m * m) * L[3], 3), (Decimal(l * l) * L[5], 5)])
    x, y = per[1][0] - per[0][0], per[2][0] - per[0][0]
    r2, r3 = float((-x).exp()), float((-y).exp())
    r2d, r3d = (-x).exp(), (-y).exp()
    tz = per[0][0].sqrt()
    eps = (-tz / 2).exp()
    W = int(Decimal("0.02") * (tz / 4).exp())
    epsf = float(eps)
    found = []
    for b in range(-W, W + 1):
        base = b * r2
        for c in range(-W, W + 1):
            s = base + c * r3
            a = -round(s)
            if a == 0 or abs(a) > W:
                continue
            if abs(s + a) <= epsf * 1.0001 + 1e-12:
                # confirm in high precision
                v = Decimal(a) + b * r2d + c * r3d
                if abs(v) <= eps:
                    found.append((a, b, c))
    print("n=%5d  W=%4d  eps=%.3e  near-resonant vectors with a!=0 and max<=W: %s  [%.1fs]" % (n, W, epsf, found if found else "none", time.time() - t0))
    sys.stdout.flush()
