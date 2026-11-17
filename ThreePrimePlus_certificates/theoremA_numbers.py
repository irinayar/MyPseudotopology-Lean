"""Numbers for Theorem A of ThreePrimePlus: per-triple t, certified W_z = 0.02 e^(t/4) (or e^x/4 for n=39268),
mass bound 3 beta^2 tau(W_z), truncation 3 beta^2 tau(ceil t^2), and totals.  Window c_w = 0.15."""
import math, sys
from decimal import Decimal, getcontext
getcontext().prec = 60
cw = 0.15
J = 4000
RMAX = 4000
def what(r):
    if r == 0:
        return 1.0
    prod = 1.0
    for j in range(1, J + 1):
        y = 2 * math.pi * cw * r / (j * j)
        if y < 1e-3:
            tail = (2 * math.pi * cw * r) ** 2 / 6.0 * sum(1.0 / (k ** 4) for k in range(j, j + 2000))
            prod *= math.exp(-tail)
            break
        prod *= math.sin(y) / y
    return prod
vals = [what(r) for r in range(RMAX + 1)]
beta0 = vals[0] ** 2 + 2 * sum(v * v for v in vals[1:])
beta = 1.001 * beta0        # kappa_Q sums to beta_0 up to aliasing errors below 1e-90 for Q >= 2^600
sq = [v * v for v in vals]
suffix = [0.0] * (RMAX + 2)
for r in range(RMAX, -1, -1):
    suffix[r] = suffix[r + 1] + sq[r]
def tau(v):
    if v >= RMAX:
        return 0.0
    r0 = int(math.floor(v)) + 1
    return 2 * suffix[r0] * 1.001
L = {2: Decimal(2).ln(), 3: Decimal(3).ln(), 5: Decimal(5).ln()}
triples = [(32,25,21),(34,27,22),(35,28,23),(38,30,25),(43,34,28),(44,35,29),(49,39,32),(50,40,33),(58,46,38),(64,51,42),(67,53,44),(73,58,48),(87,69,57),(93,74,61),(102,81,67),(116,92,76),(131,104,86),(137,109,90),(160,127,105),(166,132,109),(189,150,124),(195,155,128),(224,178,147),(253,201,166),(282,224,185),(326,259,214),(355,282,233),(384,305,252),(413,328,271),(739,587,485),(768,610,504),(1123,892,737),(2144,1703,1407),(2499,1985,1640),(2883,2290,1892),(3267,2595,2144),(5766,4580,3784),(39268,31191,25770)]
print("beta_0 = %.5f, beta = %.5f, 3 beta^2 = %.3f" % (beta0, beta, 3 * beta * beta))
tot_mass = 0.0; tot_trunc = 0.0; worst = 0.0
rows = []
for (n, m, l) in triples:
    per = sorted([(Decimal(n * n) * L[2], 2), (Decimal(m * m) * L[3], 3), (Decimal(l * l) * L[5], 5)])
    t = float(per[0][0].sqrt())
    x = float(per[1][0] - per[0][0])
    if n <= 5766:
        W = 0.02 * math.exp(min(t / 4, 700))
    else:
        W = math.exp(min(x, 700)) / 4
    M2 = math.ceil(t * t)
    mass = 3 * beta ** 2 * tau(W)
    trunc = 3 * beta ** 2 * tau(M2)
    rows.append((n, t, W, mass, trunc))
    tot_mass += mass; tot_trunc += trunc
    worst = max(worst, mass + trunc)
for r in rows[:6] + rows[-3:]:
    print("n=%6d  t=%9.4f  W=%.4e  mass bound=%.3e  truncation=%.3e" % r)
print("sum of mass bounds over the 38 triples: %.3e" % tot_mass)
print("sum of truncation terms:                %.3e" % tot_trunc)
print("max over triples of (mass + truncation): %.3e" % worst)
