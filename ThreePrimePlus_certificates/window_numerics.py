"""Explicit numerics of the stretched-exponential window (ThreePrimePlus Section 3, Lemma Windows).
w = density of the infinite convolution of uniform laws on [-l_j, l_j], l_j = c_w / j^2.
what(r) = prod_j sin(2 pi l_j r)/(2 pi l_j r);  for periods Q >= 2^600 the aliasing error in kappa_Q(r) is < 1e-100,
so kappa_Q(r) = what(r)^2 / m_Q^2 with m_Q = 1 up to 1e-100.
beta_0 = sum_r what(r)^2 = int w^2 (Parseval); tau(v) = sum_{|r|>v} what(r)^2."""
import math, sys
cw = float(sys.argv[1]) if len(sys.argv) > 1 else 0.15
J = 4000
RMAX = 4000
def what(r):
    if r == 0:
        return 1.0
    s = 0.0
    prod = 1.0
    for j in range(1, J + 1):
        y = 2 * math.pi * cw * r / (j * j)
        if y < 1e-3:
            # sinc(y) ~ 1 - y^2/6 for the remaining factors: sum_{j>=j0} y_j^2/6 (zeta tail)
            tail = (2 * math.pi * cw * r) ** 2 / 6.0 * sum(1.0 / (k ** 4) for k in range(j, j + 2000))
            tail += (2 * math.pi * cw * r) ** 2 / 6.0 * (1.0 / (3.0 * (j + 2000) ** 3))
            prod *= math.exp(-tail)
            break
        prod *= math.sin(y) / y
    return prod
vals = [what(r) for r in range(RMAX + 1)]
beta0 = vals[0] ** 2 + 2 * sum(v * v for v in vals[1:])
print("c_w = %.3f, sum of supports l_j = %.4f, beta_0 = sum what^2 = %.5f" % (cw, cw * math.pi ** 2 / 6, beta0))
def tau(v):
    return 2 * sum(vals[r] ** 2 for r in range(int(math.floor(v)) + 1, RMAX + 1))
for v in (1, 2, 5, 10, 14, 20, 30, 50, 100, 300, 700, 1000, 2000):
    print("tau(%d) = %.3e" % (v, tau(v)))
print("what(1..8):", ["%.4f" % vals[r] for r in range(1, 9)])
