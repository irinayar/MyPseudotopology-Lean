"""Rigorous tail of the kernel weights beyond r = 4000 for c_w = 0.15.
|sin y / y| <= min(1, 1/|y|), so |w^(r)| <= prod_{j: y_j >= 1} 1/y_j with y_j = 2 pi c_w r / j^2, i.e.
kappa(r) <= B(r)^2, B(r) = prod_{j <= J} j^2/(2 pi c_w r), J = floor(sqrt(2 pi c_w r)).  B is decreasing in r.
Prints log10 B(4000)^2 and log10 of 2 * sum_{r >= 4000} B(r)^2 (the sum is truncated at r = 10^6, where the terms are below 10^-300)."""
import math
cw = 0.15
c = 2 * math.pi * cw
def logB(r):
    J = int(math.isqrt(int(c * r)))
    while (J + 1) ** 2 <= c * r:
        J += 1
    return sum(math.log(j * j / (c * r)) for j in range(1, J + 1))
print("log10 B(4000)^2 = %.2f" % (2 * logB(4000) / math.log(10)))
tot = 0.0
for r in range(4000, 20001):
    tot += math.exp(2 * logB(r))
print("2 * sum_{4000<=r<=20000} B(r)^2 = %.3e  (log10 = %.2f)" % (2 * tot, math.log10(2 * tot) if tot > 0 else float('-inf')))
