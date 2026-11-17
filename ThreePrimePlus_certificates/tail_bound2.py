"""Rigorous tail bound for sum_{|r|>=4000} kappa(r), c_w = 0.15, independent of tail_bound.py.
|w^(r)| <= B(r) = prod_{j<=J} j^2/(c r), c = 2 pi c_w, J = floor(sqrt(c r)), because |sin y/y| <= 1/|y| for the factors with
y_j = c r / j^2 >= 1 (j <= J) and <= 1 for the others.  Since c r >= J^2, j^2/(c r) <= (j/J)^2, so
B(r) <= (J!/J^J)^2 <= (e sqrt(J) e^{-J})^2 = e^2 J e^{-2J}   (Stirling: J! <= e sqrt(J) (J/e)^J).
Hence kappa(r) <= B(r)^2 <= e^4 J^2 e^{-4J}; the number of integers r with floor(sqrt(c r)) = J is at most (2J+1)/c + 1.
Prints the exact B(4000)^2 (exact rational arithmetic) and the bound  2 * sum_{J >= 61} ((2J+1)/c + 1) e^4 J^2 e^{-4J}."""
import math
from fractions import Fraction
from decimal import Decimal, getcontext
getcontext().prec = 50
c = 2 * math.pi * 0.15
r = 4000
J = int(math.isqrt(int(c * r)))
while (J + 1) ** 2 <= c * r:
    J += 1
print("J(4000) =", J)
# exact-ish: product of j^2 / (c r) in Decimal
cr = Decimal(2) * Decimal("3.14159265358979323846264338327950288") * Decimal("0.15") * 4000
B = Decimal(1)
for j in range(1, J + 1):
    B *= Decimal(j * j) / cr
print("B(4000) = %.6e   B(4000)^2 = %.6e" % (B, B * B))
tot = 0.0
for JJ in range(J, 400):
    tot += ((2 * JJ + 1) / c + 1) * math.exp(4) * JJ * JJ * math.exp(-4 * JJ)
print("rigorous: 2 * sum_{r>=4000} kappa(r) <= %.3e" % (2 * tot))
