"""Direct check of Theorem (b) for small n: for every n with 10 <= n <= NMAX and the nearest integers m ~ alpha n, l ~ beta n (and their neighbours),
compute the logarithmic diameter D of (2^(n^2), 3^(m^2), 5^(l^2)) and report min D/sqrt(n); the theorem predicts D >= 2.4e-5 sqrt(n)."""
import math, sys
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 300000
L2, L3, L5 = math.log(2), math.log(3), math.log(5)
al, be = math.sqrt(L2 / L3), math.sqrt(L2 / L5)
best = (1e9, None)
rec = []
for n in range(10, NMAX + 1):
    m0, l0 = round(al * n), round(be * n)
    a = n * n * L2
    for m in (m0 - 1, m0, m0 + 1):
        x = m * m * L3
        for l in (l0 - 1, l0, l0 + 1):
            y = l * l * L5
            D = max(a, x, y) - min(a, x, y)
            r = D / math.sqrt(n)
            if r < best[0]:
                best = (r, (n, m, l, D))
            if D < 0.5:
                rec.append((n, m, l, D))
print("min D/sqrt(n) = %.3e at (n,m,l,D) = %s   (theorem: >= 2.4e-5)" % (best[0], best[1]))
print("triples with D < 0.5:", rec[:10], len(rec))
