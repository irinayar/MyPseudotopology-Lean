"""Numerical test of the transference lemma: if z = (n, m, l) in Z^3 has |m - alpha n| <= delta and |l - beta n| <= delta
(delta <= 1), then there is a nonzero h in Z^3 with |h1|,|h2| <= 15 sqrt(n), |h0| <= 30 sqrt(n) and |h0 + h1 alpha + h2 beta| <= 15 delta / sqrt(n).
Brute force over (h1, h2) with h0 the nearest integer, for random (alpha, beta) and all n <= NMAX with small simultaneous error."""
import math, random, sys
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6000
worst = 0.0
cases = 0
for trial in range(6):
    alpha, beta = random.random() * 0.9 + 0.05, random.random() * 0.9 + 0.05
    for n in range(10, NMAX + 1):
        ea = abs(n * alpha - round(n * alpha)); eb = abs(n * beta - round(n * beta))
        delta = max(ea, eb)
        if delta > n ** -0.7 or delta == 0:
            continue
        R = int(15 * math.sqrt(n)) + 1
        best = 1e9
        for h1 in range(-R, R + 1):
            a1 = h1 * alpha
            for h2 in range(-R, R + 1):
                s = a1 + h2 * beta
                h0 = -round(s)
                if h1 == 0 and h2 == 0 and h0 == 0:
                    continue
                v = abs(s + h0)
                if v < best:
                    best = v
        bound = 15 * delta / math.sqrt(n)
        cases += 1
        worst = max(worst, best / bound)
        if best > bound:
            print("VIOLATION", alpha, beta, n, delta, best, bound)
print("cases:", cases, " max (min |h.v|) / bound =", worst)
