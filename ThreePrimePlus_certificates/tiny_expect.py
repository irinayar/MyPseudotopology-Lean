"""Poisson-model expectation of the number of tiny triples: for each pair (p,q,j) with 0 <= x <= log 5 and each vector (a,b,c),
a != 0, b,c != 0, |.|<=2 with rho3 = -(a+b rho2)/c in (0, rho2], the third period must fall within |c|^-1 e^(-t/2) of
the real target; the spacing of the values rho3(l) is rho3 * (2 l + 1) log s, so the probability is about
min(1, 2 e^(-t/2) / (|c| * rho3 * (2 l + 1) * log s))."""
import math, itertools
primes = [2, 3, 5]
XMAX = math.log(5)
vecs = [(a, b, c) for a in range(-2, 3) for b in range(-2, 3) for c in range(-2, 3) if a != 0 and b != 0 and c != 0]
total = 0.0
npairs = 0
for p, q in itertools.permutations(primes, 2):
    s = [r for r in primes if r not in (p, q)][0]
    Lp, Lq, Ls = math.log(p), math.log(q), math.log(s)
    ratio = math.sqrt(Lp / Lq)
    for j in range(1, 3000001):
        t = j * math.sqrt(Lp)
        if t < 26:
            continue
        jp = round(j * ratio)
        x = jp * jp * Lq - j * j * Lp
        if x < 0 or x > XMAX:
            continue
        npairs += 1
        rho2 = math.exp(-x)
        for (a, b, c) in vecs:
            rho3 = -(a + b * rho2) / c
            if not (1e-15 < rho3 <= rho2):
                continue
            y = -math.log(rho3)
            l = math.sqrt((j * j * Lp + y) / Ls)
            pr = min(1.0, 2 * math.exp(-t / 2) / (abs(c) * rho3 * (2 * l + 1) * Ls))
            total += pr
print("pairs:", npairs, " expected number of tiny triples (t>=26, j<=3e6):", total)
