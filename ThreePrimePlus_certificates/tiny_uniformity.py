"""Uniformity test with ONE sample per close pair (the vectors (a,b,c) of the same pair give almost the same l*, so they are not independent samples).
For each ordered pair (p,q), j >= 32 with x = log(Q2/Q1) in [0, log(2B+1)]: d = distance of j*sqrt(log p/log s) from the nearest integer (s = third prime).
Under the independence heuristic d is uniform on [0,1/2]. Usage: tiny_uniformity.py B JMAX"""
import math, itertools, sys
B = int(sys.argv[1]); JMAX = int(sys.argv[2])
primes = [2, 3, 5]; XMAX = math.log(2 * B + 1)
ds = []
for p, q in itertools.permutations(primes, 2):
    s = [r for r in primes if r not in (p, q)][0]
    Lp, Lq, Ls = math.log(p), math.log(q), math.log(s)
    ratio = math.sqrt(Lp / Lq); r3 = math.sqrt(Lp / Ls)
    for j in range(32, JMAX + 1):
        jp = round(j * ratio)
        x = jp * jp * Lq - j * j * Lp
        if 0 <= x <= XMAX:
            v = j * r3
            ds.append(abs(v - round(v)))
N = len(ds); bins = [0] * 5
for d in ds: bins[min(4, int(d / 0.1))] += 1
e = N / 5.0; chi2 = sum((o - e) ** 2 / e for o in bins)
print("B=%d JMAX=%d pairs N=%d bins(5 of [0,1/2])=%s chi2(4 dof; 95%%: 9.49, 99.9%%: 18.5)=%.2f mean d=%.4f (uniform 0.25)" % (B, JMAX, N, bins, chi2, sum(ds) / N))
