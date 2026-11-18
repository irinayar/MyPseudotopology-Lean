"""Poisson-model expectation of the number of B-small close triples (all n >= 32), for several B, and its tail beyond n0.

Model (heuristic, as in tiny_expect.py): for each ordered pair of primes (p,q) (Q1 = p^(j^2) < Q2 = q^(jp^2), the nearest index jp = round(j*sqrt(log p/log q)))
with x = log(Q2/Q1) in [0, log(2B+1)] (Lemma tinyclose), and each vector (a,b,c) with a>0 (the vectors v and -v give the same relation), b != 0, c != 0, |a|,|b|,|c| <= B,
the target rho3 = -(a + b rho2)/c must lie in (0, rho2]; the third period (prime s, index l) must put rho3 within e^(-t/2)/|c| of the target, t = j sqrt(log p);
the spacing of the values rho3(l) is rho3 (2l+1) log s, so the probability is min(1, 2 e^(-t/2) / (|c| rho3 (2 l + 1) log s)).
Output: expected numbers of such triples with n >= n0 for n0 in (32, 64, 128, 256, 1000).  Usage: tiny_expect_B.py B JMAX"""
import math, itertools, sys
B = int(sys.argv[1]); JMAX = int(sys.argv[2])
primes = [2, 3, 5]
XMAX = math.log(2 * B + 1)
vecs = [(a, b, c) for a in range(1, B + 1) for b in range(-B, B + 1) for c in range(-B, B + 1) if b != 0 and c != 0]
thr = [32, 64, 128, 256, 1000]
tot = {n0: 0.0 for n0 in thr}
npairs = 0
for p, q in itertools.permutations(primes, 2):
    s = [r for r in primes if r not in (p, q)][0]
    Lp, Lq, Ls = math.log(p), math.log(q), math.log(s)
    ratio = math.sqrt(Lp / Lq)
    for j in range(32, JMAX + 1):
        t = j * math.sqrt(Lp)
        jp = round(j * ratio)
        x = jp * jp * Lq - j * j * Lp
        if x < 0 or x > XMAX:
            continue
        npairs += 1
        rho2 = math.exp(-x)
        sub = 0.0
        for (a, b, c) in vecs:
            rho3 = -(a + b * rho2) / c
            if not (1e-15 < rho3 <= rho2):
                continue
            y = -math.log(rho3)
            l = math.sqrt((j * j * Lp + y) / Ls)
            sub += min(1.0, 2 * math.exp(-t / 2) / (abs(c) * rho3 * (2 * l + 1) * Ls))
        for n0 in thr:
            if j >= n0:
                tot[n0] += sub
print("B = %d  (|vectors| = %d, pairs with x <= log(2B+1) for 32 <= n <= %d, ordered primes: %d)" % (B, len(vecs), JMAX, npairs))
for n0 in thr:
    print("  expected number of B-small triples with n >= %d : %.3e" % (n0, tot[n0]))
