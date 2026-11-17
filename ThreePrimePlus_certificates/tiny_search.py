"""Window-free search for tiny near-resonant vectors.
For every ordered pair of primes (p,q) of {2,3,5} with third prime s, every index j (period Q1=p^(j^2)) and
j' = nearest integer to j sqrt(log p/log q) (period Q2=q^(j'^2) > Q1, x = log(Q2/Q1) in [0, XMAX]), and every integer vector
(a,b,c) with 1<=|a|<=2, |b|,|c|<=2, solve a + b e^-x + c rho3 = 0 for rho3 in (0, e^-x], take the nearest index l of the
third period Q3 = s^(l^2) and test |a + b rho2 + c rho3(l)| < e^(-t/2), t = sqrt(log Q1).
Prints the minimal residual ratio (residual / e^(-t/2)) seen and all candidates with residual < 1e-3 (double precision screen).
Usage: tiny_search.py JMAX"""
import sys, math, itertools
JMAX = int(sys.argv[1])
primes = [2, 3, 5]
XMAX = math.log(8) + 0.2
vecs = [(a, b, c) for a in range(-2, 3) for b in range(-2, 3) for c in range(-2, 3) if a != 0 and (c != 0 or b != 0)]
cands = []
npairs = 0
for p, q in itertools.permutations(primes, 2):
    s = [r for r in primes if r not in (p, q)][0]
    Lp, Lq, Ls = math.log(p), math.log(q), math.log(s)
    ratio = math.sqrt(Lp / Lq)
    for j in range(1, JMAX + 1):
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
            if c == 0:
                continue
            rho3 = -(a + b * rho2) / c
            if not (1e-15 < rho3 <= rho2 * (1 + 1e-9)):
                continue
            y = -math.log(rho3)
            lv = math.sqrt((j * j * Lp + y) / Ls)
            for l in (math.floor(lv), math.ceil(lv)):
                if l < 1:
                    continue
                yl = l * l * Ls - j * j * Lp
                if yl < x:
                    continue
                res = abs(a + b * rho2 + c * math.exp(-yl))
                if res < 1e-3:
                    cands.append((res, p, q, s, j, jp, l, (a, b, c), x, yl, t))
print("pairs (p,q,j) with x in [0,%.3f]: %d" % (XMAX, npairs))
cands.sort()
for cd in cands[:40]:
    res, p, q, s, j, jp, l, v, x, yl, t = cd
    print("res=%.3e  thr=exp(-t/2)=%.3e  order(%d,%d,%d) j=%d j'=%d l=%d vec=%s x=%.4f y=%.4f t=%.2f" % (res, math.exp(-t / 2), p, q, s, j, jp, l, v, x, yl, t))
print("number of screened candidates (res<1e-3): %d" % len(cands))
