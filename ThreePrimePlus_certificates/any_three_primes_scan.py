"""Illustration for other triples of primes (p<q<r): close triples of the explicit window found by scanning the nearest integers m = round(alpha n), l = round(beta n),
alpha = sqrt(log p/log q), beta = sqrt(log p/log r), n <= NMAX.  A triple (n,m,l), n >= 32, is 'close' if its logarithmic diameter is at most W(n) = (1+floor(log2 n))^2 log 2
and no other period of the three chains lies in the closed interval spanned by its periods.  double precision (n^2 log p <= 4e12 for NMAX = 2e6; errors ~1e-3 << the margins);
NOT certified: an illustration of how the census depends on the primes, using the nearest-integer reduction (valid because |m - alpha n| <= 1/2 for every triple of diameter <= W when
W/(n sqrt(log p log q)) < 1/2, i.e. for n large; for small n the scan also tests m = round(alpha n) +-1).  Usage: any_three_primes_scan.py p q r NMAX"""
import math, sys
p, q, r = map(int, sys.argv[1:4]); NMAX = int(sys.argv[4])
L = [math.log(p), math.log(q), math.log(r)]
al, be = math.sqrt(L[0] / L[1]), math.sqrt(L[0] / L[2])
def other_periods(lo, hi, members):
    cnt = 0
    for i in range(3):
        a = int(math.ceil(math.sqrt(lo / L[i]) - 1e-9)); b = int(math.floor(math.sqrt(hi / L[i]) + 1e-9))
        cnt += max(0, b - a + 1)
    return cnt
found = []; diam_only = 0
for n in range(32, NMAX + 1):
    W = (1 + int(math.log2(n))) ** 2 * math.log(2)
    a = n * n * L[0]
    for m in (round(al * n) - 1, round(al * n), round(al * n) + 1):
        if m < 1: continue
        b = m * m * L[1]
        if abs(a - b) > W: continue
        for l in (round(be * n) - 1, round(be * n), round(be * n) + 1):
            if l < 1: continue
            c = l * l * L[2]
            lo, hi = min(a, b, c), max(a, b, c)
            if hi - lo <= W:
                diam_only += 1
                if other_periods(lo, hi, 3) == 3:
                    found.append((n, m, l))
print("primes (%d,%d,%d): alpha=%.6f beta=%.6f; n<=%d: triples with diameter <= W: %d; close triples (no other period inside): %d; largest n: %s" % (p, q, r, al, be, NMAX, diam_only, len(found), found[-1] if found else None))
print("first close triples:", found[:8])
