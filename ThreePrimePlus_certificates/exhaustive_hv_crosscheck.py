"""Cross-check of exhaustive_hv.py by brute force for ||h||_inf <= HB: all h with |h.v| ||h||_inf^2 <= 1/4 found by direct search over (h1,h2)
(h0 the nearest integer) are compared with the list produced by the lattice enumeration (file given as argument)."""
import sys, re, math
from decimal import Decimal, getcontext
getcontext().prec = 60
L2, L3, L5 = Decimal(2).ln(), Decimal(3).ln(), Decimal(5).ln()
alpha, beta = (L2 / L3).sqrt(), (L2 / L5).sqrt()
HB = int(sys.argv[2]) if len(sys.argv) > 2 else 2048
af, bf = float(alpha), float(beta)
cand = []
for h1 in range(-HB, HB + 1):
    a1 = h1 * af
    for h2 in range(-HB, HB + 1):
        s = a1 + h2 * bf
        h0 = -round(s)
        if h0 == 0 and h1 == 0 and h2 == 0: continue
        hinf = max(abs(h0), abs(h1), abs(h2))
        if hinf > HB: continue
        d = abs(s + h0)
        if d * hinf * hinf <= 0.3:
            cand.append((h0, h1, h2))
def norm(h): return tuple(h) if tuple(h) > tuple(-x for x in h) else tuple(-x for x in h)
brute = set()
for h in cand:
    hv = abs(Decimal(h[0]) + Decimal(h[1]) * alpha + Decimal(h[2]) * beta)
    hinf = max(abs(x) for x in h)
    if hv * hinf * hinf <= Decimal("0.25"):
        brute.add(norm(h))
listed = set()
for line in open(sys.argv[1], encoding="utf8"):
    m = re.match(r"^(\d+)\s+([0-9.e+-]+)\s+([0-9.]+)\s+\S+\s+\[(-?\d+),\s*(-?\d+),\s*(-?\d+)\]", line.strip())
    if m and int(m.group(1)) <= HB and float(m.group(3)) <= 0.25:
        listed.add(norm((int(m.group(4)), int(m.group(5)), int(m.group(6)))))
print("brute force (||h|| <= %d, product <= 1/4): %d vectors; lattice enumeration list: %d vectors" % (HB, len(brute), len(listed)))
print("missing from the list:", sorted(brute - listed)[:10], " extra in the list:", sorted(listed - brute)[:10])
