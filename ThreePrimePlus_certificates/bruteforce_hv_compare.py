"""Compare the candidates of bruteforce_hv.cs (C#, doubles) with the exact lattice enumeration list: exact filter |h.v| ||h||^2 <= 1/4 in 80-digit arithmetic."""
import sys, re
from decimal import Decimal, getcontext
getcontext().prec = 80
L2, L3, L5 = Decimal(2).ln(), Decimal(3).ln(), Decimal(5).ln()
alpha, beta = (L2 / L3).sqrt(), (L2 / L5).sqrt()
H = int(sys.argv[3])
def norm(h): return tuple(h) if tuple(h) > tuple(-x for x in h) else tuple(-x for x in h)
brute = set()
for line in open(sys.argv[1]):
    p = line.split()
    if len(p) == 3:
        h = tuple(int(x) for x in p)
        hinf = max(abs(x) for x in h)
        hv = abs(Decimal(h[0]) + Decimal(h[1]) * alpha + Decimal(h[2]) * beta)
        if hv * hinf * hinf <= Decimal("0.25"): brute.add(norm(h))
listed = set()
for fn in sys.argv[2].split(","):
    for line in open(fn, encoding="utf8"):
        m = re.search(r"\[(-?\d+),\s*(-?\d+),\s*(-?\d+)\]\s*$", line.strip())
        if m and re.match(r"^\d+\s", line):
            h = tuple(int(m.group(i)) for i in (1, 2, 3))
            if max(abs(x) for x in h) <= H:
                hv_ok = True
                listed.add(norm(h))
# restrict the lattice list to product <= 1/4 as well
def prod(h):
    hinf = max(abs(x) for x in h)
    return abs(Decimal(h[0]) + Decimal(h[1]) * alpha + Decimal(h[2]) * beta) * hinf * hinf
listed25 = {h for h in listed if prod(h) <= Decimal("0.25")}
print("brute force (C#) with exact filter, ||h|| <= %d, product <= 1/4: %d vectors; lattice enumeration list (same range and filter): %d vectors" % (H, len(brute), len(listed25)))
print("missing from the lattice list:", sorted(brute - listed25)[:5], " extra in the lattice list:", sorted(listed25 - brute)[:5])
