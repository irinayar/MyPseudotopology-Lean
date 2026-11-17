"""Summary of an exhaustive_hv_fast.py output (format: norm, 1e<log10|h.v|>, product, J, [h0, h1, h2]).
Prints the number of vectors, the smallest products |h.v| ||h||^2, the maximum exponent J for ||h|| >= 10^6, the largest norm (digits), and recomputes the
five smallest products in high-precision decimal arithmetic (prec = 3 * digits of the largest norm + 700).  Usage: exhaustive_hv_summary2.py file"""
import sys, re
from decimal import Decimal, getcontext
rows = []
for line in open(sys.argv[1], encoding="utf8"):
    m = re.match(r"^(\d+)\s+1e(-?[0-9.]+)\s+([0-9.]+)\s+([0-9.]+)\s+\[(-?\d+),\s*(-?\d+),\s*(-?\d+)\]\s*$", line.strip())
    if m:
        rows.append((int(m.group(1)), float(m.group(2)), float(m.group(3)), float(m.group(4)), [int(m.group(i)) for i in (5, 6, 7)]))
print("vectors:", len(rows))
rows_p = sorted(rows, key=lambda r: r[2])
maxdig = len(str(max(r[0] for r in rows)))
getcontext().prec = 3 * maxdig + 700   # h.v is about 10^(-2 digits) while the terms are 10^digits: need >= 3 digits + margin
L2, L3, L5 = Decimal(2).ln(), Decimal(3).ln(), Decimal(5).ln()
alpha, beta = (L2 / L3).sqrt(), (L2 / L5).sqrt()
print("smallest products |h.v| ||h||^2 (printed; recomputed in %d digits):" % getcontext().prec)
for r in rows_p[:5]:
    h = r[4]
    hinf = max(abs(x) for x in h)
    hv = abs(Decimal(h[0]) + Decimal(h[1]) * alpha + Decimal(h[2]) * beta)
    prod = hv * hinf * hinf
    print("  %.6f  recomputed %.6f  ||h|| = 10^%d  J = %.4f" % (r[2], float(prod), len(str(r[0])) - 1, r[3]))
big = [r for r in rows if r[0] >= 10 ** 6]
print("max exponent J over ||h|| >= 1e6: %.4f" % max(r[3] for r in big))
print("min product over ||h|| >= 1e30: %.6f" % min(r[2] for r in rows if r[0] >= 10 ** 30))
print("largest norm: 10^%d  (%d digits)" % (maxdig - 1, maxdig))
