"""Summarize exhaustive_hv output files: recompute |h.v| ||h||^2 and the exponent for every listed vector in 700-digit arithmetic
and print the minimum product, the maximum exponent for ||h|| >= 10^6, and the number of vectors.  Usage: exhaustive_hv_summary.py file1 [file2 ...]"""
import sys, re
from decimal import Decimal, getcontext
getcontext().prec = 900
L2, L3, L5 = Decimal(2).ln(), Decimal(3).ln(), Decimal(5).ln()
alpha, beta = (L2 / L3).sqrt(), (L2 / L5).sqrt()
rows = []
for fn in sys.argv[1:]:
    for line in open(fn, encoding="utf8"):
        m = re.search(r"\[(-?\d+),\s*(-?\d+),\s*(-?\d+)\]\s*$", line.strip())
        if m and re.match(r"^\d+\s", line):
            h = [int(m.group(i)) for i in (1, 2, 3)]
            hinf = max(abs(x) for x in h)
            hv = abs(Decimal(h[0]) + Decimal(h[1]) * alpha + Decimal(h[2]) * beta)
            rows.append((hv * hinf * hinf, hinf, hv, h))
rows.sort(key=lambda r: r[0])
print("vectors:", len(rows))
print("smallest products |h.v| ||h||^2:")
for p, hinf, hv, h in rows[:5]:
    print("  %.8f  ||h||=%.3e (10^%d)  J=%.4f" % (float(p), float(hinf), len(str(hinf)) - 1, float(-hv.ln() / Decimal(hinf).ln())))
big = [r for r in rows if r[1] >= 10 ** 6]
print("max exponent J over ||h|| >= 1e6: %.4f" % max(float(-r[2].ln() / Decimal(r[1]).ln()) for r in big))
print("largest norm: 10^%d" % (len(str(max(r[1] for r in rows))) - 1))
