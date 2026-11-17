"""For each of the 38 close triples: sorted periods, t = sqrt(log Q1), gaps x = log(Q2/Q1), y = log(Q3/Q1),
first-gap bound W_fg = e^x/4 (any near-resonant vector has max(|b|,|c|) >= W_fg), lattice bound W_lat = 0.02 e^(t/4)
(n <= 5766 only), and the combined bound W = max(W_fg, W_lat)."""
import math
from decimal import Decimal, getcontext
getcontext().prec = 60
triples = [(32,25,21),(34,27,22),(35,28,23),(38,30,25),(43,34,28),(44,35,29),(49,39,32),(50,40,33),(58,46,38),(64,51,42),(67,53,44),(73,58,48),(87,69,57),(93,74,61),(102,81,67),(116,92,76),(131,104,86),(137,109,90),(160,127,105),(166,132,109),(189,150,124),(195,155,128),(224,178,147),(253,201,166),(282,224,185),(326,259,214),(355,282,233),(384,305,252),(413,328,271),(739,587,485),(768,610,504),(1123,892,737),(2144,1703,1407),(2499,1985,1640),(2883,2290,1892),(3267,2595,2144),(5766,4580,3784),(39268,31191,25770)]
L = {2: Decimal(2).ln(), 3: Decimal(3).ln(), 5: Decimal(5).ln()}
print("   n    order   t        x        y      log W_fg   log W_lat   log W")
for (n, m, l) in triples:
    per = sorted([(Decimal(n * n) * L[2], 2), (Decimal(m * m) * L[3], 3), (Decimal(l * l) * L[5], 5)])
    x, y = per[1][0] - per[0][0], per[2][0] - per[0][0]
    t = per[0][0].sqrt()
    lw_fg = float(x) - math.log(4)
    lw_lat = float(t) / 4 + math.log(0.02) if n <= 5766 else float("-inf")
    order = "".join(str(p[1]) for p in per)
    print("%6d  %s  %8.2f %8.3f %8.3f  %8.2f  %8.2f  %8.2f" % (n, order, float(t), float(x), float(y), lw_fg, lw_lat, max(lw_fg, lw_lat)))
