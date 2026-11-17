"""LaTeX fragment: for each of the 38 close triples, n, order of the primes of the sorted periods, x = log(Q2/Q1), and
log10 of the lower bound W_z for the largest coordinate of a near-resonant vector:
W_z = max(e^x/4, 0.02 e^(t/4) [n <= 5766], 2500 [n in 32,34,38,43,44,49,50,58 by direct search], 649+1 for n = 35)."""
import math
from decimal import Decimal, getcontext
getcontext().prec = 60
triples = [(32,25,21),(34,27,22),(35,28,23),(38,30,25),(43,34,28),(44,35,29),(49,39,32),(50,40,33),(58,46,38),(64,51,42),(67,53,44),(73,58,48),(87,69,57),(93,74,61),(102,81,67),(116,92,76),(131,104,86),(137,109,90),(160,127,105),(166,132,109),(189,150,124),(195,155,128),(224,178,147),(253,201,166),(282,224,185),(326,259,214),(355,282,233),(384,305,252),(413,328,271),(739,587,485),(768,610,504),(1123,892,737),(2144,1703,1407),(2499,1985,1640),(2883,2290,1892),(3267,2595,2144),(5766,4580,3784),(39268,31191,25770)]
L = {2: Decimal(2).ln(), 3: Decimal(3).ln(), 5: Decimal(5).ln()}
rows = []
for (n, m, l) in triples:
    per = sorted([(Decimal(n * n) * L[2], 2), (Decimal(m * m) * L[3], 3), (Decimal(l * l) * L[5], 5)])
    x = float(per[1][0] - per[0][0]); t = float(per[0][0].sqrt())
    lw = x - math.log(4)
    if n <= 5766:
        lw = max(lw, t / 4 + math.log(0.02))
    if n in (32, 34, 38, 43, 44, 49, 50, 58):
        lw = max(lw, math.log(2500))
    if n == 35:
        lw = max(lw, math.log(650))
    order = "".join(str(p[1]) for p in per)
    rows.append((n, order, x, lw / math.log(10)))
half = (len(rows) + 1) // 2
for i in range(half):
    a = rows[i]
    s = "%d & %s & %.2f & %.1f" % a
    if i + half < len(rows):
        b = rows[i + half]
        s += " & %d & %s & %.2f & %.1f" % b
    print(s + r" \\")
