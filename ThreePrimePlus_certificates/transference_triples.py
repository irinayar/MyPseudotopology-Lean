"""Apply the transference lemma to the known close triples: for z = (n,m,l), delta = max(|m - alpha n|, |l - beta n|),
find by brute force over (h1,h2), |h_i| <= 15 sqrt(n), the minimum of |h0 + h1 alpha + h2 beta| (h0 nearest integer) and compare with
15 delta / sqrt(n).  alpha = sqrt(log2/log3), beta = sqrt(log2/log5) in 60-digit precision rounded to double after reduction."""
import math, sys
from decimal import Decimal, getcontext
getcontext().prec = 60
L2, L3, L5 = Decimal(2).ln(), Decimal(3).ln(), Decimal(5).ln()
alpha_d, beta_d = (L2 / L3).sqrt(), (L2 / L5).sqrt()
alpha, beta = float(alpha_d), float(beta_d)
triples = [(32,25,21),(34,27,22),(35,28,23),(38,30,25),(43,34,28),(44,35,29),(49,39,32),(50,40,33),(58,46,38),(64,51,42),(67,53,44),(73,58,48),(87,69,57),(93,74,61),(102,81,67),(116,92,76),(131,104,86),(137,109,90),(160,127,105),(166,132,109),(189,150,124),(195,155,128),(224,178,147),(253,201,166),(282,224,185),(326,259,214),(355,282,233),(384,305,252),(413,328,271),(739,587,485),(768,610,504)]
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 768
print("   n    delta      15 delta/sqrt(n)   min |h.v| found   ratio   (|h|inf at the minimum)")
for (n, m, l) in triples:
    if n > NMAX:
        continue
    delta = max(abs(float(m - alpha_d * n)), abs(float(l - beta_d * n)))
    R = int(15 * math.sqrt(n)) + 1
    best = 1e9; arg = None
    for h1 in range(-R, R + 1):
        a1 = h1 * alpha
        for h2 in range(-R, R + 1):
            if h1 == 0 and h2 == 0:
                continue
            s = a1 + h2 * beta
            h0 = -round(s)
            v = abs(s + h0)
            if v < best:
                best = v; arg = (h0, h1, h2)
    bound = 15 * delta / math.sqrt(n)
    print("%5d  %.3e   %.3e        %.3e        %.3f   %s" % (n, delta, bound, best, best / bound, arg))
