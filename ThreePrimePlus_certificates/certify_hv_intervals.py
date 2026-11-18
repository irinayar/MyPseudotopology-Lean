"""Interval-arithmetic certificate (pure Python integers, no external library) for the exhaustive enumeration of exhaustive_hv_fast.py.

Two checks, both with rigorous directed rounding (all quantities are integer fixed-point numbers with P fractional bits):
 (1) ENCLOSURE.  Intervals for log 2, log 3, log 5 (from the series 2*atanh(1/m)), then for alpha = sqrt(log2/log3), beta = sqrt(log2/log5).
 (2) SLACK.  For every scale k = 1..KMAX and W = 2^(3k), the integers r_i = round(W v_i) used by the enumeration (recomputed exactly as in
     exhaustive_hv_fast.py, decimal precision int(3*KMAX*0.30103)+400) satisfy |W v_i - r_i| <= 0.5001 for the true v_i (v_0 = 1 trivially).
     With this slack the enumeration radius 10 H^2 is justified: the last coordinate of a lattice vector with |h.v| <= H^-2 and ||h|| <= H
     is at most H + 1.5003 H, so the squared norm is at most 3H^2 + (2.5003H)^2 < 10H^2.
 (3) LIST.  For every vector h of the listing, the interval for h.v does not contain 0 and |h.v| * ||h||^2 >= 1.1e-4 (rigorous lower bound);
     the exponent J = -log|h.v|/log||h|| is bounded above using the lower bound of |h.v|.
Usage: certify_hv_intervals.py LISTING KMAX     (LISTING = exhaustive_hv_fast_3000.txt, KMAX = 3000)"""
import sys, re, math
from decimal import Decimal, getcontext

LISTING, KMAX = sys.argv[1], int(sys.argv[2])
P = 12000                      # fractional bits of the interval arithmetic (about 3612 decimal digits)
ONE = 1 << P

def atanh_inv(m):
    """interval [lo, hi] (scaled by ONE) containing atanh(1/m) = sum_{k>=0} 1/((2k+1) m^(2k+1))."""
    m2 = m * m
    pw = ONE // m                       # floor(ONE / m^(2k+1)), updated by floor division (error < 1 ulp per step)
    s = 0; k = 0; nterms = 0
    # keep the exact integer power instead of repeated floors to keep error <= 1 ulp per term
    den = m
    while True:
        term = ONE // ((2 * k + 1) * den)
        if term == 0: break
        s += term; nterms += 1
        k += 1; den *= m2
    # each term floor-error < 1 ulp; omitted tail: terms below 1 ulp, geometric with ratio <= 1/m2 <= 1/9: total < 1 ulp
    return s, s + nterms + 2

def ivdiv(a, b):                         # a, b positive intervals (scaled): a/b scaled
    return (a[0] * ONE) // b[1], -((-(a[1] * ONE)) // b[0])

def ivsqrt(a):
    return math.isqrt(a[0] * ONE), math.isqrt(a[1] * ONE) + 1

a2 = atanh_inv(3); a3 = atanh_inv(5); a5 = atanh_inv(9)
L2 = (2 * a2[0], 2 * a2[1])
L3 = (L2[0] + 2 * a3[0], L2[1] + 2 * a3[1])          # ln 3 = ln 2 + ln(3/2),  3/2 = (1+1/5)/(1-1/5)
L5 = (2 * L2[0] + 2 * a5[0], 2 * L2[1] + 2 * a5[1])  # ln 5 = 2 ln 2 + ln(5/4), 5/4 = (1+1/9)/(1-1/9)
alpha = ivsqrt(ivdiv(L2, L3)); beta = ivsqrt(ivdiv(L2, L5))
V = [(ONE, ONE), alpha, beta]
def width_bits(iv): return (iv[1] - iv[0]).bit_length()
print("interval widths (bits of ulps):  ln2 %d  ln3 %d  ln5 %d  alpha %d  beta %d" % (width_bits(L2), width_bits(L3), width_bits(L5), width_bits(alpha), width_bits(beta)))
# sanity: compare with decimal evaluation
getcontext().prec = 400
da = (Decimal(2).ln() / Decimal(3).ln()).sqrt(); db = (Decimal(2).ln() / Decimal(5).ln()).sqrt()
assert abs(Decimal(alpha[0]) / Decimal(ONE) - da) < Decimal(10) ** -300 and abs(Decimal(beta[1]) / Decimal(ONE) - db) < Decimal(10) ** -300
print("sanity check against Decimal: ok")

# (2) slack check, r_i recomputed exactly as in exhaustive_hv_fast.py
getcontext().prec = int(3.0 * KMAX * 0.30103) + 400
L2d, L3d, L5d = Decimal(2).ln(), Decimal(3).ln(), Decimal(5).ln()
vd = [Decimal(1), (L2d / L3d).sqrt(), (L2d / L5d).sqrt()]
worst = 0.0
for k in range(1, KMAX + 1):
    W = 1 << (3 * k)
    for i in (1, 2):
        r = int(round(Decimal(W) * vd[i]))
        lo = V[i][0] * W - r * ONE; hi = V[i][1] * W - r * ONE      # W v_i - r_i, scaled by ONE, rigorous interval
        m = max(abs(lo), abs(hi))
        assert m * 10000 <= 5001 * ONE, ("slack violated", k, i)
        worst = max(worst, m / ONE)
print("slack check: |W v_i - r_i| <= 0.5001 for all scales k = 1..%d  (largest observed %.6f)  -> enumeration radius 10 H^2 certified" % (KMAX, worst))

# (3) the listing
rows = []
for line in open(LISTING, encoding="utf-8-sig"):
    m = re.match(r"^(\d+)\s+1e(-?[0-9.]+)\s+([0-9.]+)\s+([0-9.]+|nan)\s+\[(-?\d+),\s*(-?\d+),\s*(-?\d+)\]\s*$", line.strip())
    if m: rows.append((int(m.group(1)), [int(m.group(i)) for i in (5, 6, 7)]))
minprod = None; maxJ = 0.0; maxJ_norm = 0.0
for hinf, h in rows:
    assert hinf == max(abs(x) for x in h)
    lo = hi = 0
    for hi_, (a, b) in zip(h, V):
        if hi_ >= 0: lo += hi_ * a; hi += hi_ * b
        else: lo += hi_ * b; hi += hi_ * a
    assert lo > 0 or hi < 0, ("interval contains 0", h)
    lowabs = lo if lo > 0 else -hi                                   # rigorous lower bound of |h.v|, scaled by ONE
    n2 = hinf * hinf
    assert 100000 * lowabs * n2 >= 11 * ONE, ("product below 1.1e-4", h)
    # product lower bound as a float (ratio of big ints) and exponent J upper bound
    prod_lb = (lowabs * n2 * 10 ** 12 // ONE) / 1e12
    minprod = prod_lb if minprod is None else min(minprod, prod_lb)
    if hinf >= 10 ** 6:
        bl = lowabs.bit_length()
        mant = (lowabs >> (bl - 60)) if bl > 60 else (lowabs << (60 - bl))
        lv = math.log10(mant) + (bl - 60 - P) * math.log10(2)      # log10 of the lower bound of |h.v|
        lh = math.log10(hinf) if hinf < 10 ** 300 else (len(str(hinf)) - 1) + math.log10(float(str(hinf)[:15]) / 10 ** 14)
        J = -lv / lh
        if J > maxJ: maxJ, maxJ_norm = J, lh
print("vectors checked: %d; every interval for h.v excludes 0; rigorous lower bound of the smallest product |h.v| ||h||^2: %.6f" % (len(rows), minprod))
print("every listed vector has |h.v| ||h||^2 >= 1.1e-4 (certified); largest exponent J for ||h|| >= 10^6 (certified upper bound): %.4f at log10||h|| = %.1f" % (maxJ, maxJ_norm))
