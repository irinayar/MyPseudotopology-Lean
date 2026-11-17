"""First-gap sieve for the bounded three-level prefix test (ThreePrimePlus Section 2, eq. prefix).

Necessary condition (elementary): if |a1/Q1 + a2/Q2 + a3/Q3| < (6B+1)/Q4 with a1 != 0, |a_j| <= B, and
Q1 < Q2 < Q3 < Q4 are consecutive periods, then Q2/Q1 <= 8B+1.  [Proof: 1/Q1 <= |a1/Q1|
<= |a2|/Q2 + |a3|/Q3 + (6B+1)/Q4 <= 2B/Q2 + (6B+1)/Q4, and (6B+1)/Q4 <= 1/(2 Q1) for large Q4/Q1, so Q2/Q1 <= 8B+1.]
Hence only pairs (p^(j^2), q^(j'^2)) of different primes with |j'^2 log q - j^2 log p| <= T = log(8B+1) matter.
This script enumerates all such pairs with j <= JMAX through continued fractions (Worley-type enumeration of the
fractions j'/j with |theta - j'/j| <= C/j^2, intermediate fractions r*p_{k+1} +- s*p_k, cross-checked by brute force),
then tests each consecutive triple exactly with high-precision decimals.
"""
import sys
from decimal import Decimal, getcontext
from math import isqrt

B = int(sys.argv[1]) if len(sys.argv) > 1 else 128
DIG = int(sys.argv[2]) if len(sys.argv) > 2 else 60      # JMAX = 10^DIG
BRUTE = int(sys.argv[3]) if len(sys.argv) > 3 else 2000000
PREC = 2 * (2 * DIG + 40) + 200
getcontext().prec = PREC
LN = {p: Decimal(p).ln() for p in (2, 3, 5)}
T = Decimal(8 * B + 1).ln()
S = 12          # r,s range of intermediate fractions (Worley: r*s < 2c, c ~ 3.6, so r,s <= 7 suffices; S is generous)


def cf_convergents(theta, limit_digits):
    """convergents (p,q) of theta, computed from a rational approximation of theta with PREC-60 digits."""
    scale = 10 ** (PREC - 60)
    num = int((theta * scale).to_integral_value())
    den = scale
    h0, h1, k0, k1 = 0, 1, 1, 0
    out = []
    a, b = num, den
    while b:
        t = a // b
        a, b = b, a - t * b
        h0, h1 = h1, t * h1 + h0
        k0, k1 = k1, t * k1 + k0
        out.append((h1, k1))
        if k1 > 10 ** (limit_digits + 3) or k1 * k1 > scale // 10 ** 10:
            break
    return out


def x_of(p, q, j, jp):
    """|j'^2 log q - j^2 log p| for index j of p and j' of q."""
    return abs(Decimal(jp * jp) * LN[q] - Decimal(j * j) * LN[p])


def candidates(p, q, jmax):
    theta = (LN[p] / LN[q]).sqrt()
    conv = cf_convergents(theta, DIG)
    found = {}
    cs = [(1, 0)] + [(h, k) for h, k in conv]          # p_{-1}/q_{-1} = 1/0 trick not needed; keep convergents only
    cs = conv
    for i in range(len(cs) - 1):
        (pa, qa), (pb, qb) = cs[i], cs[i + 1]
        for r in range(0, S + 1):
            for s in range(0, S + 1):
                if r == 0 and s == 0:
                    continue
                for sg in (1, -1):
                    b = r * qb + sg * s * qa
                    a = r * pb + sg * s * pa
                    if b <= 0 or b > jmax:
                        continue
                    x1 = x_of(p, q, b, a)
                    if x1 == 0:
                        continue
                    gmax = int((T / x1).sqrt().to_integral_value()) + 1
                    for g in range(1, min(gmax, 2000) + 1):
                        if g * b > jmax:
                            break
                        j, jp = g * b, g * a
                        if x_of(p, q, j, jp) <= T:
                            found[(j, jp)] = 1
    # also the convergents themselves (r=1,s=0 at every level) and their multiples are included above
    return sorted(found)


def brute(p, q, jmax):
    from decimal import localcontext
    out = []
    with localcontext() as ctx:
        ctx.prec = 50
        lp, lq, TT = +LN[p], +LN[q], +T
        theta = (lp / lq).sqrt()
        for j in range(1, jmax + 1):
            jp = int((theta * j).to_integral_value())
            for c in (jp - 1, jp, jp + 1):
                if c >= 1 and abs(Decimal(c * c) * lq - Decimal(j * j) * lp) <= TT:
                    out.append((j, c))
    return out


def periods_log(p, idx):
    return Decimal(idx * idx) * LN[p]


def next_periods_above(r, val, count=2):
    """the `count` smallest log-periods of chain r that exceed `val` (a Decimal)."""
    idx = int((val / LN[r]).sqrt().to_integral_value())
    while periods_log(r, idx) > val and idx > 1:
        idx -= 1
    while periods_log(r, idx) <= val:
        idx += 1
    return [(periods_log(r, idx + i), r, idx + i) for i in range(count)]


def test_triple(p, q, j, jp, report):
    primes = (2, 3, 5)
    lp, lq = periods_log(p, j), periods_log(q, jp)
    (l1, p1, i1), (l2, p2, i2) = sorted([(lp, p, j), (lq, q, jp)])
    # Q1 = smaller, Q2 = larger; check consecutiveness against the third chain and the neighbours
    third = [r for r in primes if r not in (p, q)][0]
    cands = []
    for r in primes:
        cands += next_periods_above(r, l2, 2)
    cands.sort()
    # nothing of any chain may lie strictly between Q1 and Q2
    for r in primes:
        for idx in (i1 + 1, i2 - 1):
            pass
    inside = False
    for r in primes:
        idx = int((l1 / LN[r]).sqrt().to_integral_value())
        for t in range(max(idx - 2, 1), idx + 3):
            v = periods_log(r, t)
            if l1 < v < l2:
                inside = True
    if inside:
        return "notconsecutive"
    l3, l4 = cands[0][0], cands[1][0]
    x, y, z = l2 - l1, l3 - l1, l4 - l1
    rho2 = (-x).exp()
    # necessary bound for passing: min_{a1,a2} |a1 + a2 rho2| <= (7B+1) e^{-y}
    # (pass => |a1 + a2 rho2| <= B rho3 + (6B+1) rho4 <= (7B+1) e^{-y}).
    # Low-precision value of the minimum, nearest a1 for every a2.
    from decimal import localcontext
    with localcontext() as ctx:
        ctx.prec = 60
        r2 = +rho2
        best = Decimal(2) * B
        for a2 in range(-B, B + 1):
            v = a2 * r2
            n0 = int((-v).to_integral_value())
            for a1 in (n0 - 1, n0, n0 + 1):
                if 1 <= a1 <= B:
                    R = abs(a1 + v)
                    if R < best:
                        best = R
        ybig = y > Decimal(130 * 2.3026)          # e^{-y} < 1e-130
    if ybig and best > Decimal(10) ** -40:
        return "rejected"
    thr_y = Decimal(7 * B + 1) * (-y).exp() if y < PREC * 2 else Decimal(0)
    if best > Decimal(10) ** -40 and best > thr_y * 10:
        return "rejected"
    if best <= Decimal(10) ** -40:
        report.append(("UNRESOLVED small minimum", p, q, j, jp, str(best)))
        return "tested-exact"
    # exact check of all (a1,a2,a3)
    rho3 = (-y).exp()
    thr = Decimal(6 * B + 1) * (-z).exp()
    for a1 in range(1, B + 1):
        for a2 in range(-B, B + 1):
            Rp = a1 + a2 * rho2
            a3 = -int((Rp / rho3).to_integral_value())
            for c3 in (a3 - 1, a3, a3 + 1):
                if abs(c3) <= B and abs(Rp + c3 * rho3) < thr:
                    report.append((p, q, j, jp, a1, a2, c3))
    return "tested-exact"


def main():
    jmax = 10 ** DIG
    total = {"rejected": 0, "notconsecutive": 0, "tested-exact": 0}
    passing = []
    biggest = 0
    for (p, q) in ((2, 3), (2, 5), (3, 5)):
        cand = candidates(p, q, jmax)
        # brute-force cross-check on the range j <= BRUTE
        bf = set(c for c in brute(p, q, min(BRUTE, jmax)) if min(c) >= 32)
        cs = set(c for c in cand if c[0] <= BRUTE and min(c) >= 32)
        missing = bf - cs
        print("pair", (p, q), "candidates", len(cand), "brute-force pairs j<=%d:" % BRUTE, len(bf), "missing from enumeration:", len(missing))
        for (j, jp) in [c for c in cand if min(c) >= 32]:
            res = test_triple(p, q, j, jp, passing)
            total[res] += 1
            biggest = max(biggest, j)
    print("JMAX = 10^%d, B = %d" % (DIG, B))
    print("triples tested:", total, " passing vectors:", len(passing), " largest index of the first-listed prime:", len(str(biggest)), "digits")
    for t in passing[:20]:
        print("PASS", t)


main()
