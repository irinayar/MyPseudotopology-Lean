"""Conservative interval certificate for the bounded initial Fourier test."""
from decimal import Decimal, ROUND_FLOOR, ROUND_CEILING, getcontext
from math import isqrt
import sys

DIGITS = 160
SCALE = 10**DIGITS
getcontext().prec = 210
PRIMES = (2, 3, 5)


def ceil_div(a, b):
    return -((-a)//b)


def scaled_bounds(x):
    return (
        int(x.next_minus().scaleb(DIGITS).to_integral_value(ROUND_FLOOR)),
        int(x.next_plus().scaleb(DIGITS).to_integral_value(ROUND_CEILING)),
    )


# Decimal ln and exp are correctly rounded. Adjacent representable
# values enclose each exact output. Scaling here shifts the decimal point.
logs = {p: scaled_bounds(Decimal(p).ln()) for p in PRIMES}


def log_level(p, j):
    l, u = logs[p]
    return j*j*l, j*j*u


def odd_range(n, p, width):
    lower, upper = log_level(2, n)
    p_lower, p_upper = logs[p]
    first = isqrt(max(0, (lower-width)//p_upper))
    last = isqrt((upper+width)//p_lower)
    return range(max(1, first), last+1)


def ratio_bounds(den, num):
    """Return scaled bounds on exp(log(num)-log(den))."""
    lower = Decimal(num[0]-den[1]).scaleb(-DIGITS)
    upper = Decimal(num[1]-den[0]).scaleb(-DIGITS)
    return scaled_bounds(lower.exp())[0], scaled_bounds(upper.exp())[1]


def initial_test(q, nxt, bound):
    q1, q2, q3 = q
    r2l, r2u = ratio_bounds(q2, q1)
    r3l, r3u = ratio_bounds(q3, q1)
    tol = (6*bound+1) * ratio_bounds(nxt, q1)[1]
    slack = bound*(r3u-r3l)
    assert r3l > 0
    for a in range(1, bound+1):
        for b in range(-bound, bound+1):
            lo = a*SCALE + b*(r2l if b >= 0 else r2u)
            hi = a*SCALE + b*(r2u if b >= 0 else r2l)
            first = max(-bound, ceil_div(-tol-hi-slack, r3l))
            last = min(bound, (tol-lo+slack)//r3l)
            if first <= last:
                yield a, b, first, last


def scan(nmax, bound):
    tested = rejected = uncertain_diameter = 0
    for n in range(32, nmax+1):
        bits = n.bit_length()**2
        width = bits*logs[2][1]
        for m in odd_range(n, 3, width):
            for ell in odd_range(n, 5, width):
                indices = (n, m, ell)
                q = sorted(log_level(p, j) for p, j in zip(PRIMES, indices))
                if q[-1][0]-q[0][1] > width:
                    continue
                assert all(x[1] < y[0] for x, y in zip(q, q[1:]))
                if q[-1][1]-q[0][0] > bits*logs[2][0]:
                    uncertain_diameter += 1
                successors = [log_level(p, j+1) for p, j in zip(PRIMES, indices)]
                predecessors = [log_level(p, j-1) for p, j in zip(PRIMES, indices)]
                nxt_l = min(x[0] for x in successors)
                nxt_u = min(x[1] for x in successors)
                assert max(x[1] for x in predecessors) < q[0][0]
                assert q[-1][1] < nxt_l
                tested += 1
                possible = list(initial_test(q, (nxt_l, nxt_u), bound))
                if possible:
                    print("not excluded by intervals", indices, possible, flush=True)
                else:
                    rejected += 1
    print(nmax, bound, tested, rejected, uncertain_diameter, flush=True)
    assert tested == rejected


if __name__ == "__main__":
    scan(int(sys.argv[1]), int(sys.argv[2]))
