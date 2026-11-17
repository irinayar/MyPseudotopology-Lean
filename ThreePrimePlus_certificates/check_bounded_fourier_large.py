"""Screen the wider log-square window by certified continued fractions."""
from math import prod
from itertools import product
from pathlib import Path
import sys

import check_bounded_fourier_intervals as iv

previous = Path(__file__).resolve().parents[1] / "tvgplus_v31_research_20261109"
sys.path.insert(0, str(previous))
from continued_fraction_triples import ALPHA, BETA, candidate_indices, near_indices


def screen(limit, bound):
    tested = rejected = scanned = 0
    largest = None
    for j in range(5, limit.bit_length()):
        lo, hi = 2**j, min(2**(j+1)-1, limit)
        bits = (j+1)**2
        # A log difference <= bits*log(2) gives |n*alpha-m|
        # <= bits*log(2)/(n*sqrt(log(2)*log(3))) < 2*bits/lo.
        width_num = 2*bits
        for n in candidate_indices(lo, hi, width_num):
            scanned += 1
            for m, ell in product(near_indices(n, ALPHA, width_num, lo),
                                  near_indices(n, BETA, width_num, lo)):
                indices = n, m, ell
                q = sorted(iv.log_level(p, k) for p, k in zip(iv.PRIMES, indices))
                if q[-1][0]-q[0][1] > bits*iv.logs[2][1]:
                    continue
                assert q[-1][1]-q[0][0] <= bits*iv.logs[2][0]
                assert all(x[1] < y[0] for x, y in zip(q, q[1:]))
                future = [iv.log_level(p, k+1) for p, k in zip(iv.PRIMES, indices)]
                prior = [iv.log_level(p, k-1) for p, k in zip(iv.PRIMES, indices)]
                nxt = min(x[0] for x in future), min(x[1] for x in future)
                assert max(x[1] for x in prior) < q[0][0] and q[-1][1] < nxt[0]
                tested += 1
                largest = max(largest or indices, indices)
                found = list(iv.initial_test(q, nxt, bound))
                if found:
                    print("not excluded", indices, found, flush=True)
                else:
                    rejected += 1
    print("through", limit, "B", bound, "sieve candidates", scanned,
          "close triples", tested, "rejected", rejected, "largest", largest)
    assert tested == rejected


if __name__ == "__main__":
    screen(int(sys.argv[1]), int(sys.argv[2]))
