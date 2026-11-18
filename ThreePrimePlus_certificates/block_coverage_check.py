"""Block-stitching check for the larger-window census (ThreePrimeContinue, proof of the proposition on larger windows).

For the block 2^k <= n < 2^(k+1) one has W(n) = (1+k)^2 log 2.  Theorem (exhaustive range), part (b), gives logarithmic diameter > 9e-6 sqrt(n) for
10^17 <= n <= N_K = 2^6000/3; hence a triple of diameter <= A W(n) cannot exist in the block as soon as 9e-6 2^(k/2) > A (1+k)^2 log 2 and k >= 57.
k0(A) = least k >= 57 such that the inequality holds for all k' in [k, 399] (for k' > 399 it holds a fortiori, 2^(k'/2) beats k'^2).
The census (census_by_planes*.py) covers the blocks 5 <= k <= K_LAST[A].  Coverage requires k0(A) <= K_LAST[A] + 1 (overlap).
Double precision; the smallest relative margin is printed.  Usage: python block_coverage_check.py"""
import math
K_LAST = {1: 60, 2: 62, 5: 64, 10: 66, 100: 76}
ok_all = True
for A, kl in K_LAST.items():
    k0 = None
    for k in range(57, 400):
        if all(9e-6 * 2 ** (j / 2) > A * (1 + j) ** 2 * math.log(2) for j in range(k, 400)):
            k0 = k
            break
    margin = min((9e-6 * 2 ** (j / 2) - A * (1 + j) ** 2 * math.log(2)) / (A * (1 + j) ** 2 * math.log(2)) for j in range(k0, 400))
    covered = k0 is not None and k0 <= kl + 1
    ok_all &= covered
    print("A=%3d  k0=%d  last computed block=%d  covered=%s  smallest relative margin for k>=k0: %.3e" % (A, k0, kl, covered, margin))
print("all windows covered:", ok_all)
