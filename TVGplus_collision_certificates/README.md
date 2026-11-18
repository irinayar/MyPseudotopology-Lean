# Exact finite collision certificates (TVGplus, two primes)

Programs and outputs behind the two numerical examples of the *finite collision criterion* in `TVGplusJoint_v8` (Proposition "Finite collision criterion for two primes") and `TVGplus_v42`:

For r = 1/D, X a positive integer, A = {k in [0,X] : P_3(k) < r}, B' = {k in [0,X] : P_2(k) < r}, E = #{(a,b,a',b') in A x B' x A x B' : a - b = a' - b'} = |A||B'| + 2 sum_{h>0} r_A(h) r_B(h), L = ceil((|A||B'|)^2 / E). Every integer t with |t| <= 2L - 2X - 2 admits an integer k with |k| <= X, P_3(k) < 2r, P_2(k - t) < 2r.

All numbers below are exact integers produced by exact integer arithmetic (no floating point in the counts or in the target range). Statements about the programs' correctness rest on the small direct checks of `JA_pair_recursion.py` (522 cases against brute-force enumeration, run by `validate()`) and on the agreement of different CRT prefixes; they are not machine-certified.

## Files

| File | Content |
|---|---|
| `JA_pair_recursion.py` | exact recursion `pair_counter(p, D, h)(X)` = number of k in [0, X-h] with k and k+h both in the one-prime ball of radius 1/D; `validate()` compares it with brute force in 522 small cases (`python -c "import JA_pair_recursion as m; print(m.validate())"` prints 522). Unchanged copy of the archived file (its `__main__` part, which writes into the author's local archive, is not used). |
| `crt_collision_certificate.py` | the certificate: counts, energy E, number of candidate shifts, target range `2L-(2X+1)-1`, and the hull range. Usage `crt_collision_certificate.py D X BINARY_LEVEL TERNARY_LEVEL`. Identical to the archived script except for one added line (the `sys.path.insert` for the directory of the script) so that it finds `JA_pair_recursion.py` next to it. |
| `crt_collision_certificate.md` | the author's note on the method (sorted CRT window of residues; exact residue recursion) and on the earlier radii 1/60, 1/70, 1/72. |
| `TVGplusJoint_collision_example_r20_X1e12_prefix43.txt`, `..._prefix53.txt` | outputs for D = 20, X = 10^12 with prefix levels (4,3) and (5,3). |
| `TVGplusJoint_collision_example_r40_X1e15_prefix53.txt`, `..._prefix54.txt` | outputs for D = 40, X = 10^15 with prefix levels (5,3) and (5,4). |

## Commands and results

```
python crt_collision_certificate.py 20 1000000000000 4 3      # about 80 s
python crt_collision_certificate.py 20 1000000000000 5 3      # about 30 s
python crt_collision_certificate.py 40 1000000000000000 5 3   # about 6.6 min
python crt_collision_certificate.py 40 1000000000000000 5 4   # about 20 s
```

| r | X | \|A\| (ternary) | \|B'\| (binary) | E | candidates / contributing | target range 2L-2X-2 |
|---|---|---|---|---|---|---|
| 1/20 | 10^12 | 48511238 | 5912303 | 57992347830509656 | 64402 / 35211 | 836987264164 |
| 1/40 | 10^15 | 1647676973 | 11058338 | 317187602218588562 | 19149 / 1580 | 93329802745946 |

For each example the two prefix choices give byte-identical output. The output of the repository copy of the script (D = 20, X = 10^12, prefix (5,3)) was checked to be identical to the saved file. Python 3.12 (standard library only).

## SHA-256 (of the files as stored in this repository, LF line endings; the two output pairs are identical files)

```
bde5732ec62a96b5e9d4875cbfde5076d39b12b9d6930aef0c59f68a0e182748  JA_pair_recursion.py
8d4897f694ff3c381861ee565f245b1752787c5d5e9108794548a08c91bd9a23  crt_collision_certificate.py
e9447ab3fd6e1cc1a44697e15fc6f8aa66340d6eac50e8928ed9835b193a9121  crt_collision_certificate.md
206fe8f3d1d3b388a99ed25befd9af091e1fd16560da3609f87531c527e2f97f  TVGplusJoint_collision_example_r20_X1e12_prefix43.txt (= prefix53)
69b6b882bcbbdc9bccb457c1670aec90a2c5225e61cb6a0fd7d64fd8b30b98b7  TVGplusJoint_collision_example_r40_X1e15_prefix53.txt (= prefix54)
```
