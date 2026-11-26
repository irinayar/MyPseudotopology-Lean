# A lattice certificate for the energy at D = 10^15

Data and checker for the section "A short lattice basis: the energy at very small radii" of

I. Yaroshevskaya, *Two Prime-Square Metrics on the Integers II*.

Here `p = 2`, `q = 3`, `u = 3^6400`, `v = 2^10201`, and digit number `k` of the prime `l` has the weight
`l^((k-1)^2)` and the range `floor(l^(2k-1)/D)`.

## Files

* `joint_gmp_float_D1000000000000000_s80_t101_h124.json`: a 124 by 124 integer matrix (`basis`) whose rows
  lie in the congruence lattice of the digits 36 to 101 of the prime 2 and 23 to 80 of the prime 3 modulo `u`.
  SHA-256 `5aacc4b96613a5401a2757b85f942aa4e60018da878d862468d7c18c189e2358`. The matrix was found by
  ChatGPT (OpenAI) with lattice reduction; the program which found it is not published here, and nothing
  depends on how it was found.
* `Program.cs`, `basis124.csproj`: a checker which is independent of the search.
* `run.txt`: its output.

## What the checker does

It reads from the file only `D`, `s`, `t`, the selected (prime, index) pairs and the matrix, and recomputes
everything else in exact integer arithmetic:

* the digit lengths and weights, regularity of `D`, and the height conditions;
* the 124 row congruences;
* `|det| = u`, certified by Gaussian elimination modulo many primes together with the bound of Hadamard;
* the column widths and the rational numbers `U`, `L`, `E = (U-1)(1-L)`;
* `E < 0.282780231673` and the energy bound `(4/3)(1+5/D)(1+E) < 1.711`, also at two smaller values of `D`.

The printed ratios `ln(Dv)/ln^2 D` and the sum of the `alpha_j` are floating-point displays and are not used by any
check. The article's window condition `3.4 < ln(Dv)/ln^2 D < 6` on `9*10^14 <= D <= 10^15` is a statement about
these ratios, which the checker displays but does not certify.

## Running it

.NET SDK 8.0 or later.

```sh
cd TwoPrimes_supplement/basis124
dotnet run -c Release -- joint_gmp_float_D1000000000000000_s80_t101_h124.json
```

The last line should be `ALL CHECKS PASSED`.

## Scope

This is a computer-assisted result for one finite range of `D`. It is not checked in Lean. It does not prove
the energy bound for all large `D`.
