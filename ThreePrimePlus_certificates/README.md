# ThreePrimePlus v14: research archive (scripts and outputs)

All scripts are plain Python 3 (standard library only). They were run with the Oracle-bundled Python 3 on Windows.

| File | What it does | Command used | Output |
|---|---|---|---|
| `genW6.py` | Exact lattice certificate (LLL + Fincke-Pohst, rational arithmetic) that no integer vector with a != 0, max coordinate <= 0.02 e^(t/4), has \|a + b rho2 + c rho3\| <= e^(-t/2), for the close triples with n <= 5766 (Proposition "Lattice certificate") | `python genW6.py 32 5766 1/50` | `genW6_out.txt` (n = 32..3267; the run stopped at n = 5766 only because the print statement overflowed a float, fixed afterwards), `genW6_5766.txt` (n = 5766) |
| `brute_check.py` | Independent check without lattice reduction for n <= 58: all (b,c) with \|b\|,\|c\| <= W, the only candidate a being the nearest integer to -(b rho2 + c rho3) | `python brute_check.py 58` | `brute_check_out.txt` (n <= 50; n = 58 gave "none" in a separate run, 29.6 s) |
| `theoremA_numbers.py` | beta, tau, per-triple mass bound 3 beta^2 tau(W_z), truncation terms, totals (Theorem A(d)); window c_w = 0.15 | `python theoremA_numbers.py` | printed table: n = 32: 3.093e-3; n = 34: 1.323e-4; n = 35: 1.523e-6; n >= 38: <= 1.2e-10; total 3.227e-3 |
| `window_numerics.py` | Window numerics (product formula for the Fourier transform of w) | see header | |
| `firstgap_sieve.py` | First-gap sieve for the bounded prefix test (Appendix) | see header | |
| `tiny_search.py` | Window-free search for tiny near-resonant vectors (coordinates in [-2,2]) over all six orders of the primes, first-period index <= 3e6, t >= 26 | `python tiny_search.py 3000000` | `tiny_search_out3e6.txt` (71 pairs with x <= log 8 + 0.2, no residual below 1e-3) |
| `tiny_expect.py` | Poisson expectation of the number of tiny triples (heuristic) | `python tiny_expect.py` | 55 pairs with x <= log 5, expectation 1.8e-5 |
| `claude_indep_bounded_fourier_check.py` | Independent enumeration of the close triples (80-digit Decimal logarithms) for 32 <= n <= 10^5 | `python claude_indep_bounded_fourier_check.py` | reproduces the 38 triples of Table 1 |
| `check_bounded_fourier_intervals.py`, `check_bounded_fourier_large.py` | Codex's certified continued-fraction sieve (outward-rounded interval arithmetic) for the census through 10^40 | see headers | The full execution log of the run through 10^40 is NOT in this folder. |

## What is and is not verified here

* The lattice certificate was rerun by the author's assistant after changing the threshold from e^(-0.41 n) (v11) to the per-triple threshold e^(-t/2); all 37 triples n <= 5766 are certified; the n <= 58 cases were also checked by brute force.
* Floating-point caveat: the numerical constants beta and tau use double precision with a safety factor 1.001 (see Section 2 of the manuscript); they are upper bounds up to rounding but are not interval-arithmetic certificates.
* The census through 10^40 relies on Codex's sieve; only the range n <= 10^5 was reproduced independently.

## Added with the second round (generator bounds, gap table, tail bound)

| File | What it does | Output |
|---|---|---|
| `gaps_table.py` | For the 38 close triples: sorted prime order, t, x = log(Q2/Q1), y, first-gap bound e^x/4, lattice bound 0.02 e^(t/4) | `gaps_table_out.txt` |
| `min_gen.py` | Brute-force list of near-resonant vectors (max coordinate <= 2500) for the triples n <= 58; n = 35 has (-66, 650, 553) as the smallest, no other triple has any | `min_gen_out.txt` |
| `table_gaps.py` | Generates the LaTeX rows of Table 2 (log10 of the generator lower bound W_z) | `table_gaps.tex` |
| `theoremA_numbers2.py` | Theorem A numbers with W_z = max(e^x/4, 0.02 e^(t/4), 2500 for n <= 58 except n = 35, 649 for n = 35): per-triple loss <= 2.91e-47, truncation <= 2.61e-47, sums 2.909e-47 and 2.608e-47 | `theoremA_numbers2_out.txt` |
| `tail_bound.py` | Rigorous bound for the kernel-weight tail beyond r = 4000 (|sin y / y| <= 1/|y|): hat w(4000)^2 <= 1e-101.49, 2 sum_{r>=4000} <= 2.2e-100 | `tail_bound_out.txt` |

## Added after the two audits of 2026-11-17

| File | What it does | Output |
|---|---|---|
| `tail_bound2.py` | Independent rigorous tail bound for sum_{r>=4000} kappa(r) (c_w = 0.15): kappa(r) <= e^4 J^2 e^(-4J), J = floor(sqrt(2 pi c_w r)) (Stirling), counted over r; exact B(4000)^2 = 3.2e-102 | `tail_bound2_out.txt`: 2 * sum <= 5.9e-99 |
| `lattice_count_test.py` | Numerical sanity check of Lemma "Lattice points in a convex set" (|S| <= 2A/covolume + 2 for non-collinear S) on random lattices and thin parallelograms | 177 non-collinear cases, no violation, max |S|/bound = 0.67 |
