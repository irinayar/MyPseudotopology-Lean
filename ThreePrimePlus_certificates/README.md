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

## Transference scripts (v17)

| File | What it does | Output |
|---|---|---|
| `transference_test.py` | Brute-force check of the transference lemma (|h1|,|h2| <= 15 sqrt(n), |h.v| <= 15 delta/sqrt(n)) on random (alpha, beta) | 23 cases, worst ratio 0.001 of the bound |
| `transference_triples.py` | Same for the known close triples with n <= 413 (alpha = sqrt(log2/log3), beta = sqrt(log2/log5)) | `transference_triples_out.txt` |

## Exhaustive exponent range and elementary transference (v18)

| File | What it does | Output |
|---|---|---|
| `exhaustive_hv.py` | EXACT enumeration (LLL + Fincke-Pohst, rational arithmetic) at every dyadic scale H = 2^k of all integer h with ||h||_inf <= H and \|h.v\| <= H^-2, v = (1, sqrt(log2/log3), sqrt(log2/log5)); usage `exhaustive_hv.py KMIN KMAX` | `exhaustive_hv_out_200.txt` (k = 1..200, 43 s), `exhaustive_hv_out_201_600.txt` (k = 201..600, 1232 s; first line starts with a byte-order mark) |
| `exhaustive_hv_summary.py` | Recomputes \|h.v\| ||h||^2 for every listed vector in 900 digits; prints the minimum product, the maximum exponent for ||h|| >= 10^6, the number of vectors | `exhaustive_hv_summary_600.txt`: 1735 vectors, min product 1.17e-4 at ||h|| = 3.3e38, max exponent 2.264 (||h|| >= 1e6), largest norm 10^180 |
| `exhaustive_hv_crosscheck.py` | Brute-force check for ||h|| <= 2048 against the enumeration list | 13 = 13 vectors, identical |
| `orthogonal_plane_test.py` | Elementary transference on 13 known triples: shortest h orthogonal to (n,m,l) has ||h|| <= 2 sqrt n and \|h.v\| <= 2 delta / sqrt n | `orthogonal_plane_test_out.txt` |
| `diameter_scan.py` | Direct check for 10 <= n <= 4e5: minimum log-diameter of (n, m, l) over the neighbours of the nearest integers | min D/sqrt(n) = 0.358 at (29,23,19); no triple with D < 0.5 |
| `transference_test.py`, `transference_triples.py` | Earlier (Minkowski II) version of the transference check | see v17 README rows |

## Independent census by plane enumeration (v18)

| File | What it does | Output |
|---|---|---|
| `census_by_planes.py` | Exhaustive census of the close triples of the explicit window (and of window factor A: diameter <= A W(n)) by exact enumeration of plane normals h (|h.v| <= eta_k, ||h|| <= H_k) and of the lattice points of each plane near the line R v; no continued fractions. Usage `census_by_planes.py KMIN KMAX [A]` | `census_by_planes_out.txt` (A = 1, k = 5..53, 8 s: the 38 triples), `census_by_planes_A{1,2,5,10,100}.txt` (k = 5..60: 38, 161, 758, 2058, 39856 triples), `census_by_planes_A100_61_72.txt` (none) |

| `tvgplus_lemma_checks.py` | Numerical checks of TVGplus_v42's window-kernel lemma (kappa bounds, Fourier positivity) and of the averaged-transfer lemma (exact identity to 2.5e-15, mass estimate) | `tvgplus_lemma_checks_out.txt` |

## Exhaustive range extended to norm 2^3000 (v18)

| File | What it does | Output |
|---|---|---|
| `exhaustive_hv_fast.py` | Same claim as `exhaustive_hv.py` (all h with \|\|h\|\| <= 2^k and \|h.v\| <= 2^-2k, k = KMIN..KMAX) with the reduced basis carried from scale to scale; usage `exhaustive_hv_fast.py 1 3000` (about 12 minutes; the final listing uses exponents of the decimal expansions, no logarithms) | `exhaustive_hv_fast_3000_log.txt` (progress lines every 50 scales), `exhaustive_hv_summary_3000.txt` (summary). The full listing of 8379 vectors is 15 MB and is NOT stored here; it is regenerated by the command above; SHA-256 of the file written by our run: 3ab2cb1420456ce569b6dea70cea54e0c997bb8edc833070f9c773083756190d |
| `exhaustive_hv_summary2.py` | Summary of the listing (number of vectors, smallest products, maximum exponent, largest norm; recomputation of the five smallest products in 3 x digits + 700 digits) | `exhaustive_hv_summary_3000.txt`: 8379 vectors, min product 1.17e-4 at norm 3.3e38, max exponent 2.264 for norm >= 1e6, largest norm 10^903 |

The fast implementation reproduces exactly the 1735 vectors of norm <= 2^600 of the first implementation (checked by set equality).

## Census with the pigeonhole transference box (v18)

`census_by_planes.py` now uses the pigeonhole lemma of `TPPTransfer.lean` (H_k = ceil(sqrt(6N)), eta_k = 2 H_k delta_k / N). Outputs `census_pg_A{1,2,5,10,100}.txt` (blocks k = 5..60, 62, 64, 66, 76): the same lists of 38, 161, 758, 2058, 39856 close triples as before (the earlier outputs `census_by_planes_*.txt` used the Hermite box).
