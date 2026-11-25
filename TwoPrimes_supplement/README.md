# TwoPrimes: computational supplement

Programs, data and finite certificates for the article

I. Yaroshevskaya, *Two Prime-Square Metrics on the Integers: Completion, Collision Energy and Witness Heights*.

Throughout, `P_p(k) = sup_{n >= 1} || k / p^(n^2) ||`. Section numbers refer to the current text of the article.

## What this supplement does and does not establish

* The computations are **computer-assisted evidence**. Apart from the Lean module named below they are not machine-certified.
* Programs that use exact integer arithmetic are marked **exact**. Programs that use floating point (midpoint quadrature, lattice enumeration in `double`, logarithms in `double`) are marked **floating**.
* None of this proves the open hypotheses (H), (L) or the unit-target bound.

## Lean certificate

`LeanCheck/TwoPrimesWitness.lean` (axiom report: `LeanCheck/TwoPrimesAxioms8.lean`) proves that for **every** `D` from 8 to 3000 the table of the appendix contains an integer `k` with `P_3(k) < 1/D` and `P_2(k-1) < 1/D`. Theorem: `TwoPrimesWitness.unit_witness`. It uses only `propext`, `Classical.choice` and `Quot.sound`.

It certifies the **upper bound** `h_D(1) <= |k|` only. It does **not** certify that no smaller `k` exists.

```sh
lake build LeanCheck.TwoPrimesWitness
lake env lean LeanCheck/TwoPrimesAxioms8.lean
```

## Where minimality of the unit-target heights comes from

Every D from 8 to 3000 is certified by `programs/latcert`, a lattice enumeration that cannot lose a point:

* the Gram-Schmidt data of the reduced basis and the coefficients of the shift are exact integers;
* every real number used to discard a branch is an interval of doubles containing it, rounded outwards after each operation;
* every surviving point is checked with exact integers, and there is no node limit.

This is a **computer-assisted** result: it relies on the correctness of the program, of the .NET runtime and of IEEE-754 arithmetic. It is not checked in Lean and has not been independently audited.

```sh
cd programs/latcert
dotnet run -c Release -- unit 8 3000          # data/certified_unit_run.txt
dotnet run -c Release -- targets 1 1000 10,12,16,18,22,26,28,30,32,36,40,48,64,80,100
dotnet run -c Release -- targets 1 100 128,160,200,256   # data/certified_targets_run.txt (both runs)
```

Independent agreements:

| Range of D | Agreement with |
|---|---|
| D <= 270 | exact Chinese-remainder window search (`witness`), data `exact_minima_window_D62_270.txt` for 62 <= D <= 270 |
| 504 <= D <= 524 | exact window search |
| 525 <= D <= 904 | exact searches reported in the author's earlier manuscript on prime-square metrics (not rerun here) |
| 8 <= D <= 3000 | `lattshift` (floating enumeration of the same lattice): identical values |
| small cases | direct search by increasing absolute value (`latcert brute D t Kmax`): 128 cases with D <= 13, no difference |

## Requirements

.NET SDK 8.0 or later; Perl for the two scripts in `programs/explicit_bound`.

```sh
cd programs/b1check
dotnet run -c Release
```

Arguments follow `--`, for example `dotnet run -c Release -- 20 4194304 0 0`.

## Programs

"Rerun" says what was executed again from these sources when the supplement was assembled.

| Folder | Article | Arithmetic | Command (arguments) | Expected | Rerun |
|---|---|---|---|---|---|
| `latcert` | Section 9, certified minima | exact data, outward-rounded intervals | `unit 8 3000`; `targets t0 t1 D1,D2,...`; `brute D t Kmax` | the values of the unit-target and target tables | yes, all |
| `b1check` | Section 4, example D = 20 | exact | none | 45 positive shifts, E = 25731586, 24.5 %, 54.5 % | yes |
| `digitcheck` | Section 4, digit model | exact | `3 20 10000` | model equals direct set (75 elements) | this case |
| `explicit_bound` | Section 6 | exact | `perl cmp.pl`; `perl chk.pl` | table of bounds; for m = 8 a collision with k = 480, N = 196608 | yes |
| `crtpq` | Sections 7 and 8.5, exact energies | exact | `20 4194304 0 0`; `20 1000000000000 0 0`; `40 1000000000000000 0 0` | E = 36476611; 57992347830509656; 317187602218588562 | these three |
| `crtpq` | Section 8.5, stage heights | exact | `60 stages 1e15 4e17` | C = 1.4048 at X = 307380021558248448 | D = 60 only; other rows are saved data |
| `separated` | Section 7, a route that does not work | floating (logarithms) | none | 7.5, 12.7, 27.2, 74.5 | yes |
| `cutks` | Section 8.1, cut balls | exact sets, floating distance | `20 2 5 200` | ratio distance/bound at most 0.347 | this case; the full sample of the article is not reproducible from a recorded parameter list |
| `oneL2` | Section 8.2 | floating | `18 2 6 3 5 1545342480` | principal part 1.33402 | this case |
| `nonres` | Sections 8.3 and 8.5, certificate | floating | `cert 20 3 3.4 6.0 1.0`; loop in `scripts/certsweep.sh` | one summary line per (D, l), data `certificate_sweep.txt` | yes, all 659 pairs (identical to the original run; no lattice sum exceeds its certificate) |
| `ordscan` | peak law of the cluster model | floating | `100 2 4` | peak 27.574 at order 2 | this case; the 220-case table is not regenerated |
| `ordcrit` | direct check of the cluster model, screening criterion | exact tests, floating sizes | see below | 2773 cases | yes, all |
| `expscan` | rate of the minimal exponent | floating | `3 5 30 100 0.5 2` | supremum 3.3788 on this range | this case |
| `lscheck`, `lscheck2` | Section 8.4, constructed heights | exact | `0.01 3.866 100 140 20`; `2 3 0.01 3.866 100 120 5` | failures = 0 | these cases |
| `gammacheck`, `gammarow` | the bound Gamma_D | floating closed forms, exact first minimum | `2 3 0.01 3.866 100 120 10` | best Gamma = 1.3333; data `gamma_rows.txt` | this case |
| `clmodel` | Section 8.5, lower levels | exact correlation, floating model | `D pA nA JA pB nB JB X` | sample tool | builds and runs |
| `latid` | exact lattice form of the energy | exact counts | `2 3 20 4 3`; `2 3 20 5 4` | E = 4629; E = 2.549708E8 with 81 hull points, 51 with c > 0 | yes |
| `astar2` | screen by pairs of levels | exact continued fractions, floating logarithms | `2 3 600 9 0.01 0.5` | 413 pairs, 35552 usable, cap 242.8, margin 8.95 | first row; all rows in `level_pair_scan.txt` |
| `witness` | Section 9, exact minima | exact | `270 1 1` | least value 1699742784904311585885913089 | this case |
| `lattshift` | unit-target table | floating enumeration, exact check | `8 3000` | data `unit_target_heights_D8_3000.txt` | see data |
| `lattshiftT` | worst case over targets | floating enumeration, exact check | `brute 14 1000000 1`; `targets t0 t1 D1,D2,...` | 195615 | this case; data `target_heights.txt` |
| `modelcount` | heuristic model | exact counts | `brute 20 100000`; `atall <staircase file>` | digit count equals direct count | these |
| `appendix_examples` | appendix examples | exact | none | every line `OK` or the printed values of the appendix | yes |

### The direct check of the cluster model (2773 cases)

For l = 3, 5, 7 and D = 40, 60, 80, 100, 130, 170, 220, 300, 400, run `ordcrit l D D 1` with the environment variables `HDIV=1.25 XLO=0.5 XHI=6.0 LAM=0 HIMAX=60 V=2`; each line starting with `ALL` is a case `D N M JA JB`. Then run `nonres row D 2 N JA l M JB`. The 2773 results are in `data/direct_check_2773_cases.txt`: 72 cases have lambda < 5; the other 2701 have model energy `Ccont` at most 1.7278, mean 1.33, and none reaches 2.

## Data

| File | Content |
|---|---|
| `unit_target_heights_D8_3000.txt` | the staircase `h_D(1)`, D = 8..3000, 56 blocks |
| `certified_unit_run.txt` | output of `latcert unit 8 3000` |
| `certified_targets_run.txt` | output of `latcert targets` (all targets of the worst-case table) |
| `target_heights.txt` | worst case over small targets |
| `exact_minima_window_D62_270.txt` | exact window search for the unit target |
| `stage_energies_pair_2_3.txt` | exact energies at completed stage heights |
| `certificate_sweep.txt` | the numerical certificate for non-resonance, one line per (D, l) |
| `direct_check_2773_cases.txt` | direct check of the cluster model |
| `gamma_rows.txt` | the bound Gamma_D at constructed heights |
| `level_pair_scan.txt` | screen by pairs of levels |
| `suitable_heights_other_pairs.txt` | exact checks of the height construction for other prime pairs |

## Not included

The outputs of the screen over every regular D up to 156000; the rows of the 220-case peak table; interval enclosures and certificates mentioned in the article as coming from independent reviews.
