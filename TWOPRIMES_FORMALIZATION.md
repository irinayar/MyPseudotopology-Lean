# TwoPrimes: Lean checks for the two-prime square-chain metrics (21 November 2026)

Modules: `LeanCheck/TwoPrimesTransfer.lean`, `TwoPrimesBall.lean`, `TwoPrimesTable.lean` (axiom report `TwoPrimesAxioms.lean`), `TwoPrimesRange.lean`, `TwoPrimesChildren.lean`, `TwoPrimesMonotone.lean` (axiom report `TwoPrimesAxioms2.lean`) and, added on 23 November 2026 for TwoPrimes_v5, `TwoPrimesFejer.lean`, `TwoPrimesUnimodal.lean`, `TwoPrimesCutBall.lean` (axiom report `TwoPrimesAxioms3.lean`; these three need only Mathlib) and, added on 23 November 2026 for TwoPrimes_v7, `TwoPrimesBlock.lean` (axiom report `TwoPrimesAxioms4.lean`; needs only Mathlib) and, added on 23 November 2026 for TwoPrimes_v8, `TwoPrimesLevels.lean` (axiom report `TwoPrimesAxioms5.lean`; needs only Mathlib) and, added on 23 November 2026 for TwoPrimes_v9, `TwoPrimesSweep.lean` (axiom report `TwoPrimesAxioms6.lean`; needs only Mathlib). Typechecked with Lean 4.35.0 and Mathlib, no `sorry`; every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`. The modules use only the layer `MixedPrimeBasics`, `MixedPrimeRadii`, `MixedPrimeSplit` (the pseudonorm `Pn S k = sup_{q ∈ S} ‖k/q‖`, the scale sets `sqScales ℓ = {ℓ^(n²)}`, subadditivity and `Pn (m k) ≤ |m| Pn k`); no diagonal density and no analysis is assumed.

Notation: `P_ℓ = Pn (sqScales ℓ)`. For a radius `η`, an integer `m` is a witness for the unit target if `Pn S3 m < η` and `Pn S2 (m - 1) < η`.

| Declaration | Statement |
|---|---|
| `transfer_unit` | `S2, S3` nonempty, `t ≠ 0`, `m` a witness for the unit target at radius `η` ⟹ `Pn S3 (t m) < |t| η` and `Pn S2 (t m - t) < |t| η`. |
| `transfer_height` | If moreover `|m| ≤ H`, there is `k` with `|k| ≤ |t| H` and the same two bounds; so `h_ε(t) ≤ |t| h_{ε/|t|}(1)` for the least witness heights. |
| `witness_mono` | A witness at radius `η` is a witness at every radius `η' ≥ η` (monotonicity of `h_ε`). |
| `transfer_unit_sq` | `transfer_unit` for `S3 = sqScales 3`, `S2 = sqScales 2`. |
| `half_ratio_bounds` | For `Q ≥ 2`: `1/3 ≤ ⌊Q/2⌋/Q ≤ 1/2`. |
| `nrm_far_multiple` | For `ℓ ≥ 2`, `b < n²`: `‖ ℓ^b ⌊ℓ^(n²-b)/2⌋ / ℓ^(n²) ‖ ≥ 1/3`. |
| `exists_far_multiple` | For `ℓ ≥ 2` and every `b` there is a multiple `k` of `ℓ^b` with `Pn (sqScales ℓ) k ≥ 1/3`. |
| `no_adic_nbhd_in_ball` | For `δ ≤ 1/3` the ball `{P_ℓ < δ}` contains no `ℓ`-adic neighbourhood `ℓ^b ℤ` of `0`: the topology of `(ℤ, P_ℓ)` is strictly finer than the `ℓ`-adic topology (the finer-than part is `MixedPrime.valuation_bound`). |
| `ExplicitOK`, `explicit_m8`, `explicit_m16`, `explicit_m32`, `explicit_m64` | Exact arithmetic side conditions of the refined explicit null-witness bound `u(1/m) ≤ N = 2^(a₂²) 3^(a₃²) (2m)^d` (minimality of `a₂, a₃`, and `2 m N < 2^((R₂+1)²)`, `2 m N < 3^((R₃+1)²)`) for `m = 8, 16, 32, 64`, with `N = 805306368` at `m = 8`. The pigeonhole step is not part of Lean. |
| `near_coincidence_5_4` | `128·2^25 < 100·3^16 < 129·2^25`: the square levels `2^25` and `3^16` differ by a factor in `(1.28, 1.29)`. |
| `card_le_of_cover` | Finite sets `A, B` of integers such that every `t` with `|t| ≤ M` is `a - b` with `a ∈ A`, `b ∈ B` satisfy `2M + 1 ≤ |A||B|` (the counting step of the theorem that the exponent of the range claim is at least `x_S`). |
| `unit_target_dvd`, `Pn_three_one`, `unit_target_lower` | If `P₃(k) < ε ≤ 1/3`, `P₂(k - 1) < ε` and `ε ≤ 2^(-(2⌊√(a-1)⌋+1))` (`a ≥ 1`), then `2^a ∣ k - 1` and `2^a ≤ |k - 1|`; `P₃(1) ≥ 1/3` (uses `MixedPrime.valuation_bound`). |
| `nrm_ge_of_mem_Icc`, `gap_ge`, `exists_gap` | `ε 2^(n²) ≤ k ≤ (1 - ε) 2^(n²)` implies `P₂(k) ≥ ε`; for `0 ≤ ε < 1/2` and every `H` there is `s` such that no integer `b` with `|b - s| ≤ H` has `P₂(b) < ε` (the ball has arbitrarily long gaps; basis of "no bound is uniform in the target"). |
| `children_iff` | `r ≤ θ ≤ 1 - r`, `|s| < r`: `|j + s| < J + θ ↔ |j| ≤ J` for integers `j`, natural `J`. |
| `not_dvd_pow_of_not_pow`, `children_of_regular` | `D` not a power of the prime `ℓ` implies `D ∤ ℓ^m`; for `D ≥ 2` not a power of `ℓ` and `|s| < 1/D`: `|j + s| < ℓ^m / D ↔ |j| ≤ ⌊ℓ^m / D⌋` (Lemma 4.1 of TwoPrimes_v2, the child count of the digit model). |
| `fib`, `card_diff_eq`, `card_same_eq`, `card_diff_le` | In a finite abelian group `G` with `φ : X → G`: `#{(x, x') : φ x - φ x' = d} ≤ #{(x, x') : φ x = φ x'}` (Cauchy-Schwarz on the fibre sizes). |
| `collision_le` | `#{(x, y, x', y') : φ x + ψ y = φ x' + ψ y'} ≤ |Y|² #{(x, x') : φ x = φ x'}`: the collision probability of a sum is at most that of one summand (Lemma G1, finite abelian group form; the integer case follows by reducing modulo a large integer, not formalized). |

Added for TwoPrimes_v5 (Section 8 of the article; elementary finite statements only):

| Declaration | Statement |
|---|---|
| `eq_of_modEq_of_mem_Icc`, `card_congr_pairs` | For naturals `J, N` with `2J < N`: two integers of `[-J, J]` that are congruent modulo `N` are equal, and exactly `2J + 1` pairs of `[-J, J]²` are congruent modulo `N` (the counting core of the Fejer averaging identity `∑_{r mod N} F_J(r/N) = N/(2J+1)`; the trigonometric form is not formalized). |
| `unimodal_sum_le_integral_add_max` | If `f : ℝ → ℝ` is monotone on `[x₀, x₀+p]` and antitone on `[x₀+p, x₀+p+q]` then `∑_{i=0}^{p+q} f(x₀+i) ≤ ∫_{x₀}^{x₀+p+q} f + f(x₀+p)` (sum of a unimodal function ≤ integral + maximum; the chord-sum step of the lattice-point lemma). |
| `cluster_mid_card_le_one`, `cut_count_bounds` | For a union of clusters `j q + Y j` (`j ∈ I`, `Y j ⊂ [-U, U]`, `0 < q`, `2U < q`) and every integer `x`: at most one cluster is cut by `x` (`j q - U ≤ x < j q + U`), and the number of elements `≤ x` lies between the total size of the clusters with `j q + U ≤ x` and that total plus `M` when every cluster has at most `M ≥ 0` elements (the discrete counting step of the near-uniformity theorem for cut balls, Theorem 8.1 of TwoPrimes_v5). |

Added for TwoPrimes_v7 (Section 7, block collision lemma; elementary finite statements only):

| Declaration | Statement |
|---|---|
| `occupancy_le_nat`, `occupancy_le` | A finite set `S` of integers inside a window `[a, b]` of `N = b - a + 1` consecutive integers such that no `x ∈ S` has `x + t ∈ S` (`t ≠ 0`, or `t = T > 0` natural) satisfies `2 |S| ≤ N + |t|` (the occupancy bound `n_i ≤ (X/K + |t| + 1)/2` of Proposition 7.3 of TwoPrimes_v7). |
| `block_cs` | `(∑_{n ∈ S} μ n)^2 ≤ |S| ∑_{n ∈ S} (μ n)^2` for real `μ` on a finite set of integers (Cauchy-Schwarz on one block). |

Added for TwoPrimes_v8 (Section 8.4, level-structure proposition; elementary steps only):

| Declaration | Statement |
|---|---|
| `two_floor_add_one_ge` | For a real `ρ ≥ 1`: `ρ ≤ 2 ⌊ρ⌋ + 1` (so `2 J_n + 1 ≥ ρ_n` when `ρ_n ≥ 1`). |
| `sum_odd_Ico` | For naturals `n₀ ≤ N`: `∑_{n ∈ [n₀, N)} (2 n - 1) = (N-1)^2 - (n₀-1)^2` in `ℤ` (the exponent bookkeeping in the lower bound for `|A|`). |

Added for TwoPrimes_v9 (Section 8.4, level structure for general pairs of primes; elementary step only):

| Declaration | Statement |
|---|---|
| `sweep_decrease`, `sweep_bound` | Real phases `φ j` (`j < K`) all in the zone `(a-2, 2)` with `2 < a`, each step `φ (j+1) = φ j + a` or `φ j + a - b`, satisfy `φ j = φ 0 - j (b - a)` and `(K-1)(b-a) < 4 - a`: among `K` consecutive levels with `(K-1)(b-a) ≥ 4 - a` one is outside the zone (the circle step in the choice of levels). |

Added for TwoPrimes_v16 (Section 6, explicit null-witness bound with arcs of length `1/m`; module `TwoPrimesTable2`):

| Declaration | Statement |
|---|---|
| `arc_diff_lt` | For real `m > 0` and reals `x, y` with `⌊m x⌋ = ⌊m y⌋`: `|x - y| < 1/m` (two points of one half-open arc of length `1/m` differ by less than `1/m`; the arc step of the pigeonhole argument). |
| `ExplicitArcsOK`, `arcs_m8`, `arcs_m16`, `arcs_m32`, `arcs_m64` | Arithmetic side conditions of the explicit bound with `m` arcs, `N = 2^(a₂²) 3^(a₃²) m^d`, `m N < 2^((R₂+1)²)`, `m N < 3^((R₃+1)²)` for `(m; a₂, a₃, R₂, R₃, d) = (8; 2,1,4,3,4), (16; 2,1,5,4,6), (32; 3,2,7,5,7), (64; 3,2,8,6,9)`, and `2^4 · 3 · 8^4 = 196608`. The pigeonhole step itself is not formalized. |

Not formalized (stated in the TwoPrimes notes): the real-analysis part of the level-structure proposition (choice of the levels by the sweep over three consecutive `N`, asymptotics with logarithms), the comparison of the difference distribution with the triangular law, the block masses and the final assembly of the block collision lemma; the digit-set model of the balls as a whole (only its child count, `children_of_regular`, is checked) and the product formula for their autocorrelation, the collision-energy computations and certificates (computer-assisted, exact integer arithmetic, outside Lean), the completion `X_p` and its identification with `{x ∈ ℤ_p : ‖f_n(x)‖ → 0}`, non-local-compactness of `X_p`, the pigeonhole step of the explicit bound, and the energy estimate `C(r,X) ≤ 8/3 − δ` (open). Also not formalized from v5: the analytic parts of the near-uniformity theorem for cut balls (comparison of the linear function with the uniform law, the Kolmogorov distance), the principal Fourier part (Fourier analysis), the planar lattice-point lemma (needs Minkowski's second theorem, the Brunn-Minkowski and Rogers-Shephard inequalities), the layer-cake theorem for log-concave weights, and all computer-assisted certificates.

To recheck: `lake build` and `#print axioms` for each declaration above (`TwoPrimesAxioms.lean`, `TwoPrimesAxioms2.lean`, `TwoPrimesAxioms3.lean`, `TwoPrimesAxioms4.lean`, `TwoPrimesAxioms5.lean`, `TwoPrimesAxioms6.lean`, `TwoPrimesAxioms7.lean`).

## Unit-target witnesses (module `TwoPrimesWitness`, appendix table of unit-target heights)

| Declaration | Statement |
|---|---|
| `Small p D x` | for every `n ≥ 1` some multiple of `p^(n²)` is closer to `x` than `p^(n²)/D` (that is, `‖x/p^(n²)‖ < 1/D`; the values tend to 0, so this is `P_p(x) < 1/D`). |
| `small_of_check` | a finite test (levels `1..N` and `D·|x| < p^((N+1)²)`) implies `Small p D x`. |
| `unit_witness` | for every `D` with `8 ≤ D ≤ 3000` a row of the explicit table gives `k` with `Small 3 D k` and `Small 2 D (k-1)`. |

This certifies upper bounds `h_D(1) ≤ |k|` for the least witness height. **Minimality is not formalized.** Axiom report: `TwoPrimesAxioms8.lean` (only `propext`, `Classical.choice`, `Quot.sound`). The programs and data of the article are in `TwoPrimes_supplement/`.

## Appendix statements and lattice completeness (module `TwoPrimesAppendix`)

| Declaration | Statement |
|---|---|
| `box_sqnorm_lt`, `partial_le_sqnorm`, `coeff_expansion`, `no_point_lost` | the proposition "No lattice point is lost": if `w + ∑ z_i b_i` lies in the open box `(-1,1)^n`, every partial sum of the squared Gram–Schmidt terms is below `n`. The interval arithmetic and the program `latcert` are **not** formalized. |
| `fibre_card`, `sum_sq_formula`, `parity_energy`, `parity_disjoint` | the parity family showing that the threshold 8/3 is sharp: multiplicities `m - |d|`, the sum `3(m^2 + 2 ∑ (m-k)^2) = m(2m^2+1)`, and disjointness. The assembly into the energy of the two sets and the Kolmogorov distance are not formalized. |
| `peak_sum` | the finite sum in the resonance-peak formula (the reduction to this sum is not formalized). |
| `decomposition` | the exact three-term identity for `C - C_model`, as algebra in the two weighted sums. |
| `nrm_sub_le`, `chain_estimate` | `‖(x - r)/q‖ ≤ ‖x/q‖ + b_N/b_{N+1}`, the approximation estimate of the general divisibility chain (the completion statement is not formalized). |

Axiom report: `TwoPrimesAxioms9.lean` (only `propext`, `Classical.choice`, `Quot.sound`).

## Far-apart top steps and non-resonance (module `TwoPrimesNonresonance`)

Smaller step `u = q^(s^2)` (from the larger prime `q`), larger step `v = p^(t^2)`.

| Declaration | Statement |
|---|---|
| `U_upper`, `U_lower` | the largest element of the lower digit set lies between (step)/(2D) and (step)/D. |
| `gauge_lower`, `bound` | if `v >= 20 D u`, `X >= D v` and `D >= 100`, then for every nonzero integer pair `c (1 + (2 sqrt A0 + 1 + 2/G)/A_eff) <= 1.85`, where `c` is any number in the enclosure of the continuous energy and `G` the gauge of the pair. |
| `rotation`, `irrational_ratio`, `exists_far` | heights `X = D v` with `v >= K D u` exist for all large `D`, in every window `[x0, x2]` with `x0 ln p > 1` and `x0 ln q > 9/4`. |
| `nonresonance` | both together, with the actual digit-set data and both top ranges at least `D`. |
| `exists_far_two_three` | the existence statement for the primes 2, 3 and the window `[3.4, 6]` (the hypotheses are satisfiable). |

**Assumed, not formalized:** the enclosure `C0 - 2XW/Q^2 <= C_cont <= C0` and the formulas for the area `A0` and `H(0)` of the cluster model (they enter as hypotheses and definitions), and the inequality `C_model <= Gamma_D` (geometry of numbers). The energy bound on the actual balls (the remaining hypothesis) is open and not formalized.

Axiom report: `TwoPrimesAxioms10.lean` (only `propext`, `Classical.choice`, `Quot.sound`).

## The energy at far-apart heights (module `TwoPrimesFormula`)

Top steps `u`, `v` with `v >= 20 D u`, height `X = D v`, radius parameter `D >= 100`; `Y`, `Z` finite sets of integers with `D |y| < u`, `D |z| < v`, `0` in `Z`, `|Z| >= 5`. `A = {j u + y in [0, X]}`, `B = {k v + z in [0, X]}`. `H D` is the kernel `K_D(theta) = sum_{|m|<D} (D-|m|)^2 e(m theta)`, written as a double sum of cosines.

| Declaration | Statement |
|---|---|
| `H_eq`, `H_succ_le` | `K_D = 2 sum_{j<D} F_j + F_D` (Fejer kernels), and `K_{D+1} <= (1 + 4/(D-2)) K_D`. |
| `H_ge_near`, `weight_le_far` | the weight `K_D/K_D(0)` is at least `4/pi^2` within `1/(2D)` of an integer, and at most `3/(4 D^2 delta^2)` at distance `delta`. |
| `energy_formula` | `(1 - 5/D)(4/3) kappa_D <= C <= (1 + 5/D)(4/3) kappa_D`. |
| `energy_le_kappa` | `C <= 1.36 kappa`. |
| `Setting.one_le_kappaD`, `Setting.kappaD_le_kappa` | `1 <= kappa_D <= kappa`. |
| `energy_lower`, `energy_of_kappaD`, `kappaD_of_energy`, `near_sum_le` | `C >= (4/3)(1 - 5/D)`; `kappa_D <= 1.64` gives `C <= 2.3`; `C <= 2.3` gives `kappa_D <= 1.82`; the frequencies near the integers carry at most `(pi^2/4)(kappa_D - 1)`. |
| `Setting.card_setB`, `setting_satisfiable` | `|B| = D |Z| + 1`; the hypotheses are satisfiable. |

**Assumed, not formalized:** that the balls of radius `1/D` below the height are the sets `A` and `B` formed with the lower digit sets (the digit theorem of the first article), and that these digit sets satisfy the listed properties. A bound for `kappa_D` is open.

Axiom report: `TwoPrimesAxioms11.lean` (only `propext`, `Classical.choice`, `Quot.sound`).

## More top clusters (module `TwoPrimesMultiple`)

Heights `X = M v` with `M >= 100` top clusters, `M` separate from the radius parameter. The finite-set statements need only `100 |y| < u`, `100 |z| < v`, `v >= 2000 u`, `0` in `Z` and `M >= 100` (`Wide M u v Y Z`); there is no lower bound on `|Z|`. A setting of `TwoPrimesFormula` at radius `1/D` gives this (`wide_of_setting`), and `Z = {0}` is allowed (`wide_singleton`). (Before 2026-11-26 the hypothesis `|Z| >= 5` was assumed.)

| Declaration | Statement |
|---|---|
| `energy_formula_multiple` | `(1 - 5/M)(4/3) kappa_M <= C <= (1 + 5/M)(4/3) kappa_M`, where `C` is the normalized energy at `X = M v`. |
| `energy_of_kappa_lt` | `kappa_M <= K` and `200 K <= M (69 - 40 K)` give `C <= 2.3`. |
| `phi_le_four_kappa`, `kappa_le_thirtytwo` | `P_H/H^2 <= 4 kappa_H`; `kappa_M <= 32 kappa_H` for `H <= M`. |
| `blk_transfer`, `block_transfer` | `H^2 P_j <= (j + H - 1)^2 P_H`, where `P_j = sum_xi G(xi) F_j(xi v/u)`. |
| `kappa_transfer` | `kappa_M <= (1 + 3h/M + 4h^2/M^2) P_H/H^2` with `h = H - 1`, for all `M, H >= 1`. |
| `small_conductor` | for `gcd(v, Q) = 1`, `sum_{0<b<Q} W_M(b v/Q) <= pi^2 Q^2/(4 M^2)`. |
| `exists_far_multiple` | for `mu >= 0`, `(mu+1)^2 < 4 x0 ln p`, `(mu+2)^2 < 4 x0 ln q` and large `D`, one pair of levels serves every `1 <= M <= D^mu`, in the window `[x0, x2]`. |

**Assumed, not formalized:** the identification of the balls with the digit sets, as in the previous section; the passage from `C <= 2.3` to witnesses; the use of one radius from each short range. A bound for `kappa_M` is open.

Axiom report: `TwoPrimesAxioms12.lean` (only `propext`, `Classical.choice`, `Quot.sound`).

## Witnesses from a positive density of differences (module `TwoPrimesEffective`)

For a base `p` the levels have the weights `p^(n^2)`, and `Small p s k` says that `k` is within `s`
of `0` modulo `1` after division by every such weight.

* `abs_digit_le_of_far`, `card_marked_le`: a digit product of modulus at least `η` has at most
  `24 D² log(1/η)` levels whose argument is visibly away from the integers.
* `run`: along levels which are not of this kind the phase is only multiplied, with no wrap-around.
* `rigidity`: if the digit products of two coprime bases are both at least `η` at `θ`, then `θ` is
  extremely close to an integer.
* `exists_four`: a Fourier positivity criterion on a large cyclic group.
* `witness_of_density`: let `V` be a set of at least `X/K` integers, each a difference `a - b` with
  `|a|, |b| ≤ X`, `a` small for `p` and `b` small for `q` at the radius `s`. Let
  `B = ⌊12 D² log(50K)⌋` and `X ≥ exp(4^(2B+1) A₀)`. Then every `|t| ≤ exp(3 A₀)` has `k` with
  `|k| ≤ 8X` which is small for `p`, with `k - t` small for `q`, at the radius `4(s + 1/D)`.

Not formalized: the existence of such sets `V` for two primes (a uniform density estimate, which
the module takes as a hypothesis) and the choice of the heights `X`. Axioms: `TwoPrimesAxioms13`.

## Only a density of differences is needed (module `TwoPrimesSupport`)

Notation as in `TwoPrimesEffective`.

* `witness_of_support`: let `W` be a set of at least `Y/K` integers, each a difference `a - b` with
  `|a|, |b| ≤ Y`, `a` small for `q` and `b` small for `p` at the radius `1/D`. Let
  `q^(2m+1) > D` and `p^(2n+1) > D`. Then every `t` with `|t| + max(q^(m²), p^(n²)) ≤ Y` has `k`
  with `|k| ≤ 35KY`, `k` small for `q` and `k - t` small for `p` at the radius `35K/D`.
* `witness_of_energy`: the same when `Y · E ≤ K (|A| |B|)²` for the collision energy `E` of `a - b`.
* `support_of_range`: conversely, witnesses for all `|t| ≤ T` give at least `2T + 1` differences.
* `walk`: the walk with the two steps which stays in a window.

Not formalized: the existence of such sets `W` for two primes (that is the open hypothesis), and
the asymptotic consequences for height exponents. Axioms: `TwoPrimesAxioms14`.

## A dual form of bounded representations (module `TwoPrimesDual`)

A quantitative form of Kronecker's theorem (transference); no priority is claimed for the principle.

* `dist_rep_le`: if `t = Σ w i * z i` with `|z i| ≤ H * J i`, then
  `‖t θ‖ ≤ H * Σ J i * ‖w i θ‖`.
* `rep_of_dual`: if every `θ` with `‖t θ‖ > 1/10` has an index with `J i * ‖w i θ‖ ≥ c`
  (`J i ≥ 1`, `c ≤ 1/2`), then `t = Σ w i * z i` with `|z i| ≤ 2 h J i`, whenever
  `log(7 h R) ≤ 16 c² h / 3` and `Σ |w i| J i ≤ R`.
* `small_of_digits`, `witness_of_dual`: the case of the weights `q^(n²)`, `p^(n²)`; the target `t`
  then has a witness at the radius `4h/D`.

Not formalized: the asymptotic consequence for the unit-target exponent, and the dual condition
itself, which is open. Axioms: `TwoPrimesAxioms15`.

## An explicit witness at a very small radius (module `TwoPrimesWitnessLarge`)

* `rounding`: if the rows of a nonsingular integer matrix lie in the congruence lattice of the
  weights modulo `u`, every residue is `Σ d j * w j` with `2 |d j| ≤ Σ i |B i j|`.
* `unit_witness_large`: an explicit integer with `|witness| < 2^10071`, with `witness` small for the
  base 3 and `witness - 1` small for the base 2 at the radius `1/D`, `D = 1.7 * 10^18`.
  Checked by the kernel (`decide +kernel`), no `native_decide`. Minimality is not claimed.

The 124-dimensional matrix and the bounds for all targets are in `TwoPrimesBasis` below; see also
`TwoPrimes_supplement/basis124`. Axioms: `TwoPrimesAxioms16`.

## The dual criterion with a loss linear in 1/c (module `TwoPrimesDualSharp`)

* `rep_of_dual_dilated`: if every `theta` with `||t theta|| > 1/10` has an index with
  `J i * ||w i theta|| >= c` (`J i >= 1`), and `2 c H >= 1`, `log(7 h H R) <= 4h/3`,
  `sum |w i| J i <= R`, then `t = sum w i z i` with `|z i| <= 2 h H J i`.
* `abs_value_of_digits`: digit sums with `D |z n| <= L q^(2n+1)` satisfy `|value| <= (2L/D) q^(N^2)`.
* `witness_of_dual_dilated`: for the weights `q^(n^2)`, `p^(n^2)`, a witness `k` for `t` at the radius
  `4 h H / D` with `|k| <= (4 h H / D) q^(Nq^2)`.

The dual condition is a hypothesis. Axioms: `TwoPrimesAxioms17`.

## The 124-dimensional certificate inside Lean (modules `TwoPrimesBasisData`, `TwoPrimesBasis`)

`TwoPrimesBasisData` is the matrix of `TwoPrimes_supplement/basis124` as Lean data, with an inverse
modulo 2. `TwoPrimesBasis` checks by `decide +kernel` (no `native_decide`) the row congruences modulo
`3^6400`, the column sums, invertibility modulo 2 and the digit bounds at every level.

* `det_ne_zero`: the matrix is nonsingular. (Its determinant is not computed.)
* `explicit`, `explicit_witness`: for every `t` with `|t| <= 2^10300` there is `k` with
  `|k - t| < 2^10143`, `P_3(k) < 7 * 10^-18` and `P_2(k - t) < 7 * 10^-18`; the difference `k - t`
  depends only on `t` modulo `3^6400`.

The energy bound at heights of this size is in `TwoPrimesBoxCertificate` below.
Axioms: `TwoPrimesAxioms18`.

## A short lattice basis gives witnesses (module `TwoPrimesShortBasis`)

* `witness_of_short_basis`: a nonsingular integer matrix with rows in the congruence lattice modulo
  `q^(s^2)` and column sums at most `rho (2 J_j + 1)` gives a witness at the radius `3 rho / D` for
  every target of the stated size.

The existence of such matrices for all large `D` is open. Axioms: `TwoPrimesAxioms18`.

## The two claims (module `TwoPrimesClaims`)

`ClaimU p q C`: for all small `eps` the target 1 has a witness `|k| <= exp(C ln^2(1/eps))`.
`ClaimA p q B`: the range claim with the exponent `B`.

* `claimU_of_density`: differences with inverse density at most `D^(delta + o(1))`, `delta < 1`, at
  heights `ln X <= x ln^2 D`, one `D` in each short range, give `ClaimU` for all constants above
  `x/(1 - delta)^2`.
* `claimA_of_density`, `density_of_claimA`, `claimA_iff_density`: `ClaimA` for all exponents above
  `B0` is equivalent to a positive density of the differences at heights `ln X <= B ln^2 D`.
* `claimU_of_visible`: if for every large `D` every `theta` with `||theta|| > 1/10` has a level
  `l^(n^2) <= exp(x ln^2 D)` with `I_n ||l^(n^2) theta|| >= D^(delta - 1)`, `0 < delta <= 1`, then
  `ClaimU` holds for all constants above `x/delta^2`.
* `claimU_of_dual_condition`: the case of the thresholds `D^(-tau)` for all small `tau`.

The hypotheses are open. The converse direction of the dual criterion uses the digit description of
the balls and is not formalized. Axioms: `TwoPrimesAxioms19`.

## The lattice-box estimate and the energy bound (modules `TwoPrimesBox`, `TwoPrimesBoxCertificate`)

* `box_bounds`, `box_energy`: for independent uniform integer digits and **any nonsingular** matrix
  whose rows lie in the congruence lattice modulo `Q` (the rows may span a proper sublattice),
  `prod (N_j + 1 - r_j)^+ <= Q * n_c <= prod (N_j - 1 + r_j)` and
  `sum_{0<b<Q} |E e(b g / Q)|^2 <= (U - 1)(1 - L)`.
* `kappa_le`, `finite_energy`: for every `D` in `[9 * 10^14, 10^15]` the normalized collision energy
  of the sets built from the digit sets of 3 (80 levels) and 2 (101 levels) at `X = D * 2^10201` is
  less than `1.711`.
* `window`: `3.4 ln^2 D < ln X < 6 ln^2 D`.

That the two balls are these sets is the digit description of the first article and is not part of
the module. Axioms: `TwoPrimesAxioms20`.

## The dual side of the certificate (module `TwoPrimesDualGap`)

* `phase`: for every real `theta`, if `J_j ||w_j theta|| < 90` at all 124 digits then
  `||theta|| < 1/10` (the first 123 rows of the matrix are exact relations between the weights).
* `dual_gap`: for `b` not divisible by `3^6400`, `max N_j ||b w_j / 3^6400|| > 140` and
  `sum (N_j ||b w_j / 3^6400||)^2 > 336^2`.

Here `J_j = floor(l^(2m-1) / 10^15)` and `N_j = 2 J_j + 1`. The results are due to ChatGPT.
Axioms: `TwoPrimesAxioms21`.

## The weighted sum (module `TwoPrimesSum`)

* `diag`: `kappa_M >= (3M/(2M^2+1)) u / (|Y| |Z|)` for any finite sets.
* `average`: the average over the units modulo `q^R` of `sum G(xi) W_M(a xi / u)` is at most
  `1 + (3M/(2M^2+1)) (sum G - 1)`.
* `lowcond`: the frequencies of a conductor prime to `p` are bounded by one digit factor of `p`
  and the sizes of the others.
* `qmass`: the closed formula for `sum_{b mod q^a} |phi_Y(b/q^a)|^2`.

Not formalized: the two asymptotic statements and the two examples of that part of the article.
Axioms: `TwoPrimesAxioms22`.

## The normalized kernel decreases (module `TwoPrimesKernel`)

* `weight_antitone`: `W_N(theta) <= W_M(theta)` for `1 <= M <= N` and every real `theta`, where
  `W_M = K_M / K_M(0)`.
* `kappa_antitone`: hence `kappa_N <= kappa_M` for the same lower sets.

The theorem and its proof are due to ChatGPT. Axioms: `TwoPrimesAxioms23`.

## Narrower windows with one budget (module `TwoPrimesWindows`)

Sharpens `TwoPrimesEffective.witness_of_density`.

* `rigidity_joint`: if the product of the two digit products at `theta` has modulus at least
  `eta`, then `theta` is within `exp(-2.19 A)/2` of an integer, for levels up to
  `exp((9/4)^(B+1) A)` with `B = floor(24 D^2 log(1/eta))` and `A >= 2500 log q`.
* `witness_of_density_sharp`: the height `exp(4^(2B+1) A)` is replaced by `exp((9/4)^(B+1) A)`,
  with `B = floor(12 D^2 log(50K))`, for targets `|t| <= exp(2A)`.

One budget of `B+1` windows for all bases is also used in `ThreePrimesDensityM13`; its use here,
and window ratios close to `sqrt 2`, were proposed by ChatGPT. Axioms: `TwoPrimesAxioms24`.

## Free heights in bounded gaps (module `TwoPrimesFreeHeight`)

* `exists_free`: for any finite set of bases, every `[R, 2 exp(H) R]` with
  `H = (number of bases) * log(8D) + 1` contains a free height once `R` is explicitly large.
* `witness_of_density_wide`: `witness_of_density_sharp` for targets `|t| <= exp(2.19 A)/5`.
* `witness_of_free_heights`: if every large free height carries enough differences, every target
  `t` has a witness `|k| <= 16 exp(H + E A0) (1+|t|)^(E/2.19)`, `E = (9/4)^(B+1)`.  The density is
  a hypothesis.

The bounded gap and the exponent are due to ChatGPT. Axioms: `TwoPrimesAxioms25`.
