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
