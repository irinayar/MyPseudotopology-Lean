# ThreePrimePlus: Lean checks of the elementary and algebraic steps (17 November 2026)

Modules: `LeanCheck/TPPQuartic.lean`, `TPPFirstGap.lean`, `TPPConv.lean`, `TPPSep.lean`, `TPPElim.lean`, `TPPCross.lean` (imported by `LeanCheck.lean`) and the audit entry point `LeanCheck/TPPAxioms.lean`. A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article statements needs mathematical review.

What is **not** formalized: Matveev's theorem on linear forms in logarithms (it enters `sep_of_matveev` as the hypothesis `m₀ ≤ |Λ|`), the stretched-exponential window and its Fourier decay, the Fourier-analytic definitions of the kernels, and the exact lattice enumeration (a finite computation done with LLL and Fincke-Pohst; it is not part of the Lean files).

## `TPPFirstGap`

| Declaration | Statement |
|---|---|
| `first_gap` | If `0 < x ≤ y`, `a ≠ 0` and `|a + b e^{-x} + c e^{-y}| ≤ 1/2` for integers `a, b, c`, then `e^x ≤ 4 max(|b|,|c|)`. |
| `divisor_near_resonant` | The form `a + b ρ₂ + c ρ₃` is linear: if `k ≥ 1` and `|k a + k b ρ₂ + k c ρ₃| < ε`, then `|a + b ρ₂ + c ρ₃| < ε`. |
| `mass_le` | `e^x ≤ 4W` gives `C W^{-4} ≤ 256 C e^{-4x}`. |

## `TPPConv`

Abstract form of the first-large-displacement bound of the normalized convolution. For functions `h i : ℝ → ℝ` with values in `[0,1]`, the one-step inequality `h i y ≤ Σ κ h (i+1)(y + r/Q)` and a terminal vanishing condition, `first_large` gives `h i y ≤ Σ_m β^m tail(i+m+1, θ_m)` at every point of norm at least `ε + Σ θ_m`. `geom_thresholds`: `Σ_{m<k} 2^{-(m+3)} ≤ 1/4`.

## `TPPSep`

Elementary parts of the two-term separation lemma: `exp_sub_one_lower` (`|e^Λ - 1| ≥ (1/2) min(1,|Λ|)`), `not_eq_of_lt` (`a q^{e'} ≠ d p^e` for `0 < a < p^e`), `abs_form_eq` (opposite signs: `|a/Q + d/Q'| = (|d|/Q') |e^Λ - 1|`), `sep_of_matveev` (the lower bound `(1/2) min(1,m₀)/Q'` from `|Λ| ≥ m₀`).

## `TPPElim`

The elimination argument: `elim_identity`, `elim_bound` (`|a'S - aS'| < 2Mδ`), `proportional_of_sep`, `cross_of_elim`, and `exists_primitive_gen` (pairwise proportional integer vectors with nonzero first coordinate are integer multiples of one primitive integer vector).

## `TPPQuartic`, `TPPCross`

`TPPQuartic`: the integer quartic `P_h(L₂,L₃,L₅)` equals `L₃²L₅²` times the product of `h₁ ± h₂α ± h₃β` (`quartic_eq_prod`), vanishes when `h·v = 0`, and satisfies `|P_h| ≤ 27 m³ L₃² L₅² |h·v|` (`quartic_bound`). `TPPCross`: the cross-product identities `dot_cross_eq`, `cross_decomp_1..3` of the ray theorem, and `exponent_pos`.

## `TPPTransfer` (pigeonhole transference and the exclusion inequality)

| Declaration | Statement |
|---|---|
| `exists_orthogonal` | If `z_i ≤ Z` (naturals) and `3 M Z + 1 < (M+1)^3`, there is a nonzero integer vector `(a,b,c)` with `|a|,|b|,|c| ≤ M` and `a z_0 + b z_1 + c z_2 = 0` (pigeonhole on the values of `x·z`, `x ∈ {0..M}^3`). |
| `hv_bound` | If `a n + b m + c l = 0`, `|m - α n| ≤ δ`, `|l - β n| ≤ δ`, then `n |a + b α + c β| ≤ (|b| + |c|) δ`. |
| `delta_lower` | If moreover `|b|,|c| ≤ M`, `n > 0` and `c₀ ≤ |a + b α + c β| M²`, then `c₀ n ≤ 2 M³ δ`. |

These are the algebraic core of the transference lemma and of the proof that no close triples exist where the exponent-2 bound `|h·v| ‖h‖² ≥ c₀` is known (the bound itself is a computer-assisted enumeration, not part of the Lean files).

## `TPPGeneral` (elementary steps for any three primes; ThreePrimeContinue, Section "Any three primes")

| Declaration | Statement |
|---|---|
| `sq_diff_factor` | `m² L₂ − n² L₁ = L₂ (m − α n)(m + α n)` when `α² L₂ = L₁`. |
| `near_of_sq_diff` | If `|m² L₂ − n² L₁| ≤ D`, `m, n ≥ 0`, `L₂, α > 0`, `α² L₂ = L₁`, then `|m − α n| · (L₂ α n) ≤ D`. |
| `sq_diff_of_near` | If `|m − α n| ≤ ε` then `|m² L₂ − n² L₁| ≤ L₂ ε (2 α n + ε)`. |
| `Qh`, `Qh_eq_prod` | `Q_h(x,y,z) = (h₀² y z − h₁² x z − h₂² x y)² − 4 h₁² h₂² x² y z` equals `y² z²` times the product of `h₀ ± h₁ α ± h₂ β` when `x = α² y = β² z`. |
| `Qh_eq_zero_iff` | for `y, z ≠ 0`: `Q_h = 0` iff one of the four numbers `h₀ ± h₁ α ± h₂ β` vanishes. |
| `sadic_reform`, `N_eq` | `(a Q₂ Q₃ + b Q₁ Q₃ + c Q₁ Q₂)/(Q₂ Q₃) = a + b Q₁/Q₂ + c Q₁/Q₃` and `N = (a Q₂ + b Q₁) Q₃ + c Q₁ Q₂`. |
| `N_ne_zero` | `N ≠ 0` for `Q₁ = p^e` when `a ≠ 0`, `|a| < p^e` and `p ∤ Q₂ Q₃` (valuation argument for the nonvanishing of the linear form). |
| `box_cond` | `3 Z ≤ M²` and `M ≥ 1` imply `3 M Z + 1 < (M+1)³`, the counting condition of `exists_orthogonal`. |

Not formalized: the planar Dirichlet argument, the Borel--Cantelli step, Khintchine's transference, Matveev's theorem and the numerical computations.

## `TPPTransferJ` (the arithmetic of the conditional finiteness theorem)

| Declaration | Statement |
|---|---|
| `rpow_neg_mono` | `0 < m ≤ M`, `J ≥ 0` ⟹ `M^(-J) ≤ m^(-J)`. |
| `delta_lower_J` | If `c > 0`, `J ≥ 0`, `n > 0`, `1 ≤ m ≤ M ≤ 4 √n`, the exponent bound `c m^(-J) ≤ |h·v|` (the hypothesis `(H_J)` for a vector of norm `m`) and the pigeonhole bound `n |h·v| ≤ 2 M δ`, then `c / (2 · 4^(J+1)) · n^((1-J)/2) ≤ δ`. |
| `log_sq_lt_rpow` | for `C, c₁, s > 0` there is `N ≥ 1` with `C (log n)² < c₁ n^s` for all `n ≥ N`. |
| `no_close_triple_large` | for `J < 3`, `c₁, C > 0` there is `N ≥ 1` such that for `n ≥ N` no `δ` satisfies both `δ ≥ c₁ n^((1-J)/2)` and `δ ≤ C (log n)² / n`. |

Together with `TPPTransfer` (`exists_orthogonal`, `hv_bound`) and `TPPGeneral` (`box_cond`) these formalize the arithmetic of the theorem "Finiteness of close triples under `(H_J)`", `J < 3`. Not formalized: the identification of the norm `m` of the pigeonhole vector with the quantity in `(H_J)` beyond the stated hypotheses, the equivalence of the diameter condition with `δ ≤ C (log n)² / n` (only the difference-of-squares step is in `TPPGeneral`), and the passage from `n` bounded to finitely many triples.
