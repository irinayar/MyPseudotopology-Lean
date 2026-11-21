# ThreePrimes: Lean checks of two explicit upper bounds and their comparison (20 November 2026)

Modules: `LeanCheck/ThreePrimesUpper.lean`, `LeanCheck/ThreePrimesTheoremB.lean` and `LeanCheck/ThreePrimesComparison.lean` (and the variants `…M1`, `…M2`, `…M3`, `…M4` described below; all imported by `LeanCheck.lean`). The first two import `LeanCheck.TVGPlusCount` (and through it `TVGPlusValuation`), reuse its pigeonhole lemma `TVGPlus.pigeonhole_box` / its predicate `InBall` and its universal divisor `TVGPlus.forced`, and use `Real.logb 2 p` for `log₂ p`. Typechecked with Lean 4.35.0 and Mathlib; no `sorry`; every declaration listed below depends only on `propext`, `Classical.choice`, `Quot.sound`. The compiler gives only deprecation warnings for `push_neg`.

**Check programs and recorded outputs** (exact-integer and decimal computations that accompany these statements: counting conditions, end-to-end pigeonhole runs, comparison tables, adversarial searches) are in the separate repository [irinayar/ThreePrimes-Supplement](https://github.com/irinayar/ThreePrimes-Supplement) (tag `supp-2026-11-21`, with a SHA-256 manifest). They are finite computations by the same agent family as the Lean files and are not an independent reproduction; this repository contains only the Lean modules.

## `ThreePrimesUpper` (Theorem "Explicit upper bound" of the article ThreePrimes, version 2)
| Declaration | Statement |
|---|---|
| `tight_ineq` | For reals `a ≥ 1`, `h ≥ 1`, `L ≥ a h² + a h`: `a h² (L + h) ≤ L²`. |
| `explicit_upper_tight` | For `S` a finite set of integers `≥ 2`, `δ > 0`, naturals `m, h, L` with `m δ ≥ 2`, `m ≤ 2^h`, a real `a ≥ 1` with `(Σ_{p∈S} √(1/log₂ p))² ≤ a` and `a h² + a h ≤ L`: some integer `k` with `1 ≤ k ≤ 2^L` has `P_p(k) < δ` for every `p ∈ S`. |
| `explicit_upper_tight_ceil` | The same with `a = max(1, g_S²)`, `g_S = Σ √(1/log₂ p)`, and `L = ⌈a h² + a h⌉`. |
| `explicit_bounds_tight` | For primes: `D_S(δ) ≤ k ≤ 2^L` (lower bound by the universal divisor `forced`). |
| `tight_le_old` | `⌈a_S h² + a_S h⌉ ≤ 4 s² h²` for nonempty `S` (`s = |S|`, `h ≥ 1`): the new exponent never exceeds the old one. |

## `ThreePrimesTheoremB` (Theorem "Explicit bound on multiples of D")
| Declaration | Statement |
|---|---|
| `nrm_sub_lt_of_box`, `pigeonhole_box_mul` | Pigeonhole on the multiples `D x`, `0 ≤ x ≤ X`: if `m^{|C|} ≤ X`, some `k = D t`, `1 ≤ t ≤ X`, has `‖k/q‖ < 1/m` on every coordinate `q = p^{n²}` of `C`. |
| `logb_D` | `log₂ D = Σ a_p² log₂ p` for `D = ∏ p^{a_p²}`. |
| `explicit_upper_mult` | For arbitrary naturals `a_p`, `δ > 0`, `m δ ≥ 2`, `m ≤ 2^h` and `h (A √(Δ+M+h) − α) ≤ M` (`A = Σ √(1/log₂ p)`, `α = Σ a_p`, `Δ = Σ a_p² log₂ p`): some integer `k` with `1 ≤ k ≤ D 2^M`, `D ∣ k`, lies in the ball (`InBall S δ k`), `D = ∏ p^{a_p²}`. |
| `quad_step`, `discQ_nonneg` | For `x ≥ t* = (hA+√Q)/2`: `h(A x − α) ≤ x² − h − Δ`; the discriminant `Q = h²A² − 4(hα − Δ − h)` is `≥ 0` (Cauchy–Schwarz). |
| `explicit_upper_B` | The closed form: the same conclusion with `M = ⌈t*² − h − Δ⌉` (`Nat.ceil`, `0` if not positive). |
| `explicit_bounds_B` | With the forced exponents `a_p = aThr p δ` (so `D = Dvis S δ`): `D_S(δ) ≤ k ≤ D_S(δ) 2^M`. |
| `size_B` | `D 2^M ≤ max(D, 2^{t*² − h + 1})` (real exponent). |

## `ThreePrimesComparison` (Theorem B is never weaker than Theorem A; article ThreePrimes, version 3, Proposition 3.4)
Imports `LeanCheck.ThreePrimesUpper` and `LeanCheck.ThreePrimesTheoremB`. No `sorry`; standard axioms only. Typechecked with Lean 4.35.0 and Mathlib with the `lean` command on all three modules in dependency order (not a full `lake build`).
| Declaration | Statement |
|---|---|
| `aThr_logb_le` | For `p ≥ 2`, `δ > 0`, `m δ ≥ 2`, `m ≤ 2^h`, `h ≥ 1`: `a_p(δ) log₂ p ≤ h − 1`. |
| `sumDelta_bounds` | If `a_p log₂ p ≤ h − 1` on `S`: `Δ ≤ (h−1) α` and `Δ ≤ (h−1)² A²`. |
| `B_le_A` | For `S` nonempty with all `p ≥ 2`, `δ > 0`, `m δ ≥ 2`, `m ≤ 2^h`, `h ≥ 1`: `(Dvis S δ : ℝ) · 2^(Mstar S (aThr · δ) h) ≤ 2^⌈max 1 (A²) h² + max 1 (A²) h⌉`, i.e. `D_S(δ) 2^M ≤ 2^L`. |

## Variants with weaker hypotheses on `m` (article ThreePrimes, versions 5 and 6)
The same three theorems with the hypothesis `m δ ≥ 2` replaced by `1 < m δ` (suffix `M1`, version 5; for example `m = ⌊1/δ⌋ + 1`) and by `1 ≤ m δ` (suffix `M2`, version 6; for example `m = ⌈1/δ⌉`). The modules `…M1`/`…M2` import the corresponding published module and reuse its lemmas unchanged; only the last step of each proof changes: every coordinate of the chain is bounded by `1/m`, so no factor `δ/2` is needed. Standard axioms only, no `sorry`; typechecked with the `lean` command in dependency order (not a full `lake build`).
| Module | Declarations | Hypothesis |
|---|---|---|
| `ThreePrimesUpperM1` | `explicit_upper_tightM1`, `explicit_upper_tight_ceilM1`, `explicit_bounds_tightM1` | `1 < m δ`, `m ≤ 2^h` |
| `ThreePrimesTheoremBM1` | `explicit_upper_multM1`, `explicit_upper_BM1`, `explicit_bounds_BM1` | `1 < m δ`, `m ≤ 2^h` |
| `ThreePrimesComparisonM1` | `aThr_logb_leM1` (`a_p log₂ p ≤ h`), `sumDelta_boundsM1`, `B_le_AM1` (shorter proof: `h α` is an integer `≥ Δ`) | `1 < m δ`, `m ≤ 2^h`, `h ≥ 1` |
| `ThreePrimesStrictM2` | `finite_lt_bound`, `Pn_sq_lt`: if the coordinates `n ≤ R` are each `< c` and the tail `n > R` is uniformly `≤ B < c`, then `Pn (sqScales p) k < c` | – |
| `ThreePrimesUpperM2` | `explicit_upper_tight_ceilM2`, `explicit_bounds_tightM2` (also `explicit_upper_tightM2`) | `1 ≤ m δ`, `m ≤ 2^h` |
| `ThreePrimesTheoremBM2` | `explicit_upper_multM2`, `explicit_upper_BM2`, `explicit_bounds_BM2` | `1 ≤ m δ`, `m ≤ 2^h` |
| `ThreePrimesComparisonM2` | `aThr_logb_leM2`, `sumDelta_boundsM2`, `B_le_AM2` | `1 ≤ m δ`, `m ≤ 2^h`, `h ≥ 1` |
In the `M2` modules the retained coordinates are finitely many and each strictly `< 1/m`, and the omitted coordinates satisfy the integer inequality `q ≥ N m + 1`, hence `‖k/q‖ ≤ N/(N m + 1) < 1/m`; `Pn_sq_lt` combines the two into a strict bound `P_p(k) < 1/m ≤ δ`. The hypothesis `0 < δ` is kept in the statements of `UpperM2` and `TheoremBM2` although it is no longer used (linter warning only). The `M1` modules are implied by the `M2` modules and are kept because article version 5 cites them.

## Variants with a real `η` in place of the natural number `h` (article ThreePrimes, version 7)
The `M3` modules replace the natural number `h` (with `m ≤ 2^h`) by a real `η` with `(m : ℝ) ≤ 2^η` (`Real.rpow`; for example `η = log₂ m`), with `1 ≤ m δ`. The count `m^|C| ≤ 2^(η|C|) ≤ 2^L` and the cut-off `N m ≤ 2^(L+η)` are done with `Real.rpow` and `Real.logb`; the strict supremum step is `Pn_sq_lt` of `ThreePrimesStrictM2`. They import the published modules and `ThreePrimesStrictM2`. Standard axioms only, no `sorry`; typechecked with the `lean` command in dependency order (not a full `lake build`).
| Module | Declarations | Hypothesis |
|---|---|---|
| `ThreePrimesUpperM3` | `explicit_upper_tightM3`, `explicit_upper_tight_ceilM3`, `explicit_bounds_tightM3` | `1 ≤ m δ`, `(m : ℝ) ≤ 2^η`, `1 ≤ η` |
| `ThreePrimesTheoremBM3` | definitions `discQR`, `tstarR`, `MstarR` (real-`η` forms of `Q`, `t*`, `M`); lemmas `discQR_nonneg`, `size_BR`; `explicit_upper_multM3`, `explicit_upper_BM3`, `explicit_bounds_BM3` | `1 ≤ m δ`, `(m : ℝ) ≤ 2^η`, `0 ≤ η` |
| `ThreePrimesComparisonM3` | `aThr_logb_leM3` (`a_p log₂ p ≤ η`), `sumDelta_boundsM3`, `tstar_le_M3`, `tstar_sq_M3`, `final_stepM3`, `B_le_A_slackM3` (`c ≤ η α − Δ`, `0 ≤ c ≤ 1`: `D_S(δ) 2^M ≤ 2^(L+1−c)`), `B_le_A_succM3` (`c = 0`: `≤ 2^(L+1)`), `B_le_A_sharpM3` (`c = 1`, hypothesis `1 ≤ η α − Δ`: `≤ 2^L`) | `1 ≤ m δ`, `(m : ℝ) ≤ 2^η`, `1 ≤ η` |
| `ThreePrimesComparisonM4` (imports `ThreePrimesComparisonM3`) | `y_le_slackM3` (`t*² − η − Δ ≤ (L − c) − Δ` for `0 ≤ c ≤ 1`, `c ≤ η α − Δ`), `B_le_A_ceilM3` (hypothesis `⌈Δ⌉ ≤ η α`: `D_S(δ) 2^M ≤ 2^L`; contains the integer case and `1 ≤ η α − Δ`) | `1 ≤ m δ`, `(m : ℝ) ≤ 2^η`, `1 ≤ η` |
The sharp comparison `D_S(δ) 2^M ≤ 2^L` for a real `η` is proved only under `⌈Δ⌉ ≤ η α` (`B_le_A_ceilM3`; for an integer `h` unconditionally, `B_le_AM2`); the region `Δ ≤ η α < ⌈Δ⌉` is open, and the inequality holds in all finite checks made. The hypothesis `0 < δ` is kept in `UpperM3` and `TheoremBM3` although it is no longer used (linter warning only).

## Differences from the prose and what is not formalized
The article states the theorems for `m = ⌈2/δ⌉`, `h = ⌈log₂ m⌉`, `0 < δ ≤ 1/2`; the modules assume only `m δ ≥ 2`, `m ≤ 2^h` (and `h ≥ 1` in `ThreePrimesUpper`). The retained coordinates are cut off per prime at `⌊√((L+h)/log₂ p)⌋` (respectively `⌊√((Δ+M+h)/log₂ p)⌋` with `n > a_p`) instead of `p^{n²} ≤ N m` (resp. `≤ D 2^M m`); the error is bounded through `δ/2 < δ`, as in `TVGPlus.explicit_upper`. `discQ_nonneg` proves `Q ≥ 0` (the prose has `Q > 0`). Not formalized: the numerical checks, the comparison tables and the asymptotic expansion of the leading constant. The correspondence between these statements and the article needs mathematical review.
