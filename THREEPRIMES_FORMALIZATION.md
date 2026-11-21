# ThreePrimes: Lean checks of two explicit upper bounds and their comparison (20 November 2026)

Modules: `LeanCheck/ThreePrimesUpper.lean`, `LeanCheck/ThreePrimesTheoremB.lean` and `LeanCheck/ThreePrimesComparison.lean` (all imported by `LeanCheck.lean`). The first two import `LeanCheck.TVGPlusCount` (and through it `TVGPlusValuation`), reuse its pigeonhole lemma `TVGPlus.pigeonhole_box` / its predicate `InBall` and its universal divisor `TVGPlus.forced`, and use `Real.logb 2 p` for `log₂ p`. Typechecked with Lean 4.35.0 and Mathlib; no `sorry`; every declaration listed below depends only on `propext`, `Classical.choice`, `Quot.sound`. The compiler gives only deprecation warnings for `push_neg`.

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

## Differences from the prose and what is not formalized
The article states the theorems for `m = ⌈2/δ⌉`, `h = ⌈log₂ m⌉`, `0 < δ ≤ 1/2`; the modules assume only `m δ ≥ 2`, `m ≤ 2^h` (and `h ≥ 1` in `ThreePrimesUpper`). The retained coordinates are cut off per prime at `⌊√((L+h)/log₂ p)⌋` (respectively `⌊√((Δ+M+h)/log₂ p)⌋` with `n > a_p`) instead of `p^{n²} ≤ N m` (resp. `≤ D 2^M m`); the error is bounded through `δ/2 < δ`, as in `TVGPlus.explicit_upper`. `discQ_nonneg` proves `Q ≥ 0` (the prose has `Q > 0`). Not formalized: the numerical checks, the comparison tables and the asymptotic expansion of the leading constant. The correspondence between these statements and the article needs mathematical review.
