# PVG: Lean checks of algebraic and analytic steps (6 November 2026)

These modules check abstract algebraic, cardinal and analytic components of steps in the article "Pseudotopological Vector Groups on Real Line" (version PVG_v9, Section 8). They do **not** formalize the compact group `Hom(ℝ, 𝕋)`, ultrafilter limits or the pseudotopologies `η_G`; Theorem 8.23 (classification below the Bohr topology), Corollary 8.25, Proposition 8.28(b) and Corollary 8.29 are not formalized. A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article statements needs mathematical review.

Modules: `LeanCheck/PVGAlgebra.lean`, `LeanCheck/PVGInterpolation.lean`, `LeanCheck/PVGCharacters.lean`; audit entry point `LeanCheck/PVGAxioms.lean` (output in `verification/pvg-check.txt`). The three modules are imported by `LeanCheck.lean`; `PVGAxioms.lean` is not.

| Lean declaration | Article statement | Relation |
|---|---|---|
| `maximal_admissible_iff` | Corollary 8.27(a) | `K` any real vector space, line `L`; admissible means `Disjoint G L`; maximal iff `Codisjoint G L`. |
| `exists_maximal_admissible` | used in Corollary 8.27(b) | Every admissible subspace lies in a maximal one (Zorn). |
| `no_common_admissible` | algebraic core of Corollary 8.24 | If `φ a ∈ L` forces `a = 0`, the graph `{e a + φ a}` is admissible and no subspace containing it and `range φ` is admissible. |
| `ker_isCompl`, `retraction_unique`, `retractionEquiv` | Corollary 8.27(b),(c) | Complements of the line correspond bijectively to linear maps `π` with `π e1 = 1` (`H = ker π`). The statement `U → x iff π(L(U)) = x` is not formalized. |
| `rank_eq_of_card` | Lemma 8.26(c), Proposition 8.28(b) | A real vector space of cardinality `2 ^ 𝔠` has dimension `2 ^ 𝔠`. |
| `card_retractions` | Corollary 8.27(c) | In dimension `2 ^ 𝔠` there are exactly `2 ^ (2 ^ 𝔠)` linear `π` with `π e1 = 1`. |
| `interpolation`, `interpolation_round` | Lemma 8.26(a) | For `y 0 ≠ 0`, `4 |y k| ≤ |y (k+1)|` and any `S ⊆ ℕ` there is `b` with `b y k` at distance at least `1/3` from the integers (`k ∈ S`; also at most `1/2`) and within `1/6` of an integer (`k ∉ S`). Indices start at 0. |
| `limits_ne`, `distinct_limits` | Lemma 8.26(b) | Abstract: `X` a topological space and `ψ b : X → ℝ` continuous with `ψ b (e t) = |b t - round (b t)|`; then distinct ultrafilters on `ℕ` have distinct limits of `e ∘ y`. |
| `bounded_conv_euclid` | Proposition 8.28(a) | Abstract: a convergence relation on filters of `ℝ` with unique limits, convergent for Euclidean convergent filters and monotone under refinement; a bounded convergent sequence converges in the Euclidean sense to the same limit. |
| `trivial_intersection` | Proposition 8.17, `H₀ ∩ e(ℝ) = {0}` | For nonzero additive `f : ℝ →+ ℚ`: if `f (a b) - x b ∈ ℤ` for all real `b`, then `x = 0` and `a = 0`. |

Also not formalized: the count of `2 ^ 𝔠` free ultrafilters on `ℕ`.
