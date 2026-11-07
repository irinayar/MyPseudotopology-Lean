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

## Question 9.5: reductions for sequential compactness of `η_π` (`PVGSequences`, 7 November 2026)

Module `LeanCheck/PVGSequences.lean` (imported by `LeanCheck.lean`), axiom report in `LeanCheck/PVGSequencesAxioms.lean` and `verification/pvg-sequences-check.txt`. It checks the reductions R1 to R4 of the research note on Question 9.5 of `PVG_v10` in a concrete setting: `K = ℝ →+ AddCircle 1` (all algebraic characters of `ℝ`, pointwise topology; compact, Hausdorff, a real vector space with `(c • κ) b = κ (c b)`), `e x = (b ↦ b x mod 1)` and the limits `L y U = lim_U e (y k)` for free ultrafilters `U` on `ℕ`.

| Declaration | Statement |
|---|---|
| `L_add`, `L_smul`, `L_const` (R3) | `L (y + z) U = L y U + L z U`, `L (c • y) U = c • L y U`, `L (const x) U = e x`. |
| `interpolation_bounded` | Lemma 8.26(a) with `0 ≤ b ≤ 2 / |y 0|`. |
| `L_sub_ne_e` (R2) | For `y 0 ≠ 0`, `4 |y k| ≤ |y (k+1)|` and free ultrafilters `U ≠ V`: `L y U - L y V ≠ e d` for every real `d`. |
| `exists_lacunary_subseq` | An unbounded real sequence has a lacunary subsequence. |
| `R1`, `R1_linear` (R1) | With `SC π a := ∃ B infinite, ∃ x, ∀ free U ∋ B, π (L a U) = x`: if `π (e x) = x` and `SC π y` holds for every lacunary `y`, then `SC π a` holds for every real sequence `a`. |
| `R4`, `R1_R4` (R4) | A linear `π` with `π e1 = 1` satisfying the constancy criterion for all sequences of a set `Lac` exists iff there is a choice `y ↦ B_y` (infinite sets) such that the real span of all differences `Lf y U - Lf y V` (`U, V` free, containing `B_y`) meets `ℝ e1` only in `0`; concrete form `R1_R4` for `K` and the lacunary sequences. |

Not formalized: the pseudotopology `η_π` itself (so "sequentially compact" is replaced by the criterion `SC` of Question 9.5, whose equivalence with sequential compactness of `η_π` is argued in the text of `PVG_v10`), and the answer to Question 9.5, which remains open.
