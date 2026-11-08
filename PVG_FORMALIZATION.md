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

## Question 9.5: independence of the limits of a sparse sequence (`PVGIndependence`, 7 November 2026)

Module `LeanCheck/PVGIndependence.lean` (imported by `LeanCheck.lean`; it imports `PVGSequences`), axiom report in `LeanCheck/PVGIndependenceAxioms.lean` and `verification/pvg-independence-check.txt`. It checks Lemma G and Theorem A of the research note `PVG_Q95_independence_2026-11-07.md` in the setting of `PVGSequences`.

| Declaration | Statement |
|---|---|
| `arcs`, `arcs_signed` (Lemma G) | For `a k > 0`, `0 < α ≤ 1`, `1 + α ≤ R α`, `R a k ≤ a (k+1)` and any real centres `c k` there is `b` with `0 ≤ b ≤ 2 / a 0` and, for every `k`, an integer `n` with `|b a k - c k - n| ≤ α/2` (signed version for `R \|z k\| ≤ \|z (k+1)\|`). |
| `exists_disjoint_family` | Pairwise distinct ultrafilters `W : Fin n → Ultrafilter ℕ` have pairwise disjoint members `S i ∈ W i`. |
| `independence` (Theorem A) | If all `y k ≠ 0` and `\|y (k+1)\| / \|y k\| → ∞`, `W : Fin n → Ultrafilter ℕ` is injective with all `W i` free and `γ : Fin n → ℝ` has some `γ i ≠ 0`, then `∑ γ i • L y (W i) ≠ e x` for every real `x`. |
| `independence_finset`, `linearIndependent_L` | The same for a finite set of free ultrafilters; the vectors `L y U` (`U` free) are linearly independent over `ℝ`, and their real span meets `e(ℝ)` only in `0`. |

Not formalized: Theorem B (finitely many jointly lacunary sequences), the density property of good retractions, the consequences for the retraction `π`, and the answer to Question 9.5, which remains open (dependent sequences and `c` many sequences).

## Question 9.5: merged independence, Proposition 8.38 and Corollary 8.39 (`PVGMerged`, `PVGUncountable`, 8 November 2026)

Modules `LeanCheck/PVGMerged.lean` and `LeanCheck/PVGUncountable.lean` (imported by `LeanCheck.lean`; they import `PVGIndependence`), axiom reports in `LeanCheck/PVGMergedAxioms.lean` and `LeanCheck/PVGUncountableAxioms.lean`. Same concrete setting as `PVGSequences` (`K = ℝ →+ AddCircle 1`, `e`, `L y U`). Checked with Lean 4.35.0 and the same Mathlib build: no `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only.

| Declaration | Statement |
|---|---|
| `free_map`, `L_comp` | The image of a free ultrafilter under an injective map is free; `L (y ∘ f) U = L y (f_* U)`. |
| `independence_merged` | Theorem 8.36 in merged form: if all terms of `y¹, …, yᵐ` occur in one sequence `z` with nonzero terms and `|z (k+1)| / |z k| → ∞` (injective `ι j` with pairwise disjoint ranges, `y j k = z (ι j k)`), `W_1, …, W_n` are pairwise distinct free ultrafilters and the real `γ j l` are not all zero, then `∑ γ j l • L (y j) (W l) ≠ e x`. Reduction to `independence`. The sorted enumeration that produces `z` is not formalized. |
| `FiniteToOne`, `free_map_fto`, `L_rep` | Finite-to-one maps send free ultrafilters to free ultrafilters; if `y k = ∑ r j • y0 (c j) (σ j k) + z k` with `z → a` along `B`, then `L y U = ∑ r j • L (y0 (c j)) (σ j ⁎ U) + e a` for free `U ∋ B`. |
| `prop_uncountable_gen`, `disjoint_span_L`, `prop_uncountable` | Proposition 8.38: for a base family whose limits span a subspace meeting `ℝ e1` only in `0`, the span of the differences `L (y i) U - L (y i) V` (`U, V` free, containing `B i`) of finite combinations of finite-to-one re-indexings plus a convergent remainder meets `ℝ e1` only in `0`; the one-base case. |
| `exists_retraction_of_family` | Corollary 8.39: if the sets `B i` are infinite there is a real linear `π` with `π e1 = 1` and `SC π (y i)` for every `i` (via `R4`). |

Not formalized: the sorted merged enumeration, the jointly lacunary family version of Proposition 8.38 (discharge of the base-span hypothesis from joint lacunarity), Lemma 8.40, Proposition 8.41, Proposition 8.37, and the answer to Question 9.5, which remains open.

## Question 9.5: sorted merge, families, Lemma 8.40, Proposition 8.41 (`PVGSorted`, 8 November 2026)

Module `LeanCheck/PVGSorted.lean` (imported by `LeanCheck.lean`; it imports `PVGMerged` and `PVGUncountable`), axiom report in `LeanCheck/PVGSortedAxioms.lean`. Same concrete setting as `PVGSequences`. Lean 4.35.0 and the same Mathlib build: no `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only.

| Declaration | Statement |
|---|---|
| `exists_sort` | An injective `f : α → β` with finite initial segments on an infinite `α` has an enumeration `σ : ℕ ≃ α` with `f ∘ σ` strictly increasing (rank). |
| `independence_listing`, `PairSep`, `listing_of_sep`, `independence_sep` | Theorem 8.36 with the paper's hypothesis (a listing of all terms with consecutive ratios tending to infinity), and in the pairwise form (for every `R` all but finitely many pairs of distinct terms have ratio at least `R`) from which the sorted listing is built. |
| `JointSep`, `disjoint_span_L_family`, `prop_uncountable_family`, `exists_retraction_of_joint_family` | Proposition 8.38 and Corollary 8.39 for a family of base sequences every finite subfamily of which satisfies the hypothesis of Theorem 8.36. |
| `corollary_indepB` | Corollary 8.35: thinning a lacunary sequence to a sparse set. |
| `lemma_separation` | Lemma 8.40 (separation), with the recursive choice of the proof. |
| `Depth`, `depth_admissible` | Proposition 8.41 (sequences of finite depth), by induction on the depth, with thinnings and finite-to-one maps into `B`. |

Not formalized: Proposition 8.37 (finitely and countably many sequences), infinite depth and the simultaneous choice, everything that needs the convergence `η_π`.
