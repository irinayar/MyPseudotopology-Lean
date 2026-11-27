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

## Question 9.5: Proposition 8.37, finitely and countably many sequences (`PVGFinite`, 8 November 2026)

Module `LeanCheck/PVGFinite.lean` (imported by `LeanCheck.lean`; it imports `PVGSorted`), axiom report in `LeanCheck/PVGFiniteAxioms.lean`. Same concrete setting as `PVGSequences`. Lean 4.35.0 and the same Mathlib build: no `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only.

| Declaration | Statement |
|---|---|
| `decomp` | A sequence in a finite-dimensional real inner product space has a subsequence `∑ i, f i • v i + ρ` with unit vectors `v i`, `ρ` convergent, `\|f i\| → ∞` and `\|f i'\|/\|f i\| → 0` for `i < i'` (strong induction on the dimension of a subspace containing the sequence). |
| `jointSep_fin`, `thin_joint` | Thinning to a subsequence along which all `\|f i (b t)\|` are jointly separated (the hypothesis of Theorem 8.36). |
| `finite_family` | Proposition 8.37, finite case: an infinite `B ⊆ C` such that the span of the differences `L (y j) U - L (y j) V` (`U, V` free containing `B`) meets `ℝ e1` only in `0`. |
| `countable_family` | Proposition 8.37, countable case (diagonal argument). |

Not formalized: the simultaneous choice for all lacunary sequences, infinite depth, everything that needs the convergence `η_π`.

## Section 8: pseudotopologies, `η_G`, the classification and the convergence statements (`PVGPseudo`, `PVGClassify`, `PVGMinimal`, `PVGCard`, 8 November 2026)

Modules `LeanCheck/PVGPseudo.lean`, `PVGClassify.lean`, `PVGMinimal.lean`, `PVGCard.lean` (imported by `LeanCheck.lean`), axiom reports in the matching `*Axioms.lean` files. Same concrete setting as `PVGSequences`. Lean 4.35.0 and the same Mathlib build: no `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only. The density of `e(ℝ)` in `K` (cited in the article) is the hypothesis `hdense : DenseRange e` where it is used (uniqueness of `G`, order reversal).

| Module | Declaration | Statement |
|---|---|---|
| `PVGPseudo` | `IsPseudoTop`, `PHausdorff`, `IsPVG`, `etaConv`, `bohrConv`, `Lr` | Definitions 2.1 to 2.3 (addition in the form of Lemma 2.4), the convergence `η_G` and the Bohr limit of an ultrafilter on `ℝ`. |
| | `exists_ultra_map`, `lr_add_decomp`, `etaConv_pvg` | Proposition 8.18 in general form: for an admissible `G`, `η_G` is a Hausdorff PVG coarser than the Bohr topology. |
| `PVGClassify` | `classify`, `etaConv_le_iff`, `etaConv_inj`, `classifyPVG` | Theorem 8.23: the Hausdorff PVGs coarser than the Bohr topology are exactly the `η_G`, `G` is unique, and `η_G` is coarser than `η_{G'}` iff `G' ≤ G`. |
| `PVGMinimal` | `etaConv_ker_iff`, `ultra_converges`, `minimal_ker` | Corollary 8.27(b), the convergence parts. |
| | `seqConv_iff`, `seqCompact_iff`, `lacred`, `admref` | Propositions 8.30 and 8.32. |
| | `noCoarsestPVG` | Corollary 8.25. |
| `PVGCard` | `card_free_ultra`, `card_K`, `rank_K` | `2^𝔠` free ultrafilters; `#K = 2^𝔠`, `dim_ℝ K = 2^𝔠` (Lemma 8.26(c)). |
| | `seqG_bounded`, `seqG_unbounded` | Proposition 8.28. |
| | `card_retractions_K`, `card_minimal`, `minimal_antichain` | Corollary 8.27(c). |
| | `block_sum_inverse` | The identity of Remark 8.42. |

Not formalized: Corollary 8.24 (pretopological iff `G` closed; it uses the cited minimality of the Bohr topology), the "not pretopological, not Fréchet–Urysohn" parts of Corollary 8.29, Proposition 2.5 and Sections 3 to 7.

## Section 2 and Corollary 8.29: null filters and non-Fréchet–Urysohn examples (`PVGNull`, `PVGNonzero`, 8 November 2026)

Modules `LeanCheck/PVGNull.lean` and `LeanCheck/PVGNonzero.lean` (imported by `LeanCheck.lean`), axiom reports in the matching `*Axioms.lean` files. No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only.

| Module | Declaration | Statement |
|---|---|---|
| `PVGNull` | `IsNullFamily`, `convOf`, `convOf_isPVG`, `convOf_hausdorff_iff` | Proposition 2.5 (first half) for an arbitrary real vector space: a family of filters with (i) to (iv) defines a PVG pseudotopology whose null filters are the members of the family; Hausdorff iff no nonempty filter `F` and `z ≠ 0` with `F` and `F - z` in the family. |
| | `nullFamily_of_pvg`, `conv_iff_translate`, `conv_eq_convOf` | Proposition 2.5 (second half): the null filters of a PVG form such a family and `F → x` iff `F - x → 0`. |
| `PVGNonzero` | `IsFU`, `euclid_coarser`, `exists_nonzero_admissible` | Fréchet–Urysohn property; `η_G` is coarser than the Euclidean convergence; `H_0` is a nonzero admissible subspace. |
| | `not_FU` | Corollary 8.29, last assertion (with `hdense : DenseRange e`): for an admissible `G` with `0 < dim G < 2^𝔠`, `η_G` is not Fréchet–Urysohn. |

Not formalized: that `η_G` is not pretopological for `G ≠ 0` (Corollary 8.24 and the cited minimality of the Bohr topology).

## Sections 3 to 7 and Corollary 8.24 (`PVGIdeal`, `PVGExamples`, `PVGBohr`, `PVGLacCount`, `PVGLacIdeal`, `PVGLacDilation`, `PVGLacMain`, `PVGClosed`, 8 November 2026)

Eight modules in `LeanCheck/` (imported by `LeanCheck.lean`), axiom reports in the matching `*Axioms.lean` files. No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only. Convergence relations are `Filter ℝ → ℝ → Prop`; "Euclidean convergence of `F` to `x`" is `F ≤ 𝓝 x`. The Bohr topology `bohrTop` is the topology induced by `e : ℝ → K`.

| Module | Declaration | Statement |
|---|---|---|
| `PVGIdeal` | `IsIdeal`, `xi_isPVG`, `xi_hausdorff` | Definition 6.1 (I1)–(I5) and Proposition 6.2 (first part), for a real vector space with a group topology with continuous dilations. |
| | `isPretop_iff_zero`, `xi_pretop_iff`, `xi_not_pretop`, `xi_not_topological` | Lemma 6.3, Theorem 6.4 (pretopology criterion), Corollary 6.5. |
| | `modTop`, `mem_modTop_iff` | Proposition 6.6 (topological modification and its description by closures). |
| `PVGExamples` | `discrete_isPVG`, `discrete_not_coarser` | Example 3.1. |
| | `countable_isPVG`, `countable_not_pretop`, `countable_not_topological` | Example 3.2 (the ideal of countable sets). |
| | `coarser_of_continuous_one`, `joint_euclid` | Proposition 3.3; Theorem 4.1 (joint continuity forces the Euclidean convergence). |
| `PVGBohr` | `bohr_isTopologicalAddGroup`, `bohr_t2`, `bohr_constSMul`, `bohr_coarser_euclid`, `bohr_unbounded` | Proposition 5.1 (a)–(d). |
| | `bohrConv_isPVG`, `bohr_not_euclid`, `bohr_not_jointCont` | Corollary 5.2. |
| `PVGLacCount` | `rep_of_mem_sumSet`, `lower_bound`, `count_bound` | Lemma 7.1 in a weaker form: for `ρ > 0` and every `L`, `Σ ∩ [-ρ s_L, ρ s_L]` is finite and `ncard² ≤ K s_L`, where the article states `K (log r)^k`. The power saving is what Lemmas 7.2 and 7.3 use. |
| `PVGLacIdeal` | `univ_not_mem_IS`, `IS_isIdeal` | Lemma 7.2 (`I_S` satisfies (I1)–(I5)). |
| `PVGLacDilation` | `exists_dilation` | Lemma 7.3 (Borel–Cantelli). |
| `PVGLacMain` | `lacConv_isPVG`, `lacConv_hausdorff`, `lac_coarser_euclid`, `lac_finer_bohr`, `lac_not_pretop`, `lac_not_topological`, `lac_not_euclid` | Theorem 7.4. |
| | `lac_modTop_le_euclid`, `bohr_le_lac_modTop`, `lac_ball_not_open` | Remark 7.6 (`τ_B ⊆ τ_ξ ⊆ τ_E`, `(-1,1)` not `τ_ξ`-open). |
| `PVGClosed` | `BohrMinimal` | The cited minimality of the Bohr topology among Hausdorff TVG topologies (Y1981), as an explicit hypothesis. |
| | `etaConv_pretop_closed` (with `DenseRange e`), `etaConv_topological_of_closed` | Corollary 8.24, two unconditional halves: `η_G` pretopological implies `G` closed; `G` closed implies `η_G` is the convergence of the topology induced by `ℝ → K/G`. |
| | `closed_eq_bot`, `closedPVG`, `closedPVG_bot` | Corollary 8.24 with `BohrMinimal`: pretopological iff closed iff `G = 0`. |
| | `nonzeroG_not_pretop`, `nonzeroG_not_topological`, `complement_ne_bot`, `minimal_not_pretop`, `minimal_not_topological` | The non-pretopological parts of Corollaries 8.29 and 8.27(c), with `BohrMinimal`. |

Not formalized: Section 8 results outside these (for example Propositions `bohrseq`, `finite`, `clusters`, `relaxed`, `ctblFU`, Theorems `notFU`, `clusterbound`, `extendFU`, `precompact` and the structure of `τ_ξ`), the sharper polylogarithmic bound in Lemma 7.1, the cited minimality of the Bohr topology, the simultaneous choice of the sets `B_y` (Question `compactFU`) and infinite depth, which are open questions.

## Section 8, sequences and the Fréchet–Urysohn property (`PVGSeqFU`, `PVGSeqFU2`, `PVGClusters`, 8 November 2026)

Three modules in `LeanCheck/` (imported by `LeanCheck.lean`), axiom reports in the matching `*Axioms.lean` files. No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only. Statements are cited by the labels of `PVG_v19.tex`.

| Module | Declaration | Statement |
|---|---|---|
| `PVGSeqFU` | `bohrseq` | Proposition `bohrseq`: a real sequence converges in the Bohr topology iff in the Euclidean topology (from Proposition `seqG` for `G = 0`). |
| | `xiB_seq`, `xiB_euclid_of_FU`, `xiB_eq_euclid_of_FU` | Theorem `notFU` (a), (b), (c) for an ideal `I` and `ξ = ξ_{τ_B, I}`. |
| | `lac_not_FU`, `lac_seq_iff` | Corollary `notFU` (a), (b) for the PVG of Theorem `main` (the sequential modification is not formalized). |
| | `beta_open_mod`, `relaxed_closed`, `relaxed_strict`, `finite_closed` | Propositions `finite` and `relaxed`, for an arbitrary real vector space with a group topology with continuous dilations. |
| | `countable_isFU` | Proposition `ctblFU`, first assertion. |
| `PVGSeqFU2` | `xiN`, `extend_seq`, `extend_euclid_of_FU`, `extend_eq_euclid` | Theorem `extendFU` (a), (b), (c), for a neighbourhood system `N` with `N x ≤ 𝓝_B x`. |
| | `countable_modTop` | Proposition `ctblFU`, last assertion: the topological modification of the countable PVG is the Euclidean topology. |
| | `lacclosed` | Proposition `lacclosed`: `{t_k}` with `|t_{k+1}| ≥ 5|t_k|` is closed in the Bohr topology (interpolation lemma). |
| `PVGClusters` | `K_nhds_zero_basic`, `exists_small_multiple`, `mem_closure_bohr`, `clusters` | Proposition `clusters`: `0 ∉ C` and `0 ∈ cl_{τ_B} C` for `C = ⋃_i {M_i h : 1 ≤ h ≤ H_i}` (pigeonhole in the torus). |

Not formalized in Section 8 (besides the items in the earlier sections of this file): Lemma `lacchar` (replaced by `interpolation_bounded`, which gives the same neighbourhood), Theorem `clusterbound` and Corollary `modstrict` (`τ_B ⊊ τ_ξ ⊊ τ_E`; the ingredients `lacclosed`, `clusters`, `relaxed_strict` and `lac_ball_not_open` are here), Proposition `precompact` (uses the structure of precompact group topologies), Corollary `notxiform`, Proposition `taustructure`, Remark `coherentproduct`.

## Cluster bound and strict modification (`PVGClusterBound`, `PVGModStrict`, 8 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom reports in the matching `*Axioms.lean` files.

| Module | Declaration | Statement |
|---|---|---|
| `PVGClusterBound` | `exists_clrep`, `clrep_inj`, `cluster_label` | The steps of the proof of Theorem `clusterbound`: representation `σ = ∑ d_n s_n` of an element of `[-m,m] + Σ`, admissible top index `T` (`4i² ≤ T² + a`, `T² ≤ 4i² + b + i`), uniqueness of `T`, and injectivity of the top coefficient on each layer. |
| | `clusterbound` | Theorem `clusterbound`: for `J ∈ I_S` there is `q` with `#(J ∩ {M_i h : 1 ≤ h ≤ i}) ≤ q` for all `i` (`M_i = 2^(4i²)`). |
| `PVGModStrict` | `Tc_closed`, `trace_closed` | For every `J ∈ I_S` the trace `J ∩ ⋃_i {M_i h}` is `τ_B`-closed (finite part plus finitely many ratio-5 sequences, `lacclosed`). |
| | `modstrict` | Corollary `modstrict`: `τ_B ⊆ τ_ξ ⊆ τ_E`, `τ_ξ ⊄ τ_B` (a set closed in `τ_ξ` but not in `τ_B`), `τ_E ⊄ τ_ξ` (the interval `(-1,1)`). |

Still not formalized in Section 8: Lemma `lacchar` (replaced by `interpolation_bounded`), Proposition `precompact`, Corollary `notxiform`, Proposition `taustructure`, Remark `coherentproduct`.

## Corollary `notxiform`, structure of the modification, coherent product (`PVGSec8Rest`, 8 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGSec8RestAxioms.lean`.

| Declaration | Statement |
|---|---|
| `AdmPair`, `notxiform` | Corollary `notxiform`, with the cited minimality of the Bohr topology (`BohrMinimal`) as a hypothesis: `η_G` for an admissible `G ≠ 0` is a Hausdorff PVG, coarser than the Euclidean convergence, and is not `ξ_{β,I}` for any admissible pair. |
| `tau_open_iff` | Proposition `taustructure` (a), for any ideal `I` and group topology `β`: `U` is open in the modification iff for every `J ∈ I` and `x ∈ U ∩ J` some neighbourhood `W` of `x` has `W ∩ J ⊆ U`. |
| `tau_unbounded` | Proposition `taustructure` (b) for the lacunary PVG: every nonempty open set of the modification is Euclidean-unbounded. |
| `tau_seq_iff` | Proposition `taustructure` (c), sequences: convergent sequences of the modification are the Euclidean convergent ones. |
| `cohTop`, `prod_le_coh`, `add_continuous_coh` | Remark `coherentproduct`: the coherent topology on `ℝ × ℝ` contains the product of the modification with itself, and addition is continuous from it into the modification. |

Not formalized: the statement on compact sets in Proposition `taustructure` (c) (uses Glicksberg's theorem), Proposition `precompact` (uses the structure of precompact group topologies and the classification of continuous characters of `ℝ`), Lemma `lacchar` (replaced by the interpolation lemma).

## Weak topologies of dilation-invariant character subgroups (`PVGWeak`, 8 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGWeakAxioms.lean`. For a real subspace `D ≤ K` (invariant under the dilation operators `D_c`), `weakTop D` is the initial topology on `ℝ` of the characters in `D`; `WD D` is `ℝ` with this topology as a type synonym.

| Declaration | Statement |
|---|---|
| `weakW_inducing`, instances | `weakTop D` is a group topology and every dilation is continuous (because `D` is a subspace). |
| `weakW_continuous_char` | Every `d ∈ D` is continuous. |
| `weakW_t2` | Hausdorff if `e(b) ∈ D` for all `b`. |
| `weakTop_le_bohr` | It contains the Bohr topology if `e(b) ∈ D` for all `b`. |

For `D = e(ℝ) ⊕ G`, `G` admissible, this is the TVG-side counterpart of `η_G` (same `G`, finer than `τ_B` instead of coarser). That its dual is `D`, and that it is strictly finer than `τ_B` for `G ≠ 0`, use Pontryagin duality and the classification of continuous characters of `ℝ`; they are not formalized.

## No unbounded null sequences for group topologies inside the Euclidean one (`PVGSeqGen`, 9 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGSeqGenAxioms.lean`.

| Declaration | Statement |
|---|---|
| `exists_closed_nhds_sub` | In a Hausdorff topological additive group every neighbourhood `W` of `0` contains `V - V` for a closed neighbourhood `V` of `0`. |
| `no_unbounded_null_seq` | Let `X` be a real vector space with a Hausdorff group topology in which every fixed dilation is continuous, and `ι : ℝ →ₗ[ℝ] X` a continuous (Euclidean) linear injection. If `\|x_k\| → ∞` then `ι(x_k)` does not tend to `0`. Proof by Baire category. |

For `X = (ℝ, β)` and `ι = id` the hypotheses say that `β` is a Hausdorff group topology inside the Euclidean topology with continuous dilations. The consequences that such a `β` has the same convergent sequences as the Euclidean topology and is therefore not sequential (otherwise it would equal the Euclidean topology and contain the Bohr topology) are hand-checked and not formalized.

## Convergent sequences for group topologies inside the Euclidean one (`PVGSeqGen2`, 9 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGSeqGen2Axioms.lean`. Same abstract setting as `PVGSeqGen`: `X` a real vector space with a Hausdorff group topology in which every fixed dilation is continuous, `ι : ℝ →ₗ[ℝ] X` a Euclidean-continuous linear injection.

| Declaration | Statement |
|---|---|
| `seq_conv_euclid` | If `ι(x_k) → ι(a)` in `X`, then `x_k → a` in `ℝ` (parts: Baire lemma `no_unbounded_null_seq`, Bolzano–Weierstrass, uniqueness of limits). |
| `isEmbedding_of_sequential` | If the subspace `ι(ℝ)` of `X` is a sequential space, then `ι` is a topological embedding. |

For `X = (ℝ, β)` and `ι = id` these are parts (b) and (c) of Proposition 8.44 of PVG_v21: the `β`-convergent sequences are the Euclidean convergent ones, and a sequential `β` equals the Euclidean topology. The instance `X = (ℝ, β)` is not stated separately in Lean.

## Existence of a monothetic topology below the Euclidean one: parts of the proof (`PVGBetaDense`, `PVGBetaHalf`, 9 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom reports in `PVGBetaDenseAxioms.lean` and `PVGBetaHalfAxioms.lean`. These cover two steps of the proof of Theorem `thm:betaexists` of PVG_v22; the other steps are not formalized.

`PVGBetaDense` (abstract setting of `PVGSeqGen`: `X` a real vector space with a group topology and continuous fixed dilations, `ι : ℝ →ₗ[ℝ] X` Euclidean-continuous; for `X = (ℝ, β)`, `ι = id` this is a group topology `β` inside the Euclidean topology with continuous dilations):

| Declaration | Statement |
|---|---|
| `half_mem_closure` | If every neighbourhood of `0` contains some `ι(k + 1/2)`, then `ι(1/2)` lies in the closure of `ι(ℤ)`. |
| `dyadic_mem_closure` | Then `ι(j/2^n)` lies in the closure of `ι(ℤ)` for all integers `j` and `n ∈ ℕ` (dilation by `1/2` maps the closure into itself). |
| `range_subset_closure` | Then `ι(x)` lies in the closure of `ι(ℤ)` for every real `x` (dyadic rationals are dense and `ι` is continuous): `ι(ℤ)` is dense in `ι(ℝ)`. |

`PVGBetaHalf` (Lemma `lem:halfint`): `KroneckerDensity` (Kronecker's density theorem: `1, β₁, …, β_w` linearly independent over `ℚ` implies that for every target `θ` and `ε > 0` some integer `k` has `‖kβ_s − θ_s‖ < ε` for all `s`) is an explicit hypothesis, not proved; Mathlib has only the one-dimensional case.

| Declaration | Statement |
|---|---|
| `half_integer_witness` | Assume `KroneckerDensity`. If `y₁, …, y_M` are reals and `1` is not in their rational linear span, then for every `ε > 0` there is an integer `k` with `‖(k + 1/2) y_l‖ < ε` for all `l` (rational basis of the span, common denominator, Kronecker with target `−β/2`). |

Not formalized: Lemma `lem:deletion` (deletion of centers, which uses the additivity of transcendence degree; Mathlib has `Algebra.trdeg_add_eq` and `AlgebraicIndependent.extendScalars`), the Cantor-type construction of the measure and the estimate of `ρ`, and Proposition `prop:noFUxi`.

## Deleting centers (`PVGBetaDelete`, 9 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGBetaDeleteAxioms.lean`. Lemma `lem:deletion` of PVG_v22 (this replaces the sentence above that said it was not formalized).

| Declaration | Statement |
|---|---|
| `one_not_mem_span` | If the numbers `x_j`, `j ∈ T`, are algebraically independent over the subring `ℚ[c₁, …, c_m]` of `ℝ`, then `1` is not in the rational linear span of the products `c_i x_j`, `j ∈ T` (a nonzero polynomial `Σ a_j Y_j − 1` over `ℚ[c]` would vanish). |
| `exists_indep_subfamily` | If `x₁, …, x_N` are algebraically independent over `ℚ`, there is a set `T` of indices with `N ≤ m + |T|` such that `x_j`, `j ∈ T`, are algebraically independent over `ℚ[c₁, …, c_m]`. Proof: the transcendence degree of `ℚ[c]` over `ℚ` is at most `m` (surjection from `ℚ[Y₁, …, Y_m]`), the tower law `trdeg_add_eq`, a transcendence basis of `ℚ[c][x]` over `ℚ[c]` among the `x_j`. |
| `deletion` | The lemma: there is `T` with `N ≤ m + |T|` and `1 ∉ span_ℚ {c_i x_j : i ≤ m, j ∈ T}`; the complement of `T` has at most `m` elements. |

## Admissible pairs below the Euclidean convergence (`PVGNoFU`, 9 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGNoFUAxioms.lean`. Proposition `prop:noFUxi` of PVG_v22. The Euclidean topology is written `eT` so that a variable topology `β` on `ℝ` does not capture the default instance.

| Declaration | Statement |
|---|---|
| `euclid_le_of_coarse` | If every Euclidean convergent filter converges for `ξ_{β,I}`, then every `β`-open set is Euclidean open (apply coarseness to the neighbourhood filter `𝓝 x`). |
| `seq_euclid_of_group_topology` | For a Hausdorff group topology `β` on `ℝ` with continuous dilations, inside the Euclidean topology, a `β`-convergent sequence is Euclidean convergent (`PVG.Gen.seq_conv_euclid` for `X = (ℝ, β)`, `ι = id`). |
| `noFU_xi_of_seq` | The Fréchet–Urysohn argument for an abstract `β` whose convergent sequences are Euclidean convergent: a `ξ_{β,I}`-convergent filter that does not contain a Euclidean neighbourhood is refined by the complement of that neighbourhood, and the Fréchet–Urysohn property gives a sequence in the complement converging to the point. |
| `noFU_xi` | **The proposition.** For a Hausdorff group topology `β` with continuous dilations, an ideal `I` and `ξ = ξ_{β,I}`: if `ξ` is coarser than the Euclidean convergence and Fréchet–Urysohn (`IsFU`), then `ξ`-convergence of a filter is equivalent to Euclidean convergence. |

## The existence theorem assembled from a measure with the stage property (`PVGBetaTop`, `PVGBetaRho`, `PVGBetaStage`, `PVGBetaMain`, 9 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom reports in `PVGBetaTopAxioms.lean`, `PVGBetaRhoAxioms.lean`, `PVGBetaStageAxioms.lean`, `PVGBetaMainAxioms.lean`. Theorem `thm:betaexists` of PVG_v22. **Not formalized:** the Cantor-type construction (nested intervals around algebraically independent centers, with the radii chosen after the finite families of witnesses) and the construction of the measure; its output enters `PVGBetaMain` as the hypothesis `StageProperty μ`. Kronecker's density theorem enters `PVGBetaStage` as the hypothesis `KroneckerDensity` of `PVGBetaHalf`.

`PVGBetaTop` (abstract pseudonorm `ρ`, `IsPseudoNorm ρ K`: `ρ 0 = 0`, `ρ ≥ 0`, even, subadditive, `ρ t ≤ K|t|`, `ρ t > 0` for `t ≠ 0`): `betaTop` is the topology with base `V(F,δ) = {t : ρ(ct) < δ for all c ∈ F}` at `0` (`AddGroupFilterBasis`).

| Declaration | Statement |
|---|---|
| `betaTop_isTopologicalAddGroup`, `betaTop_t2`, `eT_le_betaTop`, `betaTop_constSMul` | Part (a): a Hausdorff group topology, inside the Euclidean topology, with all dilations continuous. |
| `half_in_nhds` | If `HalfInt ρ` (every basic set contains a half-integer), every neighbourhood of `0` contains one. |
| `chi_one_not_continuous`, `chi_not_continuous` | Part (c): the characters `t ↦ bt + ℤ`, `b ≠ 0`, are not continuous (`chi b`). |
| `int_dense` | `ℤ` is dense (through `PVG.Gen.range_subset_closure`). |

`PVGBetaRho`: `gf θ = min 1 (2π‖θ‖)`, `rho μ t = ∫ gf(tλ) dμ`. `isPseudoNorm_rho`: for a probability measure carried by `[1,2]` without atoms, `rho μ` is a pseudonorm with `K = 4π` (`gf_add_le`, `gf_le_lin`, `gf_eq_zero`, `rho_pos` from the absence of atoms). `rho_le_of_good`: if `‖aλ‖ < ε` on a measurable set `G` then `rho μ a ≤ 2πε + μ(Gᶜ)`.

`PVGBetaStage` (Claim A): `witness_pointwise` (for one `c` in `ℝⁿ`: an integer `k` and at most `n` excluded indices with `‖c_i (k + 1/2) x_j‖ < ε` for the others; from `deletion` and `half_integer_witness`), `finite_witnesses` (a finite family of witnesses serves every `c` of the box `[-n,n]ⁿ`; compactness).

`PVGBetaMain`: `halfInt_of_stages` (a probability measure with `StageProperty` gives `HalfInt (rho μ)`: pad a finite set of dilations to a vector of the box), `exists_beta_of_stage_measure` (for an atomless probability measure `μ` carried by `[1,2]` with `StageProperty μ`: `betaTop` is a Hausdorff group topology inside the Euclidean one with continuous dilations, every neighbourhood of `0` contains a half-integer, no character `t ↦ bt + ℤ`, `b ≠ 0`, is continuous, and `ℤ` is dense).

## The construction of the measure and the full existence theorem (`PVGBetaCantor`, `PVGBetaChoose`, 9 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom reports in `PVGBetaCantorAxioms.lean` and `PVGBetaChooseAxioms.lean`. With these two modules Theorem `thm:betaexists` of PVG_v22 is formalized in full; **Kronecker's density theorem is the only hypothesis** (`KroneckerDensity` of `PVGBetaHalf`; Mathlib has only the one-dimensional case).

`PVGBetaCantor`: a *stage system* `Stages x r` is a family of centers `x n a` (`a < 2^n`) and radii `r n` such that the closed intervals `Iv x r n a = [x n a − r n, x n a + r n]` are nested (children of `(n,a)` are `(n+1, 2a)`, `(n+1, 2a+1)`), pairwise disjoint at each level, `Iv x r 0 0 = [1,2]`, and satisfy the witness property `P`.

| Declaration | Statement |
|---|---|
| `Stages.sep` | Distinct intervals of one level are disjoint (induction using the sibling and nesting axioms). |
| `psi`, `Stages.seq_tendsto`, `Stages.psi_mem`, `Stages.psi_aemeasurable` | The digits of `u ∈ [0,1)` give a Cauchy sequence of centers; the limit `psi u` lies in the interval of every level; `psi` is measurable. |
| `cantorMeasure`, `Stages.isProb`, `Stages.mass_ge`, `Stages.supp`, `Stages.null_single` | The image of Lebesgue measure on `[0,1)` is a probability measure, gives mass at least `2^{-n}` to each level-`n` interval, is carried by `[1,2]` and has no atoms. |
| `Stages.stageProperty`, `exists_measure_of_stages` | It has the stage property of `PVGBetaMain`. |

`PVGBetaChoose` (with `KroneckerDensity`):

| Declaration | Statement |
|---|---|
| `exists_new_center`, `exists_family` | In every open interval there is a real number transcendental over the ring generated by finitely many given numbers (the algebraic numbers over a countable ring form a countable set); hence algebraically independent numbers in prescribed open intervals. |
| `exists_next` | From a stage of positive radius: new centers in the parent intervals, algebraically independent; radius chosen after the finite family of witnesses of `PVGBetaStage`, so that nesting, separation of siblings and the witness property hold. |
| `exists_stages`, `exists_stage_measure` | A stage system exists (recursion), hence a measure with the stage property. |
| `exists_beta` | **Theorem `thm:betaexists`**: for `KroneckerDensity`, there is a topology `β` on `ℝ` that is a Hausdorff group topology, inside the Euclidean topology, with all dilations continuous, every neighbourhood of `0` contains a half-integer, no character `t ↦ bt + ℤ` (`b ≠ 0`) is continuous, and `ℤ` is dense. |

## Kronecker's density theorem and the existence theorem without hypotheses (`PVGKronecker`, `PVGBetaFinal`, 9 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom reports in `PVGKroneckerAxioms.lean` and `PVGBetaFinalAxioms.lean`. This removes the hypothesis `KroneckerDensity` of the earlier modules.

`PVGKronecker` (Weyl's proof, using Mathlib's `UnitAddTorus`, the exponential monomials `mFourier`, and `span_mFourier_closure_eq_top`):

| Declaration | Statement |
|---|---|
| `avg`, `trans`, `avg_norm_le`, `mFourier_nsmul` | The averages `(1/K) Σ_{k<K} g(kb)` along an orbit of the torus, their norm bound, and `mFourier n (k b) = (mFourier n b)^k`. |
| `z_ne_one` | If `1, β₁, …, β_w` are linearly independent over `ℚ` and `n ≠ 0`, then `mFourier n (β) ≠ 1`. |
| `avg_char_tendsto` | For `n ≠ 0` the averages of `mFourier n` tend to `0` (geometric series bound `2/(K ‖z − 1‖)`). |
| `hasLim_char`, `hasLim_span` | The averages of a trigonometric polynomial and of all its translates have a common limit (induction on the span). |
| `trans_asymp` | For every continuous `g` and every translation `a`, `avg(g(· + a)) − avg(g) → 0` (density of trigonometric polynomials, `ε/4` argument). |
| `kronecker_density` | `KroneckerDensity`: the orbit `(kβ₁, …, kβ_w)` is dense modulo `1` (a bump function around the target, a finite family of translates covering the torus, and the averages of the translates tending to `0` against a lower bound `c > 0`). |

`PVGBetaFinal`: `exists_beta_unconditional`, the existence theorem of `PVGBetaChoose` (`exists_beta`) applied to `kronecker_density`: there is a Hausdorff group topology on `ℝ` inside the Euclidean topology with all dilations continuous, every neighbourhood of `0` contains a half-integer, no character `t ↦ bt + ℤ` (`b ≠ 0`) is continuous, and `ℤ` is dense.

## The variant with the recurrence property and the admissible pair `(β, I_S)` (`PVGBetaQStage`, `PVGBetaQCantor`, `PVGBetaQChoose`, `PVGBetaQMain`, 9 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom reports in `PVGBetaQStageAxioms.lean`, `PVGBetaQCantorAxioms.lean`, `PVGBetaQChooseAxioms.lean`, `PVGBetaQMainAxioms.lean`. No hypothesis (Kronecker's theorem is `kronecker_density`); the minimality of the Bohr topology enters only in `not_le_bohr`, as the explicit hypothesis `BohrMinimal` of `PVGClosed`.

`PVGBetaQStage` (property `(Q_n)`, no algebraic independence needed):

| Declaration | Statement |
|---|---|
| `Qprop` | For every vector `c` of the box `[-n,n]^n` there are `p > q ≥ n` with `‖c_i (s_p − s_q) λ‖ < 1/n` for all `i ≤ n` and all `λ` in all intervals of level `n` (`s_n = 2^(n²)`). |
| `witness_Q_pointwise` | Pigeonhole in the compact torus: for one `c` and finitely many centers there are `p > q ≥ n` with all `‖c_i (s_p − s_q) x_j‖ < ε`. |
| `finite_witnesses_Q` | A finite family of such pairs serves the whole box (open neighbourhoods, compactness). |
| `exists_Q_radius` | After the choice of the centers, a radius `r'' ≤ r'` can be chosen so that the stage has `Qprop` (`n T r'' < 1/(2n)`). |

`PVGBetaQCantor`: `StagesQ` (the stage system `Stages` with the extra field `Q`), `StagesQ.recurProp` (the Cantor-type measure is carried by the intervals of every level, so `Qprop` gives the recurrence on a set of full measure), `recur_rho` (property `(Q)` for `ρ_μ`: for every finite `F`, `δ > 0`, `N` there are `p > q ≥ N` with `ρ_μ(c (s_p − s_q)) < δ` for all `c ∈ F`).

`PVGBetaQChoose`: `Pprop_mono`, `exists_nextQ` (one step: `exists_next` followed by `exists_Q_radius`), `exists_stagesQ`, `exists_Q_measure` (a probability measure without atoms, carried by `[1,2]`, with the stage property and the recurrence property).

`PVGBetaQMain`:

| Declaration | Statement |
|---|---|
| `RecurTop`, `recur_betaTop` | The recurrence property for the neighbourhoods of `0`: `c (s_p − s_q) ∈ W` with `p > q ≥ N`; it holds for `betaTop` of `ρ_μ` when `μ` has `RecurProp`. |
| `zero_mem_closure_D_beta` | If `β` has `RecurTop`, `c t ∈ A` for only finitely many `t ∈ T`, then `0 ∈ closure_β (Dset c A)`. |
| `xiIS_main` | For a Hausdorff group topology `β` inside the Euclidean topology with continuous dilations and `RecurTop`, `ξ_{β,I_S}` is a Hausdorff PVG, coarser than the Euclidean convergence, **not pretopological**, not Euclidean, and not Fréchet–Urysohn (with `noFU_xi`). |
| `exists_beta_Q` | There is a `β` with all the properties of `exists_beta_unconditional` and `RecurTop`. |
| `chi_continuous_bohr`, `ne_bohr`, `not_le_bohr` | The characters are `τ_B`-continuous, so `β ≠ τ_B`; with `BohrMinimal`, `¬ (τ_B ≤ β)` in Lean's order, that is, `β` is not contained in `τ_B`. |

## An `I_S`-thin cluster set (`PVGThinSet`, 9 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGThinSetAxioms.lean`. Formal counterpart of Proposition `thinset` of `PVG_v24`.

| Declaration | Statement |
|---|---|
| `Mt`, `Ct` | `M_i = (i+1) s_{i+1}` and `Ct = ⋃_i {M_i h : 1 ≤ h ≤ i}` (`s_n = 2^(n²)`). |
| `not_mem_of_large` | If `j` is large, no element `z` with `j s_j ≤ |z| ≤ j² s_j` lies in `[-m,m] + ∑ d_n s_n` with coefficients `d_n` in a finite set (case analysis on the largest nonzero index: `≤ j` gives `|z| ≤ m + 2 c₁ s_j < j s_j`; `≥ j+1` gives `|z| ≥ c₀ 2^{2j} s_j − m > j² s_j`), using `lower_bound` and `geom_sS` of `PVGLacCount`. |
| `thin_Ct` | `Ct ∩ J` is finite for every `J ∈ I_S`. |
| `thin_cluster_modstrict` | `0 ∉ Ct`, `0 ∈ cl_{τ_B} Ct` (`clusters`), `ℝ ∖ Ct` is `τ_ξ`-open (`finite_closed`) and not `τ_B`-open; so `τ_B ⊊ τ_ξ` is witnessed by a set meeting every member of `I_S` in a finite set. |

## The pair `(β, I)` and the topological modification (`PVGModXi`, 9 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGModXiAxioms.lean`. All topologies are written explicitly (`@IsOpen X β`, `@xiConv X γ I`) so that no local instance is captured.

| Declaration | Statement |
|---|---|
| `xi_eq_of_between` | If every `β`-open set is `γ`-open and every `γ`-open set is open in the topological modification `modTop (ξ_{β,I})`, then `ξ_{γ,I} = ξ_{β,I}` (no group structure needed). |
| `xi_modTop_eq` | `ξ_{τ_ξ, I} = ξ_{β,I}`: the pair `(β, I)` may be replaced by `(τ_ξ, I)`. |

## An unbounded convergent sequence and the Hausdorff property of the modification (`PVGBaireHaus`, `PVGBaireHaus2`, 10 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGBaireHausAxioms.lean`. `ConvOpen conv U` means that `U` is open in the topological modification `modTop conv`. The proof of `theorem_A` uses only translations, dilations and Baire's theorem, not addition of neighbourhoods. The statements are for `X = ℝ`.

| Declaration | Statement |
|---|---|
| `baire_step` | If `ℝ = ⋃ D N`, every nonempty open `V` meets `interior (closure (D N))` for some `N` (Baire's theorem for the closed sets `closure (D N)`). |
| `convOpen_isOpen` | If `conv` is coarser than the Euclidean convergence, `conv`-open sets are Euclidean open. |
| `convOpen_translate`, `convOpen_dilate` | `{w \| w + x ∈ U}` is `conv`-open if `U` is; if `U ∋ 0` is `conv`-open and `u → 0` for `conv`, then `a * u k ∈ U` eventually, for every real `a`. |
| `theorem_A` | **Theorem A.** Let `conv` be a PVG on `ℝ` coarser than the Euclidean convergence and `u` a sequence with `conv (map u atTop) 0` and `∀ R N, ∃ n ≥ N, R < \|u n\|`. Then every `conv`-open neighbourhood of `0` meets every `conv`-open neighbourhood of every real `x`; in particular the modification is not Hausdorff. |
| `seq_euclid_of_hausdorff` | If, in addition, any two different points have disjoint `conv`-open neighbourhoods, every `conv`-convergent sequence converges in the Euclidean topology (Theorem A for unbounded translates; a Euclidean limit different from the `conv`-limit for bounded ones). |
| `noFU_xi_of_xiseq` | The argument of `noFU_xi_of_seq` with the hypothesis on `ξ`-convergent sequences. |
| `noFU_of_hausdorff_topology` | For an arbitrary Hausdorff topology `γ` on `ℝ` (no group structure) and an ideal `I` such that `ξ_{γ,I}` is a PVG: if `ξ_{γ,I}` is coarser than the Euclidean convergence and Fréchet–Urysohn, it is the Euclidean convergence. |

## Pretopological and topological PVGs coincide (`PVGPretopTop`, 10 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGPretopTopAxioms.lean`. For a PVG on a real vector space, `V(0) → 0` gives a topology whose neighbourhood filters are the `V(x)`; only continuity of addition at `(0,0)` (`V(0) + V(0) ≥ V(0)`) and `p2` are used.

| Declaration | Statement |
|---|---|
| `zero_mem_of_mem_Vfil` | Members of `V(0)` contain `0`. |
| `Vfil_add_small` | For `U ∈ V(0)` there is `W ∈ V(0)` with `x + y ∈ U` for all `x, y ∈ W` (from `V(0) + V(0) → 0`). |
| `pretop_isTopological` | A pretopological PVG is the convergence of a topology (`U` open iff `{z \| x + z ∈ U} ∈ V(0)` for all `x ∈ U`). |
| `isPretop_iff_isTopological` | For a PVG, pretopological iff topological. |

## A Boolean algebra of lacunary PVGs (`PVGSubIdeal`, `PVGSubGap`, `PVGSubMain`, `PVGSubFinite`, `PVGSubTop`, 10 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGSubAxioms.lean`. For `A ⊆ ℕ`: `SsetA A = {0} ∪ {±s_n : n ∈ A, n ≥ 1}`, `sumSetA A l`, `IA A` the sets contained in `[-m,m] + a₁S_A + … + a_kS_A`, `subConv A = ξ_{τ_B, I_A}`. Not formalized: `I_A ∩ I_B = I_{A ∩ B}` (hand proof only).

| Declaration | Statement |
|---|---|
| `IA_isIdeal` | `I_A` satisfies (I1) to (I5) (`ne_univ` from `I_A ⊆ I_S`, `IA_sub_IS`). |
| `IA_mono`, `IA_mono_of_diff_finite` | `A ⊆ B` or `A \ B` finite implies `I_A ⊆ I_B` (`sumSetA_approx`). |
| `rep_of_mem_sumSetA`, `sigma_dichotomy` | Representation `∑ d_n s_n` of the elements of `a₁S_A + … + a_kS_A` with `d_n = 0` for `n ∉ A`; if `d_j = 0` then `\|σ\| ≤ 2 c₁ s_{j-1}` or `\|σ\| ≥ c₀ s_{j+1}/2`. |
| `top_index` | **Lemma (top index).** If `n ∉ A` is large, no `z = e + σ` with `\|e\| ≤ m`, `σ ∈ a₁S_A + … + a_kS_A`, satisfies `γ₁ s_n ≤ \|z\| ≤ γ₂ s_n`. |
| `subConv_isPVG`, `subConv_hausdorff`, `subConv_coarser_euclid`, `subConv_finer_bohr` | `ξ_A` is a Hausdorff PVG between the Bohr topology and the Euclidean convergence. |
| `zero_mem_closure_DA`, `DsetA_inter_finite` | `0` is in the Bohr closure of `D = {c(s_n - s_l) : n, l ∈ A, l < n} \ J` (for `c` as in `exists_dilation`); if `C ∩ B = ∅` and `J ∈ I_B`, then `J ∩ {s_n - s_l : n, l ∈ C}` is finite. |
| `conv_sub_iff` | Every `ξ_A`-convergent filter is `ξ_B`-convergent iff `A \ B` is finite. |
| `subConv_eq_euclid_of_finite` | `ξ_A` is the Euclidean convergence for finite `A` (`bohr_nhds_trace`). |
| `subConv_not_pretop`, `subConv_not_topological`, `subConv_not_FU` | For infinite `A`, `ξ_A` is not pretopological, not topological and not Fréchet–Urysohn. |
| `modTop_sub_iff` | Every open set of `modTop (ξ_B)` is open in `modTop (ξ_A)` iff `A \ B` is finite (`ℝ \ D_C` for `C = A \ B`). |

## Joins in the Boolean algebra of lacunary PVGs (`PVGJoinLr`, `PVGJoinMain`, 10 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGJoinAxioms.lean`. For `A, B ⊆ ℕ`, `subConv A = ξ_{τ_B, I_A}` as in `PVGSubMain`. The proof uses the independence theorem for jointly lacunary sequences (`independence_sep` of `PVGSorted`) for the two enumerations `y^A`, `y^B` (`ys_joint`, `lam_indep`). Not formalized: the identity `I_A ∩ I_B = I_{A ∩ B}` (meets).

| Declaration | Statement |
|---|---|
| `exists_lift`, `exists_split` | An ultrafilter containing a sum set `X + Y` is the image of an ultrafilter on `ℝ × ℝ`; it is finer than the sum filter of the projections and its Bohr limit is the sum of the Bohr limits. |
| `Esub`, `LamA`, `Lr_SsetA_mem`, `Lr_sumSetA_mem` | For infinite `A`, the Bohr limit of an ultrafilter containing `a₁S_A + … + a_kS_A` lies in `e(ℝ) + Λ_A`, `Λ_A` the real span of the limits `L_{y^A}(W)`, `W` free. |
| `sumSetA_union_sub` | `a₁S_{A ∪ B} + … ⊆ (a₁S_A + …) + (a₁S_B + …)`. |
| `ys_joint`, `lam_indep` | For disjoint infinite `A`, `B`: `y^A`, `y^B` satisfy the hypothesis of the independence theorem, and `λ₁ ∈ Λ_A`, `λ₂ ∈ Λ_B`, `λ₁ + λ₂ ∈ e(ℝ)` imply `λ₁ = λ₂ = 0`. |
| `join_ultra`, `join_core`, `join_least` | **Theorem (joins).** If `conv` is a PVG (`IsPVG`) in which every `ξ_A`-convergent and every `ξ_B`-convergent filter converges, then every `ξ_{A ∪ B}`-convergent filter converges (disjoint case, then general). |
| `subConv_union_isLeast` | `ξ_{A ∪ B}` is a PVG containing `ξ_A` and `ξ_B`, and the least such. |

## Meets in the Boolean algebra of lacunary PVGs (`PVGSubInter`, 10 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGSubInterAxioms.lean`. Formalizes Theorem 8.63 (d): `I_A ∩ I_B = I_{A ∩ B}`.

| Declaration | Statement |
|---|---|
| `rep2_of_mem_sumSetA` | The representation `∑ d_n s_n` of the elements of `a₁S_A + … + a_kS_A`, with `d_n ≠ 0 → n ∈ A, n ≥ 1`, coefficients in `Cset l` and at most `k` nonzero terms. |
| `agree_above` | Two such expansions (for `A`, `B`) with bounded difference have equal coefficients above a bound that depends only on the coefficient lists and on the bound (lower bound for the top coefficient). |
| `finite_sum_mem` | A sum of at most `k` terms `d_n s_n`, `n ∈ A'`, `d_n` in a finite set `C`, lies in `sumSetA A'` of the fixed list `C.toList.flatMap (replicate k)`. |
| `IA_inter`, `IA_inter_iff` | `J ∈ I_A ∩ I_B` implies `J ∈ I_{A ∩ B}`; `I_{A ∩ B} = I_A ∩ I_B`. |
| `subConv_inter_iff`, `subConv_inter_coarsest` | A filter converges for `ξ_{A ∩ B}` iff it converges for `ξ_A` and `ξ_B`; `ξ_{A ∩ B}` is a PVG, finer than both, and the coarsest such. |

## Semitopological structure, first countability, local compactness and the Baire property (`PVGSemiTop`, `PVGNotLC`, 11 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom reports in `PVGSemiTopAxioms.lean` and `PVGNotLCAxioms.lean`. Formalizes Propositions 8.66, 8.67 and 8.70 of PVG_v30 (hand proofs there; the Lean statements below are for `tauA A = modTop (subConv A)`, the topological modification of `ξ_{τ_B, I_A}`, `s_n = 2^(n^2)`).

| Declaration | Statement |
|---|---|
| `modTop_translate_isOpen`, `modTop_continuous_add_const` | For a PVG `conv` on a real vector space, every translation is continuous for `modTop conv`. |
| `closure_add_closure_subset_of_translations`, `closure_add_closure_modTop` | Proposition 8.67: `cl X + cl Y ⊆ cl (X + Y)` (abstract form for a topology with continuous translations; for `modTop conv`). |
| `bohrOpen_isOpen_tauA`, `bohrClosed_isClosed_tauA`, `Icc_bohrClosed` | `τ_B ⊆ τ_{ξ_A}`; the intervals `[a, b]` are Bohr closed. |
| `tauA_nhds_zero_unbounded`, `tauA_mem_nhds_zero_unbounded`, `tauA_unbounded_of_nonempty` | Proposition 8.66 (a): for `A` infinite every `tauA A`-neighbourhood of `0` contains arbitrarily large positive numbers; every nonempty open set is unbounded. |
| `exists_five_seq`, `sub_range_bohrClosed` | Sequences with `5 z_j < z_{j+1}` in prescribed sets; every subset of `{z_j}` is Bohr closed (Proposition 8.7 applied to subsequences, `lacclosed`). |
| `tauA_not_countablyGenerated` | Proposition 8.66 (b): the neighbourhood filter of `0` in `tauA A` is not countably generated. |
| `infinite_closed_discrete_not_compact` | An infinite injective sequence all of whose subsets are closed does not lie in a compact set (generic topology). |
| `tauA_not_locallyCompact`, `tauA_not_baire` | Proposition 8.70: `tauA A` is not locally compact and not a Baire space (ℝ is the union of the closed nowhere dense sets `[-n, n]`). |

## The reduction behind condition (N) (`PVGNTrace`, 11 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGNTraceAxioms.lean`. Formalizes the reduction of Question 9.2 to condition (N) (research note, Addenda AC and AI; hand proof there). Inclusions of topologies are stated with open sets.

| Declaration | Statement |
|---|---|
| `modTop_trace_eq` | For any family `I` of subsets of `ℝ`, the topological modification of `ξ_{τ_B, I}` induces on every `J ∈ I` exactly the Bohr trace (no group-topology hypothesis). |
| `lac_trace_eq`, `sub_trace_eq` | The cases `I = I_S` and `I = I_A`. |
| `bohr_open_lac`, `lac_open_euclid`, `lac_strict` | `τ_B ⊆ τ_ξ ⊆ τ_E`, and the complement of the thin set `C_t` is `τ_ξ`-open but not Bohr-open. |
| `N_of_group` | If `τ_ξ = modTop lacConv` is a group topology (Question 9.2 positive for the lacunary ideal), then condition (N) holds with `γ = τ_ξ`: a group topology `γ` with `τ_B ⊊ γ ⊆ τ_E` and Bohr trace on every member of `I_S`. |

## A finiteness lemma for the sets `E_r` (`PVGDiffFinite`, 12 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGDiffFiniteAxioms.lean`. Formalizes Lemma AS1 of the research note (Lemma 8.74 of PVG_v32): with `s_n = 2^(n^2)`, `S = {0} ∪ {±s_n}` and `E_r = {r (s_n - s_l) : n > l ≥ 1}`.

| Declaration | Statement |
|---|---|
| `Er_pairs_finite` | If neither `r` nor `-r` is a signed subset sum of the coefficients `l` (`Cset l`), only finitely many pairs `(n, l')`, `1 ≤ l' < n`, satisfy `r (s_n - s_l') ∈ [-m, m] + sumSet l`. (Largest-index argument with `lower_bound`.) |
| `Er_inter_finite_of_sub` | `J ∩ E_r` is finite for every `J ⊆ [-m, m] + sumSet l` under the same hypothesis. |
| `Er_inter_finite_of_subgroup` | The same for coefficients in an additive subgroup `A` of `ℝ` with `r ∉ A` (the statement of the lemma). |
| `Er_inter_IS_finite` | The same for members of the lacunary ideal `IS` whose coefficient list avoids `±r`. |

## The topological modification of the lacunary PVG is not a group topology (`PVGNotGroupArith`, `PVGNotGroupShift`, `PVGNotGroupClosure`, `PVGNotGroup`, 12 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGNotGroupAxioms.lean`. Formalizes Lemma 8.78 and Theorem 8.79 of PVG_v34 (research note, Addendum BU). With `s_n = 2^(n^2)` (`sS`), `c_i = 3^i` (`cc`), `M_i = 3i + 4` (`MM`), `E_i = {s_{n-k} - s_{m-l} + c_i (s_n - s_m) : 1 ≤ k, l ≤ i, k ≠ l, M_i ≤ n < m}` (`Ei`) and `E = ⋃_{i ≥ 2} E_i` (`Eall`).

| Declaration | Statement |
|---|---|
| `Ei_ne_zero`, `zero_notMem_Eall` | `0 ∉ E_i`, `0 ∉ E` (Lemma 8.78(a)). |
| `Ei_not_mem_piece` | For every piece `[-m₀, m₀] + sumSet l` there is `i₀` with no element of `E_i`, `i ≥ i₀`, in it (Lemma 8.78(b); largest-index argument with `lower_bound`). |
| `shiftU_free`, `shiftU_ne`, `shiftU_inj` | The shift `n ↦ n - d` of a free ultrafilter on `ℕ` is free, does not fix it (`d ≥ 1`), and `shiftU k Z ≠ shiftU l Z` for `k ≠ l`. |
| `indep4` | Independence (`PVGIndependence`) for four limits `a • L A + b • L B + c • L C + d • L D = e r` with possibly coinciding ultrafilters: the merged coefficients vanish. |
| `closure_Ei` | The Bohr closure of `E_i` is `E_i` (`i ≥ 2`; Lemma 8.78(c); ultrafilters on the index set, cases `Z₂` principal, `Z₁` principal, `Z₁` free). |
| `Eall_compl_open` | `ℝ \ E` is `τ_ξ = modTop lacConv`-open (Lemma 8.78(d)). |
| `modTop_not_continuousAdd`, `modTop_not_topAddGroup` | **Theorem 8.79**: addition is not continuous at `(0,0)` for `τ_ξ`, so `τ_ξ` is not a group topology; hence the negative answer to Question 9.2 of PVG_v33. (Iterated choice of `n` and then `m` along a free ultrafilter `W₀` replaces the Fubini square; compactness of `K` gives `k ≠ l` with `L(W₀-k) - L(W₀-l)` in a given neighbourhood of `0`.) |

## The modification of `ξ_A` is not a group topology for infinite `A`; a topology with the Bohr trace lies inside `τ_ξ` (`PVGNotGroupPos`, `PVGNotGroupAClosure`, `PVGNotGroupA`, `PVGGammaInXi`, 12 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGNotGroupAxioms2.lean`. Formalizes Theorem 8.81 and Proposition 8.83 of PVG_v35 (research note, Addenda BV and BW2).

| Declaration | Statement |
|---|---|
| `pos_ne_zero`, `pos_not_mem_piece` | For four positions `p₁, p₂, p₃, p₄` with `p₁, p₂, p₃ < p₄`, `p₁ ≠ p₃`, `M_i ≤ p₃`: `s_{p₁} - s_{p₂} + c_i (s_{p₃} - s_{p₄}) ≠ 0`, and for `i` large it lies in no fixed piece `[-m₀, m₀] + sumSet l` (the four-position form of Lemma 8.78(a), (b)). |
| `yA_ratio`, `indep4y`, `closure_EiA` | For the subsequence `y_j = s_{φ j}` (`φ` strictly increasing): `y_{j+1}/y_j → ∞`; independence for four limits with possibly coinciding ultrafilters for an arbitrary sequence `y`; the Bohr closure of `EiA φ i` is itself. |
| `EallA_compl_open` | `ℝ \ E^A` is `modTop (subConv A)`-open. |
| `modTop_subConv_not_continuousAdd`, `modTop_subConv_not_topAddGroup` | For every infinite `A ⊆ ℕ`, addition is not continuous at `(0,0)` for `τ_{ξ_A} = modTop (subConv A)`; it is not a group topology. (`φ = Nat.nth (· ∈ A)`.) |
| `topology_le_modTop`, `topology_le_modTop_lac` | A topology `γ` inducing the Bohr topology on every member of an ideal `I` is contained in `modTop (xiConv I)`; the case `I = I_S` (condition (N): `γ ⊆ τ_ξ`). |

## The core of Part II of PVG_v43: Lemma 8.90, Propositions 8.91 and 8.92, the category form of Step 6, and Steps 2 to 6 of Proposition 8.88 and the proof of Proposition 8.97 conditional on Step 1 (`PVGProdLimit`, `PVGTotBdd`, `PVGDenseTrace`, `PVGBaireDigits`, `PVGNoLqcCore`, `PVGCyclicCore`, 13 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGPartIIAxioms.lean`. Numbers refer to PVG_v43 (research note, Addenda CE, CF, CH, CI, CJ). **Not formalized:** Step 1 of Proposition 8.88 (a locally quasi-convex `γ` between `τ_B` and `τ_E` gives a bounded infinite `γ`-equicontinuous set of characters; here it is the hypothesis `hV`, `hcE`, `hC`, `hinj`), the Lebesgue-null part of Step 6 (only the category form is proved), Proposition 8.94 (uses Glicksberg's theorem), Proposition 8.96, Theorem 8.86. **Note:** the hypothesis `0 ∈ D` of `denseTrace` is missing in the statement of Proposition 8.92 in PVG_v43 and is needed.

| Declaration | Statement |
|---|---|
| `prodLimit_K`, `prodLimit_bohr`, `prodLimit_lt`, `prodLimit` | **Lemma 8.90**: for real `a` and a free ultrafilter `U`, for `U`-most `n` and `U`-most `m`, `e(a s_n - a s_m)` lies in a given neighbourhood of `0` in `K` (in `bohrTop` for the real points), and `n < m`. |
| `Ja`, `Hyp`, `hyp_of_trace` | `J_a = aS + (-a)S`; if a topology `γ` induces the Bohr topology on `J_b`, then for every free `U` and `γ`-neighbourhood `W` of `0`, `U`-most `n`, `U`-most `m`: `n < m` and `b s_n - b s_m ∈ W`. |
| `totbdd_seq`, `totbdd` | **Proposition 8.91**: if `γ` induces the Bohr topology on `J_a`, every `γ`-neighbourhood `W` of `0` has a finite `F` with `a s ∈ F + W` for all `s ∈ S` (no group structure on `γ` is used). |
| `denseTrace_core`, `denseTrace` | **Proposition 8.92** (with `0 ∈ D`): a group topology coarser than the Euclidean topology whose trace on a Euclidean-dense `D ∋ 0` is coarser than the Bohr trace is coarser than the Bohr topology (`bohrTop ≤ γ`). |
| `isClosed_FdigDil`, `interior_FdigDil`, `baire_digits`, `exists_not_mem_digits` | Step 6 of Proposition 8.88, category form: `F = {y : ‖2^{n²} y‖ ≤ 1/4 for all n ≥ 1}`; `δ⁻¹F` is closed with empty interior for `δ ≠ 0`; for any sequence `δ_K ≠ 0` the set of `a` with `δ_K a ∉ F` for all `K` is dense. |
| `step5`, `digit_of_trace`, `nolqc_core` | Steps 2 to 6 of **Proposition 8.88**, conditional on Step 1: if `γ` induces the Bohr topology on `J_a`, then `(c_{K+1} - c_K) a ∈ F` for some `K`; arbitrarily close to every real number there is an `a` for which `γ` does not induce the Bohr topology on `J_a`. |
| `bohr_precompact`, `int_of_dint`, `cyclic_core` | **Proposition 8.97**, conditional on Step 1: every subset of `ℝ` is totally bounded for the Bohr topology (compactness of `K`); `‖nθ‖ < 1/4` for all integers `n` implies `θ ∈ ℤ`; if `γ` induces the Bohr topology on the cyclic subgroup `xℤ`, then `(c_{K+1} - c_K) x ∈ ℤ` for some `K`. |

## A necessary condition on every witness of (N), the pseudo-norm criterion, and atoms that sum to an interval (`PVGNecessaryE`, `PVGNormCriterion`, `PVGAtomsInterval`, 16 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGPartIIIAxioms.lean`. Numbers refer to PVG_v47 (research note). **Not formalized:** the direction "(N) ⟹ criterion" of the pseudo-norm criterion (Birkhoff–Kakutani construction of an invariant pseudometric), and the statements about the failure of three natural assignment strategies. Condition (N) itself remains open.

| Declaration | Statement |
|---|---|
| `TraceNhd`, `traceNhd_of_induced_eq` | `TraceNhd γ J`: every `γ`-neighbourhood of `0` contains `{z ∈ J : e z ∈ Y}` for an open `Y ∋ e 0` of `K`; it holds if `γ` and the Bohr topology induce the same topology on `J ∋ 0`. |
| `exists_Eall_mem_nhds`, `condN_nhds_meets_Eall` | For an arbitrary group topology `γ` on `ℝ` with `TraceNhd` on `J_1 = S - S` and on `J_{c_i}`, `i ≥ 2`, every `γ`-neighbourhood of `0` meets `E = ⋃ E_i` (`Eall`); in particular for every group topology with the Bohr trace on every member of `I_S`. Same proof as `modTop_not_continuousAdd`, with a `γ`-neighbourhood `V` with `V + V ⊆ W`. |
| `ConditionN`, `phiBasis`, `phiTop`, `phiTop_isTopologicalAddGroup`, `mem_nhds_phiTop`, `N_of_norm` | Statement of condition (N); for symmetric subadditive `Φ : ℝ → ℝ` with `Φ 0 = 0` the sets `{Φ < ε}` form an `AddGroupFilterBasis`; if `Φ` satisfies (a) `Φ → 0` Euclidean-ly, (b) `Φ → 0` along Bohr-null nets in every member of `I_S`, (c) `Φ ≥ θ` somewhere in every Bohr neighbourhood of `0`, then (N) holds with `γ = τ_B ⊓ τ_Φ`. Nonnegativity of `Φ` is not needed. |
| `Jtil`, `Jtil_mem_IS`, `Atoms`, `atoms_add_contains_interval` | `J_a = [-1,1] + aS - aS ∈ I_S`; for every assignment `a ↦ B_a` of Bohr neighbourhoods of `0`, the set of atoms `⋃_a (J_a ∩ B_a)` has `Atoms + Atoms` containing a nonempty Euclidean open set (`prodLimit` and Baire). |

## The Bohr trace on one cyclic subgroup, and open sets of the modification (`PVGCyclicTrace`, `PVGTauTwoSided`, 25 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom reports in `PVGCyclicTraceAxioms.lean` and `PVGTauTwoSidedAxioms.lean`.

The cyclic-subgroup statement replaces the earlier conditional core `cyclic_core` (`PVGCyclicCore`): local quasi-convexity is not needed. "`γ` is coarser than the Euclidean topology" is stated as: every `γ`-neighbourhood of `0` contains an interval around `0`. The statement about ideals that contain some `aℤ`, and the statement that no proper interval is open, follow at once and are not formalized.

| Declaration | Statement |
|---|---|
| `cyclicTrace_le` | A group topology `γ` coarser than the Euclidean topology whose trace on `aℤ`, `a ≠ 0`, is coarser than the Bohr trace is coarser than the Bohr topology (`bohrTop ≤ γ`). |
| `cyclicTrace_eq`, `cyclicTrace_zero` | If moreover `γ` is finer than the Bohr topology and induces the Bohr topology on `aℤ`, `a ≠ 0`, then `γ = bohrTop`; for `γ ≠ bohrTop` only `a = 0` has the Bohr trace. |
| `tau_unbounded_side`, `tau_unbounded_above`, `tau_unbounded_below` | Every nonempty open set of the topological modification of the lacunary PVG is unbounded above and below. |

## The two Bohr topologies on the interval-free pieces, and compact thickening (`PVGFinitePiece`, 25 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGFinitePieceAxioms.lean`.

`τ_D` (`discTop`) is generated by all algebraic characters of `ℝ`, `τ_B` (`bohrTop`) by the Euclidean continuous ones; `I₀` (`I0`) consists of the subsets of the sets `F + a₁S + … + a_kS` with `F` finite. The two topologies are different on `ℝ` and even on finite-rank subgroups, but agree on every member of `I₀`. `intervalFree_witness` proves the existence statement of the theorem on condition (N) without intervals with the witness `τ_D`; the box construction of the article is not formalized.

| Declaration | Statement |
|---|---|
| `piece_limits`, `finitePiece_char` | Limits along ultrafilters on sums of dilates of `S`; on `F + a₁S + … + a_kS` every algebraic character is continuous for the trace of `τ_B` (uses `independence_finset`). |
| `finitePiece_trace`, `discTop_ne_bohr`, `intervalFree_witness` | `τ_D` and `τ_B` induce the same topology on every member of `I₀`; `τ_D ≠ τ_B`; hence a group topology strictly finer than `τ_B` has the Bohr trace on every member of `I₀`. |
| `thickening` | For a group topology `γ` finer than `τ_B`: the Bohr trace on every member of the lacunary ideal holds iff `γ` is coarser than the Euclidean topology and has the Bohr trace on every member of `I₀`. |

## The interval-free modification is not a group topology (`PVGIntervalFree`, 25 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGIntervalFreeAxioms.lean`. The box topology of the article is not formalized; the strict inclusions are checked with `τ_D` in its place.

| Declaration | Statement |
|---|---|
| `I0_isIdeal`, `Jc_mem_I0` | `I₀` is an admissible ideal and contains the sets `c (S - S)` used in the argument. |
| `Eall_compl_open0`, `modTop0_not_continuousAdd` | `ℝ \ E` is open in the topological modification `τ₀` of `ξ_{τ_B, I₀}`; addition is not continuous for `τ₀`. |
| `intervalFree_strict` | `τ_B ⊂ τ_D ⊂ τ₀`, both strictly. |

## Locally quasi-convex topologies for countably many coefficients (`PVGTwoCountable`, `PVGTwoDimension`, 25 November 2026)

These modules concern a working article that continues the PVG article (its Section 4). No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGTwoAxioms.lean`.

`γ_δ` (`gamTop δ`) is the Bohr topology together with uniform convergence on the characters `x ↦ δ_k x mod 1`; `A(δ)` (`InA δ t`, `Agroup`) is the set of `a` with `sup_n ‖a δ_k t_n‖ → 0`.

| Declaration | Statement |
|---|---|
| `gam_group`, `gam_le_bohr`, `gam_coarser_euclid`, `gam_lqc` | `γ_δ` is a locally quasi-convex group topology between the Bohr and the Euclidean topology (`δ` bounded). |
| `gam_not_precompact`, `gam_ne_bohr` | If `δ` takes infinitely many values, `γ_δ` is not precompact, hence not the Bohr topology. |
| `trace_eq`, `inA_of_trace` | `γ_δ` induces the Bohr topology on subsets of `[-m, m] + a_1 T + … + a_r T` with `a_i ∈ A(δ)`; the Bohr trace near `0` on `[-1,1] + aT + (-a)T` forces `a ∈ A(δ)`. |
| `inA_of_step1` | The necessity of the criterion, conditional on Step 1 of the proof of Proposition 16.1 of the PVG article (a hypothesis, not proved here). |
| `syndetic`, `small`, `exists_seq`, `countable_witness` | For `|t_{n+1}/t_n| → ∞` and every countable set of coefficients there is such a topology, different from the Bohr topology. |
| `dimH_Agroup`, `dyadic_mem`, `dimension_witness` | For `t_n = 2^(n²)` and `δ_k = 2^{-(4^k+k)}`: `A(δ)` has Hausdorff dimension `1`, contains the dyadic rationals, and `γ_δ` has the properties above. |
| `dilates_totally_bounded` | `aS` is `γ_δ`-totally bounded for `a ∈ A(δ)`. |

Not formalized: that `A(δ)` is a null set (it rests on Proposition 16.1 of the PVG article).

## No witness of condition (N) (`PVGTwoNoWitness`, 25 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGTwoNoWitnessAxioms.lean`.

| Declaration | Statement |
|---|---|
| `null_cover`, `group_null_cover` | If a group topology on `ℝ` is coarser than the usual one and not precompact, and `T` is unbounded, then `{a : aT is totally bounded}` lies in a countable union of closed Lebesgue-null sets. |
| `tb_of_dilates`, `group_tb_of_dilates` | If `aT` is totally bounded for every `a`, the group is precompact. |
| `trace_null` | For a non-precompact such topology, the `a` for which it induces the Bohr topology on `J_a` lie in such a null set. |
| `no_witness` | A group topology coarser than the usual one that induces the Bohr topology on every `J_a` is precompact. |
| `Agroup_null` | The group `A(δ)` of the dimension theorem lies in such a null set. |

Not formalized: that a precompact group topology is the initial topology of its continuous characters (Comfort and Ross), which turns `no_witness` into the statement that condition (N) fails.

## An averaged topology (`PVGTwoAverage`, 25 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGTwoAverageAxioms.lean`.
`avTop` is the Bohr topology of `ℝ` together with the pseudonorm `sup_N N⁻¹ ∑_{p ≤ N} ‖x / 2^p‖`; `InL a` says that
`sup_n Φ_N(a s_n) → 0`, where `Φ_N` is the `N`-th average.

| Declaration | Statement |
|---|---|
| `av_group`, `av_le_bohr`, `av_coarser_euclid`, `av_not_precompact`, `av_ne_bohr` | `avTop` is a group topology strictly between the Bohr and the Euclidean topology, and it is not precompact. |
| `av_trace`, `inL_zero`, `inL_neg`, `inL_add` | It induces the Bohr topology on subsets of `[-m, m] + a_1 S + … + a_r S` with `a_i` in the group `Λ`. |
| `inL_of_digits` | A number whose binary digits have uniform density zero lies in `Λ`. |
| `exists_not_inA` | For every sequence `δ_k ≠ 0`, `δ_k → 0`, some `a ∈ Λ` is not in `A(δ)`. |
| `av_no_step1_witness` | Hence the Bohr trace fails somewhere on `Λ` for a locally quasi-convex topology, conditional on Step 1 of the proof of Proposition 16.1 of the PVG article (a hypothesis, not proved here). |

Not formalized: Step 1, and the statement that every locally quasi-convex group topology coarser than `avTop` is coarser than the Bohr topology.

## Which sets of coefficients can be served (`PVGTwoServed`, 26 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGTwoServedAxioms.lean`. Typechecked module by module with Lean 4.35.0; no full `lake build`.

- `trace_of_tb`, `served_of_tb`: for a group topology between the Bohr and the usual one, total boundedness of the dilates of the lacunary set gives the Bohr trace on the corresponding members of the ideal.
- `av_tb_iff`: for the averaged topology the totally bounded dilates are exactly those with coefficient in the group of Section 6.
- `ae_volume_pos`: a projection estimate: for a probability measure with `μ(ball r) ≤ M r^s`, `1/2 < s < 1`, carried by a compact `K`, the set `K + lam K` has positive measure for almost every `lam` in `[1,2]`.
- `ae_sum_eq_univ`: for almost every such `lam`, every real number is `a + lam b` with `a, b` in the group of the dimension theorem.
- `exists_two_unservable`: two such groups that no non-precompact group topology below the usual one serves together.

Not formalized: the reduction to topologies with a countable base, and the theorem of Comfort and Ross.

## A servable set and one point (`PVGTwoPoint`, 26 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGTwoPointAxioms.lean`. Typechecked module by module with Lean 4.35.0; no full `lake build`.

- `inA_of_Cdig`, `Yset_rep`: for a sparse sequence `delta`, a compact set of coefficients in `A(delta)` whose dilates of the lacunary set contain every sum of powers of two that avoids the windows.
- `Yset_tb`: total boundedness of these dilates forces total boundedness of the set of those sums.
- `near_Yset`, `exists_cover`: every real is a point `c s_n`, plus a difference of two such sums, plus a bounded term.
- `exists_point_unservable`: there is `c` such that no non-precompact group topology below the usual one makes `aS`, `a` in `A(delta)`, and `cS` totally bounded, although `A(delta)` alone has such a topology.

Not formalized: the statement for generic `c`.

## Rigidity and an unservable increasing union (`PVGTwoUnion`, 26 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGTwoUnionAxioms.lean`. Typechecked module by module with Lean 4.35.0; no full `lake build`.

- `rigidity`: if all dilates `aS`, `a` in `A(delta)`, are totally bounded in a group topology below the usual one, then each neighbourhood of 0 covers, with finitely many translates, a set `{x | ‖x δ_k‖ ≤ ε for all k}`.
- `union_core`, `exists_union_unservable`: if also the dilates for `a / 2^m` are totally bounded for arbitrarily large `m`, the topology is precompact; every group topology coarser than all `γ_(2^m δ)` is precompact.

Not formalized: the statement about maximal sets.

## A Fréchet–Urysohn pseudotopological vector group (`PVGTwoFU`, 26 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGTwoFUAxioms.lean`. Typechecked module by module with Lean 4.35.0; no full `lake build`.

An ultrafilter converges to `x` if for one finite tuple `a` it contains, for every `N`, the points `x + u + sum a_i σ_i` with `|u| < 1/(N+1)` and `σ_i` zero or `±2^((n+1)^2)`, `n ≥ N`; a filter converges if all finer ultrafilters do.

- `tconv_pure`, `tconv_mono`, `tconv_of_ultra`, `tconv_add`, `tconv_mul`: a pseudotopology with continuous addition and dilations.
- `tconv_nhds`, `tconv_sT`, `tconv_unique`: coarser than the usual convergence, an unbounded convergent sequence, Hausdorff.
- `tconv_frechet`, `tconv_not_pretopological`: Fréchet–Urysohn and not pretopological.
- `xi_iff`: on ultrafilters, the lacunary convergence is this one together with the Bohr topology.

## Bounded signed sums (`PVGTwoBounded`, 26 November 2026)

No `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only. Typechecked as a single module; no full `lake build`.

- `bounded_sum`: for a positive sequence with `s (n+1) / s n` tending to infinity, a bounded signed sum with finitely many fixed coefficients has vanishing combined coefficients at all large indices.

## Almost every added point (`PVGTwoAlmost`, 26 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGTwoAlmostAxioms.lean`. Typechecked module by module with Lean 4.35.0; no full `lake build`.

Lebesgue measure on `[0,1)`, sparse sequence of `PVGTwoPoint`.

- `bad_volume`: the numbers whose binary blocks never show a given pattern of level `K` have small measure.
- `ae_all_patterns`: for almost every `c` and all large `K` every pattern of level `K` occurs.
- `ae_cover`, `ae_point_unservable`: for almost every `c`, a group topology below the usual one that makes all `aS`, `a` in `A(delta)`, and `cS` totally bounded is precompact.

Not formalized: the statement about a comeagre set.

## The statements left out before (`PVGTwoClassical`, `PVGTwoRest`, `PVGTwoComeagre`, 26 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; axiom report in `PVGTwoRestAxioms.lean`. Typechecked module by module with Lean 4.35.0; no full `lake build`.

- `below_bohr`: a precompact group topology contained in the usual one is contained in the Bohr topology (from the Peter-Weyl theorem in `ChainPW7`); `bohr_of_dilates`, `not_precompact_between`, `trace_null_between`, `no_dilated_convergence`.
- `step1`, `criterion`, `not_lqc_Lambda`, `lqc_below_av`, `av_not_lqc`, `Lambda_uncountable`: locally quasi-convex topologies and the averaged topology.
- `serves_dil`, `servable_group`, `servable_countable`, `countable_base_iff`, `countable_base_Hg`: which sets can be served; a countable base is enough.
- `not_servable_two`, `not_servable_point`, `not_servable_union`, `maximal_servable`, `union_finest`, `two_finest`.
- `cover_of_patterns`, `residual_patterns`, `comeagre_point`: a comeagre set of added points.

## Section 8 for a general sequence (`PVGTwoFUGen`, 26 November 2026)

No `sorry`, same three axioms; report in `PVGTwoFUGenAxioms.lean`.

- The statements of `PVGTwoFU` for every sequence of nonzero reals with `|s (n+1)| / |s n|` tending to infinity.

## Three further statements (`PVGTwoRestTwo`, 26 November 2026)

No `sorry`, same three axioms; report in `PVGTwoRestTwoAxioms.lean`.

- `xi_finest`: a group topology in which every lacunary convergent filter converges is contained in the Bohr topology.
- `trace_forces_usual`: the Bohr trace on one set `J_a` puts a group topology below the usual one.
- `no_rigidity`: a sequence with `A(delta) = {0}` for which the rigidity conclusion fails.

## The finest topology that serves a set (`PVGTwoFinest`, 26 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; report in `PVGTwoFinestAxioms.lean`.

- `parity_serves`: for `delta_k -> 0`, `|delta_k| <= 1`, adding the condition that `sum_k round(delta_k x) theta_k -> 0` modulo 1 gives a group topology finer than `gamma_delta` in which all `aS`, `a` in `A(delta)`, are totally bounded.
- `odd_points`, `parity_strict`: for the sparse sequence and `theta_k = 1/2` it is strictly finer.
- `finest_lqc`: for the sparse sequence, `gamma_delta` is the finest locally quasi-convex topology with this property.
- `exists_finest`, `finest_not_lqc`: every servable set has a finest serving topology; here it is not locally quasi-convex.

## The finest serving topology described (`PVGTwoStab`, `PVGTwoDescribe`, `PVGTwoMany`, 26 November 2026)

No `sorry`, no `native_decide`, axioms `propext`, `Classical.choice`, `Quot.sound` only; report in `PVGTwoDescribeAxioms.lean`. The Kalton-Roberts theorem (`Stab.KaltonRoberts`) is NOT proved here: it is a hypothesis of the statements that use it.

- `Stab.inf_box`: nearly additive circle-valued functions on boxes of integer points are nearly characters (using Kalton-Roberts).
- `Two.finest_described`: using it, the finest group topology serving `A(delta)` is generated by all the parity topologies.
- `Two.odd_points_gen`: the singleton parity lemma for every sequence of natural exponents with gaps tending to infinity.
- `Two.many_embed`, `Two.many_card`: exactly `2 ^ continuum` serving topologies lie below `gamma_delta` in Mathlib order.

## The Kalton-Roberts assumption in its classical form (`PVGTwoKR`, 27 November 2026)

No `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only.

- `kaltonRoberts_of_classical`: the assumption `Stab.KaltonRoberts` follows from Theorem 4.1 of Kalton and Roberts as stated, for set functions vanishing on the empty set. That theorem itself is not formalized.
- `finest_described_classical`: the description of the finest serving topology under the classical statement.

## Correction and completion for the parity topologies (`PVGTwoDescribe`, `PVGTwoCor`, 27 November 2026)

In `PVGTwoDescribe` as first published (ffb6427, 1f306c2), `parTop theta` was an unspecified choice among the topologies given by `parity_serves`. The checked statement `finest_described` therefore did not say that the parity topologies `gamma_(delta,theta)` generate the finest serving topology. `parTop` is now defined explicitly, and the same proofs check. No `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only.

- `parTop_spec`, `parTop_hasBasis`: properties and base of `gamma_(delta,theta)` for the sparse sequence.
- `finest_described`, `finest_described_classical`: now about these topologies.
- `gamAll_hasBasis`: the base of the finest serving topology.
- `allserving`: the topologies that serve `A(delta)`.

## The description fails for some sequences (`PVGTwoNoDescribe`, 27 November 2026)

No `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only.

- `unbounded_nhds`: for the sequence `dz` (`A(delta) = {0}`) every neighbourhood of 0 in the topology generated by all `gamma_(delta,theta)` is unbounded.
- `no_description`: the usual topology is the finest one serving `A(delta)`, and it is not generated by these topologies.

## Rigid sequences and the finest serving topology (`PVGThreeRigid`, `PVGThreeDescribe`, `PVGThreeDyadic`, 27 November 2026)

No `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only. The theorem of Kalton and Roberts is a hypothesis.

- `rig_of_finest`: if the parity topologies generate a topology finer than all serving ones, the sequence is rigid.
- `gamAll_le`, `finest_of_rig`, `rig_iff`: for `delta_k = 2^(-L_k)` with increasing `L_k`, rigidity is equivalent to that description.
- `finest_lqc` (namespace `PVG.Three`): under rigidity `gamma_delta` is the finest locally quasi-convex serving topology.
- `rig_of_bounded`: bounded gaps give rigidity. `not_rig`: unbounded gaps and dyadic `A(delta)` give no rigidity.
- `PVGThreeDescribe` is generated from `PVGTwoDescribe` with the sequence made a parameter.

## Completion of the rigidity section (`PVGThreeServing`, `PVGThreeBounded`, `PVGThreeSquares`, `PVGThreeGeneral`, 27 November 2026)

Written by ChatGPT; typechecked by Claude with small repairs in `PVGThreeBounded` and `PVGThreeSquares`. No `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only (`PVGThreeCompletionAxioms`).

- `allserving_of_rig`: the topologies that serve `A(delta)` for rigid dyadic `delta` (Kalton-Roberts assumed).
- `gam_eq_euclid_of_bounded`, `A_eq_singleton_zero_of_bounded`: bounded gaps.
- `not_rig_of_square_shift`: `L_k + j` a square infinitely often and unbounded gaps give no rigidity.
- `rig_of_finest_of_infinite_nonzero`: the description implies rigidity for every null sequence with infinitely many nonzero terms.

## Countably many coefficients (`PVGThreeCountable`, 27 November 2026)

No `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only. No Kalton-Roberts assumption.

- `tune`: a frequency near `1/(2x)` that is almost invisible on the dilates, for `x` far from the lacunary set.
- `not_rig_of_countable`: countably many coefficients and far points in `U(eps)` give no rigidity.
- `rig_iff_bounded_of_countable`: for dyadic sequences with countably many coefficients, rigidity means bounded gaps.

## Sufficient condition and classification (`PVGThreeSufficient`, `PVGThreeClassify`, 27 November 2026)

No `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only. No Kalton-Roberts assumption.
`delta_k = 2^(-L_k)`, `L` strictly increasing with `2 <= L 0`.

- `rig_of_avoids_seq`: if there are widths `w_k -> infinity` such that for every `p0` there are arbitrarily large `n`
  with no `m^2 - n^2 + p` (`m > n`, `p < p0`) in any `[L_k - w_k, L_k)`, then `delta` is rigid.
- `rig_of_far_windows`: the case of infinitely many large jumps.
- `card_divisors_pow_le`: `d(n)^K <= C n` (not found in Mathlib).
- `rig_iff_of_sparse`, `rig_iff_uncountable_of_sparse`: if `k^5 <= C L_k` and `L_k <= c^2 + c` with `c = sqrt L_k`,
  then rigidity, `L_k - c^2 -> infinity`, and uncountability of `A(delta)` are equivalent.
- `rig_four_pow`: `L_k = 4^k + k` gives a rigid sequence.

## Classification by the next square (`PVGThreeUpperGap`, 27 November 2026)

No `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only. Theorem and proof due to ChatGPT.
`c = sqrt L_k`, `D_k = (c+1)^2 - L_k`, hypothesis `k^(2s+1) <= C D_k^s` with `s >= 1`, and `2 <= L 0`.

- `card_sqdiff_large`: for `M > U^4` at most one `n <= U` has `n^2 + M` a square larger than `n^2`.
- `rig_iff_of_upper_gap`, `rig_iff_uncountable_of_upper_gap`: rigidity, `L_k - c^2 -> infinity` and
  uncountability of `A(delta)` are equivalent. This strengthens `rig_iff_of_sparse`.
