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
