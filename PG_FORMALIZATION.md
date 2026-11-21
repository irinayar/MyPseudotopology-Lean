# PG: Lean checks for pseudotopological groups built from a topology and an ideal (21 November 2026)

Modules: `LeanCheck/PGNullFilters.lean`, `PGXi.lean`, `PGDigit.lean`, `PGBlock.lean`, `PGLimit.lean`, `PGSub.lean`, `PGCompactify.lean`, `PGSUnit.lean`, and the axiom report `PGAxioms.lean`. Typechecked with Lean 4.35.0 and Mathlib (the `lean-toolchain` of this repository), one module at a time; no `sorry`; every declaration depends only on `propext`, `Classical.choice` and `Quot.sound` (see `PGAxioms.lean`). A Lean proof verifies its formal statement under its hypotheses; the correspondence with the statements of the PG article series (versions 1 to 5, unpublished) was checked by the author and has not been reviewed independently.

Setting: `G` an abelian group; filters are Mathlib filters, "finer" is `≤`, proper means `NeBot`; `F - x` is `Filter.map (· - x) F`, `F + H` is `Filter.map₂ (· + ·) F H`.

## `PGNullFilters` (a pseudotopological group is determined by its null filters)
| Declaration | Statement |
|---|---|
| `NullFamily C` | Properties (i)-(iv) of a family `C` of filters: proper, `pure 0 ∈ C`, closed under finer proper filters, sums, negatives, and ultrafilter saturation. |
| `conv_pure`, `conv_mono`, `conv_ultra` | `F → x :⇔ F - x ∈ C` satisfies the pseudotopology axioms (P1)-(P3). |
| `conv_add`, `conv_neg` | `F → x`, `H → y` imply `F + H → x + y`, and `F → x` implies `-F → -x`. |
| `conv_zero`, `hausdorff_iff` | The filters converging to `0` are exactly `C`; the convergence is Hausdorff iff no `F`, `z ≠ 0` have `F ∈ C`, `F - z ∈ C`. |
| `IsPGConv`, `nullFamily_of_conv`, `conv_iff_of_conv`, `conv_eq_of_conv` | Conversely, for any convergence relation with (P1)-(P3) and continuous addition and negation the filters converging to `0` form a null family, `F → x ↔ F - x → 0`, and the relation is the one defined by that family. |

## `PGXi` (the PG of a group topology and an ideal)
| Declaration | Statement |
|---|---|
| `AdmIdeal I` | (I1)-(I5): subsets and finite unions, singletons, `univ ∉ I`, sums `A + B`, negatives. |
| `xi I F x` | `F` proper, `F ≤ 𝓝 x` and `F` has a member in `I`. |
| `isPGConv_xi`, `xi_hausdorff` | For a Hausdorff group topology and `AdmIdeal I`, `xi I` is a Hausdorff pseudotopological group convergence. |
| `Vxi`, `Vxi_eq_map`, `pretopological_iff` | `V_ξ(x) = x + V_ξ(0)`; `ξ` is pretopological iff `V_ξ(0) → 0`. |
| `pretopological_zero_iff` | `V_ξ(0) → 0` iff there is `A ∈ I` with `0 ∉ closure (B \ A)` for every `B ∈ I`. |
| `not_pretopological_of_recipe` | If for every `A ∈ I` there is `D ∈ I` disjoint from `A` with `0 ∈ closure D`, then `ξ` is not pretopological. |
| `isOpenXi_iff`, `isOpen_isOpenXi` | `U` is open in the topological modification of `ξ` iff `closure (B \ U) ∩ U = ∅` for all `B ∈ I`; every open set is open in the modification. |

## `PGDigit` (digit sets of the integers)
| Declaration | Statement |
|---|---|
| `D p k` | Integers that are sums of at most `k` signed powers `±p^z` (`val p l` for lists of terms). |
| `zero_mem_D`, `D_mono`, `D_neg`, `D_add`, `mem_D_abs` | `0 ∈ D_k`, monotone, symmetric, `D_k + D_l ⊆ D_{k+l}`, every integer lies in some `D_k`. |
| `Ip p`, `Ip_sub`, `Ip_union`, `Ip_single`, `Ip_add`, `Ip_neg` | The ideal of subsets contained in some `D_k` satisfies (I1), (I2), (I4), (I5). |
| `Ip_admissible` | `AdmIdeal (Ip p)` **assuming** `univ ∉ Ip p` as a hypothesis: the counting bound `#(D_k ∩ [-X,X]) ≤ K (1+log X)^k` that gives this is not formalized. |
| `Ip_pow` | `I_{p^r} = I_p` for `p ≥ 1`, `r ≥ 1`. |

## `PGBlock` (gap splitting of relations among signed powers)
| Declaration | Statement |
|---|---|
| `abs_val_le`, `dvd_val` | If all exponents are `≤ e`: `|val| ≤ length · p^e`; if all are `≥ q`: `p^q ∣ val`. |
| `gap_split` | If `val low + val high = 0`, exponents of `low` are `≤ q - L - 1`, those of `high` are `≥ q`, and `#low < p^{L+1}`, then both sums are `0`. |
| `split_zero` | A relation `val l = 0` with `#l < p^{L+1}` and no exponent in `[q - L, q - 1]` splits into the terms below `q` and at least `q`, each with sum `0`. |

Not formalized: the iteration into maximal blocks and the counting of terms in blocks (used in the weight lemma for alternating sums and in the closure lemma for `D_k` modulo powers of `p`).

## `PGLimit` (the modification as an inductive limit)
| Declaration | Statement |
|---|---|
| `isOpenXi_iff_closed_traces` | For closed sets `D k ∈ I` such that every member of `I` lies in some `D k`: `U` is open in the modification iff every `D k \ U` is closed. |
| `thin_set_closed` | If `C ∩ D k` is finite for every `k`, every subset of `C` is closed in the modification. |
| `isOpenXi_preimage_homeo`, `isOpenXi_translate`, `isOpenXi_neg` | Preimages of open sets of the modification under translations and negation (homeomorphisms preserving `I`) are open. |

Not formalized (hand proofs only): the counting lemma for `D_{p,k}`, the Bohr topology of `ℤ` and the Bohr-sequence proposition, the weight lemma, the closedness of `D_{p,k}` in the Bohr topology, the pigeonhole lemma on Bohr neighbourhoods, and the strictness construction.

## `PGSub` (a second topology containing the convergence of `ξ`; abstract part of Theorem T of version 4)
Setting as in `PGLimit`; a second topology `τ'` on `G` is given only through the family `Op` of its open sets, with the hypothesis that for every `Op`-open `W` and every `k` there is a `β`-open `O` with `O ∩ D k = W ∩ D k`.
| Declaration | Statement |
|---|---|
| `xi_converges_op` | If `F → x` for `ξ`, then `W ∈ F` for every `Op`-open `W` containing `x` (`F` converges to `x` in `τ'`). |
| `isOpenXi_of_op` | Every `Op`-open set is open in the topological modification of `ξ`. |

Not formalized: that `τ'` is a group topology (direct limit of compact sets, product theorem for `k_ω`-spaces) and its construction from the compactification.

## `PGCompactify` (closures of the digit sets in a compactification)
| Declaration | Statement |
|---|---|
| `closure_image_inter_range` | For a topological embedding `e : G → K` and closed `D ⊆ G`: `closure (e '' D) ∩ range e = e '' D`. |
| `closure_add_subset`, `closure_neg_subset` | `cl A + cl B ⊆ cl (A + B)` and `-cl A ⊆ cl (-A)` in a topological additive group. |

Not formalized: the Bohr compactification, the compactness of the closures, the direct-limit group `L`, the product theorem for `k_ω`-spaces.

## `PGSUnit` (independent bases: reduction to the S-unit equation theorem; Theorem 8.1 of version 5)
Imports `PGDigit`. Terms `±p^e` and `±q^e` are triples `(isP, positive, e)`; a configuration is a multiset of terms.
| Declaration | Statement |
|---|---|
| `pow_mul_pow_inj`, `ratio_inj` | If `p, q ≥ 2` are multiplicatively independent (`p^u = q^v → u = v = 0`), then `p^a q^b = p^c q^d` gives `a = c`, `b = d`, and `p^α/q^β = p^α'/q^β'` gives `α = α'`, `β = β'`. |
| `exists_block` | A nonzero multiset of terms with sum `0` contains a minimal nonzero sub-multiset with sum `0`. |
| `tuple_of_block`, `ratio_mem_Gam`, `block_cand` | A minimal block with a `q`-term and a `p`-term yields a list `y` in `Gam p q = {±p^a q^c}` with `∑ y = 1` and no nonempty sublist with sum `0`, and `|∑ (p-terms)| = q^β · |∑ z|` for a sublist `z` of `y`, with `β` determined by one entry of `y`. |
| `SUnitFinite p q` | **Hypothesis**: for every `m` only finitely many such lists `y` of length `m` (the S-unit equation theorem). It is not proved here. |
| `Vals_finite` | Under `SUnitFinite`, the `p`-parts of mixed minimal blocks with at most `M` terms form a finite set. |
| `reach_finite` | Under `SUnitFinite`, the set of `∑ (p-terms)` of vanishing configurations with at most `a` `p`-terms and `b` `q`-terms is finite (strong induction on `a + b`). |
| `inter_finite`, `Ip_inter_finite`, `Ip_inter_eq` | Under `SUnitFinite`: `D p k ∩ D q l` is finite; `A ∈ I_p ∩ I_q ↔ A` finite. |

Not formalized: the S-unit equation theorem (a deep theorem, not in Mathlib), the properness of the ideal generated by `I_p ∪ I_q`.
