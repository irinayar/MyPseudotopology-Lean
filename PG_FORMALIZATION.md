# PG: Lean checks for pseudotopological groups built from a topology and an ideal (21 November 2026)

Modules: `LeanCheck/PGNullFilters.lean`, `PGXi.lean`, `PGDigit.lean`, `PGBlock.lean`, `PGLimit.lean`, `PGSub.lean`, `PGCompactify.lean`, `PGSUnit.lean`, `PGGenerated.lean`, `PGIdem.lean`, `PGTop.lean`, `PGSumset.lean`, `PGGroupTop.lean`, `PGJoin.lean`, `PGTwoBases.lean`, and the axiom report `PGAxioms.lean`. Typechecked with Lean 4.35.0 and Mathlib (the `lean-toolchain` of this repository), one module at a time; no `sorry`; every declaration depends only on `propext`, `Classical.choice` and `Quot.sound` (see `PGAxioms.lean`). A Lean proof verifies its formal statement under its hypotheses; the correspondence with the statements of the PG article series (versions 1 to 9, unpublished) was checked by the author and has not been reviewed independently.

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

## `PGGenerated` (the PG generated by an ultrafilter; Theorem 9.1 of version 6, abstract part)
Imports `PGNullFilters`. For an ultrafilter `u` on an abelian group `G`: `GenUlt u` is the smallest family of ultrafilters containing `pure 0` and `u`, closed under negation and under "finer than a filter sum"; `genNull u` is the family of proper filters all of whose finer ultrafilters are in `GenUlt u`.
| Declaration | Statement |
|---|---|
| `exists_ultra_le_map₂` | Every ultrafilter finer than a filter sum `F + H` is finer than `U + V` for ultrafilters `U ≤ F`, `V ≤ H` (no compactness used). |
| `genNull_nullFamily`, `u_mem_genNull` | `genNull u` satisfies (i)-(iv) of Proposition 2.6 (`NullFamily`), and `u ∈ genNull u`. |
| `genNull_le` | It is the smallest null family containing `u`. |
| `mem_of_subgroup_mem`, `genNull_hausdorff`, `int_hausdorff` | A subgroup in `u` lies in every generated ultrafilter; if every `z ≠ 0` is missed by a subgroup in `u` the PG is Hausdorff; for `ℤ` this holds when `u` contains every `mℤ` (in particular for idempotent `u`). |

## `PGIdem` (levels `ε_1 u + ... + ε_n u`, and non-pretopology under a digit hypothesis)
Imports `PGGenerated`.
| Declaration | Statement |
|---|---|
| `Lev u n F` | `F` is a filter sum of `n` copies of `±u`. `Lev.genUlt`: every ultrafilter finer than such an `F` is in `GenUlt u`; `exists_lev_of_genUlt`: every ultrafilter of `GenUlt u` is finer than such an `F` (so `GenUlt u` is the union over `n` of the closed sets of ultrafilters finer than level-`n` filters). `Lev.add`, `Lev.neg`: closure properties. |
| `Pw C n`, `Pw_mem`, `Pw_mono` | `n`-fold sumsets; for a symmetric `C ∈ u`, `Pw C n` belongs to every level-`n` filter. |
| `Vgen u`, `not_mem_Vgen_of_lev` | The intersection of all ultrafilters converging to `0`; a set missing from a level-`n` filter is missing from `Vgen u`. |
| `not_pretopological` | If `C ∈ u` is symmetric with `0 ∈ C` and for every `N` there is `m` such that every set of `u` contains `y` with `m • y ∉ Pw C N`, then `Vgen u ∉ genNull u`: the generated PG is not pretopological. |

Not formalized: the existence of idempotent ultrafilters, verification of the hypothesis of `not_pretopological` for the digit sets of a fast-growing FS-set (by hand in the article), the p-adic residue chain, the comparison with the Protasov-Zelenyuk topology.

## `PGTop` (group topologies containing a PG; Proposition 9.7 of version 7)
Imports `PGGenerated`. For an abelian group `G` with a group topology:
| Declaration | Statement |
|---|---|
| `topNull G`, `topNull_nullFamily` | The proper filters finer than the neighbourhood filter of `0` form a `NullFamily` (a topological group is a PG). |
| `genNull_subset_topNull_iff` | The PG generated by an ultrafilter `u` is contained in the topology iff `u` converges to `0` in it; hence the group topologies containing it are exactly those in which `u` converges to `0`. |
| `null_le_nhds_iff`, `conv_le_nhds` | All members of a family `C` of filters converge to `0` iff their intersection does; if all null filters of `C` converge to `0`, then `F → x` for the PG of `C` implies `F ≤ 𝓝 x`. |

Not formalized: the description of the finest group topology in which a filter converges (Protasov-Zelenyuk; Bergman).

## `PGSumset` (Lemma 7.4 of version 7)
Imports `PGIdem` (for `Pw`). In a Hausdorff topological additive group:
| Declaration | Statement |
|---|---|
| `isCompact_Pw`, `closure_Pw` | If `A` has compact closure then `Pw (closure A) m` is compact and `closure (Pw A m) = Pw (closure A) m` (the closure of an `m`-fold sumset is the `m`-fold sumset of the closure). |

## `PGGroupTop` (Lemma 7.7 and the reduction step of Theorem 7.9 of version 8)
Imports `PGXi`. `G` an abelian group with a Hausdorff group topology `β`, `I` an admissible ideal, `IsOpenXi I` the open sets of the topological modification, `Vxi I 0` the intersection of the filters converging to `0`.
| Declaration | Statement |
|---|---|
| `nested_sums_family` | If a family `𝒪` of sets containing `0` can be halved (`U ∈ 𝒪 ⇒ ∃ U' ∈ 𝒪, U' + U' ⊆ U`), then every `O ∈ 𝒪` contains all sums `f 0 + ... + f (n-1)`, `f j ∈ P j`, for a sequence `P j ∈ 𝒪` and all `n` at once. |
| `nested_sums_nhds`, `exists_open_half` | The case of the neighbourhoods of `0` in a topological additive group. |
| `neg_mem_Vxi`, `mem_Vxi_of_isOpenXi` | `V_ξ(0)` is closed under negation; a modification-open set containing `0` belongs to `V_ξ(0)`. |
| `half_of_groupTop` | If the open sets of a group topology `τ` on `G` are exactly the sets of `IsOpenXi I`, then the open sets containing `0` can be halved. |
| `nested_sums_Vxi` | Under this halving property every modification-open `O ∋ 0` contains `S_0 + ... + S_{n-1}` for all `n`, with symmetric `S_j ∈ V_ξ(0)`. |
| `no_groupTop_of_sums` | If some modification-open `O ∋ 0` is such that for all symmetric `S_j ∈ V_ξ(0)` some sum `x_0 + ... + x_{n-1}`, `x_j ∈ S_j`, lies outside `O`, then there is no group topology whose open sets are those of the modification. |

Not formalized: the construction of the closed set `C` showing that the hypothesis of `no_groupTop_of_sums` holds for the digit ideal (Section 7 of version 8), the pigeonhole and congruence arguments, the weight lemma beyond `PGBlock`.

## `PGJoin` and `PGTwoBases` (Section 8, two bases, of version 9)
`PGJoin` imports `PGXi`. For two ideals `I`, `J` of subsets of an abelian group, `joinI I J` is the family of sets contained in some `B + C`, `B ∈ I`, `C ∈ J`.
| Declaration | Statement |
|---|---|
| `joinI_admissible`, `joinI_proper_of` | If `I`, `J` are admissible (I1)-(I5) and `univ ∉ joinI I J` (which holds if no `B + C` is the whole group), then `joinI I J` is admissible. |
| `left_subset_joinI`, `right_subset_joinI`, `xi_mono_ideal` | `I ⊆ joinI I J`, `J ⊆ joinI I J`; if `I ⊆ J` then every filter converging for `ξ_{β,I}` converges for `ξ_{β,J}`. |
`PGTwoBases` imports `PGJoin` and `PGDigit`; `Dsum p q k l = D_{p,k} + D_{q,l}`.
| Declaration | Statement |
|---|---|
| `joinI_Ip_iff` | A set is in the join of `Ip p` and `Ip q` iff it lies in some `D_{p,k} + D_{q,l}`. |
| `univ_notin_join_of_finite`, `Ipq_admissible` | If for all `k`, `l` the elements of `D_{p,k} + D_{q,l}` of absolute value at most `X` lie in a finite set with fewer than `2X+1` elements (for some `X`), then the join is proper and admissible. |
| `exists_nondegenerate_sub` | Every finite multiset of values has a sub-multiset with the same sum and no nonempty sub-multiset of sum `0` (removal of vanishing subsums). |

Not formalized: the counting hypothesis itself (it follows from the quoted height inequality for non-degenerate sums of `S`-units) and the counting of tuples.

## `PGCompletion` (the finest group topology as a trace, version 10)
`PGCompletion` imports `PGXi`. Setting: `G` an abelian group with a T0 uniform group topology `σ`, `K` a uniform abelian group, `e : G →+ K` injective, `A k ⊆ G` increasing with union `G`, `E k = closure (e '' A k)`. Neither compactness of `K` nor closedness of the `A k` is used.
| Declaration | Statement |
|---|---|
| `uniformContinuous_of_group` | A map from a subset of `K` to `G` is uniformly continuous iff for every neighbourhood `U` of `0` there is a neighbourhood `W` of `0` with `z - y ∈ W ⇒ g z - g y ∈ U`. |
| `huc_of_sub` | If `A - A ⊆ A'` and the inclusion of `A'` (with the trace of `K`) is continuous at `0` for `σ`, then `x, y ∈ A`, `e x - e y ∈ W` imply `x - y ∈ U`. |
| `exists_extension` | Under that condition the map `e x ↦ x` on `e '' A` extends to a continuous map from `closure (e '' A)` to the Raikov completion of `G` (`UniformSpace.Completion G`). |
| `denseRange_inclusion_closure`, `extension_compat` | Extensions at two levels `A ⊆ B` agree on `closure (e '' A)`. |
| `trace_open` | If the condition holds for every `A k`, every `σ`-open `V ⊆ G` is `e ⁻¹' W` for a set `W ⊆ K` whose trace on every `E k` is open in `E k` (that is, `V` is open in the trace of the direct limit topology of `⋃ E k`). |
| `trace_cont_of_contains` | If a second topology (given by neighbourhood filters `N x`) contains the convergence `ξ_{β,I}` (every filter with `xi I F x` satisfies `F ≤ N x`), then for `A ∈ I` every `U ∈ N x` contains `W ∩ A` for a `β`-neighbourhood `W` of `x` (continuity of `(A, β) → (H, second topology)`). |

Not formalized: that the direct limit topology of `⋃ E k` is a group topology (it needs the quoted theorem on products of `k_ω`-spaces), the instance `G = ℤ`, `K` the Bohr compactification, `A k = D_{p,k}`, and the hypothesis `A_k - A_k ⊆ A_{2k}` for the digit sets (this one is in `PGDigit`).

## `PGNoGroup` and `PGSeparation` (Section 8, version 11: the modification of `ξ_{p,q}` is not a group topology)
`PGNoGroup` imports `PGGroupTop`. Setting: `G` an abelian Hausdorff topological group, `I` an admissible ideal, `A n ∈ I` a sequence with every `B ∈ I` contained in some `A n`.
| Declaration | Statement |
|---|---|
| `exists_nhds_inter_subset_of_Vxi` | If `S ∈ V_ξ(0)` and `B ∈ I`, then `W ∩ B ⊆ S` for some neighbourhood `W` of `0`. |
| `isOpenXi_compl_of_cover` | If `C ∩ A n` is closed for every `n`, then `G ∖ C` is `ξ`-open (open in the topological modification). |
| `no_groupTop_of_cover` | Let `0 ∉ C`, `C ∩ A n` closed for all `n`, `B₀ ∈ I`, and suppose that for every sequence `W j` of neighbourhoods of `0` there are `n` and `f j ∈ W j ∩ B₀` with `f 0 + ... + f (n-1) ∈ C`. Then no group topology has `IsOpenXi I` as its family of open sets. |
`PGSeparation` imports `PGBlock`; terms are `(sign, exponent)` pairs and `val p l` is the value of a list.
| Declaration | Statement |
|---|---|
| `separation` | If `val p lt = val p la + val p lb`, all exponents of `lt` are `> s + L`, all exponents of `lb` are `≤ s`, no exponent of `la` lies in `(s, s + L]`, and the total number of terms is `< p^(L+1)`, then `val p lt ∈ D p la.length` (a sum of at most `|la|` signed powers). |
| `filter_flip` | Filtering by exponent commutes with flipping signs. |

Not formalized: the structure of the sets `T_i` (exact weight, exponents, pigeonhole), the finiteness `T_i ∩ (D_{p,k} + D_{q,l})` for `k < 2r` (it uses the finiteness of `D_{p,K} ∩ D_{q,l}`, `PGSUnit`, under the S-unit equation theorem as hypothesis), the choice of the cutoffs `M_i` and the verification of the hypotheses of `no_groupTop_of_cover`.

## `PGBohrGen` (Section 9, version 13: ultrafilters of positive density)
`PGBohrGen` imports `PGIdem` and `PGTop`. Setting: `G` an abelian topological group, `u` an ultrafilter with `u ≤ 𝓝 0`. The hypothesis `Bog u` says that for every `A ∈ u` the set `A + A - A - A` contains a neighbourhood of `0` (in the article, for `G = ℤ` with the Bohr topology, this is Bogolyubov's theorem for sets of positive upper Banach density, which is quoted and not formalized).
| Declaration | Statement |
|---|---|
| `lev4`, `exists_A_of_mem_lev4` | The level filter `u + u - u - u` (`Lev u 4`), and every set of it contains `A + A - A - A` for some `A ∈ u`. |
| `nhds_le_lev4` | Under `Bog u`, the neighbourhood filter of `0` is finer than the level filter `u + u - u - u`. |
| `genNull_eq_topNull` | Under `u ≤ 𝓝 0` and `Bog u`: the null filters of the PG `ξ(u)` generated by `u` are exactly the proper filters converging to `0` (`genNull u = topNull G`), i.e. `ξ(u)` is the convergence of the topology. |
| `halving4` | In a topological additive group every neighbourhood `U` of `0` contains `V + V - V - V` for a neighbourhood `V` of `0`. |
| `nhds_le_of_bog` | Under `Bog u`, every group topology `σ` (given as an explicit instance argument) in which `u` converges to `0` has all its neighbourhoods of `0` among the neighbourhoods of `0` of the given topology, i.e. `σ` is coarser. |

Not formalized: Bogolyubov's theorem, that members of ultrafilters in the smallest ideal have positive upper Banach density, that idempotent ultrafilters converge to `0` in the Bohr topology, and the identification with `G = ℤ`.

## `PGSubgroupBase` and `PGFSRigid` (Section 9, version 14: subgroup-based and strongly summable ultrafilters)
`PGSubgroupBase` imports `PGIdem`. Setting: `G` an abelian group, `u` a nonprincipal ultrafilter such that every `A ∈ u` contains `H ∖ {0}` for a subgroup `H ∈ u` ("subgroup-based"; on the Boolean group `(ℤ/2)^(ω)` these are exactly the strongly summable ultrafilters).
| Declaration | Statement |
|---|---|
| `subgroup_mem_GenUlt`, `subgroup_mem_Vgen` | Every subgroup `H ∈ u` belongs to every ultrafilter converging to `0` in the PG `ξ(u)` generated by `u`, hence to `Vgen u = V_ξ(0)`. |
| `exists_sum_of_mem_plusF_two` | A set of the filter `u + u` contains `A₁ + A₂` with `A₁, A₂ ∈ u`. |
| `Vgen_mem_genNull` | If `u` is subgroup-based (and nonprincipal), `Vgen u` is itself a null filter, i.e. `ξ(u)` is pretopological. |
`PGFSRigid` (no imports beyond Mathlib): rigidity of representations by a rapidly growing sequence `y : ℕ → ℤ`, `y n ≥ 0`.
| Declaration | Statement |
|---|---|
| `fs_rigid` | If `y n > D * (y 0 + ... + y (n-1))` for `n > N₀`, `|d n| ≤ D`, `d` has finite support and `∑ d n * y n = 0`, then `d n = 0` for all `n > N₀`. |
| `no_multiple` | If `y n > (2N+1) * (y 0 + ... + y (n-1))` for `n > N₀`, `F` is a nonempty finite set of indices `> N₀`, and `G j` are finite index sets and `ε j = ±1` for `j < N`, then `(N+1) * ∑_{n∈F} y n ≠ ∑_j ε j * ∑_{n∈G j} y n`. |

Not formalized: that `ξ(u)` for a subgroup-based `u` is the convergence of a group topology (this follows from "pretopological implies topological", not formalized), the existence of strongly summable ultrafilters, the tails lemma, the P-point argument, and the application of `no_multiple` to the criterion `not_pretopological` (`PGIdem`).

## `PGGameLemma` and `PGOpenSets` (Section 9, version 15: the topological modification for stable ordered-union ultrafilters)
`PGGameLemma` (no imports beyond Mathlib): blocks form a type `X` with a rank `mx : X → ℕ` (finitely many blocks of rank `≤ m`) and a relation `lt` (`max a < min b`) with `lt a b → mx a < mx b`; `U` is an ultrafilter on `X` with `{b | lt a b} ∈ U`, the stability property (homogeneous `H ∈ U` for every partition of the pairs `lt a b`), and a base property (inside every `H ∈ U` a `lt`-increasing sequence with the winning property `Win`).
| Declaration | Statement |
|---|---|
| `finite_lists` | Lists of bounded length over a finite set form a finite set. |
| `game_lemma` | For every strategy `S` (a member `S σ ∈ U` for every finite history `σ`) there is a `lt`-increasing sequence `a` with `Win a` and `a k ∈ S (a 0, ..., a (k-1))` for all `k`: Player 1 has no winning strategy in the game `G(U)`. |
`PGOpenSets` imports `PGIdem`; `u` is an ultrafilter on an abelian group.
| Declaration | Statement |
|---|---|
| `mem_of_mem_Vgen_lev` | A member of `Vgen u = V_ξ(u)(0)` belongs to every level filter `Lev u n F`. |
| `negF`, `lev_negF`, `negF_mem` | The all-minus filter sums `(-u) + ... + (-u)` and their members. |
| `exists_nsmul_mem` | If `s ∈ Vgen u` and `n : ℕ`, there is `A ∈ u` with `n • y ∈ s` and `n • (-y) ∈ s` for all `y ∈ A` (Lemma A: for `s = O - z`, `z + c y ∈ O` for `|c| ≤ n`). |

Not formalized: that the ultrafilters `φ_*U` with `U` stable ordered-union satisfy the hypotheses (the identification with finite subsets of `ℕ`, `FU`-sets, `max`, `min`), the strategy built from an open set, the box induction and the passage from the box to the sets `U(S_0, S_1, ...)`, the non-halvability proposition (it uses `fs_rigid` of `PGFSRigid`), and the application of the quoted base theorem (`prop:zp`).

## `PGImageStrong` and `PGSubgroupStrict` (Section 9, version 18: strong summability of images and strictness for subgroup-based ultrafilters)
`PGImageStrong` (no imports beyond Mathlib): blocks form a type `X` with a relation `lt`, a union operation `un` and a value function `f : X → ℕ` with `f a > 0` and `f (un a b) = f a + f b` when `lt a b`, `lt a b → lt b c → lt a (un b c)`; `U` is an ultrafilter on `X` with the stability property and a base property (inside every `H ∈ U` an `lt`-increasing sequence `a` in `H` with all `un (a i) (a j)`, `i < j`, in `H`).
| Declaration | Statement |
|---|---|
| `no_strictAnti_nat` | There is no strictly decreasing sequence of natural numbers. |
| `stable_image_increasing` | There is `H ∈ U` such that `f a < f b` whenever `a, b ∈ H` and `lt a b` (the homogeneity step showing that the image of a stable ordered-union ultrafilter under `φ(s) = ∑_{i∈s} x_i` with `x_i > 0` is strongly summable). |

`PGSubgroupStrict` (no imports beyond Mathlib): `u` is a nonprincipal ultrafilter on an abelian group `G` with `SubgroupBase u` (every member contains `H ∖ {0}` for a subgroup `H ∈ u`).
| Declaration | Statement |
|---|---|
| `idempotent_of_subgroupBase` | For every `A ∈ u`, `{h | {k | h + k ∈ A} ∈ u} ∈ u`, that is, `A ∈ u ⊕ u`. |
| `two_torsion_mem` | `{g | g + g = 0} ∈ u`. |
| `no_subgroupBase_of_torsionFree` | There is no such `u` on a group without elements of order `2` (in particular on `ℤ`). |

Not formalized: the passage from the homogeneous set to the finite-sum sets `FS(b)` (strong summability of the image), the colouring of a basis of `G[2]`, the infinite index of the resulting subgroup and the comparison with the Bohr topology (Corollary 9.13), and the abstract-group remark on Theorem 9.19. A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
