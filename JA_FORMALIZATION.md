# Formalization of the joint-approximation (JA) theorem in Lean 4 / Mathlib

Status date: 31 October 2026. Lean 4.35.0 and the pinned Mathlib (`lake-manifest.json`).
Article: `TVGaddmore_v28` (Joint Approximation and the Mixed-Prime Character Group).

## What is proved

Joint approximation is the statement

```lean
def JAProp : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ k : ℤ, Pn (sqScales 3) k < δ ∧ Pn (sqScales 2) (k - 1) < δ
```

(`LeanCheck/JAAssembly.lean`; `Pn S k = sup_{q ∈ S} ‖k / q‖_{ℝ/ℤ}`, `sqScales ℓ = {ℓ^(n^2) : n ≥ 1}`).

**Main theorem** (`LeanCheck/JAWeilE.lean`):

```lean
theorem JA_of_matveev (A : ℝ) (hA : 0 ≤ A) (hP : JAClose.TwoTermSeparation A) : JAProp
```

Every other step of the proof is checked. The only external hypothesis is `TwoTermSeparation A`
(`LeanCheck/JAClose.lean`), the two-term separation estimate that the article derives from Matveev's lower
bound for linear forms in logarithms (opposite-sign case, close pair of prime-square periods `Q < Q' < tQ`,
`t = sqrt(log Q)`, integers `0 < |r| ≤ ⌈t²⌉`, `|s| ≤ ⌈4t³⌉`, conclusion
`‖r/Q + s/Q'‖ ≥ Q⁻¹ exp(-A log²(2+t))`).

**Weaker hypothesis suffices.** The chain uses the separation only through a profile `a(t)` (the separation radius at a close pair
is `Q⁻¹ exp(-a(t))`), with two growth conditions (`JAProfile.lean`: `WindowProfile`, `CloseGrowth`). `A log²(2+t)` satisfies them
(`windowProfile_A`, `closeGrowth_A`), and so does `c t` for every `0 ≤ c < 1`:

```lean
theorem JA_of_weak_separation (c : ℝ) (h0 : 0 ≤ c) (h1 : c < 1)
    (hP : JAClose.TwoTermSep (fun t => c * t)) : JAProp
```

i.e. a separation `‖r/Q + s/Q'‖ ≥ Q⁻¹ exp(-c sqrt(log Q))` already gives JA. This is still a hypothesis, not a proof; it is
only a weaker one than the Matveev form above (`JAMain.JA_of_profile` is the general statement).

**JA is therefore formalized conditionally on that estimate. It is not an unconditional Lean proof of JA.**
Matveev's theorem is not in Mathlib and is not proved here, and the form of `TwoTermSeparation` has not been
verified against the published statement by an independent reader.

The axiom report is in `verification/ja-check.txt`: every listed declaration depends only on
`propext`, `Classical.choice`, `Quot.sound`. The files contain no `sorry`.

## Map of the development (`LeanCheck/`)

| Step of the proof | Modules |
|---|---|
| Window kernel, `ℤ/Q` bridge, Parseval, tail bound `25 D⁴/u³`, per-realization mass bounds | `JAWindow`, `JAWindowQ`, `JAWindowTail`, `JAMass`, `JATransfer`, `JALocalize` |
| Density, support and packing, multi-level realization, buffered heights | `JADense`, `JASupport`, `JAEnergy*`, `JABlocks`, `JAPackaging`, `JARandom`, `JARealization`, `JASpectral`, `JAMulti`, `JAMulti2`, `JAHeights`, `JAFinal`, `JAFinal2`, `JAAssembly` |
| Product identity, arc-mass reduction, kernel merging, scalar bound | `JAProduct`, `JAProduct2`, `JAScalar` |
| Center maximality, far-field recursion, kernel tail conversion, merged growth | `JACenter`, `JAFar`, `JAKernTail`, `JAFarSep`, `JAMerged`, `JASorted` |
| Separated levels (S6a), close levels with the two-term separation (S6b), non-deep levels (S6c) | `JASep`, `JAClose`, `JANonDeep` |
| Final product bound (S7) and assembly of `CentralBound` | `JAProductFinal`, `JAAssemble`, `JACentral`, `JACentral2`, `JAMain` |
| Separation profiles (`WindowProfile`, `CloseGrowth`, linear profile `c t`) | `JAProfile` |
| One-prime theorem (`P_ℓ`-continuous parameters lie in `ℤ[1/ℓ]/ℤ`) | `JAOnePrime` |
| Weil's theorem for `ℤ` (compact-quotient criterion) | `JAWeilA` (Haar measure, `L²`, translations), `JAWeilB` (compact convolution operator), `JAWeilC` (`weil_abstract`), `JAWeilD` (`weil_seminorm`), `JAWeilE` (`compactQuotientCriterion`, `JA_of_matveev`) |
| Earlier reduction to a general fact (superseded) | `JACompact` |

## How to check

```sh
lake build LeanCheck.JAWeilE LeanCheck.JACompact   # builds the whole JA chain
lake env lean LeanCheck/JAWeilE.lean               # prints the axioms of JA_of_matveev
```

## Scope and caveats

- A Lean proof verifies its formal statement under its hypotheses. That `JAProp` and `TwoTermSeparation` say what
  the article says still requires mathematical review.
- `JACompact.lean` (reduction of the compact-quotient criterion to the general statement `PrecompactMAP`) was
  written first and is kept; `JAWeilE.lean` proves the criterion outright.
- The numerical experiments in `experiments/` are not Lean proofs.

## TVGplus modules

`LeanCheck/TVGPlus*.lean` (`TVGPlusValuation`, `TVGPlusCount`, `TVGPlusCert`, `TVGPlusCertData`, `TVGPlusCertRows`,
`TVGPlusCertRowsData`, `TVGPlusPair`, `TVGPlusDD`, `TVGPlusSizes`, `TVGPlusDual`, `TVGPlusPairDual`, `TVGPlusEffective`, `TVGPlusGcd`, `TVGPlusOrderA`-`E`, `TVGPlusOrder`, `TVGPlusPairGcd`) formalize the elementary results of the article *Quantitative Bounds for Prime
Square Metrics*: valuation thresholds and the universal divisor, the pigeonhole upper bound, exact finite certificates,
and, under the hypothesis `DD S` of diagonal density, residue independence and the valuation vectors of the ball.
`TVGPlusPair.lean` derives `DD {2, 3}` from `JAProp`, so these results hold for the pair `{2, 3}` conditionally on
`TwoTermSeparation` (through `JAWeil.JA_of_matveev`). `TVGPlusGcd.gcd_iff` proves, under `DD S`, that `D_S(δ)` is the gcd of the ball (by an elementary construction that replaces the
character argument); `TVGPlusOrder` proves both bounds of the logarithmic order (`uS_lower` with `c_S`, `uS_upper` with `x_S`),
and the exact one-prime value `u_{p}(δ) = p^(a_p(δ)²)`; `TVGPlusPairGcd` states the gcd equality for `{2, 3}` (from `JAProp`, from the
Matveev separation and from the weak separation). `TVGPlusDD` proves that `DD (A ∪ B)` holds exactly when `DD A`, `DD B` and the block approximation `JA(A,B)` hold, so diagonal density
for a finite set of primes is equivalent to a chain of block approximations, and that a shifted target reduces to the unit target.
`TVGPlusSizes` gives the explicit size bound in the block construction `k = m a + (1 - m) b` (`|k| <= (|m| + 1)(|a| + |b|)`), the identity
`A_S^2 - 4 c_S = sum_p sum_{q != p} (log p log q)^(-1/2)`, `x_S < A_S^2`, and the one-prime limit of `log u / (log (1/delta))^2`.
`TVGPlusDual` proves the dual-group lemma: under `DD S`, a parameter is continuous for the `P_S`-topology exactly when `M alpha` is an
integer for some `M` whose prime factors lie in `S` (`dual_of_DD`, with the converse `contAt_of_denominator`); `TVGPlusPairDual` gives the dual
`Z[1/6]/Z` of the `{2,3}` join from `JAProp`, from the Matveev separation and from the weak separation.
`TVGPlusEffective` proves the description of sequences converging to zero (`seq_lower_liminf`, `seq_upper`) and the effective transfer
from unit-target block bounds to all targets (`effective_transfer`, for `0 < eps <= 1/2`).
Not formalized: the exact searches for the least witnesses. Axiom report: `verification/tvgplus-check.txt`.

## TVGplus: verified exhaustive searches, the model, and the close chain (2026-11-04)

`TVGSearchDef`, `TVGPlusSearch` and `TVGPlusSearchLeast` prove the soundness of a Chinese-remainder search on residue
trees: if every candidate assembled from the residues of two prime-square chains fails at an explicit coordinate, then
no integer in `[1, X]` lies in the shifted ball `{k : P_p(k - s_p) < 1/m for the listed (p, s_p)}`; with a membership
certificate this gives the least positive element (`least_of_search`, `none_of_search`).  The instances are checked by
`decide +kernel` (no `native_decide`): `TVGSearchNull23` (the least element of the ball of `{2, 3}` for
`35 <= m <= 78`, and no element up to `4 * 10^16` for `79 <= m <= 100`), `TVGSearchShA` and `TVGSearchShB` (the two
shifted problems, `3 <= m <= 66` and `3 <= m <= 53`), `TVGSearchTriA`, `TVGSearchTri0`, `TVGSearchTri0Hi` (least
elements for `{2, 3, 5}`), `TVGSearchTriAMem` (witnesses for `21 <= m <= 26`), `TVGSearchGcd235` (the gcd of the ball
for `5 <= m <= 12`), with the heaviest chunks split into the `TVGSearchPart_*` modules to bound kernel memory.
`TVGPlusModel` formalizes the independent-window model (density, the sum `Lam`, and its exact evaluation as a sum over
blocks, `lam_blocks`); `TVGPlusModelData_*` bracket `N*` for `m = 10^2, 10^4`.  `TVGSearchChain` proves that the
levels `5^(19^2) < 3^(23^2) < 2^(29^2)` form a chain with consecutive ratios below `sqrt(log Q)`.
`TVGSearchCheck` prints the axioms of every final statement (propext, Classical.choice, Quot.sound only).

## TVGplus: sorted CRT window search (2026-11-04)

`TVGWindowDef`, `TVGPlusWindow` and `TVGWindowLit` formalize the matching step of a search for the least shifted witness
(the method of Codex's `shifted_window_search.py`): with `k = r + P t`, `v = r * Pinv mod Q`, `u = rho * Pinv mod Q`
one has `u = v + t (mod Q)`, so the candidates are the pairs with `u` in the window `[v, v + (X - r) / P]` of the doubled
sorted `u`-list, found by a monotone sweep (`sweep_complete`, `window_complete`, `window_none`, `slice_none`,
`least_of_window`, `least_of_slices`; the sorting is a fuel-bounded merge sort whose output sortedness is checked by the
kernel, and only element preservation is proved).  `TVGSearchWindowCheck` reproduces by this method the shifted pair at
radius `1/12` and the shifted triple at radius `1/20`.  The rows `21 <= m <= 26` of the shifted triple exceed the memory
of the kernel on the machine used (more than 6 GB for one sorted 3-adic list) and are not covered.

## TVGplus: minimum of the shifted triple for 21 <= m <= 26 (2026-11-04, native evaluation)

`TVGWindowCoreIsolated`, `TVGWindowCore22` and `TVGWindowCore24` (core Lean only, no Mathlib) prove, for the shifted triple
`P_2(k - 1), P_3(k), P_5(k) < 1/m`, that no positive integer below the witness passes all square-power coordinates:
`triple21_no_smaller_integer` (m = 21, witness 566864750054385), `triple22_no_smaller_integer` (m = 22, 23, witness
1111607529308145) and `triple24_no_smaller` (m = 24, 25, 26, witness 1667477197289985; the range above `2^25 * 3^16` is
handled by shifting `k = j + 2^25 * 3^16`, which keeps the residues).  They reuse the sorted Chinese-remainder sweep
completeness argument of `TVGPlusWindow` and evaluate one Boolean certificate per range with `decide +native`; the
statements therefore depend, besides propext, Classical.choice and Quot.sound, on generated axioms
`<check>._native.decide.ax_...` (one for rows 21 and 22-23, two for rows 24-26).  `TVGWindowBridge` proves
`good_all_iff_pseudonorm` (standard axioms only), and `TVGWindow21Real`, `TVGWindow22Real`, `TVGWindow24Real` assemble
`triple21_real_minimum`, `triple22_23_real_minimum` and `triple24_26_real_minimum` for the article pseudonorm.  The
Lean sources of the cores and of the real-valued row 21 and 22-23 files were written by Codex; the row 24-26 bridge was
added and a proof step of `TVGWindowCore24` (a Mathlib-only tactic) was replaced to compile with core imports.

## TVGplus: shifted targets, signed to positive witnesses, full-period obstruction (2026-11-05)

`TVGShiftedLongNull` proves `explicit_long_null`: for finitely many integer bases `>= 2`, `R <= 2^L`, `m * delta >= 2` and
`m <= 2^h`, there is an integer `k` with `R <= k <= 2^(2L + 4 s^2 h^2)` whose pseudonorms are all below `delta`; it is the
pigeonhole argument of `TVGPlusCount` with one additional residue class modulo `R`.  `TVGShiftedPositive` proves
`positive_from_signed_long`: a signed witness `k0` with `|k0| <= H`, `P_p(k0 - 1) < eps/2` and `P_q(k0) < eps/2` yields a
positive witness `k <= H + 2^(2L + 16 h^2)` with `P_p(k - 1) < eps` and `P_q(k) < eps` (`H + 1 <= 2^L`, `4 <= 2^h eps`), so the
exponent of `log (1/eps)` in a signed height bound is preserved.  `TVGShiftedObstruction` proves
`full_period_tail_obstruction`: if `m P Q < p^((n+1)^2)` and `m P Q < q^((j+1)^2)` for `P = p^(n^2)`, `Q = q^(j^2)`, then
`m < p q`.  All three statements depend only on propext, Classical.choice and Quot.sound.  No upper bound for a nonzero shifted
target is proved.  The sources of the long null witness and of the obstruction were drafted by Codex and completed by Claude.

## Diagonal density for three primes: reduction layer (`DD3Reduction`, 7 November 2026)

Module `LeanCheck/DD3Reduction.lean` (imported by `LeanCheck.lean`; it imports `MixedPrimeAnalytic`, `JAMerged`, `JAEnergyIdentity`), axiom report in `LeanCheck/DD3ReductionAxioms.lean` and `verification/dd3-reduction-check.txt`. It is the first phase of a Lean version of the conditional proof of `DD({2,3,5})` (research note `TVGplus_conditional_DD235_2026-11-07.md`): the steps that change when a third chain of prime squares is added and that do not involve the pseudonorms `P_p`.

| Declaration | Statement |
|---|---|
| `three_parts_zero` | In an abelian group, if `m_i • a_i = 0` for pairwise coprime `m_2, m_3, m_5` and `a_2 + a_3 + a_5 = 0`, then all `a_i = 0`. |
| `sum_rep3`, `card_V3_ge`, `sum_sq_rep3` | For finite `A, B, C ⊆ ℤ`, weights `f, g, h` and `R(u,v) = ∑_{x-y=u, y-z=v} f(x) g(y) h(z)`: `∑_w R(w) = ∑f ∑g ∑h`, `(∑f ∑g ∑h)² ≤ |T| ∑_{w ∈ T} R(w)²`, and `∑_w R(w)²` is the collision sum over pairs of triples. |
| `energy3_eq_acf` | The collision sum equals `∑_{d ∈ D} acf_A f(d) acf_B g(d) acf_C h(d)` for any finite `D ⊇ A - A`. |
| `syndetic_of_dense_difference3` | A symmetric `W ⊆ ℤ²` containing `0` with finite `V ⊆ [-X,X]²`, `|V| ≥ c (2X+1)²`, `V - V ⊆ W` for arbitrarily large `X` is syndetic. |
| `merged_gap4`, `merged_gap_seq3`, `merged_gap_seq_odd3`, `merged_growth_exp3`, `window_card_le_three` | Among four increasing periods `b^(n²)`, `b ∈ {2,3,5}`, two share a base: `log Q_{i+3j} - log Q_i ≥ j sqrt(log Q_i)`, `Q_{i+m} ≥ Q_i exp(t_i ⌊m/3⌋)`; a logarithmic window of width at most `sqrt u` contains at most three periods. |

Not formalized: the cluster estimate with a third level and the hypothesis `H(2,3,5)` (finitely many triples of levels `2^(a²), 3^(b²), 5^(c²)` in a window of length `A log²(2+t)`), the central bound for three chains and the Fourier step, the compact-quotient step for `ℤ²`, the Matveev-type separation for the pairs `(2,5)` and `(3,5)`, and the final theorem. `H(2,3,5)` is a conjecture (a Borel-Cantelli prediction); it is not proved.

### Phases 2 and 3: cluster estimates and the final product bound (`DD3Cluster`, `DD3Product`, 7 November 2026)

Modules `LeanCheck/DD3Cluster.lean` (imports `JAClose`, `JAProductFinal`, `DD3Reduction`) and `LeanCheck/DD3Product.lean` (imports `JAProductFinal`, `JAMerged`, `MixedPrimeAnalytic`), both imported by `LeanCheck.lean`; axiom reports in `LeanCheck/DD3ClusterAxioms.lean`, `LeanCheck/DD3ProductAxioms.lean` and `verification/dd3-cluster-product-check.txt`.

`DD3Cluster` re-proves the factor estimates of the normalized product argument for scales `b_p^(n_p²)` from three chains (bases 2, 3, 5), where only the growth `Q_{p+k} ≥ Q_p exp(t_p ⌊k/3⌋)` is available:

| Declaration | Statement |
|---|---|
| `geom_three`, `sum_tau3`, `sum_tau3b` | `∑_{j<M} q^⌊j/3⌋ ≤ 6`; summation of the far-field terms with period-three growth. |
| `far_separated3`, `far_beyond3` | Far-field bound after one level (monotone scales) and after two levels (third level `Q_{p+2} ≥ Q_p exp c`). |
| `separated_factor_abs`, `close_factor_abs` | Copies of `JASep.separated_factor` and `JAClose.close_factor` with the far-field bound as a hypothesis. |
| `separated_factor3`, `close_factor3` | `f_p - 1` for a separated level, and for a close pair with the two-term separation as a hypothesis and the third level beyond `Q_p exp(a(t) + log t)`. |
| `sep_cube3`, `close_cube3_G` | Both bounds are at most a constant times `t⁻³`. |
| `merged_gap_fin3`, `hgrow3_of_merged`, `hmon_of_merged` | The growth and monotonicity hypotheses hold for a finite increasing selection of periods of the bases 2, 3, 5. |

`DD3Product` generalizes the final product bound: `sum_inv_cube_gen` (`∑ (√(lp b n))⁻³ ≤ 2 ∑_{b∈ℬ} (√log b)⁻³` over distinct periods with bases in a finite set `ℬ`), `product_final_gen` (`∏ f_i ≤ B^(K + |ℬ|⌊2T⌋) exp(Cf · 2 ∑_{b∈ℬ} (√log b)⁻³)`) and `product_final3` (`ℬ = {2,3,5}`).

Not formalized: the classification of the levels of the sorted list and the verification of the per-level hypothesis, the assembly of the central bound and the Fourier step for three weights, the compact-quotient step for `ℤ²`, the two-term separation for the pairs `(2,5)` and `(3,5)`, the hypothesis `H(2,3,5)` and the final theorem `DD {2,3,5}`. `DD3Cluster` copies parts of `JASep` and `JAClose`; the linter prints deprecation and unused-argument warnings for these copies.

### Phase 4: classification of the levels (`DD3Assemble`, 7 November 2026)

Module `LeanCheck/DD3Assemble.lean` (imports `JACentral`, `DD3Cluster`, `DD3Product`), imported by `LeanCheck.lean`; axiom report in `LeanCheck/DD3AssembleAxioms.lean` and `verification/dd3-assemble-check.txt`. It is the three-base counterpart of `JAAssemble` and `JACentral.prod_f_bound`: the product `∏_{i<L} f_i` of the factors `f_i = H_i(0)/H_{i+1}(0)` of the product identity for the sorted list of prime-square scales of the bases 2, 3, 5 is bounded independently of `L`, `N`, `m`, `X`.

| Declaration | Statement |
|---|---|
| `HTT3`, `BadTriple`, `HFin` (definitions) | The two-term separation for ordered pairs of distinct bases in `{2,3,5}` (hypothesis); a bad triple (three levels, the second a close pair with the first, the third inside the window `Q exp(a(t) + log t)`); `HFin a K₁`: at most `K₁` bad triples (hypothesis `H(2,3,5)`). |
| `htop3_of_large`, `bases_differ3` | `(8B)³ e^{-3t} ≤ 1/2` for large `t`; a close pair has different bases. |
| `level_sep3`, `level_close3` | `f_p ≤ 1 + Cs t⁻³` for a separated level; `f_p ≤ 1 + Cc t⁻³` for a close pair whose third level lies outside the window (through `separated_factor3`, `close_factor3`). |
| `non_deep_card_le_three` | At most three non-deep levels. |
| `prod_f_bound3` | Under `HTT3` and `HFin`: for large `X`, `∏_{i<L} f_i ≤ Cp`, `Cp` independent of `L, N, m, X`. |

Not formalized: the assembly of the central bound for three chains (random translations, three-fold energy, the Fourier step), the compact-quotient step for `ℤ²`, the two-term separation for the pairs `(2,5)` and `(3,5)` (assumed in `HTT3`), the derivation of `HFin` from `H(2,3,5)`, and the final theorem `DD {2,3,5}`. `H(2,3,5)` is a conjecture; it is not proved. The linter prints warnings for proofs copied from `JAAssemble` and `JANonDeep`.
