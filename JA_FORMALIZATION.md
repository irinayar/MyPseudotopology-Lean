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
