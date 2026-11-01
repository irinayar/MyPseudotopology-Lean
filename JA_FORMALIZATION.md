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
`TVGPlusCertRowsData`, `TVGPlusPair`, `TVGPlusDD`, `TVGPlusSizes`, `TVGPlusDual`, `TVGPlusPairDual`, `TVGPlusGcd`, `TVGPlusOrderA`-`E`, `TVGPlusOrder`, `TVGPlusPairGcd`) formalize the elementary results of the article *Quantitative Bounds for Prime
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
Not formalized: the exact searches for the least witnesses. Axiom report: `verification/tvgplus-check.txt`.
