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
