# TwoPrimes: Lean checks for the two-prime square-chain metrics (21 November 2026)

Modules: `LeanCheck/TwoPrimesTransfer.lean`, `TwoPrimesBall.lean`, `TwoPrimesTable.lean`, and the axiom report `TwoPrimesAxioms.lean`. Typechecked with Lean 4.35.0 and Mathlib, no `sorry`; every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`. The modules use only the layer `MixedPrimeBasics`, `MixedPrimeRadii`, `MixedPrimeSplit` (the pseudonorm `Pn S k = sup_{q ∈ S} ‖k/q‖`, the scale sets `sqScales ℓ = {ℓ^(n²)}`, subadditivity and `Pn (m k) ≤ |m| Pn k`); no diagonal density and no analysis is assumed.

Notation: `P_ℓ = Pn (sqScales ℓ)`. For a radius `η`, an integer `m` is a witness for the unit target if `Pn S3 m < η` and `Pn S2 (m - 1) < η`.

| Declaration | Statement |
|---|---|
| `transfer_unit` | `S2, S3` nonempty, `t ≠ 0`, `m` a witness for the unit target at radius `η` ⟹ `Pn S3 (t m) < |t| η` and `Pn S2 (t m - t) < |t| η`. |
| `transfer_height` | If moreover `|m| ≤ H`, there is `k` with `|k| ≤ |t| H` and the same two bounds; so `h_ε(t) ≤ |t| h_{ε/|t|}(1)` for the least witness heights. |
| `witness_mono` | A witness at radius `η` is a witness at every radius `η' ≥ η` (monotonicity of `h_ε`). |
| `transfer_unit_sq` | `transfer_unit` for `S3 = sqScales 3`, `S2 = sqScales 2`. |
| `half_ratio_bounds` | For `Q ≥ 2`: `1/3 ≤ ⌊Q/2⌋/Q ≤ 1/2`. |
| `nrm_far_multiple` | For `ℓ ≥ 2`, `b < n²`: `‖ ℓ^b ⌊ℓ^(n²-b)/2⌋ / ℓ^(n²) ‖ ≥ 1/3`. |
| `exists_far_multiple` | For `ℓ ≥ 2` and every `b` there is a multiple `k` of `ℓ^b` with `Pn (sqScales ℓ) k ≥ 1/3`. |
| `no_adic_nbhd_in_ball` | For `δ ≤ 1/3` the ball `{P_ℓ < δ}` contains no `ℓ`-adic neighbourhood `ℓ^b ℤ` of `0`: the topology of `(ℤ, P_ℓ)` is strictly finer than the `ℓ`-adic topology (the finer-than part is `MixedPrime.valuation_bound`). |
| `ExplicitOK`, `explicit_m8`, `explicit_m16`, `explicit_m32`, `explicit_m64` | Exact arithmetic side conditions of the refined explicit null-witness bound `u(1/m) ≤ N = 2^(a₂²) 3^(a₃²) (2m)^d` (minimality of `a₂, a₃`, and `2 m N < 2^((R₂+1)²)`, `2 m N < 3^((R₃+1)²)`) for `m = 8, 16, 32, 64`, with `N = 805306368` at `m = 8`. The pigeonhole step is not part of Lean. |
| `near_coincidence_5_4` | `128·2^25 < 100·3^16 < 129·2^25`: the square levels `2^25` and `3^16` differ by a factor in `(1.28, 1.29)`. |

Not formalized (stated in the TwoPrimes notes): the digit-set model of the balls and the product formula for their autocorrelation, the collision-energy computations and certificates (computer-assisted, exact integer arithmetic, outside Lean), the completion `X_p` and its identification with `{x ∈ ℤ_p : ‖f_n(x)‖ → 0}`, non-local-compactness of `X_p`, the pigeonhole step of the explicit bound, and the energy estimate `C(r,X) ≤ 8/3 − δ` (open).

To recheck: `lake build` and `#print axioms` for each declaration above (`TwoPrimesAxioms.lean`).
