import Mathlib

/-!
# TwoPrimes: arithmetic side conditions of the explicit null-witness bound

The refined pigeonhole bound of the note "TwoPrimes: explicit height bounds" (target B) states: for `δ = 1/m`
let `aₚ` be least with `m < p^(2aₚ+1)` (`p = 2, 3`), `D = 2^(a₂²) 3^(a₃²)`, choose retained levels up to `R₂, R₃`,
put `d = (R₂ - a₂) + (R₃ - a₃)` and `N = D (2m)^d`.  The pigeonhole step (multiples `D j`, `0 ≤ j ≤ (2m)^d`,
labelled by arcs of length `1/(2m)` at the retained coordinates) produces `k ≤ N` with `P_{2,3}(k) < 1/m`
provided the omitted coordinates are automatic: `2 m N < 2^((R₂+1)²)` and `2 m N < 3^((R₃+1)²)`.

This file checks, by exact natural-number arithmetic, the side conditions for the four smallest entries of the
table of the note (`m = 8, 16, 32, 64`), including the minimality of `a₂, a₃` and the value of `N`.  **The
pigeonhole step itself is not formalized here** (a different explicit form, with `N = 2^(16 h²)`, is
`TVGPlus.explicit_upper`).  The file also records the arithmetic of the closest pair of square levels below `2^(10^5)`:
`2^25` and `3^16` differ by a factor in `(1.28, 1.29)`.
-/

namespace LeanCheck
namespace TwoPrimes

/-- Side conditions for a parameter tuple `(m, a₂, a₃, R₂, R₃, d)` of the explicit bound, with
`N = 2^(a₂²) 3^(a₃²) (2m)^d`. -/
def ExplicitOK (m a2 a3 R2 R3 d : ℕ) : Prop :=
  m < 2 ^ (2 * a2 + 1) ∧ (a2 = 0 ∨ 2 ^ (2 * (a2 - 1) + 1) ≤ m) ∧
  m < 3 ^ (2 * a3 + 1) ∧ (a3 = 0 ∨ 3 ^ (2 * (a3 - 1) + 1) ≤ m) ∧
  a2 ≤ R2 ∧ a3 ≤ R3 ∧ d = (R2 - a2) + (R3 - a3) ∧
  2 * m * (2 ^ (a2 ^ 2) * 3 ^ (a3 ^ 2) * (2 * m) ^ d) < 2 ^ ((R2 + 1) ^ 2) ∧
  2 * m * (2 ^ (a2 ^ 2) * 3 ^ (a3 ^ 2) * (2 * m) ^ d) < 3 ^ ((R3 + 1) ^ 2)

theorem explicit_m8 : ExplicitOK 8 2 1 5 4 6 ∧
    2 ^ (2 ^ 2) * 3 ^ (1 ^ 2) * (2 * 8) ^ 6 = 805306368 := by
  refine ⟨?_, by norm_num⟩
  unfold ExplicitOK
  norm_num

theorem explicit_m16 : ExplicitOK 16 2 1 7 5 9 := by
  unfold ExplicitOK
  norm_num

theorem explicit_m32 : ExplicitOK 32 3 2 8 6 9 := by
  unfold ExplicitOK
  norm_num

theorem explicit_m64 : ExplicitOK 64 3 2 9 7 11 := by
  unfold ExplicitOK
  norm_num

/-- The closest pair of square levels of `2` and `3` below `2^(10^5)`: `3^16 / 2^25 ∈ (1.28, 1.29)`. -/
theorem near_coincidence_5_4 :
    128 * 2 ^ 25 < 100 * 3 ^ 16 ∧ 100 * 3 ^ 16 < 129 * 2 ^ 25 := by
  norm_num

end TwoPrimes
end LeanCheck
