import Mathlib

/-!
# TwoPrimes: the explicit null-witness bound with arcs of length `1/m`

`TwoPrimesTable` checks the side conditions of the explicit pigeonhole bound with `2m` arcs per retained
coordinate (`N = D (2m)^d`).  Two points of one half-open arc of length `1/m` already differ by less than `1/m`,
so `m` arcs suffice (the radius trick of the ThreePrimes article); the omitted coordinates then need only
`m N < p^((R_p+1)^2)`.  With `δ = 1/m`, `aₚ` least with `m < p^(2aₚ+1)` (`p = 2, 3`), `D = 2^(a₂²) 3^(a₃²)`,
`d = (R₂ - a₂) + (R₃ - a₃)` and `N = D m^d`:

if `m N < 2^((R₂+1)²)` and `m N < 3^((R₃+1)²)`, the pigeonhole step on the multiples `D j`, `0 ≤ j ≤ m^d`, with `m`
arcs per retained coordinate, gives `1 ≤ k ≤ N` with `P_{2,3}(k) < 1/m`.

This file proves (i) the arc step `arc_diff_lt`: equal `⌊m x⌋` and `⌊m y⌋` give `|x - y| < 1/m`, and (ii) by exact
natural-number arithmetic the side conditions for `m = 8, 16, 32, 64`.  **The pigeonhole step itself is not
formalized here.**
-/

namespace LeanCheck
namespace TwoPrimes

/-- Two reals in one half-open arc `[i/m, (i+1)/m)` differ by less than `1/m`. -/
theorem arc_diff_lt {m : ℝ} (hm : 0 < m) {x y : ℝ} (h : ⌊m * x⌋ = ⌊m * y⌋) : |x - y| < 1 / m := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [lt_div_iff₀ hm]
  have h2 : |m * x - m * y| = |x - y| * m := by
    rw [← mul_sub, abs_mul, abs_of_pos hm]
    ring
  linarith

/-- Side conditions for a parameter tuple `(m, a₂, a₃, R₂, R₃, d)` of the explicit bound with `m` arcs, where
`N = 2^(a₂²) 3^(a₃²) m^d`. -/
def ExplicitArcsOK (m a2 a3 R2 R3 d : ℕ) : Prop :=
  m < 2 ^ (2 * a2 + 1) ∧ (a2 = 0 ∨ 2 ^ (2 * (a2 - 1) + 1) ≤ m) ∧
  m < 3 ^ (2 * a3 + 1) ∧ (a3 = 0 ∨ 3 ^ (2 * (a3 - 1) + 1) ≤ m) ∧
  a2 ≤ R2 ∧ a3 ≤ R3 ∧ d = (R2 - a2) + (R3 - a3) ∧
  m * (2 ^ (a2 ^ 2) * 3 ^ (a3 ^ 2) * m ^ d) < 2 ^ ((R2 + 1) ^ 2) ∧
  m * (2 ^ (a2 ^ 2) * 3 ^ (a3 ^ 2) * m ^ d) < 3 ^ ((R3 + 1) ^ 2)

theorem arcs_m8 : ExplicitArcsOK 8 2 1 4 3 4 ∧
    2 ^ (2 ^ 2) * 3 ^ (1 ^ 2) * 8 ^ 4 = 196608 := by
  refine ⟨?_, by norm_num⟩
  unfold ExplicitArcsOK
  norm_num

theorem arcs_m16 : ExplicitArcsOK 16 2 1 5 4 6 := by
  unfold ExplicitArcsOK
  norm_num

theorem arcs_m32 : ExplicitArcsOK 32 3 2 7 5 7 := by
  unfold ExplicitArcsOK
  norm_num

theorem arcs_m64 : ExplicitArcsOK 64 3 2 8 6 9 := by
  unfold ExplicitArcsOK
  norm_num

end TwoPrimes
end LeanCheck
