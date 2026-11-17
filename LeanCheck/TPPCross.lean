import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# ThreePrimePlus: the cross-product identities of the ray theorem and the rank lemma

For `z = n v + e` and `z' = n' v + f` (vectors in `ℝ³`), `H = z × z'` satisfies
`H · v = det(v,e,f) = (e × f) · v` and `H = v × (n f - n' e) + e × f`.
-/

namespace TPP

/-- `(z × z') · v` for `z = n v + e`, `z' = n' v + f` equals `(e × f) · v`. -/
theorem dot_cross_eq (v1 v2 v3 e1 e2 e3 f1 f2 f3 n n' : ℝ) :
    ((n * v2 + e2) * (n' * v3 + f3) - (n * v3 + e3) * (n' * v2 + f2)) * v1 +
    ((n * v3 + e3) * (n' * v1 + f1) - (n * v1 + e1) * (n' * v3 + f3)) * v2 +
    ((n * v1 + e1) * (n' * v2 + f2) - (n * v2 + e2) * (n' * v1 + f1)) * v3 =
    (e2 * f3 - e3 * f2) * v1 + (e3 * f1 - e1 * f3) * v2 + (e1 * f2 - e2 * f1) * v3 := by
  ring

/-- First component of `z × z' = v × (n f - n' e) + e × f`. -/
theorem cross_decomp_1 (v1 v2 v3 e1 e2 e3 f1 f2 f3 n n' : ℝ) :
    (n * v2 + e2) * (n' * v3 + f3) - (n * v3 + e3) * (n' * v2 + f2) =
      (v2 * (n * f3 - n' * e3) - v3 * (n * f2 - n' * e2)) + (e2 * f3 - e3 * f2) := by
  ring

theorem cross_decomp_2 (v1 v2 v3 e1 e2 e3 f1 f2 f3 n n' : ℝ) :
    (n * v3 + e3) * (n' * v1 + f1) - (n * v1 + e1) * (n' * v3 + f3) =
      (v3 * (n * f1 - n' * e1) - v1 * (n * f3 - n' * e3)) + (e3 * f1 - e1 * f3) := by
  ring

theorem cross_decomp_3 (v1 v2 v3 e1 e2 e3 f1 f2 f3 n n' : ℝ) :
    (n * v1 + e1) * (n' * v2 + f2) - (n * v2 + e2) * (n' * v1 + f1) =
      (v1 * (n * f2 - n' * e2) - v2 * (n * f1 - n' * e1)) + (e1 * f2 - e2 * f1) := by
  ring

/-- The exponent condition of the ray theorem: if `1 < s`, `J > 0`, `(s-1) J < 2`, then
`2 - (s-1) J > 0`.  (The asymptotic contradiction `n^(2-(s-1)J) ≪ polylog` follows from this.) -/
theorem exponent_pos (s J : ℝ) (hJ : 0 < J) (hs : 1 < s) (h : (s - 1) * J < 2) : 0 < 2 - (s - 1) * J := by
  linarith

end TPP
