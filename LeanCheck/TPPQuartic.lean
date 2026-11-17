import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# ThreePrimePlus: the form `h·v` as a quartic in the logarithms

Let `α² = L₂/L₃` and `β² = L₂/L₅`, `v = (1, α, β)`.  The integer quartic
`P_h(L₂,L₃,L₅) = (h₁² L₃L₅ + h₂² L₂L₅ − h₃² L₂L₃)² − 4 h₁²h₂² L₂L₃L₅²`
equals `L₃² L₅²` times the product of `h₁ ± h₂α ± h₃β` over the four sign patterns, and
`|P_h| ≤ 27 m³ L₃² L₅² |h·v|` when `|h_i| ≤ m` and `|α|,|β| ≤ 1`
(Lemma "The form h·v as a quartic in the logarithms" of ThreePrimePlus).
-/

namespace TPP

/-- The quartic form. -/
def quartic (h1 h2 h3 L2 L3 L5 : ℝ) : ℝ :=
  (h1 ^ 2 * L3 * L5 + h2 ^ 2 * L2 * L5 - h3 ^ 2 * L2 * L3) ^ 2 - 4 * h1 ^ 2 * h2 ^ 2 * L2 * L3 * L5 ^ 2

/-- Product formula, with `L₂ = α² L₃` and `α² L₃ = β² L₅`. -/
theorem quartic_eq_prod (h1 h2 h3 α β L3 L5 : ℝ) (hrel : α ^ 2 * L3 = β ^ 2 * L5) :
    quartic h1 h2 h3 (α ^ 2 * L3) L3 L5 =
      L3 ^ 2 * L5 ^ 2 *
        ((h1 + h2 * α + h3 * β) * (h1 + h2 * α - h3 * β) *
          (h1 - h2 * α + h3 * β) * (h1 - h2 * α - h3 * β)) := by
  unfold quartic
  linear_combination
    (-(h3 ^ 2 * L3) *
      ((h1 ^ 2 * L3 * L5 + h2 ^ 2 * (α ^ 2 * L3) * L5 - h3 ^ 2 * (α ^ 2 * L3) * L3) +
        (h1 ^ 2 * L3 * L5 + h2 ^ 2 * α ^ 2 * L3 * L5 - h3 ^ 2 * β ^ 2 * L3 * L5))) * hrel

/-- A relation `h·v = 0` gives `P_h = 0`. -/
theorem quartic_eq_zero_of_dot_zero (h1 h2 h3 α β L3 L5 : ℝ) (hrel : α ^ 2 * L3 = β ^ 2 * L5)
    (h : h1 + h2 * α + h3 * β = 0) : quartic h1 h2 h3 (α ^ 2 * L3) L3 L5 = 0 := by
  rw [quartic_eq_prod h1 h2 h3 α β L3 L5 hrel, h]
  ring

private lemma abs_three_le (m x y z : ℝ) (hx : |x| ≤ m) (hy : |y| ≤ m) (hz : |z| ≤ m)
    (s t : ℝ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    |x + s * y + t * z| ≤ 3 * m := by
  have h1 := abs_le.mp hx
  have h2 := abs_le.mp hy
  have h3 := abs_le.mp hz
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    rw [abs_le] <;> constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- `|P_h| ≤ 27 m³ L₃² L₅² |h·v|`. -/
theorem quartic_bound (h1 h2 h3 α β L3 L5 m : ℝ) (hrel : α ^ 2 * L3 = β ^ 2 * L5)
    (hm1 : |h1| ≤ m) (hm2 : |h2| ≤ m) (hm3 : |h3| ≤ m) (hα : |α| ≤ 1) (hβ : |β| ≤ 1) :
    |quartic h1 h2 h3 (α ^ 2 * L3) L3 L5| ≤ 27 * m ^ 3 * L3 ^ 2 * L5 ^ 2 * |h1 + h2 * α + h3 * β| := by
  have hm0 : 0 ≤ m := le_trans (abs_nonneg _) hm1
  have e2 : |h2 * α| ≤ m := by
    rw [abs_mul]
    calc |h2| * |α| ≤ m * 1 := mul_le_mul hm2 hα (abs_nonneg _) hm0
      _ = m := mul_one m
  have e3 : |h3 * β| ≤ m := by
    rw [abs_mul]
    calc |h3| * |β| ≤ m * 1 := mul_le_mul hm3 hβ (abs_nonneg _) hm0
      _ = m := mul_one m
  have f1 : |h1 + h2 * α - h3 * β| ≤ 3 * m := by
    have := abs_three_le m h1 (h2 * α) (h3 * β) hm1 e2 e3 1 (-1) (Or.inl rfl) (Or.inr rfl)
    simpa [sub_eq_add_neg] using this
  have f2 : |h1 - h2 * α + h3 * β| ≤ 3 * m := by
    have := abs_three_le m h1 (h2 * α) (h3 * β) hm1 e2 e3 (-1) 1 (Or.inr rfl) (Or.inl rfl)
    simpa [sub_eq_add_neg] using this
  have f3 : |h1 - h2 * α - h3 * β| ≤ 3 * m := by
    have := abs_three_le m h1 (h2 * α) (h3 * β) hm1 e2 e3 (-1) (-1) (Or.inr rfl) (Or.inr rfl)
    simpa [sub_eq_add_neg] using this
  rw [quartic_eq_prod h1 h2 h3 α β L3 L5 hrel]
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
  have hL : |L3 ^ 2 * L5 ^ 2| = L3 ^ 2 * L5 ^ 2 := abs_of_nonneg (by positivity)
  have hL' : |L3 ^ 2| * |L5 ^ 2| = L3 ^ 2 * L5 ^ 2 := by
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have g1 := abs_nonneg (h1 + h2 * α + h3 * β)
  have p12 : |h1 + h2 * α - h3 * β| * |h1 - h2 * α + h3 * β| ≤ (3 * m) * (3 * m) :=
    mul_le_mul f1 f2 (abs_nonneg _) (by positivity)
  have p123 : |h1 + h2 * α - h3 * β| * |h1 - h2 * α + h3 * β| * |h1 - h2 * α - h3 * β|
      ≤ (3 * m) * (3 * m) * (3 * m) :=
    mul_le_mul p12 f3 (abs_nonneg _) (by positivity)
  rw [hL']
  have hpos : 0 ≤ L3 ^ 2 * L5 ^ 2 := by positivity
  calc L3 ^ 2 * L5 ^ 2 * (|h1 + h2 * α + h3 * β| * |h1 + h2 * α - h3 * β| * |h1 - h2 * α + h3 * β|
        * |h1 - h2 * α - h3 * β|)
      = L3 ^ 2 * L5 ^ 2 * |h1 + h2 * α + h3 * β| *
        (|h1 + h2 * α - h3 * β| * |h1 - h2 * α + h3 * β| * |h1 - h2 * α - h3 * β|) := by ring
    _ ≤ L3 ^ 2 * L5 ^ 2 * |h1 + h2 * α + h3 * β| * ((3 * m) * (3 * m) * (3 * m)) :=
        mul_le_mul_of_nonneg_left p123 (mul_nonneg hpos g1)
    _ = 27 * m ^ 3 * L3 ^ 2 * L5 ^ 2 * |h1 + h2 * α + h3 * β| := by ring

end TPP
