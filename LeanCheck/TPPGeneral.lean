import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# ThreePrimeContinue: elementary steps for any three primes

* `near_of_sq_diff`, `sq_diff_of_near`: the difference-of-squares step that turns a bounded difference `|m² L₂ − n² L₁| ≤ D`
  of quadratic quantities into the linear closeness `|m − α n| ≤ D / (L₂ α n)` (with `α² L₂ = L₁`), and conversely
  `|m − α n| ≤ ε` gives `|m² L₂ − n² L₁| ≤ L₂ ε (2 α n + ε)` (Theorem "exact form of the hypothesis", proof of `(H2) ⇔ (S)`).
* `Qh`, `Qh_eq_prod`, `Qh_eq_zero_iff`: the quartic `Q_h(x,y,z) = (h₀² y z − h₁² x z − h₂² x y)² − 4 h₁² h₂² x² y z` equals
  `y² z²` times the product of the four numbers `h₀ ± h₁ α ± h₂ β` when `x = α² y = β² z`, and vanishes iff one of them vanishes.
* `sadic_reform`, `N_eq`: the reformulation of the near-resonance `a + b Q₁/Q₂ + c Q₁/Q₃ = N/(Q₂ Q₃)`, `N = (a Q₂ + b Q₁) Q₃ + c Q₁ Q₂`.
* `N_ne_zero`: `N ≠ 0` when `Q₁ = p^e` with `|a| < p^e`, `a ≠ 0`, and `p ∤ Q₂ Q₃` (the valuation argument for the nonvanishing of the linear form).
* `box_cond`: the counting condition `3 M Z + 1 < (M+1)³` of the pigeonhole lemma holds when `3 Z ≤ M²`.
-/

namespace TPP

/-- Difference of squares: `m² L₂ − n² L₁ = L₂ (m − α n)(m + α n)` when `α² L₂ = L₁`. -/
theorem sq_diff_factor (m n α L1 L2 : ℝ) (h : α ^ 2 * L2 = L1) :
    m ^ 2 * L2 - n ^ 2 * L1 = L2 * (m - α * n) * (m + α * n) := by
  rw [← h]; ring

/-- A bounded quadratic difference gives linear closeness: `|m − α n| (L₂ α n) ≤ D`. -/
theorem near_of_sq_diff (m n α L1 L2 D : ℝ) (hL2 : 0 < L2) (hα : 0 < α) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (h : α ^ 2 * L2 = L1) (hD : |m ^ 2 * L2 - n ^ 2 * L1| ≤ D) :
    |m - α * n| * (L2 * α * n) ≤ D := by
  have e := sq_diff_factor m n α L1 L2 h
  have hpos : 0 ≤ m + α * n := by positivity
  have h1 : |m ^ 2 * L2 - n ^ 2 * L1| = L2 * |m - α * n| * (m + α * n) := by
    rw [e, abs_mul, abs_mul, abs_of_pos hL2, abs_of_nonneg hpos]
  have h2 : L2 * α * n ≤ L2 * (m + α * n) := by nlinarith [mul_nonneg hL2.le hm]
  calc |m - α * n| * (L2 * α * n) ≤ |m - α * n| * (L2 * (m + α * n)) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |m ^ 2 * L2 - n ^ 2 * L1| := by rw [h1]; ring
    _ ≤ D := hD

/-- Conversely, linear closeness gives a bounded quadratic difference. -/
theorem sq_diff_of_near (m n α L1 L2 ε : ℝ) (hL2 : 0 < L2) (hα : 0 < α) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (h : α ^ 2 * L2 = L1) (hε : |m - α * n| ≤ ε) :
    |m ^ 2 * L2 - n ^ 2 * L1| ≤ L2 * ε * (2 * α * n + ε) := by
  have e := sq_diff_factor m n α L1 L2 h
  have hpos : 0 ≤ m + α * n := by positivity
  have hle : m + α * n ≤ 2 * α * n + ε := by
    have := (abs_le.mp hε).2
    linarith
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hε
  have key : |m - α * n| * (m + α * n) ≤ ε * (2 * α * n + ε) :=
    mul_le_mul hε hle hpos hε0
  rw [e, abs_mul, abs_mul, abs_of_pos hL2, abs_of_nonneg hpos]
  calc L2 * |m - α * n| * (m + α * n) = L2 * (|m - α * n| * (m + α * n)) := by ring
    _ ≤ L2 * (ε * (2 * α * n + ε)) := mul_le_mul_of_nonneg_left key hL2.le
    _ = L2 * ε * (2 * α * n + ε) := by ring

/-- The quartic form `Q_h(x,y,z)`. -/
def Qh (h0 h1 h2 x y z : ℝ) : ℝ :=
  (h0 ^ 2 * y * z - h1 ^ 2 * x * z - h2 ^ 2 * x * y) ^ 2 - 4 * h1 ^ 2 * h2 ^ 2 * x ^ 2 * y * z

/-- Product formula: for `x = α² y = β² z`, `Q_h(x,y,z) = y² z² ∏ (h₀ ± h₁ α ± h₂ β)`. -/
theorem Qh_eq_prod (h0 h1 h2 α β x y z : ℝ) (hx : x = α ^ 2 * y) (hz : x = β ^ 2 * z) :
    Qh h0 h1 h2 x y z =
      y ^ 2 * z ^ 2 * ((h0 + h1 * α + h2 * β) * (h0 + h1 * α - h2 * β) *
        (h0 - h1 * α + h2 * β) * (h0 - h1 * α - h2 * β)) := by
  have a1 : x * z = α ^ 2 * y * z := by rw [hx]
  have a2 : x * y = β ^ 2 * z * y := by rw [hz]
  have hA : h0 ^ 2 * y * z - h1 ^ 2 * x * z - h2 ^ 2 * x * y
      = y * z * (h0 ^ 2 - h1 ^ 2 * α ^ 2 - h2 ^ 2 * β ^ 2) := by
    linear_combination (-h1 ^ 2) * a1 + (-h2 ^ 2) * a2
  have a3 : x ^ 2 = α ^ 2 * y * (β ^ 2 * z) := by
    rw [sq, ← hx, ← hz]
  unfold Qh
  rw [hA, a3]
  ring

/-- `Q_h = 0` iff one of the four numbers `h₀ ± h₁ α ± h₂ β` vanishes (a linear dependence of `1, α, β` over `ℤ`). -/
theorem Qh_eq_zero_iff (h0 h1 h2 α β x y z : ℝ) (hx : x = α ^ 2 * y) (hz : x = β ^ 2 * z)
    (hy : y ≠ 0) (hz0 : z ≠ 0) :
    Qh h0 h1 h2 x y z = 0 ↔
      (h0 + h1 * α + h2 * β = 0 ∨ h0 + h1 * α - h2 * β = 0 ∨
       h0 - h1 * α + h2 * β = 0 ∨ h0 - h1 * α - h2 * β = 0) := by
  rw [Qh_eq_prod h0 h1 h2 α β x y z hx hz]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1' | h2'
    · exact absurd h1' (mul_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hz0))
    · rcases mul_eq_zero.mp h2' with h3 | h4
      · rcases mul_eq_zero.mp h3 with h5 | h6
        · rcases mul_eq_zero.mp h5 with h7 | h8
          · exact Or.inl h7
          · exact Or.inr (Or.inl h8)
        · exact Or.inr (Or.inr (Or.inl h6))
      · exact Or.inr (Or.inr (Or.inr h4))
  · rintro (h | h | h | h) <;> simp [h]

/-- Reformulation of the near-resonance: `a + b Q₁/Q₂ + c Q₁/Q₃ = N/(Q₂ Q₃)`. -/
theorem sadic_reform (a b c Q1 Q2 Q3 : ℝ) (h2 : Q2 ≠ 0) (h3 : Q3 ≠ 0) :
    (a * Q2 * Q3 + b * Q1 * Q3 + c * Q1 * Q2) / (Q2 * Q3) = a + b * (Q1 / Q2) + c * (Q1 / Q3) := by
  field_simp

/-- `N = (a Q₂ + b Q₁) Q₃ + c Q₁ Q₂`. -/
theorem N_eq (a b c Q1 Q2 Q3 : ℝ) :
    a * Q2 * Q3 + b * Q1 * Q3 + c * Q1 * Q2 = (a * Q2 + b * Q1) * Q3 + c * Q1 * Q2 := by ring

/-- Nonvanishing of `N` for `Q₁ = p^e` with `0 < |a| < p^e` and `p ∤ Q₂ Q₃`. -/
theorem N_ne_zero (p : ℕ) (hp : p.Prime) (e : ℕ) (a b c Q2 Q3 : ℤ) (ha : a ≠ 0)
    (hlt : |a| < (p : ℤ) ^ e) (hcop : ¬ (p : ℤ) ∣ Q2 * Q3) :
    a * Q2 * Q3 + b * (p : ℤ) ^ e * Q3 + c * (p : ℤ) ^ e * Q2 ≠ 0 := by
  intro h
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd : (p : ℤ) ^ e ∣ a * (Q2 * Q3) := by
    refine ⟨-(b * Q3 + c * Q2), ?_⟩
    linear_combination h
  have h2 : (p : ℤ) ^ e ∣ a := hpr.pow_dvd_of_dvd_mul_right e hcop hdvd
  have h3 : (p : ℤ) ^ e ≤ |a| := Int.le_of_dvd (abs_pos.mpr ha) ((dvd_abs _ _).mpr h2)
  linarith

/-- The counting condition of the pigeonhole lemma. -/
theorem box_cond (Z M : ℕ) (h : 3 * Z ≤ M ^ 2) (hM : 1 ≤ M) : 3 * M * Z + 1 < (M + 1) ^ 3 := by
  have h1 : 3 * M * Z ≤ M ^ 3 := by
    calc 3 * M * Z = M * (3 * Z) := by ring
      _ ≤ M * M ^ 2 := Nat.mul_le_mul_left M h
      _ = M ^ 3 := by ring
  have h2 : (M + 1) ^ 3 = M ^ 3 + 3 * M ^ 2 + 3 * M + 1 := by ring
  rw [h2]
  nlinarith [h1, hM]

end TPP
