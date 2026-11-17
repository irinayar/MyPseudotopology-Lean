import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# ThreePrimePlus: the first-gap lemma

If `0 < x ≤ y`, `a ≠ 0` is an integer and `|a + b e^{-x} + c e^{-y}| ≤ 1/2`, then
`e^x ≤ 4 max(|b|,|c|)`.  The form is linear in the vector, so a divisor of a near-resonant
vector is near-resonant, and a generator `γ` with `max |γ_j| ≥ e^x/4` gives mass bound
`C |γ|^{-4} ≤ 256 C e^{-4x}`.
-/

namespace TPP

open Real

theorem first_gap (x y : ℝ) (hxy : x ≤ y) (a b c : ℤ) (ha : a ≠ 0)
    (h : |(a : ℝ) + b * exp (-x) + c * exp (-y)| ≤ 1 / 2) :
    exp x ≤ 4 * max |(b : ℝ)| |(c : ℝ)| := by
  have ha1 : (1 : ℝ) ≤ |(a : ℝ)| := by
    have : (1 : ℤ) ≤ |a| := Int.one_le_abs ha
    exact_mod_cast this
  have hey : exp (-y) ≤ exp (-x) := Real.exp_le_exp.mpr (by linarith)
  have hex : 0 < exp (-x) := Real.exp_pos _
  have hey0 : 0 < exp (-y) := Real.exp_pos _
  set M := max |(b : ℝ)| |(c : ℝ)| with hM
  have hb : |(b : ℝ)| ≤ M := le_max_left _ _
  have hc : |(c : ℝ)| ≤ M := le_max_right _ _
  -- |a| - |b e^{-x} + c e^{-y}| ≤ |a + ...| ≤ 1/2
  set z : ℝ := (b : ℝ) * exp (-x) + c * exp (-y) with hz
  have h1 : |(a : ℝ)| - |z| ≤ |(a : ℝ) + b * exp (-x) + c * exp (-y)| := by
    have e : (a : ℝ) = ((a : ℝ) + b * exp (-x) + c * exp (-y)) + (-z) := by rw [hz]; ring
    have h3 : |(a : ℝ)| ≤ |(a : ℝ) + b * exp (-x) + c * exp (-y)| + |z| := by
      calc |(a : ℝ)| = |((a : ℝ) + b * exp (-x) + c * exp (-y)) + (-z)| := by rw [← e]
        _ ≤ |(a : ℝ) + b * exp (-x) + c * exp (-y)| + |-z| := abs_add_le _ _
        _ = |(a : ℝ) + b * exp (-x) + c * exp (-y)| + |z| := by rw [abs_neg]
    linarith
  have h2 : |z| ≤ |(b : ℝ)| * exp (-x) + |(c : ℝ)| * exp (-y) := by
    calc |z| ≤ |(b : ℝ) * exp (-x)| + |(c : ℝ) * exp (-y)| := abs_add_le _ _
      _ = |(b : ℝ)| * exp (-x) + |(c : ℝ)| * exp (-y) := by
          rw [abs_mul, abs_mul, abs_of_pos hex, abs_of_pos hey0]
  have h3 : |(b : ℝ)| * exp (-x) + |(c : ℝ)| * exp (-y) ≤ 2 * M * exp (-x) := by
    have e1 : |(b : ℝ)| * exp (-x) ≤ M * exp (-x) := mul_le_mul_of_nonneg_right hb hex.le
    have e2 : |(c : ℝ)| * exp (-y) ≤ M * exp (-x) :=
      mul_le_mul hc hey hey0.le (le_trans (abs_nonneg _) hb)
    linarith
  have h4 : (1 : ℝ) / 2 ≤ 2 * M * exp (-x) := by linarith
  have h5 : exp x * exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hxpos : 0 < exp x := Real.exp_pos _
  have h6 : exp x * (1 / 2) ≤ exp x * (2 * M * exp (-x)) := mul_le_mul_of_nonneg_left h4 hxpos.le
  have h7 : exp x * (2 * M * exp (-x)) = 2 * M := by
    calc exp x * (2 * M * exp (-x)) = 2 * M * (exp x * exp (-x)) := by ring
      _ = 2 * M := by rw [h5, mul_one]
  linarith

/-- The form `a + b ρ₂ + c ρ₃` is linear: a divisor of a near-resonant vector is near-resonant. -/
theorem divisor_near_resonant (ρ2 ρ3 ε : ℝ) (k : ℕ) (hk : 1 ≤ k) (a b c : ℤ)
    (h : |(k : ℝ) * a + (k : ℝ) * b * ρ2 + (k : ℝ) * c * ρ3| < ε) :
    |(a : ℝ) + b * ρ2 + c * ρ3| < ε := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have e : (k : ℝ) * a + (k : ℝ) * b * ρ2 + (k : ℝ) * c * ρ3 = (k : ℝ) * ((a : ℝ) + b * ρ2 + c * ρ3) := by ring
  rw [e, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < k)] at h
  have : |(a : ℝ) + b * ρ2 + c * ρ3| ≤ (k : ℝ) * |(a : ℝ) + b * ρ2 + c * ρ3| := by
    nlinarith [abs_nonneg ((a : ℝ) + b * ρ2 + c * ρ3)]
  linarith

/-- Mass bound from the size of the generator: `W ≥ e^x/4` gives `C W^{-4} ≤ 256 C e^{-4x}`. -/
theorem mass_le (C W x : ℝ) (hC : 0 ≤ C) (hW : exp x ≤ 4 * W) :
    C * (W ^ 4)⁻¹ ≤ 256 * C * exp (-(4 * x)) := by
  have hx : 0 < exp x := Real.exp_pos _
  have hW0 : 0 < W := by linarith
  have h4 : (exp x) ^ 4 ≤ (4 * W) ^ 4 := by
    exact pow_le_pow_left₀ hx.le hW 4
  have h5 : exp (-(4 * x)) = ((exp x) ^ 4)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]
    norm_num
  have h6 : (W ^ 4)⁻¹ ≤ 256 * ((exp x) ^ 4)⁻¹ := by
    have hp : 0 < (exp x) ^ 4 := by positivity
    have hq : 0 < W ^ 4 := by positivity
    rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, div_le_div_iff₀ hq hp]
    nlinarith [h4]
  calc C * (W ^ 4)⁻¹ ≤ C * (256 * ((exp x) ^ 4)⁻¹) := mul_le_mul_of_nonneg_left h6 hC
    _ = 256 * C * exp (-(4 * x)) := by rw [h5]; ring

end TPP
