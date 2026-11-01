import LeanCheck.TVGPlusOrderB

/-!
# TVGplus: the constants `A_S`, `x_S` and the positivity of `f(B) = B - A_S sqrt B + c_S`

`A_S = ∑ 1/sqrt (log p)`, `x_S = ((A_S + sqrt (A_S² - 4 c_S))/2)²` as in `TVGplus`, Theorem "The logarithmic order".
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- `A_S = ∑ 1 / sqrt (log p)`. -/
noncomputable def aS (S : Finset ℕ) : ℝ := ∑ p ∈ S, 1 / Real.sqrt (Real.log p)

/-- `y_+ = (A_S + sqrt (A_S² - 4 c_S)) / 2` and `x_S = y_+²`. -/
noncomputable def yPlus (S : Finset ℕ) : ℝ := (aS S + Real.sqrt (aS S ^ 2 - 4 * cS S)) / 2

noncomputable def xS (S : Finset ℕ) : ℝ := yPlus S ^ 2

lemma aS_nonneg (S : Finset ℕ) : 0 ≤ aS S :=
  Finset.sum_nonneg (fun p _ => by positivity)

lemma four_cS_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    4 * cS S = ∑ p ∈ S, (1 / Real.sqrt (Real.log p)) ^ 2 := by
  unfold cS
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hl := log_pos_of_prime (hS p hp)
  rw [div_pow, Real.sq_sqrt hl.le]
  field_simp

lemma disc_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : 4 * cS S ≤ aS S ^ 2 := by
  rw [four_cS_eq S hS]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun p _ => by positivity)

lemma cS_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : 0 ≤ cS S :=
  Finset.sum_nonneg (fun p hp => by have := log_pos_of_prime (hS p hp); positivity)

lemma yPlus_ge_half (S : Finset ℕ) : aS S / 2 ≤ yPlus S := by
  unfold yPlus
  have := Real.sqrt_nonneg (aS S ^ 2 - 4 * cS S)
  linarith

lemma cS_le_xS (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : cS S ≤ xS S := by
  unfold xS yPlus
  have hd := disc_nonneg S hS
  have hc := cS_nonneg S hS
  set R := Real.sqrt (aS S ^ 2 - 4 * cS S) with hR
  have hR2 : R ^ 2 = aS S ^ 2 - 4 * cS S := Real.sq_sqrt (by linarith)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hA := aS_nonneg S
  nlinarith [mul_nonneg hA hR0, mul_nonneg hR0 hR0]

/-- For `B > x_S`: `f(B) = B - A_S sqrt B + c_S > 0`. -/
lemma f_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {B : ℝ} (hB : xS S < B) :
    0 < B - aS S * Real.sqrt B + cS S := by
  have hd := disc_nonneg S hS
  set R := Real.sqrt (aS S ^ 2 - 4 * cS S) with hR
  have hR2 : R ^ 2 = aS S ^ 2 - 4 * cS S := Real.sq_sqrt (by linarith)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hA := aS_nonneg S
  have hy0 : 0 ≤ yPlus S := by unfold yPlus; rw [← hR]; positivity
  have hβ : yPlus S < Real.sqrt B := by
    rw [Real.lt_sqrt hy0]
    exact hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ xS S := by unfold xS; positivity
    linarith
  have hβ2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
  set β := Real.sqrt B with hβdef
  have h1 : 0 < β - (aS S + R) / 2 := by
    have : yPlus S = (aS S + R) / 2 := by unfold yPlus; rw [hR]
    linarith
  have h2 : 0 < β - (aS S - R) / 2 := by linarith
  have h3 := mul_pos h1 h2
  nlinarith

/-- For `B > x_S`, `sqrt B ≥ 1 / (2 sqrt (log p))` for every `p ∈ S` (nonnegativity of the leading coefficient). -/
lemma sqrt_ge_half (S : Finset ℕ) {B : ℝ} (hB : xS S < B) {p : ℕ} (hp : p ∈ S) :
    1 / Real.sqrt (Real.log p) / 2 ≤ Real.sqrt B := by
  have h1 : 1 / Real.sqrt (Real.log p) ≤ aS S :=
    Finset.single_le_sum (f := fun q : ℕ => 1 / Real.sqrt (Real.log (q : ℝ)))
      (fun q _ => by positivity) hp
  have h2 := yPlus_ge_half S
  have hy0 : 0 ≤ yPlus S := le_trans (by have := aS_nonneg S; linarith) h2
  have hβ : yPlus S < Real.sqrt B := by
    rw [Real.lt_sqrt hy0]; exact hB
  linarith

#print axioms f_pos
#print axioms sqrt_ge_half
#print axioms cS_le_xS

end TVGPlus
end LeanCheck
