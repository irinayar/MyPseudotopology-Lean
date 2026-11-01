import LeanCheck.TVGPlusOrderC

/-!
# TVGplus: the number of retained coordinates

`count_bound`: for `B > x_S`, `L = log (1/δ) ≥ 0`, `Y ≤ (sqrt B · L + K)²` with `K = 1 + 1/(2 sqrt B)`, the number
`∑_p (⌊sqrt (Y / log p)⌋ - a_p(δ))₊` of retained coordinates is at most `(A_S sqrt B - 2 c_S) L + (A_S K + |S|/2)`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- The constant `K = 1 + 1/(2 sqrt B)`. -/
noncomputable def Kc (B : ℝ) : ℝ := 1 + 1 / (2 * Real.sqrt B)

lemma count_term {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) {B : ℝ} (hβ0 : 0 < Real.sqrt B)
    (hβ : 1 / Real.sqrt (Real.log p) / 2 ≤ Real.sqrt B) {Y : ℝ}
    (hY : Y ≤ (Real.sqrt B * Real.log (1 / δ) + Kc B) ^ 2) (hL : 0 ≤ Real.log (1 / δ)) :
    (((⌊Real.sqrt (Y / Real.log p)⌋₊ - aThr p δ : ℕ)) : ℝ) ≤
      Real.sqrt B * (1 / Real.sqrt (Real.log p)) * Real.log (1 / δ)
        - 2 * (1 / (4 * Real.log p)) * Real.log (1 / δ)
        + Kc B * (1 / Real.sqrt (Real.log p)) + 1 / 2 := by
  have hl := log_pos_of_prime hp
  set L := Real.log (1 / δ) with hLdef
  set ℓ := Real.log p with hℓ
  set u := 1 / Real.sqrt ℓ with hu
  have hsq : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hl
  have hu0 : 0 < u := by positivity
  have hu2 : u ^ 2 = 1 / ℓ := by rw [hu, div_pow, Real.sq_sqrt hl.le]; simp
  have hK0 : 0 < Kc B := by unfold Kc; positivity
  have hcoef : 0 ≤ Real.sqrt B * u - 2 * (1 / (4 * ℓ)) := by
    have : 1 / (4 * ℓ) = u ^ 2 / 4 := by rw [hu2]; field_simp
    rw [this]
    nlinarith
  have hrhs : 0 ≤ Real.sqrt B * u * L - 2 * (1 / (4 * ℓ)) * L + Kc B * u + 1 / 2 := by
    have : 0 ≤ (Real.sqrt B * u - 2 * (1 / (4 * ℓ))) * L := mul_nonneg hcoef hL
    nlinarith [mul_pos hK0 hu0]
  by_cases hcase : ⌊Real.sqrt (Y / ℓ)⌋₊ ≤ aThr p δ
  · rw [Nat.sub_eq_zero_of_le hcase]
    simpa using hrhs
  · push Not at hcase
    rw [Nat.cast_sub hcase.le]
    have h1 : (⌊Real.sqrt (Y / ℓ)⌋₊ : ℝ) ≤ Real.sqrt (Y / ℓ) := Nat.floor_le (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (Y / ℓ) ≤ u * (Real.sqrt B * L + Kc B) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      calc Y / ℓ ≤ (Real.sqrt B * L + Kc B) ^ 2 / ℓ := div_le_div_of_nonneg_right hY hl.le
        _ = (u * (Real.sqrt B * L + Kc B)) ^ 2 := by rw [mul_pow, hu2]; field_simp
    have h3 : (L / ℓ - 1) / 2 ≤ aThr p δ := aThr_ge hp hδ
    have h4 : L / ℓ = u ^ 2 * L := by rw [hu2]; field_simp
    have h5 : 1 / (4 * ℓ) = u ^ 2 / 4 := by rw [hu2]; field_simp
    rw [h4] at h3
    rw [h5]
    nlinarith

theorem count_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {δ : ℝ} (hδ : 0 < δ) {B : ℝ} (hB : xS S < B)
    {Y : ℝ} (hL : 0 ≤ Real.log (1 / δ))
    (hY : Y ≤ (Real.sqrt B * Real.log (1 / δ) + Kc B) ^ 2) :
    (((∑ p ∈ S, (⌊Real.sqrt (Y / Real.log p)⌋₊ - aThr p δ) : ℕ)) : ℝ) ≤
      (aS S * Real.sqrt B - 2 * cS S) * Real.log (1 / δ) + (aS S * Kc B + S.card / 2) := by
  have hB0 : 0 < B := lt_of_le_of_lt (by unfold xS; positivity) hB
  have hβ0 : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB0
  push_cast
  calc ∑ p ∈ S, (((⌊Real.sqrt (Y / Real.log p)⌋₊ - aThr p δ : ℕ)) : ℝ)
      ≤ ∑ p ∈ S, (Real.sqrt B * (1 / Real.sqrt (Real.log p)) * Real.log (1 / δ)
        - 2 * (1 / (4 * Real.log p)) * Real.log (1 / δ)
        + Kc B * (1 / Real.sqrt (Real.log p)) + 1 / 2) := by
        apply Finset.sum_le_sum
        intro p hp
        exact count_term (hS p hp) hδ hβ0 (sqrt_ge_half S hB hp) hY hL
    _ = (aS S * Real.sqrt B - 2 * cS S) * Real.log (1 / δ) + (aS S * Kc B + S.card / 2) := by
        have e1 : ∑ p ∈ S, Real.sqrt B * (1 / Real.sqrt (Real.log p)) * Real.log (1 / δ)
            = Real.sqrt B * Real.log (1 / δ) * aS S := by
          unfold aS; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intros; ring
        have e2 : ∑ p ∈ S, 2 * (1 / (4 * Real.log p)) * Real.log (1 / δ)
            = 2 * Real.log (1 / δ) * cS S := by
          unfold cS; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intros; ring
        have e3 : ∑ p ∈ S, Kc B * (1 / Real.sqrt (Real.log p)) = Kc B * aS S := by
          unfold aS; rw [Finset.mul_sum]
        have e4 : ∑ p ∈ S, (1 / 2 : ℝ) = S.card / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, e1, e2, e3, e4]
        ring

#print axioms count_term
#print axioms count_bound

end TVGPlus
end LeanCheck
