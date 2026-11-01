import Mathlib

/-!
# Separation profiles

The analysis of the central bound uses the two-term separation only through a *profile* `a(t)`: the separation radius at a close pair of
scale `Q` and `t = sqrt (log Q)` is `Q⁻¹ exp(-a(t))`.  The proofs need two growth properties of `a`:

* `WindowProfile a` (non-deep levels): `a ≥ 0`, `a` monotone on `[0, ∞)`, and for every `c ≥ 0` the inequality
  `(c + a S)^2 + (c + a S) ≤ S^2` for all large `S`;
* `CloseGrowth a` (close levels): `a t + log t ≤ t` for all large `t`.

The original hypothesis `a(t) = A log^2(2+t)` satisfies both (proved in `JANonDeep` and `JAProductFinal`).  Here we prove both properties for the
much weaker profile `a(t) = c t`, `0 ≤ c < 1`, i.e. a separation `Q⁻¹ exp(-c sqrt (log Q))`.
-/

namespace LeanCheck

/-- Properties of a separation profile used for the non-deep levels. -/
structure WindowProfile (a : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ t → 0 ≤ a t
  mono : ∀ s t, 0 ≤ s → s ≤ t → a s ≤ a t
  window : ∀ c : ℝ, 0 ≤ c → ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S → (c + a S) ^ 2 + (c + a S) ≤ S ^ 2

/-- Growth of a separation profile used for the close levels. -/
def CloseGrowth (a : ℝ → ℝ) : Prop := ∃ T : ℝ, ∀ t : ℝ, T ≤ t → 1 ≤ t → a t + Real.log t ≤ t

/-- The linear profile `a(t) = c t`, `0 ≤ c < 1`, is a window profile. -/
theorem windowProfile_weak (c : ℝ) (h0 : 0 ≤ c) (h1 : c < 1) : WindowProfile (fun t => c * t) where
  nonneg := fun t ht => mul_nonneg h0 ht
  mono := fun s t _ hst => mul_le_mul_of_nonneg_left hst h0
  window := by
    intro c₀ hc₀
    have hpos : 0 < 1 - c ^ 2 := by nlinarith
    set K : ℝ := c₀ ^ 2 + c₀ + 2 * c₀ * c + c with hK
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    refine ⟨K / (1 - c ^ 2) + 1, by positivity, ?_⟩
    intro S hS
    have hS1 : 1 ≤ S := by
      have : 0 ≤ K / (1 - c ^ 2) := div_nonneg hK0 hpos.le
      linarith
    have hS0 : 0 ≤ S := by linarith
    have hKS : K ≤ (1 - c ^ 2) * S := by
      have h : K / (1 - c ^ 2) ≤ S := by linarith
      rw [div_le_iff₀ hpos] at h
      linarith
    have h2 := mul_le_mul_of_nonneg_left hKS hS0
    have h3 := mul_nonneg (add_nonneg (sq_nonneg c₀) hc₀) (sub_nonneg.mpr hS1)
    show (c₀ + c * S) ^ 2 + (c₀ + c * S) ≤ S ^ 2
    nlinarith [h2, h3]

/-- The linear profile has `c t + log t ≤ t` for large `t`. -/
theorem closeGrowth_weak (c : ℝ) (h1 : c < 1) : CloseGrowth (fun t => c * t) := by
  have hpos : 0 < 1 - c := by linarith
  refine ⟨4 / (1 - c) ^ 2, ?_⟩
  intro t hT ht1
  have ht0 : 0 < t := by linarith
  set s : ℝ := Real.sqrt t with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht0
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht0.le
  have hlog : Real.log t = 2 * Real.log s := by
    have := Real.log_sqrt ht0.le
    rw [← hs] at this
    linarith
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  have hsge : 2 / (1 - c) ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    have : (2 / (1 - c)) ^ 2 = 4 / (1 - c) ^ 2 := by field_simp; ring
    rw [this]; exact hT
  have h2s : 2 ≤ (1 - c) * s := by
    have := mul_le_mul_of_nonneg_left hsge hpos.le
    have e : (1 - c) * (2 / (1 - c)) = 2 := by field_simp
    linarith
  show c * t + Real.log t ≤ t
  have : t = s * s := by rw [← hs2]; ring
  nlinarith [mul_le_mul_of_nonneg_left h2s hs0.le]

end LeanCheck
