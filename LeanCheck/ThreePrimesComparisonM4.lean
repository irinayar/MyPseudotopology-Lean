import LeanCheck.ThreePrimesComparisonM3

/-!
# ThreePrimes (exploration M4): the sharp comparison under `⌈Δ⌉ ≤ η α`

`y_le_slackM3` is the intermediate bound of `B_le_A_slackM3` (`t*² − η − Δ ≤ L − c − Δ`), and
`B_le_A_ceilM3` applies it with `c = ⌈Δ⌉ − Δ ∈ [0,1)`: if `⌈Δ⌉ ≤ η α` then `D_S(δ) 2^M ≤ 2^L`.
This contains the integer case (`η α` is an integer `≥ Δ`) and the case `η α − Δ ≥ 1`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- Intermediate bound: `t*² − η − Δ ≤ (L − c) − Δ` for `0 ≤ c ≤ 1`, `c ≤ η α − Δ`. -/
theorem y_le_slackM3 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (m : ℕ) (η : ℝ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 1 ≤ η)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsl : c ≤ η * sumAlpha S (fun p => aThr p δ) - sumDelta S (fun p => aThr p δ)) :
    (tstarR S (fun p => aThr p δ) η) ^ 2 - η - sumDelta S (fun p => aThr p δ)
      ≤ (((⌈max 1 ((sumA S) ^ 2) * η ^ 2 + max 1 ((sumA S) ^ 2) * η⌉₊ : ℕ) : ℝ) - c)
        - sumDelta S (fun p => aThr p δ) := by
  have hη0 : 0 ≤ η := by linarith
  set a : ℕ → ℕ := fun p => aThr p δ with ha
  set AA : ℝ := max 1 ((sumA S) ^ 2) with hAA
  set L : ℕ := ⌈AA * η ^ 2 + AA * η⌉₊ with hLdef
  have hAA1 : 1 ≤ AA := le_max_left _ _
  have hAAA : (sumA S) ^ 2 ≤ AA := le_max_right _ _
  have hL : AA * η ^ 2 + AA * η ≤ L := Nat.le_ceil _
  have hlam : ∀ p ∈ S, (a p : ℝ) * Real.logb 2 (p : ℝ) ≤ η :=
    fun p hp => aThr_logb_leM3 (hS p hp) hδ hm hmh hη0
  obtain ⟨hΔα, hΔC⟩ := sumDelta_boundsM3 hS a hlam
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb (hS p hp)
  have hΔ0 : 0 ≤ sumDelta S a := by
    apply Finset.sum_nonneg
    intro p hp
    have := hlb p hp
    positivity
  have hA0 : 0 ≤ sumA S := Finset.sum_nonneg (fun p _ => Real.sqrt_nonneg _)
  have hα0 : 0 ≤ sumAlpha S a := Finset.sum_nonneg (fun p _ => Nat.cast_nonneg _)
  have hQ := discQR_nonneg hS hne a η hη0
  -- Δ ≤ L
  have hΔL : sumDelta S a ≤ L := by
    have h2 : η ^ 2 * (sumA S) ^ 2 ≤ AA * η ^ 2 := by
      calc η ^ 2 * (sumA S) ^ 2 ≤ η ^ 2 * AA := by gcongr
        _ = _ := by ring
    have h3 : 0 ≤ AA * η := by positivity
    linarith
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  -- X = sqrt (L + η - c)
  have hXarg : (0 : ℝ) ≤ (L : ℝ) + η - c := by
    have : 0 ≤ AA * η ^ 2 := by positivity
    have : 0 ≤ AA * η := by positivity
    linarith
  set X : ℝ := Real.sqrt ((L : ℝ) + η - c) with hX
  have hXsq : X ^ 2 = (L : ℝ) + η - c := Real.sq_sqrt hXarg
  have hXnn : 0 ≤ X := Real.sqrt_nonneg _
  -- x0 = sqrt (L + η) ≥ X
  set x0 : ℝ := Real.sqrt ((L : ℝ) + η) with hx0
  have hx0sq : x0 ^ 2 = (L : ℝ) + η := Real.sq_sqrt (by linarith)
  have hx0nn : 0 ≤ x0 := Real.sqrt_nonneg _
  have hXx0 : X ≤ x0 := by
    apply Real.sqrt_le_sqrt
    linarith
  have hkey : AA * η ^ 2 * ((L : ℝ) + η) ≤ (L : ℝ) ^ 2 := tight_ineq hAA1 hη hL
  have hAx0 : η * sumA S * x0 ≤ L := by
    by_contra hcon
    push_neg at hcon
    have hnn : 0 ≤ η * sumA S * x0 := by positivity
    have hsq := mul_self_lt_mul_self hL0 hcon
    have e1 : (η * sumA S * x0) * (η * sumA S * x0) = η ^ 2 * (sumA S) ^ 2 * ((L : ℝ) + η) := by
      rw [← hx0sq]; ring
    have e2 : η ^ 2 * (sumA S) ^ 2 * ((L : ℝ) + η) ≤ AA * η ^ 2 * ((L : ℝ) + η) := by
      have : 0 ≤ η ^ 2 * ((L : ℝ) + η) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hAAA this]
    nlinarith [hsq, e1, e2, hkey]
  have hAX : η * sumA S * X ≤ L := by
    calc η * sumA S * X ≤ η * sumA S * x0 := by
          apply mul_le_mul_of_nonneg_left hXx0 (by positivity)
      _ ≤ L := hAx0
  -- η A ≤ X
  have hXA : η * sumA S ≤ X := by
    have h1 : (η * sumA S) ^ 2 ≤ X ^ 2 := by
      rw [hXsq]
      have h1' : (η * sumA S) ^ 2 ≤ AA * η ^ 2 := by
        calc (η * sumA S) ^ 2 = η ^ 2 * (sumA S) ^ 2 := by ring
          _ ≤ η ^ 2 * AA := by gcongr
          _ = _ := by ring
      have h2 : 0 ≤ AA * η := by positivity
      linarith
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_self_lt_mul_self hXnn hcon]
  have hXpos : 0 < X := by
    have : 0 < X ^ 2 := by
      rw [hXsq]
      have : 1 ≤ AA * η ^ 2 := by nlinarith
      have : 0 ≤ AA * η := by positivity
      linarith
    exact lt_of_le_of_ne hXnn (fun h => by rw [← h] at this; simp at this)
  have hφ : 0 ≤ X ^ 2 - η * sumA S * X + (η * sumAlpha S a - η - sumDelta S a) := by
    rw [hXsq]; linarith [hAX, hsl]
  have htX : tstarR S a η ≤ X := tstar_le_M3 a hQ hXA hXpos hφ
  have ht0 : 0 ≤ tstarR S a η := by
    unfold tstarR
    have := Real.sqrt_nonneg (discQR S a η)
    positivity
  have htsq : (tstarR S a η) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ ht0 htX 2
  have hyE : (tstarR S a η) ^ 2 - η - sumDelta S a ≤ ((L : ℝ) - c) - sumDelta S a := by
    rw [hXsq] at htsq; linarith
  exact hyE

/-- **Sharp comparison under `⌈Δ⌉ ≤ η α`.** -/
theorem B_le_A_ceilM3 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (m : ℕ) (η : ℝ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 1 ≤ η)
    (hce : (⌈sumDelta S (fun p => aThr p δ)⌉₊ : ℝ) ≤ η * sumAlpha S (fun p => aThr p δ)) :
    (Dvis S δ : ℝ) * (2 : ℝ) ^ (MstarR S (fun p => aThr p δ) η)
      ≤ (2 : ℝ) ^ (⌈max 1 ((sumA S) ^ 2) * η ^ 2 + max 1 ((sumA S) ^ 2) * η⌉₊) := by
  have hη0 : 0 ≤ η := by linarith
  set a : ℕ → ℕ := fun p => aThr p δ with ha
  set AA : ℝ := max 1 ((sumA S) ^ 2) with hAA
  set L : ℕ := ⌈AA * η ^ 2 + AA * η⌉₊ with hLdef
  have hAA1 : 1 ≤ AA := le_max_left _ _
  have hAAA : (sumA S) ^ 2 ≤ AA := le_max_right _ _
  have hlam : ∀ p ∈ S, (a p : ℝ) * Real.logb 2 (p : ℝ) ≤ η :=
    fun p hp => aThr_logb_leM3 (hS p hp) hδ hm hmh hη0
  obtain ⟨hΔα, hΔC⟩ := sumDelta_boundsM3 hS a hlam
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb (hS p hp)
  have hΔ0 : 0 ≤ sumDelta S a := by
    apply Finset.sum_nonneg
    intro p hp
    have := hlb p hp
    positivity
  have hA0 : 0 ≤ sumA S := Finset.sum_nonneg (fun p _ => Real.sqrt_nonneg _)
  have hL : AA * η ^ 2 + AA * η ≤ L := Nat.le_ceil _
  have hΔL : sumDelta S a ≤ L := by
    have h2 : η ^ 2 * (sumA S) ^ 2 ≤ AA * η ^ 2 := by
      calc η ^ 2 * (sumA S) ^ 2 ≤ η ^ 2 * AA := by gcongr
        _ = _ := by ring
    have h3 : 0 ≤ AA * η := by positivity
    linarith
  -- c = ⌈Δ⌉ - Δ
  set K : ℕ := ⌈sumDelta S a⌉₊ with hK
  have hKΔ : sumDelta S a ≤ (K : ℝ) := Nat.le_ceil _
  have hKlt : (K : ℝ) < sumDelta S a + 1 := Nat.ceil_lt_add_one hΔ0
  have hKL : K ≤ L := Nat.ceil_le.mpr hΔL
  have hy := y_le_slackM3 hS hne hδ m η hm hmh hη (c := (K : ℝ) - sumDelta S a)
    (by linarith) (by linarith) (by linarith)
  have hyK : (tstarR S a η) ^ 2 - η - sumDelta S a ≤ (((L - K : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hKL]
    linarith
  have hMK : MstarR S a η ≤ L - K := by
    unfold MstarR
    exact Nat.ceil_le.mpr hyK
  have hDvis : (Dvis S δ : ℝ) = (2 : ℝ) ^ (sumDelta S a) := by
    have hDpos' : (0 : ℝ) < (Dvis S δ : ℝ) := by
      have : 0 < Dvis S δ := by
        unfold Dvis
        apply Finset.prod_pos
        intro p hp
        have := hS p hp
        positivity
      exact_mod_cast this
    have h1 := Real.rpow_logb (b := 2) (x := (Dvis S δ : ℝ)) (by norm_num) (by norm_num) hDpos'
    have h2 : Real.logb 2 (Dvis S δ : ℝ) = sumDelta S a := by
      unfold sumDelta
      exact logb_D hS a
    rw [h2] at h1
    exact h1.symm
  calc (Dvis S δ : ℝ) * (2 : ℝ) ^ (MstarR S a η)
      ≤ (Dvis S δ : ℝ) * (2 : ℝ) ^ (L - K) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) hMK
    _ = (2 : ℝ) ^ (sumDelta S a + (((L - K : ℕ) : ℝ))) := by
        rw [hDvis, ← Real.rpow_natCast, Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ ((L : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [Nat.cast_sub hKL]
        linarith
    _ = (2 : ℝ) ^ L := Real.rpow_natCast 2 L

#print axioms y_le_slackM3
#print axioms B_le_A_ceilM3

end TVGPlus
end LeanCheck
