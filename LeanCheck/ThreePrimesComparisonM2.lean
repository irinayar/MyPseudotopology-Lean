import LeanCheck.ThreePrimesComparison

/-!
# ThreePrimes (version M2): Theorem B is never weaker than Theorem A, with `m δ ≥ 1`

`B_le_AM2`: with the forced exponents `a_p = aThr p δ`, `m δ ≥ 1`, `m ≤ 2^h`, `1 ≤ h`, one has
`D_S(δ) 2^M ≤ 2^L` (`M = Mstar S a h`, `L = ⌈a_S h² + a_S h⌉`, `a_S = max 1 (g_S²)`).
Shorter than the proof for `m δ ≥ 2` (`ThreePrimesComparison`): minimality of `a_p` gives
`a_p log₂ p ≤ h`, hence `Δ ≤ h α` (an integer `h α ≥ Δ`, so `h α ≥ ⌈Δ⌉`) and `Δ ≤ h² A²`;
then `M ≤ L - h α ≤ ⌊L - Δ⌋`. The lemma `sumDelta_bounds` of `ThreePrimesComparison` is reused with `h + 1`.
-/
namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- For the forced exponent, `a_p(δ) log₂ p ≤ h` (when `1 ≤ m δ`, `m ≤ 2^h`). -/
lemma aThr_logb_leM2 {p : ℕ} (hp : 2 ≤ p) {δ : ℝ} (hδ : 0 < δ) {m h : ℕ}
    (hm : 1 ≤ (m : ℝ) * δ) (hmh : m ≤ 2 ^ h) :
    (aThr p δ : ℝ) * Real.logb 2 (p : ℝ) ≤ (h : ℝ) := by
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  rcases Nat.eq_zero_or_pos (aThr p δ) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, zero_mul]
    exact hh0
  · have hlt : aThr p δ - 1 < aThr p δ := by omega
    have hmin := aThr_min hlt
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hP : (0 : ℝ) < (p : ℝ) ^ (2 * (aThr p δ - 1) + 1) := by positivity
    have e : 2 * (aThr p δ - 1) + 1 = 2 * aThr p δ - 1 := by omega
    rw [e] at hmin hP
    have hmR : (m : ℝ) ≤ 2 ^ h := by exact_mod_cast hmh
    have h2 : (1 : ℝ) ≤ 2 ^ h * δ := by
      calc (1 : ℝ) ≤ m * δ := hm
        _ ≤ 2 ^ h * δ := by gcongr
    have h3 : (1 : ℝ) ≤ 2 ^ h * (1 / (p : ℝ) ^ (2 * aThr p δ - 1)) := by
      calc (1 : ℝ) ≤ 2 ^ h * δ := h2
        _ ≤ _ := by gcongr
    have h4 : (p : ℝ) ^ (2 * aThr p δ - 1) ≤ 2 ^ h := by
      have := h3
      rw [mul_one_div, le_div_iff₀ hP] at this
      linarith
    have h5 : Real.logb 2 ((p : ℝ) ^ (2 * aThr p δ - 1)) ≤ Real.logb 2 ((2 : ℝ) ^ h) :=
      Real.logb_le_logb_of_le (by norm_num) hP h4
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h5
    have hc : ((2 * aThr p δ - 1 : ℕ) : ℝ) = 2 * (aThr p δ : ℝ) - 1 := by
      have : 1 ≤ 2 * aThr p δ := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hc] at h5
    have hl := one_le_logb hp
    have ha1 : (1 : ℝ) ≤ aThr p δ := by exact_mod_cast hpos
    have hl0 : (0 : ℝ) ≤ Real.logb 2 (p : ℝ) := by linarith
    have hprod : 0 ≤ ((aThr p δ : ℝ) - 1) * Real.logb 2 (p : ℝ) :=
      mul_nonneg (by linarith) hl0
    nlinarith [h5, hprod]

/-- Sum bounds for `a_p log₂ p ≤ h`: `Δ ≤ h α` and `Δ ≤ h² A²` (from `sumDelta_bounds` with `h + 1`). -/
lemma sumDelta_boundsM2 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) {h : ℕ}
    (hlam : ∀ p ∈ S, (a p : ℝ) * Real.logb 2 (p : ℝ) ≤ (h : ℝ)) :
    sumDelta S a ≤ (h : ℝ) * sumAlpha S a ∧ sumDelta S a ≤ (h : ℝ) ^ 2 * (sumA S) ^ 2 := by
  have := sumDelta_bounds hS a (h := h + 1) (by omega)
    (fun p hp => by have := hlam p hp; push_cast; linarith)
  simpa using this

/-- **Theorem B is never worse than Theorem A** (forced exponents):
`D_S(δ) 2^M ≤ 2^L` with `L = ⌈a_S h² + a_S h⌉`, `a_S = max 1 (A²)`. -/
theorem B_le_AM2 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (m h : ℕ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : m ≤ 2 ^ h) (hh : 1 ≤ h) :
    (Dvis S δ : ℝ) * (2 : ℝ) ^ (Mstar S (fun p => aThr p δ) h)
      ≤ (2 : ℝ) ^ ⌈max 1 ((sumA S) ^ 2) * (h : ℝ) ^ 2 + max 1 ((sumA S) ^ 2) * h⌉₊ := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  set a : ℕ → ℕ := fun p => aThr p δ with ha
  set AA : ℝ := max 1 ((sumA S) ^ 2) with hAA
  set L : ℕ := ⌈AA * (h : ℝ) ^ 2 + AA * h⌉₊ with hLdef
  have hAA1 : 1 ≤ AA := le_max_left _ _
  have hAAA : (sumA S) ^ 2 ≤ AA := le_max_right _ _
  have hL : AA * (h : ℝ) ^ 2 + AA * h ≤ L := Nat.le_ceil _
  have hlam : ∀ p ∈ S, (a p : ℝ) * Real.logb 2 (p : ℝ) ≤ (h : ℝ) :=
    fun p hp => aThr_logb_leM2 (hS p hp) hδ hm hmh
  obtain ⟨hΔα, hΔC⟩ := sumDelta_boundsM2 hS a hlam
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb (hS p hp)
  have hΔ0 : 0 ≤ sumDelta S a := by
    apply Finset.sum_nonneg
    intro p hp
    have := hlb p hp
    positivity
  have hA0 : 0 ≤ sumA S := Finset.sum_nonneg (fun p _ => Real.sqrt_nonneg _)
  have hα0 : 0 ≤ sumAlpha S a := Finset.sum_nonneg (fun p _ => Nat.cast_nonneg _)
  have hQ := discQ_nonneg hS hne a h
  -- Δ ≤ L
  have hΔL : sumDelta S a ≤ L := by
    have h2 : (h : ℝ) ^ 2 * (sumA S) ^ 2 ≤ AA * (h : ℝ) ^ 2 := by
      calc (h : ℝ) ^ 2 * (sumA S) ^ 2 ≤ (h : ℝ) ^ 2 * AA := by gcongr
        _ = _ := by ring
    have h3 : 0 ≤ AA * (h : ℝ) := by positivity
    linarith
  -- x0 = sqrt (L + h)
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  set x0 : ℝ := Real.sqrt ((L : ℝ) + h) with hx0
  have hx0sq : x0 ^ 2 = (L : ℝ) + h := Real.sq_sqrt (by linarith)
  have hx0nn : 0 ≤ x0 := Real.sqrt_nonneg _
  -- h A x0 ≤ L
  have hkey : AA * (h : ℝ) ^ 2 * ((L : ℝ) + h) ≤ (L : ℝ) ^ 2 := tight_ineq hAA1 hh1 hL
  have hAx0 : (h : ℝ) * sumA S * x0 ≤ L := by
    by_contra hcon
    push_neg at hcon
    have hnn : 0 ≤ (h : ℝ) * sumA S * x0 := by positivity
    have hsq := mul_self_lt_mul_self hL0 hcon
    have e1 : ((h : ℝ) * sumA S * x0) * ((h : ℝ) * sumA S * x0)
        = (h : ℝ) ^ 2 * (sumA S) ^ 2 * ((L : ℝ) + h) := by
      rw [← hx0sq]; ring
    have e2 : (h : ℝ) ^ 2 * (sumA S) ^ 2 * ((L : ℝ) + h) ≤ AA * (h : ℝ) ^ 2 * ((L : ℝ) + h) := by
      have : 0 ≤ (h : ℝ) ^ 2 * ((L : ℝ) + h) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hAAA this]
    nlinarith [hsq, e1, e2, hkey]
  -- x0 ≥ h A
  have hx0hA : (h : ℝ) * sumA S ≤ x0 := by
    have : ((h : ℝ) * sumA S) ^ 2 ≤ x0 ^ 2 := by
      rw [hx0sq]
      have h1 : ((h : ℝ) * sumA S) ^ 2 ≤ AA * (h : ℝ) ^ 2 := by
        calc ((h : ℝ) * sumA S) ^ 2 = (h : ℝ) ^ 2 * (sumA S) ^ 2 := by ring
          _ ≤ (h : ℝ) ^ 2 * AA := by gcongr
          _ = _ := by ring
      have h2 : 0 ≤ AA * (h : ℝ) := by positivity
      linarith
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_self_lt_mul_self hx0nn hcon]
  have hxpos : 0 < x0 := Real.sqrt_pos.mpr (by linarith)
  have hs0 : 0 ≤ Real.sqrt (discQ S a h) := Real.sqrt_nonneg _
  set s : ℝ := Real.sqrt (discQ S a h) with hs
  have hs2 : s ^ 2 = (h : ℝ) ^ 2 * (sumA S) ^ 2
      - 4 * ((h : ℝ) * sumAlpha S a - sumDelta S a - h) := by
    rw [hs, Real.sq_sqrt hQ]; rfl
  set t : ℝ := tstar S a h with htdef
  have ht : t = ((h : ℝ) * sumA S + s) / 2 := rfl
  have hhA0 : 0 ≤ (h : ℝ) * sumA S := by positivity
  have hα' : sumDelta S a ≤ (h : ℝ) * sumAlpha S a := hΔα
  have hfx0 : 0 ≤ x0 ^ 2 - (h : ℝ) * sumA S * x0
      + ((h : ℝ) * sumAlpha S a - h - sumDelta S a) := by
    rw [hx0sq]; linarith [hAx0, hα']
  have hprod : (x0 - t) * (x0 - ((h : ℝ) * sumA S - s) / 2)
      = x0 ^ 2 - (h : ℝ) * sumA S * x0 + ((h : ℝ) * sumAlpha S a - h - sumDelta S a) := by
    rw [ht]; linear_combination (-1 / 4 : ℝ) * hs2
  have htx : t ≤ x0 := by
    by_contra hcon
    push_neg at hcon
    have hr : 0 < x0 - ((h : ℝ) * sumA S - s) / 2 := by linarith
    have hneg : (x0 - t) * (x0 - ((h : ℝ) * sumA S - s) / 2) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hr
    linarith
  have hy : t ^ 2 - h - sumDelta S a = (h : ℝ) * (sumA S * t - sumAlpha S a) := by
    rw [ht]; linear_combination (1 / 4 : ℝ) * hs2
  have hyL : t ^ 2 - h - sumDelta S a ≤ (L : ℝ) - (h : ℝ) * sumAlpha S a := by
    rw [hy]
    have h1 : (h : ℝ) * (sumA S * t) ≤ (h : ℝ) * (sumA S * x0) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htx hA0) (Nat.cast_nonneg h)
    nlinarith [h1, hAx0]
  -- the divisor
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
  have hαeq : sumAlpha S a = ((∑ p ∈ S, a p : ℕ) : ℝ) := by
    unfold sumAlpha; push_cast; rfl
  set K : ℕ := ⌊(L : ℝ) - sumDelta S a⌋₊ with hK
  have hKle : (K : ℝ) ≤ (L : ℝ) - sumDelta S a := Nat.floor_le (by linarith)
  have hMK : Mstar S a h ≤ K := by
    unfold Mstar
    apply Nat.ceil_le.mpr
    show t ^ 2 - h - sumDelta S a ≤ K
    -- `N = h α` is a natural number `≥ Δ`, hence `N ≥ ⌈Δ⌉` and `L - N ≤ ⌊L - Δ⌋`
    set N : ℕ := h * ∑ p ∈ S, a p with hN
    have hNeq : ((N : ℕ) : ℝ) = (h : ℝ) * sumAlpha S a := by
      rw [hαeq, hN]; push_cast; ring
    by_cases hNL : N ≤ L
    · have hle : (((L - N : ℕ)) : ℝ) ≤ (L : ℝ) - sumDelta S a := by
        rw [Nat.cast_sub hNL]; linarith [hNeq, hα']
      have hKge : L - N ≤ K := Nat.le_floor hle
      have hKge' : (((L - N : ℕ)) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKge
      rw [Nat.cast_sub hNL] at hKge'
      linarith [hyL, hNeq, hKge']
    · push_neg at hNL
      have hLN : (L : ℝ) < (N : ℝ) := by exact_mod_cast hNL
      have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      linarith [hyL, hNeq, hLN, hK0]
  have h2K : (2 : ℝ) ^ K = (2 : ℝ) ^ ((K : ℕ) : ℝ) := (Real.rpow_natCast 2 K).symm
  have h2L : (2 : ℝ) ^ L = (2 : ℝ) ^ ((L : ℕ) : ℝ) := (Real.rpow_natCast 2 L).symm
  calc (Dvis S δ : ℝ) * (2 : ℝ) ^ (Mstar S a h)
      ≤ (Dvis S δ : ℝ) * (2 : ℝ) ^ K := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) hMK
    _ = (2 : ℝ) ^ (sumDelta S a + (K : ℝ)) := by
        rw [hDvis, h2K, Real.rpow_add (by norm_num)]
    _ ≤ (2 : ℝ) ^ ((L : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hKle])
    _ = (2 : ℝ) ^ L := h2L.symm


#print axioms aThr_logb_leM2
#print axioms sumDelta_boundsM2
#print axioms B_le_AM2

end TVGPlus
end LeanCheck
