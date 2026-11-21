import LeanCheck.ThreePrimesComparison
import LeanCheck.ThreePrimesTheoremBM3

/-!
# ThreePrimes (version M3): comparison of Theorem B and Theorem A for a real `η`

Real-`η` versions (`m ≤ 2^η`, `1 ≤ η`, `1 ≤ m δ`) of `ThreePrimesComparisonM2`. The proof of the sharp
inequality `D_S(δ) 2^M ≤ 2^L` for an integer `h` used that `h α` is an integer `≥ Δ`; this is not
available for a real `η`. What is proved here:

* `B_le_A_slackM3`: for a real `c ∈ [0,1]` with `c ≤ η α − Δ`: `D_S(δ) 2^M ≤ 2^(L + 1 − c)`.
* `B_le_A_succM3` (`c = 0`): `D_S(δ) 2^M ≤ 2^(L+1)` always.
* `B_le_A_sharpM3` (`c = 1`): `D_S(δ) 2^M ≤ 2^L` whenever `1 ≤ η α − Δ`.

Here `L = ⌈a_S η² + a_S η⌉`, `a_S = max 1 (A²)`, `M = MstarR`. Whether `D_S(δ) 2^M ≤ 2^L` holds for every
real `η` is not decided by these lemmas (it holds in all finite checks made).
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- For the forced exponent, `a_p(δ) log₂ p ≤ η` (when `1 ≤ m δ`, `m ≤ 2^η`, `0 ≤ η`). -/
lemma aThr_logb_leM3 {p : ℕ} (hp : 2 ≤ p) {δ : ℝ} (hδ : 0 < δ) {m : ℕ} {η : ℝ}
    (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 0 ≤ η) :
    (aThr p δ : ℝ) * Real.logb 2 (p : ℝ) ≤ η := by
  rcases Nat.eq_zero_or_pos (aThr p δ) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, zero_mul]
    exact hη
  · have hlt : aThr p δ - 1 < aThr p δ := by omega
    have hmin := aThr_min hlt
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hP : (0 : ℝ) < (p : ℝ) ^ (2 * (aThr p δ - 1) + 1) := by positivity
    have e : 2 * (aThr p δ - 1) + 1 = 2 * aThr p δ - 1 := by omega
    rw [e] at hmin hP
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ η * δ := by
      calc (1 : ℝ) ≤ m * δ := hm
        _ ≤ (2 : ℝ) ^ η * δ := by gcongr
    have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ η * (1 / (p : ℝ) ^ (2 * aThr p δ - 1)) := by
      calc (1 : ℝ) ≤ (2 : ℝ) ^ η * δ := h2
        _ ≤ _ := by gcongr
    have h4 : (p : ℝ) ^ (2 * aThr p δ - 1) ≤ (2 : ℝ) ^ η := by
      have := h3
      rw [mul_one_div, le_div_iff₀ hP] at this
      linarith
    have h5 : Real.logb 2 ((p : ℝ) ^ (2 * aThr p δ - 1)) ≤ Real.logb 2 ((2 : ℝ) ^ η) :=
      Real.logb_le_logb_of_le (by norm_num) hP h4
    rw [Real.logb_pow, Real.logb_rpow (by norm_num) (by norm_num)] at h5
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

/-- Sum bounds for `a_p log₂ p ≤ η`: `Δ ≤ η α` and `Δ ≤ η² A²`. -/
lemma sumDelta_boundsM3 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) {η : ℝ}
    (hlam : ∀ p ∈ S, (a p : ℝ) * Real.logb 2 (p : ℝ) ≤ η) :
    sumDelta S a ≤ η * sumAlpha S a ∧ sumDelta S a ≤ η ^ 2 * (sumA S) ^ 2 := by
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb (hS p hp)
  constructor
  · unfold sumDelta sumAlpha
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have h0 : (0 : ℝ) ≤ a p := Nat.cast_nonneg _
    have := hlam p hp
    calc (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ) = (a p : ℝ) * ((a p : ℝ) * Real.logb 2 (p : ℝ)) := by ring
      _ ≤ (a p : ℝ) * η := mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  · have hg0 : ∀ p ∈ S, 0 ≤ Real.sqrt (1 / Real.logb 2 (p : ℝ)) := fun p _ => Real.sqrt_nonneg _
    have hg2 : ∀ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ)) ^ 2 = 1 / Real.logb 2 (p : ℝ) := by
      intro p hp
      have hl := hlb p hp
      have hpos : 0 < Real.logb 2 (p : ℝ) := by linarith
      exact Real.sq_sqrt (by positivity)
    have hAC : ∑ p ∈ S, 1 / Real.logb 2 (p : ℝ) ≤ (sumA S) ^ 2 := by
      have := Finset.sum_sq_le_sq_sum_of_nonneg (s := S)
        (f := fun p : ℕ => Real.sqrt (1 / Real.logb 2 (p : ℝ))) hg0
      rw [Finset.sum_congr rfl hg2] at this
      exact this
    have key : sumDelta S a ≤ η ^ 2 * ∑ p ∈ S, 1 / Real.logb 2 (p : ℝ) := by
      unfold sumDelta
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hl := hlb p hp
      have hpos : 0 < Real.logb 2 (p : ℝ) := by linarith
      have h0 : 0 ≤ (a p : ℝ) * Real.logb 2 (p : ℝ) := by
        have : (0 : ℝ) ≤ a p := Nat.cast_nonneg _
        positivity
      have hsq : ((a p : ℝ) * Real.logb 2 (p : ℝ)) ^ 2 ≤ η ^ 2 :=
        pow_le_pow_left₀ h0 (hlam p hp) 2
      rw [mul_one_div, le_div_iff₀ hpos]
      nlinarith [hsq]
    have hη2 : 0 ≤ η ^ 2 := by positivity
    calc sumDelta S a ≤ η ^ 2 * ∑ p ∈ S, 1 / Real.logb 2 (p : ℝ) := key
      _ ≤ η ^ 2 * (sumA S) ^ 2 := mul_le_mul_of_nonneg_left hAC hη2

/-- `t* ≤ X` as soon as `η A ≤ X`, `0 < X` and `φ(X) ≥ 0`. -/
lemma tstar_le_M3 {S : Finset ℕ} (a : ℕ → ℕ) {η : ℝ} (hQ : 0 ≤ discQR S a η)
    {X : ℝ} (hXA : η * sumA S ≤ X) (hXpos : 0 < X)
    (hφ : 0 ≤ X ^ 2 - η * sumA S * X + (η * sumAlpha S a - η - sumDelta S a)) :
    tstarR S a η ≤ X := by
  set s : ℝ := Real.sqrt (discQR S a η) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = η ^ 2 * (sumA S) ^ 2 - 4 * (η * sumAlpha S a - sumDelta S a - η) := by
    rw [hs, Real.sq_sqrt hQ]; rfl
  set t : ℝ := tstarR S a η with htdef
  have ht : t = (η * sumA S + s) / 2 := rfl
  have hprod : (X - t) * (X - (η * sumA S - s) / 2)
      = X ^ 2 - η * sumA S * X + (η * sumAlpha S a - η - sumDelta S a) := by
    rw [ht]; linear_combination (-1 / 4 : ℝ) * hs2
  by_contra hcon
  push_neg at hcon
  have hr : 0 < X - (η * sumA S - s) / 2 := by linarith
  have hneg : (X - t) * (X - (η * sumA S - s) / 2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hr
  linarith

/-- `t*² − η − Δ = η (A t* − α)`. -/
lemma tstar_sq_M3 {S : Finset ℕ} (a : ℕ → ℕ) {η : ℝ} (hQ : 0 ≤ discQR S a η) :
    (tstarR S a η) ^ 2 - η - sumDelta S a = η * (sumA S * tstarR S a η - sumAlpha S a) := by
  set s : ℝ := Real.sqrt (discQR S a η) with hs
  have hs2 : s ^ 2 = η ^ 2 * (sumA S) ^ 2 - 4 * (η * sumAlpha S a - sumDelta S a - η) := by
    rw [hs, Real.sq_sqrt hQ]; rfl
  set t : ℝ := tstarR S a η with htdef
  have ht : t = (η * sumA S + s) / 2 := rfl
  rw [ht]; linear_combination (1 / 4 : ℝ) * hs2

/-- Last step: `D = 2^Δ`, `M = ⌈y⌉`, `y ≤ E − Δ`, `Δ ≤ E + 1` give `D 2^M ≤ 2^(E+1)`. -/
lemma final_stepM3 {D Δ y E : ℝ} {M : ℕ} (hD : D = (2 : ℝ) ^ Δ) (hM : M = ⌈y⌉₊)
    (hy : y ≤ E - Δ) (hΔE : Δ ≤ E + 1) : D * (2 : ℝ) ^ M ≤ (2 : ℝ) ^ (E + 1) := by
  by_cases hy0 : 0 ≤ y
  · have hlt : (M : ℝ) < y + 1 := by rw [hM]; exact Nat.ceil_lt_add_one hy0
    calc D * (2 : ℝ) ^ M = (2 : ℝ) ^ (Δ + (M : ℝ)) := by
          rw [hD, Real.rpow_add (by norm_num), Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ (E + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · have hM0 : M = 0 := by
      rw [hM]
      apply Nat.ceil_eq_zero.mpr
      linarith [not_le.mp hy0]
    rw [hM0, hD]
    simp only [pow_zero, mul_one]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hΔE

/-- **Theorem B versus Theorem A for a real `η`, with a slack `c`.** If `0 ≤ c ≤ 1` and
`c ≤ η α − Δ` then `D_S(δ) 2^M ≤ 2^(L + 1 − c)`. -/
theorem B_le_A_slackM3 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (m : ℕ) (η : ℝ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 1 ≤ η)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsl : c ≤ η * sumAlpha S (fun p => aThr p δ) - sumDelta S (fun p => aThr p δ)) :
    (Dvis S δ : ℝ) * (2 : ℝ) ^ (MstarR S (fun p => aThr p δ) η)
      ≤ (2 : ℝ) ^ (((⌈max 1 ((sumA S) ^ 2) * η ^ 2 + max 1 ((sumA S) ^ 2) * η⌉₊ : ℕ) : ℝ) + 1 - c) := by
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
  have hfin := final_stepM3 (D := (Dvis S δ : ℝ)) (Δ := sumDelta S a)
    (y := (tstarR S a η) ^ 2 - η - sumDelta S a) (E := (L : ℝ) - c) (M := MstarR S a η)
    hDvis rfl hyE (by linarith)
  have e : (L : ℝ) - c + 1 = (L : ℝ) + 1 - c := by ring
  rw [e] at hfin
  exact hfin

/-- **Theorem B is at most `2^(L+1)`** for every real `η` (forced exponents). -/
theorem B_le_A_succM3 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (m : ℕ) (η : ℝ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 1 ≤ η) :
    (Dvis S δ : ℝ) * (2 : ℝ) ^ (MstarR S (fun p => aThr p δ) η)
      ≤ (2 : ℝ) ^ (⌈max 1 ((sumA S) ^ 2) * η ^ 2 + max 1 ((sumA S) ^ 2) * η⌉₊ + 1) := by
  have h := B_le_A_slackM3 hS hne hδ m η hm hmh hη (c := 0) le_rfl (by norm_num) (by
    have hη0 : 0 ≤ η := by linarith
    have hlam : ∀ p ∈ S, ((fun p => aThr p δ) p : ℝ) * Real.logb 2 (p : ℝ) ≤ η :=
      fun p hp => aThr_logb_leM3 (hS p hp) hδ hm hmh hη0
    have := (sumDelta_boundsM3 hS (fun p => aThr p δ) hlam).1
    linarith)
  rw [sub_zero] at h
  generalize (⌈max 1 ((sumA S) ^ 2) * η ^ 2 + max 1 ((sumA S) ^ 2) * η⌉₊) = L at h ⊢
  have e : (L : ℝ) + 1 = ((L + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [e, Real.rpow_natCast] at h
  exact h

/-- **Theorem B is at most `2^L`** (the sharp comparison) for a real `η` whenever `1 ≤ η α − Δ`. -/
theorem B_le_A_sharpM3 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    (m : ℕ) (η : ℝ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 1 ≤ η)
    (hsl : 1 ≤ η * sumAlpha S (fun p => aThr p δ) - sumDelta S (fun p => aThr p δ)) :
    (Dvis S δ : ℝ) * (2 : ℝ) ^ (MstarR S (fun p => aThr p δ) η)
      ≤ (2 : ℝ) ^ (⌈max 1 ((sumA S) ^ 2) * η ^ 2 + max 1 ((sumA S) ^ 2) * η⌉₊) := by
  have h := B_le_A_slackM3 hS hne hδ m η hm hmh hη (c := 1) (by norm_num) le_rfl hsl
  generalize (⌈max 1 ((sumA S) ^ 2) * η ^ 2 + max 1 ((sumA S) ^ 2) * η⌉₊) = L at h ⊢
  have e : (L : ℝ) + 1 - 1 = (L : ℝ) := by ring
  rw [e, Real.rpow_natCast] at h
  exact h

#print axioms aThr_logb_leM3
#print axioms sumDelta_boundsM3
#print axioms B_le_A_succM3
#print axioms B_le_A_sharpM3

end TVGPlus
end LeanCheck
