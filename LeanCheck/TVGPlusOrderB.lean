import LeanCheck.TVGPlusOrderA

/-!
# TVGplus: the logarithmic order, lower bound and the size of `D_S(δ)`

With `L = log (1/δ)` and `ℓ_p = log p`:

* `aThr_ge`, `aThr_le`: `(L/ℓ_p - 1)/2 ≤ a_p(δ) ≤ (L/ℓ_p + 1)/2`;
* `log_Dvis_le`, `log_Dvis_ge`: `c_S L² - |S| L/2 ≤ log D_S(δ) ≤ c_S L² + |S| L/2 + (∑ ℓ_p)/4` (the lower bound for `L ≥ ℓ_p`),
  where `c_S = ∑ 1/(4 ℓ_p)`;
* `order_lower`: for every `b < c_S` and all small `δ`, every positive element `k` of the ball satisfies `exp(b L²) ≤ k`
  (the lower bound `c_S ≤ liminf log u_S(δ) / L²`).
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- `c_S = (1/4) ∑ 1 / log p`. -/
noncomputable def cS (S : Finset ℕ) : ℝ := ∑ p ∈ S, 1 / (4 * Real.log p)

lemma log_pos_of_prime {p : ℕ} (hp : p.Prime) : 0 < Real.log p :=
  Real.log_pos (by exact_mod_cast hp.one_lt)

lemma log_inv_eq {δ : ℝ} : Real.log (1 / δ) = -Real.log δ := by
  rw [one_div, Real.log_inv]

lemma aThr_ge {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) :
    (Real.log (1 / δ) / Real.log p - 1) / 2 ≤ aThr p δ := by
  have hl := log_pos_of_prime hp
  have h := aThr_spec hp.two_le hδ
  have hp0 : (0 : ℝ) < (p : ℝ) ^ (2 * aThr p δ + 1) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  have h2 := Real.log_lt_log (by positivity) h
  rw [one_div, Real.log_inv, Real.log_pow] at h2
  rw [log_inv_eq]
  push_cast at h2
  have key : -Real.log δ ≤ (2 * (aThr p δ : ℝ) + 1) * Real.log p := by linarith
  have : -Real.log δ / Real.log p ≤ 2 * (aThr p δ : ℝ) + 1 := (div_le_iff₀ hl).mpr key
  linarith

lemma aThr_le {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (aThr p δ : ℝ) ≤ (Real.log (1 / δ) / Real.log p + 1) / 2 := by
  have hl := log_pos_of_prime hp
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  rcases Nat.eq_zero_or_pos (aThr p δ) with h0 | hpos
  · rw [h0]
    have : 0 < Real.log (1 / δ) / Real.log p := div_pos hL hl
    simp only [Nat.cast_zero]
    linarith
  · have hlt : aThr p δ - 1 < aThr p δ := by omega
    have h := aThr_min hlt
    have hp0 : (0 : ℝ) < (p : ℝ) ^ (2 * (aThr p δ - 1) + 1) := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity
    have h2 := Real.log_le_log hδ h
    rw [one_div, Real.log_inv, Real.log_pow] at h2
    rw [log_inv_eq]
    have e : ((2 * (aThr p δ - 1) + 1 : ℕ) : ℝ) = 2 * (aThr p δ : ℝ) - 1 := by
      have : 1 ≤ aThr p δ := hpos
      push_cast [Nat.cast_sub this]
      ring
    rw [e] at h2
    have key : (2 * (aThr p δ : ℝ) - 1) * Real.log p ≤ -Real.log δ := by linarith
    have : 2 * (aThr p δ : ℝ) - 1 ≤ -Real.log δ / Real.log p := (le_div_iff₀ hl).mpr key
    linarith

lemma log_Dvis (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (δ : ℝ) :
    Real.log (Dvis S δ : ℝ) = ∑ p ∈ S, ((aThr p δ : ℝ) ^ 2) * Real.log p := by
  unfold Dvis
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  · intro p hp
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
    simp [this]

lemma sum_term_eq (S : Finset ℕ) (L : ℝ) :
    ∑ p ∈ S, (L ^ 2 * (1 / (4 * Real.log p)) + L / 2 + Real.log p / 4) =
      L ^ 2 * cS S + S.card * (L / 2) + (∑ p ∈ S, Real.log p) / 4 := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    ← Finset.sum_div]
  simp [cS, nsmul_eq_mul]

theorem log_Dvis_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.log (Dvis S δ : ℝ) ≤ Real.log (1 / δ) ^ 2 * cS S + S.card * (Real.log (1 / δ) / 2) +
      (∑ p ∈ S, Real.log p) / 4 := by
  rw [log_Dvis S hS, ← sum_term_eq]
  apply Finset.sum_le_sum
  intro p hp
  have hl := log_pos_of_prime (hS p hp)
  have h1 := aThr_le (hS p hp) hδ hδ1
  have h0 : (0 : ℝ) ≤ aThr p δ := Nat.cast_nonneg _
  set L := Real.log (1 / δ)
  have h2 : (aThr p δ : ℝ) ^ 2 ≤ ((L / Real.log p + 1) / 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : (aThr p δ : ℝ) ^ 2 * Real.log p ≤ ((L / Real.log p + 1) / 2) ^ 2 * Real.log p :=
    mul_le_mul_of_nonneg_right h2 hl.le
  refine h3.trans (le_of_eq ?_)
  field_simp
  ring

theorem log_Dvis_ge (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {δ : ℝ} (hδ : 0 < δ)
    (hL : ∀ p ∈ S, Real.log p ≤ Real.log (1 / δ)) :
    Real.log (1 / δ) ^ 2 * cS S - S.card * (Real.log (1 / δ) / 2) ≤ Real.log (Dvis S δ : ℝ) := by
  rw [log_Dvis S hS]
  have : Real.log (1 / δ) ^ 2 * cS S - S.card * (Real.log (1 / δ) / 2) =
      ∑ p ∈ S, (Real.log (1 / δ) ^ 2 * (1 / (4 * Real.log p)) - Real.log (1 / δ) / 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const]
    simp [cS, nsmul_eq_mul]
  rw [this]
  apply Finset.sum_le_sum
  intro p hp
  have hl := log_pos_of_prime (hS p hp)
  have h1 := aThr_ge (hS p hp) hδ
  have hLp := hL p hp
  set L := Real.log (1 / δ)
  have h0 : 0 ≤ (L / Real.log p - 1) / 2 := by
    have : 1 ≤ L / Real.log p := by rw [le_div_iff₀ hl]; linarith
    linarith
  have h2 : ((L / Real.log p - 1) / 2) ^ 2 ≤ (aThr p δ : ℝ) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : ((L / Real.log p - 1) / 2) ^ 2 * Real.log p ≤ (aThr p δ : ℝ) ^ 2 * Real.log p :=
    mul_le_mul_of_nonneg_right h2 hl.le
  have e : ((L / Real.log p - 1) / 2) ^ 2 * Real.log p =
      L ^ 2 * (1 / (4 * Real.log p)) - L / 2 + Real.log p / 4 := by
    field_simp
    ring
  linarith

/-- **Lower bound of the logarithmic order**: for every `b < c_S` and all sufficiently small `δ`, every positive
element `k` of the ball `B^S_δ` satisfies `exp (b (log (1/δ))²) ≤ k`; i.e. `c_S ≤ liminf log u_S(δ) / (log (1/δ))²`. -/
theorem order_lower {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {b : ℝ} (hb : b < cS S) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ k : ℤ, 1 ≤ k → InBall S δ k →
      Real.exp (b * Real.log (1 / δ) ^ 2) ≤ k := by
  set L₀ : ℝ := max (max (∑ p ∈ S, Real.log p) (S.card / (2 * (cS S - b)))) 1 with hL₀
  have hcb : 0 < cS S - b := by linarith
  refine ⟨Real.exp (-L₀), Real.exp_pos _, ?_⟩
  intro δ hδ hδ0 k hk1 hk
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ0 (by
    rw [Real.exp_le_one_iff]; have : 1 ≤ L₀ := le_max_right _ _; linarith)
  have hLL : L₀ < Real.log (1 / δ) := by
    rw [log_inv_eq]
    have := Real.log_lt_log hδ hδ0
    rw [Real.log_exp] at this
    linarith
  have hLp : ∀ p ∈ S, Real.log p ≤ Real.log (1 / δ) := by
    intro p hp
    have h1 : Real.log p ≤ ∑ q ∈ S, Real.log q :=
      Finset.single_le_sum (f := fun q : ℕ => Real.log (q : ℝ))
        (fun q hq => (log_pos_of_prime (hS q hq)).le) hp
    have h2 : (∑ q ∈ S, Real.log q) ≤ L₀ := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  set L := Real.log (1 / δ) with hL
  have hcard : (S.card : ℝ) / (2 * (cS S - b)) ≤ L₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hL1 : 1 ≤ L := by have : 1 ≤ L₀ := le_max_right _ _; linarith
  have hge := log_Dvis_ge S hS hδ hLp
  have hcardL : (S.card : ℝ) / 2 ≤ (cS S - b) * L := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (cS S - b))).mp (hcard.trans hLL.le)
    linarith
  have hlogD : b * L ^ 2 ≤ Real.log (Dvis S δ : ℝ) := by nlinarith
  have hDpos : (0 : ℝ) < (Dvis S δ : ℝ) := by
    unfold Dvis
    have : 0 < ∏ p ∈ S, p ^ (aThr p δ ^ 2) :=
      Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos _)
    exact_mod_cast this
  have h1 : Real.exp (b * L ^ 2) ≤ (Dvis S δ : ℝ) := by
    calc Real.exp (b * L ^ 2) ≤ Real.exp (Real.log (Dvis S δ : ℝ)) := Real.exp_le_exp.mpr hlogD
      _ = (Dvis S δ : ℝ) := Real.exp_log hDpos
  have h2 : (Dvis S δ : ℤ) ≤ k := Int.le_of_dvd (by omega) (forced hS hδ hk)
  have h3 : (Dvis S δ : ℝ) ≤ k := by exact_mod_cast h2
  exact h1.trans h3

#print axioms aThr_ge
#print axioms aThr_le
#print axioms log_Dvis_le
#print axioms log_Dvis_ge
#print axioms order_lower


end TVGPlus
end LeanCheck
