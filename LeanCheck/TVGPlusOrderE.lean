import LeanCheck.TVGPlusOrderD

/-!
# TVGplus: the logarithmic order, upper bound

`order_upper`: for every `B > x_S` and all sufficiently small `δ` there is a positive `k ≤ 2 exp (B (log (1/δ))²)`
in the ball `B^S_δ`; i.e. `limsup log u_S(δ) / (log (1/δ))² ≤ x_S`.  Together with `order_lower` this is the two-sided statement of
`TVGplus`, Theorem "The logarithmic order".
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

set_option maxHeartbeats 1600000 in
theorem order_upper {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {B : ℝ} (hB : xS S < B) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ k : ℤ, 1 ≤ k ∧
      (k : ℝ) ≤ 2 * Real.exp (B * Real.log (1 / δ) ^ 2) ∧ InBall S δ k := by
  classical
  have hB0 : 0 < B := lt_of_le_of_lt (by unfold xS; positivity) hB
  have hβ0 : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB0
  have hβ2 : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0.le
  have hK1 : 1 ≤ Kc B := by
    unfold Kc
    have : 0 ≤ 1 / (2 * Real.sqrt B) := by positivity
    linarith
  have hf := f_pos S hS hB
  have hcB : cS S < B := lt_of_le_of_lt (cS_le_xS S hS) hB
  have hΛ : 0 ≤ ∑ p ∈ S, Real.log p := Finset.sum_nonneg (fun p hp => (log_pos_of_prime (hS p hp)).le)
  have hA := aS_nonneg S
  -- the constants
  obtain ⟨f, hfdef⟩ : ∃ f, f = B - aS S * Real.sqrt B + cS S := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = aS S * Real.sqrt B - 2 * cS S := ⟨_, rfl⟩
  obtain ⟨s0, hs0def⟩ : ∃ s0, s0 = aS S * Kc B + (S.card : ℝ) / 2 := ⟨_, rfl⟩
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = ∑ p ∈ S, Real.log p := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℝ, n = S.card := ⟨_, rfl⟩
  have hn0 : 0 ≤ n := by rw [hndef]; positivity
  have hs0 : 0 ≤ s0 := by rw [hs0def]; positivity
  have hfpos : 0 < f := by rw [hfdef]; exact hf
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; exact hΛ
  obtain ⟨W, hWdef⟩ : ∃ W, W = s0 + |T| * Real.log 2 + n / 2 + s0 * Real.log 2 + Λ / 4 := ⟨_, rfl⟩
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  obtain ⟨L₀, hL₀⟩ : ∃ L₀, L₀ = max (max 1 (W / f)) ((n / 2 + Λ / 4) / (B - cS S)) := ⟨_, rfl⟩
  refine ⟨Real.exp (-L₀), Real.exp_pos _, ?_⟩
  intro δ hδ hδ0
  have hL1' : 1 ≤ L₀ := by rw [hL₀]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ0 (by rw [Real.exp_le_one_iff]; linarith)
  have hLL : L₀ < Real.log (1 / δ) := by
    rw [log_inv_eq]
    have := Real.log_lt_log hδ hδ0
    rw [Real.log_exp] at this
    linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (1 / δ) := ⟨_, rfl⟩
  rw [← hLdef] at hLL ⊢
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hWL : W ≤ f * L := by
    have h1 : W / f ≤ L₀ := by rw [hL₀]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    have h2 := (div_le_iff₀ hfpos).mp (h1.trans hLL.le)
    linarith
  have hDL : n / 2 + Λ / 4 ≤ (B - cS S) * L := by
    have h1 : (n / 2 + Λ / 4) / (B - cS S) ≤ L₀ := by rw [hL₀]; exact le_max_right _ _
    have h2 := (div_le_iff₀ (by linarith : 0 < B - cS S)).mp (h1.trans hLL.le)
    linarith
  -- D, N0, M
  obtain ⟨Dr, hDr⟩ : ∃ Dr : ℝ, Dr = (Dvis S δ : ℝ) := ⟨_, rfl⟩
  have hDpos : 0 < Dr := by
    rw [hDr]; unfold Dvis
    have : 0 < ∏ p ∈ S, p ^ (aThr p δ ^ 2) := Finset.prod_pos (fun p hp => pow_pos (hS p hp).pos _)
    exact_mod_cast this
  have hlogD : Real.log Dr ≤ L ^ 2 * cS S + n * (L / 2) + Λ / 4 := by
    rw [hDr, hndef, hΛdef, hLdef]; exact log_Dvis_le S hS hδ hδ1
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℝ, N0 = Real.exp (B * L ^ 2) := ⟨_, rfl⟩
  have hN0pos : 0 < N0 := by rw [hN0]; exact Real.exp_pos _
  have hN01 : 1 ≤ N0 := by rw [hN0]; exact Real.one_le_exp (by positivity)
  have hDN0 : Dr ≤ N0 := by
    have h1 : Real.log Dr ≤ B * L ^ 2 := by
      have : (n / 2 + Λ / 4) * L ≤ (B - cS S) * L * L := mul_le_mul_of_nonneg_right hDL hL0
      nlinarith
    calc Dr = Real.exp (Real.log Dr) := (Real.exp_log hDpos).symm
      _ ≤ Real.exp (B * L ^ 2) := Real.exp_le_exp.mpr h1
      _ = N0 := hN0.symm
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ⌈N0 / Dr⌉₊ := ⟨_, rfl⟩
  have hMge : N0 / Dr ≤ M := by rw [hMdef]; exact Nat.le_ceil _
  have hMlt : (M : ℝ) < N0 / Dr + 1 := by rw [hMdef]; exact Nat.ceil_lt_add_one (by positivity)
  have hM1 : 1 ≤ M := by
    have : 0 < M := by rw [hMdef]; exact Nat.ceil_pos.mpr (by positivity)
    omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hNdef : ((Dvis S δ * M : ℕ) : ℝ) = Dr * M := by rw [hDr]; push_cast; ring
  have hNle : Dr * M ≤ 2 * N0 := by
    have : Dr * M ≤ Dr * (N0 / Dr + 1) := mul_le_mul_of_nonneg_left hMlt.le hDpos.le
    have e : Dr * (N0 / Dr + 1) = N0 + Dr := by field_simp
    linarith
  have hNge : N0 ≤ Dr * M := by
    have := (div_le_iff₀ hDpos).mp hMge
    linarith
  have hNpos : 0 < Dr * M := by positivity
  -- Y = log (N / δ)
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = Real.log (Dr * M / δ) := ⟨_, rfl⟩
  have hYsplit : Y = Real.log (Dr * M) + L := by
    rw [hYdef, Real.log_div hNpos.ne' hδ.ne', hLdef, log_inv_eq]; ring
  have hY0 : 0 ≤ Y := by
    rw [hYdef]
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    nlinarith
  have hYle : Y ≤ (Real.sqrt B * L + Kc B) ^ 2 := by
    have h1 : Real.log (Dr * M) ≤ Real.log (2 * N0) := Real.log_le_log hNpos hNle
    rw [Real.log_mul (by norm_num) hN0pos.ne', hN0, Real.log_exp] at h1
    have hK : Kc B = 1 + 1 / (2 * Real.sqrt B) := rfl
    have h2 : (Real.sqrt B * L + Kc B) ^ 2 = B * L ^ 2 + (2 * Real.sqrt B + 1) * L + Kc B ^ 2 := by
      have e2 : Real.sqrt B * Kc B = Real.sqrt B + 1 / 2 := by
        rw [hK]; field_simp
      calc (Real.sqrt B * L + Kc B) ^ 2
          = Real.sqrt B ^ 2 * L ^ 2 + 2 * (Real.sqrt B * Kc B) * L + Kc B ^ 2 := by ring
        _ = B * L ^ 2 + (2 * Real.sqrt B + 1) * L + Kc B ^ 2 := by rw [hβ2, e2]; ring
    have hK2 : 1 ≤ Kc B ^ 2 := by nlinarith [hK1]
    rw [h2, hYsplit]
    nlinarith [mul_nonneg hβ0.le hL0, hK2, hlog2']
  -- the cut-offs
  have hcount := count_bound S hS hδ hB (Y := Y) (by rw [← hLdef]; exact hL0) (by rw [← hLdef]; exact hYle)
  rw [← hLdef] at hcount
  -- m
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌊1 / δ⌋₊ + 1 := ⟨_, rfl⟩
  have hm : 1 / δ < (m : ℝ) := by
    rw [hmdef]; push_cast; exact Nat.lt_floor_add_one _
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmle : (m : ℝ) ≤ 2 / δ := by
    rw [hmdef]; push_cast
    have h1 : (⌊1 / δ⌋₊ : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
    have h2 : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    have : 2 / δ = 1 / δ + 1 / δ := by ring
    linarith
  have hlogm : Real.log m ≤ L + Real.log 2 := by
    have := Real.log_le_log hm0 hmle
    rw [Real.log_div (by norm_num) hδ.ne'] at this
    rw [hLdef, log_inv_eq]; linarith
  have hlogm0 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
  -- the main inequality
  have hlogM : (B - cS S) * L ^ 2 - n * (L / 2) - Λ / 4 ≤ Real.log M := by
    have h1 : Real.log (N0 / Dr) ≤ Real.log M := Real.log_le_log (by positivity) hMge
    rw [Real.log_div hN0pos.ne' hDpos.ne', hN0, Real.log_exp] at h1
    nlinarith
  set dN : ℕ := ∑ p ∈ S, (⌊Real.sqrt (Y / Real.log p)⌋₊ - aThr p δ) with hdN
  have hdN0 : (0 : ℝ) ≤ dN := Nat.cast_nonneg _
  have hprod : (dN : ℝ) * Real.log m ≤ (T * L + s0) * (L + Real.log 2) := by
    rw [hTdef, hs0def]
    exact mul_le_mul hcount hlogm hlogm0 (le_trans hdN0 hcount)
  have hineq : (T * L + s0) * (L + Real.log 2) ≤ (B - cS S) * L ^ 2 - n * (L / 2) - Λ / 4 := by
    have hfT : B - cS S - T = f := by rw [hTdef, hfdef]; ring
    have h1 : T * Real.log 2 ≤ |T| * Real.log 2 := mul_le_mul_of_nonneg_right (le_abs_self T) hlog2
    have h2 : (s0 * Real.log 2 + Λ / 4) ≤ (s0 * Real.log 2 + Λ / 4) * L :=
      le_mul_of_one_le_right (by positivity) hL1
    have h3 : (s0 + T * Real.log 2 + n / 2) * L ≤ (s0 + |T| * Real.log 2 + n / 2) * L :=
      mul_le_mul_of_nonneg_right (by linarith) hL0
    have h4 : W * L ≤ f * L * L := mul_le_mul_of_nonneg_right hWL hL0
    rw [hWdef] at h4
    nlinarith [h1, h2, h3, h4, hfT]
  have hmM : m ^ dN ≤ M := by
    have hR : (m : ℝ) ^ dN ≤ M := by
      calc (m : ℝ) ^ dN = (Real.exp (Real.log m)) ^ dN := by rw [Real.exp_log hm0]
        _ = Real.exp (dN * Real.log m) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (Real.log M) := Real.exp_le_exp.mpr (by linarith)
        _ = M := Real.exp_log hMpos
    exact_mod_cast hR
  -- the cut-off hypothesis of `upper_mult`
  have hr : ∀ p ∈ S, ((Dvis S δ * M : ℕ) : ℝ) / δ <
      ((p ^ ((⌊Real.sqrt (Y / Real.log p)⌋₊ + 1) ^ 2) : ℕ) : ℝ) := by
    intro p hp
    have hl := log_pos_of_prime (hS p hp)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    set ρ := ⌊Real.sqrt (Y / Real.log p)⌋₊ with hρ
    have h1 : Real.sqrt (Y / Real.log p) < (ρ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : Y / Real.log p < ((ρ : ℝ) + 1) ^ 2 := (Real.sqrt_lt' (by positivity)).mp h1
    have h3 : Y < ((ρ : ℝ) + 1) ^ 2 * Real.log p := (div_lt_iff₀ hl).mp h2
    rw [hNdef, ← Real.exp_log (by positivity : 0 < Dr * M / δ), ← hYdef]
    have e : (((p ^ ((ρ + 1) ^ 2) : ℕ) : ℝ)) = Real.exp ((((ρ + 1) ^ 2 : ℕ) : ℝ) * Real.log p) := by
      rw [Real.exp_nat_mul, Real.exp_log hp0]; push_cast; ring
    rw [e]
    apply Real.exp_lt_exp.mpr
    push_cast
    linarith
  obtain ⟨k, hk1, hkN, hk⟩ := upper_mult hS hδ M m hM1 hm (fun p => ⌊Real.sqrt (Y / Real.log p)⌋₊) hr hmM
  refine ⟨k, hk1, ?_, hk⟩
  have hkR : (k : ℝ) ≤ ((Dvis S δ * M : ℕ) : ℝ) := by exact_mod_cast hkN
  rw [hNdef] at hkR
  rw [← hN0]
  linarith

#print axioms order_upper

end TVGPlus
end LeanCheck
