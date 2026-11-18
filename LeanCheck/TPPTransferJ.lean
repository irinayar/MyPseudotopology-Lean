import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# ThreePrimeContinue: the arithmetic of the conditional finiteness theorem

Theorem "Finiteness of close triples under `(H_J)`" has two arithmetic steps, formalized here.

* `delta_lower_J`: if a nonzero integer vector `h` with `1 ≤ m := ‖h‖ ≤ M ≤ 4 √n` satisfies the exponent bound
  `c m^(-J) ≤ |h·v|` (`(H_J)`, `J ≥ 0`) and the pigeonhole bound `n |h·v| ≤ 2 M δ`, then
  `δ ≥ c / (2 · 4^(J+1)) · n^((1-J)/2)`.
* `no_close_triple_large`: if `J < 3`, then for `n` large the lower bound `δ ≥ c₁ n^((1-J)/2)` is incompatible with
  `δ ≤ C (log n)² / n` (the size of `δ` for a triple of diameter `O(log² n)`), so `n` is bounded.
-/

namespace TPP

open Real

/-- Monotonicity of `m ↦ m^(-J)`. -/
theorem rpow_neg_mono (m M J : ℝ) (hm : 0 < m) (hmM : m ≤ M) (hJ : 0 ≤ J) :
    M ^ (-J) ≤ m ^ (-J) := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  rw [Real.rpow_neg hm.le, Real.rpow_neg hM.le]
  have h1 : 0 < m ^ J := Real.rpow_pos_of_pos hm J
  have h2 : m ^ J ≤ M ^ J := Real.rpow_le_rpow hm.le hmM hJ
  exact inv_anti₀ h1 h2

/-- From `(H_J)` and the pigeonhole bound to a lower bound for `δ`. -/
theorem delta_lower_J (c J δ n M m hv : ℝ) (hc : 0 < c) (hJ : 0 ≤ J) (hn : 0 < n) (hm1 : 1 ≤ m)
    (hmM : m ≤ M) (hM : M ≤ 4 * Real.sqrt n) (hH : c * m ^ (-J) ≤ hv) (hb : n * hv ≤ 2 * M * δ) :
    c / (2 * 4 ^ (J + 1)) * n ^ ((1 - J) / 2) ≤ δ := by
  have hm0 : 0 < m := by linarith
  have hM0 : 0 < M := by linarith
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have h1 : c * M ^ (-J) ≤ hv :=
    le_trans (mul_le_mul_of_nonneg_left (rpow_neg_mono m M J hm0 hmM hJ) hc.le) hH
  have h2 : c * M ^ (-J) * n ≤ 2 * M * δ := by
    calc c * M ^ (-J) * n ≤ hv * n := mul_le_mul_of_nonneg_right h1 hn.le
      _ = n * hv := by ring
      _ ≤ 2 * M * δ := hb
  have hMJ : M ^ (-J) * M ^ J = 1 := by
    rw [← Real.rpow_add hM0]; simp
  have hMJ1 : M ^ (J + 1) = M ^ J * M := Real.rpow_add_one hM0.ne' J
  have h3 : c * n ≤ 2 * δ * M ^ (J + 1) := by
    have h := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hM0.le J)
    calc c * n = (c * M ^ (-J) * n) * M ^ J := by
          calc c * n = c * n * (M ^ (-J) * M ^ J) := by rw [hMJ]; ring
            _ = (c * M ^ (-J) * n) * M ^ J := by ring
      _ ≤ 2 * M * δ * M ^ J := h
      _ = 2 * δ * M ^ (J + 1) := by rw [hMJ1]; ring
  -- M^(J+1) ≤ 4^(J+1) n^((J+1)/2)
  have hJ1 : 0 ≤ J + 1 := by linarith
  have h4 : M ^ (J + 1) ≤ 4 ^ (J + 1) * n ^ ((J + 1) / 2) := by
    calc M ^ (J + 1) ≤ (4 * Real.sqrt n) ^ (J + 1) := Real.rpow_le_rpow hM0.le hM hJ1
      _ = 4 ^ (J + 1) * (Real.sqrt n) ^ (J + 1) := Real.mul_rpow (by norm_num) hsq.le
      _ = 4 ^ (J + 1) * n ^ ((J + 1) / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]; congr 2; ring
  have hP : 0 < 2 * 4 ^ (J + 1) * n ^ ((J + 1) / 2) := by positivity
  have h5 : c * n ≤ δ * (2 * 4 ^ (J + 1) * n ^ ((J + 1) / 2)) := by
    have hδ : 0 ≤ δ := by
      by_contra hneg0
      have hneg : δ < 0 := not_le.mp hneg0
      have : 2 * δ * M ^ (J + 1) < 0 := by
        have hp : 0 < M ^ (J + 1) := Real.rpow_pos_of_pos hM0 _
        nlinarith
      nlinarith [mul_pos hc hn]
    calc c * n ≤ 2 * δ * M ^ (J + 1) := h3
      _ ≤ 2 * δ * (4 ^ (J + 1) * n ^ ((J + 1) / 2)) :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
      _ = δ * (2 * 4 ^ (J + 1) * n ^ ((J + 1) / 2)) := by ring
  have hpow : n ^ ((1 - J) / 2) * n ^ ((J + 1) / 2) = n := by
    rw [← Real.rpow_add hn]
    have : (1 - J) / 2 + (J + 1) / 2 = 1 := by ring
    rw [this, Real.rpow_one]
  have h6 : (c / (2 * 4 ^ (J + 1)) * n ^ ((1 - J) / 2)) * (2 * 4 ^ (J + 1) * n ^ ((J + 1) / 2))
      = c * n := by
    have h42 : (2 : ℝ) * 4 ^ (J + 1) ≠ 0 := by positivity
    calc (c / (2 * 4 ^ (J + 1)) * n ^ ((1 - J) / 2)) * (2 * 4 ^ (J + 1) * n ^ ((J + 1) / 2))
        = c * (n ^ ((1 - J) / 2) * n ^ ((J + 1) / 2)) * ((2 * 4 ^ (J + 1)) / (2 * 4 ^ (J + 1))) := by ring
      _ = c * n := by rw [hpow, div_self h42]; ring
  refine le_of_mul_le_mul_right ?_ hP
  rw [h6]
  exact h5

/-- A power beats the square of the logarithm. -/
theorem log_sq_lt_rpow (C c1 s : ℝ) (hC : 0 < C) (hc1 : 0 < c1) (hs : 0 < s) :
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n : ℝ, N ≤ n → C * (Real.log n) ^ 2 < c1 * n ^ s := by
  set K : ℝ := 16 * C / (c1 * s ^ 2) + 1 with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 16 * C / (c1 * s ^ 2) := by positivity
    linarith
  refine ⟨max 1 (K ^ (2 / s)), le_max_left _ _, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : 0 < n := by linarith
  have hKpos : 0 < K := by linarith
  -- n^(s/2) ≥ K
  have hge : K ≤ n ^ (s / 2) := by
    have h1 : K ^ (2 / s) ≤ n := le_trans (le_max_right _ _) hn
    have h2 : (K ^ (2 / s)) ^ (s / 2) ≤ n ^ (s / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hKpos.le _) h1 (by linarith)
    have h3 : (K ^ (2 / s)) ^ (s / 2) = K := by
      rw [← Real.rpow_mul hKpos.le]
      have : 2 / s * (s / 2) = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [h3] at h2; exact h2
  -- log n ≤ n^(s/4) / (s/4)
  have hlog : Real.log n ≤ n ^ (s / 4) / (s / 4) := Real.log_le_rpow_div hn0.le (by linarith)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hsq : (Real.log n) ^ 2 ≤ (n ^ (s / 4) / (s / 4)) ^ 2 := by
    exact pow_le_pow_left₀ hlog0 hlog 2
  have hnp : 0 < n ^ (s / 4) := Real.rpow_pos_of_pos hn0 _
  have hexp : (n ^ (s / 4)) ^ 2 = n ^ (s / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; push_cast; ring
  have hsum : n ^ (s / 2) * n ^ (s / 2) = n ^ s := by
    rw [← Real.rpow_add hn0]; congr 1; ring
  have e1 : (n ^ (s / 4) / (s / 4)) ^ 2 = n ^ (s / 2) * (16 / s ^ 2) := by
    rw [div_pow, hexp]; field_simp; ring
  have hK2 : 16 * C / (c1 * s ^ 2) < n ^ (s / 2) := by linarith
  have hnh : 0 < n ^ (s / 2) := Real.rpow_pos_of_pos hn0 _
  have hmul : 16 * C / (c1 * s ^ 2) * n ^ (s / 2) < n ^ (s / 2) * n ^ (s / 2) :=
    by nlinarith
  have hfin : 16 * C / s ^ 2 * n ^ (s / 2) < c1 * n ^ s := by
    have hc1s : 0 < c1 * s ^ 2 := by positivity
    have : 16 * C / s ^ 2 * n ^ (s / 2) = c1 * (16 * C / (c1 * s ^ 2) * n ^ (s / 2)) := by
      field_simp
    rw [this, ← hsum]
    nlinarith [hmul, hc1]
  calc C * (Real.log n) ^ 2 ≤ C * (n ^ (s / 2) * (16 / s ^ 2)) := by
        rw [← e1]; exact mul_le_mul_of_nonneg_left hsq hC.le
    _ = 16 * C / s ^ 2 * n ^ (s / 2) := by ring
    _ < c1 * n ^ s := hfin

/-- For `J < 3` a lower bound `δ ≥ c₁ n^((1-J)/2)` and an upper bound `δ ≤ C (log n)²/n` are incompatible for large `n`. -/
theorem no_close_triple_large (J c1 C : ℝ) (hJ : J < 3) (hc1 : 0 < c1) (hC : 0 < C) :
    ∃ N : ℝ, 1 ≤ N ∧ ∀ n δ : ℝ, N ≤ n → ¬ (c1 * n ^ ((1 - J) / 2) ≤ δ ∧ δ ≤ C * (Real.log n) ^ 2 / n) := by
  obtain ⟨N, hN1, hN⟩ := log_sq_lt_rpow C c1 ((3 - J) / 2) hC hc1 (by linarith)
  refine ⟨N, hN1, ?_⟩
  rintro n δ hn ⟨h1, h2⟩
  have hn0 : 0 < n := by linarith
  have key := hN n hn
  have hpow : n ^ ((1 - J) / 2) * n = n ^ ((3 - J) / 2) := by
    rw [← Real.rpow_add_one hn0.ne']; congr 1; ring
  have h3 : c1 * n ^ ((1 - J) / 2) ≤ C * (Real.log n) ^ 2 / n := le_trans h1 h2
  have h4 : c1 * n ^ ((1 - J) / 2) * n ≤ C * (Real.log n) ^ 2 := by
    have := mul_le_mul_of_nonneg_right h3 hn0.le
    rwa [div_mul_cancel₀ _ hn0.ne'] at this
  have h5 : c1 * n ^ ((3 - J) / 2) ≤ C * (Real.log n) ^ 2 := by
    calc c1 * n ^ ((3 - J) / 2) = c1 * n ^ ((1 - J) / 2) * n := by rw [← hpow]; ring
      _ ≤ _ := h4
  linarith

end TPP
