import LeanCheck.TwoPrimesAdaptive

/-!
# The critical logarithmic density

`witness_of_critical_density`: fix the radius and the target.  If arbitrarily large heights `X`
carry sets of differences with `|V| ≥ X/K` where `K` is as small as wanted compared with
`(log X)^(1/a)`, `a = 12 D² log 2`, then the target has a witness.  The starting parameter is
chosen once for the target.  The existence of the sets is a hypothesis.

The criterion is due to ChatGPT.
-/

namespace TwoPrimesCritical

open Finset Real TwoPrimesEffective TwoPrimesAdaptive

theorem witness_of_critical_density {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) {s : ℝ} (t : ℤ)
    (dens : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧ ∃ K : ℝ, 1 ≤ K ∧
      K ≤ ε * (log X) ^ (1 / (12 * (D : ℝ) ^ 2 * log 2)) ∧
      ∃ V : Finset ℤ, ∃ a b : ℤ → ℤ, (X : ℝ) ≤ K * V.card ∧ (∀ v ∈ V, v = a v - b v) ∧
        (∀ v ∈ V, |a v| ≤ (X : ℤ)) ∧ (∀ v ∈ V, |b v| ≤ (X : ℤ)) ∧
        (∀ v ∈ V, Small p s (a v)) ∧ (∀ v ∈ V, Small q s (b v))) :
    ∃ k : ℤ, Small p (4 * (s + 1 / D)) k ∧ Small q (4 * (s + 1 / D)) (k - t) := by
  classical
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set e : ℝ := 12 * (D : ℝ) ^ 2 * log 2 with he
  have he0 : 0 < e := by
    have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have : (0 : ℝ) < (D : ℝ) ^ 2 := pow_pos (by linarith) 2
    exact mul_pos (mul_pos (by norm_num) this) h2
  set c : ℝ := max (sqrt (log p)) (sqrt (log q)) with hc
  have hcp : sqrt (log p) ≤ c := le_max_left _ _
  have hcq : sqrt (log q) ≤ c := le_max_right _ _
  have hc0 : 0 < c := lt_of_lt_of_le (sqrt_log_pos hp) hcp
  set x0 : ℝ := max (50 * c) (max (log (2 * D) / (2 * sqrt (log p)))
    (max (log (2 * D) / (2 * sqrt (log q))) (sqrt (log (32 * (1 + |(t : ℝ)|)) / 2)))) with hx0
  have hx : 50 * c ≤ x0 := le_max_left _ _
  have hx00 : 0 ≤ x0 := le_trans (by positivity) hx
  have hx1 : log (2 * D) / (2 * sqrt (log p)) ≤ x0 :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hx2 : log (2 * D) / (2 * sqrt (log q)) ≤ x0 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hx3 : sqrt (log (32 * (1 + |(t : ℝ)|)) / 2) ≤ x0 :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hrange : ∀ r : ℕ, 2 ≤ r → log (2 * D) / (2 * sqrt (log r)) ≤ x0 →
      log (2 * D) ^ 2 ≤ 4 * log r * x0 ^ 2 := by
    intro r hr h
    have hs : 0 < sqrt (log (r : ℝ)) := sqrt_log_pos hr
    rw [div_le_iff₀ (by positivity)] at h
    have h0 : 0 ≤ log (2 * (D : ℝ)) := log_nonneg (by linarith)
    have h1 := pow_le_pow_left₀ h0 h 2
    have e1 : (x0 * (2 * sqrt (log r))) ^ 2 = 4 * log r * x0 ^ 2 := by
      rw [mul_pow, mul_pow, sq_sqrt (TwoPrimesEffective.log_pos' hr).le]; ring
    rwa [e1] at h1
  set M : ℝ := (x0 + 4 * c / (sqrt 2 - 1)) ^ 2 with hM
  have hM0 : 0 < M := by
    have h1 : 0 < 4 * c / (sqrt 2 - 1) :=
      div_pos (by linarith) (by linarith [sqrt2_bounds.1])
    have : 0 < x0 + 4 * c / (sqrt 2 - 1) := by linarith
    exact pow_pos this 2
  have h17 : (0 : ℝ) < 17 ^ e := rpow_pos_of_pos (by norm_num) _
  have hbase : (0 : ℝ) < 1 / (4 * 17 ^ e * M) :=
    div_pos one_pos (mul_pos (mul_pos (by norm_num) h17) hM0)
  set ε : ℝ := (1 / (4 * 17 ^ e * M)) ^ (1 / e) with hε
  have hε0 : 0 < ε := rpow_pos_of_pos hbase _
  obtain ⟨X, hX, K, hK, hKX, V, a, b, hV, hdiff, haX, hbX, ha, hb⟩ := dens ε hε0 4096
  have hXr : (4096 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hlX : 0 ≤ log (X : ℝ) := log_nonneg (by linarith)
  set B : ℕ := ⌊12 * (D : ℝ) ^ 2 * log (17 * K)⌋₊ with hB
  have hK0 : 0 < K := by linarith
  have h17K : (0 : ℝ) < 17 * K := by linarith
  have h2B : (2 : ℝ) ^ B ≤ (17 * K) ^ e := by
    have h1 : (B : ℝ) ≤ 12 * (D : ℝ) ^ 2 * log (17 * K) :=
      Nat.floor_le (mul_nonneg (by positivity) (log_nonneg (by linarith)))
    have e2 : (2 : ℝ) ^ B = exp (B * log 2) := by
      rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [e2, rpow_def_of_pos h17K]
    apply exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right h1 (log_pos (by norm_num : (1 : ℝ) < 2)).le
    refine le_trans this (le_of_eq ?_)
    rw [he]; ring
  have hKe : K ^ e ≤ (1 / (4 * 17 ^ e * M)) * log X := by
    have h1 := rpow_le_rpow hK0.le hKX he0.le
    have e1 : (ε * (log X) ^ (1 / e)) ^ e = (1 / (4 * 17 ^ e * M)) * log X := by
      rw [mul_rpow hε0.le (rpow_nonneg hlX _), hε, ← rpow_mul hbase.le, ← rpow_mul hlX,
        one_div_mul_cancel he0.ne', rpow_one, rpow_one]
    rwa [e1] at h1
  have hΛ : xs c x0 (B + 1) ^ 2 ≤ log X / 2 := by
    have h1 : xs c x0 (B + 1) ^ 2 ≤ 2 ^ (B + 1) * M := xs_sq_le hc0.le hx00 (B + 1)
    have h2 : (2 : ℝ) ^ B ≤ 17 ^ e * ((1 / (4 * 17 ^ e * M)) * log X) := by
      refine le_trans h2B ?_
      rw [mul_rpow (by norm_num) hK0.le]
      exact mul_le_mul_of_nonneg_left hKe h17.le
    have e3 : 17 ^ e * ((1 / (4 * 17 ^ e * M)) * log X) = log X / (4 * M) := by
      field_simp
    rw [e3] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ 2 * M by linarith)
    have e4 : log (X : ℝ) / (4 * M) * (2 * M) = log X / 2 := by
      field_simp; ring
    have e5 : (2 : ℝ) ^ (B + 1) * M = 2 ^ B * (2 * M) := by rw [pow_succ]; ring
    rw [e4] at h3
    rw [e5] at h1
    exact le_trans h1 h3
  have hXbig : 64 * exp (xs c x0 (B + 1) ^ 2) ≤ X := by
    set r : ℝ := exp (log X / 2) with hr
    have hr2 : r ^ 2 = X := by
      rw [sq, hr, ← exp_add, add_halves, exp_log hXpos]
    have hr0 : 0 < r := exp_pos _
    have hr64 : 64 ≤ r := by
      have h1 : (64 : ℝ) ^ 2 ≤ r ^ 2 := by rw [hr2]; linarith
      exact (pow_le_pow_iff_left₀ (by norm_num) hr0.le two_ne_zero).mp h1
    have h2 : exp (xs c x0 (B + 1) ^ 2) ≤ r := exp_le_exp.mpr hΛ
    have h3 := mul_le_mul_of_nonneg_right hr64 hr0.le
    nlinarith
  have htx : |(t : ℝ)| ≤ exp (2 * x0 ^ 2) / 32 := by
    have ht1 : (1 : ℝ) ≤ 32 * (1 + |(t : ℝ)|) := by
      have := abs_nonneg (t : ℝ); linarith
    have hl : 0 ≤ log (32 * (1 + |(t : ℝ)|)) := log_nonneg ht1
    have h1 := pow_le_pow_left₀ (sqrt_nonneg _) hx3 2
    rw [sq_sqrt (by linarith)] at h1
    have h2 : 32 * (1 + |(t : ℝ)|) ≤ exp (2 * x0 ^ 2) := by
      have := exp_le_exp.mpr (show log (32 * (1 + |(t : ℝ)|)) ≤ 2 * x0 ^ 2 by linarith)
      rwa [exp_log (by linarith)] at this
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
    linarith
  have hX100 : 100 ≤ X := le_trans (by norm_num) hX
  obtain ⟨k, _, hkp, hkq⟩ := witness_of_density_adaptive hp hq hpq hD (s := s) hK hcp hcq hx
    (hrange p hp hx1) (hrange q hq hx2) hB (X := X) hXbig hX100 V hV a b hdiff haX hbX ha hb
    t htx
  exact ⟨k, hkp, hkq⟩

end TwoPrimesCritical
