/-- Lower bound for `P` through the first square scale above `2|k|`:
`P(k) ≥ 2^{-(2 √(log₂ (2|k|)) + 2)}`. -/
lemma sqrt_log_lower (k : ℤ) (hk : k ≠ 0) :
    (2 : ℝ) ^ (-(2 * Real.sqrt (Real.logb 2 (2 * |(k : ℝ)|)) + 2)) ≤ Pn (sqScales 2) k := by
  set a : ℝ := |(k : ℝ)| with ha
  have ha1 : 1 ≤ a := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
    have : (1 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h1
    simpa [ha] using this
  have ha0 : 0 < a := by linarith
  set m : ℝ := Real.logb 2 (2 * a) with hm
  have hm1 : 1 ≤ m := by
    rw [hm, Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    norm_num; linarith
  have h2m : (2 : ℝ) ^ m = 2 * a := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  set sm : ℝ := Real.sqrt m with hsm
  have hsq : sm * sm = m := Real.mul_self_sqrt (by linarith)
  have hsm0 : 0 ≤ sm := Real.sqrt_nonneg _
  have hsm1 : 1 ≤ sm := by
    rw [hsm]; exact Real.one_le_sqrt.mpr hm1
  set n : ℕ := ⌈sm⌉₊ with hn
  have hnle : sm ≤ n := Nat.le_ceil sm
  have hnlt : (n : ℝ) < sm + 1 := Nat.ceil_lt_add_one hsm0
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := hsm1.trans hnle
    exact_mod_cast this
  have hn2a : m ≤ (n : ℝ) ^ 2 := by nlinarith
  have hn2b : (n : ℝ) ^ 2 < m + 2 * sm + 1 := by nlinarith
  have hcast : (2 : ℝ) ^ ((n : ℝ) ^ 2) = (2 : ℝ) ^ (n ^ 2) := by
    rw [show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hq1 : 2 * a ≤ (2 : ℝ) ^ (n ^ 2) := by
    calc 2 * a = (2 : ℝ) ^ m := h2m.symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) ^ 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hn2a
      _ = (2 : ℝ) ^ (n ^ 2) := hcast
  have hq2 : (2 : ℝ) ^ (n ^ 2) ≤ 2 * a * (2 : ℝ) ^ (2 * sm + 1) := by
    calc (2 : ℝ) ^ (n ^ 2) = (2 : ℝ) ^ ((n : ℝ) ^ 2) := hcast.symm
      _ ≤ (2 : ℝ) ^ (m + (2 * sm + 1)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 * a * (2 : ℝ) ^ (2 * sm + 1) := by rw [Real.rpow_add (by norm_num), h2m]
  have hqpos : (0 : ℝ) < (2 : ℝ) ^ (n ^ 2) := by positivity
  have hqe : ((2 ^ (n ^ 2) : ℕ) : ℝ) = (2 : ℝ) ^ (n ^ 2) := by push_cast; rfl
  have hmem : (2 ^ (n ^ 2) : ℕ) ∈ sqScales 2 := mem_sqScales hn1
  have hP := le_Pn hmem k
  have habs : |(k : ℝ) / (((2 ^ (n ^ 2) : ℕ)) : ℝ)| = a / (2 : ℝ) ^ (n ^ 2) := by
    rw [abs_div, hqe, abs_of_pos hqpos]
  have hhalf : |(k : ℝ) / (((2 ^ (n ^ 2) : ℕ)) : ℝ)| ≤ 1 / 2 := by
    rw [habs, div_le_iff₀ hqpos]; linarith
  rw [nrm_eq_abs hhalf, habs] at hP
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ (2 * sm + 1) := by positivity
  have hpow : (2 : ℝ) ^ (-(2 * sm + 2)) = 1 / (2 * (2 : ℝ) ^ (2 * sm + 1)) := by
    rw [Real.rpow_neg (by norm_num), show 2 * sm + 2 = (2 * sm + 1) + 1 by ring,
      Real.rpow_add (by norm_num), Real.rpow_one]
    field_simp
  rw [hpow]
  refine le_trans ?_ hP
  rw [div_le_div_iff₀ (by positivity) hqpos]
  nlinarith [hq2, ha0, hp2]

