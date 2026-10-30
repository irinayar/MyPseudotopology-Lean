import LeanCheck.ChainM1

/-!
# The mixed-prime dual has Hausdorff dimension zero: trigonometric lemmas
(TVGadd-v4 Theorem `mixed:dimension`)

We replace the integral in the printed Parseval step by the discrete orthogonality of the grid `{m/M}`:  for `M` larger than the
spread of a finite set `A` of integers, `∑_{m<M} ∑_{k,l ∈ A} cos(2π (k-l) m/M) = M |A|`.
-/

namespace LeanCheck

open Finset Real

section Trig

lemma norm_coe_eq_abs_of_le {x : ℝ} (h : |x| ≤ 1 / 2) : ‖(x : Circ)‖ = |x| := by
  rw [norm_coe_circ]
  apply le_antisymm
  · have := round_le x 0
    simpa using this
  · by_cases hz : round x = 0
    · simp [hz]
    · have h1 : (1 : ℝ) ≤ |(round x : ℝ)| := by exact_mod_cast Int.one_le_abs hz
      have h2 : |(round x : ℝ)| ≤ |x - round x| + |x| := by
        calc |(round x : ℝ)| = |x - (x - round x)| := by ring_nf
          _ ≤ |x| + |x - round x| := abs_sub _ _
          _ = |x - round x| + |x| := add_comm _ _
      linarith

lemma cos_ge_of_norm_le_eighth {x : ℝ} (h : ‖(x : Circ)‖ ≤ 1 / 8) : √2 / 2 ≤ Real.cos (2 * π * x) := by
  rw [norm_coe_circ] at h
  set n := round x with hn
  have hx : x = (x - n) + n := by ring
  have hc : Real.cos (2 * π * x) = Real.cos (2 * π * (x - n)) := by
    have : 2 * π * x = 2 * π * (x - n) + (n : ℤ) * (2 * π) := by push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi]
  rw [hc, ← Real.cos_abs, show 2 * π * (x - n) = 2 * π * (x - n) from rfl]
  have habs : |2 * π * (x - n)| = 2 * π * |x - n| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  rw [habs, ← Real.cos_pi_div_four]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  nlinarith [Real.pi_pos, abs_nonneg (x - n)]

end Trig

section Orth

lemma sum_cos_grid (M : ℕ) (hM : 0 < M) (j : ℤ) (hj : j ≠ 0) (hjM : |j| < M) :
    ∑ m ∈ range M, Real.cos (2 * π * j * m / M) = 0 := by
  set z : ℂ := Complex.exp (2 * π * Complex.I * j / M) with hz
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have h2 : (j : ℂ) = (n : ℂ) * M := by
      have : (2 * π * Complex.I * j / M) = n * (2 * π * Complex.I) := hn
      field_simp at this
      linear_combination this
    have h3 : j = n * M := by exact_mod_cast h2
    have h4 : n ≠ 0 := by rintro rfl; simp at h3; exact hj h3
    have h5 : (1 : ℤ) ≤ |n| := Int.one_le_abs h4
    have h6 : |j| = |n| * M := by rw [h3, abs_mul]; simp
    have : (M : ℤ) ≤ |j| := by rw [h6]; nlinarith [(by exact_mod_cast hM : (1 : ℤ) ≤ M)]
    omega
  have hzM : z ^ M = 1 := by
    rw [hz, ← Complex.exp_nat_mul]
    have : (M : ℂ) * (2 * π * Complex.I * j / M) = j * (2 * π * Complex.I) := by
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hsum : ∑ m ∈ range M, z ^ m = 0 := by
    rw [geom_sum_eq hz1, hzM]; simp
  have hre := congrArg Complex.re hsum
  rw [Complex.re_sum, Complex.zero_re] at hre
  rw [← hre]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [hz, ← Complex.exp_nat_mul]
  have : (m : ℂ) * (2 * π * Complex.I * j / M) = ((2 * π * j * m / M : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

end Orth

section Grid

noncomputable def Cf (A : Finset ℤ) (t : ℝ) : ℝ := ∑ k ∈ A, Real.cos (2 * π * k * t)
noncomputable def Sf (A : Finset ℤ) (t : ℝ) : ℝ := ∑ k ∈ A, Real.sin (2 * π * k * t)
noncomputable def Qf (A : Finset ℤ) (t : ℝ) : ℝ :=
  ∑ k ∈ A, ∑ l ∈ A, Real.cos (2 * π * ((k : ℝ) - l) * t)

lemma Qf_eq (A : Finset ℤ) (t : ℝ) : Qf A t = Cf A t ^ 2 + Sf A t ^ 2 := by
  unfold Qf Cf Sf
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Real.cos_sub]
  congr 1; ring

lemma Qf_nonneg (A : Finset ℤ) (t : ℝ) : 0 ≤ Qf A t := by
  rw [Qf_eq]; positivity

lemma sum_Qf_grid (A : Finset ℤ) (M : ℕ) (hM : 0 < M) (hA : ∀ k ∈ A, ∀ l ∈ A, |k - l| < M) :
    ∑ m ∈ range M, Qf A ((m : ℝ) / M) = M * A.card := by
  unfold Qf
  rw [Finset.sum_comm]
  have h1 : ∀ k ∈ A, ∑ m ∈ range M, ∑ l ∈ A, Real.cos (2 * π * ((k : ℝ) - l) * ((m : ℝ) / M)) = M := by
    intro k hk
    rw [Finset.sum_comm]
    have : ∀ l ∈ A, ∑ m ∈ range M, Real.cos (2 * π * ((k : ℝ) - l) * ((m : ℝ) / M)) = if k = l then (M : ℝ) else 0 := by
      intro l hl
      by_cases hkl : k = l
      · subst hkl; simp
      · rw [if_neg hkl]
        have := sum_cos_grid M hM (k - l) (sub_ne_zero.2 hkl) (hA k hk l hl)
        rw [← this]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        congr 1; push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp [hk]
  rw [Finset.sum_congr rfl (fun k hk => h1 k hk)]
  simp [mul_comm]

lemma grid_count (A : Finset ℤ) (M : ℕ) (hM : 0 < M) (hA : ∀ k ∈ A, ∀ l ∈ A, |k - l| < M) :
    (((range M).filter (fun m : ℕ => (A.card : ℝ) ^ 2 / 4 ≤ Qf A ((m : ℝ) / M))).card : ℝ) * ((A.card : ℝ) ^ 2 / 4)
      ≤ M * A.card := by
  rw [← sum_Qf_grid A M hM hA]
  calc (((range M).filter (fun m : ℕ => (A.card : ℝ) ^ 2 / 4 ≤ Qf A ((m : ℝ) / M))).card : ℝ) * ((A.card : ℝ) ^ 2 / 4)
      = ∑ m ∈ (range M).filter (fun m : ℕ => (A.card : ℝ) ^ 2 / 4 ≤ Qf A ((m : ℝ) / M)), (A.card : ℝ) ^ 2 / 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ (range M).filter (fun m : ℕ => (A.card : ℝ) ^ 2 / 4 ≤ Qf A ((m : ℝ) / M)), Qf A ((m : ℝ) / M) :=
        Finset.sum_le_sum (fun m hm => (Finset.mem_filter.1 hm).2)
    _ ≤ ∑ m ∈ range M, Qf A ((m : ℝ) / M) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun m _ _ => Qf_nonneg A _)

end Grid

end LeanCheck
