import LeanCheck.ChainTopZeta

/-!
# The dictionary lemma: continuity of `ζ_z` for `λ_{range M}` gives the quarter-arc statement `Cont`

For `M = Mseq α` (`α i > 0`), a compatible residue system `z`, and the character `ζ_z = zetaHom`:
if `ζ_z` is continuous for the group topology `λ_{range M}` on `ℚ/ℤ`, then `Cont α z δ` holds for some `δ > 0`,
where `Cont` is the finite-level statement used in `case_dichotomy`.
-/

namespace LeanCheck

open Filter Topology

lemma zsmul_coe_circ (n : ℤ) (x : ℝ) : n • (x : Circ) = ((n * x : ℝ) : Circ) := by
  have : ((n * x : ℝ) : Circ) = ((n • x : ℝ) : Circ) := by rw [zsmul_eq_mul]
  rw [this, AddCircle.coe_zsmul]

lemma Mxval_int_ge {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) (ρ : ℕ → ℤ) {K i : ℕ} (hi : K ≤ i) :
    ∃ n : ℤ, (Mseq α i : ℚ) * xval α ρ K = n := by
  refine ⟨∑ j ∈ Finset.range K, ρ j * ((Mseq α i / Mseq α (j + 1) : ℕ) : ℤ), ?_⟩
  rw [Int.cast_sum]
  unfold xval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j + 1 ≤ i := by have := Finset.mem_range.mp hj; omega
  have hd : Mseq α (j + 1) ∣ Mseq α i := Mseq_dvd α hj'
  have hne : (Mseq α (j + 1) : ℚ) ≠ 0 := by
    have := Mseq_pos hα (j + 1); positivity
  have key : ((Mseq α i / Mseq α (j + 1) : ℕ) : ℚ) = (Mseq α i : ℚ) / Mseq α (j + 1) :=
    Nat.cast_div hd hne
  simp only [Int.cast_mul, Int.cast_natCast, key]
  ring

/-- The element `x = ∑_{j<K} ρ_j / M_{j+1}` of `ℚ/ℤ`. -/
noncomputable def xe {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) (ρ : ℕ → ℤ) (K : ℕ) : TorsA :=
  ⟨(((xval α ρ K : ℚ) : ℝ) : Circ), by
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨Mseq α K, Mseq_pos hα K, ?_⟩
    rw [nsmul_coe_circ, AddCircle.coe_eq_zero_iff]
    obtain ⟨n, hn⟩ := Mxval_int_ge hα ρ (le_refl K)
    refine ⟨n, ?_⟩
    have : (Mseq α K : ℝ) * ((xval α ρ K : ℚ) : ℝ) = n := by exact_mod_cast hn
    rw [this]; simp⟩

lemma xe_coe {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) (ρ : ℕ → ℤ) (K : ℕ) :
    ((xe hα ρ K : TorsA) : Circ) = (((xval α ρ K : ℚ) : ℝ) : Circ) := rfl

lemma xe_obs {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) (ρ : ℕ → ℤ) (K : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hball : ∀ i ≤ K, ∃ n : ℤ, |((((Mseq α i : ℚ) * xval α ρ K : ℚ)) : ℝ) - n| < δ) :
    xe hα ρ K ∈ obs (Set.range (Mseq α)) δ := by
  rintro c ⟨i, rfl⟩
  rw [xe_coe, nsmul_coe_circ]
  by_cases hi : i ≤ K
  · obtain ⟨n, hn⟩ := hball i hi
    have : (((((Mseq α i : ℚ) * xval α ρ K : ℚ)) : ℝ)) = (Mseq α i : ℝ) * ((xval α ρ K : ℚ) : ℝ) := by
      push_cast; ring
    rw [this] at hn
    exact lt_of_le_of_lt (norm_coe_le _ n) hn
  · obtain ⟨n, hn⟩ := Mxval_int_ge hα ρ (le_of_lt (not_le.mp hi))
    have : (Mseq α i : ℝ) * ((xval α ρ K : ℚ) : ℝ) = n := by exact_mod_cast hn
    rw [this]
    have h0 : ((n : ℝ) : Circ) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]; exact ⟨n, by simp⟩
    rw [h0]; simpa using hδ

lemma chi_eq {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) {z : ℕ → ℤ}
    (hz : ∀ k, (Mseq α k : ℤ) ∣ z (k + 1) - z k) (ρ : ℕ → ℤ) (K : ℕ) :
    ∃ m : ℤ, chi α z ρ K = (z K : ℝ) * ((xval α ρ K : ℚ) : ℝ) + m := by
  have hM : ∀ n, Mseq α n ∣ Mseq α (n + 1) := fun n => Mseq_dvd α (Nat.le_succ n)
  have hc : ∀ j, ∃ c : ℤ, j < K → z K - z (j + 1) = (Mseq α (j + 1) : ℤ) * c := by
    intro j
    by_cases hj : j < K
    · obtain ⟨c, hc⟩ := z_dvd hM hz (Nat.succ_le_of_lt hj)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose c hc using hc
  refine ⟨-(∑ j ∈ Finset.range K, ρ j * c j), ?_⟩
  unfold chi xval
  push_cast
  have hsum : ∑ j ∈ Finset.range K, (ρ j : ℝ) * ((z (j + 1) : ℝ) / (Mseq α (j + 1) : ℝ))
      = ∑ j ∈ Finset.range K, ((z K : ℝ) * ((ρ j : ℝ) / (Mseq α (j + 1) : ℝ)) - (ρ j : ℝ) * (c j : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have e : (z K : ℝ) - z (j + 1) = (Mseq α (j + 1) : ℝ) * c j := by exact_mod_cast hc j hj'
    have e2 : (z (j + 1) : ℝ) = z K - (Mseq α (j + 1) : ℝ) * c j := by linarith
    have hMne : (Mseq α (j + 1) : ℝ) ≠ 0 := by
      have := Mseq_pos hα (j + 1); positivity
    rw [e2]
    field_simp
  rw [hsum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end LeanCheck
