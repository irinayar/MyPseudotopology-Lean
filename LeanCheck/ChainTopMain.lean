import LeanCheck.ChainTopDict

/-!
# Topological capstone of Theorem H

For the explicit chains `F₁ = {M_n}` and `F₂ = {1} ∪ {M_n + g_n}` of `ChainCapstone`, the profinite
integer `ζ_G = ∑_s g_{a_s}` acts on `ℚ/ℤ` as an additive character `ζ : ℚ/ℤ → ℝ/ℤ`, and

* `ζ` is **not** continuous for `λ_{F₁}` and **not** continuous for `λ_{F₂}`,
* `ζ` **is** continuous for the join `λ_{F₁} ∨ λ_{F₂}` (Mathlib's `⊓`),
* `ζ` is not of the form `x ↦ u • x` for any integer `u` (it is not in `ℤι`).

Here `λ_C` is the group topology on `ℚ/ℤ` with zero-neighbourhood base `{x | ∀ c ∈ C, ‖c • x‖ < δ}`.
-/

namespace LeanCheck

open Filter Topology

lemma cont_of_continuous {α : ℕ → ℕ} (hα : ∀ i, 0 < α i)
    (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ Mseq α n) {z : ℕ → ℤ} (hz : Compat α z)
    (hcont : @Continuous TorsA Circ (basisOf (Set.range (Mseq α))).topology _
      (zetaHom hnull (fun n => Mseq_dvd α (Nat.le_succ n)) z hz)) :
    ∃ δ : ℝ, 0 < δ ∧ Cont α z δ := by
  obtain ⟨δ, hδ, hq⟩ := quarter_of_continuous _ _ hcont
  refine ⟨δ, hδ, fun K ρ hball => ?_⟩
  have hmem := xe_obs hα ρ K hδ hball
  have h1 := hq _ hmem
  have hk : Mseq α K • ((xe hα ρ K : TorsA) : Circ) = 0 := by
    rw [xe_coe, nsmul_coe_circ, AddCircle.coe_eq_zero_iff]
    obtain ⟨n, hn⟩ := Mxval_int_ge hα ρ (le_refl K)
    refine ⟨n, ?_⟩
    have : (Mseq α K : ℝ) * ((xval α ρ K : ℚ) : ℝ) = n := by exact_mod_cast hn
    rw [this]; simp
  rw [zetaHom_apply hnull (fun n => Mseq_dvd α (Nat.le_succ n)) z hz _ hk, xe_coe,
    zsmul_coe_circ] at h1
  obtain ⟨n, hn⟩ := exists_int_of_norm_lt h1
  obtain ⟨m, hm⟩ := chi_eq hα hz ρ K
  refine ⟨n + m, ?_⟩
  have : chi α z ρ K - ((n + m : ℤ) : ℝ) = (z K : ℝ) * ((xval α ρ K : ℚ) : ℝ) - n := by
    rw [hm]; push_cast; ring
  rw [this]; exact hn

lemma zeta_not_continuous {α : ℕ → ℕ} (hα : ∀ i, 2 ≤ α i)
    (hlarge : ∀ A : ℝ, ∃ i0 : ℕ, ∀ i ≥ i0, A ≤ α i)
    (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ Mseq α n) {z : ℕ → ℤ} (hz : Compat α z)
    (hr : Represents α z) :
    ¬ @Continuous TorsA Circ (basisOf (Set.range (Mseq α))).topology _
      (zetaHom hnull (fun n => Mseq_dvd α (Nat.le_succ n)) z hz) := by
  intro hcont
  have hα0 : ∀ i, 0 < α i := fun i => lt_of_lt_of_le (by norm_num) (hα i)
  obtain ⟨δ, hδ, hC⟩ := cont_of_continuous hα0 hnull hz hcont
  obtain ⟨u, i1, hu⟩ := case_dichotomy hα hlarge hz hδ hC
  exact zetaG_not_M_integer (Mseq α) hnull z hr ⟨u, i1, hu⟩

lemma zeta_eq_Psum {α : ℕ → ℕ} (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ Mseq α n)
    {z : ℕ → ℤ} (hz : Compat α z) (hr : Represents α z) (x : TorsA) :
    ∃ S0 : ℕ, ∀ S ≥ S0,
      zetaHom hnull (fun n => Mseq_dvd α (Nat.le_succ n)) z hz x = (Psum S : ℤ) • (x : Circ) := by
  obtain ⟨k, hk⟩ := exists_k hnull x
  obtain ⟨S0, hS0⟩ := hr k
  refine ⟨S0, fun S hS => ?_⟩
  rw [zetaHom_apply hnull (fun n => Mseq_dvd α (Nat.le_succ n)) z hz x hk]
  obtain ⟨c, hc⟩ := hS0 S hS
  have h0 : ((Psum S : ℤ) - z k) • (x : Circ) = 0 := by
    rw [hc, mul_comm, mul_smul, natCast_zsmul, hk, smul_zero]
  rw [sub_zsmul] at h0
  exact (add_neg_eq_zero.mp h0).symm

/-- The join statement: `ζ_G` is continuous for `λ_{range M1} ⊓ λ_{range M2}` as soon as the ball estimate
`hjoin` holds (it is provided by `capstone`). -/
lemma zeta_join_continuous {α1 α2 : ℕ → ℕ}
    (hn1 : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ Mseq α1 n) {z1 : ℕ → ℤ} (hc1 : Compat α1 z1)
    (hr1 : Represents α1 z1)
    (hjoin : ∀ δ : ℝ, 0 < δ → δ < 1 / 16 → ∀ x : ℝ,
        (∀ n, ∃ k : ℤ, |(Mseq α1 n : ℝ) * x - k| < δ) →
        (∀ n, ∃ k : ℤ, |(Mseq α2 n : ℝ) * x - k| < δ) →
        ∀ S, ∃ N : ℤ, |∑ s ∈ Finset.range S, (gG (aG s) : ℝ) * x - N| < 1 / 4) :
    @Continuous TorsA Circ
      ((basisOf (Set.range (Mseq α1))).topology ⊓ (basisOf (Set.range (Mseq α2))).topology) _
      (zetaHom hn1 (fun n => Mseq_dvd α1 (Nat.le_succ n)) z1 hc1) := by
  refine continuous_of_quarter_join (Set.range (Mseq α1)) (Set.range (Mseq α2)) _
    ⟨1 / 32, by norm_num, fun x hx1 hx2 => ?_⟩
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (x : Circ)
  have h1 : ∀ n, ∃ k : ℤ, |(Mseq α1 n : ℝ) * t - k| < 1 / 32 := by
    intro n
    have := hx1 (Mseq α1 n) ⟨n, rfl⟩
    rw [← ht] at this
    change ‖(Mseq α1 n) • ((t : ℝ) : Circ)‖ < 1 / 32 at this
    rw [nsmul_coe_circ] at this
    exact exists_int_of_norm_lt this
  have h2 : ∀ n, ∃ k : ℤ, |(Mseq α2 n : ℝ) * t - k| < 1 / 32 := by
    intro n
    have := hx2 (Mseq α2 n) ⟨n, rfl⟩
    rw [← ht] at this
    change ‖(Mseq α2 n) • ((t : ℝ) : Circ)‖ < 1 / 32 at this
    rw [nsmul_coe_circ] at this
    exact exists_int_of_norm_lt this
  have hj := hjoin (1 / 32) (by norm_num) (by norm_num) t h1 h2
  obtain ⟨S0, hS0⟩ := zeta_eq_Psum hn1 hc1 hr1 x
  rw [hS0 S0 le_rfl]
  obtain ⟨N, hN⟩ := hj S0
  rw [← ht]
  change ‖(Psum S0 : ℤ) • ((t : ℝ) : Circ)‖ < 1 / 4
  rw [zsmul_coe_circ]
  have e : (((Psum S0 : ℤ) : ℝ) * t) = ∑ s ∈ Finset.range S0, (gG (aG s) : ℝ) * t := by
    simp [Psum, Finset.sum_mul]
  rw [e]
  exact lt_of_le_of_lt (norm_coe_le _ N) hN

/-- `ζ_G` is not of the form `x ↦ u • x`. -/
lemma zeta_not_int {α1 : ℕ → ℕ} (hn1 : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ Mseq α1 n)
    {z1 : ℕ → ℤ} (hc1 : Compat α1 z1) (hr1 : Represents α1 z1) :
    ∀ u : ℤ, ∃ x : TorsA,
      zetaHom hn1 (fun n => Mseq_dvd α1 (Nat.le_succ n)) z1 hc1 x ≠ u • (x : Circ) := by
  intro u
  by_contra hall
  push_neg at hall
  apply zetaG_not_integer
  refine ⟨u, fun N hN => ?_⟩
  have hx : IsOfFinAddOrder (((1 / N : ℝ)) : Circ) := by
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hN, ?_⟩
    rw [nsmul_coe_circ, AddCircle.coe_eq_zero_iff]
    refine ⟨1, ?_⟩
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp [this]
  obtain ⟨S0, hS0⟩ := zeta_eq_Psum hn1 hc1 hr1 (⟨_, hx⟩ : TorsA)
  refine ⟨S0, fun S hS => ?_⟩
  have e := hS0 S hS
  rw [hall] at e
  have h0 : ((Psum S : ℤ) - u) • (((1 / N : ℝ)) : Circ) = 0 := by
    rw [sub_zsmul]
    have e' : u • (((1 / N : ℝ)) : Circ) = (Psum S : ℤ) • (((1 / N : ℝ)) : Circ) := e
    rw [← e']; simp
  rw [zsmul_coe_circ, AddCircle.coe_eq_zero_iff] at h0
  obtain ⟨n, hn⟩ := h0
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [zsmul_eq_mul, mul_one] at hn
  have : (((Psum S : ℤ) - u : ℤ) : ℝ) = N * n := by
    rw [hn]; field_simp
  have : (Psum S : ℤ) - u = N * n := by exact_mod_cast this
  exact ⟨n, this⟩

/-- The topological form of Theorem H for the explicit chains. -/
theorem topological_capstone :
    ∃ (M1 M2 : ℕ → ℕ) (ζ : TorsA →+ Circ),
      ¬ @Continuous TorsA Circ (basisOf (Set.range M1)).topology _ ζ ∧
      ¬ @Continuous TorsA Circ (basisOf (Set.range M2)).topology _ ζ ∧
      @Continuous TorsA Circ
        ((basisOf (Set.range M1)).topology ⊓ (basisOf (Set.range M2)).topology) _ ζ ∧
      (∀ u : ℤ, ∃ x : TorsA, ζ x ≠ u • (x : Circ)) := by
  obtain ⟨α1, α2, hα1, hl1, hα2, hl2, h01, h02, hrel, hn1, hn2, ⟨z1, hc1, hr1⟩,
    ⟨z2, hc2, hr2⟩, _, _, hjoin⟩ := capstone
  have heq : zetaHom hn1 (fun n => Mseq_dvd α1 (Nat.le_succ n)) z1 hc1
      = zetaHom hn2 (fun n => Mseq_dvd α2 (Nat.le_succ n)) z2 hc2 := by
    ext x
    obtain ⟨S1, h1⟩ := zeta_eq_Psum hn1 hc1 hr1 x
    obtain ⟨S2, h2⟩ := zeta_eq_Psum hn2 hc2 hr2 x
    rw [h1 (max S1 S2) (le_max_left _ _), h2 (max S1 S2) (le_max_right _ _)]
  refine ⟨Mseq α1, Mseq α2, zetaHom hn1 (fun n => Mseq_dvd α1 (Nat.le_succ n)) z1 hc1,
    zeta_not_continuous hα1 hl1 hn1 hc1 hr1, ?_, ?_, ?_⟩
  · rw [heq]; exact zeta_not_continuous hα2 hl2 hn2 hc2 hr2
  · exact zeta_join_continuous hn1 hc1 hr1 hjoin
  · exact zeta_not_int hn1 hc1 hr1

end LeanCheck
