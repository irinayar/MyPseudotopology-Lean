import LeanCheck.ChainTopMain

/-!
# Every character of `ℚ/ℤ` is a profinite integer, and the dual of `λ_{range M}` is exactly `ℤι`

For a profitely null divisibility chain `M` (`M n > 0`, `M n ∣ M (n+1)`):

* `hom_is_zeta` : every additive character `χ : ℚ/ℤ → ℝ/ℤ` equals `ζ_z` for a compatible residue system `z`
  (this is `Hom(ℚ/ℤ, 𝕋) = Ẑ = lim ℤ/M_n`);
* `dual_exact` : for ratios `≥ 2` tending to infinity and `M 0 = 1`, a character is continuous for `λ_{range M}`
  if and only if it is `x ↦ u • x` for an integer `u`.  That is, `λ_{range M}` is compatible with `ℤι`.
-/

namespace LeanCheck

open Filter Topology

lemma torsion_form {m : ℕ} (hm : 0 < m) {y : Circ} (h : m • y = 0) :
    ∃ n : ℤ, y = n • (((1 / (m : ℝ) : ℝ)) : Circ) := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective y
  rw [← ht] at h
  change m • ((t : ℝ) : Circ) = 0 at h
  rw [nsmul_coe_circ, AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← ht, zsmul_coe_circ]
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [zsmul_eq_mul, mul_one] at hn
  have : t = n * (1 / (m : ℝ)) := by rw [hn]; field_simp
  rw [this]

section hom

variable {M : ℕ → ℕ}

/-- The element `1/M k` of `ℚ/ℤ`. -/
noncomputable def eE (hpos : ∀ n, 0 < M n) (k : ℕ) : TorsA :=
  ⟨((1 / (M k : ℝ) : ℝ) : Circ), by
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨M k, hpos k, ?_⟩
    rw [nsmul_coe_circ, AddCircle.coe_eq_zero_iff]
    refine ⟨1, ?_⟩
    have : (M k : ℝ) ≠ 0 := by exact_mod_cast (hpos k).ne'
    simp [this]⟩

lemma eE_coe (hpos : ∀ n, 0 < M n) (k : ℕ) :
    ((eE hpos k : TorsA) : Circ) = ((1 / (M k : ℝ) : ℝ) : Circ) := rfl

lemma kill_e (hpos : ∀ n, 0 < M n) (k : ℕ) : M k • (eE hpos k : TorsA) = 0 := by
  apply Subtype.ext
  rw [AddSubgroup.coe_nsmul, eE_coe, nsmul_coe_circ, AddSubgroup.coe_zero, AddCircle.coe_eq_zero_iff]
  refine ⟨1, ?_⟩
  have : (M k : ℝ) ≠ 0 := by exact_mod_cast (hpos k).ne'
  simp [this]

theorem hom_is_zeta (hpos : ∀ n, 0 < M n) (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n)
    (hM : ∀ n, M n ∣ M (n + 1)) (χ : TorsA →+ Circ) :
    ∃ (z : ℕ → ℤ) (hz : ∀ k, (M k : ℤ) ∣ z (k + 1) - z k), χ = zetaHom hnull hM z hz := by
  have hker : ∀ k, M k • χ (eE hpos k) = 0 := by
    intro k; rw [← map_nsmul, kill_e, map_zero]
  choose z hz using fun k => torsion_form (hpos k) (hker k)
  have hcomp : ∀ k, (M k : ℤ) ∣ z (k + 1) - z k := by
    intro k
    obtain ⟨r, hr⟩ := hM k
    have hMk : (M k : ℝ) ≠ 0 := by exact_mod_cast (hpos k).ne'
    have hrpos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · have := hpos (k + 1); rw [hr, h0] at this; simp at this
      · exact h0
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hMr : (M (k + 1) : ℝ) = M k * r := by exact_mod_cast hr
    have h1 : r • (eE hpos (k + 1) : TorsA) = eE hpos k := by
      apply Subtype.ext
      rw [AddSubgroup.coe_nsmul, eE_coe, eE_coe, nsmul_coe_circ, hMr]
      congr 1
      field_simp
    have h2 : χ (eE hpos k) = r • χ (eE hpos (k + 1)) := by rw [← h1, map_nsmul]
    rw [hz k, hz (k + 1), zsmul_coe_circ, zsmul_coe_circ, nsmul_coe_circ, hMr] at h2
    have h3 : ((((r : ℝ) * ((z (k + 1) : ℝ) * (1 / ((M k : ℝ) * r)))
        - (z k : ℝ) * (1 / (M k : ℝ)) : ℝ)) : Circ) = 0 := by
      rw [AddCircle.coe_sub, h2, sub_self]
    rw [AddCircle.coe_eq_zero_iff] at h3
    obtain ⟨n, hn⟩ := h3
    rw [zsmul_eq_mul, mul_one] at hn
    refine ⟨n, ?_⟩
    have : ((z (k + 1) - z k : ℤ) : ℝ) = M k * n := by
      rw [hn]; push_cast; field_simp
    exact_mod_cast this
  refine ⟨z, hcomp, ?_⟩
  ext x
  obtain ⟨k, hk⟩ := exists_k hnull x
  rw [zetaHom_apply hnull hM z hcomp x hk]
  obtain ⟨m', hm'⟩ := torsion_form (hpos k) hk
  have hx : x = m' • eE hpos k := by
    apply Subtype.ext
    rw [AddSubgroup.coe_zsmul, eE_coe]; exact hm'
  rw [hx, map_zsmul, hz k, AddSubgroup.coe_zsmul, eE_coe, smul_comm]

end hom

lemma intHom_continuous {M : ℕ → ℕ} (h1 : (1 : ℕ) ∈ Set.range M) (u : ℤ) (χ : TorsA →+ Circ)
    (hχ : ∀ x : TorsA, χ x = u • (x : Circ)) :
    @Continuous TorsA Circ (basisOf (Set.range M)).topology _ χ := by
  refine continuous_of_quarter _ χ ⟨1 / (4 * ((|u| : ℝ) + 1)), by positivity, fun x hx => ?_⟩
  have hx1 := hx 1 h1
  rw [hχ, one_nsmul] at *
  have hnorm : ‖u • (x : Circ)‖ ≤ |(u : ℝ)| * ‖(x : Circ)‖ := by
    have := norm_zsmul_le u (x : Circ)
    simpa [Int.norm_eq_abs] using this
  have hpos : (0 : ℝ) < 4 * ((|u| : ℝ) + 1) := by positivity
  calc ‖u • (x : Circ)‖ ≤ |(u : ℝ)| * ‖(x : Circ)‖ := hnorm
    _ ≤ |(u : ℝ)| * (1 / (4 * ((|u| : ℝ) + 1))) := by
        gcongr
    _ < 1 / 4 := by
        rw [mul_one_div, div_lt_div_iff₀ hpos (by norm_num)]
        nlinarith [abs_nonneg (u : ℝ)]

/-- `λ_{range (Mseq α)}` is compatible with `ℤι`: its continuous characters are exactly `x ↦ u • x`. -/
theorem dual_exact {α : ℕ → ℕ} (hα : ∀ i, 2 ≤ α i) (hlarge : ∀ A : ℝ, ∃ i0 : ℕ, ∀ i ≥ i0, A ≤ α i)
    (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ Mseq α n) (h0 : Mseq α 0 = 1) (χ : TorsA →+ Circ) :
    @Continuous TorsA Circ (basisOf (Set.range (Mseq α))).topology _ χ ↔
      ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ) := by
  have hα0 : ∀ i, 0 < α i := fun i => lt_of_lt_of_le (by norm_num) (hα i)
  have hpos : ∀ n, 0 < Mseq α n := Mseq_pos hα0
  have hdvd : ∀ n, Mseq α n ∣ Mseq α (n + 1) := fun n => Mseq_dvd α (Nat.le_succ n)
  constructor
  · intro hcont
    obtain ⟨z, hz, rfl⟩ := hom_is_zeta hpos hnull hdvd χ
    obtain ⟨δ, hδ, hC⟩ := cont_of_continuous hα0 hnull hz hcont
    obtain ⟨u, i1, hu⟩ := case_dichotomy hα hlarge hz hδ hC
    refine ⟨u, fun x => ?_⟩
    obtain ⟨k, hk⟩ := exists_k hnull x
    have hkk : Mseq α (max i1 k + 1) • (x : Circ) = 0 :=
      kill_of_dvd hdvd (le_trans (le_max_right _ _) (Nat.le_succ _)) hk
    rw [zetaHom_apply hnull hdvd z hz x hkk]
    obtain ⟨c, hc⟩ := hu (max i1 k) (le_max_left _ _)
    have h00 : (z (max i1 k + 1) - u) • (x : Circ) = 0 := by
      rw [hc, mul_comm, mul_smul, natCast_zsmul, hkk, smul_zero]
    rw [sub_zsmul] at h00
    exact add_neg_eq_zero.mp h00
  · rintro ⟨u, hu⟩
    exact intHom_continuous ⟨0, by simpa using h0⟩ u χ hu

/-- `λ_C` is Hausdorff when `1 ∈ C` (the inclusion into the circle is continuous and injective). -/
lemma t2_basisOf {C : Set ℕ} (h1 : 1 ∈ C) : @T2Space TorsA (basisOf C).topology := by
  letI : TopologicalSpace TorsA := (basisOf C).topology
  have hc : Continuous ((AddCommGroup.torsion Circ).subtype) :=
    continuous_of_quarter C _ ⟨1 / 8, by norm_num, fun x hx => by
      have := hx 1 h1
      rw [one_nsmul] at this
      show ‖(x : Circ)‖ < 1 / 4
      linarith⟩
  exact T2Space.of_injective_continuous (f := fun x : TorsA => (x : Circ)) Subtype.val_injective hc

/-- **Final capstone.**  There are two group topologies `λ₁, λ₂` on `ℚ/ℤ`, both Hausdorff, with continuous
character group exactly `ℤι` (compatible), whose join has a continuous character outside `ℤι`. -/
theorem final_capstone :
    ∃ (M1 M2 : ℕ → ℕ) (ζ : TorsA →+ Circ),
      (1 ∈ Set.range M1) ∧ (1 ∈ Set.range M2) ∧
      @T2Space TorsA (basisOf (Set.range M1)).topology ∧
      @T2Space TorsA (basisOf (Set.range M2)).topology ∧
      (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (Set.range M1)).topology _ χ ↔
        ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) ∧
      (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (Set.range M2)).topology _ χ ↔
        ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) ∧
      @Continuous TorsA Circ
        ((basisOf (Set.range M1)).topology ⊓ (basisOf (Set.range M2)).topology) _ ζ ∧
      (∀ u : ℤ, ∃ x : TorsA, ζ x ≠ u • (x : Circ)) := by
  obtain ⟨α1, α2, hα1, hl1, hα2, hl2, h01, h02, hrel, hn1, hn2, ⟨z1, hc1, hr1⟩,
    ⟨z2, hc2, hr2⟩, _, _, hjoin⟩ := capstone
  have h1r : 1 ∈ Set.range (Mseq α1) := ⟨0, h01⟩
  have h2r : 1 ∈ Set.range (Mseq α2) := ⟨0, h02⟩
  exact ⟨Mseq α1, Mseq α2, zetaHom hn1 (fun n => Mseq_dvd α1 (Nat.le_succ n)) z1 hc1,
    h1r, h2r, t2_basisOf h1r, t2_basisOf h2r,
    fun χ => dual_exact hα1 hl1 hn1 h01 χ, fun χ => dual_exact hα2 hl2 hn2 h02 χ,
    zeta_join_continuous hn1 hc1 hr1 hjoin, zeta_not_int hn1 hc1 hr1⟩

end LeanCheck
