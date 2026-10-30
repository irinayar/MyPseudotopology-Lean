import LeanCheck.ChainK2

/-!
# Countable group topologies with a countable zero-neighbourhood base are metrizable
and the metrizability of the prime-square topologies
(HamelCharactersTVG_v18 Theorem 22.1 `thm:prime-v8`, metrizability)
-/

namespace LeanCheck

open Filter Topology

section Metrizable

/-- A Hausdorff group topology on `ℚ` in which zero has a countable neighbourhood base is metrizable. -/
theorem metrizable_rat (t : TopologicalSpace ℚ) (hg : @IsTopologicalAddGroup ℚ t _) (ht2 : @T2Space ℚ t)
    (B : ℕ → Set ℚ) (hB : (@nhds ℚ t 0).HasBasis (fun _ : ℕ => True) B) : @TopologicalSpace.MetrizableSpace ℚ t := by
  letI : TopologicalSpace ℚ := t
  haveI : IsTopologicalAddGroup ℚ := hg
  haveI : T2Space ℚ := ht2
  let b : Set (Set ℚ) := Set.range (fun p : ℚ × ℕ => (fun y => p.1 + y) '' interior (B p.2))
  have hbc : b.Countable := Set.countable_range _
  have hopen : ∀ u ∈ b, IsOpen u := by
    rintro _ ⟨⟨x, n⟩, rfl⟩
    exact (isOpenMap_add_left x) _ isOpen_interior
  have hbasis : TopologicalSpace.IsTopologicalBasis b := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds hopen ?_
    intro a u hau hu
    have hnh : (fun y => a + y) ⁻¹' u ∈ 𝓝 (0 : ℚ) := by
      have : Continuous fun y : ℚ => a + y := continuous_const.add continuous_id
      exact this.continuousAt.preimage_mem_nhds (by simpa using hu.mem_nhds hau)
    obtain ⟨n, -, hn⟩ := hB.mem_iff.1 hnh
    refine ⟨(fun y => a + y) '' interior (B n), ⟨(a, n), rfl⟩, ⟨0, mem_interior_iff_mem_nhds.2 (hB.mem_of_mem trivial), by simp⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have := hn (interior_subset hy)
    simpa using this
  haveI := hbasis.secondCountableTopology hbc
  haveI : T3Space ℚ := inferInstance
  exact TopologicalSpace.metrizableSpace_of_t3_secondCountable ℚ

lemma xiSet_mono_eps (C : Set ℕ) (d : ℕ) {ε ε' : ℝ} (h : ε ≤ ε') : xiSet C d ε ⊆ xiSet C d ε' :=
  fun q hq c hc => lt_of_lt_of_le (hq c hc) h

/-- The topologies `ξ_C` have a countable zero-neighbourhood base. -/
lemma xi_countable_basis (C : Set ℕ) :
    (@nhds ℚ (xi C) 0).HasBasis (fun _ : ℕ × ℕ => True) (fun k => xiSet C (k.1 + 1) (1 / ((k.2 : ℝ) + 1))) := by
  refine (xi_nhds_hasBasis C).to_hasBasis (fun s hs => ?_) (fun k _ => ?_)
  · obtain ⟨d, hd, ε, hε, rfl⟩ := hs
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    exact ⟨(d - 1, m), trivial, by
      have : d - 1 + 1 = d := by omega
      simp only [this]
      exact xiSet_mono_eps C d hm.le⟩
  · exact ⟨xiSet C (k.1 + 1) (1 / ((k.2 : ℝ) + 1)), xiSet_mem C (k.1 + 1) (Nat.succ_pos _) _ (by positivity), subset_rfl⟩

/-- **Theorem 22.1, metrizability.**  `γ_p` is metrizable. -/
theorem gamma_p_metrizable (p : ℕ) (hp : 2 ≤ p) : @TopologicalSpace.MetrizableSpace ℚ (xi (Cp p)) := by
  have hmem := gamma_p_mem p hp
  let e : ℕ ≃ ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ)).symm
  refine metrizable_rat (xi (Cp p)) hmem.1.1 hmem.1.2.1 (fun n => xiSet (Cp p) ((e n).1 + 1) (1 / (((e n).2 : ℝ) + 1))) ?_
  have h := xi_countable_basis (Cp p)
  refine (Filter.hasBasis_iff.2 fun s => ?_)
  rw [h.mem_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨e.symm k, trivial, by simpa using hk⟩
  · rintro ⟨n, -, hn⟩
    exact ⟨e n, trivial, hn⟩

end Metrizable

section NotPrecompact

lemma norm_coe_pos_small {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1 / 2) : ‖(v : Circ)‖ = v := by
  rw [norm_coe_circ]
  have : round v = 0 := by
    rw [round_eq_zero_iff]; constructor <;> linarith
  rw [this]; simp [abs_of_nonneg h0]

/-- The key estimate: for `j < k`, the points `p^{(j+1)²-1}` and `p^{(k+1)²-1}` are separated by the observation `p^{(k+1)²}`. -/
lemma pts_far (p : ℕ) (hp : 2 ≤ p) {j k : ℕ} (hjk : j < k) :
    1 / (2 * (p : ℝ)) ≤ ‖xt (((p : ℚ) ^ ((k + 1) ^ 2 - 1)) - (p : ℚ) ^ ((j + 1) ^ 2 - 1)) 1 (p ^ ((k + 1) ^ 2))‖ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨m, hm⟩ : ∃ m, (k + 1) ^ 2 - 1 = ((j + 1) ^ 2 - 1) + m + 3 := by
    refine ⟨(k + 1) ^ 2 - (j + 1) ^ 2 - 3, ?_⟩
    have h1 : (j + 1) ^ 2 + 3 ≤ (k + 1) ^ 2 := by nlinarith
    have h2 : 1 ≤ (j + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hexp : (k + 1) ^ 2 = ((j + 1) ^ 2 - 1) + m + 3 + 1 := by
    have h2 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  set B := (j + 1) ^ 2 - 1 with hB
  have hval : ((((p : ℚ) ^ ((k + 1) ^ 2 - 1) - (p : ℚ) ^ B) / (((1 : ℕ) : ℚ) * ((p ^ ((k + 1) ^ 2) : ℕ) : ℚ)) : ℚ) : ℝ)
      = 1 / (p : ℝ) - 1 / (p : ℝ) ^ (m + 4) := by
    rw [hm, hexp]
    push_cast
    field_simp
    ring
  unfold xt
  rw [hval]
  have hpm : (p : ℝ) ^ 4 ≤ (p : ℝ) ^ (m + 4) := pow_le_pow_right₀ (by linarith) (by omega)
  have hpos4 : (0 : ℝ) < (p : ℝ) ^ 4 := by positivity
  have hle : 1 / (p : ℝ) ^ (m + 4) ≤ 1 / (p : ℝ) ^ 4 := one_div_le_one_div_of_le hpos4 hpm
  have h2p : 1 / (p : ℝ) ^ 4 ≤ 1 / (2 * p) := by
    rw [div_le_div_iff₀ hpos4 (by positivity)]
    have h3 : (2 : ℝ) ^ 3 ≤ (p : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hp1 3
    have h4 : (p : ℝ) ^ 4 = (p : ℝ) * (p : ℝ) ^ 3 := by ring
    rw [h4]
    nlinarith
  have hlow : 1 / (2 * (p : ℝ)) ≤ 1 / (p : ℝ) - 1 / (p : ℝ) ^ (m + 4) := by
    have : 1 / (p : ℝ) - 1 / (2 * p) = 1 / (2 * p) := by field_simp; ring
    linarith
  have hupper : 1 / (p : ℝ) - 1 / (p : ℝ) ^ (m + 4) < 1 / 2 := by
    have : 0 < 1 / (p : ℝ) ^ (m + 4) := by positivity
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp1
    linarith
  have hnn : 0 ≤ 1 / (p : ℝ) - 1 / (p : ℝ) ^ (m + 4) := by
    have : 0 < 1 / (2 * (p : ℝ)) := by positivity
    linarith
  rw [norm_coe_pos_small hnn hupper]
  exact hlow

/-- **Theorem 22.1, non-precompactness.**  `γ_p` is not precompact. -/
theorem gamma_p_not_precompact (p : ℕ) (hp : 2 ≤ p) : ¬ PrecompactG (xi (Cp p)) := by
  intro h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hU : xiSet (Cp p) 1 (1 / (4 * (p : ℝ))) ∈ @nhds ℚ (xi (Cp p)) 0 :=
    (xi_nhds_hasBasis (Cp p)).mem_of_mem (xiSet_mem (Cp p) 1 one_pos _ (by positivity))
  obtain ⟨F, hF⟩ := h _ hU
  let pts : ℕ → ℚ := fun k => (p : ℚ) ^ ((k + 1) ^ 2 - 1)
  choose t ht hUt using fun k => hF (pts k)
  obtain ⟨k, j, hkj, htkj⟩ := Finite.exists_ne_map_eq_of_infinite (fun k => (⟨t k, ht k⟩ : F))
  have htt : t k = t j := congrArg Subtype.val htkj
  have key : ∀ k j : ℕ, j < k → t k = t j → False := by
    intro k j hjk htt
    have hc : p ^ ((k + 1) ^ 2) ∈ Cp p := mem_Cp.2 ⟨k + 1, rfl⟩
    have h1 : ‖xt (pts k - t k) 1 (p ^ ((k + 1) ^ 2))‖ < 1 / (4 * (p : ℝ)) := hUt k _ hc
    have h2 : ‖xt (pts j - t j) 1 (p ^ ((k + 1) ^ 2))‖ < 1 / (4 * (p : ℝ)) := hUt j _ hc
    have e : xt (pts k - pts j) 1 (p ^ ((k + 1) ^ 2)) =
        xt (pts k - t k) 1 (p ^ ((k + 1) ^ 2)) - xt (pts j - t j) 1 (p ^ ((k + 1) ^ 2)) := by
      rw [← xt_sub, htt]; congr 1; ring
    have hfar := pts_far p hp hjk
    rw [show (pts k - pts j) = ((p : ℚ) ^ ((k + 1) ^ 2 - 1)) - (p : ℚ) ^ ((j + 1) ^ 2 - 1) from rfl, e] at *
    have h3 := norm_sub_le (xt (pts k - t k) 1 (p ^ ((k + 1) ^ 2))) (xt (pts j - t j) 1 (p ^ ((k + 1) ^ 2)))
    have : 1 / (2 * (p : ℝ)) = 1 / (4 * p) + 1 / (4 * p) := by field_simp; ring
    linarith
  rcases lt_or_gt_of_ne hkj with hlt | hgt
  · exact key j k hlt htt.symm
  · exact key k j hgt htt

end NotPrecompact

end LeanCheck
