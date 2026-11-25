import LeanCheck.PVGFinitePiece
import LeanCheck.PVGNotGroupA
import LeanCheck.PVGGammaInXi

/-!
# PVG: the topological modification for the interval-free ideal is not a group topology (Lean check)

Scope. `ξ₀ = ξ_{τ_B, I₀}` for the ideal `I₀` of subsets of the sets `F + a₁S + … + a_kS`, `F` finite.

* `I0_isIdeal` : `I₀` is an admissible ideal;
* `Eall_compl_open0` : the set `ℝ \ E` is open in the modification of `ξ₀`;
* `modTop0_not_continuousAdd` : addition is not continuous for that modification (the argument of `modTop_not_continuousAdd`
  with the members `S - S` and `c S - c S` of `I₀`);
* `intervalFree_strict` : with `τ_D` of `PVGFinitePiece`, `τ_B ⊂ τ_D ⊂ τ₀` strictly, where `τ₀` is the modification. The box
  topology of the article is not formalized.

In Mathlib's order `t₁ ≤ t₂` means that `t₁` is finer. A Lean proof verifies its formal statement under its hypotheses; the
correspondence with the article requires mathematical review.
-/

open Filter Topology Set Pointwise

namespace PVG
namespace Lac

open Q95

/-- `I₀` satisfies the ideal axioms. -/
theorem I0_isIdeal : IsIdeal I0 where
  mono := fun {A B} hA hBA => by
    obtain ⟨F, hF, l, h⟩ := hA
    exact ⟨F, hF, l, hBA.trans h⟩
  union := fun {A B} hA hB => by
    obtain ⟨F, hF, l, h⟩ := hA
    obtain ⟨F', hF', l', h'⟩ := hB
    refine ⟨F ∪ F', hF.union hF', l ++ l', fun z hz => ?_⟩
    rcases hz with hz | hz
    · obtain ⟨y, hy, σ, hσ, rfl⟩ := h hz
      exact ⟨y, Or.inl hy, σ, sumSet_append_left l l' hσ, rfl⟩
    · obtain ⟨y, hy, σ, hσ, rfl⟩ := h' hz
      exact ⟨y, Or.inr hy, σ, sumSet_append_right l l' hσ, rfl⟩
  single := fun x => ⟨{x}, finite_singleton x, [], fun z hz => ⟨x, rfl, 0, rfl, by
    rw [mem_singleton_iff] at hz; simp [hz]⟩⟩
  ne_univ := fun h => IS_isIdeal.ne_univ (I0_subset_IS h)
  add := fun {A B} hA hB => by
    obtain ⟨F, hF, l, h⟩ := hA
    obtain ⟨F', hF', l', h'⟩ := hB
    refine ⟨F + F', hF.add hF', l ++ l', fun z hz => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    obtain ⟨y, hy, σ, hσ, rfl⟩ := h ha
    obtain ⟨y', hy', σ', hσ', rfl⟩ := h' hb
    exact ⟨y + y', add_mem_add hy hy', σ + σ', sumSet_append_add l l' σ σ' hσ hσ', by ring⟩
  smul := fun a {A} hA => by
    obtain ⟨F, hF, l, h⟩ := hA
    refine ⟨(fun y => a * y) '' F, hF.image _, l.map (fun c => a * c), fun z hz => ?_⟩
    obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.1 hz
    obtain ⟨y, hy, σ, hσ, rfl⟩ := h hw
    exact ⟨a * y, ⟨y, hy, rfl⟩, a * σ, sumSet_smul_mem a l σ hσ, by simp [smul_eq_mul]; ring⟩

lemma Jc_mem_I0 (c : ℝ) : Jc c ∈ I0 := by
  refine ⟨{0}, finite_singleton 0, [c, -c], ?_⟩
  rintro z ⟨a, b, ha, hb, rfl⟩
  refine ⟨0, rfl, c * sS a + ((-c) * sS b + 0), ?_, by ring⟩
  refine ⟨c * sS a, ⟨sS a, Sset_mem_pos ha, rfl⟩, (-c) * sS b + 0, ?_, rfl⟩
  exact ⟨(-c) * sS b, ⟨sS b, Sset_mem_pos hb, rfl⟩, 0, rfl, rfl⟩

/-- `ℝ \ E` is open in the modification of `ξ_{τ_B, I₀}`. -/
theorem Eall_compl_open0 : @IsOpen ℝ (modTop (@xiConv ℝ bohrTop I0)) Eallᶜ := by
  have hmem := @mem_modTop_iff ℝ _ _ bohrTop bohr_isTopologicalAddGroup bohr_constSMul I0 Eallᶜ
  refine hmem.2 ?_
  intro J hJ
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx1, hx2⟩
  exact hx2 (closure_J_Eall (I0_subset_IS hJ) hx1)

/-- Addition is not continuous for the modification of `ξ_{τ_B, I₀}`. -/
theorem modTop0_not_continuousAdd : ¬ @ContinuousAdd ℝ (modTop (@xiConv ℝ bohrTop I0)) _ := by
  intro hca
  letI τ : TopologicalSpace ℝ := modTop (@xiConv ℝ bohrTop I0)
  have hU : IsOpen Eallᶜ := Eall_compl_open0
  have hcont : Continuous (fun p : ℝ × ℝ => p.1 + p.2) := hca.continuous_add
  have hpre := hcont.isOpen_preimage Eallᶜ hU
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' Eallᶜ := by
    simpa using zero_notMem_Eall
  obtain ⟨V1, V2, hV1, hV2, h01, h02, hsub⟩ := isOpen_prod_iff.1 hpre 0 0 h00
  set V : Set ℝ := V1 ∩ V2 with hVdef
  have hVopen : IsOpen V := hV1.inter hV2
  have h0V : (0 : ℝ) ∈ V := ⟨h01, h02⟩
  have hVV : ∀ u ∈ V, ∀ w ∈ V, u + w ∈ Eallᶜ := fun u hu w hw => hsub (Set.mk_mem_prod hu.1 hw.2)
  -- a free ultrafilter and the points `L(W₀ - k)`
  obtain ⟨W0, hW0⟩ : ∃ W0 : Ultrafilter ℕ, Free W0 := ⟨Ultrafilter.of Filter.cofinite, Ultrafilter.of_le _⟩
  set p : ℕ → K := fun k => L sS (shiftU k W0) with hp
  -- the Bohr neighbourhood for `J₀ = J_1`
  obtain ⟨Y0, hY0, h0Y0, hY0V⟩ := local_bohrI I0 hVopen h0V (Jc_mem_I0 1)
  obtain ⟨κ, hκ⟩ := exists_clusterPt_of_compactSpace (Filter.map p atTop)
  have hsub0 : ∃ V1 ∈ 𝓝 κ, ∀ a ∈ V1, ∀ c ∈ V1, a - c ∈ Y0 := by
    have h1 : Tendsto (fun q : K × K => q.1 - q.2) (𝓝 (κ, κ)) (𝓝 (κ - κ)) :=
      continuous_sub.tendsto (κ, κ)
    rw [sub_self] at h1
    have h2 := h1 (hY0.mem_nhds (by simpa [e_zero] using h0Y0))
    rw [nhds_prod_eq, Filter.mem_map, mem_prod_self_iff] at h2
    obtain ⟨V1, hV1, hV1sub⟩ := h2
    exact ⟨V1, hV1, fun a ha c hc => hV1sub (Set.mk_mem_prod ha hc)⟩
  obtain ⟨Vk, hVk, hVkY⟩ := hsub0
  have hfreq : ∃ᶠ j in atTop, p j ∈ Vk := (mapClusterPt_iff_frequently.1 hκ) Vk hVk
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨k, hk1, hkV⟩ := hfreq 1
  obtain ⟨l, hl, hlV⟩ := hfreq (k + 1)
  have hl1 : 1 ≤ l := by omega
  have hkl : k ≠ l := by omega
  have hpkl : p k - p l ∈ Y0 := hVkY _ hkV _ hlV
  -- the index `i` and the Bohr neighbourhood for `J_{c_i}`
  set i : ℕ := max (max k l) 2 with hi
  have hi2 : 2 ≤ i := le_max_right _ _
  have hki : k ≤ i := le_trans (le_max_left _ _) (le_max_left _ _)
  have hli : l ≤ i := le_trans (le_max_right _ _) (le_max_left _ _)
  set c : ℝ := cc i with hc
  obtain ⟨Yi, hYi, h0Yi, hYiV⟩ := local_bohrI I0 hVopen h0V (Jc_mem_I0 c)
  have h0Yi' : (0 : K) ∈ Yi := by simpa [e_zero] using h0Yi
  have h0Y0' : (0 : K) ∈ Y0 := by simpa [e_zero] using h0Y0
  -- convergence along `W₀`
  have hpl : ∀ l' : ℕ, Tendsto (fun m => e (sS (m - l'))) (W0 : Filter ℕ) (𝓝 (p l')) :=
    fun l' => tendsto_e_comp sS W0 (fun m => m - l')
  have hL3 : Tendsto (fun m => e (sS m)) (W0 : Filter ℕ) (𝓝 (L sS W0)) := tendsto_L sS W0
  have hsm : ∀ κ : K, Tendsto (fun κ' : K => c • κ') (𝓝 κ) (𝓝 (c • κ)) :=
    fun κ => (continuous_smul_const c).tendsto κ
  -- first coordinate `n`
  have hB1 : ∀ᶠ n in (W0 : Filter ℕ), e (sS (n - k)) - p l ∈ Y0 := by
    have := (hpl k).sub_const (p l)
    exact this.eventually (hY0.mem_nhds hpkl)
  have hB2 : ∀ᶠ n in (W0 : Filter ℕ), c • e (sS n) - c • L sS W0 ∈ Yi := by
    have h1 := ((hsm _).comp hL3).sub_const (c • L sS W0)
    rw [sub_self] at h1
    exact h1.eventually (hYi.mem_nhds h0Yi')
  have hB3 : ∀ᶠ n in (W0 : Filter ℕ), MM i ≤ n := by
    refine hW0 (Filter.mem_cofinite.2 ((Set.finite_Iio (MM i)).subset ?_))
    intro n hn
    simpa using hn
  obtain ⟨n, hn1, hn2, hn3⟩ : ∃ n, e (sS (n - k)) - p l ∈ Y0 ∧ c • e (sS n) - c • L sS W0 ∈ Yi ∧
      MM i ≤ n := ((hB1.and hB2).and hB3).exists.imp fun n h => ⟨h.1.1, h.1.2, h.2⟩
  -- second coordinate `m`
  have hC1 : ∀ᶠ m in (W0 : Filter ℕ), e (sS (n - k)) - e (sS (m - l)) ∈ Y0 := by
    have := (tendsto_const_nhds (x := e (sS (n - k)))).sub (hpl l)
    exact this.eventually (hY0.mem_nhds hn1)
  have hC2 : ∀ᶠ m in (W0 : Filter ℕ), c • e (sS n) - c • e (sS m) ∈ Yi := by
    have := (tendsto_const_nhds (x := c • e (sS n))).sub ((hsm _).comp hL3)
    exact this.eventually (hYi.mem_nhds hn2)
  have hC3 : ∀ᶠ m in (W0 : Filter ℕ), n < m := by
    refine hW0 (Filter.mem_cofinite.2 ((Set.finite_Iic n).subset ?_))
    intro m hm
    simpa using hm
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m, e (sS (n - k)) - e (sS (m - l)) ∈ Y0 ∧
      c • e (sS n) - c • e (sS m) ∈ Yi ∧ n < m :=
    ((hC1.and hC2).and hC3).exists.imp fun m h => ⟨h.1.1, h.1.2, h.2⟩
  have hMM : MM i = 3 * i + 4 := rfl
  have hn1' : 1 ≤ n - k := by omega
  have hm1' : 1 ≤ m - l := by omega
  have hnpos : 1 ≤ n := by omega
  have hmpos : 1 ≤ m := by omega
  -- `u` and `w` lie in `V`
  have hu : sS (n - k) - sS (m - l) ∈ V := by
    have h1 : (1 : ℝ) * (sS (n - k) - sS (m - l)) ∈ Jc 1 := ⟨n - k, m - l, hn1', hm1', rfl⟩
    have h2 : e ((1 : ℝ) * (sS (n - k) - sS (m - l))) ∈ Y0 := by
      rw [one_mul, e_sub]; exact hm1
    simpa using hY0V _ h1 h2
  have hw : c * (sS n - sS m) ∈ V := by
    have h1 : c * (sS n - sS m) ∈ Jc c := ⟨n, m, hnpos, hmpos, rfl⟩
    have h2 : e (c * (sS n - sS m)) ∈ Yi := by
      rw [e_mul_sub]; exact hm2
    exact hYiV _ h1 h2
  have hyE : sS (n - k) - sS (m - l) + c * (sS n - sS m) ∈ Eall :=
    ⟨i, hi2, ⟨k, l, n, m, hk1, hki, hl1, hli, hkl, hn3, hm3, rfl⟩⟩
  exact hVV _ hu _ hw hyE


/-- `τ_B ⊂ τ_D ⊂ τ₀`, both inclusions strict (in Mathlib's order the finer topology is the smaller one). -/
theorem intervalFree_strict :
    modTop (@xiConv ℝ bohrTop I0) ≤ discTop ∧ modTop (@xiConv ℝ bohrTop I0) ≠ discTop ∧
      discTop ≤ bohrTop ∧ discTop ≠ bohrTop := by
  refine ⟨fun U hU => ?_, fun h => ?_, discTop_le_bohr, discTop_ne_bohr⟩
  · exact topology_le_modTop I0 I0_isIdeal discTop (fun J hJ => finitePiece_trace hJ) hU
  · apply modTop0_not_continuousAdd
    rw [h]
    exact discTop_group.toContinuousAdd

end Lac
end PVG
