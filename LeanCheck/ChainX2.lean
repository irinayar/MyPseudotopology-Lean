import LeanCheck.ChainX1

/-!
# Directed joins and the precise greatest-member criterion
(TVGQ-v7 Lemma 11.1 `directed`, Proposition 12.1 `compatible-scalars`, Theorem 12.2 `greatest-criterion`)

Mathlib's `≤` on topologies is "finer than", and `sInf` is the join in the paper's sense.

* `directed_join_Lcls`, `directed_join_Ccls` : every nonempty directed family in `ℒ(H)` (resp. `𝒞_ℚ(H)`) has its
  join in the class;
* `compatible_scalars` : for `η` in the compatible class of `H_{f,S}`: `ℚ ⊆ C_η ⊆ M(S)`;
* `greatest_criterion` : every member has a maximal extension; and TFAE: a greatest member exists; every binary
  join of members is compatible; the maximal member is unique; `ℒ(H)` has a Mackey topology.
-/

namespace LeanCheck

open Filter Topology

section Directed

variable {G : Type*} [AddCommGroup G]

lemma directed_nhds {F : Set (TopologicalSpace G)}
    (hdir : DirectedOn (fun a b : TopologicalSpace G => b ≤ a) F) :
    DirectedOn ((fun τ : TopologicalSpace G => @nhds G τ 0) ⁻¹'o (· ≥ ·)) F := by
  intro a ha b hb
  obtain ⟨c, hc, hca, hcb⟩ := hdir a ha b hb
  exact ⟨c, hc, nhds_mono hca, nhds_mono hcb⟩

/-- **Lemma 11.1, first assertion.**  The join of a nonempty directed family in `ℒ(H)` lies in `ℒ(H)`. -/
theorem directed_join_Lcls (H : Set (G →+ Circ)) (F : Set (TopologicalSpace G)) (hne : F.Nonempty)
    (hF : F ⊆ Lcls H) (hdir : DirectedOn (fun a b : TopologicalSpace G => b ≤ a) F) :
    sInf F ∈ Lcls H := by
  obtain ⟨τ0, hτ0⟩ := hne
  have hgrp : @IsTopologicalAddGroup G (sInf F) _ := by
    rw [sInf_eq_iInf']
    exact isTopologicalAddGroup_iInf (fun a : F => (hF a.2).1)
  refine ⟨hgrp, ?_, ?_, ?_⟩
  · have hc : Continuous[sInf F, τ0] (id : G → G) :=
      continuous_iff_le_induced.mpr (by rw [@induced_id G τ0]; exact sInf_le hτ0)
    exact @T2Space.of_injective_continuous G G (sInf F) τ0 (hF hτ0).2.1 id Function.injective_id hc
  · intro V hV
    rw [nhds_sInf] at hV
    obtain ⟨τ, hτF, hτ⟩ := (Filter.mem_biInf_of_directed (directed_nhds hdir) ⟨τ0, hτ0⟩).1 hV
    obtain ⟨U, hU, hUV, hq⟩ := (hF hτF).2.2.1 V hτ
    exact ⟨U, nhds_mono (sInf_le hτF) hU, hUV, qc_mono (sInf_le hτF) hq⟩
  · intro χ
    constructor
    · intro hχ
      have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (χ 0) := by
        rw [map_zero]
        exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
      have hpre : χ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} ∈ @nhds G (sInf F) 0 :=
        (@Continuous.continuousAt G Circ (sInf F) circTop χ 0 hχ) hS
      rw [nhds_sInf] at hpre
      obtain ⟨τ, hτF, hτ⟩ := (Filter.mem_biInf_of_directed (directed_nhds hdir) ⟨τ0, hτ0⟩).1 hpre
      have hcont : @Continuous G Circ τ circTop χ := by
        letI : TopologicalSpace G := τ
        haveI : IsTopologicalAddGroup G := (hF hτF).1
        exact continuous_of_quarter_gen χ hτ (fun x hx => hx)
      exact ((hF hτF).2.2.2 χ).1 hcont
    · intro h
      exact continuous_le_dom (sInf_le hτ0) (((hF hτ0).2.2.2 χ).2 h)

variable [Module ℚ G]

/-- **Lemma 11.1, second assertion.**  The same for the rationally scalar-continuous class `𝒞_ℚ(H)`. -/
theorem directed_join_Ccls (H : Set (G →+ Circ)) (F : Set (TopologicalSpace G)) (hne : F.Nonempty)
    (hF : F ⊆ Ccls H) (hdir : DirectedOn (fun a b : TopologicalSpace G => b ≤ a) F) :
    sInf F ∈ Ccls H := by
  refine ⟨directed_join_Lcls H F hne (fun τ hτ => (hF hτ).1) hdir, fun q => ?_⟩
  rw [continuous_sInf_rng]
  intro τ hτ
  exact continuous_le_dom (sInf_le hτ) ((hF hτ).2 q)

/-- Every member of `𝒞_ℚ(H)` has a maximal extension in `𝒞_ℚ(H)` (Zorn). -/
theorem exists_maximal_ext (H : Set (G →+ Circ)) (τ : TopologicalSpace G) (hτ : τ ∈ Ccls H) :
    ∃ μ ∈ Ccls H, μ ≤ τ ∧ ∀ ν ∈ Ccls H, ν ≤ μ → μ ≤ ν := by
  let s : Set (TopologicalSpace G) := {σ | σ ∈ Ccls H ∧ σ ≤ τ}
  obtain ⟨m, hmτ, hm⟩ := zorn_ge_nonempty₀ s (fun c hcs hc y hy => by
    refine ⟨sInf c, ⟨directed_join_Ccls H c ⟨y, hy⟩ (fun z hz => (hcs hz).1) ?_, ?_⟩,
      fun z hz => sInf_le hz⟩
    · intro a ha b hb
      rcases hc.total ha hb with h | h
      · exact ⟨b, hb, h, le_rfl⟩
      · exact ⟨a, ha, le_rfl, h⟩
    · exact (sInf_le hy).trans (hcs hy).2) τ ⟨hτ, le_rfl⟩
  exact ⟨m, hm.1.1, hm.1.2, fun ν hν hνm => hm.2 ⟨hν, hνm.trans hm.1.2⟩ hνm⟩

/-- **Theorem 12.2 (`greatest-criterion`).**  For a rationally invariant character set `H` with a nonempty class
`𝒞_ℚ(H)`: every member has a maximal extension in the class, and the following are equivalent: the class has a
greatest member; every binary join of members of the class is again in the class; the class has exactly one maximal
member; `ℒ(H)` has a greatest member (a Mackey topology). -/
theorem greatest_criterion (H : Set (G →+ Circ)) (hH : RatInv H) (hne : (Ccls H).Nonempty) :
    (∀ τ ∈ Ccls H, ∃ μ ∈ Ccls H, μ ≤ τ ∧ ∀ ν ∈ Ccls H, ν ≤ μ → μ ≤ ν) ∧
    List.TFAE
      [ ∃ μ : TopologicalSpace G, μ ∈ Ccls H ∧ ∀ τ ∈ Ccls H, μ ≤ τ,
        ∀ τ₁ ∈ Ccls H, ∀ τ₂ ∈ Ccls H, τ₁ ⊓ τ₂ ∈ Ccls H,
        ∃! μ : TopologicalSpace G, μ ∈ Ccls H ∧ ∀ ν ∈ Ccls H, ν ≤ μ → μ ≤ ν,
        ∃ μ : TopologicalSpace G, μ ∈ Lcls H ∧ ∀ τ ∈ Lcls H, μ ≤ τ ] := by
  refine ⟨exists_maximal_ext H, ?_⟩
  tfae_have 1 → 2 := by
    rintro ⟨μ, hμ, hgr⟩ τ₁ h1 τ₂ h2
    obtain ⟨hg, ht, hl, hd⟩ := h1.1
    obtain ⟨hg2, ht2, hl2, hd2⟩ := h2.1
    have hmu : μ ≤ τ₁ ⊓ τ₂ := le_inf (hgr _ h1) (hgr _ h2)
    refine ⟨⟨isTopologicalAddGroup_inf hg hg2, ?_, lqc_inf _ _ hl hl2, fun χ => ?_⟩, fun q => ?_⟩
    · have hc : Continuous[τ₁ ⊓ τ₂, τ₁] (id : G → G) :=
        continuous_iff_le_induced.mpr (by rw [@induced_id G τ₁]; exact inf_le_left)
      exact @T2Space.of_injective_continuous G G (τ₁ ⊓ τ₂) τ₁ ht id Function.injective_id hc
    · constructor
      · intro h
        exact (hμ.1.2.2.2 χ).1 (continuous_le_dom hmu h)
      · intro h
        exact continuous_le_dom inf_le_left ((hd χ).2 h)
    · exact (continuous_inf_rng (t₁ := τ₁ ⊓ τ₂)).2
        ⟨continuous_le_dom inf_le_left (h1.2 q), continuous_le_dom inf_le_right (h2.2 q)⟩
  tfae_have 2 → 1 := by
    intro h
    obtain ⟨τ0, hτ0⟩ := hne
    refine ⟨sInf (Ccls H), directed_join_Ccls H _ ⟨τ0, hτ0⟩ subset_rfl ?_, fun τ hτ => sInf_le hτ⟩
    intro a ha b hb
    exact ⟨a ⊓ b, h a ha b hb, inf_le_left, inf_le_right⟩
  tfae_have 1 → 3 := by
    rintro ⟨μ, hμ, hgr⟩
    refine ⟨μ, ⟨hμ, fun ν hν hνμ => hgr ν hν⟩, fun ν ⟨hν, hmax⟩ => ?_⟩
    exact le_antisymm (hmax μ hμ (hgr ν hν)) (hgr ν hν)
  tfae_have 3 → 1 := by
    rintro ⟨μ0, ⟨hμ0, hmax0⟩, huniq⟩
    refine ⟨μ0, hμ0, fun τ hτ => ?_⟩
    obtain ⟨m, hm, hmτ, hmmax⟩ := exists_maximal_ext H τ hτ
    have : m = μ0 := huniq m ⟨hm, hmmax⟩
    rw [← this]; exact hmτ
  tfae_have 1 ↔ 4 := by
    constructor
    · rintro ⟨μ, hμ, hgr⟩
      exact ⟨μ, ((mackey_equivalence H hH).1 μ).1 ⟨hμ, hgr⟩⟩
    · rintro ⟨μ, hμ, hgr⟩
      exact ⟨μ, ((mackey_equivalence H hH).1 μ).2 ⟨hμ, hgr⟩⟩
  tfae_finish

end Directed

/-! ### Proposition 12.1: scalar restrictions throughout the compatible class -/

/-- **Proposition 12.1.**  For every `η` in the compatible TVGQ class of `H_{f,S}`:
`ℚ ⊆ C_η ⊆ M(S)`. -/
theorem compatible_scalars (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ)
    (η : TopologicalSpace ℝ) (hη : η ∈ Ccls (Hset f S : Set Chars)) :
    (∀ q : ℚ, (q : ℝ) ∈ scalarCont η) ∧ scalarCont η ⊆ scalarRing S := by
  refine ⟨fun q => ?_, fun r hr a ha => ?_⟩
  · have := hη.2 q
    rw [mq_real] at this
    exact this
  · have hmem : (pfHom f a : Chars) ∈ (Hset f S : Set Chars) :=
      ⟨0, a, ha, fun x => by simp [pfHom_apply, chiH]⟩
    have hc : @Continuous ℝ Circ η circTop (pfHom f a) := (hη.1.2.2.2 _).2 hmem
    have hc2 : @Continuous ℝ Circ η circTop ((pfHom f a : Chars) ∘ fun x : ℝ => r * x) :=
      @Continuous.comp ℝ ℝ Circ η η circTop _ _ hc hr
    have hmem2 := (hη.1.2.2.2 ((pfHom f a).comp (AddMonoidHom.mulLeft r))).1 hc2
    obtain ⟨c', a', ha', h'⟩ := hmem2
    have heq : ∀ x, chiH f 0 (a * r) x = chiH f c' a' x := fun x => by
      rw [← h' x]
      simp [pfHom_apply, chiH, mul_assoc]
    have := chiH_unique f u hu 0 (a * r) c' a' heq
    rw [this.2]; exact ha'

end LeanCheck
