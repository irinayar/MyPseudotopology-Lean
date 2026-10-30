import LeanCheck.ChainU3

/-!
# Directed joins and the greatest-member criterion
(HamelCharactersTVG_v18 Proposition 18.1 `prop:directed-v8`, Proposition 24.1 `prop:scalar-join-v10`;
 TVGQ analogues)

For an abelian group `G`, a set `H` of characters and a set `S` of scalar maps `G → G`, `Kcls H S` is the class of
Hausdorff locally quasi-convex group topologies with continuous character group exactly `H` in which all maps in `S`
are continuous.  (`𝒞_f` is `Kcls H_f {x ↦ a x}`; `ℒ_f` is `Kcls H_f ∅`.)  In Mathlib's order `τ ≤ τ'` means that `τ`
is finer, so the paper's join is `⊓` / `⨅`, and "greatest" means `μ ≤ τ` for all `τ`.

* `directed_join_mem`      : a nonempty directed join of members is a member;
* `exists_minimal_ext`     : every member has a maximal extension in the class (Zorn);
* `greatest_iff_binary`    : a greatest member exists ⟺ every binary join is a member ⟺ there is a unique maximal member;
* `binary_join_mem_iff`    : (Prop. 24.1) the join of two members is a Hausdorff lqc topology with all scalars continuous
                             and all of `H` continuous, and it is a member iff it has no additional characters.
-/

namespace LeanCheck

open Filter Topology

section Kcls

variable {G : Type*} [AddCommGroup G]

/-- Hausdorff locally quasi-convex group topologies with exactly the characters `H` and all scalar maps `S`
continuous. -/
def Kcls (H : Set (G →+ Circ)) (S : Set (G → G)) : Set (TopologicalSpace G) :=
  {τ | @IsTopologicalAddGroup G τ _ ∧ @T2Space G τ ∧ LocQC τ ∧
    (∀ χ : G →+ Circ, @Continuous G Circ τ circTop χ ↔ χ ∈ H) ∧ ∀ s ∈ S, Continuous[τ, τ] s}

lemma t2_of_le' {t t' : TopologicalSpace G} (h : t ≤ t') (ht' : @T2Space G t') : @T2Space G t :=
  @T2Space.of_injective_continuous G G t t' _ id Function.injective_id (continuous_id_of_le h)

lemma dil_iInf {ι : Type*} (τ : ι → TopologicalSpace G) (s : G → G) (h : ∀ i, Continuous[τ i, τ i] s) :
    Continuous[⨅ i, τ i, ⨅ i, τ i] s := by
  rw [continuous_iff_le_induced, induced_iInf]
  exact le_iInf fun i => (iInf_le τ i).trans (continuous_iff_le_induced.1 (h i))

lemma dil_inf (τ₁ τ₂ : TopologicalSpace G) (s : G → G) (h₁ : Continuous[τ₁, τ₁] s)
    (h₂ : Continuous[τ₂, τ₂] s) : Continuous[τ₁ ⊓ τ₂, τ₁ ⊓ τ₂] s := by
  rw [continuous_iff_le_induced, induced_inf]
  exact le_inf (inf_le_left.trans (continuous_iff_le_induced.1 h₁))
    (inf_le_right.trans (continuous_iff_le_induced.1 h₂))

/-- A character continuous for a directed infimum of group topologies is continuous for one of them. -/
lemma cont_of_directed {ι : Type*} [Nonempty ι] (τ : ι → TopologicalSpace G) (hdir : Directed (· ≥ ·) τ)
    (hgrp : ∀ i, @IsTopologicalAddGroup G (τ i) _) (χ : G →+ Circ)
    (hc : @Continuous G Circ (⨅ i, τ i) circTop χ) : ∃ k, @Continuous G Circ (τ k) circTop χ := by
  have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (χ 0) := by
    rw [map_zero]
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  have hpre : χ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} ∈ @nhds G (⨅ i, τ i) 0 :=
    (@Continuous.continuousAt G Circ (⨅ i, τ i) _ χ 0 hc) hS
  rw [nhds_iInf] at hpre
  have hdirF : Directed (· ≥ ·) (fun i => @nhds G (τ i) 0) := by
    intro i j
    obtain ⟨k, hk1, hk2⟩ := hdir i j
    exact ⟨k, nhds_mono hk1, nhds_mono hk2⟩
  rw [Filter.mem_iInf_of_directed hdirF] at hpre
  obtain ⟨k, hk⟩ := hpre
  refine ⟨k, ?_⟩
  letI : TopologicalSpace G := τ k
  haveI : IsTopologicalAddGroup G := hgrp k
  exact continuous_of_quarter_gen χ hk (fun x hx => hx)

/-- A nonempty directed join of members of `Kcls H S` is a member. -/
theorem directed_join_mem (H : Set (G →+ Circ)) (S : Set (G → G)) {ι : Type*} [Nonempty ι]
    (τ : ι → TopologicalSpace G) (hdir : Directed (· ≥ ·) τ) (hτ : ∀ i, τ i ∈ Kcls H S) :
    (⨅ i, τ i) ∈ Kcls H S := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  refine ⟨isTopologicalAddGroup_iInf (fun i => (hτ i).1), t2_of_le' (iInf_le τ i0) (hτ i0).2.1,
    lqc_iInf τ (fun i => (hτ i).2.2.1), fun χ => ⟨fun hc => ?_, fun hχ => ?_⟩,
    fun s hs => dil_iInf τ s (fun i => (hτ i).2.2.2.2 s hs)⟩
  · obtain ⟨k, hk⟩ := cont_of_directed τ hdir (fun i => (hτ i).1) χ hc
    exact ((hτ k).2.2.2.1 χ).1 hk
  · exact continuous_le_dom (iInf_le τ i0) (((hτ i0).2.2.2.1 χ).2 hχ)

/-- Every member of `Kcls H S` has a maximal extension in `Kcls H S` (Zorn's lemma). -/
theorem exists_minimal_ext (H : Set (G →+ Circ)) (S : Set (G → G)) (η : TopologicalSpace G)
    (hη : η ∈ Kcls H S) : ∃ m : TopologicalSpace G, m ≤ η ∧ Minimal (· ∈ Kcls H S) m := by
  refine zorn_ge_nonempty₀ (Kcls H S) (fun c hcs hc y hy => ?_) η hη
  have hne : Nonempty c := ⟨⟨y, hy⟩⟩
  have hdir : Directed (· ≥ ·) (fun z : c => (z : TopologicalSpace G)) := by
    intro a b
    rcases hc.total a.2 b.2 with h | h
    · exact ⟨b, h, le_rfl⟩
    · exact ⟨a, le_rfl, h⟩
  refine ⟨⨅ z : c, (z : TopologicalSpace G),
    directed_join_mem H S (fun z : c => (z : TopologicalSpace G)) hdir (fun z => hcs z.2), ?_⟩
  intro z hz
  exact iInf_le (fun z : c => (z : TopologicalSpace G)) ⟨z, hz⟩

/-- **Proposition 18.1.**  Let `Kcls H S` be nonempty.  The following are equivalent: a greatest member exists;
every binary join of members is a member; there is exactly one maximal member. -/
theorem greatest_iff_binary (H : Set (G →+ Circ)) (S : Set (G → G)) (hne : (Kcls H S).Nonempty) :
    ((∃ μ ∈ Kcls H S, ∀ τ ∈ Kcls H S, μ ≤ τ) ↔ ∀ τ₁ ∈ Kcls H S, ∀ τ₂ ∈ Kcls H S, τ₁ ⊓ τ₂ ∈ Kcls H S) ∧
    ((∃ μ ∈ Kcls H S, ∀ τ ∈ Kcls H S, μ ≤ τ) ↔ ∃! m : TopologicalSpace G, Minimal (· ∈ Kcls H S) m) := by
  -- (a) ⇒ (b)
  have hab : (∃ μ ∈ Kcls H S, ∀ τ ∈ Kcls H S, μ ≤ τ) →
      ∀ τ₁ ∈ Kcls H S, ∀ τ₂ ∈ Kcls H S, τ₁ ⊓ τ₂ ∈ Kcls H S := by
    rintro ⟨μ, hμ, hgr⟩ τ₁ h₁ τ₂ h₂
    have hle : μ ≤ τ₁ ⊓ τ₂ := le_inf (hgr _ h₁) (hgr _ h₂)
    refine ⟨isTopologicalAddGroup_inf h₁.1 h₂.1, t2_of_le' inf_le_left h₁.2.1, lqc_inf τ₁ τ₂ h₁.2.2.1 h₂.2.2.1,
      fun χ => ⟨fun hc => ?_, fun hχ => ?_⟩, fun s hs => dil_inf τ₁ τ₂ s (h₁.2.2.2.2 s hs) (h₂.2.2.2.2 s hs)⟩
    · exact (hμ.2.2.2.1 χ).1 (continuous_le_dom hle hc)
    · exact continuous_le_dom (inf_le_left) ((h₁.2.2.2.1 χ).2 hχ)
  -- (b) ⇒ (a)
  have hba : (∀ τ₁ ∈ Kcls H S, ∀ τ₂ ∈ Kcls H S, τ₁ ⊓ τ₂ ∈ Kcls H S) →
      ∃ μ ∈ Kcls H S, ∀ τ ∈ Kcls H S, μ ≤ τ := by
    intro hbin
    obtain ⟨τ0, hτ0⟩ := hne
    haveI : Nonempty (Kcls H S) := ⟨⟨τ0, hτ0⟩⟩
    have hdir : Directed (· ≥ ·) (fun z : Kcls H S => (z : TopologicalSpace G)) := by
      intro a b
      exact ⟨⟨a.1 ⊓ b.1, hbin _ a.2 _ b.2⟩, inf_le_left, inf_le_right⟩
    exact ⟨⨅ z : Kcls H S, (z : TopologicalSpace G),
      directed_join_mem H S (fun z : Kcls H S => (z : TopologicalSpace G)) hdir (fun z => z.2),
      fun τ hτ => iInf_le (fun z : Kcls H S => (z : TopologicalSpace G)) ⟨τ, hτ⟩⟩
  -- (a) ⇒ (c)
  have hac : (∃ μ ∈ Kcls H S, ∀ τ ∈ Kcls H S, μ ≤ τ) → ∃! m : TopologicalSpace G, Minimal (· ∈ Kcls H S) m := by
    rintro ⟨μ, hμ, hgr⟩
    refine ⟨μ, ⟨hμ, fun τ hτ hτμ => hgr τ hτ⟩, fun m hm => ?_⟩
    exact le_antisymm (hm.2 hμ (hgr m hm.1)) (hgr m hm.1)
  -- (c) ⇒ (a)
  have hca : (∃! m : TopologicalSpace G, Minimal (· ∈ Kcls H S) m) → ∃ μ ∈ Kcls H S, ∀ τ ∈ Kcls H S, μ ≤ τ := by
    rintro ⟨m, hm, huniq⟩
    refine ⟨m, hm.1, fun τ hτ => ?_⟩
    obtain ⟨m', hm'le, hm'min⟩ := exists_minimal_ext H S τ hτ
    have : m' = m := huniq m' hm'min
    rw [← this]; exact hm'le
  exact ⟨⟨fun h => hab h, hba⟩, ⟨hac, hca⟩⟩

/-- **Proposition 24.1.**  The join of two members is always a Hausdorff locally quasi-convex group topology with all
scalar maps continuous and all of `H` continuous; it is a member iff it has no additional continuous character. -/
theorem binary_join_mem_iff (H : Set (G →+ Circ)) (S : Set (G → G)) (τ₁ τ₂ : TopologicalSpace G)
    (h₁ : τ₁ ∈ Kcls H S) (h₂ : τ₂ ∈ Kcls H S) :
    (@IsTopologicalAddGroup G (τ₁ ⊓ τ₂) _ ∧ @T2Space G (τ₁ ⊓ τ₂) ∧ LocQC (τ₁ ⊓ τ₂) ∧
      (∀ χ ∈ H, @Continuous G Circ (τ₁ ⊓ τ₂) circTop χ) ∧ ∀ s ∈ S, Continuous[τ₁ ⊓ τ₂, τ₁ ⊓ τ₂] s) ∧
    (τ₁ ⊓ τ₂ ∈ Kcls H S ↔ ∀ χ : G →+ Circ, @Continuous G Circ (τ₁ ⊓ τ₂) circTop χ → χ ∈ H) := by
  have hcont : ∀ χ ∈ H, @Continuous G Circ (τ₁ ⊓ τ₂) circTop χ := fun χ hχ =>
    continuous_le_dom inf_le_left ((h₁.2.2.2.1 χ).2 hχ)
  have hgrp := isTopologicalAddGroup_inf h₁.1 h₂.1
  have ht2 := t2_of_le' (inf_le_left : τ₁ ⊓ τ₂ ≤ τ₁) h₁.2.1
  have hlqc := lqc_inf τ₁ τ₂ h₁.2.2.1 h₂.2.2.1
  have hdil : ∀ s ∈ S, Continuous[τ₁ ⊓ τ₂, τ₁ ⊓ τ₂] s := fun s hs =>
    dil_inf τ₁ τ₂ s (h₁.2.2.2.2 s hs) (h₂.2.2.2.2 s hs)
  refine ⟨⟨hgrp, ht2, hlqc, hcont, hdil⟩, ⟨fun h χ hc => (h.2.2.2.1 χ).1 hc, fun h => ?_⟩⟩
  exact ⟨hgrp, ht2, hlqc, fun χ => ⟨h χ, fun hχ => hcont χ hχ⟩, hdil⟩

end Kcls

end LeanCheck
