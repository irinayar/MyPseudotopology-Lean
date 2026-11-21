import Mathlib
import LeanCheck.PGNullFilters

/-!
# PG: the pseudotopological group of a topology and an ideal (Lean check)

Scope. Section 3 of `PG_v1`/`PG_v2`. Let `G` be an abelian group with a Hausdorff group topology `β` and `I` a family of
subsets of `G` with (I1)-(I5) (`AdmIdeal`). The relation `xi I F x` ("`F` is proper, contains the `β`-neighbourhoods of `x`
and has a member in `I`") is

* `isPGConv_xi` : a pseudotopological group convergence in the sense of `PGNullFilters` (properties P1-P3, addition,
  negation), Proposition 3.2;
* `xi_hausdorff` : Hausdorff (Proposition 3.2);
* `Vxi` : the filter `V_ξ(x)` (intersection of the filters converging to `x`), `Vxi_eq_map` : `V_ξ(x) = x + V_ξ(0)`
  (Lemma 3.4), `pretopological_iff` : `ξ` is pretopological iff `V_ξ(0) → 0`;
* `pretopological_zero_iff` : Theorem 3.5 (criterion: `V_ξ(0) → 0` iff there is `A ∈ I` with `0 ∉ cl(I' \ A)` for all `I' ∈ I`);
* `not_pretopological_of_recipe` : Corollary 3.6;
* `isOpenXi_iff` : Proposition 3.7 (description of the topological modification), `isOpen_isOpenXi` : every `β`-open set is open
  in the modification.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

variable {G : Type*} [AddCommGroup G]

/-- The conditions (I1)-(I5) of Definition 3.1 on a family `I` of subsets of `G`. -/
structure AdmIdeal (I : Set (Set G)) : Prop where
  sub : ∀ A ∈ I, ∀ B : Set G, B ⊆ A → B ∈ I
  union : ∀ A ∈ I, ∀ B ∈ I, A ∪ B ∈ I
  single : ∀ x : G, ({x} : Set G) ∈ I
  proper : (Set.univ : Set G) ∉ I
  add : ∀ A ∈ I, ∀ B ∈ I, Set.image2 (· + ·) A B ∈ I
  neg : ∀ A ∈ I, (fun x : G => -x) '' A ∈ I

theorem AdmIdeal.empty_mem {I : Set (Set G)} (hI : AdmIdeal I) : (∅ : Set G) ∈ I :=
  hI.sub _ (hI.single 0) _ (Set.empty_subset _)

variable [TopologicalSpace G]

/-- `F → x` for the PG of the topology and the ideal `I`. -/
def xi (I : Set (Set G)) (F : Filter G) (x : G) : Prop :=
  F.NeBot ∧ F ≤ 𝓝 x ∧ ∃ A ∈ I, A ∈ F

theorem xi_pure {I : Set (Set G)} (hI : AdmIdeal I) (x : G) : xi I (pure x) x :=
  ⟨inferInstance, pure_le_nhds x, {x}, hI.single x, Set.mem_singleton x⟩

theorem xi_mono {I : Set (Set G)} {F H : Filter G} {x : G} (hF : xi I F x) (hle : H ≤ F)
    (hne : H.NeBot) : xi I H x := by
  obtain ⟨_, h1, A, hA, hAF⟩ := hF
  exact ⟨hne, hle.trans h1, A, hA, hle hAF⟩

theorem xi_ultra {I : Set (Set G)} (hI : AdmIdeal I) {F : Filter G} {x : G} (hne : F.NeBot)
    (hU : ∀ U : Ultrafilter G, (U : Filter G) ≤ F → xi I U x) : xi I F x := by
  refine ⟨hne, ?_, ?_⟩
  · rw [Filter.le_iff_ultrafilter]
    intro U hU'
    exact (hU U hU').2.1
  · by_contra hno
    push_neg at hno
    let K : Filter G := Filter.comk (fun s => s ∈ I) hI.empty_mem
      (fun t ht s hs => hI.sub t ht s hs) (fun s hs t ht => hI.union s hs t ht)
    have hK : ∀ s : Set G, s ∈ K ↔ sᶜ ∈ I := fun s => Filter.mem_comk
    have hFK : (F ⊓ K).NeBot := by
      rw [Filter.inf_neBot_iff]
      intro s hs t ht
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hsub : s ⊆ tᶜ := by
        intro y hy hyt
        have : y ∈ s ∩ t := ⟨hy, hyt⟩
        rw [hemp] at this
        exact this
      exact hno s (hI.sub _ ((hK t).1 ht) s hsub) hs
    let U : Ultrafilter G := Ultrafilter.of (F ⊓ K)
    have hUle : (U : Filter G) ≤ F ⊓ K := Ultrafilter.of_le _
    have hUF : (U : Filter G) ≤ F := hUle.trans inf_le_left
    have hUK : (U : Filter G) ≤ K := hUle.trans inf_le_right
    obtain ⟨_, _, A, hA, hAU⟩ := hU U hUF
    have hAc : Aᶜ ∈ K := (hK Aᶜ).2 (by simpa using hA)
    have hAcU : Aᶜ ∈ (U : Filter G) := hUK hAc
    have hem : (∅ : Set G) ∈ (U : Filter G) := by
      have := Filter.inter_mem hAU hAcU
      simpa using this
    exact (U : Filter G).empty_notMem hem

variable [IsTopologicalAddGroup G]

theorem xi_add {I : Set (Set G)} (hI : AdmIdeal I) {F H : Filter G} {x y : G}
    (hF : xi I F x) (hH : xi I H y) : xi I (Filter.map₂ (· + ·) F H) (x + y) := by
  obtain ⟨hFn, hF1, A, hA, hAF⟩ := hF
  obtain ⟨hHn, hH1, B, hB, hBH⟩ := hH
  refine ⟨hFn.map₂ hHn, ?_, Set.image2 (· + ·) A B, hI.add A hA B hB, Filter.image2_mem_map₂ hAF hBH⟩
  have ht : Tendsto (fun p : G × G => p.1 + p.2) (F ×ˢ H) (𝓝 (x + y)) := by
    have h1 : Tendsto (fun p : G × G => p.1) (F ×ˢ H) (𝓝 x) := tendsto_fst.mono_right hF1
    have h2 : Tendsto (fun p : G × G => p.2) (F ×ˢ H) (𝓝 y) := tendsto_snd.mono_right hH1
    exact h1.add h2
  rw [← Filter.map_prod_eq_map₂]
  exact ht

theorem xi_neg {I : Set (Set G)} (hI : AdmIdeal I) {F : Filter G} {x : G}
    (hF : xi I F x) : xi I (Filter.map (fun z : G => -z) F) (-x) := by
  obtain ⟨hFn, hF1, A, hA, hAF⟩ := hF
  refine ⟨inferInstance, ?_, _, hI.neg A hA, Filter.image_mem_map hAF⟩
  have : Tendsto (fun z : G => -z) F (𝓝 (-x)) := (continuous_neg.tendsto x).mono_left hF1
  exact this

/-- Proposition 3.2: the PG convergence of an admissible pair. -/
theorem isPGConv_xi {I : Set (Set G)} (hI : AdmIdeal I) : IsPGConv (xi I : Filter G → G → Prop) where
  ne := fun F x hF => hF.1
  p1 := xi_pure hI
  p2 := fun F H x hF hle hne => xi_mono hF hle hne
  p3 := fun F x hne hU => xi_ultra hI hne hU
  add := fun F H x y hF hH => xi_add hI hF hH
  neg := fun F x hF => xi_neg hI hF

variable [T2Space G]

/-- Proposition 3.2: Hausdorff. -/
theorem xi_hausdorff {I : Set (Set G)} {F : Filter G} {x y : G} (hx : xi I F x) (hy : xi I F y) :
    x = y := by
  have := hx.1
  exact tendsto_nhds_unique (f := id) hx.2.1 hy.2.1

/-! ### Translation, the filter `V_ξ(x)`, and the pretopology criterion -/

/-- `F → x` iff `F - x → 0` (Proposition 2.6 applied to `ξ`). -/
theorem xi_iff_sub {I : Set (Set G)} (hI : AdmIdeal I) (F : Filter G) (x : G) :
    xi I F x ↔ xi I (Filter.map (fun y => y - x) F) 0 :=
  conv_iff_of_conv (isPGConv_xi hI) F x

theorem xi_map_add {I : Set (Set G)} (hI : AdmIdeal I) {F : Filter G} (x : G)
    (hF : xi I F 0) : xi I (Filter.map (fun y => y + x) F) x := by
  rw [xi_iff_sub hI, Filter.map_map]
  have : ((fun y : G => y - x) ∘ fun y => y + x) = id := by
    funext y; simp
  rw [this, Filter.map_id]
  exact hF

/-- `V_ξ(x)`, the intersection of the filters converging to `x`. -/
def Vxi (I : Set (Set G)) (x : G) : Filter G := sSup {F : Filter G | xi I F x}

theorem mem_Vxi {I : Set (Set G)} {x : G} {A : Set G} :
    A ∈ Vxi I x ↔ ∀ F : Filter G, xi I F x → A ∈ F := by
  unfold Vxi
  rw [Filter.mem_sSup]
  rfl

/-- Lemma 3.4: `V_ξ(x) = x + V_ξ(0)`. -/
theorem Vxi_eq_map {I : Set (Set G)} (hI : AdmIdeal I) (x : G) :
    Vxi I x = Filter.map (fun y => y + x) (Vxi I 0) := by
  ext s
  rw [Filter.mem_map, mem_Vxi, mem_Vxi]
  constructor
  · intro h F' hF'
    have := h (Filter.map (fun y => y + x) F') (xi_map_add hI x hF')
    exact this
  · intro h F hF
    have h1 := h (Filter.map (fun y => y - x) F) ((xi_iff_sub hI F x).1 hF)
    have e : (fun y : G => y - x) ⁻¹' ((fun y : G => y + x) ⁻¹' s) = s := by
      ext y; simp
    rw [Filter.mem_map, e] at h1
    exact h1

/-- `ξ` is pretopological iff `V_ξ(0) → 0` (Lemma 3.4). -/
theorem pretopological_iff {I : Set (Set G)} (hI : AdmIdeal I) :
    (∀ x : G, xi I (Vxi I x) x) ↔ xi I (Vxi I 0) 0 := by
  constructor
  · intro h
    exact h 0
  · intro h x
    rw [Vxi_eq_map hI x]
    exact xi_map_add hI x h

theorem Vxi_zero_neBot {I : Set (Set G)} (hI : AdmIdeal I) : (Vxi I 0).NeBot := by
  refine ⟨fun hbot => ?_⟩
  have h0 : (∅ : Set G) ∈ Vxi I 0 := by rw [hbot]; exact Filter.mem_bot
  have := mem_Vxi.1 h0 (pure 0) (xi_pure hI 0)
  simp at this

theorem Vxi_zero_le {I : Set (Set G)} : Vxi I 0 ≤ 𝓝 0 := by
  intro s hs
  rw [mem_Vxi]
  intro F hF
  exact hF.2.1 hs

theorem mem_Vxi_zero_iff {I : Set (Set G)} (hI : AdmIdeal I) (A : Set G) :
    A ∈ Vxi I 0 ↔ ∀ B ∈ I, (0 : G) ∉ closure (B \ A) := by
  constructor
  · intro hA B hB h0
    have hne : (𝓝 (0 : G) ⊓ 𝓟 (B \ A)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 h0
    have hxi : xi I (𝓝 (0 : G) ⊓ 𝓟 (B \ A)) 0 :=
      ⟨hne, inf_le_left, B \ A, hI.sub B hB _ Set.sdiff_subset,
        Filter.mem_inf_of_right (Filter.mem_principal_self _)⟩
    have h1 : A ∈ (𝓝 (0 : G) ⊓ 𝓟 (B \ A)) := mem_Vxi.1 hA _ hxi
    have h2 : B \ A ∈ (𝓝 (0 : G) ⊓ 𝓟 (B \ A)) := Filter.mem_inf_of_right (Filter.mem_principal_self _)
    have h3 := Filter.inter_mem h1 h2
    have : A ∩ (B \ A) = ∅ := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
      tauto
    rw [this] at h3
    exact Filter.empty_notMem _ h3
  · intro h
    rw [mem_Vxi]
    rintro F ⟨hn, hle, B, hB, hBF⟩
    have h0 := h B hB
    rw [mem_closure_iff_nhds] at h0
    push Not at h0
    obtain ⟨t, ht, hempty⟩ := h0
    have htF : t ∈ F := hle ht
    have h1 := Filter.inter_mem htF hBF
    refine Filter.mem_of_superset h1 ?_
    intro y hy
    by_contra hyA
    have : y ∈ t ∩ (B \ A) := ⟨hy.1, hy.2, hyA⟩
    rw [hempty] at this
    exact this

/-- Theorem 3.5: the pretopology criterion. -/
theorem pretopological_zero_iff {I : Set (Set G)} (hI : AdmIdeal I) :
    xi I (Vxi I 0) 0 ↔ ∃ A ∈ I, ∀ B ∈ I, (0 : G) ∉ closure (B \ A) := by
  constructor
  · rintro ⟨_, _, A, hA, hAV⟩
    exact ⟨A, hA, (mem_Vxi_zero_iff hI A).1 hAV⟩
  · rintro ⟨A, hA, h⟩
    haveI := Vxi_zero_neBot hI
    exact ⟨inferInstance, Vxi_zero_le, A, hA, (mem_Vxi_zero_iff hI A).2 h⟩

/-- Corollary 3.6. -/
theorem not_pretopological_of_recipe {I : Set (Set G)} (hI : AdmIdeal I)
    (h : ∀ A ∈ I, ∃ D ∈ I, Disjoint D A ∧ (0 : G) ∈ closure D) :
    ¬ (∀ x : G, xi I (Vxi I x) x) := by
  intro H
  obtain ⟨A, hA, hB⟩ := (pretopological_zero_iff hI).1 ((pretopological_iff hI).1 H)
  obtain ⟨D, hD, hdisj, h0⟩ := h A hA
  apply hB D hD
  rwa [hdisj.sdiff_eq_left]

/-! ### Proposition 3.7: the topological modification -/

/-- `U` is open in the topological modification of `ξ`. -/
def IsOpenXi (I : Set (Set G)) (U : Set G) : Prop :=
  ∀ x ∈ U, ∀ F : Filter G, xi I F x → U ∈ F

theorem isOpenXi_iff {I : Set (Set G)} (hI : AdmIdeal I) (U : Set G) :
    IsOpenXi I U ↔ ∀ B ∈ I, closure (B \ U) ∩ U = ∅ := by
  constructor
  · intro H B hB
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxc, hxU⟩
    have hne : (𝓝 x ⊓ 𝓟 (B \ U)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxc
    have hxi : xi I (𝓝 x ⊓ 𝓟 (B \ U)) x :=
      ⟨hne, inf_le_left, B \ U, hI.sub B hB _ Set.sdiff_subset,
        Filter.mem_inf_of_right (Filter.mem_principal_self _)⟩
    have h1 : U ∈ (𝓝 x ⊓ 𝓟 (B \ U)) := H x hxU _ hxi
    have h2 : B \ U ∈ (𝓝 x ⊓ 𝓟 (B \ U)) := Filter.mem_inf_of_right (Filter.mem_principal_self _)
    have h3 := Filter.inter_mem h1 h2
    have : U ∩ (B \ U) = ∅ := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
      tauto
    rw [this] at h3
    exact Filter.empty_notMem _ h3
  · intro H x hx F ⟨hn, hle, B, hB, hBF⟩
    have hx' : x ∉ closure (B \ U) := fun hc => by
      have : x ∈ closure (B \ U) ∩ U := ⟨hc, hx⟩
      rw [H B hB] at this
      exact this
    rw [mem_closure_iff_nhds] at hx'
    push Not at hx'
    obtain ⟨t, ht, hempty⟩ := hx'
    have h1 := Filter.inter_mem (hle ht) hBF
    refine Filter.mem_of_superset h1 ?_
    intro y hy
    by_contra hyU
    have : y ∈ t ∩ (B \ U) := ⟨hy.1, hy.2, hyU⟩
    rw [hempty] at this
    exact this

/-- Every `β`-open set is open in the modification. -/
theorem isOpen_isOpenXi {I : Set (Set G)} {U : Set G} (hU : IsOpen U) : IsOpenXi I U := by
  intro x hx F hF
  exact hF.2.1 (hU.mem_nhds hx)

end PG
