import Mathlib
import LeanCheck.PGNullFilters
import LeanCheck.PGGenerated
import LeanCheck.PGTwoGeneration
import LeanCheck.PGTwoLattice
import LeanCheck.PGTwoFinal

/-!
# PGtwo: Hausdorff quotients of a PG (Lean check)

Scope. Section 6 of the second article (`PGtwo.tex`), Lemma 6.5 and Theorem 6.6, abstract form. A PG on `G` is given by a
null family `C` (`PGNullFilters`).

* `hausdorff_iff_principal` : the convergence is Hausdorff iff the only point `g` with `pure g ∈ C` is `0` (Lemma 6.5(a));
* `IsOpenXi C O` and `closed_iff_conv_closed` : a set is closed for the topological modification iff every proper
  convergent filter containing it has its limit in it (Lemma 6.5(b));
* `quotC N C` : the final structure on `G ⧸ N` for the quotient map (Theorem 6.2 of the article, `PGTwoFinal`);
  `pure_mem_quotC_iff` : `pure (g + N)` converges to `0` in it iff some null filter has all its members meeting the coset
  `g + N`;
* `quot_hausdorff_iff`, `hausdorff_quotient_iff` : the quotient is Hausdorff iff `N` is convergence-closed, iff `N` is closed
  for the topological modification (Theorem 6.6). The group `G` need not be Hausdorff.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

variable {G : Type*} [AddCommGroup G]

/-- Lemma 6.5(a). -/
theorem hausdorff_iff_principal {C : Set (Filter G)} (hC : NullFamily C) :
    (∀ (F : Filter G) (z : G), F ∈ C → Filter.map (fun y => y - z) F ∈ C → z = 0) ↔
      (∀ g : G, (pure g : Filter G) ∈ C → g = 0) := by
  constructor
  · intro H g hg
    exact H (pure g) g hg (by rw [Filter.map_pure, sub_self]; exact hC.pure_zero)
  · intro H F z hF hFz
    have hG : Filter.map₂ (· + ·) (Filter.map (fun y => y - z) F) (Filter.map (fun x : G => -x) F) ∈ C :=
      hC.add _ hFz _ (hC.neg F hF)
    have hle : (pure (-z) : Filter G) ≤
        Filter.map₂ (· + ·) (Filter.map (fun y => y - z) F) (Filter.map (fun x : G => -x) F) := by
      rw [Filter.pure_le_iff]
      intro S hS
      obtain ⟨s, hs, t, ht, hst⟩ := Filter.mem_map₂_iff.1 hS
      have hne : F.NeBot := hC.ne F hF
      obtain ⟨x, hx1, hx2⟩ := Filter.nonempty_of_mem (Filter.inter_mem (Filter.mem_map.1 hs) (Filter.mem_map.1 ht))
      have h3 := hst ⟨x - z, hx1, -x, hx2, rfl⟩
      have e : x - z + -x = -z := by abel
      show -z ∈ S
      have h4 : x - z + -x ∈ S := h3
      rwa [e] at h4
    have h1 : (pure (-z) : Filter G) ∈ C := hC.finer _ hG _ hle inferInstance
    have := H _ h1
    exact neg_eq_zero.1 this

/-- Openness for the topological modification of the PG. -/
def IsOpenXi (C : Set (Filter G)) (O : Set G) : Prop :=
  ∀ x ∈ O, ∀ F : Filter G, F.NeBot → conv C F x → O ∈ F

/-- Lemma 6.5(b). -/
theorem closed_iff_conv_closed {C : Set (Filter G)} (hC : NullFamily C) (N : Set G) :
    IsOpenXi C Nᶜ ↔ ∀ (F : Filter G) (x : G), F.NeBot → conv C F x → N ∈ F → x ∈ N := by
  constructor
  · intro h F x hne hconv hN
    by_contra hx
    have h1 := h x hx F hne hconv
    obtain ⟨y, hy1, hy2⟩ := Filter.nonempty_of_mem (Filter.inter_mem hN h1)
    exact hy2 hy1
  · intro h x hx F hne hconv
    by_contra hnot
    have hne' : (F ⊓ 𝓟 N).NeBot := by
      rw [Filter.inf_principal_neBot_iff]
      intro U hU
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      apply hnot
      refine Filter.mem_of_superset hU ?_
      intro y hy hyN
      have : y ∈ U ∩ N := ⟨hy, hyN⟩
      rw [hempty] at this
      exact this
    have hc : conv C (F ⊓ 𝓟 N) x := conv_mono hC hconv inf_le_left hne'
    exact hx (h _ x hne' hc (Filter.mem_inf_of_right (Filter.mem_principal_self N)))

section Quotient

variable (N : AddSubgroup G)

/-- The final structure on `G ⧸ N` for the quotient map. -/
def quotC (C : Set (Filter G)) : Set (Filter (G ⧸ N)) :=
  genFam {F | ∃ F0 ∈ C, F = Filter.map (QuotientAddGroup.mk' N) F0}

theorem quotC_nullFamily (C : Set (Filter G)) : NullFamily (quotC N C) := genFam_nullFamily _

theorem sumClosure_mem {C : Set (Filter G)} (hC : NullFamily C) {σ : Filter (G ⧸ N)}
    (h : SumClosure {F | ∃ F0 ∈ C, F = Filter.map (QuotientAddGroup.mk' N) F0} σ) :
    ∃ F0 ∈ C, σ = Filter.map (QuotientAddGroup.mk' N) F0 := by
  induction h with
  | zero => exact ⟨pure 0, hC.pure_zero, by rw [Filter.map_pure, map_zero]⟩
  | gen hF => exact hF
  | neg hF =>
    obtain ⟨F0, hF0, rfl⟩ := hF
    refine ⟨Filter.map (fun x : G => -x) F0, hC.neg _ hF0, ?_⟩
    rw [Filter.map_map, Filter.map_map]
    congr 1
  | add h1 h2 ih1 ih2 =>
    obtain ⟨F0, hF0, rfl⟩ := ih1
    obtain ⟨F1, hF1, rfl⟩ := ih2
    refine ⟨Filter.map₂ (· + ·) F0 F1, hC.add _ hF0 _ hF1, ?_⟩
    symm
    apply Filter.map_map₂_distrib
    intro a b
    exact map_add _ _ _

/-- `pure (g + N)` is null in the quotient iff some null filter has all its members meeting the coset of `g`. -/
theorem pure_mem_quotC_iff {C : Set (Filter G)} (hC : NullFamily C) (g : G) :
    (pure (QuotientAddGroup.mk' N g) : Filter (G ⧸ N)) ∈ quotC N C ↔
      ∃ F ∈ C, ∀ A ∈ F, ∃ a ∈ A, QuotientAddGroup.mk' N a = QuotientAddGroup.mk' N g := by
  constructor
  · rintro ⟨_, hU⟩
    obtain ⟨σ, hσ, hle⟩ := hU (pure (QuotientAddGroup.mk' N g)) (by simp)
    obtain ⟨F0, hF0, rfl⟩ := sumClosure_mem N hC hσ
    refine ⟨F0, hF0, fun A hA => ?_⟩
    have h1 : (QuotientAddGroup.mk' N) '' A ∈ Filter.map (QuotientAddGroup.mk' N) F0 :=
      Filter.image_mem_map hA
    have h2 : QuotientAddGroup.mk' N g ∈ (QuotientAddGroup.mk' N) '' A := hle h1
    obtain ⟨a, ha, hag⟩ := h2
    exact ⟨a, ha, hag⟩
  · rintro ⟨F, hF, h⟩
    have hmem : Filter.map (QuotientAddGroup.mk' N) F ∈ quotC N C := by
      refine subset_genFam ?_ ⟨F, hF, rfl⟩
      rintro _ ⟨F0, hF0, rfl⟩
      exact (hC.ne F0 hF0).map _
    have hle : (pure (QuotientAddGroup.mk' N g) : Filter (G ⧸ N)) ≤ Filter.map (QuotientAddGroup.mk' N) F := by
      rw [Filter.pure_le_iff]
      intro S hS
      obtain ⟨a, ha, hag⟩ := h _ hS
      have : QuotientAddGroup.mk' N a ∈ S := ha
      rwa [hag] at this
    exact (quotC_nullFamily N C).finer _ hmem _ hle inferInstance

/-- Theorem 6.6: the quotient has no nonzero principal null filter iff `N` is convergence-closed. -/
theorem quot_hausdorff_iff {C : Set (Filter G)} (hC : NullFamily C) :
    (∀ q : G ⧸ N, (pure q : Filter (G ⧸ N)) ∈ quotC N C → q = 0) ↔
      ∀ (F : Filter G) (x : G), F.NeBot → conv C F x → (N : Set G) ∈ F → x ∈ N := by
  constructor
  · intro H F x hne hconv hN
    by_contra hx
    have hmem : (pure (QuotientAddGroup.mk' N (-x)) : Filter (G ⧸ N)) ∈ quotC N C := by
      rw [pure_mem_quotC_iff N hC]
      refine ⟨Filter.map (fun y => y - x) F, hconv, fun A hA => ?_⟩
      obtain ⟨y, hy1, hy2⟩ := Filter.nonempty_of_mem (Filter.inter_mem hN hA)
      refine ⟨y - x, hy2, ?_⟩
      have hy : QuotientAddGroup.mk' N y = 0 := (QuotientAddGroup.eq_zero_iff y).2 hy1
      simp [map_sub, hy]
    have h0 := H _ hmem
    apply hx
    have : QuotientAddGroup.mk' N (-x) = 0 := h0
    have h1 : -x ∈ N := (QuotientAddGroup.eq_zero_iff (-x)).1 this
    simpa using N.neg_mem h1
  · intro H q hq
    obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective q
    have hq' : (pure (QuotientAddGroup.mk' N g) : Filter (G ⧸ N)) ∈ quotC N C := hq
    obtain ⟨F, hF, hmeet⟩ := (pure_mem_quotC_iff N hC g).1 hq'
    have hne' : (F ⊓ 𝓟 {a | QuotientAddGroup.mk' N a = QuotientAddGroup.mk' N g}).NeBot := by
      rw [Filter.inf_principal_neBot_iff]
      intro U hU
      obtain ⟨a, ha, hag⟩ := hmeet U hU
      exact ⟨a, ha, hag⟩
    have hF' : F ⊓ 𝓟 {a | QuotientAddGroup.mk' N a = QuotientAddGroup.mk' N g} ∈ C :=
      hC.finer F hF _ inf_le_left hne'
    have hconv : conv C (Filter.map (fun y => y - g) (F ⊓ 𝓟 {a | QuotientAddGroup.mk' N a = QuotientAddGroup.mk' N g}))
        (-g) := by
      unfold conv
      rw [Filter.map_map]
      have : ((fun y : G => y - -g) ∘ fun y => y - g) = id := by funext y; simp
      rw [this, Filter.map_id]
      exact hF'
    have hNmem : (N : Set G) ∈ Filter.map (fun y => y - g)
        (F ⊓ 𝓟 {a | QuotientAddGroup.mk' N a = QuotientAddGroup.mk' N g}) := by
      rw [Filter.mem_map]
      refine Filter.mem_of_superset (Filter.mem_inf_of_right (Filter.mem_principal_self _)) ?_
      intro a ha
      have : QuotientAddGroup.mk' N (a - g) = 0 := by
        have ha' : QuotientAddGroup.mk' N a = QuotientAddGroup.mk' N g := ha
        simp [map_sub, ha']
      exact (QuotientAddGroup.eq_zero_iff (a - g)).1 this
    have hx := H _ (-g) (hne'.map _) hconv hNmem
    have : g ∈ N := by simpa using N.neg_mem hx
    exact (QuotientAddGroup.eq_zero_iff g).2 this

/-- Theorem 6.6: the quotient PG is Hausdorff iff `N` is closed for the topological modification of the PG. -/
theorem hausdorff_quotient_iff {C : Set (Filter G)} (hC : NullFamily C) :
    (∀ (F : Filter (G ⧸ N)) (z : G ⧸ N), F ∈ quotC N C → Filter.map (fun y => y - z) F ∈ quotC N C → z = 0) ↔
      IsOpenXi C (N : Set G)ᶜ :=
  ((hausdorff_iff_principal (quotC_nullFamily N C)).trans (quot_hausdorff_iff N hC)).trans
    (closed_iff_conv_closed hC (N : Set G)).symm

end Quotient

end PG
