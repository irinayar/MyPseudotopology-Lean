import Mathlib
import LeanCheck.PGIdem

/-!
# PG: ultrafilters with a base of subgroups (Lean check)

Scope. Section 1 of research note (x) (not yet in an article): the Boolean group case, in a form valid for every abelian
group. Let `u` be a nonprincipal ultrafilter on an abelian group `G` such that every `A ∈ u` contains `H ∖ {0}` for a
subgroup `H ∈ u` (for example a strongly summable ultrafilter on the Boolean group `(ℤ/2)^(ω)`, where `FS(x_i)` with
independent `x_i` is `H ∖ {0}`).

* `subgroup_mem_Vgen` : every subgroup `H ∈ u` belongs to every ultrafilter converging to `0` in the PG `ξ(u)` generated
  by `u`, that is, to `Vgen u = V_ξ(u)(0)`;
* `Vgen_mem_genNull` : under the hypothesis, `V_ξ(0)` is itself a null filter, i.e. `ξ(u)` is pretopological.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set

namespace PG

variable {G : Type*} [AddCommGroup G]

theorem subgroup_mem_GenUlt {u : Ultrafilter G} (H : AddSubgroup G) (hH : (H : Set G) ∈ (u : Filter G)) :
    ∀ W : Ultrafilter G, GenUlt u W → (H : Set G) ∈ (W : Filter G) := by
  intro W hW
  induction hW with
  | zero => exact Filter.mem_pure.2 H.zero_mem
  | gen => exact hH
  | neg hU ih =>
    rw [Ultrafilter.coe_map, Filter.mem_map]
    have : (fun x : G => -x) ⁻¹' (H : Set G) = (H : Set G) := by
      ext x; simp
    rw [this]; exact ih
  | add hU hV hle ihU ihV =>
    apply hle
    refine Filter.mem_of_superset (Filter.image2_mem_map₂ ihU ihV) ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact H.add_mem ha hb

theorem subgroup_mem_Vgen {u : Ultrafilter G} (H : AddSubgroup G) (hH : (H : Set G) ∈ (u : Filter G)) :
    (H : Set G) ∈ Vgen u :=
  mem_Vgen.2 (subgroup_mem_GenUlt H hH)

/-- A set of the filter `u + u` contains `A₁ + A₂` with `A₁, A₂ ∈ u`. -/
theorem exists_sum_of_mem_plusF_two {u : Ultrafilter G} {s : Set G} (hs : s ∈ plusF u 2) :
    ∃ A₁ ∈ (u : Filter G), ∃ A₂ ∈ (u : Filter G), ∀ a ∈ A₁, ∀ b ∈ A₂, a + b ∈ s := by
  have hs' : s ∈ Filter.map₂ (· + ·) (u : Filter G) (Filter.map₂ (· + ·) (u : Filter G) (pure (0 : G) : Filter G)) := hs
  obtain ⟨A₁, hA₁, B, hB, h1⟩ := Filter.mem_map₂_iff.1 hs'
  obtain ⟨A₂, hA₂, T, hT, h2⟩ := Filter.mem_map₂_iff.1 hB
  have h0 : (0 : G) ∈ T := Filter.mem_pure.1 hT
  refine ⟨A₁, hA₁, A₂, hA₂, fun a ha b hb => ?_⟩
  have hb' : b + 0 ∈ B := h2 ⟨b, hb, 0, h0, rfl⟩
  have := h1 ⟨a, ha, b + 0, hb', rfl⟩
  simpa using this

theorem Vgen_mem_genNull (u : Ultrafilter G) (hnp : ∀ x : G, ({x} : Set G) ∉ (u : Filter G))
    (hbase : ∀ A ∈ (u : Filter G), ∃ H : AddSubgroup G, (H : Set G) ∈ (u : Filter G) ∧
      ∀ x ∈ H, x ≠ 0 → x ∈ A) :
    Vgen u ∈ genNull u := by
  have hne : (Vgen u).NeBot := by
    refine ⟨fun h => ?_⟩
    have h0 : (∅ : Set G) ∈ Vgen u := by rw [h]; exact Filter.mem_bot
    have := mem_Vgen.1 h0 (pure 0) GenUlt.zero
    exact Filter.empty_notMem _ this
  refine ⟨hne, ?_⟩
  intro U hU
  have hle : (U : Filter G) ≤ plusF u 2 := by
    intro s hs
    obtain ⟨A₁, hA₁, A₂, hA₂, hsum⟩ := exists_sum_of_mem_plusF_two hs
    obtain ⟨H, hHu, hHA⟩ := hbase (A₁ ∩ A₂) (Filter.inter_mem hA₁ hA₂)
    have hHs : (H : Set G) ⊆ s := by
      intro h hh
      -- find a ∈ H with a ≠ 0 and a ≠ h
      have hex : ∃ a ∈ (H : Set G), a ≠ 0 ∧ a ≠ h := by
        by_contra hcon
        push Not at hcon
        have hsub : (H : Set G) ⊆ ({0, h} : Set G) := by
          intro a ha
          by_cases ha0 : a = 0
          · simp [ha0]
          · have := hcon a ha ha0
            simp [this]
        have hfin : ({0, h} : Set G) ∈ (u : Filter G) := Filter.mem_of_superset hHu hsub
        have hu2 : (({0} : Set G) ∪ {h}) ∈ (u : Filter G) := by
          rw [← Set.insert_eq]; exact hfin
        rcases (Ultrafilter.union_mem_iff (f := u)).1 hu2 with h1 | h1
        · exact hnp 0 h1
        · exact hnp h h1
      obtain ⟨a, haH, ha0, hah⟩ := hex
      have h1 : a ∈ A₁ ∩ A₂ := hHA a haH ha0
      have hb : h - a ∈ A₁ ∩ A₂ :=
        hHA (h - a) (H.sub_mem hh haH) (sub_ne_zero.2 (Ne.symm hah))
      have := hsum a h1.1 (h - a) hb.2
      simpa using this
    have hHU : (H : Set G) ∈ (U : Filter G) := hU (subgroup_mem_Vgen H hHu)
    exact Filter.mem_of_superset hHU hHs
  exact (lev_plusF u 2).genUlt U hle

end PG
