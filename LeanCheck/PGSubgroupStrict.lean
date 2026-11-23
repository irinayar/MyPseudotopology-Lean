import Mathlib

/-!
# PG: ultrafilters with a base of subgroups are idempotent and live on the 2-torsion (Lean check)

Scope. The group-theoretic part of the strictness theorem of `PG_v18` (Section 9). Let `u` be a nonprincipal ultrafilter
on an abelian group `G` such that every `A ∈ u` contains `H ∖ {0}` for a subgroup `H ∈ u` (`SubgroupBase u`).

* `idempotent_of_subgroupBase` : `{h | {k | h + k ∈ A} ∈ u} ∈ u` for every `A ∈ u`, that is, `A ∈ u ⊕ u`
  (so `u` is idempotent);
* `two_torsion_mem` : `{g | g + g = 0} ∈ u`;
* `no_subgroupBase_of_torsionFree` : there is no such ultrafilter on a group without elements of order `2`
  (in particular none on `ℤ`).

Not formalized: the colouring of a basis of `G[2]` (every subgroup of finite index meets both colours), the passage to a
subgroup of infinite index, and the comparison with the Bohr topology.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set

namespace PG

section subgroupstrict

variable {G : Type*} [AddCommGroup G]

/-- Every member of `u` contains `H ∖ {0}` for a subgroup `H` that belongs to `u`. -/
def SubgroupBase (u : Ultrafilter G) : Prop :=
  ∀ A ∈ (u : Filter G), ∃ H : AddSubgroup G, (H : Set G) ∈ (u : Filter G) ∧ ∀ h ∈ H, h ≠ 0 → h ∈ A

theorem compl_singleton_mem {u : Ultrafilter G} (hnp : ∀ g : G, ({g} : Set G) ∉ (u : Filter G)) (g : G) :
    ({g} : Set G)ᶜ ∈ (u : Filter G) :=
  Ultrafilter.compl_mem_iff_notMem.2 (hnp g)

theorem exists_ne_zero_mem {u : Ultrafilter G} (hnp : ∀ g : G, ({g} : Set G) ∉ (u : Filter G))
    {H : Set G} (hH : H ∈ (u : Filter G)) : ∃ h ∈ H, h ≠ 0 := by
  obtain ⟨h, hh, hh0⟩ := Filter.nonempty_of_mem (Filter.inter_mem hH (compl_singleton_mem hnp (0 : G)))
  exact ⟨h, hh, hh0⟩

theorem idempotent_of_subgroupBase {u : Ultrafilter G} (hnp : ∀ g : G, ({g} : Set G) ∉ (u : Filter G))
    (hb : SubgroupBase u) (A : Set G) (hA : A ∈ (u : Filter G)) :
    {h | {k | h + k ∈ A} ∈ (u : Filter G)} ∈ (u : Filter G) := by
  obtain ⟨H, hH, hHA⟩ := hb A hA
  refine Filter.mem_of_superset hH ?_
  intro h hh
  have h1 : (H : Set G) ∩ ({-h} : Set G)ᶜ ∈ (u : Filter G) :=
    Filter.inter_mem hH (compl_singleton_mem hnp (-h))
  refine Filter.mem_of_superset h1 ?_
  intro k hk
  have hk1 : k ∈ H := hk.1
  have hk2 : k ≠ -h := hk.2
  show h + k ∈ A
  apply hHA
  · exact H.add_mem hh hk1
  · intro h0
    exact hk2 (eq_neg_of_add_eq_zero_right h0)

theorem two_torsion_mem {u : Ultrafilter G} (hnp : ∀ g : G, ({g} : Set G) ∉ (u : Filter G))
    (hb : SubgroupBase u) : {g : G | g + g = 0} ∈ (u : Filter G) := by
  by_contra hE
  have hEc : {g : G | g + g = 0}ᶜ ∈ (u : Filter G) := Ultrafilter.compl_mem_iff_notMem.2 hE
  let r : G → G → Prop := WellOrderingRel
  have hwo : IsWellOrder G r := inferInstance
  let D : Set G := {g | g + g ≠ 0 ∧ r g (-g)}
  let D' : Set G := {g | g + g ≠ 0 ∧ r (-g) g}
  have hcov : D ∪ D' ∈ (u : Filter G) := by
    refine Filter.mem_of_superset hEc ?_
    intro g hg
    have hg' : g + g ≠ 0 := hg
    have hne : g ≠ -g := by
      intro h
      apply hg'
      have h2 : g + g = -g + g := by rw [← h]
      rw [h2]
      exact neg_add_cancel g
    rcases trichotomous_of r g (-g) with h | h | h
    · exact Or.inl ⟨hg', h⟩
    · exact absurd h hne
    · exact Or.inr ⟨hg', h⟩
  -- a set in `u` all of whose elements `g` have `r g (-g)` (resp. `r (-g) g`) is impossible
  have key : ∀ X : Set G, X ∈ (u : Filter G) → (∀ g ∈ X, g + g ≠ 0 ∧ (r g (-g) ∨ r (-g) g)) →
      (∀ g ∈ X, r g (-g)) ∨ (∀ g ∈ X, r (-g) g) → False := by
    intro X hX _ hX2
    obtain ⟨H, hH, hHX⟩ := hb X hX
    obtain ⟨h, hhH, hh0⟩ := exists_ne_zero_mem hnp hH
    have h1 : h ∈ X := hHX h hhH hh0
    have h2 : -h ∈ X := hHX (-h) (H.neg_mem hhH) (neg_ne_zero.2 hh0)
    rcases hX2 with hh | hh
    · have a1 := hh h h1
      have a2 := hh (-h) h2
      rw [neg_neg] at a2
      exact asymm_of r a1 a2
    · have a1 := hh h h1
      have a2 := hh (-h) h2
      rw [neg_neg] at a2
      exact asymm_of r a1 a2
  rcases Ultrafilter.union_mem_iff.1 hcov with hD | hD'
  · exact key D hD (fun g hg => ⟨hg.1, Or.inl hg.2⟩) (Or.inl (fun g hg => hg.2))
  · exact key D' hD' (fun g hg => ⟨hg.1, Or.inr hg.2⟩) (Or.inr (fun g hg => hg.2))

theorem no_subgroupBase_of_torsionFree {u : Ultrafilter G} (hnp : ∀ g : G, ({g} : Set G) ∉ (u : Filter G))
    (hb : SubgroupBase u) (htf : ∀ g : G, g + g = 0 → g = 0) : False := by
  have h := two_torsion_mem hnp hb
  have hsub : {g : G | g + g = 0} ⊆ {(0 : G)} := fun g hg => htf g hg
  exact hnp 0 (Filter.mem_of_superset h hsub)

end subgroupstrict

end PG
