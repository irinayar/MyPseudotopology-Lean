import Mathlib
import LeanCheck.PVGIdeal

/-!
# PVG: pretopological and topological coincide (Lean check)

Scope. Proposition 8.60 of PVG_v27 (planned), Addendum N of the research note. For a PVG on a real vector space, `V(0) → 0` (that is, the
PVG is pretopological) implies that the PVG is the convergence of a topology; together with `topological_isPretop` of `PVGIdeal.lean` a PVG
is pretopological if and only if it is topological. The topology is `U` open iff `{z | x + z ∈ U} ∈ V(0)` for every `x ∈ U`; the proof uses
only continuity of addition at `(0,0)` (that is, `V(0) + V(0) ≥ V(0)`), not the dilations.

* `pretop_isTopological`: a pretopological PVG is topological;
* `isPretop_iff_isTopological`: for a PVG, pretopological iff topological.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Q95

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {conv : Filter X → X → Prop}

/-- Members of `V(0)` contain `0`. -/
lemma zero_mem_of_mem_Vfil (h : IsPVG conv) {U : Set X} (hU : U ∈ Vfil conv 0) : (0 : X) ∈ U := by
  have := mem_Vfil.1 hU (pure 0) (h.p1 0)
  simpa using this

/-- `V(0) + V(0) ≥ V(0)`: every member of `V(0)` contains a sum of members of `V(0)`; in the form: there is `W ∈ V(0)` with `x + y ∈ U`
for all `x, y ∈ W`. -/
lemma Vfil_add_small (h : IsPVG conv) (hp : IsPretop conv) {U : Set X} (hU : U ∈ Vfil conv 0) :
    ∃ W ∈ Vfil conv 0, ∀ x ∈ W, ∀ y ∈ W, x + y ∈ U := by
  have h1 := h.add (hp 0) (hp 0)
  rw [add_zero] at h1
  have h2 := mem_Vfil.1 hU _ h1
  rw [Filter.mem_map₂_iff] at h2
  obtain ⟨s, hs, t, ht, hst⟩ := h2
  refine ⟨s ∩ t, Filter.inter_mem hs ht, fun x hx y hy => hst (Set.mem_image2_of_mem hx.1 hy.2)⟩

/-- **A pretopological PVG is topological.** -/
theorem pretop_isTopological (h : IsPVG conv) (hp : IsPretop conv) : IsTopological conv := by
  set V : Filter X := Vfil conv 0 with hV
  let τ : TopologicalSpace X :=
    { IsOpen := fun U => ∀ x ∈ U, {z | x + z ∈ U} ∈ V
      isOpen_univ := fun x _ => by simp
      isOpen_inter := fun U U' hU hU' x hx => by
        have := Filter.inter_mem (hU x hx.1) (hU' x hx.2)
        exact Filter.mem_of_superset this (fun z hz => hz)
      isOpen_sUnion := fun S hS x hx => by
        obtain ⟨U, hUS, hxU⟩ := hx
        exact Filter.mem_of_superset (hS U hUS x hxU) (fun z hz => ⟨U, hUS, hz⟩) }
  -- the neighbourhood filter of `x` is `V(x)`
  have hnhds : ∀ x : X, @nhds X τ x = Vfil conv x := by
    intro x
    ext s
    rw [@mem_nhds_iff X τ x s, Vfil_eq_map h x, Filter.mem_map]
    constructor
    · rintro ⟨U, hUs, hUo, hxU⟩
      refine Filter.mem_of_superset (hUo x hxU) (fun z hz => ?_)
      exact hUs (by simpa [add_comm] using hz)
    · intro hs
      let U : Set X := {y | {z | y + z ∈ s} ∈ V}
      have hxU : x ∈ U := by
        refine Filter.mem_of_superset hs (fun z hz => ?_)
        simpa [add_comm] using hz
      refine ⟨U, ?_, ?_, hxU⟩
      · intro y hy
        have := zero_mem_of_mem_Vfil h hy
        simpa using this
      · intro y hy
        obtain ⟨W, hW, hWsmall⟩ := Vfil_add_small h hp hy
        refine Filter.mem_of_superset hW (fun z hz => ?_)
        show {w | y + z + w ∈ s} ∈ V
        refine Filter.mem_of_superset hW (fun w hw => ?_)
        have := hWsmall z hz w hw
        simpa [add_assoc] using this
  refine ⟨τ, fun F x => ?_⟩
  rw [hnhds x]
  constructor
  · intro hF
    exact fun s hs => mem_Vfil.1 hs F hF
  · intro hF
    exact h.p2 (hp x) hF

/-- For a PVG, pretopological and topological coincide. -/
theorem isPretop_iff_isTopological (h : IsPVG conv) : IsPretop conv ↔ IsTopological conv :=
  ⟨pretop_isTopological h, topological_isPretop⟩

#print axioms pretop_isTopological
#print axioms isPretop_iff_isTopological

end Q95
end PVG
