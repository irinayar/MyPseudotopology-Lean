import Mathlib
import LeanCheck.PVGNull
import LeanCheck.PVGIdeal

/-!
# PVG: the topological modification of a PVG is a semitopological group (Lean check)

Scope. Proposition 8.67 and Remark 8.68 of PVG_v30 (Addendum Z1 of the research note).

* `modTop_translate_isOpen`, `modTop_continuous_add_const`: for a PVG convergence `conv` on a real vector space `X`, every translation
  `x ↦ x + a` is continuous (hence a homeomorphism) for the topological modification `modTop conv`;
* `closure_add_closure_subset_of_translations`: on an additive commutative group with a topology in which all translations are
  continuous, `closure X + closure Y ⊆ closure (X + Y)`;
* `closure_add_closure_modTop`: the consequence for `modTop conv` (Proposition 8.67): `cl_τ X + cl_τ Y ⊆ cl_τ (X + Y)`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter Topology

namespace PVG
namespace Q95

section Semi

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {conv : Filter X → X → Prop}

/-- For a PVG `conv`, the preimage of a `modTop conv`-open set under a translation is `modTop conv`-open. -/
theorem modTop_translate_isOpen (h : IsPVG conv) (a : X) {U : Set X}
    (hU : @IsOpen X (modTop conv) U) : @IsOpen X (modTop conv) ((fun x => x + a) ⁻¹' U) := by
  intro x hx F hF
  have h1 := h.add hF (h.p1 a)
  rw [Filter.map₂_pure_right] at h1
  exact hU (x + a) hx _ h1

/-- Every translation is continuous for the topological modification of a PVG. -/
theorem modTop_continuous_add_const (h : IsPVG conv) (a : X) :
    @Continuous X X (modTop conv) (modTop conv) (fun x => x + a) :=
  @continuous_def X X (modTop conv) (modTop conv) _ |>.2 fun _ hU => modTop_translate_isOpen h a hU

end Semi

/-- **Proposition 8.67** (abstract form). In a commutative group with a topology for which all translations are continuous,
`closure X + closure Y ⊆ closure (X + Y)`. -/
theorem closure_add_closure_subset_of_translations {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    (h : ∀ a : G, Continuous (fun x : G => x + a)) (X Y : Set G) :
    closure X + closure Y ⊆ closure (X + Y) := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have step1 : ∀ x' ∈ closure X, ∀ y' ∈ Y, x' + y' ∈ closure (X + Y) := by
    intro x' hx' y' hy'
    have h2 : (fun u : G => u + y') '' closure X ⊆ closure ((fun u : G => u + y') '' X) :=
      image_closure_subset_closure_image (h y')
    have h3 : x' + y' ∈ closure ((fun u : G => u + y') '' X) := h2 ⟨x', hx', rfl⟩
    refine closure_mono ?_ h3
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hu, y', hy', rfl⟩
  have hcont : Continuous (fun y' : G => x + y') := by
    simpa [add_comm] using h x
  have hclosed : IsClosed {y' : G | x + y' ∈ closure (X + Y)} := isClosed_closure.preimage hcont
  have hsub : Y ⊆ {y' : G | x + y' ∈ closure (X + Y)} := fun y' hy' => step1 x hx y' hy'
  exact closure_minimal hsub hclosed hy

/-- **Proposition 8.67.** For a PVG `conv`, `cl_τ X + cl_τ Y ⊆ cl_τ (X + Y)` for the topological modification `τ = modTop conv`. -/
theorem closure_add_closure_modTop {X : Type*} [AddCommGroup X] [Module ℝ X] {conv : Filter X → X → Prop}
    (h : IsPVG conv) (S T : Set X) :
    @closure X (modTop conv) S + @closure X (modTop conv) T ⊆ @closure X (modTop conv) (S + T) := by
  letI : TopologicalSpace X := modTop conv
  exact closure_add_closure_subset_of_translations (fun a => modTop_continuous_add_const h a) S T

#print axioms modTop_translate_isOpen
#print axioms modTop_continuous_add_const
#print axioms closure_add_closure_subset_of_translations
#print axioms closure_add_closure_modTop

end Q95
end PVG
