import Mathlib
import LeanCheck.PVGSeqFU

/-!
# PVG: `ξ_{β,I}` does not change when `β` is replaced by a topology between `β` and its topological modification (Lean check)

Scope. Addendum J of the research note. For a topology `β` on `X` and a family `I` of subsets, let `ξ = ξ_{β,I}` and let `τ_ξ = modTop ξ` be its
topological modification. If `γ` is a topology with `β ⊆ γ ⊆ τ_ξ` (every `β`-open set is `γ`-open and every `γ`-open set is `τ_ξ`-open), then
`ξ_{γ,I} = ξ_{β,I}`. In particular `ξ_{τ_ξ, I} = ξ_{β,I}`: the pair `(β, I)` may be replaced by `(τ_ξ, I)`, and `τ_ξ` is the finest topology `γ`
with `ξ_{γ,I} = ξ_{β,I}`. No group structure is needed for this statement. All topologies are written explicitly (`@IsOpen X β`, `@xiConv X γ I`)
so that no local instance is captured.

* `xi_eq_of_between`: the statement for an arbitrary `γ` between `β` and `τ_ξ`;
* `xi_modTop_eq`: the case `γ = τ_ξ`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Q95

/-- `ξ_{γ,I} = ξ_{β,I}` for every topology `γ` between `β` and the topological modification of `ξ_{β,I}`. -/
theorem xi_eq_of_between {X : Type*} (β γ : TopologicalSpace X) (I : Set (Set X))
    (h1 : ∀ U : Set X, @IsOpen X β U → @IsOpen X γ U)
    (h2 : ∀ U : Set X, @IsOpen X γ U → @IsOpen X (modTop (@xiConv X β I)) U) (F : Filter X) (x : X) :
    @xiConv X γ I F x ↔ @xiConv X β I F x := by
  constructor
  · rintro ⟨hF, A, hA, hAI⟩
    refine ⟨fun W hW => ?_, A, hA, hAI⟩
    obtain ⟨U, hUW, hUo, hxU⟩ := (@mem_nhds_iff X β x W).1 hW
    exact hF (Filter.mem_of_superset (@IsOpen.mem_nhds X γ x U (h1 U hUo) hxU) hUW)
  · rintro ⟨hF, A, hA, hAI⟩
    refine ⟨fun W hW => ?_, A, hA, hAI⟩
    obtain ⟨U, hUW, hUo, hxU⟩ := (@mem_nhds_iff X γ x W).1 hW
    have hU : U ∈ F := h2 U hUo x hxU F ⟨hF, A, hA, hAI⟩
    exact Filter.mem_of_superset hU hUW

/-- `ξ_{τ_ξ, I} = ξ_{β,I}`. -/
theorem xi_modTop_eq {X : Type*} (β : TopologicalSpace X) (I : Set (Set X)) (F : Filter X) (x : X) :
    @xiConv X (modTop (@xiConv X β I)) I F x ↔ @xiConv X β I F x :=
  xi_eq_of_between β (modTop (@xiConv X β I)) I
    (fun U hU y hy F' hF' => hF'.1 (@IsOpen.mem_nhds X β y U hU hy)) (fun U hU => hU) F x

#print axioms xi_eq_of_between
#print axioms xi_modTop_eq

end Q95
end PVG
