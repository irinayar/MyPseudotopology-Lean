import Mathlib
import LeanCheck.PVGNTrace

/-!
# PVG: a topology with the Bohr trace on every member of the ideal is contained in `τ_ξ` (Lean check)

Scope. Proposition BW2 of the research note (Proposition 8.82 of PVG_v35). Let `I` be an ideal of subsets of `ℝ` (`IsIdeal I`) and `γ` a
topology on `ℝ` that induces on every `J ∈ I` the Bohr trace. Then every `γ`-open set is open for the topological modification
`τ_ξ = modTop (xiConv I)` of `ξ_{τ_B, I}` (`topology_le_modTop`); in particular for `I = I_S` (`topology_le_modTop_lac`): a topology
as in condition (N) lies inside `τ_ξ`. The proof adds the point `x` to the member `J` of the ideal (`J ∪ {x} ∈ I`) and uses the Bohr trace
on `J ∪ {x}`. No group structure is used.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set
open scoped Classical

namespace PVG
namespace Lac
open Q95

theorem topology_le_modTop (I : Set (Set ℝ)) (hI : IsIdeal I) (γ : TopologicalSpace ℝ)
    (htr : ∀ J ∈ I, TopologicalSpace.induced (Subtype.val : J → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop)
    {U : Set ℝ} (hU : @IsOpen ℝ γ U) : @IsOpen ℝ (modTop (@xiConv ℝ bohrTop I)) U := by
  have hmem := @mem_modTop_iff ℝ _ _ bohrTop bohr_isTopologicalAddGroup bohr_constSMul I U
  refine hmem.2 ?_
  intro J hJ
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hxc, hxU⟩
  have hJ' : J ∪ {x} ∈ I := hI.union hJ (hI.single x)
  have hopen : @IsOpen (↥(J ∪ {x})) (TopologicalSpace.induced (Subtype.val : ↥(J ∪ {x}) → ℝ) γ)
      (Subtype.val ⁻¹' U) := ⟨U, hU, rfl⟩
  rw [htr _ hJ'] at hopen
  obtain ⟨O, hO, hOeq⟩ := hopen
  have hxO : x ∈ O := by
    have : (⟨x, Or.inr rfl⟩ : ↥(J ∪ {x})) ∈ (Subtype.val ⁻¹' U : Set ↥(J ∪ {x})) := hxU
    rw [← hOeq] at this
    exact this
  obtain ⟨z, hzO, hzJU⟩ := (@mem_closure_iff ℝ bohrTop x (J \ U)).1 hxc O hO hxO
  have hzJ' : z ∈ J ∪ {x} := Or.inl hzJU.1
  have : (⟨z, hzJ'⟩ : ↥(J ∪ {x})) ∈ (Subtype.val ⁻¹' O : Set ↥(J ∪ {x})) := hzO
  rw [hOeq] at this
  exact hzJU.2 this

/-- Condition (N) (trace part): a topology with the Bohr trace on every member of `I_S` is contained in `τ_ξ`. -/
theorem topology_le_modTop_lac (γ : TopologicalSpace ℝ)
    (htr : ∀ J ∈ IS, TopologicalSpace.induced (Subtype.val : J → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop)
    {U : Set ℝ} (hU : @IsOpen ℝ γ U) : @IsOpen ℝ (modTop lacConv) U :=
  topology_le_modTop IS IS_isIdeal γ htr hU

end Lac
end PVG
