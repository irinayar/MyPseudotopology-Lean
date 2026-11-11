import Mathlib
import LeanCheck.PVGThinSet
import LeanCheck.PVGLacMain
import LeanCheck.PVGSubMain

/-!
# PVG: the reduction behind condition (N) (Lean check)

Scope. Condition (N) of the research note (Addenda AC, AI): there is a group topology `γ` on `ℝ` with `τ_B ⊊ γ ⊆ τ_E` whose trace on every
member `J` of the lacunary ideal `I_S` is the Bohr trace. Here `τ_B` is the Bohr topology (`bohrTop`), `τ_E` the Euclidean one, and
`τ_ξ = modTop lacConv` the topological modification of `ξ = ξ_{τ_B, I_S}` (Theorem 7.4 of PVG_v30). Inclusions of topologies are written
with open sets (Mathlib's order `≤` on topologies is the reverse of inclusion of the families of open sets).

* `modTop_trace_eq` : for any family `I` of subsets of `ℝ`, the topological modification of `ξ_{τ_B, I}` induces on every `J ∈ I` exactly the
  Bohr trace (no group-topology assumption on the modification is needed);
* `lac_trace_eq`, `sub_trace_eq` : the cases `I = I_S` and `I = I_A`;
* `bohr_open_lac` , `lac_open_euclid`, `lac_strict` : `τ_B ⊆ τ_ξ ⊆ τ_E`, and `τ_ξ` has an open set (the complement of the thin set `C_t`) that
  is not Bohr-open;
* `N_of_group` : **if `τ_ξ` is a group topology (Question 9.2 positive) then condition (N) holds with `γ = τ_ξ`**. Hence a negative answer to (N)
  gives a negative answer to Question 9.2.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter Topology
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-- The topological modification `τ_{ξ_{τ_B,I}}` induces on every `J ∈ I` the Bohr trace: a relatively open set of `J` for the modification is
relatively Bohr-open (the converse inclusion is automatic). -/
theorem modTop_trace_eq {I : Set (Set ℝ)} {J : Set ℝ} (hJ : J ∈ I) :
    TopologicalSpace.induced (Subtype.val : J → ℝ) (modTop (@xiConv ℝ bohrTop I)) =
      TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop := by
  have hmem := @mem_modTop_iff ℝ _ _ bohrTop bohr_isTopologicalAddGroup bohr_constSMul I
  apply TopologicalSpace.ext
  funext W
  apply propext
  change (∃ U : Set ℝ, @IsOpen ℝ (modTop (@xiConv ℝ bohrTop I)) U ∧ Subtype.val ⁻¹' U = W) ↔
    (∃ U : Set ℝ, @IsOpen ℝ bohrTop U ∧ Subtype.val ⁻¹' U = W)
  constructor
  · rintro ⟨U, hU, rfl⟩
    have hcl := (hmem U).1 hU J hJ
    refine ⟨(@closure ℝ bohrTop (J \ U))ᶜ, (@isOpen_compl_iff ℝ (@closure ℝ bohrTop (J \ U)) bohrTop).2 (@isClosed_closure ℝ bohrTop _), ?_⟩
    ext ⟨x, hxJ⟩
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hxc
      by_contra hxU
      exact hxc (@subset_closure ℝ bohrTop (J \ U) x ⟨hxJ, hxU⟩)
    · intro hxU hxc
      have : x ∈ @closure ℝ bohrTop (J \ U) ∩ U := ⟨hxc, hxU⟩
      rw [hcl] at this
      exact this
  · rintro ⟨U, hU, rfl⟩
    refine ⟨U, ?_, rfl⟩
    intro x hx F hF
    exact hF.1 (@IsOpen.mem_nhds ℝ bohrTop x U hU hx)

/-- The trace of `τ_ξ` on every member of the lacunary ideal `I_S` is the Bohr trace. -/
theorem lac_trace_eq {J : Set ℝ} (hJ : J ∈ IS) :
    TopologicalSpace.induced (Subtype.val : J → ℝ) (modTop lacConv) =
      TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop :=
  modTop_trace_eq (I := IS) hJ

/-- The trace of `τ_{ξ_A}` on every member of the ideal `I_A` is the Bohr trace. -/
theorem sub_trace_eq (A : Set ℕ) {J : Set ℝ} (hJ : J ∈ IA A) :
    TopologicalSpace.induced (Subtype.val : J → ℝ) (modTop (subConv A)) =
      TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop :=
  modTop_trace_eq (I := IA A) hJ

/-- `τ_B ⊆ τ_ξ`: every Bohr-open set is `τ_ξ`-open. -/
theorem bohr_open_lac {U : Set ℝ} (hU : @IsOpen ℝ bohrTop U) : @IsOpen ℝ (modTop lacConv) U :=
  bohr_le_lac_modTop hU

/-- `τ_ξ ⊆ τ_E`: every `τ_ξ`-open set is Euclidean open. -/
theorem lac_open_euclid {U : Set ℝ} (hU : @IsOpen ℝ (modTop lacConv) U) : IsOpen U :=
  lac_modTop_le_euclid hU

/-- `τ_B ⊊ τ_ξ`: the complement of the thin set `C_t` is `τ_ξ`-open but not Bohr-open. -/
theorem lac_strict : ∃ U : Set ℝ, @IsOpen ℝ (modTop lacConv) U ∧ ¬ @IsOpen ℝ bohrTop U := by
  obtain ⟨-, -, -, hopen, hnot⟩ := thin_cluster_modstrict
  exact ⟨Ctᶜ, hopen, hnot⟩

set_option warn.classDefReducibility false in
/-- The Euclidean topology of `ℝ` (as a term, to avoid local-instance capture below). -/
def euclidTop : TopologicalSpace ℝ := inferInstance

/-- **The reduction.** If `τ_ξ` (the topological modification of `ξ_{τ_B,I_S}`) is a group topology, then condition (N) holds with
`γ = τ_ξ`: `γ` is a group topology, `τ_B ⊊ γ ⊆ τ_E`, and `γ` has the Bohr trace on every member of `I_S`. -/
theorem N_of_group (h : @IsTopologicalAddGroup ℝ (modTop lacConv) _) :
    ∃ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ ∧
      (∀ U : Set ℝ, @IsOpen ℝ bohrTop U → @IsOpen ℝ γ U) ∧
      (∃ U : Set ℝ, @IsOpen ℝ γ U ∧ ¬ @IsOpen ℝ bohrTop U) ∧
      (∀ U : Set ℝ, @IsOpen ℝ γ U → @IsOpen ℝ euclidTop U) ∧
      ∀ J ∈ IS, TopologicalSpace.induced (Subtype.val : J → ℝ) γ = TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop :=
  ⟨modTop lacConv, h, fun _ hU => bohr_open_lac hU, lac_strict, fun _ hU => lac_open_euclid hU, fun _ hJ => lac_trace_eq hJ⟩

end Lac
end PVG
