import Mathlib
import LeanCheck.PVGSubMain

/-!
# PVG: the topological modifications of the lacunary subfamilies (Lean check)

Scope. The statement on the topological modifications in Addendum N2 / Theorem 8.61 of PVG_v27 (planned). Let `τ_A` be the topological
modification `modTop (subConv A)` of `ξ_A = ξ_{τ_B, I_A}`.

* `modTop_sub_of_diff_finite`: if `A \ B` is finite, then every `τ_B`-open set is `τ_A`-open;
* `modTop_sub_iff`: every `τ_B`-open set is `τ_A`-open if and only if `A \ B` is finite (for infinite `C = A \ B` the set
  `ℝ \ D_C`, `D_C = {s_n - s_l : n, l ∈ C}`, is `τ_B`-open and not `τ_A`-open).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter Topology
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-- `A \ B` finite implies `τ_B ⊆ τ_A`. -/
theorem modTop_sub_of_diff_finite {A B : Set ℕ} (h : (A \ B).Finite) {U : Set ℝ}
    (hU : @IsOpen ℝ (modTop (subConv B)) U) : @IsOpen ℝ (modTop (subConv A)) U :=
  fun x hx F hF => hU x hx F (conv_sub_of_diff_finite h hF)

/-- `τ_B ⊆ τ_A` implies that `A \ B` is finite. -/
theorem diff_finite_of_modTop_sub {A B : Set ℕ}
    (h : ∀ U : Set ℝ, @IsOpen ℝ (modTop (subConv B)) U → @IsOpen ℝ (modTop (subConv A)) U) : (A \ B).Finite := by
  by_contra hinf
  set C : Set ℕ := A \ B with hC
  have hCB : ∀ n ∈ C, n ∉ B := fun n hn => hn.2
  have hCA : C ⊆ A := fun n hn => hn.1
  have hD := zero_mem_closure_DA hinf (c := 1) le_rfl (J := ∅) (by
    refine Set.Finite.subset Set.finite_empty ?_
    rintro t ⟨_, ht⟩
    exact absurd ht (Set.notMem_empty _))
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_t2
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  set D : Set ℝ := DsetA C 1 ∅ with hDdef
  have h0 : (0 : ℝ) ∉ D := fun h0 => absurd (DsetA_pos le_rfl h0) (lt_irrefl _)
  -- `Dᶜ` is `τ_B`-open
  have hopenB : @IsOpen ℝ (modTop (subConv B)) Dᶜ := by
    rw [mem_modTop_iff (I := IA B) Dᶜ]
    intro J hJ
    have hfin : (J ∩ D).Finite := DsetA_inter_finite hCB hJ
    have : J \ Dᶜ = J ∩ D := by ext x; simp
    rw [this, hfin.isClosed.closure_eq]
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hx hxc
    exact hxc hx.2
  have hopenA := h _ hopenB
  rw [mem_modTop_iff (I := IA A) Dᶜ] at hopenA
  have hDA : D ∈ IA A := IA_mono hCA (DsetA_mem_IA C 1 ∅)
  have := hopenA D hDA
  have hdiff : D \ Dᶜ = D := by ext x; simp
  rw [hdiff] at this
  have h0mem : (0 : ℝ) ∈ closure D ∩ Dᶜ := ⟨hD, h0⟩
  rw [this] at h0mem
  exact h0mem

theorem modTop_sub_iff {A B : Set ℕ} :
    (∀ U : Set ℝ, @IsOpen ℝ (modTop (subConv B)) U → @IsOpen ℝ (modTop (subConv A)) U) ↔ (A \ B).Finite :=
  ⟨diff_finite_of_modTop_sub, fun h _ hU => modTop_sub_of_diff_finite h hU⟩

#print axioms modTop_sub_iff

end Lac
end PVG
