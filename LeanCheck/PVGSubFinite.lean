import Mathlib
import LeanCheck.PVGSubMain

/-!
# PVG: `ξ_A` is the Euclidean convergence for finite `A` (Lean check)

Scope. Part (a) of Theorem 8.61 of PVG_v27 (planned), Addendum N2. For finite `A ⊆ ℕ` every member of `I_A` is bounded; on a bounded set the
Bohr and the Euclidean topologies agree (a continuous bijection from a compact space onto a Hausdorff space), so a filter that is finer
than a Bohr neighbourhood filter and contains a bounded set is Euclidean convergent.

* `IA_bounded_of_finite`, `sumSetA_empty` (in `PVGSubMain`): the members of `I_A` are bounded for finite `A`;
* `bohr_nhds_trace`: for `x`, `R` and `ε > 0` there is a Bohr neighbourhood `W` of `x` with `W ∩ [-R,R] ⊆ B(x,ε)`;
* `subConv_eq_euclid_of_finite`: `subConv A` is the Euclidean convergence for finite `A`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter Topology
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-- On a bounded set the Bohr neighbourhoods of `x` refine the Euclidean ones. -/
lemma bohr_nhds_trace {x : ℝ} (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ W ∈ @nhds ℝ bohrTop x, W ∩ Icc (-R) R ⊆ Metric.ball x ε := by
  have hK : IsCompact (Icc (-R) R \ Metric.ball x ε) := isCompact_Icc.diff Metric.isOpen_ball
  have hcont : @Continuous ℝ ℝ inferInstance bohrTop id := by
    rw [@continuous_def ℝ ℝ inferInstance bohrTop]
    intro U hU
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact bohr_coarser_euclid y (@IsOpen.mem_nhds ℝ bohrTop y U hU hy)
  have himg : @IsCompact ℝ bohrTop (id '' (Icc (-R) R \ Metric.ball x ε)) := @IsCompact.image ℝ ℝ inferInstance bohrTop _ id hK hcont
  have hcl : @IsClosed ℝ bohrTop (id '' (Icc (-R) R \ Metric.ball x ε)) := @IsCompact.isClosed ℝ bohrTop bohr_t2 _ himg
  have hxn : x ∈ (id '' (Icc (-R) R \ Metric.ball x ε))ᶜ := by
    rintro ⟨y, hy, hyx⟩
    exact hy.2 (by rw [show y = x from hyx]; exact Metric.mem_ball_self hε)
  refine ⟨(id '' (Icc (-R) R \ Metric.ball x ε))ᶜ, @IsOpen.mem_nhds ℝ bohrTop x _ hcl.isOpen_compl hxn, ?_⟩
  rintro y ⟨hyW, hyI⟩
  by_contra hyb
  exact hyW ⟨y, ⟨hyI, hyb⟩, rfl⟩

/-- **Theorem 8.61 (a).** For finite `A`, `ξ_A` is the Euclidean convergence. -/
theorem subConv_eq_euclid_of_finite {A : Set ℕ} (hA : A.Finite) (F : Filter ℝ) (x : ℝ) :
    subConv A F x ↔ F ≤ 𝓝 x := by
  refine ⟨fun hF => ?_, fun h => subConv_coarser_euclid A h⟩
  obtain ⟨J, hJF, hJI⟩ := hF.2
  obtain ⟨M, hM⟩ := IA_bounded_of_finite hA hJI
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨W, hW, hWI⟩ := bohr_nhds_trace (x := x) M hε
  have hWF : W ∈ F := hF.1 hW
  refine Filter.mem_of_superset (Filter.inter_mem hWF hJF) (fun y hy => hball (hWI ⟨hy.1, ?_⟩))
  have := hM y hy.2
  exact ⟨by linarith [(abs_le.1 this).1], (abs_le.1 this).2⟩

#print axioms subConv_eq_euclid_of_finite

end Lac
end PVG
