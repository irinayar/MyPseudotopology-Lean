import Mathlib
import LeanCheck.PVGBetaChoose
import LeanCheck.PVGKronecker

/-!
# PVG: the existence theorem without hypotheses (Lean check)

Scope. Theorem `thm:betaexists` of PVG_v22, with Kronecker's density theorem proved in `PVGKronecker`.

* `exists_beta_unconditional`: there is a topology `β` on `ℝ` that is a Hausdorff group topology inside the Euclidean topology with all
  dilations continuous, every neighbourhood of `0` contains a half-integer, no character `t ↦ bt + ℤ` with `b ≠ 0` is continuous, and
  `ℤ` is dense in `(ℝ, β)`.

A Lean proof verifies its formal statement; the correspondence with the article requires mathematical review.
-/

namespace PVG
namespace Beta

theorem exists_beta_unconditional :
    ∃ β : TopologicalSpace ℝ,
      @IsTopologicalAddGroup ℝ β _ ∧ @T2Space ℝ β ∧ eT ≤ β ∧ @ContinuousConstSMul ℝ ℝ β _ ∧
      (∀ V ∈ @nhds ℝ β 0, ∃ k : ℤ, ((k : ℝ) + 1 / 2) ∈ V) ∧
      (∀ b : ℝ, b ≠ 0 → ¬ @Continuous ℝ (AddCircle (1 : ℝ)) β cT (chi b)) ∧
      (∀ x : ℝ, x ∈ @closure ℝ β (Set.range (fun k : ℤ => (k : ℝ)))) :=
  exists_beta kronecker_density

end Beta
end PVG
