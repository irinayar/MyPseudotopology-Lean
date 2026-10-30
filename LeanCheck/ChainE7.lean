import LeanCheck.ChainE6

/-!
# The quotient associated with a coefficient admits rational multiplications
(HamelCharactersTVG_v18 Lemma 19.1 `lem:quotient-v8`, last assertion)

For a TVG topology `μ` on `ℝ` (all real dilations continuous), the quotient topology `λ_μ` on `ℚ ≅ ℝ / ker f`
(coinduced along `f`) admits every fixed rational multiplication continuously, because `f (s x) = s f(x)` for rational `s`.
-/

namespace LeanCheck

open Filter Topology

theorem lamTop_rational_scalar (f : ℝ →+ ℚ) (μ : TopologicalSpace ℝ)
    (hdil : ∀ a : ℝ, Continuous[μ, μ] (fun x : ℝ => a * x)) (s : ℚ) :
    Continuous[lamTop f μ, lamTop f μ] (fun q : ℚ => s * q) := by
  have h1 : TopologicalSpace.coinduced (fun x : ℝ => (s : ℝ) * x) μ ≤ μ :=
    continuous_iff_coinduced_le.1 (hdil s)
  rw [continuous_iff_coinduced_le]
  unfold lamTop
  rw [coinduced_compose]
  have e : ((fun q : ℚ => s * q) ∘ fun x : ℝ => f x) = (fun x : ℝ => f x) ∘ (fun x : ℝ => (s : ℝ) * x) := by
    funext x
    simp only [Function.comp]
    exact (f_ratmul f s x).symm
  rw [e, ← coinduced_compose]
  exact coinduced_mono h1

end LeanCheck
