import LeanCheck.ChainPW7

/-!
# The results that were conditional on F2, now unconditional

`generatedFact` (F2, Peter–Weyl) is proved in `ChainPW7`; here the theorems that took `PrecompactDuality`
(or `GeneratedFact`) as a hypothesis are instantiated with it.
-/

namespace LeanCheck

open Filter Topology

/-- **Theorem `classification`**, unconditional: Hausdorff precompact TVGQ topologies on `ℝ` correspond
bijectively and order-preservingly to point-separating rationally invariant character subgroups. -/
theorem classification_unc :
    (∀ H : AddSubgroup Chars, SepSub H → PTVGQ (theta (H : Set Chars))) ∧
    (∀ τ : TopologicalSpace ℝ, PTVGQ τ → ∃ H : AddSubgroup Chars, SepSub H ∧ τ = theta (H : Set Chars)) ∧
    (∀ H H' : AddSubgroup Chars, SepSub H → SepSub H' →
      (theta (H : Set Chars) = theta (H' : Set Chars) ↔ H = H')) ∧
    (∀ H H' : AddSubgroup Chars, SepSub H → SepSub H' →
      (theta (H' : Set Chars) ≤ theta (H : Set Chars) ↔ H ≤ H')) :=
  classification precompactDuality

/-- The bijection of the classification, unconditional. -/
noncomputable def classificationEquiv_unc :
    {H : AddSubgroup Chars // SepSub H} ≃ {τ : TopologicalSpace ℝ // PTVGQ τ} :=
  classificationEquiv precompactDuality

/-- `θ_ℚ` is minimal among Hausdorff TVGQ topologies, unconditional. -/
theorem thetaQ_minimal_unc (τ : TopologicalSpace ℝ)
    (hg : @IsTopologicalAddGroup ℝ τ _) (ht : @T2Space ℝ τ)
    (hq : ∀ q : ℚ, Continuous[τ, τ] (mq q : ℝ → ℝ)) (hle : thetaQ ≤ τ) : τ = thetaQ :=
  thetaQ_minimal precompactDuality τ hg ht hq hle

/-- **Theorem `classification_TVG`**, unconditional. -/
theorem classification_TVG_unc :
    (∀ H : AddSubgroup Chars, Separates (H : Set Chars) → RealInv (H : Set Chars) →
      PTVG (theta (H : Set Chars))) ∧
    (∀ τ : TopologicalSpace ℝ, PTVG τ → ∃ H : AddSubgroup Chars,
      Separates (H : Set Chars) ∧ RealInv (H : Set Chars) ∧ τ = theta (H : Set Chars)) ∧
    (∀ H H' : AddSubgroup Chars, Separates (H : Set Chars) → Separates (H' : Set Chars) →
      (theta (H : Set Chars) = theta (H' : Set Chars) ↔ H = H')) ∧
    (∀ H H' : AddSubgroup Chars, Separates (H : Set Chars) → Separates (H' : Set Chars) →
      (theta (H' : Set Chars) ≤ theta (H : Set Chars) ↔ H ≤ H')) :=
  classification_TVG generatedFact

end LeanCheck
