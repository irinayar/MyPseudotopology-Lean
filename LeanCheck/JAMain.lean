import Mathlib
import LeanCheck.JACentral2

/-!
# Joint approximation from the two named external inputs

`JA_of_inputs`: the Matveev two-term separation (`TwoTermSeparation A` for some `A ≥ 0`) and the compact-quotient criterion
(`SyndeticW → JAProp`) together imply joint approximation.  Everything else is proved in Lean (standard axioms only).
-/

namespace LeanCheck
namespace JAMain

open JAAssembly

/-- **Joint approximation for a general separation profile `a`**: the compact-quotient criterion and the two-term separation with
profile `a` (`WindowProfile a`, `CloseGrowth a`). -/
theorem JA_of_profile (hQ : CompactQuotientCriterion) (a : ℝ → ℝ) (ha : WindowProfile a)
    (hG : CloseGrowth a) (hP : JAClose.TwoTermSep a) : JAProp := by
  refine JAHeights.JA_of_centralBound hQ (fun ε hε => ?_)
  refine ⟨max 3 (2 / ε), ?_⟩
  have hD : 3 ≤ max 3 (2 / ε) := le_max_left _ _
  obtain ⟨C, hC, hcb⟩ := JACentral2.central_bound (max 3 (2 / ε)) a hD ha hG hP
  refine ⟨C, hD, ?_, hC, hcb⟩
  have h0 : 0 < max 3 (2 / ε) := by linarith
  rw [div_le_iff₀ h0]
  have h1 : 2 / ε ≤ max 3 (2 / ε) := le_max_right _ _
  have h2 : 2 / ε * ε = 2 := by field_simp
  nlinarith

/-- **Joint approximation, conditional on exactly the two external inputs** (original form, profile `A log^2(2+t)`). -/
theorem JA_of_inputs (hQ : CompactQuotientCriterion) (A : ℝ) (hA : 0 ≤ A)
    (hP : JAClose.TwoTermSeparation A) : JAProp :=
  JA_of_profile hQ _ (JANonDeep.windowProfile_A A hA) (JAProductFinal.closeGrowth_A A hA) hP

#print axioms JA_of_profile
#print axioms JA_of_inputs

end JAMain
end LeanCheck
