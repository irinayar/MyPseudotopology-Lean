import LeanCheck.TVGWindowBridge
import LeanCheck.TVGSearchTriAMem
import LeanCheck.TVGWindowCore22

namespace LeanCheck.TVGSearch

open MixedPrime

theorem triple22_23_real_minimum :
    LeastOn ps_triAm 22 23 1111607529308145 := by
  refine ⟨by decide, ?_⟩
  intro m hlo hhi
  refine ⟨witness_triAm_22_23 m hlo hhi, ?_⟩
  intro k hk hlt hin
  have h22 := ShiftedIn_mono (m := 22) (by decide) hlo hin
  apply WindowCore22.triple22_no_smaller_integer hk hlt
  intro n hn
  exact ⟨(good_all_iff_pseudonorm (by decide) (by decide) hk).mpr (h22 (2, 1) (by simp [ps_triAm])) n hn,
    (good_all_iff_pseudonorm (by decide) (by decide) (Nat.zero_le k)).mpr (h22 (3, 0) (by simp [ps_triAm])) n hn,
    (good_all_iff_pseudonorm (by decide) (by decide) (Nat.zero_le k)).mpr (h22 (5, 0) (by simp [ps_triAm])) n hn⟩

#print axioms triple22_23_real_minimum

#print axioms triple22_23_real_minimum
end LeanCheck.TVGSearch
