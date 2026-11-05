import LeanCheck.TVGWindowBridge
import LeanCheck.TVGSearchTriAMem
import LeanCheck.TVGWindowCore24

namespace LeanCheck.TVGSearch

open MixedPrime

theorem triple24_26_real_minimum :
    LeastOn ps_triAm 24 26 1667477197289985 := by
  refine ⟨by decide, ?_⟩
  intro m hlo hhi
  refine ⟨witness_triAm_24_26 m hlo hhi, ?_⟩
  intro k hk hlt hin
  have h24 := ShiftedIn_mono (m := 24) (by decide) hlo hin
  apply WindowCore24.triple24_no_smaller hk hlt
  intro n hn
  exact ⟨(good_all_iff_pseudonorm (by decide) (by decide) hk).mpr (h24 (2, 1) (by simp [ps_triAm])) n hn,
    (good_all_iff_pseudonorm (by decide) (by decide) (Nat.zero_le k)).mpr (h24 (3, 0) (by simp [ps_triAm])) n hn,
    (good_all_iff_pseudonorm (by decide) (by decide) (Nat.zero_le k)).mpr (h24 (5, 0) (by simp [ps_triAm])) n hn⟩

#print axioms triple24_26_real_minimum
end LeanCheck.TVGSearch
