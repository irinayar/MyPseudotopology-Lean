import LeanCheck.TVGWindowBridge
import LeanCheck.TVGWindowCoreIsolated

namespace LeanCheck.TVGSearch

open MixedPrime

theorem triple21_real_minimum : LeastOn [(2, 1), (3, 0), (5, 0)] 21 21 566864750054385 := by
  refine ⟨by decide, ?_⟩
  intro m hlo hhi
  have hm : m = 21 := Nat.le_antisymm hhi hlo
  subst m
  have hw : ShiftedIn [(2, 1), (3, 0), (5, 0)] 21 566864750054385 := by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl
    · exact (good_all_iff_pseudonorm (by decide) (by decide) (by decide)).mp
        (fun n hn => (WindowCore.triple21_all_good n hn).1)
    · exact (good_all_iff_pseudonorm (by decide) (by decide) (by decide)).mp
        (fun n hn => (WindowCore.triple21_all_good n hn).2.1)
    · exact (good_all_iff_pseudonorm (by decide) (by decide) (by decide)).mp
        (fun n hn => (WindowCore.triple21_all_good n hn).2.2)
  refine ⟨hw, ?_⟩
  intro k hk hlt hin
  apply WindowCore.triple21_no_smaller_integer hk hlt
  intro n hn
  exact ⟨(good_all_iff_pseudonorm (by decide) (by decide) hk).mpr (hin (2, 1) (by simp)) n hn,
    (good_all_iff_pseudonorm (by decide) (by decide) (Nat.zero_le k)).mpr (hin (3, 0) (by simp)) n hn,
    (good_all_iff_pseudonorm (by decide) (by decide) (Nat.zero_le k)).mpr (hin (5, 0) (by simp)) n hn⟩

#print axioms triple21_real_minimum
end LeanCheck.TVGSearch
