import LeanCheck.TVGPlusSearchLeast

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace LeanCheck
namespace TVGSearch

/-- The primes with their shifts. -/
def ps_triAm : List (Prod Nat Nat) := [(2, 1), (3, 0), (5, 0)]

theorem memw_triAm_21_21 : memAll ps_triAm 566864750054385 3056 65536 7 = true := by decide +kernel
theorem witness_triAm_21_21 : forall m, 21 <= m -> m <= 21 -> ShiftedIn ps_triAm m 566864750054385 :=
  shifted_of_mem (by decide) (by decide) (by decide) (by decide) memw_triAm_21_21

theorem memw_triAm_22_23 : memAll ps_triAm 1111607529308145 1441808 33554432 7 = true := by decide +kernel
theorem witness_triAm_22_23 : forall m, 22 <= m -> m <= 23 -> ShiftedIn ps_triAm m 1111607529308145 :=
  shifted_of_mem (by decide) (by decide) (by decide) (by decide) memw_triAm_22_23

theorem memw_triAm_24_26 : memAll ps_triAm 1667477197289985 21372662973952 562949953421312 7 = true := by decide +kernel
theorem witness_triAm_24_26 : forall m, 24 <= m -> m <= 26 -> ShiftedIn ps_triAm m 1667477197289985 :=
  shifted_of_mem (by decide) (by decide) (by decide) (by decide) memw_triAm_24_26

end TVGSearch
end LeanCheck
