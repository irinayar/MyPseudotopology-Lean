import LeanCheck.TVGPlusSearchLeast
import LeanCheck.TVGSearchPart_tri0_23_26_0
import LeanCheck.TVGSearchPart_tri0_23_26_1
import LeanCheck.TVGSearchPart_tri0_23_26_2
import LeanCheck.TVGSearchPart_tri0_23_26_3
import LeanCheck.TVGSearchPart_tri0_23_26_4
import LeanCheck.TVGSearchPart_tri0_23_26_5
import LeanCheck.TVGSearchPart_tri0_23_26_6
import LeanCheck.TVGSearchPart_tri0_23_26_7

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace LeanCheck
namespace TVGSearch

/-- The primes with their shifts. -/
def ps_tri0Hi : List (Prod Nat Nat) := [(2, 0), (3, 0), (5, 0)]

-- plateau m = 21..22, u = 3054762480; |T2|=1911 |T3|=11 pairs+tree=41545 candidates=3072 N=4 chunks=1
theorem setup_tri0_21_22 : searchSetup 2 5 5 2 318 3054762479 = true := by decide +kernel
theorem chunk_tri0_21_22_0 : searchChunk' 2 5 0 0 [(3, 0)] 21 5 2 318 3054762479 4 0 33554432 = true := by decide +kernel
theorem chunks_tri0_21_22 : ChunkOK 2 5 0 0 [(3, 0)] 21 5 2 318 3054762479 4 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_tri0_21_22_0
  exact h
theorem mem_tri0_21_22 : memAll ((2, 0) :: (5, 0) :: [(3, 0)]) 3054762480 3054762480 68719476736 6 = true := by decide +kernel
theorem leastOn_tri0_21_22 : LeastOn ps_tri0Hi 21 22 3054762480 :=
  LeastOn_perm (by decide) (least_of_search (lo := 21) (hi := 22) (u := 3054762480) (X := 3054762479) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_21_22 chunks_tri0_21_22 (by decide) mem_tri0_21_22)

-- plateau m = 23..26, u = 15258341867520; |T2|=1485 |T3|=2981 pairs+tree=4478612 candidates=1030661 N=4 chunks=8
theorem setup_tri0_23_26 : searchSetup 2 5 5 3 1775318 15258341867519 = true := by decide +kernel
theorem chunks_tri0_23_26 : ChunkOK 2 5 0 0 [(3, 0)] 23 5 3 1775318 15258341867519 4 0 (2 ^ (5 * 5)) := by
  have h := ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (searchChunk'_spec chunk_tri0_23_26_0) (searchChunk'_spec chunk_tri0_23_26_1)) (searchChunk'_spec chunk_tri0_23_26_2)) (searchChunk'_spec chunk_tri0_23_26_3)) (searchChunk'_spec chunk_tri0_23_26_4)) (searchChunk'_spec chunk_tri0_23_26_5)) (searchChunk'_spec chunk_tri0_23_26_6)) (searchChunk'_spec chunk_tri0_23_26_7)
  exact h
theorem mem_tri0_23_26 : memAll ((2, 0) :: (5, 0) :: [(3, 0)]) 15258341867520 2618032128 68719476736 6 = true := by decide +kernel
theorem leastOn_tri0_23_26 : LeastOn ps_tri0Hi 23 26 15258341867520 :=
  LeastOn_perm (by decide) (least_of_search (lo := 23) (hi := 26) (u := 15258341867520) (X := 15258341867519) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_23_26 chunks_tri0_23_26 (by decide) mem_tri0_23_26)

end TVGSearch
end LeanCheck
