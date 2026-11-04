import LeanCheck.TVGPlusSearchLeast

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace LeanCheck
namespace TVGSearch

/-- The primes with their shifts. -/
def ps_triA : List (Prod Nat Nat) := [(2, 1), (3, 0), (5, 0)]

-- plateau m = 3..5, u = 15; |T2|=1 |T3|=3 pairs+tree=11 candidates=2 N=2 chunks=1
theorem setup_triA_3_5 : searchSetup 3 5 1 1 2 14 = true := by decide +kernel
theorem chunk_triA_3_5_0 : searchChunk' 3 5 0 0 [(2, 1)] 3 1 1 2 14 2 0 3 = true := by decide +kernel
theorem chunks_triA_3_5 : ChunkOK 3 5 0 0 [(2, 1)] 3 1 1 2 14 2 0 (3 ^ (1 * 1)) := by
  have h := searchChunk'_spec chunk_triA_3_5_0
  exact h
theorem mem_triA_3_5 : memAll ((3, 0) :: (5, 0) :: [(2, 1)]) 15 15 81 2 = true := by decide +kernel
theorem leastOn_triA_3_5 : LeastOn ps_triA 3 5 15 :=
  LeastOn_perm (by decide) (least_of_search (lo := 3) (hi := 5) (u := 15) (X := 14) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_triA_3_5 chunks_triA_3_5 (by decide) mem_triA_3_5)

-- plateau m = 6..6, u = 2595; |T2|=3 |T3|=41 pairs+tree=263 candidates=34 N=2 chunks=1
theorem setup_triA_6_6 : searchSetup 2 5 2 2 586 2594 = true := by decide +kernel
theorem chunk_triA_6_6_0 : searchChunk' 2 5 1 0 [(3, 0)] 6 2 2 586 2594 2 0 16 = true := by decide +kernel
theorem chunks_triA_6_6 : ChunkOK 2 5 1 0 [(3, 0)] 6 2 2 586 2594 2 0 (2 ^ (2 * 2)) := by
  have h := searchChunk'_spec chunk_triA_6_6_0
  exact h
theorem mem_triA_6_6 : memAll ((2, 1) :: (5, 0) :: [(3, 0)]) 2595 95 625 3 = true := by decide +kernel
theorem leastOn_triA_6_6 : LeastOn ps_triA 6 6 2595 :=
  LeastOn_perm (by decide) (least_of_search (lo := 6) (hi := 6) (u := 2595) (X := 2594) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_triA_6_6 chunks_triA_6_6 (by decide) mem_triA_6_6)

-- plateau m = 7..7, u = 56865; |T2|=27 |T3|=35 pairs+tree=1181 candidates=171 N=3 chunks=1
theorem setup_triA_7_7 : searchSetup 2 5 3 2 448 56864 = true := by decide +kernel
theorem chunk_triA_7_7_0 : searchChunk' 2 5 1 0 [(3, 0)] 7 3 2 448 56864 3 0 512 = true := by decide +kernel
theorem chunks_triA_7_7 : ChunkOK 2 5 1 0 [(3, 0)] 7 3 2 448 56864 3 0 (2 ^ (3 * 3)) := by
  have h := searchChunk'_spec chunk_triA_7_7_0
  exact h
theorem mem_triA_7_7 : memAll ((2, 1) :: (5, 0) :: [(3, 0)]) 56865 8672 65536 4 = true := by decide +kernel
theorem leastOn_triA_7_7 : LeastOn ps_triA 7 7 56865 :=
  LeastOn_perm (by decide) (least_of_search (lo := 7) (hi := 7) (u := 56865) (X := 56864) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_triA_7_7 chunks_triA_7_7 (by decide) mem_triA_7_7)

-- plateau m = 8..8, u = 1831905; |T2|=223 |T3|=7 pairs+tree=2529 candidates=518 N=3 chunks=1
theorem setup_triA_8_8 : searchSetup 2 3 4 2 58 1831904 = true := by decide +kernel
theorem chunk_triA_8_8_0 : searchChunk' 2 3 1 0 [(5, 0)] 8 4 2 58 1831904 3 0 65536 = true := by decide +kernel
theorem chunks_triA_8_8 : ChunkOK 2 3 1 0 [(5, 0)] 8 4 2 58 1831904 3 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_triA_8_8_0
  exact h
theorem mem_triA_8_8 : memAll ((2, 1) :: (3, 0) :: [(5, 0)]) 1831905 9 81 4 = true := by decide +kernel
theorem leastOn_triA_8_8 : LeastOn ps_triA 8 8 1831905 :=
  LeastOn_perm (by decide) (least_of_search (lo := 8) (hi := 8) (u := 1831905) (X := 1831904) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_triA_8_8 chunks_triA_8_8 (by decide) mem_triA_8_8)

-- plateau m = 9..13, u = 2027505; |T2|=203 |T3|=5 pairs+tree=1983 candidates=383 N=3 chunks=1
theorem setup_triA_9_13 : searchSetup 2 3 4 2 58 2027504 = true := by decide +kernel
theorem chunk_triA_9_13_0 : searchChunk' 2 3 1 0 [(5, 0)] 9 4 2 58 2027504 3 0 65536 = true := by decide +kernel
theorem chunks_triA_9_13 : ChunkOK 2 3 1 0 [(5, 0)] 9 4 2 58 2027504 3 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_triA_9_13_0
  exact h
theorem mem_triA_9_13 : memAll ((2, 1) :: (3, 0) :: [(5, 0)]) 2027505 6 81 4 = true := by decide +kernel
theorem leastOn_triA_9_13 : LeastOn ps_triA 9 13 2027505 :=
  LeastOn_perm (by decide) (least_of_search (lo := 9) (hi := 13) (u := 2027505) (X := 2027504) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_triA_9_13 chunks_triA_9_13 (by decide) mem_triA_9_13)

-- plateau m = 14..14, u = 1675752465; |T2|=6935 |T3|=3 pairs+tree=70157 candidates=12743 N=3 chunks=1
theorem setup_triA_14_14 : searchSetup 2 3 5 2 77 1675752464 = true := by decide +kernel
theorem chunk_triA_14_14_0 : searchChunk' 2 3 1 0 [(5, 0)] 14 5 2 77 1675752464 3 0 33554432 = true := by decide +kernel
theorem chunks_triA_14_14 : ChunkOK 2 3 1 0 [(5, 0)] 14 5 2 77 1675752464 3 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_triA_14_14_0
  exact h
theorem mem_triA_14_14 : memAll ((2, 1) :: (3, 0) :: [(5, 0)]) 1675752465 3069654 43046721 5 = true := by decide +kernel
theorem leastOn_triA_14_14 : LeastOn ps_triA 14 14 1675752465 :=
  LeastOn_perm (by decide) (least_of_search (lo := 14) (hi := 14) (u := 1675752465) (X := 1675752464) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_triA_14_14 chunks_triA_14_14 (by decide) mem_triA_14_14)

-- plateau m = 15..20, u = 3187406865; |T2|=5865 |T3|=17 pairs+tree=144037 candidates=15142 N=4 chunks=1
theorem setup_triA_15_20 : searchSetup 2 5 5 2 318 3187406864 = true := by decide +kernel
theorem chunk_triA_15_20_0 : searchChunk' 2 5 1 0 [(3, 0)] 15 5 2 318 3187406864 4 0 33554432 = true := by decide +kernel
theorem chunks_triA_15_20 : ChunkOK 2 5 1 0 [(3, 0)] 15 5 2 318 3187406864 4 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_triA_15_20_0
  exact h
theorem mem_triA_15_20 : memAll ((2, 1) :: (5, 0) :: [(3, 0)]) 3187406865 93135 1953125 5 = true := by decide +kernel
theorem leastOn_triA_15_20 : LeastOn ps_triA 15 20 3187406865 :=
  LeastOn_perm (by decide) (least_of_search (lo := 15) (hi := 20) (u := 3187406865) (X := 3187406864) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_triA_15_20 chunks_triA_15_20 (by decide) mem_triA_15_20)

end TVGSearch
end LeanCheck
