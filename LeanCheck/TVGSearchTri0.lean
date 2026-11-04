import LeanCheck.TVGPlusSearchLeast

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace LeanCheck
namespace TVGSearch

/-- The primes with their shifts. -/
def ps_tri0 : List (Prod Nat Nat) := [(2, 0), (3, 0), (5, 0)]

-- plateau m = 3..3, u = 60; |T2|=5 |T3|=3 pairs+tree=30 candidates=10 N=2 chunks=1
theorem setup_tri0_3_3 : searchSetup 2 5 2 1 1 59 = true := by decide +kernel
theorem chunk_tri0_3_3_0 : searchChunk' 2 5 0 0 [(3, 0)] 3 2 1 1 59 2 0 16 = true := by decide +kernel
theorem chunks_tri0_3_3 : ChunkOK 2 5 0 0 [(3, 0)] 3 2 1 1 59 2 0 (2 ^ (2 * 2)) := by
  have h := searchChunk'_spec chunk_tri0_3_3_0
  exact h
theorem mem_tri0_3_3 : memAll ((2, 0) :: (5, 0) :: [(3, 0)]) 60 21 81 2 = true := by decide +kernel
theorem leastOn_tri0_3_3 : LeastOn ps_tri0 3 3 60 :=
  LeastOn_perm (by decide) (least_of_search (lo := 3) (hi := 3) (u := 60) (X := 59) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_3_3 chunks_tri0_3_3 (by decide) mem_tri0_3_3)

-- plateau m = 4..4, u = 66; |T2|=3 |T3|=3 pairs+tree=24 candidates=7 N=2 chunks=1
theorem setup_tri0_4_4 : searchSetup 2 5 2 1 1 65 = true := by decide +kernel
theorem chunk_tri0_4_4_0 : searchChunk' 2 5 0 0 [(3, 0)] 4 2 1 1 65 2 0 16 = true := by decide +kernel
theorem chunks_tri0_4_4 : ChunkOK 2 5 0 0 [(3, 0)] 4 2 1 1 65 2 0 (2 ^ (2 * 2)) := by
  have h := searchChunk'_spec chunk_tri0_4_4_0
  exact h
theorem mem_tri0_4_4 : memAll ((2, 0) :: (5, 0) :: [(3, 0)]) 66 1 5 2 = true := by decide +kernel
theorem leastOn_tri0_4_4 : LeastOn ps_tri0 4 4 66 :=
  LeastOn_perm (by decide) (least_of_search (lo := 4) (hi := 4) (u := 66) (X := 65) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_4_4 chunks_tri0_4_4 (by decide) mem_tri0_4_4)

-- plateau m = 5..5, u = 1950; |T2|=39 |T3|=1 pairs+tree=150 candidates=27 N=2 chunks=1
theorem setup_tri0_5_5 : searchSetup 2 5 3 1 3 1949 = true := by decide +kernel
theorem chunk_tri0_5_5_0 : searchChunk' 2 5 0 0 [(3, 0)] 5 3 1 3 1949 2 0 512 = true := by decide +kernel
theorem chunks_tri0_5_5 : ChunkOK 2 5 0 0 [(3, 0)] 5 3 1 3 1949 2 0 (2 ^ (3 * 3)) := by
  have h := searchChunk'_spec chunk_tri0_5_5_0
  exact h
theorem mem_tri0_5_5 : memAll ((2, 0) :: (5, 0) :: [(3, 0)]) 1950 98 512 3 = true := by decide +kernel
theorem leastOn_tri0_5_5 : LeastOn ps_tri0 5 5 1950 :=
  LeastOn_perm (by decide) (least_of_search (lo := 5) (hi := 5) (u := 1950) (X := 1949) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_5_5 chunks_tri0_5_5 (by decide) mem_tri0_5_5)

-- plateau m = 6..6, u = 3090; |T2|=3 |T3|=41 pairs+tree=263 candidates=37 N=2 chunks=1
theorem setup_tri0_6_6 : searchSetup 2 5 2 2 586 3089 = true := by decide +kernel
theorem chunk_tri0_6_6_0 : searchChunk' 2 5 0 0 [(3, 0)] 6 2 2 586 3089 2 0 16 = true := by decide +kernel
theorem chunks_tri0_6_6 : ChunkOK 2 5 0 0 [(3, 0)] 6 2 2 586 3089 2 0 (2 ^ (2 * 2)) := by
  have h := searchChunk'_spec chunk_tri0_6_6_0
  exact h
theorem mem_tri0_6_6 : memAll ((2, 0) :: (5, 0) :: [(3, 0)]) 3090 3090 19683 3 = true := by decide +kernel
theorem leastOn_tri0_6_6 : LeastOn ps_tri0 6 6 3090 :=
  LeastOn_perm (by decide) (least_of_search (lo := 6) (hi := 6) (u := 3090) (X := 3089) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_6_6 chunks_tri0_6_6 (by decide) mem_tri0_6_6)

-- plateau m = 7..7, u = 138750; |T2|=27 |T3|=35 pairs+tree=1181 candidates=408 N=3 chunks=1
theorem setup_tri0_7_7 : searchSetup 2 5 3 2 448 138749 = true := by decide +kernel
theorem chunk_tri0_7_7_0 : searchChunk' 2 5 0 0 [(3, 0)] 7 3 2 448 138749 3 0 512 = true := by decide +kernel
theorem chunks_tri0_7_7 : ChunkOK 2 5 0 0 [(3, 0)] 7 3 2 448 138749 3 0 (2 ^ (3 * 3)) := by
  have h := searchChunk'_spec chunk_tri0_7_7_0
  exact h
theorem mem_tri0_7_7 : memAll ((2, 0) :: (5, 0) :: [(3, 0)]) 138750 2 16 4 = true := by decide +kernel
theorem leastOn_tri0_7_7 : LeastOn ps_tri0 7 7 138750 :=
  LeastOn_perm (by decide) (least_of_search (lo := 7) (hi := 7) (u := 138750) (X := 138749) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_7_7 chunks_tri0_7_7 (by decide) mem_tri0_7_7)

-- plateau m = 8..8, u = 1970640; |T2|=223 |T3|=7 pairs+tree=2529 candidates=578 N=3 chunks=1
theorem setup_tri0_8_8 : searchSetup 2 3 4 2 58 1970639 = true := by decide +kernel
theorem chunk_tri0_8_8_0 : searchChunk' 2 3 0 0 [(5, 0)] 8 4 2 58 1970639 3 0 65536 = true := by decide +kernel
theorem chunks_tri0_8_8 : ChunkOK 2 3 0 0 [(5, 0)] 8 4 2 58 1970639 3 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_tri0_8_8_0
  exact h
theorem mem_tri0_8_8 : memAll ((2, 0) :: (3, 0) :: [(5, 0)]) 1970640 2340 19683 4 = true := by decide +kernel
theorem leastOn_tri0_8_8 : LeastOn ps_tri0 8 8 1970640 :=
  LeastOn_perm (by decide) (least_of_search (lo := 8) (hi := 8) (u := 1970640) (X := 1970639) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_8_8 chunks_tri0_8_8 (by decide) mem_tri0_8_8)

-- plateau m = 9..9, u = 130675680; |T2|=203 |T3|=269 pairs+tree=56790 candidates=5535 N=3 chunks=1
theorem setup_tri0_9_9 : searchSetup 2 3 4 3 12856 130675679 = true := by decide +kernel
theorem chunk_tri0_9_9_0 : searchChunk' 2 3 0 0 [(5, 0)] 9 4 3 12856 130675679 3 0 65536 = true := by decide +kernel
theorem chunks_tri0_9_9 : ChunkOK 2 3 0 0 [(5, 0)] 9 4 3 12856 130675679 3 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_tri0_9_9_0
  exact h
theorem mem_tri0_9_9 : memAll ((2, 0) :: (3, 0) :: [(5, 0)]) 130675680 3542048 33554432 5 = true := by decide +kernel
theorem leastOn_tri0_9_9 : LeastOn ps_tri0 9 9 130675680 :=
  LeastOn_perm (by decide) (least_of_search (lo := 9) (hi := 9) (u := 130675680) (X := 130675679) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_9_9 chunks_tri0_9_9 (by decide) mem_tri0_9_9)

-- plateau m = 10..10, u = 169866240; |T2|=175 |T3|=245 pairs+tree=45058 candidates=5642 N=3 chunks=1
theorem setup_tri0_10_10 : searchSetup 2 3 4 3 12856 169866239 = true := by decide +kernel
theorem chunk_tri0_10_10_0 : searchChunk' 2 3 0 0 [(5, 0)] 10 4 3 12856 169866239 3 0 65536 = true := by decide +kernel
theorem chunks_tri0_10_10 : ChunkOK 2 3 0 0 [(5, 0)] 10 4 3 12856 169866239 3 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_tri0_10_10_0
  exact h
theorem mem_tri0_10_10 : memAll ((2, 0) :: (3, 0) :: [(5, 0)]) 169866240 1950 19683 5 = true := by decide +kernel
theorem leastOn_tri0_10_10 : LeastOn ps_tri0 10 10 169866240 :=
  LeastOn_perm (by decide) (least_of_search (lo := 10) (hi := 10) (u := 169866240) (X := 169866239) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_10_10 chunks_tri0_10_10 (by decide) mem_tri0_10_10)

-- plateau m = 11..11, u = 300814320; |T2|=115 |T3|=225 pairs+tree=27802 candidates=6032 N=3 chunks=1
theorem setup_tri0_11_11 : searchSetup 2 3 4 3 12856 300814319 = true := by decide +kernel
theorem chunk_tri0_11_11_0 : searchChunk' 2 3 0 0 [(5, 0)] 11 4 3 12856 300814319 3 0 65536 = true := by decide +kernel
theorem chunks_tri0_11_11 : ChunkOK 2 3 0 0 [(5, 0)] 11 4 3 12856 300814319 3 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_tri0_11_11_0
  exact h
theorem mem_tri0_11_11 : memAll ((2, 0) :: (3, 0) :: [(5, 0)]) 300814320 55 625 5 = true := by decide +kernel
theorem leastOn_tri0_11_11 : LeastOn ps_tri0 11 11 300814320 :=
  LeastOn_perm (by decide) (least_of_search (lo := 11) (hi := 11) (u := 300814320) (X := 300814319) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_11_11 chunks_tri0_11_11 (by decide) mem_tri0_11_11)

-- plateau m = 12..13, u = 601551840; |T2|=105 |T3|=205 pairs+tree=23452 candidates=10033 N=3 chunks=1
theorem setup_tri0_12_13 : searchSetup 2 3 4 3 12856 601551839 = true := by decide +kernel
theorem chunk_tri0_12_13_0 : searchChunk' 2 3 0 0 [(5, 0)] 12 4 3 12856 601551839 3 0 65536 = true := by decide +kernel
theorem chunks_tri0_12_13 : ChunkOK 2 3 0 0 [(5, 0)] 12 4 3 12856 601551839 3 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_tri0_12_13_0
  exact h
theorem mem_tri0_12_13 : memAll ((2, 0) :: (3, 0) :: [(5, 0)]) 601551840 6 81 5 = true := by decide +kernel
theorem leastOn_tri0_12_13 : LeastOn ps_tri0 12 13 601551840 :=
  LeastOn_perm (by decide) (least_of_search (lo := 12) (hi := 13) (u := 601551840) (X := 601551839) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_12_13 chunks_tri0_12_13 (by decide) mem_tri0_12_13)

-- plateau m = 14..14, u = 1507856880; |T2|=6935 |T3|=3 pairs+tree=70157 candidates=11448 N=3 chunks=1
theorem setup_tri0_14_14 : searchSetup 2 3 5 2 77 1507856879 = true := by decide +kernel
theorem chunk_tri0_14_14_0 : searchChunk' 2 3 0 0 [(5, 0)] 14 5 2 77 1507856879 3 0 33554432 = true := by decide +kernel
theorem chunks_tri0_14_14 : ChunkOK 2 3 0 0 [(5, 0)] 14 5 2 77 1507856879 3 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_tri0_14_14_0
  exact h
theorem mem_tri0_14_14 : memAll ((2, 0) :: (3, 0) :: [(5, 0)]) 1507856880 4592 65536 5 = true := by decide +kernel
theorem leastOn_tri0_14_14 : LeastOn ps_tri0 14 14 1507856880 :=
  LeastOn_perm (by decide) (least_of_search (lo := 14) (hi := 14) (u := 1507856880) (X := 1507856879) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_14_14 chunks_tri0_14_14 (by decide) mem_tri0_14_14)

-- plateau m = 15..20, u = 3054762480; |T2|=5865 |T3|=17 pairs+tree=144037 candidates=14555 N=4 chunks=1
theorem setup_tri0_15_20 : searchSetup 2 5 5 2 318 3054762479 = true := by decide +kernel
theorem chunk_tri0_15_20_0 : searchChunk' 2 5 0 0 [(3, 0)] 15 5 2 318 3054762479 4 0 33554432 = true := by decide +kernel
theorem chunks_tri0_15_20 : ChunkOK 2 5 0 0 [(3, 0)] 15 5 2 318 3054762479 4 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_tri0_15_20_0
  exact h
theorem mem_tri0_15_20 : memAll ((2, 0) :: (5, 0) :: [(3, 0)]) 3054762480 3054762480 68719476736 6 = true := by decide +kernel
theorem leastOn_tri0_15_20 : LeastOn ps_tri0 15 20 3054762480 :=
  LeastOn_perm (by decide) (least_of_search (lo := 15) (hi := 20) (u := 3054762480) (X := 3054762479) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_tri0_15_20 chunks_tri0_15_20 (by decide) mem_tri0_15_20)

end TVGSearch
end LeanCheck
