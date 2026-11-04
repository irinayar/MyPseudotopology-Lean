import LeanCheck.TVGPlusSearchLeast

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace LeanCheck
namespace TVGSearch

/-- The primes with their shifts. -/
def ps_shA : List (Prod Nat Nat) := [(2, 1), (3, 0)]

-- plateau m = 3..7, u = 3; |T2|=1 |T3|=1 pairs+tree=6 candidates=0 N=1 chunks=1
theorem setup_shA_3_7 : searchSetup 2 3 1 1 2 2 = true := by decide +kernel
theorem chunk_shA_3_7_0 : searchChunk' 2 3 1 0 [] 3 1 1 2 2 1 0 2 = true := by decide +kernel
theorem chunks_shA_3_7 : ChunkOK 2 3 1 0 [] 3 1 1 2 2 1 0 (2 ^ (1 * 1)) := by
  have h := searchChunk'_spec chunk_shA_3_7_0
  exact h
theorem mem_shA_3_7 : memAll ((2, 1) :: (3, 0) :: []) 3 2 16 2 = true := by decide +kernel
theorem leastOn_shA_3_7 : LeastOn ps_shA 3 7 3 :=
  LeastOn_perm (by decide) (least_of_search (lo := 3) (hi := 7) (u := 3) (X := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_3_7 chunks_shA_3_7 (by decide) mem_shA_3_7)

-- plateau m = 8..10, u = 561; |T2|=1 |T3|=7 pairs+tree=47 candidates=2 N=1 chunks=1
theorem setup_shA_8_10 : searchSetup 2 3 2 2 76 560 = true := by decide +kernel
theorem chunk_shA_8_10_0 : searchChunk' 2 3 1 0 [] 8 2 2 76 560 1 0 16 = true := by decide +kernel
theorem chunks_shA_8_10 : ChunkOK 2 3 1 0 [] 8 2 2 76 560 1 0 (2 ^ (2 * 2)) := by
  have h := searchChunk'_spec chunk_shA_8_10_0
  exact h
theorem mem_shA_8_10 : memAll ((2, 1) :: (3, 0) :: []) 561 48 512 3 = true := by decide +kernel
theorem leastOn_shA_8_10 : LeastOn ps_shA 8 10 561 :=
  LeastOn_perm (by decide) (least_of_search (lo := 8) (hi := 10) (u := 561) (X := 560) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_8_10 chunks_shA_8_10 (by decide) mem_shA_8_10)

-- plateau m = 11..11, u = 59937; |T2|=115 |T3|=1 pairs+tree=800 candidates=20 N=1 chunks=1
theorem setup_shA_11_11 : searchSetup 2 3 4 1 1 59936 = true := by decide +kernel
theorem chunk_shA_11_11_0 : searchChunk' 2 3 1 0 [] 11 4 1 1 59936 1 0 65536 = true := by decide +kernel
theorem chunks_shA_11_11 : ChunkOK 2 3 1 0 [] 11 4 1 1 59936 1 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shA_11_11_0
  exact h
theorem mem_shA_11_11 : memAll ((2, 1) :: (3, 0) :: []) 59937 5600 65536 4 = true := by decide +kernel
theorem leastOn_shA_11_11 : LeastOn ps_shA 11 11 59937 :=
  LeastOn_perm (by decide) (least_of_search (lo := 11) (hi := 11) (u := 59937) (X := 59936) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_11_11 chunks_shA_11_11 (by decide) mem_shA_11_11)

-- plateau m = 12..12, u = 136161; |T2|=105 |T3|=1 pairs+tree=790 candidates=85 N=2 chunks=1
theorem setup_shA_12_12 : searchSetup 2 3 4 1 1 136160 = true := by decide +kernel
theorem chunk_shA_12_12_0 : searchChunk' 2 3 1 0 [] 12 4 1 1 136160 2 0 65536 = true := by decide +kernel
theorem chunks_shA_12_12 : ChunkOK 2 3 1 0 [] 12 4 1 1 136160 2 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shA_12_12_0
  exact h
theorem mem_shA_12_12 : memAll ((2, 1) :: (3, 0) :: []) 136161 1620 19683 4 = true := by decide +kernel
theorem leastOn_shA_12_12 : LeastOn ps_shA 12 12 136161 :=
  LeastOn_perm (by decide) (least_of_search (lo := 12) (hi := 12) (u := 136161) (X := 136160) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_12_12 chunks_shA_12_12 (by decide) mem_shA_12_12)

-- plateau m = 13..13, u = 196593; |T2|=95 |T3|=1 pairs+tree=780 candidates=94 N=2 chunks=1
theorem setup_shA_13_13 : searchSetup 2 3 4 1 1 196592 = true := by decide +kernel
theorem chunk_shA_13_13_0 : searchChunk' 2 3 1 0 [] 13 4 1 1 196592 2 0 65536 = true := by decide +kernel
theorem chunks_shA_13_13 : ChunkOK 2 3 1 0 [] 13 4 1 1 196592 2 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shA_13_13_0
  exact h
theorem mem_shA_13_13 : memAll ((2, 1) :: (3, 0) :: []) 196593 6 81 4 = true := by decide +kernel
theorem leastOn_shA_13_13 : LeastOn ps_shA 13 13 196593 :=
  LeastOn_perm (by decide) (least_of_search (lo := 13) (hi := 13) (u := 196593) (X := 196592) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_13_13 chunks_shA_13_13 (by decide) mem_shA_13_13)

-- plateau m = 14..15, u = 198129; |T2|=1 |T3|=105 pairs+tree=874 candidates=68 N=2 chunks=1
theorem setup_shA_14_15 : searchSetup 2 3 2 3 6151 198128 = true := by decide +kernel
theorem chunk_shA_14_15_0 : searchChunk' 2 3 1 0 [] 14 2 3 6151 198128 2 0 16 = true := by decide +kernel
theorem chunks_shA_14_15 : ChunkOK 2 3 1 0 [] 14 2 3 6151 198128 2 0 (2 ^ (2 * 2)) := by
  have h := searchChunk'_spec chunk_shA_14_15_0
  exact h
theorem mem_shA_14_15 : memAll ((2, 1) :: (3, 0) :: []) 198129 1299 19683 4 = true := by decide +kernel
theorem leastOn_shA_14_15 : LeastOn ps_shA 14 15 198129 :=
  LeastOn_perm (by decide) (least_of_search (lo := 14) (hi := 15) (u := 198129) (X := 198128) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_14_15 chunks_shA_14_15 (by decide) mem_shA_14_15)

-- plateau m = 16..16, u = 2028561; |T2|=47 |T3|=3 pairs+tree=597 candidates=51 N=1 chunks=1
theorem setup_shA_16_16 : searchSetup 2 3 4 2 58 2028560 = true := by decide +kernel
theorem chunk_shA_16_16_0 : searchChunk' 2 3 1 0 [] 16 4 2 58 2028560 1 0 65536 = true := by decide +kernel
theorem chunks_shA_16_16 : ChunkOK 2 3 1 0 [] 16 4 2 58 2028560 1 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shA_16_16_0
  exact h
theorem mem_shA_16_16 : memAll ((2, 1) :: (3, 0) :: []) 2028561 1212 19683 4 = true := by decide +kernel
theorem leastOn_shA_16_16 : LeastOn ps_shA 16 16 2028561 :=
  LeastOn_perm (by decide) (least_of_search (lo := 16) (hi := 16) (u := 2028561) (X := 2028560) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_16_16 chunks_shA_16_16 (by decide) mem_shA_16_16)

-- plateau m = 17..17, u = 300086289; |T2|=45 |T3|=87 pairs+tree=5100 candidates=913 N=1 chunks=1
theorem setup_shA_17_17 : searchSetup 2 3 4 3 12856 300086288 = true := by decide +kernel
theorem chunk_shA_17_17_0 : searchChunk' 2 3 1 0 [] 17 4 3 12856 300086288 1 0 65536 = true := by decide +kernel
theorem chunks_shA_17_17 : ChunkOK 2 3 1 0 [] 17 4 3 12856 300086288 1 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shA_17_17_0
  exact h
theorem mem_shA_17_17 : memAll ((2, 1) :: (3, 0) :: []) 300086289 1903600 33554432 5 = true := by decide +kernel
theorem leastOn_shA_17_17 : LeastOn ps_shA 17 17 300086289 :=
  LeastOn_perm (by decide) (least_of_search (lo := 17) (hi := 17) (u := 300086289) (X := 300086288) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_17_17 chunks_shA_17_17 (by decide) mem_shA_17_17)

-- plateau m = 18..22, u = 300480513; |T2|=45 |T3|=81 pairs+tree=4830 candidates=847 N=1 chunks=1
theorem setup_shA_18_22 : searchSetup 2 3 4 3 12856 300480512 = true := by decide +kernel
theorem chunk_shA_18_22_0 : searchChunk' 2 3 1 0 [] 18 4 3 12856 300480512 1 0 65536 = true := by decide +kernel
theorem chunks_shA_18_22 : ChunkOK 2 3 1 0 [] 18 4 3 12856 300480512 1 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shA_18_22_0
  exact h
theorem mem_shA_18_22 : memAll ((2, 1) :: (3, 0) :: []) 300480513 1509376 33554432 5 = true := by decide +kernel
theorem leastOn_shA_18_22 : LeastOn ps_shA 18 22 300480513 :=
  LeastOn_perm (by decide) (least_of_search (lo := 18) (hi := 22) (u := 300480513) (X := 300480512) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_18_22 chunks_shA_18_22 (by decide) mem_shA_18_22)

-- plateau m = 23..30, u = 300874257; |T2|=33 |T3|=63 pairs+tree=3264 candidates=482 N=1 chunks=1
theorem setup_shA_23_30 : searchSetup 2 3 4 3 12856 300874256 = true := by decide +kernel
theorem chunk_shA_23_30_0 : searchChunk' 2 3 1 0 [] 23 4 3 12856 300874256 1 0 65536 = true := by decide +kernel
theorem chunks_shA_23_30 : ChunkOK 2 3 1 0 [] 23 4 3 12856 300874256 1 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shA_23_30_0
  exact h
theorem mem_shA_23_30 : memAll ((2, 1) :: (3, 0) :: []) 300874257 1115632 33554432 5 = true := by decide +kernel
theorem leastOn_shA_23_30 : LeastOn ps_shA 23 30 300874257 :=
  LeastOn_perm (by decide) (least_of_search (lo := 23) (hi := 30) (u := 300874257) (X := 300874256) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_23_30 chunks_shA_23_30 (by decide) mem_shA_23_30)

-- plateau m = 31..31, u = 301662225; |T2|=27 |T3|=15 pairs+tree=1104 candidates=96 N=1 chunks=1
theorem setup_shA_31_31 : searchSetup 2 3 4 3 12856 301662224 = true := by decide +kernel
theorem chunk_shA_31_31_0 : searchChunk' 2 3 1 0 [] 31 4 3 12856 301662224 1 0 65536 = true := by decide +kernel
theorem chunks_shA_31_31 : ChunkOK 2 3 1 0 [] 31 4 3 12856 301662224 1 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shA_31_31_0
  exact h
theorem mem_shA_31_31 : memAll ((2, 1) :: (3, 0) :: []) 301662225 16 512 5 = true := by decide +kernel
theorem leastOn_shA_31_31 : LeastOn ps_shA 31 31 301662225 :=
  LeastOn_perm (by decide) (least_of_search (lo := 31) (hi := 31) (u := 301662225) (X := 301662224) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_31_31 chunks_shA_31_31 (by decide) mem_shA_31_31)

-- plateau m = 32..48, u = 302054913; |T2|=7 |T3|=15 pairs+tree=548 candidates=24 N=1 chunks=1
theorem setup_shA_32_48 : searchSetup 2 3 4 3 12856 302054912 = true := by decide +kernel
theorem chunk_shA_32_48_0 : searchChunk' 2 3 1 0 [] 32 4 3 12856 302054912 1 0 65536 = true := by decide +kernel
theorem chunks_shA_32_48 : ChunkOK 2 3 1 0 [] 32 4 3 12856 302054912 1 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shA_32_48_0
  exact h
theorem mem_shA_32_48 : memAll ((2, 1) :: (3, 0) :: []) 302054913 405 19683 5 = true := by decide +kernel
theorem leastOn_shA_32_48 : LeastOn ps_shA 32 48 302054913 :=
  LeastOn_perm (by decide) (least_of_search (lo := 32) (hi := 48) (u := 302054913) (X := 302054912) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_32_48 chunks_shA_32_48 (by decide) mem_shA_32_48)

-- plateau m = 49..63, u = 7627190764545; |T2|=105 |T3|=801 pairs+tree=106791 candidates=445 N=1 chunks=1
theorem setup_shA_49_63 : searchSetup 2 3 5 4 14148104 7627190764544 = true := by decide +kernel
theorem chunk_shA_49_63_0 : searchChunk' 2 3 1 0 [] 49 5 4 14148104 7627190764544 1 0 33554432 = true := by decide +kernel
theorem chunks_shA_49_63 : ChunkOK 2 3 1 0 [] 49 5 4 14148104 7627190764544 1 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_shA_49_63_0
  exact h
theorem mem_shA_49_63 : memAll ((2, 1) :: (3, 0) :: []) 7627190764545 1024 65536 6 = true := by decide +kernel
theorem leastOn_shA_49_63 : LeastOn ps_shA 49 63 7627190764545 :=
  LeastOn_perm (by decide) (least_of_search (lo := 49) (hi := 63) (u := 7627190764545) (X := 7627190764544) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_49_63 chunks_shA_49_63 (by decide) mem_shA_49_63)

-- plateau m = 64..66, u = 567690557129217; |T2|=47 |T3|=483 pairs+tree=39989 candidates=8918 N=2 chunks=1
theorem setup_shA_64_66 : searchSetup 2 3 5 4 14148104 567690557129216 = true := by decide +kernel
theorem chunk_shA_64_66_0 : searchChunk' 2 3 1 0 [] 64 5 4 14148104 567690557129216 2 0 33554432 = true := by decide +kernel
theorem chunks_shA_64_66 : ChunkOK 2 3 1 0 [] 64 5 4 14148104 567690557129216 2 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_shA_64_66_0
  exact h
theorem mem_shA_64_66 : memAll ((2, 1) :: (3, 0) :: []) 567690557129217 1040186880 68719476736 7 = true := by decide +kernel
theorem leastOn_shA_64_66 : LeastOn ps_shA 64 66 567690557129217 :=
  LeastOn_perm (by decide) (least_of_search (lo := 64) (hi := 66) (u := 567690557129217) (X := 567690557129216) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shA_64_66 chunks_shA_64_66 (by decide) mem_shA_64_66)

end TVGSearch
end LeanCheck
