import LeanCheck.TVGPlusSearchLeast
import LeanCheck.TVGSearchPart_shB_52_53_0
import LeanCheck.TVGSearchPart_shB_52_53_1
import LeanCheck.TVGSearchPart_shB_52_53_2
import LeanCheck.TVGSearchPart_shB_52_53_3
import LeanCheck.TVGSearchPart_shB_52_53_4
import LeanCheck.TVGSearchPart_shB_52_53_5
import LeanCheck.TVGSearchPart_shB_52_53_6
import LeanCheck.TVGSearchPart_shB_52_53_7
import LeanCheck.TVGSearchPart_shB_52_53_8
import LeanCheck.TVGSearchPart_shB_52_53_9

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace LeanCheck
namespace TVGSearch

/-- The primes with their shifts. -/
def ps_shB : List (Prod Nat Nat) := [(2, 0), (3, 1)]

-- plateau m = 3..3, u = 4; |T2|=1 |T3|=1 pairs+tree=6 candidates=0 N=1 chunks=1
theorem setup_shB_3_3 : searchSetup 2 3 1 1 2 3 = true := by decide +kernel
theorem chunk_shB_3_3_0 : searchChunk' 2 3 0 1 [] 3 1 1 2 3 1 0 2 = true := by decide +kernel
theorem chunks_shB_3_3 : ChunkOK 2 3 0 1 [] 3 1 1 2 3 1 0 (2 ^ (1 * 1)) := by
  have h := searchChunk'_spec chunk_shB_3_3_0
  exact h
theorem mem_shB_3_3 : memAll ((2, 0) :: (3, 1) :: []) 4 4 16 2 = true := by decide +kernel
theorem leastOn_shB_3_3 : LeastOn ps_shB 3 3 4 :=
  LeastOn_perm (by decide) (least_of_search (lo := 3) (hi := 3) (u := 4) (X := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_3_3 chunks_shB_3_3 (by decide) mem_shB_3_3)

-- plateau m = 4..5, u = 16; |T2|=3 |T3|=1 pairs+tree=16 candidates=0 N=1 chunks=1
theorem setup_shB_4_5 : searchSetup 2 3 2 1 1 15 = true := by decide +kernel
theorem chunk_shB_4_5_0 : searchChunk' 2 3 0 1 [] 4 2 1 1 15 1 0 16 = true := by decide +kernel
theorem chunks_shB_4_5 : ChunkOK 2 3 0 1 [] 4 2 1 1 15 1 0 (2 ^ (2 * 2)) := by
  have h := searchChunk'_spec chunk_shB_4_5_0
  exact h
theorem mem_shB_4_5 : memAll ((2, 0) :: (3, 1) :: []) 16 15 81 2 = true := by decide +kernel
theorem leastOn_shB_4_5 : LeastOn ps_shB 4 5 16 :=
  LeastOn_perm (by decide) (least_of_search (lo := 4) (hi := 5) (u := 16) (X := 15) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_4_5 chunks_shB_4_5 (by decide) mem_shB_4_5)

-- plateau m = 6..6, u = 82; |T2|=1 |T3|=9 pairs+tree=41 candidates=4 N=1 chunks=1
theorem setup_shB_6_6 : searchSetup 2 3 1 2 41 81 = true := by decide +kernel
theorem chunk_shB_6_6_0 : searchChunk' 2 3 0 1 [] 6 1 2 41 81 1 0 2 = true := by decide +kernel
theorem chunks_shB_6_6 : ChunkOK 2 3 0 1 [] 6 1 2 41 81 1 0 (2 ^ (1 * 1)) := by
  have h := searchChunk'_spec chunk_shB_6_6_0
  exact h
theorem mem_shB_6_6 : memAll ((2, 0) :: (3, 1) :: []) 82 82 512 3 = true := by decide +kernel
theorem leastOn_shB_6_6 : LeastOn ps_shB 6 6 82 :=
  LeastOn_perm (by decide) (least_of_search (lo := 6) (hi := 6) (u := 82) (X := 81) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_6_6 chunks_shB_6_6 (by decide) mem_shB_6_6)

-- plateau m = 7..7, u = 478; |T2|=3 |T3|=7 pairs+tree=61 candidates=6 N=1 chunks=1
theorem setup_shB_7_7 : searchSetup 2 3 2 2 76 477 = true := by decide +kernel
theorem chunk_shB_7_7_0 : searchChunk' 2 3 0 1 [] 7 2 2 76 477 1 0 16 = true := by decide +kernel
theorem chunks_shB_7_7 : ChunkOK 2 3 0 1 [] 7 2 2 76 477 1 0 (2 ^ (2 * 2)) := by
  have h := searchChunk'_spec chunk_shB_7_7_0
  exact h
theorem mem_shB_7_7 : memAll ((2, 0) :: (3, 1) :: []) 478 2 16 3 = true := by decide +kernel
theorem leastOn_shB_7_7 : LeastOn ps_shB 7 7 478 :=
  LeastOn_perm (by decide) (least_of_search (lo := 7) (hi := 7) (u := 478) (X := 477) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_7_7 chunks_shB_7_7 (by decide) mem_shB_7_7)

-- plateau m = 8..8, u = 496; |T2|=1 |T3|=7 pairs+tree=47 candidates=2 N=1 chunks=1
theorem setup_shB_8_8 : searchSetup 2 3 2 2 76 495 = true := by decide +kernel
theorem chunk_shB_8_8_0 : searchChunk' 2 3 0 1 [] 8 2 2 76 495 1 0 16 = true := by decide +kernel
theorem chunks_shB_8_8 : ChunkOK 2 3 0 1 [] 8 2 2 76 495 1 0 (2 ^ (2 * 2)) := by
  have h := searchChunk'_spec chunk_shB_8_8_0
  exact h
theorem mem_shB_8_8 : memAll ((2, 0) :: (3, 1) :: []) 496 9 81 3 = true := by decide +kernel
theorem leastOn_shB_8_8 : LeastOn ps_shB 8 8 496 :=
  LeastOn_perm (by decide) (least_of_search (lo := 8) (hi := 8) (u := 496) (X := 495) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_8_8 chunks_shB_8_8 (by decide) mem_shB_8_8)

-- plateau m = 9..10, u = 976; |T2|=1 |T3|=5 pairs+tree=45 candidates=3 N=1 chunks=1
theorem setup_shB_9_10 : searchSetup 2 3 2 2 76 975 = true := by decide +kernel
theorem chunk_shB_9_10_0 : searchChunk' 2 3 0 1 [] 9 2 2 76 975 1 0 16 = true := by decide +kernel
theorem chunks_shB_9_10 : ChunkOK 2 3 0 1 [] 9 2 2 76 975 1 0 (2 ^ (2 * 2)) := by
  have h := searchChunk'_spec chunk_shB_9_10_0
  exact h
theorem mem_shB_9_10 : memAll ((2, 0) :: (3, 1) :: []) 976 48 512 3 = true := by decide +kernel
theorem leastOn_shB_9_10 : LeastOn ps_shB 9 10 976 :=
  LeastOn_perm (by decide) (least_of_search (lo := 9) (hi := 10) (u := 976) (X := 975) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_9_10 chunks_shB_9_10 (by decide) mem_shB_9_10)

-- plateau m = 11..15, u = 195616; |T2|=115 |T3|=1 pairs+tree=800 candidates=112 N=2 chunks=1
theorem setup_shB_11_15 : searchSetup 2 3 4 1 1 195615 = true := by decide +kernel
theorem chunk_shB_11_15_0 : searchChunk' 2 3 0 1 [] 11 4 1 1 195615 2 0 65536 = true := by decide +kernel
theorem chunks_shB_11_15 : ChunkOK 2 3 0 1 [] 11 4 1 1 195615 2 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shB_11_15_0
  exact h
theorem mem_shB_11_15 : memAll ((2, 0) :: (3, 1) :: []) 195616 32 512 4 = true := by decide +kernel
theorem leastOn_shB_11_15 : LeastOn ps_shB 11 15 195616 :=
  LeastOn_perm (by decide) (least_of_search (lo := 11) (hi := 15) (u := 195616) (X := 195615) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_11_15 chunks_shB_11_15 (by decide) mem_shB_11_15)

-- plateau m = 16..26, u = 589840; |T2|=47 |T3|=3 pairs+tree=597 candidates=22 N=1 chunks=1
theorem setup_shB_16_26 : searchSetup 2 3 4 2 58 589839 = true := by decide +kernel
theorem chunk_shB_16_26_0 : searchChunk' 2 3 0 1 [] 16 4 2 58 589839 1 0 65536 = true := by decide +kernel
theorem chunks_shB_16_26 : ChunkOK 2 3 0 1 [] 16 4 2 58 589839 1 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shB_16_26_0
  exact h
theorem mem_shB_16_26 : memAll ((2, 0) :: (3, 1) :: []) 589840 3 81 4 = true := by decide +kernel
theorem leastOn_shB_16_26 : LeastOn ps_shB 16 26 589840 :=
  LeastOn_perm (by decide) (least_of_search (lo := 16) (hi := 26) (u := 589840) (X := 589839) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_16_26 chunks_shB_16_26 (by decide) mem_shB_16_26)

-- plateau m = 27..31, u = 301465072; |T2|=27 |T3|=17 pairs+tree=1158 candidates=108 N=1 chunks=1
theorem setup_shB_27_31 : searchSetup 2 3 4 3 12856 301465071 = true := by decide +kernel
theorem chunk_shB_27_31_0 : searchChunk' 2 3 0 1 [] 27 4 3 12856 301465071 1 0 65536 = true := by decide +kernel
theorem chunks_shB_27_31 : ChunkOK 2 3 0 1 [] 27 4 3 12856 301465071 1 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shB_27_31_0
  exact h
theorem mem_shB_27_31 : memAll ((2, 0) :: (3, 1) :: []) 301465072 16 512 5 = true := by decide +kernel
theorem leastOn_shB_27_31 : LeastOn ps_shB 27 31 301465072 :=
  LeastOn_perm (by decide) (least_of_search (lo := 27) (hi := 31) (u := 301465072) (X := 301465071) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_27_31 chunks_shB_27_31 (by decide) mem_shB_27_31)

-- plateau m = 32..36, u = 1376648704; |T2|=223 |T3|=1 pairs+tree=4007 candidates=111 N=2 chunks=1
theorem setup_shB_32_36 : searchSetup 2 3 5 2 77 1376648703 = true := by decide +kernel
theorem chunk_shB_32_36_0 : searchChunk' 2 3 0 1 [] 32 5 2 77 1376648703 2 0 33554432 = true := by decide +kernel
theorem chunks_shB_32_36 : ChunkOK 2 3 0 1 [] 32 5 2 77 1376648703 2 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_shB_32_36_0
  exact h
theorem mem_shB_32_36 : memAll ((2, 0) :: (3, 1) :: []) 1376648704 916992 33554432 5 = true := by decide +kernel
theorem leastOn_shB_32_36 : LeastOn ps_shB 32 36 1376648704 :=
  LeastOn_perm (by decide) (least_of_search (lo := 32) (hi := 36) (u := 1376648704) (X := 1376648703) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_32_36 chunks_shB_32_36 (by decide) mem_shB_32_36)

-- plateau m = 37..38, u = 825506200576; |T2|=7 |T3|=1547 pairs+tree=39703 candidates=3164 N=2 chunks=1
theorem setup_shB_37_38 : searchSetup 2 3 4 4 11980120 825506200575 = true := by decide +kernel
theorem chunk_shB_37_38_0 : searchChunk' 2 3 0 1 [] 37 4 4 11980120 825506200575 2 0 65536 = true := by decide +kernel
theorem chunks_shB_37_38 : ChunkOK 2 3 0 1 [] 37 4 4 11980120 825506200575 2 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shB_37_38_0
  exact h
theorem mem_shB_37_38 : memAll ((2, 0) :: (3, 1) :: []) 825506200576 21782408868 847288609443 6 = true := by decide +kernel
theorem leastOn_shB_37_38 : LeastOn ps_shB 37 38 825506200576 :=
  LeastOn_perm (by decide) (least_of_search (lo := 37) (hi := 38) (u := 825506200576) (X := 825506200575) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_37_38 chunks_shB_37_38 (by decide) mem_shB_37_38)

-- plateau m = 39..40, u = 826109327872; |T2|=7 |T3|=1469 pairs+tree=39157 candidates=3009 N=2 chunks=1
theorem setup_shB_39_40 : searchSetup 2 3 4 4 11980120 826109327871 = true := by decide +kernel
theorem chunk_shB_39_40_0 : searchChunk' 2 3 0 1 [] 39 4 4 11980120 826109327871 2 0 65536 = true := by decide +kernel
theorem chunks_shB_39_40 : ChunkOK 2 3 0 1 [] 39 4 4 11980120 826109327871 2 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_shB_39_40_0
  exact h
theorem mem_shB_39_40 : memAll ((2, 0) :: (3, 1) :: []) 826109327872 21179281572 847288609443 6 = true := by decide +kernel
theorem leastOn_shB_39_40 : LeastOn ps_shB 39 40 826109327872 :=
  LeastOn_perm (by decide) (least_of_search (lo := 39) (hi := 40) (u := 826109327872) (X := 826109327871) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_39_40 chunks_shB_39_40 (by decide) mem_shB_39_40)

-- plateau m = 41..42, u = 7628265358336; |T2|=175 |T3|=1177 pairs+tree=234059 candidates=1080 N=1 chunks=1
theorem setup_shB_41_42 : searchSetup 2 3 5 4 14148104 7628265358335 = true := by decide +kernel
theorem chunk_shB_41_42_0 : searchChunk' 2 3 0 1 [] 41 5 4 14148104 7628265358335 1 0 33554432 = true := by decide +kernel
theorem chunks_shB_41_42 : ChunkOK 2 3 0 1 [] 41 5 4 14148104 7628265358335 1 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_shB_41_42_0
  exact h
theorem mem_shB_41_42 : memAll ((2, 0) :: (3, 1) :: []) 7628265358336 1023354 43046721 6 = true := by decide +kernel
theorem leastOn_shB_41_42 : LeastOn ps_shB 41 42 7628265358336 :=
  LeastOn_perm (by decide) (least_of_search (lo := 41) (hi := 42) (u := 7628265358336) (X := 7628265358335) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_41_42 chunks_shB_41_42 (by decide) mem_shB_41_42)

-- plateau m = 43..51, u = 563432331870208; |T2|=115 |T3|=1111 pairs+tree=154825 candidates=49833 N=2 chunks=1
theorem setup_shB_43_51 : searchSetup 2 3 5 4 14148104 563432331870207 = true := by decide +kernel
theorem chunk_shB_43_51_0 : searchChunk' 2 3 0 1 [] 43 5 4 14148104 563432331870207 2 0 33554432 = true := by decide +kernel
theorem chunks_shB_43_51 : ChunkOK 2 3 0 1 [] 43 5 4 14148104 563432331870207 2 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_shB_43_51_0
  exact h
theorem mem_shB_43_51 : memAll ((2, 0) :: (3, 1) :: []) 563432331870208 1342111744 68719476736 7 = true := by decide +kernel
theorem leastOn_shB_43_51 : LeastOn ps_shB 43 51 563432331870208 :=
  LeastOn_perm (by decide) (least_of_search (lo := 43) (hi := 51) (u := 563432331870208) (X := 563432331870207) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_43_51 chunks_shB_43_51 (by decide) mem_shB_43_51)

-- plateau m = 52..53, u = 2818941084826624; |T2|=7505 |T3|=765 pairs+tree=5958571 candidates=5461 N=1 chunks=10
theorem setup_shB_52_53 : searchSetup 2 3 6 4 42885478 2818941084826623 = true := by decide +kernel
theorem chunks_shB_52_53 : ChunkOK 2 3 0 1 [] 52 6 4 42885478 2818941084826623 1 0 (2 ^ (6 * 6)) := by
  have h := ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (ChunkOK_trans (searchChunk'_spec chunk_shB_52_53_0) (searchChunk'_spec chunk_shB_52_53_1)) (searchChunk'_spec chunk_shB_52_53_2)) (searchChunk'_spec chunk_shB_52_53_3)) (searchChunk'_spec chunk_shB_52_53_4)) (searchChunk'_spec chunk_shB_52_53_5)) (searchChunk'_spec chunk_shB_52_53_6)) (searchChunk'_spec chunk_shB_52_53_7)) (searchChunk'_spec chunk_shB_52_53_8)) (searchChunk'_spec chunk_shB_52_53_9)
  exact h
theorem mem_shB_52_53 : memAll ((2, 0) :: (3, 1) :: []) 2818941084826624 2818941084826623 150094635296999121 7 = true := by decide +kernel
theorem leastOn_shB_52_53 : LeastOn ps_shB 52 53 2818941084826624 :=
  LeastOn_perm (by decide) (least_of_search (lo := 52) (hi := 53) (u := 2818941084826624) (X := 2818941084826623) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_shB_52_53 chunks_shB_52_53 (by decide) mem_shB_52_53)

end TVGSearch
end LeanCheck
