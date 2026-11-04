import LeanCheck.TVGPlusSearchLeast

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace LeanCheck
namespace TVGSearch

/-- The primes with their shifts. -/
def ps_null23 : List (Prod Nat Nat) := [(2, 0), (3, 0)]

-- plateau m = 35..36, u = 824129551872; |T2|=7 |T3|=1625 pairs+tree=40249 candidates=3321 N=2 chunks=1
theorem setup_null23_35_36 : searchSetup 2 3 4 4 11980120 824129551871 = true := by decide +kernel
theorem chunk_null23_35_36_0 : searchChunk' 2 3 0 0 [] 35 4 4 11980120 824129551871 2 0 65536 = true := by decide +kernel
theorem chunks_null23_35_36 : ChunkOK 2 3 0 0 [] 35 4 4 11980120 824129551871 2 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_null23_35_36_0
  exact h
theorem mem_null23_35_36 : memAll ((2, 0) :: (3, 0) :: []) 824129551872 23159057571 847288609443 6 = true := by decide +kernel
theorem leastOn_null23_35_36 : LeastOn ps_null23 35 36 824129551872 :=
  LeastOn_perm (by decide) (least_of_search (lo := 35) (hi := 36) (u := 824129551872) (X := 824129551871) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_null23_35_36 chunks_null23_35_36 (by decide) mem_null23_35_36)

-- plateau m = 37..42, u = 2543459304960; |T2|=7 |T3|=1547 pairs+tree=39703 candidates=9759 N=2 chunks=1
theorem setup_null23_37_42 : searchSetup 2 3 4 4 11980120 2543459304959 = true := by decide +kernel
theorem chunk_null23_37_42_0 : searchChunk' 2 3 0 0 [] 37 4 4 11980120 2543459304959 2 0 65536 = true := by decide +kernel
theorem chunks_null23_37_42 : ChunkOK 2 3 0 0 [] 37 4 4 11980120 2543459304959 2 0 (2 ^ (4 * 4)) := by
  have h := searchChunk'_spec chunk_null23_37_42_0
  exact h
theorem mem_null23_37_42 : memAll ((2, 0) :: (3, 0) :: []) 2543459304960 1536 65536 6 = true := by decide +kernel
theorem leastOn_null23_37_42 : LeastOn ps_null23 37 42 2543459304960 :=
  LeastOn_perm (by decide) (least_of_search (lo := 37) (hi := 42) (u := 2543459304960) (X := 2543459304959) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_null23_37_42 chunks_null23_37_42 (by decide) mem_null23_37_42)

-- plateau m = 43..44, u = 553260607994880; |T2|=115 |T3|=1111 pairs+tree=154825 candidates=48942 N=2 chunks=1
theorem setup_null23_43_44 : searchSetup 2 3 5 4 14148104 553260607994879 = true := by decide +kernel
theorem chunk_null23_43_44_0 : searchChunk' 2 3 0 0 [] 43 5 4 14148104 553260607994879 2 0 33554432 = true := by decide +kernel
theorem chunks_null23_43_44 : ChunkOK 2 3 0 0 [] 43 5 4 14148104 553260607994879 2 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_null23_43_44_0
  exact h
theorem mem_null23_43_44 : memAll ((2, 0) :: (3, 0) :: []) 553260607994880 18853971399 847288609443 7 = true := by decide +kernel
theorem leastOn_null23_43_44 : LeastOn ps_null23 43 44 553260607994880 :=
  LeastOn_perm (by decide) (least_of_search (lo := 43) (hi := 44) (u := 553260607994880) (X := 553260607994879) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_null23_43_44 chunks_null23_43_44 (by decide) mem_null23_43_44)

-- plateau m = 45..60, u = 554977655129088; |T2|=115 |T3|=1067 pairs+tree=149765 candidates=47136 N=2 chunks=1
theorem setup_null23_45_60 : searchSetup 2 3 5 4 14148104 554977655129087 = true := by decide +kernel
theorem chunk_null23_45_60_0 : searchChunk' 2 3 0 0 [] 45 5 4 14148104 554977655129087 2 0 33554432 = true := by decide +kernel
theorem chunks_null23_45_60 : ChunkOK 2 3 0 0 [] 45 5 4 14148104 554977655129087 2 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_null23_45_60_0
  exact h
theorem mem_null23_45_60 : memAll ((2, 0) :: (3, 0) :: []) 554977655129088 324 19683 7 = true := by decide +kernel
theorem leastOn_null23_45_60 : LeastOn ps_null23 45 60 554977655129088 :=
  LeastOn_perm (by decide) (least_of_search (lo := 45) (hi := 60) (u := 554977655129088) (X := 554977655129087) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_null23_45_60 chunks_null23_45_60 (by decide) mem_null23_45_60)

-- plateau m = 61..78, u = 560063366364672; |T2|=85 |T3|=497 pairs+tree=60557 candidates=16378 N=2 chunks=1
theorem setup_null23_61_78 : searchSetup 2 3 5 4 14148104 560063366364671 = true := by decide +kernel
theorem chunk_null23_61_78_0 : searchChunk' 2 3 0 0 [] 61 5 4 14148104 560063366364671 2 0 33554432 = true := by decide +kernel
theorem chunks_null23_61_78 : ChunkOK 2 3 0 0 [] 61 5 4 14148104 560063366364671 2 0 (2 ^ (5 * 5)) := by
  have h := searchChunk'_spec chunk_null23_61_78_0
  exact h
theorem mem_null23_61_78 : memAll ((2, 0) :: (3, 0) :: []) 560063366364672 550881 43046721 7 = true := by decide +kernel
theorem leastOn_null23_61_78 : LeastOn ps_null23 61 78 560063366364672 :=
  LeastOn_perm (by decide) (least_of_search (lo := 61) (hi := 78) (u := 560063366364672) (X := 560063366364671) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) setup_null23_61_78 chunks_null23_61_78 (by decide) mem_null23_61_78)

-- plateau m = 79..100, u = 0; |T2|=1989 |T3|=385 pairs+tree=862925 candidates=10349 N=2 chunks=2
theorem setup_null23_79_100 : searchSetup 2 3 6 4 42885478 40000000000000000 = true := by decide +kernel
theorem chunk_null23_79_100_0 : searchChunk' 2 3 0 0 [] 79 6 4 42885478 40000000000000000 2 0 68350312960 = true := by decide +kernel
theorem chunk_null23_79_100_1 : searchChunk' 2 3 0 0 [] 79 6 4 42885478 40000000000000000 2 68350312960 68719476736 = true := by decide +kernel
theorem chunks_null23_79_100 : ChunkOK 2 3 0 0 [] 79 6 4 42885478 40000000000000000 2 0 (2 ^ (6 * 6)) := by
  have h := ChunkOK_trans (searchChunk'_spec chunk_null23_79_100_0) (searchChunk'_spec chunk_null23_79_100_1)
  exact h
theorem noneOn_null23_79_100 : NoneOn ps_null23 79 100 40000000000000000 :=
  NoneOn_perm (by decide) (none_of_search (lo := 79) (hi := 100) (X := 40000000000000000) (by decide) (by decide) (by decide) (by decide) (by decide) setup_null23_79_100 chunks_null23_79_100)

end TVGSearch
end LeanCheck
