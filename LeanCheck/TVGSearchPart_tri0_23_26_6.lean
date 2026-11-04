import LeanCheck.TVGPlusSearchLeast

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace LeanCheck
namespace TVGSearch

theorem chunk_tri0_23_26_6 : searchChunk' 2 5 0 0 [(3, 0)] 23 5 3 1775318 15258341867519 4 33027584 33421312 = true := by decide +kernel

end TVGSearch
end LeanCheck
