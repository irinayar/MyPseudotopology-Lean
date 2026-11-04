import LeanCheck.TVGPlusSearchLeast

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace LeanCheck
namespace TVGSearch

theorem chunk_shB_52_53_2 : searchChunk' 2 3 0 1 [] 52 6 4 42885478 2818941084826623 1 569834496 838534144 = true := by decide +kernel

end TVGSearch
end LeanCheck
