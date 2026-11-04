import LeanCheck.TVGWindowLit

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-!
# Sorted window search: validation instances

Two exhaustive searches done with the sorted CRT window search (`TVGPlusWindow`, soundness theorem `window_none`),
which reproduce results obtained earlier by the pair scan:

* the shifted pair `P_2(k - 1), P_3(k) < 1/12`: no `k <= 136160` (the least element is `136161`);
* the shifted triple `P_2(k - 1), P_3(k), P_5(k) < 1/20`: no `k <= 3187406864` (the least element is `3187406865`).
-/

namespace LeanCheck
namespace TVGSearch

theorem window_pair_12_none : ∀ k : ℕ, 1 ≤ k → k ≤ 136160 → ¬ ShiftedIn [(2, 1), (3, 0)] 12 k :=
  window_none (p := 2) (q := 3) (sp := 1) (sq := 0) (rest := []) (m := 12) (n2 := 4) (n3 := 3)
    (Pinv := 12856) (X := 136160) (N := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)

theorem window_triple_20_none :
    ∀ k : ℕ, 1 ≤ k → k ≤ 3187406864 → ¬ ShiftedIn [(2, 1), (3, 0), (5, 0)] 20 k :=
  window_none (p := 2) (q := 3) (sp := 1) (sq := 0) (rest := [(5, 0)]) (m := 20) (n2 := 5) (n3 := 3)
    (Pinv := 15710) (X := 3187406864) (N := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel)

#print axioms window_pair_12_none
#print axioms window_triple_20_none

end TVGSearch
end LeanCheck
