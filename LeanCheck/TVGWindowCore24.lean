import LeanCheck.TVGWindowCoreIsolated
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Decide
namespace LeanCheck.TVGSearch.WindowCore24
open LeanCheck.TVGSearch LeanCheck.TVGSearch.WindowCore
theorem triple24_no_failed_coordinate {k : Nat}
    (h : ∀ n, 1 ≤ n →
      good 2 1 24 n k = true ∧ good 3 0 24 n k = true ∧ good 5 0 24 n k = true) :
    failsAny [(2, 1, 6), (3, 0, 5), (5, 0, 1)] 24 6 k = false := by
  have noFail {p s start : Nat} (hs : 1 ≤ start)
      (hg : ∀ n, 1 ≤ n → good p s 24 n k = true) :
      failsFrom p s 24 start 6 k = false := by
    unfold failsFrom
    rw [List.any_eq_false]
    intro j _
    rw [hg (start + j) (by omega)]
    decide
  simp [failsAny,
    noFail (p := 2) (s := 1) (start := 6) (by decide) (fun n hn => (h n hn).1),
    noFail (p := 3) (s := 0) (start := 5) (by decide) (fun n hn => (h n hn).2.1),
    noFail (p := 5) (s := 0) (start := 1) (by decide) (fun n hn => (h n hn).2.2)]


set_option maxHeartbeats 0 in
private theorem full_check :
    windowSliceCheck 2 3 1 0 [(5, 0)] 24 4 4 14148104
      1444408272617471 6 0 65536 = true := by decide +native

theorem triple24_no_smaller_integer {k : Nat}
    (hk : 1 ≤ k) (hbound : k < 1444408272617472)
    (h : ∀ n, 1 ≤ n →
      good 2 1 24 n k = true ∧ good 3 0 24 n k = true ∧ good 5 0 24 n k = true) :
    False := by
  have hp : goodUpTo 2 1 24 4 k = true := by
    simp [goodUpTo, (h 1 (by decide)).1, (h 2 (by decide)).1,
      (h 3 (by decide)).1, (h 4 (by decide)).1]
  have hq : goodUpTo 3 0 24 4 k = true := by
    simp [goodUpTo, (h 1 (by decide)).2.1, (h 2 (by decide)).2.1,
      (h 3 (by decide)).2.1, (h 4 (by decide)).2.1]
  have hr := tree_complete (by decide) (by decide) 4 k hp
  have hr' : k % 2 ^ (4 * 4) ∈ (tree 2 1 24 4).filter
      (fun r => decide (0 ≤ r ∧ r < 65536)) :=
    List.mem_filter.2 ⟨hr, by simp [show k % 65536 < 65536 from Nat.mod_lt _ (by decide)]⟩
  have h2 : k % 2 ^ (5 * 5) ∈ liftSlice 2 1 24 4 0 65536 :=
    lift_mem (by decide) (by decide) hr' (h 5 (by decide)).1
  have h3 := tree_complete (by decide) (by decide) 4 k hq
  have check := full_check
  unfold windowSliceCheck windowCheckAux at check
  simp only [Bool.and_eq_true, List.all_eq_true] at check
  obtain ⟨⟨hSR, hC⟩, hall⟩ := check
  have hc := window_complete (p := 2) (q := 3) (sq := 0) (m := 24)
    (n2 := 5) (n3 := 4) (Pinv := 14148104) (X := 1444408272617471)
    (liftSlice 2 1 24 4 0 65536) (by decide) (by decide) (by decide)
    hSR hC hk (Nat.le_of_lt_succ hbound) h2 h3
  have hf : failsAny [(2, 1, 6), (3, 0, 5), (5, 0, 1)] 24 6 k = true := hall k hc
  rw [triple24_no_failed_coordinate h] at hf
  exact Bool.noConfusion hf

#print axioms triple24_no_smaller_integer






set_option maxHeartbeats 0 in
private theorem second_check :
    let TP := liftSlice 2 1 24 4 0 65536
    let SR := sortedRL TP (3 ^ 16) 14148104
    let C := doubled (3 ^ 16) (sortedU 3 0 24 4 (3 ^ 16) 14148104)
    sortedB SR = true ∧ sortedB C = true ∧
    (sweep (2 ^ 25) 223068924672512 C SR).all
      (fun j => failsAny [(2, 1, 6), (3, 0, 5), (5, 0, 1)] 24 6
        (j + 1444408272617472)) = true := by decide +native

theorem triple24_no_smaller {k : Nat}
    (hk : 1 ≤ k) (hbound : k < 1667477197289985)
    (h : ∀ n, 1 ≤ n →
      good 2 1 24 n k = true ∧ good 3 0 24 n k = true ∧ good 5 0 24 n k = true) :
    False := by
  by_cases hb : k < 1444408272617472
  · exact triple24_no_smaller_integer hk hb h
  let j := k - 1444408272617472
  have he : j + 1444408272617472 = k := by omega
  have hjmax : j ≤ 223068924672512 := by omega
  have hj2 : j % 2 = k % 2 := by omega
  have hj : 1 ≤ j := by
    cases Nat.eq_zero_or_pos j with
    | inr hpos => exact hpos
    | inl hz =>
      have hk0 : k % 2 = 0 := by omega
      have hg := (h 1 (by decide)).1
      unfold good idist at hg
      simp only [decide_eq_true_eq] at hg
      simp only [Nat.mul_one, Nat.pow_one] at hg
      split at hg <;> omega
  have hp : goodUpTo 2 1 24 4 k = true := by
    simp [goodUpTo, (h 1 (by decide)).1, (h 2 (by decide)).1,
      (h 3 (by decide)).1, (h 4 (by decide)).1]
  have hq : goodUpTo 3 0 24 4 k = true := by
    simp [goodUpTo, (h 1 (by decide)).2.1, (h 2 (by decide)).2.1,
      (h 3 (by decide)).2.1, (h 4 (by decide)).2.1]
  have hr := tree_complete (by decide) (by decide) 4 k hp
  have hr' : k % 2 ^ (4 * 4) ∈ (tree 2 1 24 4).filter
      (fun r => decide (0 ≤ r ∧ r < 65536)) :=
    List.mem_filter.2 ⟨hr, by simp [show k % 65536 < 65536 from Nat.mod_lt _ (by decide)]⟩
  have h2 : j % 2 ^ (5 * 5) ∈ liftSlice 2 1 24 4 0 65536 := by
    have hmod : j % 33554432 = k % 33554432 := by omega
    rw [show j % 2 ^ (5 * 5) = k % 2 ^ (5 * 5) from hmod]
    exact lift_mem (by decide) (by decide) hr' (h 5 (by decide)).1
  have h3 : j % 3 ^ (4 * 4) ∈ tree 3 0 24 4 := by
    have hmod : j % 43046721 = k % 43046721 := by omega
    rw [show j % 3 ^ (4 * 4) = k % 3 ^ (4 * 4) from hmod]
    exact tree_complete (by decide) (by decide) 4 k hq
  obtain ⟨hSR, hC, hall⟩ := second_check
  have hc := window_complete (p := 2) (q := 3) (sq := 0) (m := 24)
    (n2 := 5) (n3 := 4) (Pinv := 14148104) (X := 223068924672512)
    (liftSlice 2 1 24 4 0 65536) (by decide) (by decide) (by decide)
    hSR hC hj hjmax h2 h3
  have hf := List.all_eq_true.mp hall j hc
  rw [he, triple24_no_failed_coordinate h] at hf
  exact Bool.noConfusion hf

#print axioms triple24_no_smaller
end LeanCheck.TVGSearch.WindowCore24
