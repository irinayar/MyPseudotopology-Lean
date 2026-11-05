import LeanCheck.TVGPlusSearchLeast

/-!
# Bridge from integer coordinates to the pseudonorm

`good_all_iff_pseudonorm`: the integer coordinate conditions `m * idist (k - s) (p^(n^2)) < p^(n^2)` for all `n >= 1` are
equivalent to `P_p(k - s) < 1/m`.  (Formalized by Codex; copied from its worktree.)
-/

namespace LeanCheck.TVGSearch

open MixedPrime

theorem good_all_iff_pseudonorm {p s m k : Nat}
    (hp : 2 ≤ p) (hm : 0 < m) (hs : s ≤ k) :
    (∀ n, 1 ≤ n → good p s m n k = true) ↔
      Pn (sqScales p) ((k : Int) - s) < 1 / (m : Real) := by
  constructor
  · intro hg
    let a := k - s
    have hcast : (a : Int) = (k : Int) - s := Nat.cast_sub hs
    rw [← hcast]
    let radius : Real := 1 / (m : Real)
    have hmR : (0 : Real) < m := by exact_mod_cast hm
    have hrad : 0 < radius := div_pos one_pos hmR
    let coord (n : Nat) : Real :=
      nrm (((a : Int) : Real) / ((p ^ (n ^ 2) : Nat) : Real))
    have pointwise (n : Nat) (hn : 1 ≤ n) : coord n < radius := by
      have hQ : 0 < p ^ (n ^ 2) := Nat.pow_pos (by omega)
      have hQR : (0 : Real) < ((p ^ (n ^ 2) : Nat) : Real) := by exact_mod_cast hQ
      have hi := (good_iff hp hs).mp (hg n hn)
      change nrm (((a : Int) : Real) / ((p ^ (n ^ 2) : Nat) : Real)) < 1 / (m : Real)
      rw [Int.cast_natCast, TVGPlus.nrm_eq_idist a _ hQ, div_lt_div_iff₀ hQR hmR]
      simpa [mul_comm] using (show ((m * TVGPlus.idist a (p ^ (n ^ 2)) : Nat) : Real) <
        ((p ^ (n ^ 2) : Nat) : Real) by exact_mod_cast hi)
    have finite_bound (N : Nat) : ∃ c : Real, c < radius ∧
        ∀ n, 1 ≤ n → n ≤ N → coord n ≤ c := by
      induction N with
      | zero => exact ⟨0, hrad, fun n hn hN => by omega⟩
      | succ N ih =>
        obtain ⟨c, hc, hcoords⟩ := ih
        refine ⟨max c (coord (N + 1)), max_lt hc (pointwise _ (by omega)), ?_⟩
        intro n hn hN
        by_cases h : n ≤ N
        · exact (hcoords n hn h).trans (le_max_left _ _)
        · have he : n = N + 1 := by omega
          rw [he]
          exact le_max_right _ _
    let N := m * a + 1
    have hN : 0 < N := by omega
    have hNR : (0 : Real) < N := by exact_mod_cast hN
    have tail_lt : (a : Real) / N < radius := by
      change (a : Real) / N < 1 / (m : Real)
      rw [div_lt_div_iff₀ hNR hmR, one_mul, mul_comm]
      exact_mod_cast (show m * a < N by exact Nat.lt_succ_self _)
    obtain ⟨c, hc, hcoords⟩ := finite_bound N
    refine lt_of_le_of_lt (Pn_le (TVGPlus.sq_nonempty p) ?_) (max_lt hc tail_lt)
    rintro q ⟨n, hn, rfl⟩
    change coord n ≤ max c ((a : Real) / N)
    by_cases h : n ≤ N
    · exact (hcoords n hn h).trans (le_max_left _ _)
    · have hexp : n ≤ n ^ 2 := by simpa [pow_two] using Nat.mul_le_mul (Nat.le_refl n) hn
      have hsize : N ≤ p ^ (n ^ 2) := by
        have htwo : 2 ^ n ≤ p ^ (n ^ 2) :=
          (Nat.pow_le_pow_left hp n).trans (Nat.pow_le_pow_right (by omega) hexp)
        have hnTwo (j : Nat) : j ≤ 2 ^ j := by
          induction j with
          | zero => decide
          | succ n ih =>
            have hpos : 0 < (2 : Nat) ^ n := Nat.pow_pos (by decide)
            rw [pow_succ]
            omega
        exact (show N ≤ n by omega).trans ((hnTwo n).trans htwo)
      have hb := nrm_big (a : Int) hN hsize
      exact (show coord n ≤ (a : Real) / N by simpa [coord] using hb).trans (le_max_right _ _)
  · intro hin n hn
    have h := goodUpTo_of_inBall hp hm hs hin n
    cases n with
    | zero => omega
    | succ n =>
      simp only [goodUpTo, Bool.and_eq_true] at h
      exact h.2

#print axioms good_all_iff_pseudonorm

end LeanCheck.TVGSearch
