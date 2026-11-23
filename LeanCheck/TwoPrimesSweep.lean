import Mathlib

/-!
# TwoPrimes: the circle step of the level-structure proposition (TwoPrimes_v9)

In the choice of the levels, the scaled phases `φ j = r(N_* + j) / L` move by `a` (no wrap) or by `a - b` (wrap)
at each step, with `2 < a < b`.  A level is *bad* if its phase lies in the zone `(a - 2, 2)` (open).
`sweep_bound`: if `K` consecutive phases are all bad then `(K - 1) (b - a) < 4 - a`.
Hence among `K` consecutive levels with `(K - 1)(b - a) ≥ 4 - a` one is good.
-/

namespace LeanCheck
namespace TwoPrimes

/-- All phases bad and each step is `+a` or `+a-b`: then every step is a wrap, so the phases decrease by `b - a`
per step. -/
lemma sweep_decrease (a b : ℝ) (ha : 2 < a) (φ : ℕ → ℝ) (K : ℕ)
    (hbad : ∀ j, j < K → a - 2 < φ j ∧ φ j < 2)
    (hstep : ∀ j, j + 1 < K → φ (j + 1) = φ j + a ∨ φ (j + 1) = φ j + a - b) :
    ∀ j, j < K → φ j = φ 0 - (j : ℝ) * (b - a) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hj' : j < K := Nat.lt_of_succ_lt hj
    have hprev := ih hj'
    have h1 := hbad j hj'
    have h2 := hbad (j + 1) hj
    rcases hstep j hj with h | h
    · -- no wrap: φ (j+1) = φ j + a > (a - 2) + a > 2, contradiction
      exfalso
      linarith [h1.1, h2.2]
    · rw [h, hprev]; push_cast; ring

lemma sweep_bound (a b : ℝ) (ha : 2 < a) (φ : ℕ → ℝ) (K : ℕ) (hK : 1 ≤ K)
    (hbad : ∀ j, j < K → a - 2 < φ j ∧ φ j < 2)
    (hstep : ∀ j, j + 1 < K → φ (j + 1) = φ j + a ∨ φ (j + 1) = φ j + a - b) :
    ((K : ℝ) - 1) * (b - a) < 4 - a := by
  have hdec := sweep_decrease a b ha φ K hbad hstep
  have hlast := hdec (K - 1) (by omega)
  have h0 := hbad 0 (by omega)
  have hl := hbad (K - 1) (by omega)
  have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub hK]; simp
  rw [hcast] at hlast
  linarith [h0.2, hl.1]

end TwoPrimes
end LeanCheck
