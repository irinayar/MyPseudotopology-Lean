import Mathlib

/-!
# TwoPrimes: two elementary steps of the level-structure proposition (TwoPrimes_v8)

* `two_floor_add_one_ge`: for a real `ρ ≥ 1`, `ρ ≤ 2 ⌊ρ⌋ + 1`.  (Used for `2 J_n + 1 ≥ ρ_n = ℓ^(2n-1)/D` when `ρ_n ≥ 1`.)
* `sum_odd_Ico`: `∑_{n = n₀}^{N-1} (2 n - 1) = (N-1)^2 - (n₀-1)^2` for `n₀ ≤ N` (the exponent bookkeeping
  `∑ (2n-1) = N^2 - (n₀-1)^2` that makes the step `u = ℓ^((N-1)^2)` cancel in the lower bound for `|A|`).
-/

namespace LeanCheck
namespace TwoPrimes

lemma two_floor_add_one_ge (ρ : ℝ) (h : 1 ≤ ρ) : ρ ≤ 2 * (⌊ρ⌋ : ℝ) + 1 := by
  have h1 : ρ < (⌊ρ⌋ : ℝ) + 1 := Int.lt_floor_add_one ρ
  have h2 : (1 : ℝ) ≤ (⌊ρ⌋ : ℝ) := by
    have : (1 : ℤ) ≤ ⌊ρ⌋ := Int.le_floor.mpr (by simpa using h)
    exact_mod_cast this
  linarith

lemma sum_odd_Ico (n₀ N : ℕ) (h2 : n₀ ≤ N) :
    ((∑ n ∈ Finset.Ico n₀ N, (2 * (n : ℤ) - 1)) : ℤ) = ((N : ℤ) - 1) ^ 2 - ((n₀ : ℤ) - 1) ^ 2 := by
  induction N, h2 using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, ih]
    push_cast
    ring

end TwoPrimes
end LeanCheck
