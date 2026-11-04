import Mathlib

/-!
# TVGplus: the close chain of levels `5^(19²) < 3^(23²) < 2^(29²)`

The three levels `Q₃ = 5^(19²) < Q₂ = 3^(23²) < Q₁ = 2^(29²)` (their logarithms are about `581.0`, `581.15`, `582.9`)
form a chain in which consecutive levels are within a factor `√(log Q)` of each other:
`Q₂² < log Q₃ · Q₃²` and `Q₁² < log Q₂ · Q₂²`.  The integer comparisons are checked by the kernel; the lower bounds
`log 5 > 1` and `log 3 > 1` come from `exp 1 < 3` (Mathlib).
-/

namespace LeanCheck
namespace TVGSearch

lemma chain_int1 : 5 ^ (19 ^ 2) < 3 ^ (23 ^ 2) := by decide +kernel
lemma chain_int2 : 3 ^ (23 ^ 2) < 2 ^ (29 ^ 2) := by decide +kernel
lemma chain_int3 : (3 ^ (23 ^ 2)) ^ 2 < 361 * (5 ^ (19 ^ 2)) ^ 2 := by decide +kernel
lemma chain_int4 : (2 ^ (29 ^ 2)) ^ 2 < 529 * (3 ^ (23 ^ 2)) ^ 2 := by decide +kernel

lemma step_lt {Qa Qb k : ℝ} (hQa : 0 < Qa) (hk : k < Real.log Qa) (h : Qb ^ 2 < k * Qa ^ 2) :
    Qb ^ 2 < Real.log Qa * Qa ^ 2 :=
  lt_trans h (mul_lt_mul_of_pos_right hk (by positivity))

lemma log_three_gt_one : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith [this]

lemma log_five_gt_one : (1 : ℝ) < Real.log 5 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith [this]

theorem chain_19_23_29 :
    (5 : ℝ) ^ (19 ^ 2) < 3 ^ (23 ^ 2) ∧ (3 : ℝ) ^ (23 ^ 2) < 2 ^ (29 ^ 2) ∧
    ((3 : ℝ) ^ (23 ^ 2)) ^ 2 < Real.log ((5 : ℝ) ^ (19 ^ 2)) * ((5 : ℝ) ^ (19 ^ 2)) ^ 2 ∧
    ((2 : ℝ) ^ (29 ^ 2)) ^ 2 < Real.log ((3 : ℝ) ^ (23 ^ 2)) * ((3 : ℝ) ^ (23 ^ 2)) ^ 2 := by
  have h1 : (5 : ℝ) ^ (19 ^ 2) < 3 ^ (23 ^ 2) := by exact_mod_cast chain_int1
  have h2 : (3 : ℝ) ^ (23 ^ 2) < 2 ^ (29 ^ 2) := by exact_mod_cast chain_int2
  have h3 : ((3 : ℝ) ^ (23 ^ 2)) ^ 2 < 361 * ((5 : ℝ) ^ (19 ^ 2)) ^ 2 := by exact_mod_cast chain_int3
  have h4 : ((2 : ℝ) ^ (29 ^ 2)) ^ 2 < 529 * ((3 : ℝ) ^ (23 ^ 2)) ^ 2 := by exact_mod_cast chain_int4
  have l5 : (361 : ℝ) < Real.log ((5 : ℝ) ^ (19 ^ 2)) := by
    rw [Real.log_pow]
    have := log_five_gt_one
    have e : (((19 ^ 2 : ℕ)) : ℝ) = 361 := by norm_num
    rw [e]; linarith
  have l3 : (529 : ℝ) < Real.log ((3 : ℝ) ^ (23 ^ 2)) := by
    rw [Real.log_pow]
    have := log_three_gt_one
    have e : (((23 ^ 2 : ℕ)) : ℝ) = 529 := by norm_num
    rw [e]; linarith
  exact ⟨h1, h2, step_lt (by positivity) l5 h3, step_lt (by positivity) l3 h4⟩

#print axioms chain_19_23_29

end TVGSearch
end LeanCheck
