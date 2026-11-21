import LeanCheck.MixedPrimeRadii

/-!
# TwoPrimes: no `ℓ`-adic neighbourhood lies in a ball of the square-chain metric

For `ℓ ≥ 2` let `Pn (sqScales ℓ)` be the pseudonorm `P_ℓ(k) = sup_n ‖k / ℓ^(n²)‖` of the article.
Every ball `{P_ℓ < δ}` lies in `ℓ^(a²) ℤ` (the valuation lemma `MixedPrime.valuation_bound`), so the topology of
`(ℤ, P_ℓ)` is finer than the `ℓ`-adic topology.  This module proves the strictness (Proposition D1(c) of the
note "the joint completion and its characters"):

* `half_ratio_bounds`: for `Q ≥ 2`, `1/3 ≤ ⌊Q/2⌋ / Q ≤ 1/2`.
* `exists_far_multiple`: for every `b` the integer `k = ℓ^b ⌊ℓ^(n²-b)/2⌋`, `n = b + 1`, is a multiple of `ℓ^b`
  with `Pn (sqScales ℓ) k ≥ 1/3`.
* `no_adic_nbhd_in_ball`: for `δ ≤ 1/3` no neighbourhood `ℓ^b ℤ` of `0` is contained in the ball of radius `δ`.
-/

namespace LeanCheck
namespace TwoPrimes

open LeanCheck.MixedPrime

/-- For `Q ≥ 2`: `1/3 ≤ ⌊Q/2⌋ / Q ≤ 1/2`. -/
lemma half_ratio_bounds {Q : ℕ} (hQ : 2 ≤ Q) :
    (1 : ℝ) / 3 ≤ ((Q / 2 : ℕ) : ℝ) / Q ∧ ((Q / 2 : ℕ) : ℝ) / Q ≤ 1 / 2 := by
  have h1 : 2 * (Q / 2) ≤ Q := by omega
  have h2 : Q ≤ 2 * (Q / 2) + 1 := by omega
  have h3 : 1 ≤ Q / 2 := by omega
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have h1' : 2 * ((Q / 2 : ℕ) : ℝ) ≤ Q := by exact_mod_cast h1
  have h2' : (Q : ℝ) ≤ 2 * ((Q / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
  have h3' : (1 : ℝ) ≤ ((Q / 2 : ℕ) : ℝ) := by exact_mod_cast h3
  constructor
  · rw [le_div_iff₀ hQ0]; linarith
  · rw [div_le_iff₀ hQ0]; linarith

/-- For `ℓ ≥ 2` and `b < n²`, the multiple `k = ℓ^b ⌊ℓ^(n²-b)/2⌋` of `ℓ^b` satisfies
`‖k / ℓ^(n²)‖ ≥ 1/3`. -/
lemma nrm_far_multiple {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (b n : ℕ) (hb : b < n ^ 2) :
    (1 : ℝ) / 3 ≤ nrm ((((ℓ ^ b * (ℓ ^ (n ^ 2 - b) / 2) : ℕ) : ℤ) : ℝ) / ((ℓ ^ (n ^ 2) : ℕ) : ℝ)) := by
  obtain ⟨m, hm⟩ : ∃ m, m = n ^ 2 - b := ⟨_, rfl⟩
  rw [← hm]
  have hm1 : 1 ≤ m := by omega
  have hQ : 2 ≤ ℓ ^ m :=
    calc 2 ≤ ℓ := hℓ
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ m := Nat.pow_le_pow_right (by omega) hm1
  have hexp : ℓ ^ (n ^ 2) = ℓ ^ b * ℓ ^ m := by
    rw [← pow_add]; congr 1; omega
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hb0 : (ℓ : ℝ) ^ b ≠ 0 := by positivity
  have hm0 : (ℓ : ℝ) ^ m ≠ 0 := by positivity
  obtain ⟨hlo, hhi⟩ := half_ratio_bounds hQ
  have hQc : ((ℓ ^ m : ℕ) : ℝ) = (ℓ : ℝ) ^ m := by push_cast; ring
  rw [hQc] at hlo hhi
  have e : (((ℓ ^ b * (ℓ ^ m / 2) : ℕ) : ℤ) : ℝ) / ((ℓ ^ (n ^ 2) : ℕ) : ℝ)
      = ((ℓ ^ m / 2 : ℕ) : ℝ) / ((ℓ : ℝ) ^ m) := by
    rw [hexp, Int.cast_natCast]
    simp only [Nat.cast_mul, Nat.cast_pow]
    field_simp
  rw [e]
  have hnn : (0 : ℝ) ≤ ((ℓ ^ m / 2 : ℕ) : ℝ) / ((ℓ : ℝ) ^ m) := by positivity
  have habs : |((ℓ ^ m / 2 : ℕ) : ℝ) / ((ℓ : ℝ) ^ m)| ≤ 1 / 2 := by
    rw [abs_of_nonneg hnn]; exact hhi
  rw [nrm_eq_abs habs, abs_of_nonneg hnn]
  exact hlo

/-- For every `b` there is a multiple of `ℓ^b` far from `0` for `P_ℓ`: `Pn (sqScales ℓ) k ≥ 1/3`. -/
theorem exists_far_multiple {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (b : ℕ) :
    ∃ k : ℤ, ((ℓ : ℤ) ^ b ∣ k) ∧ (1 : ℝ) / 3 ≤ Pn (sqScales ℓ) k := by
  refine ⟨((ℓ ^ b * (ℓ ^ ((b + 1) ^ 2 - b) / 2) : ℕ) : ℤ), ?_, ?_⟩
  · exact ⟨((ℓ ^ ((b + 1) ^ 2 - b) / 2 : ℕ) : ℤ), by push_cast; ring⟩
  · have hb : b < (b + 1) ^ 2 := by nlinarith
    have h := nrm_far_multiple hℓ b (b + 1) hb
    have hmem : ℓ ^ ((b + 1) ^ 2) ∈ sqScales ℓ := mem_sqScales (by omega)
    exact h.trans (le_Pn hmem _)

/-- No `ℓ`-adic neighbourhood `ℓ^b ℤ` of `0` is contained in a ball `{P_ℓ < δ}` with `δ ≤ 1/3`; hence the
topology of `(ℤ, P_ℓ)` is strictly finer than the `ℓ`-adic topology. -/
theorem no_adic_nbhd_in_ball {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {δ : ℝ} (hδ : δ ≤ 1 / 3) (b : ℕ) :
    ¬ ∀ k : ℤ, (ℓ : ℤ) ^ b ∣ k → Pn (sqScales ℓ) k < δ := by
  intro h
  obtain ⟨k, hk, hk3⟩ := exists_far_multiple hℓ b
  have := h k hk
  linarith

end TwoPrimes
end LeanCheck
