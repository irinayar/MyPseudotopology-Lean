import LeanCheck.TVGPlusValuation
import LeanCheck.JAWeilE
import LeanCheck.MixedPrimeSplit

/-!
# TVGplus for the pair `{2, 3}`: diagonal density from joint approximation

`DD_pair_of_JA`: joint approximation (`JAProp`) implies the diagonal density hypothesis `DD {2, 3}` of
`TVGPlusValuation` (every integer target vector is approximated in `P_2` and `P_3` simultaneously).  Hence the results of
`TVGPlusValuation` that were proved under `DD S` hold for `S = {2, 3}` conditionally on the single hypothesis
`TwoTermSeparation` of the joint-approximation development (`JA_of_matveev`):

* `pair_residues_of_matveev` (residue independence),
* `pair_valuation_vector_iff_of_matveev` (valuation vectors of the ball),
* `pair_gcd_valuation_of_matveev` (the ball contains an element of valuation exactly `a_p(δ)^2` at both primes, so the
  gcd of the ball has exactly this valuation at `2` and `3`).

Not covered: the absence of other prime factors in the gcd (it needs the character argument).
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime JAAssembly

private lemma sqne (ℓ : ℕ) : (sqScales ℓ).Nonempty := ⟨ℓ ^ (1 ^ 2), 1, le_rfl, rfl⟩

/-- **Joint approximation implies diagonal density for the pair `{2, 3}`.** -/
theorem DD_pair_of_JA (hJA : JAProp) : DD ({2, 3} : Finset ℕ) := by
  intro t ε hε
  set m : ℤ := t 2 - t 3 with hm
  have hden : 0 < |(m : ℝ)| + 1 := by positivity
  obtain ⟨k₀, h3, h2⟩ := hJA (ε / (|(m : ℝ)| + 1)) (by positivity)
  have hlt : |(m : ℝ)| * (ε / (|(m : ℝ)| + 1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith [abs_nonneg (m : ℝ)]
  refine ⟨t 3 + m * k₀, ?_⟩
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · have e : t 3 + m * k₀ - t 2 = m * (k₀ - 1) := by rw [hm]; ring
    rw [e]
    calc Pn (sqScales 2) (m * (k₀ - 1)) ≤ |(m : ℝ)| * Pn (sqScales 2) (k₀ - 1) :=
          Pn_zsmul_le (sqne 2) _ _
      _ ≤ |(m : ℝ)| * (ε / (|(m : ℝ)| + 1)) := mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)
      _ < ε := hlt
  · have e : t 3 + m * k₀ - t 3 = m * k₀ := by ring
    rw [e]
    calc Pn (sqScales 3) (m * k₀) ≤ |(m : ℝ)| * Pn (sqScales 3) k₀ := Pn_zsmul_le (sqne 3) _ _
      _ ≤ |(m : ℝ)| * (ε / (|(m : ℝ)| + 1)) := mul_le_mul_of_nonneg_left h3.le (abs_nonneg _)
      _ < ε := hlt

private lemma pair_prime : ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num

/-- Residue independence for `{2, 3}`, conditionally on the two-term separation. -/
theorem pair_residues_of_matveev (A : ℝ) (hA : 0 ≤ A) (hP : JAClose.TwoTermSeparation A) {δ : ℝ}
    (kp : ℕ → ℤ) (N : ℕ → ℕ) (hkp : ∀ p ∈ ({2, 3} : Finset ℕ), Pn (sqScales p) (kp p) < δ) :
    ∃ k : ℤ, InBall ({2, 3} : Finset ℕ) δ k ∧ ∀ p ∈ ({2, 3} : Finset ℕ), (p : ℤ) ^ (N p) ∣ k - kp p :=
  residues pair_prime (DD_pair_of_JA (JAWeil.JA_of_matveev A hA hP)) kp N hkp

/-- Valuation vectors of the ball for `{2, 3}`, conditionally on the two-term separation. -/
theorem pair_valuation_vector_iff_of_matveev (A : ℝ) (hA : 0 ≤ A) (hP : JAClose.TwoTermSeparation A)
    {δ : ℝ} (m : ℕ → ℕ) :
    (∃ k : ℤ, InBall ({2, 3} : Finset ℕ) δ k ∧
        ∀ p ∈ ({2, 3} : Finset ℕ), (p : ℤ) ^ (m p) ∣ k ∧ ¬ (p : ℤ) ^ (m p + 1) ∣ k) ↔
      ∀ p ∈ ({2, 3} : Finset ℕ), 1 / (p : ℝ) ^ ((Nat.sqrt (m p) + 1) ^ 2 - m p) < δ :=
  valuation_vector_iff pair_prime (DD_pair_of_JA (JAWeil.JA_of_matveev A hA hP)) m

/-- The gcd of the ball for `{2, 3}` has exactly the valuation `a_p(δ)^2` at `p = 2, 3`, conditionally on the two-term
separation. -/
theorem pair_gcd_valuation_of_matveev (A : ℝ) (hA : 0 ≤ A) (hP : JAClose.TwoTermSeparation A)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℤ, InBall ({2, 3} : Finset ℕ) δ k ∧ ∀ p ∈ ({2, 3} : Finset ℕ),
      (p : ℤ) ^ (aThr p δ ^ 2) ∣ k ∧ ¬ (p : ℤ) ^ (aThr p δ ^ 2 + 1) ∣ k :=
  gcd_valuation pair_prime (DD_pair_of_JA (JAWeil.JA_of_matveev A hA hP)) hδ

#print axioms DD_pair_of_JA
#print axioms pair_residues_of_matveev
#print axioms pair_valuation_vector_iff_of_matveev
#print axioms pair_gcd_valuation_of_matveev

end TVGPlus
end LeanCheck
