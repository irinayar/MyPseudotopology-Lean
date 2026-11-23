import Mathlib

/-!
# TwoPrimes: a sum of a unimodal function over consecutive integers

If `f` is monotone on `[x₀, x₀ + p]` and antitone on `[x₀ + p, x₀ + p + q]` (so `x₀ + p` is a mode), then
`∑_{i = 0}^{p + q} f (x₀ + i) ≤ ∫_{x₀}^{x₀ + p + q} f + f (x₀ + p)`.
This is the one-dimensional lattice-point bound ("sum ≤ integral + maximum", `e = 1`) used for the one-ball stages of
the multi-stage recursion of notes X and AB of the TwoPrimes project, and the chord-sum step of Lemma X1 / X1'.
-/

namespace LeanCheck
namespace TwoPrimes

open MeasureTheory intervalIntegral

theorem unimodal_sum_le_integral_add_max (f : ℝ → ℝ) (x₀ : ℝ) (p q : ℕ)
    (hmono : MonotoneOn f (Set.Icc x₀ (x₀ + p)))
    (hanti : AntitoneOn f (Set.Icc (x₀ + p) (x₀ + p + q))) :
    ∑ i ∈ Finset.range (p + q + 1), f (x₀ + i) ≤ (∫ x in x₀..x₀ + p + q, f x) + f (x₀ + p) := by
  have hL : ∑ i ∈ Finset.range p, f (x₀ + i) ≤ ∫ x in x₀..x₀ + p, f x := hmono.sum_le_integral
  have hR : ∑ i ∈ Finset.range q, f (x₀ + p + ((i + 1 : ℕ) : ℝ)) ≤ ∫ x in (x₀ + p)..(x₀ + p + q), f x :=
    hanti.sum_le_integral
  have hint1 : IntervalIntegrable f volume x₀ (x₀ + p) := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le (by have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith)]
    exact hmono
  have hint2 : IntervalIntegrable f volume (x₀ + p) (x₀ + p + q) := by
    apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le (by have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith)]
    exact hanti
  have hsplit : (∫ x in x₀..x₀ + p, f x) + ∫ x in (x₀ + p)..(x₀ + p + q), f x
      = ∫ x in x₀..x₀ + p + q, f x := integral_add_adjacent_intervals hint1 hint2
  have hsum : ∑ i ∈ Finset.range (p + q + 1), f (x₀ + i)
      = ∑ i ∈ Finset.range p, f (x₀ + i) + f (x₀ + p) + ∑ i ∈ Finset.range q, f (x₀ + p + ((i + 1 : ℕ) : ℝ)) := by
    rw [show p + q + 1 = p + (q + 1) by ring, Finset.sum_range_add, Finset.sum_range_succ' _ q]
    have e1 : ∀ i : ℕ, f (x₀ + ((p + (i + 1) : ℕ) : ℝ)) = f (x₀ + p + ((i + 1 : ℕ) : ℝ)) := by
      intro i; congr 1; push_cast; try ring
    have e0 : f (x₀ + ((p + 0 : ℕ) : ℝ)) = f (x₀ + p) := by
      simp
    simp only [e1, e0]
    ring
  rw [hsum]
  linarith

end TwoPrimes
end LeanCheck
