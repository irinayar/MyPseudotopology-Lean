import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.Ring

/-!
# Finite averaging for the random-translation step

The character-orthogonality identity below is unconditional. Substituting conjugate
amplitudes is the finite cross-term cancellation in the paper's averaged Fourier
energy formula. This file does not yet construct the lifted spatial weights or prove
the complete random-transfer theorem.
-/

namespace LeanCheck.MixedPrimeAveraging

open scoped BigOperators

theorem finite_translation_orthogonality (P : ℕ) [NeZero P]
    (a b : ZMod P → ℂ) :
    ∑ τ : ZMod P,
      (∑ l : ZMod P, a l * ZMod.stdAddChar (l * τ)) *
        (∑ m : ZMod P, b m * ZMod.stdAddChar (-(m * τ))) =
      (P : ℂ) * ∑ l : ZMod P, a l * b l := by
  have key : ∀ τ : ZMod P,
      (∑ l : ZMod P, a l * ZMod.stdAddChar (l * τ)) *
        (∑ m : ZMod P, b m * ZMod.stdAddChar (-(m * τ))) =
      ∑ l : ZMod P, ∑ m : ZMod P,
        (a l * b m) * ZMod.stdAddChar (τ * (l - m)) := by
    intro τ
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    have hc : (ZMod.stdAddChar (τ * (l - m)) : ℂ) =
        ZMod.stdAddChar (l * τ) * ZMod.stdAddChar (-(m * τ)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [hc]
    ring
  simp_rw [key]
  rw [Finset.sum_comm]
  have horder : (∑ l : ZMod P, ∑ τ : ZMod P, ∑ m : ZMod P,
        (a l * b m) * ZMod.stdAddChar (τ * (l - m))) =
      ∑ l : ZMod P, ∑ m : ZMod P, ∑ τ : ZMod P,
        (a l * b m) * ZMod.stdAddChar (τ * (l - m)) := by
    apply Finset.sum_congr rfl
    intro l _
    exact Finset.sum_comm
  rw [horder]
  have hsum : ∀ l m : ZMod P,
      (∑ τ : ZMod P, (a l * b m) * ZMod.stdAddChar (τ * (l - m))) =
      if l = m then (a l * b m) * (P : ℂ) else 0 := by
    intro l m
    rw [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar P)]
    simp [sub_eq_zero, ZMod.card]
  simp_rw [hsum]
  simp [Finset.mul_sum, mul_comm]

end LeanCheck.MixedPrimeAveraging

#print axioms LeanCheck.MixedPrimeAveraging.finite_translation_orthogonality
