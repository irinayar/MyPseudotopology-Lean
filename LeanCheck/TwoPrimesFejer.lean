import Mathlib

/-!
# TwoPrimes: the counting form of the Fejer averaging identity

For `J, N : ℕ` with `2 J < N`, the number of pairs `(d, d')` of integers of `[-J, J]` with `d ≡ d' (mod N)` equals
`2 J + 1` (only the diagonal survives).  This is the combinatorial core of the identity
`∑_{r mod N} F_J(r / N) = N / (2 J + 1)` used in note AC of the TwoPrimes project (expand the Fejer kernel
`F_J(x) = |∑_{|d| ≤ J} e(d x)|² / (2 J + 1)²`, sum over a complete residue system modulo `N`: only the pairs with
`d ≡ d'` survive, and `N ≥ 2 J + 1` forces `d = d'`).  The trigonometric form itself is not formalized.
-/

namespace LeanCheck
namespace TwoPrimes

open Finset

/-- Two integers of `[-J, J]` that are congruent modulo `N > 2 J` are equal. -/
lemma eq_of_modEq_of_mem_Icc {J N : ℕ} (hN : 2 * J < N) {d d' : ℤ}
    (hd : d ∈ Finset.Icc (-(J : ℤ)) J) (hd' : d' ∈ Finset.Icc (-(J : ℤ)) J)
    (h : d ≡ d' [ZMOD N]) : d = d' := by
  rw [Finset.mem_Icc] at hd hd'
  have h1 : (N : ℤ) ∣ d' - d := Int.modEq_iff_dvd.mp h
  have h2 : |d' - d| < (N : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have h3 : d' - d = 0 := Int.eq_zero_of_abs_lt_dvd h1 h2
  omega

/-- The pairs of `[-J, J]²` congruent modulo `N > 2 J` are exactly the `2 J + 1` diagonal pairs. -/
theorem card_congr_pairs {J N : ℕ} (hN : 2 * J < N) :
    ((Finset.Icc (-(J : ℤ)) J ×ˢ Finset.Icc (-(J : ℤ)) J).filter
      (fun p : ℤ × ℤ => p.1 ≡ p.2 [ZMOD N])).card = 2 * J + 1 := by
  have key : (Finset.Icc (-(J : ℤ)) J ×ˢ Finset.Icc (-(J : ℤ)) J).filter
      (fun p : ℤ × ℤ => p.1 ≡ p.2 [ZMOD N]) = (Finset.Icc (-(J : ℤ)) J).image (fun d => (d, d)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, hb⟩, h⟩
      have hab := eq_of_modEq_of_mem_Icc hN ha hb h
      exact ⟨a, ha, rfl, hab⟩
    · rintro ⟨d, hd, rfl, rfl⟩
      exact ⟨⟨hd, hd⟩, Int.ModEq.refl _⟩
  rw [key, Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h)]
  simp
  omega

end TwoPrimes
end LeanCheck
