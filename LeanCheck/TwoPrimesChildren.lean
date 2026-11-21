import Mathlib

/-!
# TwoPrimes: the child count of the digit model (Lemma 4.1 of TwoPrimes_v2)

Let `ℓ` be a prime, `D` a natural number which is not a power of `ℓ`, `r = 1/D`, and `m ≥ 0`.  Put
`ρ = ℓ^m / D`.  Then for every real `s` with `|s| < r` the integers `j` with `|j + s| < ρ` are exactly those with
`|j| ≤ ⌊ℓ^m / D⌋`.  (In the digit model `m = 2n - 1`, `ρ = ρ_n`, `J_n = ⌊ρ_n⌋`, and `s` is the offset
`t'/q_{n-1}` of a point of the previous level.)

* `children_iff`: the real-arithmetic core: `r ≤ θ ≤ 1 - r`, `ρ = J + θ`, `|s| < r` gives
  `|j + s| < ρ ↔ |j| ≤ J`.
* `not_dvd_pow_of_not_pow`: if `D` is not a power of the prime `ℓ` then `D ∤ ℓ^m` for all `m`.
* `children_of_regular`: the statement for `ρ = ℓ^m / D` with `D ≥ 2` not a power of `ℓ`.
-/

namespace LeanCheck
namespace TwoPrimes

/-- Core real-arithmetic lemma. -/
theorem children_iff {r θ s : ℝ} {J : ℕ} (hθ1 : r ≤ θ) (hθ2 : θ ≤ 1 - r)
    (hs : |s| < r) (j : ℤ) : |(j : ℝ) + s| < J + θ ↔ |j| ≤ (J : ℤ) := by
  have hj : |(j : ℝ)| = ((|j| : ℤ) : ℝ) := by push_cast; rfl
  constructor
  · intro h
    by_contra hcon
    have hge : (J : ℤ) + 1 ≤ |j| := by omega
    have hge' : (J : ℝ) + 1 ≤ |(j : ℝ)| := by rw [hj]; exact_mod_cast hge
    have h1 : |(j : ℝ)| - |s| ≤ |(j : ℝ) + s| := by
      have := abs_sub_abs_le_abs_sub (j : ℝ) (-s)
      simpa [abs_neg, sub_neg_eq_add] using this
    linarith
  · intro h
    have hle : |(j : ℝ)| ≤ J := by rw [hj]; exact_mod_cast h
    have h1 : |(j : ℝ) + s| ≤ |(j : ℝ)| + |s| := abs_add_le _ _
    linarith

/-- If `D` is not a power of the prime `ℓ`, then `D` does not divide any power of `ℓ`. -/
theorem not_dvd_pow_of_not_pow {ℓ D : ℕ} (hℓ : ℓ.Prime) (hD : ¬ ∃ j : ℕ, D = ℓ ^ j) (m : ℕ) :
    ¬ D ∣ ℓ ^ m := by
  intro h
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hℓ).1 h
  exact hD ⟨j, hj⟩

/-- Lemma 4.1: for `D ≥ 2` not a power of the prime `ℓ`, `|s| < 1/D`:
`|j + s| < ℓ^m / D ↔ |j| ≤ ⌊ℓ^m / D⌋`. -/
theorem children_of_regular {ℓ D : ℕ} (hℓ : ℓ.Prime) (hD2 : 2 ≤ D) (hD : ¬ ∃ j : ℕ, D = ℓ ^ j)
    (m : ℕ) {s : ℝ} (hs : |s| < 1 / (D : ℝ)) (j : ℤ) :
    |(j : ℝ) + s| < (ℓ : ℝ) ^ m / D ↔ |j| ≤ ((ℓ ^ m / D : ℕ) : ℤ) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hnd := not_dvd_pow_of_not_pow hℓ hD m
  have hmod : ℓ ^ m % D ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have hmodlt : ℓ ^ m % D < D := Nat.mod_lt _ (by omega)
  have hdm : ℓ ^ m = D * (ℓ ^ m / D) + ℓ ^ m % D := (Nat.div_add_mod _ _).symm
  set J := ℓ ^ m / D with hJ
  set e := ℓ ^ m % D with he
  have hθ : (ℓ : ℝ) ^ m / D = J + (e : ℝ) / D := by
    have : ((ℓ ^ m : ℕ) : ℝ) = (D : ℝ) * J + e := by exact_mod_cast hdm
    have h2 : (ℓ : ℝ) ^ m = (D : ℝ) * J + e := by exact_mod_cast this
    rw [h2]; field_simp
  have h1 : (1 : ℝ) ≤ e := by exact_mod_cast (Nat.pos_of_ne_zero hmod)
  have h2 : (e : ℝ) ≤ D - 1 := by
    have : e + 1 ≤ D := hmodlt
    have : (e : ℝ) + 1 ≤ D := by exact_mod_cast this
    linarith
  have hθ1 : 1 / (D : ℝ) ≤ (e : ℝ) / D := by
    apply div_le_div_of_nonneg_right h1 hDpos.le
  have hθ2 : (e : ℝ) / D ≤ 1 - 1 / D := by
    rw [div_le_iff₀ hDpos, sub_mul, one_div, inv_mul_cancel₀ hDpos.ne']; linarith
  rw [hθ]
  exact children_iff hθ1 hθ2 hs j

end TwoPrimes
end LeanCheck
