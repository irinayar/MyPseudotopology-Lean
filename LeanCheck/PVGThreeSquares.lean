import LeanCheck.PVGThreeDyadic

/-!
# PVGthree: a recurring shifted square forces non-rigidity

For a strictly increasing sequence of natural exponents `L`, if one integer
shift `j` makes `L k + j` a square for infinitely many `k`, every coefficient
in `A(dyseq L)` is a dyadic rational. Combined with `not_rig`, this proves
non-rigidity when the gaps of `L` are unbounded.

The shift is an integer, including negative values. The infinitely many square
roots may initially include zero; strict growth of `L` lets the proof select a
positive root, as required by the sequence `sT n = 2^((n+1)^2)`.
-/

open Filter Topology Set

namespace PVG
namespace Three
open Two Q95 Lac

/-- A recurring square coordinate forces the corresponding fixed circle
coordinate of every coefficient in `A` to vanish. -/
theorem dint_zpow_eq_zero_of_infinite_shifted_squares
    (L : ℕ → ℕ) (hL : StrictMono L) (j : ℤ)
    (hsq : Set.Infinite {k : ℕ | ∃ n : ℕ, (L k : ℤ) + j = (n : ℤ) ^ 2})
    (a : ℝ) (ha : InA (dyseq L) sT a) : dint (a * (2 : ℝ) ^ j) = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (dint_nonneg _)
  rw [zero_add]
  obtain ⟨K, hK⟩ := eventually_atTop.1 (ha ε hε)
  obtain ⟨k, ⟨n, hn⟩, hk⟩ := hsq.exists_gt (max K j.natAbs)
  have hjabs : -j ≤ (j.natAbs : ℤ) := by
    simpa using (Int.le_natAbs (a := -j))
  have hkL : k ≤ L k := hL.id_le k
  have hpos : 0 < (L k : ℤ) + j := by omega
  have hnpos : 0 < n := by
    by_contra hc
    have hn0 : n = 0 := by omega
    simp only [hn0, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0)] at hn
    omega
  have hs : sT (n - 1) = (2 : ℝ) ^ ((n : ℤ) ^ 2) := by
    show (2 : ℝ) ^ ((n - 1 + 1) ^ 2) = _
    rw [Nat.sub_add_cancel hnpos, ← zpow_natCast]
    congr 1
  have he : a * dyseq L k * sT (n - 1) = a * (2 : ℝ) ^ j := by
    rw [hs, mul_assoc]
    congr 1
    unfold dyseq
    rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ two_ne_zero]
    congr 1
    omega
  have h := hK k (by omega) (n - 1)
  rwa [he] at h

/-- A real number whose multiple by an integer power of two is an integer
is a dyadic rational. -/
theorem dyadic_of_dint_zpow_eq_zero (a : ℝ) (j : ℤ)
    (h : dint (a * (2 : ℝ) ^ j) = 0) :
    ∃ r : ℕ, ∃ z : ℤ, a = z / 2 ^ r := by
  have hz : a * (2 : ℝ) ^ j = (round (a * (2 : ℝ) ^ j) : ℝ) := by
    rwa [Two.dint_eq, abs_eq_zero, sub_eq_zero] at h
  obtain ⟨z, hz⟩ : ∃ z : ℤ, a * (2 : ℝ) ^ j = z := ⟨_, hz⟩
  cases j with
  | ofNat r =>
    rw [Int.ofNat_eq_natCast, zpow_natCast] at hz
    exact ⟨r, z, (eq_div_iff (by positivity)).2 hz⟩
  | negSucc r =>
    have he : Int.negSucc r = -((r + 1 : ℕ) : ℤ) := by omega
    rw [he, zpow_neg, zpow_natCast, ← div_eq_mul_inv] at hz
    refine ⟨0, z * 2 ^ (r + 1), ?_⟩
    simpa only [pow_zero, div_one, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using
      (div_eq_iff (by positivity : (2 : ℝ) ^ (r + 1) ≠ 0)).1 hz

/-- The coefficient group is contained in the dyadic rationals if one shifted
square occurs infinitely often. -/
theorem inA_dyadic_of_infinite_shifted_squares
    (L : ℕ → ℕ) (hL : StrictMono L) (j : ℤ)
    (hsq : Set.Infinite {k : ℕ | ∃ n : ℕ, (L k : ℤ) + j = (n : ℤ) ^ 2})
    (a : ℝ) (ha : InA (dyseq L) sT a) :
    ∃ r : ℕ, ∃ z : ℤ, a = z / 2 ^ r :=
  dyadic_of_dint_zpow_eq_zero a j
    (dint_zpow_eq_zero_of_infinite_shifted_squares L hL j hsq a ha)

/-- Corollary 4.7: unbounded gaps together with infinitely many occurrences of
one shifted square imply non-rigidity. -/
theorem not_rig_of_infinite_shifted_squares
    (L : ℕ → ℕ) (hL : StrictMono L)
    (hgaps : ∀ G : ℕ, ∃ k, L k + G ≤ L (k + 1)) (j : ℤ)
    (hsq : Set.Infinite {k : ℕ | ∃ n : ℕ, (L k : ℤ) + j = (n : ℤ) ^ 2}) :
    ¬ Rig (dyseq L) :=
  not_rig L hL hgaps (inA_dyadic_of_infinite_shifted_squares L hL j hsq)

/-- The square-shift criterion stated with Mathlib's integer `IsSquare` and
an existential integer shift, exactly allowing every integer square root. -/
theorem not_rig_of_square_shift
    (L : ℕ → ℕ) (hL : StrictMono L)
    (hgaps : ∀ G : ℕ, ∃ k, L k + G ≤ L (k + 1))
    (hsq : ∃ j : ℤ, Set.Infinite {k : ℕ | IsSquare ((L k : ℤ) + j)}) :
    ¬ Rig (dyseq L) := by
  obtain ⟨j, hj⟩ := hsq
  apply not_rig_of_infinite_shifted_squares L hL hgaps j
  refine hj.mono ?_
  intro k hk
  obtain ⟨z, hz⟩ := (isSquare_iff_exists_sq _).1 hk
  refine ⟨z.natAbs, ?_⟩
  simpa only [Int.natCast_natAbs, sq_abs] using hz

end Three
end PVG
