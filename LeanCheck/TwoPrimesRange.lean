import LeanCheck.MixedPrimeRadii

/-!
# TwoPrimes: elementary steps of the range claim

* `card_le_of_cover`: if every integer `t` with `|t| ≤ M` is a difference `a - b` with `a ∈ A`, `b ∈ B`
  (finite sets), then `2 M + 1 ≤ |A| |B|`.  This is the counting inequality of Step 2 of the theorem that the
  exponent of the range claim is at least `x_S`.
* `unit_target_dvd`, `unit_target_lower`: if `P₃(k) < ε`, `P₂(k - 1) < ε`, `ε ≤ 1/3` and
  `ε ≤ 2^(-(2 ⌊√(a-1)⌋ + 1))` (`a ≥ 1`), then `2^a ∣ k - 1` and `2^a ≤ |k - 1|` (Step 1: the height of the unit
  target is at least `2^a - 1`).
* `gap_ge`, `exists_gap`: if `ε 2^(n²) ≤ k ≤ (1 - ε) 2^(n²)` then `P₂(k) ≥ ε`; hence for `0 ≤ ε < 1/2` and every
  `H` there is an integer `s` such that no `b` with `|b - s| ≤ H` has `P₂(b) < ε`: the ball of radius `ε` has
  arbitrarily long gaps (the heart of the statement that no bound is uniform over all integer targets).
-/

namespace LeanCheck
namespace TwoPrimes

open LeanCheck.MixedPrime

/-- Counting lemma: a covered range of length `2 M + 1` needs `|A| |B| ≥ 2 M + 1`. -/
theorem card_le_of_cover (A B : Finset ℤ) (M : ℕ)
    (h : ∀ t : ℤ, |t| ≤ M → ∃ a ∈ A, ∃ b ∈ B, t = a - b) :
    2 * M + 1 ≤ A.card * B.card := by
  classical
  have hsub : Finset.Icc (-(M : ℤ)) M ⊆ (A ×ˢ B).image (fun x : ℤ × ℤ => x.1 - x.2) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have h1 : |t| ≤ M := abs_le.mpr ht
    obtain ⟨a, ha, b, hb, hab⟩ := h t h1
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, hab.symm⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := A ×ˢ B) (f := fun x : ℤ × ℤ => x.1 - x.2)
  rw [Finset.card_product] at h2
  have h3 : (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
    rw [Int.card_Icc]; omega
  omega

/-- Step 1 (divisibility): `P₂(k - 1) < ε ≤ 2^(-(2⌊√(a-1)⌋+1))` forces `2^a ∣ k - 1`. -/
theorem unit_target_dvd {ε : ℝ} {a : ℕ} (ha : 1 ≤ a)
    (hε : ε ≤ 1 / (2 : ℝ) ^ (2 * Nat.sqrt (a - 1) + 1)) {k : ℤ}
    (h2 : Pn (sqScales 2) (k - 1) < ε) : (2 : ℤ) ^ a ∣ k - 1 := by
  by_contra hnd
  have h := valuation_bound (ℓ := 2) Nat.prime_two ha (k := k - 1) (by exact_mod_cast hnd)
  have h' : (1 : ℝ) / (2 : ℝ) ^ (2 * Nat.sqrt (a - 1) + 1) ≤ Pn (sqScales 2) (k - 1) := by
    simpa using h
  linarith

/-- `P₃(1) ≥ 1/3`. -/
lemma Pn_three_one : (1 : ℝ) / 3 ≤ Pn (sqScales 3) 1 := by
  have hmem : 3 ^ (1 ^ 2) ∈ sqScales 3 := mem_sqScales (le_refl 1)
  have h := le_Pn hmem 1
  have e : (((1 : ℤ) : ℝ) / ((3 ^ (1 ^ 2) : ℕ) : ℝ)) = 1 / 3 := by norm_num
  rw [e] at h
  have habs : |(1 : ℝ) / 3| ≤ 1 / 2 := by
    rw [abs_of_pos (by norm_num)]; norm_num
  rw [nrm_eq_abs habs, abs_of_pos (by norm_num)] at h
  exact h

/-- Step 1: the unit-target witness satisfies `2^a ≤ |k - 1|`. -/
theorem unit_target_lower {ε : ℝ} (hε3 : ε ≤ 1 / 3) {a : ℕ} (ha : 1 ≤ a)
    (hε : ε ≤ 1 / (2 : ℝ) ^ (2 * Nat.sqrt (a - 1) + 1)) {k : ℤ}
    (h3 : Pn (sqScales 3) k < ε) (h2 : Pn (sqScales 2) (k - 1) < ε) :
    (2 : ℤ) ^ a ≤ |k - 1| := by
  have hk1 : k ≠ 1 := by
    rintro rfl
    have := Pn_three_one
    linarith
  have hne : k - 1 ≠ 0 := sub_ne_zero.mpr hk1
  have hd := unit_target_dvd ha hε h2
  have hpos : 0 < |k - 1| := abs_pos.mpr hne
  exact Int.le_of_dvd hpos ((dvd_abs _ _).mpr hd)

lemma nrm_ge_of_mem_Icc {x ε : ℝ} (hε : 0 ≤ ε) (h1 : ε ≤ x) (h2 : x ≤ 1 - ε) : ε ≤ nrm x := by
  rw [nrm_eq]
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = round x := ⟨_, rfl⟩
  rw [← hz]
  by_cases hz0 : z ≤ 0
  · have : (z : ℝ) ≤ 0 := by exact_mod_cast hz0
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (1 : ℝ) ≤ z := by exact_mod_cast (by omega : (1 : ℤ) ≤ z)
    rw [abs_of_nonpos (by linarith)]; linarith

/-- If `ε 2^(n²) ≤ k ≤ (1 - ε) 2^(n²)` then `P₂(k) ≥ ε`. -/
theorem gap_ge {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} (hn : 1 ≤ n) {k : ℤ}
    (h1 : ε * (2 : ℝ) ^ (n ^ 2) ≤ k) (h2 : (k : ℝ) ≤ (1 - ε) * (2 : ℝ) ^ (n ^ 2)) :
    ε ≤ Pn (sqScales 2) k := by
  have hmem : 2 ^ (n ^ 2) ∈ sqScales 2 := mem_sqScales hn
  have hq : (0 : ℝ) < (2 : ℝ) ^ (n ^ 2) := by positivity
  have h := le_Pn hmem k
  refine le_trans ?_ h
  have hc : (((2 ^ (n ^ 2) : ℕ)) : ℝ) = (2 : ℝ) ^ (n ^ 2) := by push_cast; ring
  rw [hc]
  apply nrm_ge_of_mem_Icc hε
  · rw [le_div_iff₀ hq]; exact h1
  · rw [div_le_iff₀ hq]; linarith

/-- The ball `{P₂ < ε}`, `0 ≤ ε < 1/2`, has gaps of every length: for each `H` there is `s` with
`P₂(b) ≥ ε` for all integers `b` with `|b - s| ≤ H`. -/
theorem exists_gap (H : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    ∃ s : ℤ, ∀ b : ℤ, |b - s| ≤ H → ε ≤ Pn (sqScales 2) b := by
  have hδ : (0 : ℝ) < 1 / 2 - ε := by linarith
  obtain ⟨n, hn1, hn⟩ : ∃ n : ℕ, 1 ≤ n ∧ (H : ℝ) ≤ (1 / 2 - ε) * (2 : ℝ) ^ (n ^ 2) := by
    refine ⟨⌈(H : ℝ) / (1 / 2 - ε)⌉₊ + 1, by omega, ?_⟩
    set n := ⌈(H : ℝ) / (1 / 2 - ε)⌉₊ + 1 with hn
    have h1 : (H : ℝ) / (1 / 2 - ε) ≤ n := by
      have := Nat.le_ceil ((H : ℝ) / (1 / 2 - ε)); rw [hn]; push_cast; linarith
    have h2 : (n : ℝ) ≤ (2 : ℝ) ^ (n ^ 2) := by
      have h3 : n < 2 ^ (n ^ 2) :=
        lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
      exact_mod_cast h3.le
    have h4 : (H : ℝ) ≤ (1 / 2 - ε) * n := by
      rw [div_le_iff₀ hδ] at h1; linarith
    exact h4.trans (mul_le_mul_of_nonneg_left h2 hδ.le)
  have hq : (2 : ℝ) ^ (n ^ 2) = 2 * (2 : ℝ) ^ (n ^ 2 - 1) := by
    have : n ^ 2 = (n ^ 2 - 1) + 1 := by
      have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    conv_lhs => rw [this, pow_succ]
    ring
  refine ⟨(2 : ℤ) ^ (n ^ 2 - 1), fun b hb => ?_⟩
  have hb' : |(b : ℝ) - ((2 : ℤ) ^ (n ^ 2 - 1) : ℤ)| ≤ H := by exact_mod_cast hb
  have hs : (((2 : ℤ) ^ (n ^ 2 - 1) : ℤ) : ℝ) = (2 : ℝ) ^ (n ^ 2 - 1) := by push_cast; ring
  rw [hs] at hb'
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb'
  apply gap_ge hε0 hn1
  · nlinarith
  · nlinarith

end TwoPrimes
end LeanCheck
