import LeanCheck.TVGPlusDD
import LeanCheck.TVGPlusOrder

/-!
# TVGplus: explicit sizes in the block construction, and the remaining parts of the logarithmic-order theorem

* `block_combine`: the construction `k = m a + (1 - m) b` of `DD_union` with the size bound `|k| ≤ (|m| + 1) (|a| + |b|)`
  (Proposition "explicit sizes", used for the effective transfer from unit-target block witnesses to all targets).
* `affine_target_size`: for `k = t_B + (t_A - t_B) m` one has `|k| ≤ |t_B| + |t_A - t_B| |m|`.
* `aS_sq_sub_four_cS`: `A_S² - 4 c_S = ∑_{p ∈ S} ∑_{q ∈ S, q ≠ p} 1/(sqrt (log p) sqrt (log q))`
  (twice the sum over unordered pairs, as in the statement of the theorem).
* `xS_lt_aS_sq`: `x_S < A_S²` for nonempty `S`.
* `order_singleton_limit`: for one prime, `log u_{p}(δ) / (log (1/δ))² → 1/(4 log p)` (in `ε`-`δ₀` form).

No external hypothesis, no `sorry`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

theorem block_combine {A B : Finset ℕ} (t : ℕ → ℤ) {ε : ℝ} (hε : 0 < ε) (a b m : ℤ)
    (ha : ∀ p ∈ A, Pn (sqScales p) (a - t p) < ε / 4)
    (hb : ∀ q ∈ B, Pn (sqScales q) (b - t q) < ε / 4)
    (hm1 : ∀ p ∈ A, Pn (sqScales p) (m - 1) < ε / (4 * (|(a : ℝ)| + |(b : ℝ)| + 1)))
    (hm2 : ∀ q ∈ B, Pn (sqScales q) m < ε / (4 * (|(a : ℝ)| + |(b : ℝ)| + 1))) :
    (∀ p ∈ A ∪ B, Pn (sqScales p) (m * a + (1 - m) * b - t p) < ε) ∧
      |((m * a + (1 - m) * b : ℤ) : ℝ)| ≤ (|(m : ℝ)| + 1) * (|(a : ℝ)| + |(b : ℝ)|) := by
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = |(a : ℝ)| + |(b : ℝ)| + 1 := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  rw [← hMdef] at hm1 hm2
  have hab : |((b - a : ℤ) : ℝ)| ≤ M := by
    rw [hMdef]; push_cast
    have := abs_sub (b : ℝ) (a : ℝ)
    have := abs_nonneg (a : ℝ)
    linarith
  have hba : |((a - b : ℤ) : ℝ)| ≤ M := by
    rw [hMdef]; push_cast
    have := abs_sub (a : ℝ) (b : ℝ)
    have := abs_nonneg (b : ℝ)
    linarith
  have hMη : M * (ε / (4 * M)) = ε / 4 := by field_simp
  refine ⟨fun p hp => ?_, ?_⟩
  · rcases Finset.mem_union.mp hp with hpA | hpB
    · have e : m * a + (1 - m) * b - t p = (a - t p) + (b - a) * (1 - m) := by ring
      rw [e]
      have h1 := Pn_add_le (sq_nonempty p) (a - t p) ((b - a) * (1 - m))
      have h2 := Pn_zsmul_le (sq_nonempty p) (b - a) (1 - m)
      have h3 : Pn (sqScales p) (1 - m) = Pn (sqScales p) (m - 1) := by
        rw [← Pn_neg]; congr 1; ring
      have h4 := hm1 p hpA
      have h5 := ha p hpA
      rw [h3] at h2
      have h6 : |((b - a : ℤ) : ℝ)| * Pn (sqScales p) (m - 1) ≤ M * Pn (sqScales p) (m - 1) :=
        mul_le_mul_of_nonneg_right hab (Pn_nonneg _ _)
      have h7 : M * Pn (sqScales p) (m - 1) < M * (ε / (4 * M)) := mul_lt_mul_of_pos_left h4 hM
      linarith
    · have e : m * a + (1 - m) * b - t p = (b - t p) + (a - b) * m := by ring
      rw [e]
      have h1 := Pn_add_le (sq_nonempty p) (b - t p) ((a - b) * m)
      have h2 := Pn_zsmul_le (sq_nonempty p) (a - b) m
      have h4 := hm2 p hpB
      have h5 := hb p hpB
      have h6 : |((a - b : ℤ) : ℝ)| * Pn (sqScales p) m ≤ M * Pn (sqScales p) m :=
        mul_le_mul_of_nonneg_right hba (Pn_nonneg _ _)
      have h7 : M * Pn (sqScales p) m < M * (ε / (4 * M)) := mul_lt_mul_of_pos_left h4 hM
      linarith
  · push_cast
    have h1 : |(m : ℝ) * a + (1 - m) * b| ≤ |(m : ℝ)| * |(a : ℝ)| + |1 - (m : ℝ)| * |(b : ℝ)| := by
      have := abs_add_le ((m : ℝ) * a) ((1 - (m : ℝ)) * b)
      rwa [abs_mul, abs_mul] at this
    have h2 : |1 - (m : ℝ)| ≤ 1 + |(m : ℝ)| := by
      have := abs_sub (1 : ℝ) (m : ℝ)
      simpa using this
    have h3 : |1 - (m : ℝ)| * |(b : ℝ)| ≤ (1 + |(m : ℝ)|) * |(b : ℝ)| :=
      mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    nlinarith [abs_nonneg (m : ℝ), abs_nonneg (a : ℝ), abs_nonneg (b : ℝ)]

theorem affine_target_size (tA tB m : ℤ) :
    |((tB + (tA - tB) * m : ℤ) : ℝ)| ≤ |(tB : ℝ)| + |((tA - tB : ℤ) : ℝ)| * |(m : ℝ)| := by
  have := abs_add_le (tB : ℝ) (((tA - tB : ℤ) : ℝ) * m)
  rw [abs_mul] at this
  push_cast at this ⊢
  exact this

theorem aS_sq_sub_four_cS (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    aS S ^ 2 - 4 * cS S =
      ∑ p ∈ S, ∑ q ∈ S.erase p, (1 / Real.sqrt (Real.log p)) * (1 / Real.sqrt (Real.log q)) := by
  classical
  rw [four_cS_eq S hS]
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun p : ℕ => 1 / Real.sqrt (Real.log (p : ℝ)) := ⟨_, rfl⟩
  have hA : aS S = ∑ p ∈ S, u p := by rw [hu]; rfl
  have h : aS S ^ 2 = ∑ p ∈ S, u p * aS S := by
    calc aS S ^ 2 = (∑ p ∈ S, u p) * aS S := by rw [pow_two, ← hA]
      _ = ∑ p ∈ S, u p * aS S := by rw [Finset.sum_mul]
  have e : ∀ p ∈ S, u p * aS S = (u p) ^ 2 + ∑ q ∈ S.erase p, u p * u q := by
    intro p hp
    rw [hA, ← Finset.add_sum_erase S u hp, mul_add, ← Finset.mul_sum, pow_two]
  have hsq : ∑ p ∈ S, (1 / Real.sqrt (Real.log p)) ^ 2 = ∑ p ∈ S, (u p) ^ 2 := by rw [hu]
  rw [hsq, h, Finset.sum_congr rfl e, Finset.sum_add_distrib]
  rw [hu]
  ring

theorem xS_lt_aS_sq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) : xS S < aS S ^ 2 := by
  have hc : 0 < cS S :=
    Finset.sum_pos (fun p hp => by have := log_pos_of_prime (hS p hp); positivity) hne
  have hA : 0 < aS S :=
    Finset.sum_pos (fun p hp => by have := log_pos_of_prime (hS p hp); positivity) hne
  have hd := disc_nonneg S hS
  have hR : Real.sqrt (aS S ^ 2 - 4 * cS S) < aS S :=
    (Real.sqrt_lt' hA).mpr (by linarith)
  have hR0 : 0 ≤ Real.sqrt (aS S ^ 2 - 4 * cS S) := Real.sqrt_nonneg _
  unfold xS yPlus
  nlinarith

theorem order_singleton_limit {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      |Real.log (uS {p} δ) / Real.log (1 / δ) ^ 2 - 1 / (4 * Real.log p)| < ε := by
  have hl := log_pos_of_prime hp
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, L₀ = max (max (Real.log p) 1) (3 / (4 * ε) + 1) := ⟨_, rfl⟩
  have hL₀1 : 1 ≤ L₀ := by rw [hL₀]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨Real.exp (-L₀), Real.exp_pos _, ?_⟩
  intro δ hδ hδ0
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ0 (by rw [Real.exp_le_one_iff]; linarith)
  have hLL : L₀ < Real.log (1 / δ) := by
    rw [log_inv_eq]
    have := Real.log_lt_log hδ hδ0
    rw [Real.log_exp] at this
    linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (1 / δ) := ⟨_, rfl⟩
  rw [← hLdef] at hLL ⊢
  have hLp : Real.log p ≤ L := by
    have : Real.log p ≤ L₀ := by rw [hL₀]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hLe : 3 / (4 * ε) + 1 ≤ L := by
    have : 3 / (4 * ε) + 1 ≤ L₀ := by rw [hL₀]; exact le_max_right _ _
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  -- the exact value
  have hu : Real.log (uS {p} δ) = (aThr p δ : ℝ) ^ 2 * Real.log p := by
    rw [uS_singleton hp hδ]
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  rw [hu]
  set ℓ := Real.log p with hℓ
  have hg := aThr_ge hp hδ
  have hle := aThr_le hp hδ hδ1
  rw [← hLdef] at hg hle
  have ha0 : 0 ≤ (aThr p δ : ℝ) := Nat.cast_nonneg _
  have hlow0 : 0 ≤ (L / ℓ - 1) / 2 := by
    have : 1 ≤ L / ℓ := by rw [le_div_iff₀ hl]; linarith
    linarith
  have h2lo : ((L / ℓ - 1) / 2) ^ 2 ≤ (aThr p δ : ℝ) ^ 2 := pow_le_pow_left₀ hlow0 hg 2
  have h2hi : (aThr p δ : ℝ) ^ 2 ≤ ((L / ℓ + 1) / 2) ^ 2 := pow_le_pow_left₀ ha0 hle 2
  have hlo : ((L - ℓ) ^ 2 / (4 * ℓ)) ≤ (aThr p δ : ℝ) ^ 2 * ℓ := by
    have := mul_le_mul_of_nonneg_right h2lo hl.le
    have e : ((L / ℓ - 1) / 2) ^ 2 * ℓ = (L - ℓ) ^ 2 / (4 * ℓ) := by field_simp; ring
    linarith
  have hhi : (aThr p δ : ℝ) ^ 2 * ℓ ≤ ((L + ℓ) ^ 2 / (4 * ℓ)) := by
    have := mul_le_mul_of_nonneg_right h2hi hl.le
    have e : ((L / ℓ + 1) / 2) ^ 2 * ℓ = (L + ℓ) ^ 2 / (4 * ℓ) := by field_simp; ring
    linarith
  have hL2 : 0 < L ^ 2 := by positivity
  rw [abs_lt]
  have hc : 1 / (4 * ℓ) = L ^ 2 / (4 * ℓ) / L ^ 2 := by field_simp
  have hbound : (2 * L + ℓ) / (4 * L ^ 2) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have h3 : 3 / (4 * ε) < L := by linarith
    rw [div_lt_iff₀ (by positivity)] at h3
    nlinarith
  constructor
  · -- lower side
    have h1 : (aThr p δ : ℝ) ^ 2 * ℓ / L ^ 2 ≥ (L - ℓ) ^ 2 / (4 * ℓ) / L ^ 2 :=
      div_le_div_of_nonneg_right hlo hL2.le
    have e1 : (L - ℓ) ^ 2 / (4 * ℓ) / L ^ 2 - 1 / (4 * ℓ) = -((2 * L - ℓ) / (4 * L ^ 2)) := by
      field_simp; ring
    have h4 : (2 * L - ℓ) / (4 * L ^ 2) ≤ (2 * L + ℓ) / (4 * L ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  · have h1 : (aThr p δ : ℝ) ^ 2 * ℓ / L ^ 2 ≤ (L + ℓ) ^ 2 / (4 * ℓ) / L ^ 2 :=
      div_le_div_of_nonneg_right hhi hL2.le
    have e1 : (L + ℓ) ^ 2 / (4 * ℓ) / L ^ 2 - 1 / (4 * ℓ) = (2 * L + ℓ) / (4 * L ^ 2) := by
      field_simp; ring
    linarith

#print axioms block_combine
#print axioms affine_target_size
#print axioms aS_sq_sub_four_cS
#print axioms xS_lt_aS_sq
#print axioms order_singleton_limit

end TVGPlus
end LeanCheck
