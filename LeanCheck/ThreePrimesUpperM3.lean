import LeanCheck.ThreePrimesUpper
import LeanCheck.ThreePrimesStrictM2

/-!
# ThreePrimes (version M3): the pigeonhole upper bound with `m δ ≥ 1` and a real `η`

Variant of `ThreePrimesUpperM2.lean` in which the natural number `h` (with `m ≤ 2^h`, `1 ≤ h`) is replaced by a
real number `η` with `(m : ℝ) ≤ 2^η` and `1 ≤ η` (for example `η = log₂ m`, `m = ⌈1/δ⌉`). The counting step
`m^|C| ≤ 2^(η |C|) ≤ 2^L` and the cut-off `p^(n²) ≤ N m ≤ 2^(L+η)` are done with `Real.rpow` and `Real.logb`;
the last step (strict supremum bound `P_p(k) < 1/m ≤ δ` by `Pn_sq_lt`) is unchanged. The lemmas `tight_ineq`
(already stated for a real `h`) and `one_le_logb` of `ThreePrimesUpper` are reused. The declarations have the
suffix `M3`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- **Tightened explicit upper bound.** -/
theorem explicit_upper_tightM3 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (m L : ℕ) (η : ℝ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 1 ≤ η)
    {a : ℝ} (ha : 1 ≤ a) (hg : (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) ^ 2 ≤ a)
    (hL : a * η ^ 2 + a * η ≤ L) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ ((2 ^ L : ℕ) : ℤ) ∧ InBall S δ k := by
  classical
  set N : ℕ := 2 ^ L with hN
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    have hm' : (m : ℝ) = 0 := by exact_mod_cast this
    rw [hm'] at hm
    norm_num at hm
  have hm0: (0 : ℝ) < m := by exact_mod_cast hm1
  -- the per-prime cut-off
  set σ : ℕ → ℝ := fun p => Real.sqrt (((L : ℝ) + η) / Real.logb 2 (p : ℝ)) with hσ
  set r : ℕ → ℕ := fun p => ⌊σ p⌋₊ with hr
  set C : Finset (ℕ × ℕ) := S.biUnion (fun p => (Finset.Icc 1 (r p)).image (fun n => (p, n))) with hC
  have hCpos : ∀ c ∈ C, 0 < c.1 ^ (c.2 ^ 2) := by
    intro c hc
    rw [hC, Finset.mem_biUnion] at hc
    obtain ⟨p, hp, hc⟩ := hc
    rw [Finset.mem_image] at hc
    obtain ⟨n, _, rfl⟩ := hc
    have := hS p hp
    positivity
  -- cardinality
  have hcardle : (C.card : ℝ) ≤ Real.sqrt ((L : ℝ) + η) *
      ∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ)) := by
    have h1 : C.card ≤ ∑ p ∈ S, r p := by
      calc C.card ≤ ∑ p ∈ S, ((Finset.Icc 1 (r p)).image (fun n => (p, n))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ p ∈ S, r p := by
            apply Finset.sum_le_sum
            intro p _
            calc ((Finset.Icc 1 (r p)).image (fun n => (p, n))).card
                ≤ (Finset.Icc 1 (r p)).card := Finset.card_image_le
              _ = r p := by simp
    have h2 : ((∑ p ∈ S, r p : ℕ) : ℝ) ≤ ∑ p ∈ S, σ p := by
      push_cast
      apply Finset.sum_le_sum
      intro p _
      exact Nat.floor_le (Real.sqrt_nonneg _)
    have h3 : ∑ p ∈ S, σ p
        = Real.sqrt ((L : ℝ) + η) * ∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [hσ]
      simp only
      rw [div_eq_mul_one_div, Real.sqrt_mul (by positivity)]
    calc (C.card : ℝ) ≤ ((∑ p ∈ S, r p : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ p ∈ S, σ p := h2
      _ = _ := h3
  -- the counting condition η * |C| ≤ L (real η)
  have hcL : η * C.card ≤ (L : ℝ) := by
    have hh1 : (1 : ℝ) ≤ η := hη
    have hL0 : (0 : ℝ) ≤ L := by
      have : (0 : ℝ) ≤ a * η ^ 2 + a * η := by positivity
      linarith
    have hineq := tight_ineq ha hh1 hL
    set g := ∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ)) with hgdef
    have hg0 : 0 ≤ g := Finset.sum_nonneg (fun p _ => Real.sqrt_nonneg _)
    have hsq : ((C.card : ℝ)) ^ 2 ≤ ((L : ℝ) + η) * g ^ 2 := by
      have h0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
      have := pow_le_pow_left₀ h0 hcardle 2
      rw [mul_pow, Real.sq_sqrt (by positivity)] at this
      exact this
    have hfin : (η * C.card) ^ 2 ≤ (L : ℝ) ^ 2 := by
      calc (η * C.card) ^ 2 = η ^ 2 * (C.card : ℝ) ^ 2 := by ring
        _ ≤ η ^ 2 * (((L : ℝ) + η) * g ^ 2) := by gcongr
        _ ≤ η ^ 2 * (((L : ℝ) + η) * a) := by gcongr
        _ = a * η ^ 2 * ((L : ℝ) + η) := by ring
        _ ≤ (L : ℝ) ^ 2 := hineq
    by_contra hcon
    push_neg at hcon
    nlinarith [hcon, hL0]
  have hcount : m ^ C.card ≤ N := by
    have hR : (m : ℝ) ^ C.card ≤ (N : ℝ) := by
      calc (m : ℝ) ^ C.card ≤ ((2 : ℝ) ^ η) ^ C.card := pow_le_pow_left₀ hm0.le hmh _
        _ = (2 : ℝ) ^ (η * C.card) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        _ ≤ (2 : ℝ) ^ (L : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hcL
        _ = (N : ℝ) := by rw [Real.rpow_natCast, hN]; push_cast; rfl
    exact_mod_cast hR
  obtain ⟨k, hk1, hkN, hk⟩ := pigeonhole_box C hCpos m N hm1 hcount
  refine ⟨k, hk1, by exact_mod_cast hkN, ?_⟩
  intro p hp
  have hp2 := hS p hp
  have hhalf : 1 / (m : ℝ) ≤ δ := by
    rw [div_le_iff₀ hm0]
    linarith
  have hlb1 : 1 ≤ Real.logb 2 (p : ℝ) := one_le_logb hp2
  have hlbpos : 0 < Real.logb 2 (p : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by rw [hN]; positivity
    exact_mod_cast this
  have hB : (N : ℝ) / ((N : ℝ) * m + 1) < 1 / (m : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hm0]
    nlinarith
  have hfin : ∀ n : ℕ, 1 ≤ n → n ≤ r p →
      nrm ((k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) < 1 / (m : ℝ) := by
    intro n hn hnrp
    have hmem : (p, n) ∈ C := by
      rw [hC, Finset.mem_biUnion]
      exact ⟨p, hp, Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr ⟨hn, hnrp⟩, rfl⟩⟩
    exact hk (p, n) hmem
  have htail : ∀ n : ℕ, r p < n →
      nrm ((k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) ≤ (N : ℝ) / ((N : ℝ) * m + 1) := by
    intro n hnr
    have hlt : σ p < n := by
      have := Nat.lt_floor_add_one (σ p)
      have h2 : r p + 1 ≤ n := hnr
      have h3 : ((r p + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
      push_cast at h3
      have h4 : σ p < (⌊σ p⌋₊ : ℝ) + 1 := this
      simpa [hr] using lt_of_lt_of_le h4 h3
    have hσ0 : 0 ≤ σ p := Real.sqrt_nonneg _
    have hσsq : σ p ^ 2 = ((L : ℝ) + η) / Real.logb 2 (p : ℝ) := by
      rw [hσ]; simp only
      exact Real.sq_sqrt (by positivity)
    have hn2 : ((L : ℝ) + η) / Real.logb 2 (p : ℝ) < (n : ℝ) ^ 2 := by
      rw [← hσsq]
      exact pow_lt_pow_left₀ hlt hσ0 (by norm_num)
    have hn3 : (L : ℝ)+ η < (n : ℝ) ^ 2 * Real.logb 2 (p : ℝ) := by
      rw [div_lt_iff₀ hlbpos] at hn2
      exact hn2
    have hpow : (2 : ℝ) ^ ((L : ℝ) + η) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have hp0 : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        exact_mod_cast pow_pos (by omega : 0 < p) _
      have h1 : Real.logb 2 (((p ^ (n ^ 2) : ℕ) : ℝ)) ≤ Real.logb 2 ((2 : ℝ) ^ ((L : ℝ) + η)) :=
        Real.logb_le_logb_of_le (by norm_num) hp0 hcon
      have h2 : Real.logb 2 (((p ^ (n ^ 2) : ℕ) : ℝ)) = (n : ℝ) ^ 2 * Real.logb 2 (p : ℝ) := by
        push_cast
        rw [Real.logb_pow]
        push_cast
        ring
      have h3 : Real.logb 2 ((2 : ℝ) ^ ((L : ℝ) + η)) = (L : ℝ) + η := by
        rw [Real.logb_rpow (by norm_num) (by norm_num)]
      rw [h2, h3] at h1
      linarith
    have hNm : N * m < p ^ (n ^ 2) := by
      have h5 : (N * m : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        have h6 : (N : ℝ) * m ≤ (2 : ℝ) ^ ((L : ℝ) + η) := by
          calc (N : ℝ) * m ≤ (N : ℝ) * (2 : ℝ) ^ η := by gcongr
            _ = (2 : ℝ) ^ ((L : ℝ) + η) := by
                rw [Real.rpow_add (by norm_num), Real.rpow_natCast, hN]; push_cast; rfl
        exact h6.trans_lt hpow
      exact_mod_cast h5
    have hNm1 : (N : ℝ) * m + 1 ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by
      have : N * m + 1 ≤ p ^ (n ^ 2) := hNm
      have h6 : ((N * m + 1 : ℕ) : ℝ) ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h6 ⊢
      exact h6
    have hqpos : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
      exact_mod_cast pow_pos (by omega : 0 < p) _
    refine (nrm_le_abs _).trans ?_
    rw [abs_div, abs_of_pos hqpos]
    have hkabs : |(k : ℝ)| ≤ N := by
      rw [abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ k))]
      exact_mod_cast hkN
    calc |(k : ℝ)| / ((p ^ (n ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) := by
          gcongr
      _ ≤ (N : ℝ) / ((N : ℝ) * m + 1) := by
          gcongr
  have hlt := Pn_sq_lt p k (r p) hB hfin htail
  exact lt_of_lt_of_le hlt hhalf


/-- The article statement: `a_S = max(1, g_S^2)`, `L = ⌈a_S h^2 + a_S h⌉`. -/
theorem explicit_upper_tight_ceilM3 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (m : ℕ) (η : ℝ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 1 ≤ η) :
    ∃ k : ℤ, 1 ≤ k ∧
      k ≤ ((2 ^ ⌈max 1 ((∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) ^ 2) * η ^ 2
          + max 1 ((∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) ^ 2) * η⌉₊ : ℕ) : ℤ) ∧
      InBall S δ k :=
  explicit_upper_tightM3 hS hδ m _ η hm hmh hη (le_max_left _ _) (le_max_right _ _) (Nat.le_ceil _)

/-- Two-sided form with the universal divisor `D_S(δ)`. -/
theorem explicit_bounds_tightM3 {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {δ : ℝ} (hδ : 0 < δ)
    (m : ℕ) (η : ℝ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 1 ≤ η) :
    ∃ k : ℤ, 1 ≤ k ∧ (Dvis S δ : ℤ) ≤ k ∧
      k ≤ ((2 ^ ⌈max 1 ((∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) ^ 2) * η ^ 2
          + max 1 ((∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) ^ 2) * η⌉₊ : ℕ) : ℤ) ∧
      InBall S δ k := by
  obtain ⟨k, hk1, hkN, hk⟩ := explicit_upper_tight_ceilM3 (fun p hp => (hS p hp).two_le) hδ m η hm hmh hη
  exact ⟨k, hk1, Int.le_of_dvd (by omega) (forced hS hδ hk), hkN, hk⟩


#print axioms explicit_upper_tight_ceilM3
#print axioms explicit_bounds_tightM3

end TVGPlus
end LeanCheck
