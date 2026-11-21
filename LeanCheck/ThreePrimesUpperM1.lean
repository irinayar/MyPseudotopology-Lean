import LeanCheck.ThreePrimesUpper

/-!
# ThreePrimes (version M1): the pigeonhole upper bound with `m δ > 1`

Variant of `ThreePrimesUpper.lean` in which the hypothesis `2 ≤ m δ` is replaced by `1 < m δ`
(for example `m = ⌊1/δ⌋ + 1`; for `δ = 1/k` one may take `m = k + 1`). The proof is the same except for the
last step: every coordinate of the chain is `≤ 1/m < δ` (retained coordinates `< 1/m`, omitted coordinates
`≤ k/q ≤ 1/m`), so no factor `δ/2` is needed. The declarations have the suffix `M1`; the lemmas
`tight_ineq`, `one_le_logb`, `tight_le_old` of `ThreePrimesUpper` are reused unchanged.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- **Tightened explicit upper bound.** -/
theorem explicit_upper_tightM1 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (m h L : ℕ) (hm : 1 < (m : ℝ) * δ) (hmh : m ≤ 2 ^ h) (hh : 1 ≤ h)
    {a : ℝ} (ha : 1 ≤ a) (hg : (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) ^ 2 ≤ a)
    (hL : a * (h : ℝ) ^ 2 + a * h ≤ L) :
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
  set σ : ℕ → ℝ := fun p => Real.sqrt (((L : ℝ) + h) / Real.logb 2 (p : ℝ)) with hσ
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
  have hcardle : (C.card : ℝ) ≤ Real.sqrt ((L : ℝ) + h) *
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
        = Real.sqrt ((L : ℝ) + h) * ∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [hσ]
      simp only
      rw [div_eq_mul_one_div, Real.sqrt_mul (by positivity)]
    calc (C.card : ℝ) ≤ ((∑ p ∈ S, r p : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ p ∈ S, σ p := h2
      _ = _ := h3
  -- the counting condition h * |C| ≤ L
  have hcL : h * C.card ≤ L := by
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hL0 : (0 : ℝ) ≤ L := by
      have : (0 : ℝ) ≤ a * (h : ℝ) ^ 2 + a * h := by positivity
      linarith
    have hineq := tight_ineq ha hh1 hL
    set g := ∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ)) with hgdef
    have hg0 : 0 ≤ g := Finset.sum_nonneg (fun p _ => Real.sqrt_nonneg _)
    have hsq : ((C.card : ℝ)) ^ 2 ≤ ((L : ℝ) + h) * g ^ 2 := by
      have h0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
      have := pow_le_pow_left₀ h0 hcardle 2
      rw [mul_pow, Real.sq_sqrt (by positivity)] at this
      exact this
    have hfin : ((h : ℝ) * C.card) ^ 2 ≤ (L : ℝ) ^ 2 := by
      calc ((h : ℝ) * C.card) ^ 2 = (h : ℝ) ^ 2 * (C.card : ℝ) ^ 2 := by ring
        _ ≤ (h : ℝ) ^ 2 * (((L : ℝ) + h) * g ^ 2) := by gcongr
        _ ≤ (h : ℝ) ^ 2 * (((L : ℝ) + h) * a) := by gcongr
        _ = a * (h : ℝ) ^ 2 * ((L : ℝ) + h) := by ring
        _ ≤ (L : ℝ) ^ 2 := hineq
    have : (h : ℝ) * C.card ≤ L := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hcon, hL0]
    exact_mod_cast this
  have hcount : m ^ C.card ≤ N := by
    calc m ^ C.card ≤ (2 ^ h) ^ C.card := Nat.pow_le_pow_left hmh _
      _ = 2 ^ (h * C.card) := by rw [← pow_mul]
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hcL
  obtain ⟨k, hk1, hkN, hk⟩ := pigeonhole_box C hCpos m N hm1 hcount
  refine ⟨k, hk1, by exact_mod_cast hkN, ?_⟩
  intro p hp
  have hp2 := hS p hp
  have hhalf : 1 / (m : ℝ) < δ := by
    rw [div_lt_iff₀ hm0]
    linarith
  have hlb1 : 1 ≤ Real.logb 2 (p : ℝ) := one_le_logb hp2
  have hlbpos : 0 < Real.logb 2 (p : ℝ) := by linarith
  have hbound : Pn (sqScales p) k ≤ 1 / (m : ℝ) := by
    apply Pn_le (sq_nonempty p)
    rintro q ⟨n, hn, rfl⟩
    by_cases hnr : n ≤ r p
    · have hmem : (p, n) ∈ C := by
        rw [hC, Finset.mem_biUnion]
        exact ⟨p, hp, Finset.mem_image.mpr ⟨n, Finset.mem_Icc.mpr ⟨hn, hnr⟩, rfl⟩⟩
      exact (hk (p, n) hmem).le
    · push_neg at hnr
      -- n > σ p, hence n^2 * logb 2 p > L + h, hence p^(n^2) > 2^(L+h) ≥ N * m
      have hlt : σ p < n := by
        have := Nat.lt_floor_add_one (σ p)
        have h2 : r p + 1 ≤ n := hnr
        have h3 : ((r p + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
        push_cast at h3
        have h4 : σ p < (⌊σ p⌋₊ : ℝ) + 1 := this
        simpa [hr] using lt_of_lt_of_le h4 h3
      have hσ0 : 0 ≤ σ p := Real.sqrt_nonneg _
      have hσsq : σ p ^ 2 = ((L : ℝ) + h) / Real.logb 2 (p : ℝ) := by
        rw [hσ]; simp only
        exact Real.sq_sqrt (by positivity)
      have hn2 : ((L : ℝ) + h) / Real.logb 2 (p : ℝ) < (n : ℝ) ^ 2 := by
        rw [← hσsq]
        exact pow_lt_pow_left₀ hlt hσ0 (by norm_num)
      have hn3 : (L : ℝ) + h < (n : ℝ) ^ 2 * Real.logb 2 (p : ℝ) := by
        rw [div_lt_iff₀ hlbpos] at hn2
        exact hn2
      have hpow : (2 : ℝ) ^ (L + h) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        by_contra hcon
        push_neg at hcon
        have hp0 : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
          exact_mod_cast pow_pos (by omega : 0 < p) _
        have h1 : Real.logb 2 (((p ^ (n ^ 2) : ℕ) : ℝ)) ≤ Real.logb 2 ((2 : ℝ) ^ (L + h)) :=
          Real.logb_le_logb_of_le (by norm_num) hp0 hcon
        have h2 : Real.logb 2 (((p ^ (n ^ 2) : ℕ) : ℝ)) = (n : ℝ) ^ 2 * Real.logb 2 (p : ℝ) := by
          push_cast
          rw [Real.logb_pow]
          push_cast
          ring
        have h3 : Real.logb 2 ((2 : ℝ) ^ (L + h)) = ((L + h : ℕ) : ℝ) := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          simp
        rw [h2, h3] at h1
        push_cast at h1
        linarith
      have hNm : N * m ≤ p ^ (n ^ 2) := by
        have h5 : (N * m : ℝ) ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by
          have h6 : (N : ℝ) * m ≤ (2 : ℝ) ^ (L + h) := by
            have h7 : (m : ℝ) ≤ (2 : ℝ) ^ h := by exact_mod_cast hmh
            calc (N : ℝ) * m ≤ (N : ℝ) * (2 : ℝ) ^ h := by gcongr
              _ = (2 : ℝ) ^ (L + h) := by rw [hN]; push_cast; rw [pow_add]
          exact h6.trans hpow.le
        exact_mod_cast h5
      have hqpos : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        exact_mod_cast pow_pos (by omega : 0 < p) _
      refine (nrm_le_abs _).trans ?_
      rw [abs_div, abs_of_pos hqpos, div_le_iff₀ hqpos]
      have hkabs : |(k : ℝ)| ≤ N := by
        rw [abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ k))]
        exact_mod_cast hkN
      have hNmR : (N : ℝ) * m ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by exact_mod_cast hNm
      have hN0 : (0 : ℝ) ≤ N := by positivity
      calc |(k : ℝ)| ≤ N := hkabs
        _ = ((N : ℝ) * m) * (1 / (m : ℝ)) := by field_simp
        _ ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) * (1 / (m : ℝ)) := by gcongr
        _ = 1 / (m : ℝ) * ((p ^ (n ^ 2) : ℕ) : ℝ) := by ring
  linarith


/-- The article statement: `a_S = max(1, g_S^2)`, `L = ⌈a_S h^2 + a_S h⌉`. -/
theorem explicit_upper_tight_ceilM1 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (m h : ℕ) (hm : 1 < (m : ℝ) * δ) (hmh : m ≤ 2 ^ h) (hh : 1 ≤ h) :
    ∃ k : ℤ, 1 ≤ k ∧
      k ≤ ((2 ^ ⌈max 1 ((∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) ^ 2) * (h : ℝ) ^ 2
          + max 1 ((∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) ^ 2) * h⌉₊ : ℕ) : ℤ) ∧
      InBall S δ k :=
  explicit_upper_tightM1 hS hδ m h _ hm hmh hh (le_max_left _ _) (le_max_right _ _) (Nat.le_ceil _)

/-- Two-sided form with the universal divisor `D_S(δ)`. -/
theorem explicit_bounds_tightM1 {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {δ : ℝ} (hδ : 0 < δ)
    (m h : ℕ) (hm : 1 < (m : ℝ) * δ) (hmh : m ≤ 2 ^ h) (hh : 1 ≤ h) :
    ∃ k : ℤ, 1 ≤ k ∧ (Dvis S δ : ℤ) ≤ k ∧
      k ≤ ((2 ^ ⌈max 1 ((∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) ^ 2) * (h : ℝ) ^ 2
          + max 1 ((∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) ^ 2) * h⌉₊ : ℕ) : ℤ) ∧
      InBall S δ k := by
  obtain ⟨k, hk1, hkN, hk⟩ := explicit_upper_tight_ceilM1 (fun p hp => (hS p hp).two_le) hδ m h hm hmh hh
  exact ⟨k, hk1, Int.le_of_dvd (by omega) (forced hS hδ hk), hkN, hk⟩


#print axioms explicit_upper_tight_ceilM1
#print axioms explicit_bounds_tightM1

end TVGPlus
end LeanCheck
