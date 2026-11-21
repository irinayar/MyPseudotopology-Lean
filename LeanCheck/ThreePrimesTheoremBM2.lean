import LeanCheck.ThreePrimesTheoremB
import LeanCheck.ThreePrimesStrictM2

/-!
# ThreePrimes (version M2): Theorem B with `m δ ≥ 1`

Variant of `ThreePrimesTheoremB.lean` with the hypothesis `1 < m δ` (for example `m = ⌊1/δ⌋ + 1`) instead of
`2 ≤ m δ`. Only the last step of the proof changes: all coordinates of the chain are `≤ 1/m < δ`. The
definitions `sumA, sumAlpha, sumDelta, discQ, tstar, Mstar` and the lemmas `pigeonhole_box_mul`, `logb_D`,
`quad_step`, `discQ_nonneg`, `size_B` of `ThreePrimesTheoremB` are reused unchanged (`size_B` does not involve `m`).
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- **Theorem B, sufficient-condition form.** -/
theorem explicit_upper_multM2 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (m h M : ℕ) (a : ℕ → ℕ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : m ≤ 2 ^ h)
    (hcond : (h : ℝ) * (Real.sqrt ((∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ)) + M + h) *
        (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ)) ≤ M) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ ((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℤ) * ((2 ^ M : ℕ) : ℤ) ∧
      (((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℤ) ∣ k) ∧ InBall S δ k := by
  classical
  set D : ℕ := ∏ p ∈ S, p ^ (a p ^ 2) with hDdef
  set Δ : ℝ := ∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ) with hΔ
  set Λ : ℝ := Δ + M + h with hΛ
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    have hm' : (m : ℝ) = 0 := by exact_mod_cast this
    rw [hm'] at hm
    norm_num at hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb' (hS p hp)
  have hΔ0 : 0 ≤ Δ := by
    apply Finset.sum_nonneg
    intro p hp
    have := hlb p hp
    positivity
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hDpos : 0 < D := by
    rw [hDdef]
    apply Finset.prod_pos
    intro p hp
    have := hS p hp
    positivity
  set σ : ℕ → ℝ := fun p => Real.sqrt (Λ / Real.logb 2 (p : ℝ)) with hσ
  set r : ℕ → ℕ := fun p => ⌊σ p⌋₊ with hr
  have hσa : ∀ p ∈ S, (a p : ℝ) ≤ σ p := by
    intro p hp
    have hlbp := hlb p hp
    have hlpos : 0 < Real.logb 2 (p : ℝ) := by linarith
    have h1 : (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ) ≤ Δ :=
      Finset.single_le_sum (f := fun p => (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ))
        (fun q hq => by have := hlb q hq; positivity) hp
    have h2 : (a p : ℝ) ^ 2 ≤ Λ / Real.logb 2 (p : ℝ) := by
      rw [le_div_iff₀ hlpos]
      have : Δ ≤ Λ := by
        rw [hΛ]
        linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M), (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
      linarith
    calc (a p : ℝ) = Real.sqrt ((a p : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ σ p := Real.sqrt_le_sqrt h2
  set C : Finset (ℕ × ℕ) :=
    S.biUnion (fun p => (Finset.Ioc (a p) (r p)).image (fun n => (p, n))) with hC
  have hCpos : ∀ c ∈ C, 0 < c.1 ^ (c.2 ^ 2) := by
    intro c hc
    rw [hC, Finset.mem_biUnion] at hc
    obtain ⟨p, hp, hc⟩ := hc
    rw [Finset.mem_image] at hc
    obtain ⟨n, _, rfl⟩ := hc
    have := hS p hp
    positivity
  have hcardle : (C.card : ℝ) ≤ Real.sqrt Λ * (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ)))
      - ∑ p ∈ S, (a p : ℝ) := by
    have h1 : C.card ≤ ∑ p ∈ S, (r p - a p) := by
      calc C.card ≤ ∑ p ∈ S, ((Finset.Ioc (a p) (r p)).image (fun n => (p, n))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ p ∈ S, (r p - a p) := by
            apply Finset.sum_le_sum
            intro p _
            calc ((Finset.Ioc (a p) (r p)).image (fun n => (p, n))).card
                ≤ (Finset.Ioc (a p) (r p)).card := Finset.card_image_le
              _ = r p - a p := by simp
    have h2 : ((∑ p ∈ S, (r p - a p) : ℕ) : ℝ) ≤ ∑ p ∈ S, (σ p - a p) := by
      push_cast
      apply Finset.sum_le_sum
      intro p hp
      have hle : a p ≤ r p := Nat.le_floor (hσa p hp)
      rw [Nat.cast_sub hle]
      have := Nat.floor_le (Real.sqrt_nonneg (Λ / Real.logb 2 (p : ℝ)))
      simp only [hr]
      linarith
    have h3 : ∑ p ∈ S, (σ p - a p)
        = Real.sqrt Λ * (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      rw [hσ]
      simp only
      rw [div_eq_mul_one_div, Real.sqrt_mul hΛ0]
    calc (C.card : ℝ) ≤ ((∑ p ∈ S, (r p - a p) : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ p ∈ S, (σ p - a p) := h2
      _ = _ := h3
  have hcL : h * C.card ≤ M := by
    have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    have h1 : (h : ℝ) * C.card ≤ M := by
      calc (h : ℝ) * C.card ≤ (h : ℝ) * (Real.sqrt Λ *
            (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ)) :=
            mul_le_mul_of_nonneg_left hcardle hh0
        _ ≤ M := hcond
    exact_mod_cast h1
  have hcount : m ^ C.card ≤ 2 ^ M := by
    calc m ^ C.card ≤ (2 ^ h) ^ C.card := Nat.pow_le_pow_left hmh _
      _ = 2 ^ (h * C.card) := by rw [← pow_mul]
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hcL
  obtain ⟨k, hk1, hkN, hkD, hk⟩ := pigeonhole_box_mul C hCpos m (2 ^ M) D hm1 hDpos hcount
  refine ⟨k, hk1, hkN, hkD, ?_⟩
  intro p hp
  have hp2 := hS p hp
  have hhalf : 1 / (m : ℝ) ≤ δ := by
    rw [div_le_iff₀ hm0]
    linarith
  have hlbp := hlb p hp
  have hlpos : 0 < Real.logb 2 (p : ℝ) := by linarith
  have hNpos : (0 : ℝ) < ((D * 2 ^ M : ℕ) : ℝ) := by positivity
  have hB : ((D * 2 ^ M : ℕ) : ℝ) / (((D * 2 ^ M : ℕ) : ℝ) * m + 1) < 1 / (m : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hm0]
    nlinarith
  have hfin : ∀ n : ℕ, 1 ≤ n → n ≤ r p →
      nrm ((k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) < 1 / (m : ℝ) := by
    intro n hn hnrp
    by_cases han : n ≤ a p
    · -- the coordinate divides D, hence k
      have hdvd1 : p ^ (n ^ 2) ∣ D := by
        calc p ^ (n ^ 2) ∣ p ^ (a p ^ 2) := pow_dvd_pow p (Nat.pow_le_pow_left han 2)
          _ ∣ D := Finset.dvd_prod_of_mem (fun p => p ^ (a p ^ 2)) hp
      have hdvd : ((p ^ (n ^ 2) : ℕ) : ℤ) ∣ k :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hdvd1) hkD
      obtain ⟨z, hz⟩ := hdvd
      have hqpos : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        exact_mod_cast pow_pos (by omega : 0 < p) _
      have hkz : (k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) = (z : ℝ) := by
        rw [hz]
        push_cast
        field_simp
      rw [hkz, nrm_int]
      positivity
    · push_neg at han
      have hmem : (p, n) ∈ C := by
        rw [hC, Finset.mem_biUnion]
        exact ⟨p, hp, Finset.mem_image.mpr ⟨n, Finset.mem_Ioc.mpr ⟨han, hnrp⟩, rfl⟩⟩
      exact hk (p, n) hmem
  have htail : ∀ n : ℕ, r p < n →
      nrm ((k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) ≤
        ((D * 2 ^ M : ℕ) : ℝ) / (((D * 2 ^ M : ℕ) : ℝ) * m + 1) := by
    intro n hnr
    have hlt : σ p < n := by
      have h1 := Nat.lt_floor_add_one (σ p)
      have h2 : r p + 1 ≤ n := hnr
      have h3 : ((r p + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
      push_cast at h3
      have h4 : σ p < (⌊σ p⌋₊ : ℝ) + 1 := h1
      simpa [hr] using lt_of_lt_of_le h4 h3
    have hσ0 : 0 ≤ σ p := Real.sqrt_nonneg _
    have hσsq : σ p ^ 2 = Λ / Real.logb 2 (p : ℝ) := by
      rw [hσ]; simp only
      exact Real.sq_sqrt (by positivity)
    have hn2 : Λ / Real.logb 2 (p : ℝ) < (n : ℝ) ^ 2 := by
      rw [← hσsq]
      exact pow_lt_pow_left₀ hlt hσ0 (by norm_num)
    have hn3 : Λ < (n : ℝ) ^ 2 * Real.logb 2 (p : ℝ) := by
      rw [div_lt_iff₀ hlpos] at hn2
      exact hn2
    have hDpos' : (0 : ℝ) < D := by exact_mod_cast hDpos
    have hpow : (D : ℝ) * (2 : ℝ) ^ (M + h) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have hp0 : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        exact_mod_cast pow_pos (by omega : 0 < p) _
      have h1 : Real.logb 2 (((p ^ (n ^ 2) : ℕ) : ℝ))
          ≤ Real.logb 2 ((D : ℝ) * (2 : ℝ) ^ (M + h)) :=
        Real.logb_le_logb_of_le (by norm_num) hp0 hcon
      have h2 : Real.logb 2 (((p ^ (n ^ 2) : ℕ) : ℝ)) = (n : ℝ) ^ 2 * Real.logb 2 (p : ℝ) := by
        push_cast
        rw [Real.logb_pow]
        push_cast
        ring
      have h3 : Real.logb 2 ((D : ℝ) * (2 : ℝ) ^ (M + h)) = Δ + ((M + h : ℕ) : ℝ) := by
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
          Real.logb_self_eq_one (by norm_num), hDdef, logb_D hS a]
        ring
      rw [h2, h3] at h1
      have : Λ = Δ + ((M + h : ℕ) : ℝ) := by rw [hΛ]; push_cast; ring
      linarith
    have hNm : D * 2 ^ M * m < p ^ (n ^ 2) := by
      have h5 : ((D * 2 ^ M * m : ℕ) : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        have h7 : (m : ℝ) ≤ (2 : ℝ) ^ h := by exact_mod_cast hmh
        push_cast
        calc (D : ℝ) * 2 ^ M * m ≤ (D : ℝ) * 2 ^ M * (2 : ℝ) ^ h := by gcongr
          _ = (D : ℝ) * (2 : ℝ) ^ (M + h) := by rw [pow_add]; ring
          _ < ((p : ℝ) ^ (n ^ 2)) := by exact_mod_cast hpow
      exact_mod_cast h5
    have hNm1 : ((D * 2 ^ M : ℕ) : ℝ) * m + 1 ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by
      have : D * 2 ^ M * m + 1 ≤ p ^ (n ^ 2) := hNm
      have h6 : ((D * 2 ^ M * m + 1 : ℕ) : ℝ) ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h6 ⊢
      exact h6
    have hqpos : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
      exact_mod_cast pow_pos (by omega : 0 < p) _
    refine (nrm_le_abs _).trans ?_
    rw [abs_div, abs_of_pos hqpos]
    have hkabs : |(k : ℝ)| ≤ ((D * 2 ^ M : ℕ) : ℝ) := by
      rw [abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ k))]
      have : (k : ℝ) ≤ (((D : ℤ) * ((2 ^ M : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast hkN
      push_cast at this ⊢
      exact this
    calc |(k : ℝ)| / ((p ^ (n ^ 2) : ℕ) : ℝ) ≤ ((D * 2 ^ M : ℕ) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) := by
          gcongr
      _ ≤ ((D * 2 ^ M : ℕ) : ℝ) / (((D * 2 ^ M : ℕ) : ℝ) * m + 1) := by
          gcongr
  have hlt := Pn_sq_lt p k (r p) hB hfin htail
  exact lt_of_lt_of_le hlt hhalf

#print axioms logb_D

#print axioms explicit_upper_multM2

/-- **Theorem B (closed form).** -/
theorem explicit_upper_BM2 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (m h : ℕ) (a : ℕ → ℕ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : m ≤ 2 ^ h) :
    ∃ k : ℤ, 1 ≤ k ∧
      k ≤ ((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℤ) * ((2 ^ (Mstar S a h) : ℕ) : ℤ) ∧
      (((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℤ) ∣ k) ∧ InBall S δ k := by
  have hQ := discQ_nonneg hS hne a h
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb' (hS p hp)
  have hA0 : 0 ≤ sumA S := Finset.sum_nonneg (fun p _ => Real.sqrt_nonneg _)
  have hΔ0 : 0 ≤ sumDelta S a := by
    apply Finset.sum_nonneg
    intro p hp
    have := hlb p hp
    positivity
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  apply explicit_upper_multM2 hS hδ m h (Mstar S a h) a hm hmh
  set M := Mstar S a h with hMdef
  set t := tstar S a h with ht
  have ht0 : 0 ≤ t := by
    rw [ht]; unfold tstar
    have := Real.sqrt_nonneg (discQ S a h)
    positivity
  have hM : t ^ 2 - h - sumDelta S a ≤ M := Nat.le_ceil _
  have hΛ : t ^ 2 ≤ sumDelta S a + M + h := by linarith
  have hΛ0 : 0 ≤ sumDelta S a + M + h := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hx : t ≤ Real.sqrt (sumDelta S a + M + h) := by
    calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht0).symm
      _ ≤ _ := Real.sqrt_le_sqrt hΛ
  have hxsq : Real.sqrt (sumDelta S a + M + h) ^ 2 = sumDelta S a + M + h := Real.sq_sqrt hΛ0
  have hq := quad_step (A := sumA S) (α := sumAlpha S a) (Δ := sumDelta S a) (h := (h : ℝ)) hh0 hA0 hQ
    (x := Real.sqrt (sumDelta S a + M + h)) hx
  have hqq : (h : ℝ) * (sumA S * Real.sqrt (sumDelta S a + M + h) - sumAlpha S a)
      ≤ Real.sqrt (sumDelta S a + M + h) ^ 2 - h - sumDelta S a := hq
  rw [hxsq] at hqq
  unfold sumA sumAlpha sumDelta at hqq
  have e : (h : ℝ) * (Real.sqrt ((∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ)) + M + h) *
        (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ))
      = (h : ℝ) * ((∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) *
        Real.sqrt ((∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ)) + M + h) - ∑ p ∈ S, (a p : ℝ)) := by
    ring
  rw [e]
  linarith

/-- Two-sided form of Theorem B with the forced exponents `a_p = a_p(δ)`:
`D_S(δ) ≤ k ≤ D_S(δ) 2^M`. -/
theorem explicit_bounds_BM2 {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (m h : ℕ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : m ≤ 2 ^ h) :
    ∃ k : ℤ, 1 ≤ k ∧ (Dvis S δ : ℤ) ≤ k ∧
      k ≤ (Dvis S δ : ℤ) * ((2 ^ (Mstar S (fun p => aThr p δ) h) : ℕ) : ℤ) ∧ InBall S δ k := by
  obtain ⟨k, hk1, hkN, hkD, hk⟩ :=
    explicit_upper_BM2 (fun p hp => (hS p hp).two_le) hne hδ m h (fun p => aThr p δ) hm hmh
  exact ⟨k, hk1, Int.le_of_dvd (by omega) hkD, hkN, hk⟩

#print axioms explicit_upper_BM2
#print axioms explicit_bounds_BM2

end TVGPlus
end LeanCheck
