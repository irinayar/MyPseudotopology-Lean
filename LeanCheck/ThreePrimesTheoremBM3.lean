import LeanCheck.ThreePrimesTheoremB
import LeanCheck.ThreePrimesStrictM2

/-!
# ThreePrimes (version M3): Theorem B with a real `η` and `m δ ≥ 1`

Variant of `ThreePrimesTheoremBM2.lean` in which the natural number `h` (with `m ≤ 2^h`) is replaced by a
real number `η` with `m ≤ 2^η` (for example `η = log₂ m`). The definitions `discQR`, `tstarR`, `MstarR`
and the lemmas `discQR_nonneg`, `size_BR` are the real-`η` versions of `discQ`, `tstar`, `Mstar`,
`discQ_nonneg`, `size_B` of `ThreePrimesTheoremB`; the lemmas `quad_step`, `pigeonhole_box_mul`, `logb_D`,
`Pn_sq_lt` are reused unchanged.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- The discriminant `Q = η² A² − 4 (η α − Δ − η)`. -/
noncomputable def discQR (S : Finset ℕ) (a : ℕ → ℕ) (η : ℝ) : ℝ :=
  η ^ 2 * (sumA S) ^ 2 - 4 * (η * sumAlpha S a - sumDelta S a - η)
/-- `t* = (hA + √Q)/2`. -/
noncomputable def tstarR (S : Finset ℕ) (a : ℕ → ℕ) (η : ℝ) : ℝ :=
  (η * sumA S + Real.sqrt (discQR S a η)) / 2
/-- `M = ⌈t*² − η − Δ⌉` (zero if that is not positive). -/
noncomputable def MstarR (S : Finset ℕ) (a : ℕ → ℕ) (η : ℝ) : ℕ :=
  ⌈(tstarR S a η) ^ 2 - η - sumDelta S a⌉₊

/-- The discriminant is nonnegative (Cauchy–Schwarz). -/
lemma discQR_nonneg {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) (a : ℕ → ℕ) (η : ℝ) (hη : 0 ≤ η) :
    0 ≤ discQR S a η := by
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb' (hS p hp)
  set g : ℕ → ℝ := fun p => Real.sqrt (1 / Real.logb 2 (p : ℝ)) with hg
  set f : ℕ → ℝ := fun p => (a p : ℝ) * Real.sqrt (Real.logb 2 (p : ℝ)) with hf
  have hfg : ∀ p ∈ S, f p * g p = (a p : ℝ) := by
    intro p hp
    have hl := hlb p hp
    have hpos : 0 < Real.logb 2 (p : ℝ) := by linarith
    have : Real.sqrt (Real.logb 2 (p : ℝ)) * Real.sqrt (1 / Real.logb 2 (p : ℝ)) = 1 := by
      rw [← Real.sqrt_mul hpos.le, mul_one_div_cancel hpos.ne', Real.sqrt_one]
    simp only [hf, hg]
    calc (a p : ℝ) * Real.sqrt (Real.logb 2 (p : ℝ)) * Real.sqrt (1 / Real.logb 2 (p : ℝ))
        = (a p : ℝ) * (Real.sqrt (Real.logb 2 (p : ℝ)) * Real.sqrt (1 / Real.logb 2 (p : ℝ))) := by ring
      _ = a p := by rw [this]; ring
  have hf2 : ∀ p ∈ S, f p ^ 2 = (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ) := by
    intro p hp
    have hl := hlb p hp
    have hpos : 0 < Real.logb 2 (p : ℝ) := by linarith
    simp only [hf]
    rw [mul_pow, Real.sq_sqrt hpos.le]
  have hg2 : ∀ p ∈ S, g p ^ 2 = 1 / Real.logb 2 (p : ℝ) := by
    intro p hp
    have hl := hlb p hp
    have hpos : 0 < Real.logb 2 (p : ℝ) := by linarith
    simp only [hg]
    exact Real.sq_sqrt (by positivity)
  have hg0 : ∀ p ∈ S, 0 ≤ g p := fun p _ => Real.sqrt_nonneg _
  have CS := Finset.sum_mul_sq_le_sq_mul_sq S f g
  have e1 : ∑ p ∈ S, f p * g p = sumAlpha S a := by
    unfold sumAlpha; exact Finset.sum_congr rfl hfg
  have e2 : ∑ p ∈ S, f p ^ 2 = sumDelta S a := by
    unfold sumDelta; exact Finset.sum_congr rfl hf2
  set C0 : ℝ := ∑ p ∈ S, 1 / Real.logb 2 (p : ℝ) with hC0
  have e3 : ∑ p ∈ S, g p ^ 2 = C0 := Finset.sum_congr rfl hg2
  have e4 : ∑ p ∈ S, g p = sumA S := rfl
  rw [e1, e2, e3] at CS
  have hAC : C0 ≤ (sumA S) ^ 2 := by
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := S) (f := g) hg0
    rw [e3, e4] at this
    exact this
  have hC0pos : 0 < C0 := by
    apply Finset.sum_pos _ hne
    intro p hp
    have hl := hlb p hp
    have hpos : 0 < Real.logb 2 (p : ℝ) := by linarith
    positivity
  have hh0 : (0 : ℝ) ≤ η := hη
  unfold discQR
  set A := sumA S
  set α := sumAlpha S a
  set Δ := sumDelta S a
  have k1 : η ^ 2 * C0 * C0 ≤ η ^ 2 * C0 * A ^ 2 :=
    mul_le_mul_of_nonneg_left hAC (by positivity)
  have k2 : (η * C0 - 2 * α) ^ 2 ≥ 0 := sq_nonneg _
  have k3 : 0 ≤ η * C0 := by positivity
  by_contra hneg
  push_neg at hneg
  have : C0 * (η ^ 2 * A ^ 2 - 4 * (η * α - Δ - η)) < 0 :=
    mul_neg_of_pos_of_neg hC0pos hneg
  nlinarith [k1, k2, k3, CS]



/-- The size of the bound: `D 2^M ≤ max (D, 2^(t*² − η + 1))`. -/
theorem size_BR {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (η : ℝ) :
    (((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) * 2 ^ (MstarR S a η) : ℕ) : ℝ)
      ≤ max (((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℕ) : ℝ)
          ((2 : ℝ) ^ ((tstarR S a η) ^ 2 - η + 1)) := by
  set D : ℕ := ∏ p ∈ S, p ^ (a p ^ 2) with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    apply Finset.prod_pos
    intro p hp
    have := hS p hp
    positivity
  have hDpos' : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hDrp : (D : ℝ) = (2 : ℝ) ^ (sumDelta S a) := by
    have h1 := Real.rpow_logb (b := 2) (x := (D : ℝ)) (by norm_num) (by norm_num) hDpos'
    have h2 : Real.logb 2 (D : ℝ) = sumDelta S a := by
      unfold sumDelta
      exact logb_D hS a
    rw [h2] at h1
    exact h1.symm
  by_cases hx : 0 ≤ (tstarR S a η) ^ 2 - η - sumDelta S a
  · have hlt : ((MstarR S a η : ℕ) : ℝ) < (tstarR S a η) ^ 2 - η - sumDelta S a + 1 :=
      Nat.ceil_lt_add_one hx
    have h2M : (2 : ℝ) ^ (MstarR S a η) ≤ (2 : ℝ) ^ ((tstarR S a η) ^ 2 - η - sumDelta S a + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlt.le
    push_cast
    calc (D : ℝ) * (2 : ℝ) ^ (MstarR S a η)
        ≤ (2 : ℝ) ^ (sumDelta S a) * (2 : ℝ) ^ ((tstarR S a η) ^ 2 - η - sumDelta S a + 1) := by
          rw [hDrp]
          gcongr
      _ = (2 : ℝ) ^ ((tstarR S a η) ^ 2 - η + 1) := by
          rw [← Real.rpow_add (by norm_num)]
          congr 1
          ring
      _ ≤ _ := le_max_right _ _
  · have hM0 : MstarR S a η = 0 := by
      unfold MstarR
      apply Nat.ceil_eq_zero.mpr
      linarith [not_le.mp hx]
    rw [hM0]
    push_cast
    simp


/-- **Theorem B, sufficient-condition form.** -/
theorem explicit_upper_multM3 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (m M : ℕ) (η : ℝ) (a : ℕ → ℕ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 0 ≤ η)
    (hcond : η * (Real.sqrt ((∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ)) + M + η) *
        (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ)) ≤ M) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ ((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℤ) * ((2 ^ M : ℕ) : ℤ) ∧
      (((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℤ) ∣ k) ∧ InBall S δ k := by
  classical
  set D : ℕ := ∏ p ∈ S, p ^ (a p ^ 2) with hDdef
  set Δ : ℝ := ∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ) with hΔ
  set Λ : ℝ := Δ + M + η with hΛ
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
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; have := (Nat.cast_nonneg M : (0 : ℝ) ≤ M); linarith
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
        linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M), hη]
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
  have hcL : η * C.card ≤ (M : ℝ) := by
    have hh0 : (0 : ℝ) ≤ η := hη
    calc η * C.card ≤ η * (Real.sqrt Λ *
          (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ)) :=
          mul_le_mul_of_nonneg_left hcardle hh0
      _ ≤ M := hcond
  have hcount : m ^ C.card ≤ 2 ^ M := by
    have hR : (m : ℝ) ^ C.card ≤ ((2 ^ M : ℕ) : ℝ) := by
      calc (m : ℝ) ^ C.card ≤ ((2 : ℝ) ^ η) ^ C.card := pow_le_pow_left₀ hm0.le hmh _
        _ = (2 : ℝ) ^ (η * C.card) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        _ ≤ (2 : ℝ) ^ (M : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hcL
        _ = ((2 ^ M : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
    exact_mod_cast hR
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
    have hpow : (D : ℝ) * (2 : ℝ) ^ ((M : ℝ) + η) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have hp0 : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        exact_mod_cast pow_pos (by omega : 0 < p) _
      have h1 : Real.logb 2 (((p ^ (n ^ 2) : ℕ) : ℝ))
          ≤ Real.logb 2 ((D : ℝ) * (2 : ℝ) ^ ((M : ℝ) + η)) :=
        Real.logb_le_logb_of_le (by norm_num) hp0 hcon
      have h2 : Real.logb 2 (((p ^ (n ^ 2) : ℕ) : ℝ)) = (n : ℝ) ^ 2 * Real.logb 2 (p : ℝ) := by
        push_cast
        rw [Real.logb_pow]
        push_cast
        ring
      have h3 : Real.logb 2 ((D : ℝ) * (2 : ℝ) ^ ((M : ℝ) + η)) = Δ + ((M : ℝ) + η) := by
        rw [Real.logb_mul (by positivity) (by positivity),
          Real.logb_rpow (by norm_num) (by norm_num), hDdef, logb_D hS a]
      rw [h2, h3] at h1
      have : Λ = Δ + ((M : ℝ) + η) := by rw [hΛ]; ring
      linarith
    have hNm : D * 2 ^ M * m < p ^ (n ^ 2) := by
      have h5 : ((D * 2 ^ M * m : ℕ) : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        have h7 : (m : ℝ) ≤ (2 : ℝ) ^ η := hmh
        push_cast
        calc (D : ℝ) * 2 ^ M * m ≤ (D : ℝ) * 2 ^ M * (2 : ℝ) ^ η := by gcongr
          _ = (D : ℝ) * (2 : ℝ) ^ ((M : ℝ) + η) := by
              rw [Real.rpow_add (by norm_num), Real.rpow_natCast]; ring
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


/-- **Theorem B (closed form).** -/
theorem explicit_upper_BM3 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ) (η : ℝ) (a : ℕ → ℕ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 0 ≤ η) :
    ∃ k : ℤ, 1 ≤ k ∧
      k ≤ ((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℤ) * ((2 ^ (MstarR S a η) : ℕ) : ℤ) ∧
      (((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℤ) ∣ k) ∧ InBall S δ k := by
  have hQ := discQR_nonneg hS hne a η hη
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb' (hS p hp)
  have hA0 : 0 ≤ sumA S := Finset.sum_nonneg (fun p _ => Real.sqrt_nonneg _)
  have hΔ0 : 0 ≤ sumDelta S a := by
    apply Finset.sum_nonneg
    intro p hp
    have := hlb p hp
    positivity
  have hh0 : (0 : ℝ) ≤ η := hη
  apply explicit_upper_multM3 hS hδ m (MstarR S a η) η a hm hmh hη
  set M := MstarR S a η with hMdef
  set t := tstarR S a η with ht
  have ht0 : 0 ≤ t := by
    rw [ht]; unfold tstarR
    have := Real.sqrt_nonneg (discQR S a η)
    positivity
  have hM : t ^ 2 - η - sumDelta S a ≤ M := Nat.le_ceil _
  have hΛ : t ^ 2 ≤ sumDelta S a + M + η := by linarith
  have hΛ0 : 0 ≤ sumDelta S a + M + η := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hx : t ≤ Real.sqrt (sumDelta S a + M + η) := by
    calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht0).symm
      _ ≤ _ := Real.sqrt_le_sqrt hΛ
  have hxsq : Real.sqrt (sumDelta S a + M + η) ^ 2 = sumDelta S a + M + η := Real.sq_sqrt hΛ0
  have hq := quad_step (A := sumA S) (α := sumAlpha S a) (Δ := sumDelta S a) (h := η) hh0 hA0 hQ
    (x := Real.sqrt (sumDelta S a + M + η)) hx
  have hqq : η * (sumA S * Real.sqrt (sumDelta S a + M + η) - sumAlpha S a)
      ≤ Real.sqrt (sumDelta S a + M + η) ^ 2 - η - sumDelta S a := hq
  rw [hxsq] at hqq
  unfold sumA sumAlpha sumDelta at hqq
  have e : η * (Real.sqrt ((∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ)) + M + η) *
        (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ))
      = η * ((∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) *
        Real.sqrt ((∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ)) + M + η) - ∑ p ∈ S, (a p : ℝ)) := by
    ring
  rw [e]
  linarith

/-- Two-sided form of Theorem B with the forced exponents `a_p = a_p(δ)`:
`D_S(δ) ≤ k ≤ D_S(δ) 2^M`. -/
theorem explicit_bounds_BM3 {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ) (η : ℝ) (hm : 1 ≤ (m : ℝ) * δ) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 0 ≤ η) :
    ∃ k : ℤ, 1 ≤ k ∧ (Dvis S δ : ℤ) ≤ k ∧
      k ≤ (Dvis S δ : ℤ) * ((2 ^ (MstarR S (fun p => aThr p δ) η) : ℕ) : ℤ) ∧ InBall S δ k := by
  obtain ⟨k, hk1, hkN, hkD, hk⟩ :=
    explicit_upper_BM3 (fun p hp => (hS p hp).two_le) hne hδ m η (fun p => aThr p δ) hm hmh hη
  exact ⟨k, hk1, Int.le_of_dvd (by omega) hkD, hkN, hk⟩


#print axioms explicit_upper_multM3
#print axioms explicit_upper_BM3
#print axioms explicit_bounds_BM3

end TVGPlus
end LeanCheck
