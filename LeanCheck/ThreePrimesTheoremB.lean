import LeanCheck.TVGPlusCount

/-!
# ThreePrimes: Theorem B (explicit bound on multiples of `D_S(δ)`)

Pigeonhole on the multiples `D x`, `0 ≤ x ≤ X` (`pigeonhole_box_mul`); Theorem B in sufficient-condition form (`explicit_upper_mult`), in closed form with `t*` and `M = ⌈t*² − h − Δ⌉` (`explicit_upper_B`, `discQ_nonneg`, `quad_step`), two-sided form with `D_S(δ)` (`explicit_bounds_B`) and the size `D 2^M ≤ max (D, 2^(t*² − h + 1))` (`size_B`).
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- Two reals whose scaled fractional parts fall in the same one of `m` boxes differ by less than `1/m`
modulo `1`. -/
lemma nrm_sub_lt_of_box {a b : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (h : ⌊(m : ℝ) * Int.fract a⌋₊ = ⌊(m : ℝ) * Int.fract b⌋₊) : nrm (b - a) < 1 / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set a' := (m : ℝ) * Int.fract a with ha
  set b' := (m : ℝ) * Int.fract b with hb
  have ha0 : 0 ≤ a' := by have := Int.fract_nonneg a; positivity
  have hb0 : 0 ≤ b' := by have := Int.fract_nonneg b; positivity
  have h1 := Nat.floor_le ha0
  have h2 := Nat.lt_floor_add_one a'
  have h3 := Nat.floor_le hb0
  have h4 := Nat.lt_floor_add_one b'
  rw [h] at h1 h2
  have hab : |a' - b'| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hfr : |Int.fract b - Int.fract a| < 1 / m := by
    have e : Int.fract b - Int.fract a = (b' - a') / m := by rw [ha, hb]; field_simp
    rw [e, abs_div, abs_of_pos hm0, abs_sub_comm]
    exact div_lt_div_of_pos_right hab hm0
  have e2 : b - a = (Int.fract b - Int.fract a) + ((⌊b⌋ - ⌊a⌋ : ℤ) : ℝ) := by
    push_cast; rw [Int.fract, Int.fract]; ring
  rw [e2, nrm_add_int]
  exact lt_of_le_of_lt (nrm_le_abs _) hfr

/-- Pigeonhole on the multiples `D x`, `0 ≤ x ≤ X`: some `k = D t`, `1 ≤ t ≤ X`, is `< 1/m` in every
retained coordinate. -/
lemma pigeonhole_box_mul (C : Finset (ℕ × ℕ)) (hq : ∀ c ∈ C, 0 < c.1 ^ (c.2 ^ 2)) (m X D : ℕ)
    (hm : 1 ≤ m) (hD : 1 ≤ D) (hX : m ^ C.card ≤ X) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ (D : ℤ) * X ∧ (D : ℤ) ∣ k ∧
      ∀ c ∈ C, nrm ((k : ℝ) / ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ)) < 1 / m := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set q : ℕ × ℕ → ℝ := fun c => ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ) with hqdef
  have hlt : ∀ (c : ℕ × ℕ) (x : ℕ), c ∈ C →
      ⌊(m : ℝ) * Int.fract (((D * x : ℕ) : ℝ) / q c)⌋₊ < m := by
    intro c x hc
    rw [Nat.floor_lt (by have := Int.fract_nonneg (((D * x : ℕ) : ℝ) / q c); positivity)]
    have := Int.fract_lt_one (((D * x : ℕ) : ℝ) / q c)
    nlinarith
  let F : Fin (X + 1) → (C → Fin m) := fun x c =>
    ⟨⌊(m : ℝ) * Int.fract (((D * (x : ℕ) : ℕ) : ℝ) / q c.1)⌋₊, hlt c.1 x c.2⟩
  have hcard : Fintype.card (C → Fin m) < Fintype.card (Fin (X + 1)) := by
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ,
      Fintype.card_coe]
    omega
  obtain ⟨x, y, hxy, hF⟩ := Fintype.exists_ne_map_eq_of_card_lt F hcard
  have core : ∀ x y : Fin (X + 1), x < y → F x = F y →
      ∃ k : ℤ, 1 ≤ k ∧ k ≤ (D : ℤ) * X ∧ (D : ℤ) ∣ k ∧
        ∀ c ∈ C, nrm ((k : ℝ) / ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ)) < 1 / m := by
    intro x y hlt' hFxy
    have hxy' : (x : ℕ) < (y : ℕ) := hlt'
    have hy : (y : ℕ) ≤ X := Nat.lt_succ_iff.mp y.2
    refine ⟨(D : ℤ) * (((y : ℕ) : ℤ) - ((x : ℕ) : ℤ)), ?_, ?_, ⟨_, rfl⟩, ?_⟩
    · have h1 : (1 : ℤ) ≤ D := by exact_mod_cast hD
      have h2 : (1 : ℤ) ≤ ((y : ℕ) : ℤ) - ((x : ℕ) : ℤ) := by omega
      nlinarith
    · have h1 : ((y : ℕ) : ℤ) ≤ X := by exact_mod_cast hy
      have h2 : (0 : ℤ) ≤ D := by positivity
      have h3 : (0 : ℤ) ≤ ((x : ℕ) : ℤ) := by positivity
      nlinarith
    · intro c hc
      have hfl : ⌊(m : ℝ) * Int.fract (((D * (x : ℕ) : ℕ) : ℝ) / q c)⌋₊
          = ⌊(m : ℝ) * Int.fract (((D * (y : ℕ) : ℕ) : ℝ) / q c)⌋₊ := by
        have := congrFun hFxy ⟨c, hc⟩
        exact congrArg Fin.val this
      have key := nrm_sub_lt_of_box hm hfl
      have e : ((D * (y : ℕ) : ℕ) : ℝ) / q c - ((D * (x : ℕ) : ℕ) : ℝ) / q c
          = ((((D : ℤ) * (((y : ℕ) : ℤ) - ((x : ℕ) : ℤ)) : ℤ)) : ℝ)
            / ((c.1 ^ (c.2 ^ 2) : ℕ) : ℝ) := by
        simp only [hqdef]
        push_cast
        ring
      rw [e] at key
      exact key
  rcases lt_or_gt_of_ne hxy with h | h
  · exact core x y h hF
  · exact core y x h hF.symm

#print axioms nrm_sub_lt_of_box
#print axioms pigeonhole_box_mul


lemma one_le_logb' {p : ℕ} (hp : 2 ≤ p) : 1 ≤ Real.logb 2 (p : ℝ) := by
  have : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 (p : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast hp)
  rwa [Real.logb_self_eq_one (by norm_num)] at this

/-- `log₂ D = Δ` for `D = ∏ p^(a_p²)`. -/
lemma logb_D {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) :
    Real.logb 2 (((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℕ) : ℝ)
      = ∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ) := by
  push_cast
  rw [Real.logb_prod S (fun p => ((p : ℝ)) ^ (a p ^ 2)) (fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    positivity)]
  apply Finset.sum_congr rfl
  intro p _
  rw [Real.logb_pow]
  push_cast
  ring

/-- **Theorem B, sufficient-condition form.** -/
theorem explicit_upper_mult {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (m h M : ℕ) (a : ℕ → ℕ) (hm : 2 ≤ (m : ℝ) * δ) (hmh : m ≤ 2 ^ h)
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
    rw [this] at hm
    simp at hm
    linarith
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
  have hhalf : 1 / (m : ℝ) ≤ δ / 2 := by
    rw [div_le_div_iff₀ hm0 (by norm_num)]
    linarith
  have hlbp := hlb p hp
  have hlpos : 0 < Real.logb 2 (p : ℝ) := by linarith
  have hbound : Pn (sqScales p) k ≤ δ / 2 := by
    apply Pn_le (sq_nonempty p)
    rintro q ⟨n, hn, rfl⟩
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
      linarith
    · push_neg at han
      by_cases hnr : n ≤ r p
      · have hmem : (p, n) ∈ C := by
          rw [hC, Finset.mem_biUnion]
          exact ⟨p, hp, Finset.mem_image.mpr ⟨n, Finset.mem_Ioc.mpr ⟨han, hnr⟩, rfl⟩⟩
        exact ((hk (p, n) hmem).trans_le hhalf).le
      · push_neg at hnr
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
        have hNm : D * 2 ^ M * m ≤ p ^ (n ^ 2) := by
          have h5 : ((D * 2 ^ M * m : ℕ) : ℝ) ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by
            have h7 : (m : ℝ) ≤ (2 : ℝ) ^ h := by exact_mod_cast hmh
            push_cast
            calc (D : ℝ) * 2 ^ M * m ≤ (D : ℝ) * 2 ^ M * (2 : ℝ) ^ h := by gcongr
              _ = (D : ℝ) * (2 : ℝ) ^ (M + h) := by rw [pow_add]; ring
              _ ≤ ((p : ℝ) ^ (n ^ 2)) := by exact_mod_cast hpow.le
          exact_mod_cast h5
        have hqpos : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
          exact_mod_cast pow_pos (by omega : 0 < p) _
        refine (nrm_le_abs _).trans ?_
        rw [abs_div, abs_of_pos hqpos, div_le_iff₀ hqpos]
        have hkabs : |(k : ℝ)| ≤ ((D * 2 ^ M : ℕ) : ℝ) := by
          rw [abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ k))]
          have : (k : ℝ) ≤ (((D : ℤ) * ((2 ^ M : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast hkN
          push_cast at this ⊢
          exact this
        have hNmR : ((D * 2 ^ M : ℕ) : ℝ) * m ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by
          have : ((D * 2 ^ M * m : ℕ) : ℝ) ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by exact_mod_cast hNm
          push_cast at this ⊢
          exact this
        have hN0 : (0 : ℝ) ≤ ((D * 2 ^ M : ℕ) : ℝ) := by positivity
        calc |(k : ℝ)| ≤ ((D * 2 ^ M : ℕ) : ℝ) := hkabs
          _ = ((D * 2 ^ M : ℕ) : ℝ) * (m * δ) / (m * δ) := by field_simp
          _ ≤ ((D * 2 ^ M : ℕ) : ℝ) * (m * δ) / 2 := by
              apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hm
          _ = (((D * 2 ^ M : ℕ) : ℝ) * m) * δ / 2 := by ring
          _ ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) * δ / 2 := by gcongr
          _ = δ / 2 * ((p ^ (n ^ 2) : ℕ) : ℝ) := by ring
  linarith

#print axioms logb_D
#print axioms explicit_upper_mult


/-- `A = ∑ (log₂ p)^(-1/2)`. -/
noncomputable def sumA (S : Finset ℕ) : ℝ := ∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))
/-- `α = ∑ a_p`. -/
noncomputable def sumAlpha (S : Finset ℕ) (a : ℕ → ℕ) : ℝ := ∑ p ∈ S, (a p : ℝ)
/-- `Δ = ∑ a_p² log₂ p = log₂ D`. -/
noncomputable def sumDelta (S : Finset ℕ) (a : ℕ → ℕ) : ℝ :=
  ∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ)
/-- The discriminant `Q = h² A² − 4 (h α − Δ − h)`. -/
noncomputable def discQ (S : Finset ℕ) (a : ℕ → ℕ) (h : ℕ) : ℝ :=
  (h : ℝ) ^ 2 * (sumA S) ^ 2 - 4 * ((h : ℝ) * sumAlpha S a - sumDelta S a - h)
/-- `t* = (hA + √Q)/2`. -/
noncomputable def tstar (S : Finset ℕ) (a : ℕ → ℕ) (h : ℕ) : ℝ :=
  ((h : ℝ) * sumA S + Real.sqrt (discQ S a h)) / 2
/-- `M = ⌈t*² − h − Δ⌉` (zero if that is not positive). -/
noncomputable def Mstar (S : Finset ℕ) (a : ℕ → ℕ) (h : ℕ) : ℕ :=
  ⌈(tstar S a h) ^ 2 - h - sumDelta S a⌉₊

/-- The quadratic step: for `x ≥ t*`, `h (A x − α) ≤ x² − h − Δ`. -/
lemma quad_step {A α Δ h : ℝ} (hh : 0 ≤ h) (hA : 0 ≤ A)
    (hQ : 0 ≤ h ^ 2 * A ^ 2 - 4 * (h * α - Δ - h)) {x : ℝ}
    (hx : (h * A + Real.sqrt (h ^ 2 * A ^ 2 - 4 * (h * α - Δ - h))) / 2 ≤ x) :
    h * (A * x - α) ≤ x ^ 2 - h - Δ := by
  set s := Real.sqrt (h ^ 2 * A ^ 2 - 4 * (h * α - Δ - h)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = h ^ 2 * A ^ 2 - 4 * (h * α - Δ - h) := Real.sq_sqrt hQ
  have h1 : 0 ≤ x - (h * A + s) / 2 := by linarith
  have h2 : 0 ≤ x - (h * A - s) / 2 := by linarith
  have h3 := mul_nonneg h1 h2
  nlinarith [h3, hs2]

/-- The discriminant is nonnegative (Cauchy–Schwarz). -/
lemma discQ_nonneg {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) (a : ℕ → ℕ) (h : ℕ) :
    0 ≤ discQ S a h := by
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
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  unfold discQ
  set A := sumA S
  set α := sumAlpha S a
  set Δ := sumDelta S a
  have k1 : (h : ℝ) ^ 2 * C0 * C0 ≤ (h : ℝ) ^ 2 * C0 * A ^ 2 :=
    mul_le_mul_of_nonneg_left hAC (by positivity)
  have k2 : (h * C0 - 2 * α) ^ 2 ≥ 0 := sq_nonneg _
  have k3 : 0 ≤ (h : ℝ) * C0 := by positivity
  by_contra hneg
  push_neg at hneg
  have : C0 * ((h : ℝ) ^ 2 * A ^ 2 - 4 * ((h : ℝ) * α - Δ - h)) < 0 :=
    mul_neg_of_pos_of_neg hC0pos hneg
  nlinarith [k1, k2, k3, CS]

/-- **Theorem B (closed form).** -/
theorem explicit_upper_B {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (m h : ℕ) (a : ℕ → ℕ) (hm : 2 ≤ (m : ℝ) * δ) (hmh : m ≤ 2 ^ h) :
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
  apply explicit_upper_mult hS hδ m h (Mstar S a h) a hm hmh
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

#print axioms quad_step
#print axioms discQ_nonneg
#print axioms explicit_upper_B


/-- Two-sided form of Theorem B with the forced exponents `a_p = a_p(δ)`:
`D_S(δ) ≤ k ≤ D_S(δ) 2^M`. -/
theorem explicit_bounds_B {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (m h : ℕ) (hm : 2 ≤ (m : ℝ) * δ) (hmh : m ≤ 2 ^ h) :
    ∃ k : ℤ, 1 ≤ k ∧ (Dvis S δ : ℤ) ≤ k ∧
      k ≤ (Dvis S δ : ℤ) * ((2 ^ (Mstar S (fun p => aThr p δ) h) : ℕ) : ℤ) ∧ InBall S δ k := by
  obtain ⟨k, hk1, hkN, hkD, hk⟩ :=
    explicit_upper_B (fun p hp => (hS p hp).two_le) hne hδ m h (fun p => aThr p δ) hm hmh
  exact ⟨k, hk1, Int.le_of_dvd (by omega) hkD, hkN, hk⟩

/-- The size of the bound: `D 2^M ≤ max (D, 2^(t*² − h + 1))`. -/
theorem size_B {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (h : ℕ) :
    (((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) * 2 ^ (Mstar S a h) : ℕ) : ℝ)
      ≤ max (((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℕ) : ℝ)
          ((2 : ℝ) ^ ((tstar S a h) ^ 2 - h + 1)) := by
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
  by_cases hx : 0 ≤ (tstar S a h) ^ 2 - h - sumDelta S a
  · have hlt : ((Mstar S a h : ℕ) : ℝ) < (tstar S a h) ^ 2 - h - sumDelta S a + 1 :=
      Nat.ceil_lt_add_one hx
    have h2M : (2 : ℝ) ^ (Mstar S a h) ≤ (2 : ℝ) ^ ((tstar S a h) ^ 2 - h - sumDelta S a + 1) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlt.le
    push_cast
    calc (D : ℝ) * (2 : ℝ) ^ (Mstar S a h)
        ≤ (2 : ℝ) ^ (sumDelta S a) * (2 : ℝ) ^ ((tstar S a h) ^ 2 - h - sumDelta S a + 1) := by
          rw [hDrp]
          gcongr
      _ = (2 : ℝ) ^ ((tstar S a h) ^ 2 - h + 1) := by
          rw [← Real.rpow_add (by norm_num)]
          congr 1
          ring
      _ ≤ _ := le_max_right _ _
  · have hM0 : Mstar S a h = 0 := by
      unfold Mstar
      apply Nat.ceil_eq_zero.mpr
      linarith [not_le.mp hx]
    rw [hM0]
    push_cast
    simp

#print axioms explicit_bounds_B
#print axioms size_B


end TVGPlus
end LeanCheck
