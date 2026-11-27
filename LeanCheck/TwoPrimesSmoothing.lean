import LeanCheck.TwoPrimesSharpFactor

/-!
# Smoothing digits concentrated at the ends of their range

The smoothing digit of a level with range `J` is `±J` with probability `9/20` each, and uniform on
`[-J, J]` with probability `1/10`.  Only the range of a digit matters for the radius.

* `abs_phi_le`: `‖x‖ ≥ (12/25D)/J`, `D ≥ 12`, gives `|factor| ≤ exp(-4/D²)`.
* `rigidity_smooth`: hence at most `⌊D² log(1/η)/4⌋` visible levels.
* `witness_of_density_smooth`, `witness_of_critical_density_smooth`,
  `witness_of_free_heights_smooth`: the consequences with `B = ⌊D² log(17K)/8⌋`.
* `cos_le_mean`: no distribution of a digit on `[-J, J]` gives a smaller factor than
  `cos(2πσ)` at the distance `σ/J`.

The densities are hypotheses.
-/

namespace TwoPrimesSmoothing

open Finset Real TwoPrimesEffective TwoPrimesWindows TwoPrimesFreeHeight TwoPrimesAdaptive
  TwoPrimesSharpFactor

/-- The characteristic function of the smoothing digit. -/
noncomputable def phi (J : ℕ) (x : ℝ) : ℝ := 9 / 10 * cos (2 * π * J * x) + 1 / 10 * digit J x

lemma phi_neg (J : ℕ) (x : ℝ) : phi J (-x) = phi J x := by
  unfold phi
  rw [digit_neg, mul_neg, cos_neg]

lemma abs_phi_le_one (J : ℕ) (x : ℝ) : |phi J x| ≤ 1 := by
  unfold phi
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 10)]
  have h1 := abs_cos_le_one (2 * π * J * x)
  have h2 := abs_digit_le_one J x
  linarith

/-- **The factor of one smoothing digit.** -/
lemma abs_phi_le {J D : ℕ} (hJ : 1 ≤ J) (hD : 12 ≤ D) {x : ℝ}
    (h : (12 / 25 / (D : ℝ)) / J ≤ |x - round x|) : |phi J x| ≤ exp (-(4 / (D : ℝ) ^ 2)) := by
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hD' : (12 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  set y := |x - (round x : ℝ)| with hy
  have hy0 : 0 ≤ y := abs_nonneg _
  have hy2 : y ≤ 1 / 2 := abs_sub_round x
  have hphi : phi J x = phi J y := by
    have h1 : phi J x = phi J (x - round x) := by
      unfold phi
      rw [digit_sub_int]
      congr 2
      have e : 2 * π * J * (x - round x)
          = 2 * π * J * x - (((J : ℤ) * round x : ℤ) : ℝ) * (2 * π) := by
        push_cast; ring
      rw [e, cos_sub_int_mul_two_pi]
    rw [h1]
    rcases abs_cases (x - (round x : ℝ)) with ⟨ha, _⟩ | ⟨ha, _⟩
    · rw [hy, ha]
    · rw [hy, ha, phi_neg]
  rw [hphi]
  set σ : ℝ := 12 / 25 / (D : ℝ) with hσ
  have hσ0 : 0 < σ := by positivity
  have hσy : σ ≤ y * J := by
    rwa [div_le_iff₀ (by positivity)] at h
  have hsmall : 4 / (D : ℝ) ^ 2 ≤ 1 / 36 := by
    have h2 : (144 : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have key : |phi J y| ≤ 1 - 4 / (D : ℝ) ^ 2 := by
    rcases le_or_gt y (1 / (2 * (J : ℝ) + 1)) with hc | hc
    · have hM : (0 : ℝ) < 2 * J + 1 := by positivity
      have hyM : y * (2 * (J : ℝ) + 1) ≤ 1 := by rwa [le_div_iff₀ hM] at hc
      have hJy : (J : ℝ) * y ≤ 1 / 2 := by nlinarith
      have hdn := (digit_near hy0 hc).1
      have hdu : digit J y ≤ 1 := le_trans (le_abs_self _) (abs_digit_le_one _ _)
      set z : ℝ := 2 * π * σ with hz
      have hpi := pi_pos
      have hz0 : 0 ≤ z := by positivity
      have hzeq : z * D = 2 * π * (12 / 25) := by
        rw [hz, hσ]; field_simp
      have hzub : z ≤ 0.253 := by
        have h1 : z * 12 ≤ z * D := mul_le_mul_of_nonneg_left hD' hz0
        have h2 : π < 3.15 := pi_lt_d2
        linarith
      have hmono : cos (2 * π * J * y) ≤ cos z := by
        apply cos_le_cos_of_nonneg_of_le_pi hz0
        · have := mul_le_mul_of_nonneg_left hJy (show (0 : ℝ) ≤ 2 * π by positivity)
          linarith
        · have := mul_le_mul_of_nonneg_left hσy (show (0 : ℝ) ≤ 2 * π by positivity)
          rw [hz]; linarith
      have hcos : cos z ≤ 1 - z ^ 2 / 2 + z ^ 4 * (5 / 96) := by
        have hb := cos_bound (x := z) (by rw [abs_of_nonneg hz0]; linarith)
        have := (abs_le.mp hb).2
        rw [abs_of_nonneg hz0] at this
        linarith
      have hzlb : 9.08 / (D : ℝ) ^ 2 ≤ z ^ 2 := by
        have h1 : (3.014 : ℝ) ≤ z * D := by
          rw [hzeq]
          have : (3.14 : ℝ) < π := pi_gt_d2
          linarith
        have h2 := pow_le_pow_left₀ (by norm_num) h1 2
        rw [mul_pow] at h2
        rw [div_le_iff₀ (by positivity)]
        have : (9.08 : ℝ) ≤ 3.014 ^ 2 := by norm_num
        linarith
      have hz2 : z ^ 2 ≤ 0.0641 := by
        have := pow_le_pow_left₀ hz0 hzub 2
        have : (0.253 : ℝ) ^ 2 ≤ 0.0641 := by norm_num
        linarith
      have hz4 : z ^ 4 ≤ z ^ 2 * 0.0641 := by
        have e : z ^ 4 = z ^ 2 * z ^ 2 := by ring
        rw [e]; exact mul_le_mul_of_nonneg_left hz2 (sq_nonneg _)
      have hgain : 4 / (D : ℝ) ^ 2 ≤ 9 / 10 * (1 - cos z) := by
        have e : 4 / (D : ℝ) ^ 2 = (4 / 9.08) * (9.08 / (D : ℝ) ^ 2) := by
          field_simp
        have h1 : 4 / (D : ℝ) ^ 2 ≤ 4 / 9.08 * z ^ 2 := by
          rw [e]; exact mul_le_mul_of_nonneg_left hzlb (by norm_num)
        have h2 : 4 / 9.08 * z ^ 2 ≤ 9 / 10 * (z ^ 2 / 2 - z ^ 4 * (5 / 96)) := by
          have := sq_nonneg z
          nlinarith
        linarith
      unfold phi
      have hlow := neg_one_le_cos (2 * π * J * y)
      rw [abs_le]
      constructor
      · linarith
      · linarith
    · have hd := digit_half hc.le hy2
      unfold phi
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 10)]
      have h1 := abs_cos_le_one (2 * π * J * y)
      linarith
  refine le_trans key (le_trans (le_of_eq (by ring)) (add_one_le_exp _))

/-- No digit supported on `[-J, J]` has a smaller factor than `cos(2πσ)` at the distance `σ/J`. -/
lemma cos_le_mean {J : ℕ} (hJ : 1 ≤ J) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 2) (w : ℤ → ℝ)
    (hw : ∀ j ∈ Icc (-(J : ℤ)) J, 0 ≤ w j) (h1 : ∑ j ∈ Icc (-(J : ℤ)) J, w j = 1) :
    cos (2 * π * σ) ≤ ∑ j ∈ Icc (-(J : ℤ)) J, w j * cos (2 * π * j * (σ / J)) := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hpi := pi_pos
  have key : ∀ j ∈ Icc (-(J : ℤ)) J,
      w j * cos (2 * π * σ) ≤ w j * cos (2 * π * j * (σ / J)) := by
    intro j hj
    refine mul_le_mul_of_nonneg_left ?_ (hw j hj)
    rw [mem_Icc] at hj
    have hjJ : |(j : ℝ)| ≤ J := by
      rw [abs_le]
      exact ⟨by exact_mod_cast hj.1, by exact_mod_cast hj.2⟩
    have e : cos (2 * π * j * (σ / J)) = cos (2 * π * (|(j : ℝ)| * (σ / J))) := by
      rcases abs_cases (j : ℝ) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; congr 1; ring
      · rw [h, ← cos_neg]; congr 1; ring
    have hle : |(j : ℝ)| * (σ / J) ≤ σ := by
      have := mul_le_mul_of_nonneg_right hjJ (show 0 ≤ σ / J by positivity)
      rwa [mul_div_cancel₀ _ hJ'.ne'] at this
    rw [e]
    apply cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · have := mul_le_mul_of_nonneg_left hσ (show (0 : ℝ) ≤ 2 * π by positivity)
      linarith
    · exact mul_le_mul_of_nonneg_left hle (by positivity)
  have := sum_le_sum key
  rwa [← sum_mul, h1, one_mul] at this

/-! ## The smoothing variable -/

/-- Equally likely labels whose values have the law of the smoothing digit. -/
abbrev Om (J : ℕ) : Type :=
  (Fin 2 × {k : ℤ // k ∈ Icc (-(J : ℤ)) J}) ⊕ (Fin (9 * (2 * J + 1)) × Bool)

/-- The digit of a label. -/
def dig (J : ℕ) : Om J → ℤ
  | Sum.inl x => x.2.1
  | Sum.inr x => if x.2 then (J : ℤ) else -(J : ℤ)

lemma dig_mem (J : ℕ) (ω : Om J) : dig J ω ∈ Icc (-(J : ℤ)) J := by
  rcases ω with x | x
  · exact x.2.2
  · simp only [dig, mem_Icc]
    split <;> omega

lemma card_Om (J : ℕ) : Fintype.card (Om J) = 20 * (2 * J + 1) := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_bool, Fintype.card_coe, card_digits]
  ring

lemma sum_digit (J : ℕ) (x : ℝ) : ∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x)
    = ((((2 * J + 1 : ℕ) : ℝ) * digit J x : ℝ) : ℂ) := by
  have hre : (∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x)).re
      = ((2 * J + 1 : ℕ) : ℝ) * digit J x := by
    rw [Complex.re_sum, digit]
    have hM : (2 * (J : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    rw [mul_div_cancel₀ _ hM]
    refine sum_congr rfl (fun k _ => ?_)
    rw [e_re]; congr 1; ring
  have him : (∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x)).im = 0 := by
    have hc : (starRingEnd ℂ) (∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x))
        = ∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x) := by
      rw [map_sum]
      refine sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp only [mem_Icc] at hk ⊢; omega
      · intro k hk; simp only [mem_Icc] at hk ⊢; omega
      · intro k _; simp
      · intro k _; simp
      · intro k _
        rw [e_conj]; congr 1; push_cast; ring
    exact Complex.conj_eq_iff_im.mp hc
  apply Complex.ext
  · rw [hre, Complex.ofReal_re]
  · rw [him, Complex.ofReal_im]

lemma sum_Om (J : ℕ) (x : ℝ) : ∑ ω : Om J, e ((dig J ω : ℝ) * x)
    = ((((20 * (2 * J + 1) : ℕ) : ℝ) * phi J x : ℝ) : ℂ) := by
  have hinl : ∑ a : Fin 2 × {k : ℤ // k ∈ Icc (-(J : ℤ)) J}, e ((dig J (Sum.inl a) : ℝ) * x)
      = 2 * ((((2 * J + 1 : ℕ) : ℝ) * digit J x : ℝ) : ℂ) := by
    rw [Fintype.sum_prod_type]
    have : ∑ k : {k : ℤ // k ∈ Icc (-(J : ℤ)) J}, e (((k.1 : ℤ) : ℝ) * x)
        = ∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x) :=
      sum_coe_sort (Icc (-(J : ℤ)) J) (fun k : ℤ => e ((k : ℝ) * x))
    simp only [dig]
    rw [this, sum_digit, Fin.sum_univ_two]
    ring
  have hpair : e (((J : ℤ) : ℝ) * x) + e (((-(J : ℤ) : ℤ) : ℝ) * x)
      = ((2 * cos (2 * π * J * x) : ℝ) : ℂ) := by
    have h1 : e (((-(J : ℤ) : ℤ) : ℝ) * x) = (starRingEnd ℂ) (e (((J : ℤ) : ℝ) * x)) := by
      rw [e_conj]; congr 1; push_cast; ring
    rw [h1, Complex.add_conj, e_re]
    congr 2
    push_cast
    ring_nf
  have hinr : ∑ b : Fin (9 * (2 * J + 1)) × Bool, e ((dig J (Sum.inr b) : ℝ) * x)
      = ((9 * (2 * J + 1) : ℕ) : ℂ) * ((2 * cos (2 * π * J * x) : ℝ) : ℂ) := by
    rw [Fintype.sum_prod_type]
    have : ∀ i : Fin (9 * (2 * J + 1)),
        ∑ s : Bool, e ((dig J (Sum.inr (i, s)) : ℝ) * x)
          = ((2 * cos (2 * π * J * x) : ℝ) : ℂ) := by
      intro i
      rw [Fintype.sum_bool, ← hpair]
      simp [dig]
    rw [sum_congr rfl (fun i _ => this i), sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [Fintype.sum_sum_type, hinl, hinr]
  unfold phi
  push_cast
  ring

/-- The labels of the levels below `N`. -/
abbrev Idx (p D N : ℕ) : Type := (n : Fin N) → Om (range' p D n)

/-- All of them. -/
def idx (p D N : ℕ) : Finset (Idx p D N) := univ

lemma idx_nonempty (p D N : ℕ) : (idx p D N).Nonempty :=
  ⟨fun n => Sum.inr (⟨0, by omega⟩, true), mem_univ _⟩

/-- The digit vector of a label. -/
def digits {p D N : ℕ} (ω : Idx p D N) : Fin N → ℤ := fun n => dig (range' p D n) (ω n)

/-- The integer of a label. -/
def val' (p : ℕ) {D N : ℕ} (ω : Idx p D N) : ℤ := value p (digits ω)

lemma digits_mem {p D N : ℕ} (ω : Idx p D N) : digits ω ∈ vectors p D N := by
  rw [vectors, Fintype.mem_piFinset]
  intro n
  exact dig_mem _ _

lemma abs_val'_le {p D N : ℕ} (hp : 2 ≤ p) (hD : 1 ≤ D) {ω : Idx p D N}
    (_h : ω ∈ idx p D N) : |(val' p ω : ℝ)| ≤ (p : ℝ) ^ (N ^ 2) :=
  abs_value_le hp hD (digits_mem ω)

lemma small_val' {p D N : ℕ} (hp : 2 ≤ p) (hD : 1 ≤ D) {ω : Idx p D N}
    (_h : ω ∈ idx p D N) : Small p (1 / D) (val' p ω) :=
  small_value hp hD (digits_mem ω)

/-- The product of the factors of the smoothing digits. -/
noncomputable def prodPhi (p D N : ℕ) (θ : ℝ) : ℝ :=
  ∏ n ∈ Finset.range N, phi (range' p D n) ((p : ℝ) ^ (n ^ 2) * θ)

lemma sum_idx (p D N : ℕ) (θ : ℝ) :
    ∑ ω ∈ idx p D N, e ((val' p ω : ℝ) * θ)
      = (((idx p D N).card : ℝ) * prodPhi p D N θ : ℝ) := by
  have hprod : ∀ ω : Idx p D N, e ((val' p ω : ℝ) * θ)
      = ∏ n : Fin N, e ((dig (range' p D n) (ω n) : ℝ) * ((p : ℝ) ^ ((n : ℕ) ^ 2) * θ)) := by
    intro ω
    unfold e
    rw [← Complex.exp_sum]
    congr 1
    rw [val', value]
    simp only [digits]
    push_cast
    rw [sum_mul, mul_sum, sum_mul]
    exact sum_congr rfl (fun n _ => by ring)
  have hcard : (idx p D N).card = ∏ n : Fin N, 20 * (2 * range' p D n + 1) := by
    rw [idx, card_univ, Fintype.card_pi]
    exact prod_congr rfl (fun n _ => card_Om _)
  rw [hcard]
  unfold idx
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun (n : Fin N) (a : Om (range' p D n)) =>
    e ((dig (range' p D n) a : ℝ) * ((p : ℝ) ^ ((n : ℕ) ^ 2) * θ)))]
  simp_rw [sum_Om]
  rw [← Complex.ofReal_prod]
  congr 1
  rw [prod_mul_distrib, prodPhi,
    ← Fin.prod_univ_eq_prod_range (fun n => phi (range' p D n) ((p : ℝ) ^ (n ^ 2) * θ))]
  push_cast
  rfl

/-! ## Counting and rigidity -/

/-- The levels at which the argument is visibly away from the integers. -/
noncomputable def marked'' (p D N : ℕ) (θ : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun n => 1 ≤ range' p D n ∧
    (12 / 25 / (D : ℝ)) / (range' p D n)
      ≤ |(p : ℝ) ^ (n ^ 2) * θ - round ((p : ℝ) ^ (n ^ 2) * θ)|)

lemma card_marked'' {p D N : ℕ} {θ η : ℝ} (hD : 12 ≤ D) (hη : 0 < η)
    (h : η ≤ |prodPhi p D N θ|) : ((marked'' p D N θ).card : ℝ) ≤ D ^ 2 / 4 * (-log η) := by
  have hD' : (12 : ℝ) ≤ D := by exact_mod_cast hD
  have hprod : |prodPhi p D N θ| ≤ exp (-(4 / (D : ℝ) ^ 2) * (marked'' p D N θ).card) := by
    unfold prodPhi
    rw [abs_prod]
    have hsub : marked'' p D N θ ⊆ Finset.range N := filter_subset _ _
    rw [← prod_sdiff hsub]
    have h1 : ∏ n ∈ Finset.range N \ marked'' p D N θ,
        |phi (range' p D n) ((p : ℝ) ^ (n ^ 2) * θ)| ≤ 1 :=
      prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_phi_le_one _ _)
    have h2 : ∏ n ∈ marked'' p D N θ, |phi (range' p D n) ((p : ℝ) ^ (n ^ 2) * θ)|
        ≤ ∏ _n ∈ marked'' p D N θ, exp (-(4 / (D : ℝ) ^ 2)) := by
      refine prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun n hn => ?_)
      rw [marked'', mem_filter] at hn
      exact abs_phi_le hn.2.1 hD hn.2.2
    refine le_trans (mul_le_mul h1 h2 (prod_nonneg (fun _ _ => abs_nonneg _)) zero_le_one) ?_
    rw [one_mul, prod_const, ← exp_nat_mul]
    apply le_of_eq; congr 1; ring
  have hlog := log_le_log hη (le_trans h hprod)
  rw [log_exp] at hlog
  have h4 : (0 : ℝ) < (D : ℝ) ^ 2 / 4 := by positivity
  have h1 : (4 / (D : ℝ) ^ 2) * (marked'' p D N θ).card ≤ -log η := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 h4.le
  have e : (D : ℝ) ^ 2 / 4 * (4 / (D : ℝ) ^ 2 * (marked'' p D N θ).card)
      = (marked'' p D N θ).card := by
    field_simp
  rwa [e] at h2

lemma card_marked_joint'' {p q D Np Nq : ℕ} {θ η : ℝ} (hD : 12 ≤ D) (hη : 0 < η)
    (h : η ≤ |prodPhi p D Np θ| * |prodPhi q D Nq θ|) :
    ((marked'' p D Np θ).card : ℝ) + ((marked'' q D Nq θ).card : ℝ)
      ≤ D ^ 2 / 4 * (-log η) := by
  have h0 : 0 < |prodPhi p D Np θ| * |prodPhi q D Nq θ| := lt_of_lt_of_le hη h
  have h1 : 0 < |prodPhi p D Np θ| := by
    refine lt_of_le_of_ne (abs_nonneg _) (fun e => ?_)
    rw [← e, zero_mul] at h0
    exact lt_irrefl 0 h0
  have h2 : 0 < |prodPhi q D Nq θ| := by
    refine lt_of_le_of_ne (abs_nonneg _) (fun e => ?_)
    rw [← e, mul_zero] at h0
    exact lt_irrefl 0 h0
  have c1 := card_marked'' (p := p) (N := Np) (θ := θ) hD h1 le_rfl
  have c2 := card_marked'' (p := q) (N := Nq) (θ := θ) hD h2 le_rfl
  have hlog := log_le_log hη h
  rw [log_mul h1.ne' h2.ne'] at hlog
  have h4 : (0 : ℝ) ≤ (D : ℝ) ^ 2 / 4 := by positivity
  have := mul_le_mul_of_nonneg_left (neg_le_neg hlog) h4
  linarith

/-- Along a run of quiet levels with `J ≥ 50` the phase only gets multiplied. -/
lemma run_smooth {p D n1 n2 : ℕ} {θ : ℝ} (hD : 12 ≤ D) (h12 : n1 < n2)
    (hJ : ∀ n, n1 ≤ n → n < n2 → 50 ≤ range' p D n)
    (hu : ∀ n, n1 ≤ n → n < n2 →
      |(p : ℝ) ^ (n ^ 2) * θ - round ((p : ℝ) ^ (n ^ 2) * θ)|
        < (12 / 25 / (D : ℝ)) / (range' p D n))
    (hp : 0 < p) :
    ∃ a : ℤ, |θ - a / (p : ℝ) ^ (n1 ^ 2)| ≤ 1 / (p : ℝ) ^ (n2 ^ 2) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hD' : (12 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  set σ : ℝ := 12 / 25 / (D : ℝ) with hσ
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 / 25 := by
    rw [hσ, div_le_iff₀ hD0]; linarith
  have hσ2 : 2 * (D : ℝ) * σ = 24 / 25 := by
    rw [hσ]; field_simp; ring
  set x : ℕ → ℝ := fun n => (p : ℝ) ^ (n ^ 2) * θ with hx
  set a : ℤ := round (x n1) with ha
  have hsize : ∀ n, n1 ≤ n → n < n2 →
      (p : ℝ) ^ (2 * n + 1) * (σ / range' p D n) ≤ 49 / 50 ∧
      σ / range' p D n ≤ 1 / 1000 := by
    intro n hn hlt
    have hJn := hJ n hn hlt
    have hJr : (50 : ℝ) ≤ (range' p D n : ℝ) := by exact_mod_cast hJn
    have hJ0 : (0 : ℝ) < range' p D n := by linarith
    have hmul : p ^ (2 * n + 1) ≤ 2 * D * (range' p D n + 1) :=
      le_of_lt (Nat.lt_mul_div_succ (p ^ (2 * n + 1)) (show 0 < 2 * D by omega))
    have hmul' : (p : ℝ) ^ (2 * n + 1) ≤ 2 * D * (range' p D n + 1) := by exact_mod_cast hmul
    constructor
    · rw [mul_div_assoc', div_le_iff₀ hJ0]
      have h1 := mul_le_mul_of_nonneg_right hmul' hσ0.le
      have h2 : 2 * (D : ℝ) * (range' p D n + 1) * σ = (2 * D * σ) * (range' p D n + 1) := by
        ring
      rw [h2, hσ2] at h1
      linarith
    · rw [div_le_iff₀ hJ0]; linarith
  have main : ∀ n, n1 ≤ n → n < n2 → ∃ c : ℤ,
      x n - c = (p : ℝ) ^ (n ^ 2) / (p : ℝ) ^ (n1 ^ 2) * (x n1 - a) ∧
      |x n - c| < σ / range' p D n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro hlt
      refine ⟨a, ?_, hu n1 le_rfl hlt⟩
      rw [div_self (by positivity), one_mul]
    | succ n hn ih =>
      intro hlt
      have hlt' : n < n2 := by omega
      obtain ⟨c, hc, hsmall⟩ := ih hlt'
      have hstep : x (n + 1) = (p : ℝ) ^ (2 * n + 1) * x n := by
        show (p : ℝ) ^ ((n + 1) ^ 2) * θ = (p : ℝ) ^ (2 * n + 1) * ((p : ℝ) ^ (n ^ 2) * θ)
        rw [← mul_assoc, ← pow_add]; congr 2; ring
      have hpow : (p : ℝ) ^ ((n + 1) ^ 2) = (p : ℝ) ^ (2 * n + 1) * (p : ℝ) ^ (n ^ 2) := by
        rw [← pow_add]; congr 1; ring
      have e : x (n + 1) - (((p : ℤ) ^ (2 * n + 1) * c : ℤ) : ℝ)
          = (p : ℝ) ^ (2 * n + 1) * (x n - c) := by
        rw [hstep]; push_cast; ring
      have hbig : |x (n + 1) - (((p : ℤ) ^ (2 * n + 1) * c : ℤ) : ℝ)| ≤ 49 / 50 := by
        rw [e, abs_mul, abs_of_pos (pow_pos hp' _)]
        exact le_trans (mul_le_mul_of_nonneg_left hsmall.le (pow_pos hp' _).le)
          (hsize n hn hlt').1
      have hnext := hu (n + 1) (by omega) hlt
      have hnext' : |x (n + 1) - round (x (n + 1))| < 1 / 1000 :=
        lt_of_lt_of_le hnext (hsize (n + 1) (by omega) hlt).2
      have hround : (round (x (n + 1)) : ℤ) = (p : ℤ) ^ (2 * n + 1) * c := by
        have h2 : |((round (x (n + 1)) : ℤ) : ℝ)
            - (((p : ℤ) ^ (2 * n + 1) * c : ℤ) : ℝ)| < 1 := by
          have t := abs_sub_le ((round (x (n + 1)) : ℤ) : ℝ) (x (n + 1))
            (((p : ℤ) ^ (2 * n + 1) * c : ℤ) : ℝ)
          rw [abs_sub_comm ((round (x (n + 1)) : ℤ) : ℝ) (x (n + 1))] at t
          linarith
        have h3 : |round (x (n + 1)) - (p : ℤ) ^ (2 * n + 1) * c| < 1 := by exact_mod_cast h2
        have h4 := Int.abs_lt_one_iff.mp h3
        omega
      refine ⟨(p : ℤ) ^ (2 * n + 1) * c, ?_, ?_⟩
      · rw [e, hc, hpow]; ring
      · rw [← hround]; exact hnext
  obtain ⟨m, rfl⟩ : ∃ m, n2 = m + 1 := ⟨n2 - 1, by omega⟩
  have hm : n1 ≤ m := by omega
  obtain ⟨c, hc, hsmall⟩ := main m hm (Nat.lt_succ_self m)
  refine ⟨a, ?_⟩
  have hP1 : (0 : ℝ) < (p : ℝ) ^ (n1 ^ 2) := pow_pos hp' _
  have hPm : (0 : ℝ) < (p : ℝ) ^ (m ^ 2) := pow_pos hp' _
  have e1 : θ - a / (p : ℝ) ^ (n1 ^ 2) = (x m - c) / (p : ℝ) ^ (m ^ 2) := by
    rw [hc]
    show _ = (p : ℝ) ^ (m ^ 2) / (p : ℝ) ^ (n1 ^ 2) * ((p : ℝ) ^ (n1 ^ 2) * θ - a)
      / (p : ℝ) ^ (m ^ 2)
    field_simp
  have hpow : (p : ℝ) ^ ((m + 1) ^ 2) = (p : ℝ) ^ (2 * m + 1) * (p : ℝ) ^ (m ^ 2) := by
    rw [← pow_add]; congr 1; ring
  rw [e1, abs_div, abs_of_pos hPm, div_le_div_iff₀ hPm (pow_pos hp' _), one_mul, hpow,
    ← mul_assoc]
  have h1 := mul_le_mul_of_nonneg_right hsmall.le (pow_pos hp' (2 * m + 1)).le
  have h2 := (hsize m hm (Nat.lt_succ_self m)).1
  have h3 : |x m - c| * (p : ℝ) ^ (2 * m + 1) ≤ 1 := by
    rw [mul_comm (σ / _)] at h1; linarith
  exact mul_le_of_le_one_left hPm.le h3

/-- Levels inside a window have a digit range of at least `50`. -/
lemma range_fifty {p D n : ℕ} (hp : 2 ≤ p) (hD : 1 ≤ D) {c x0 : ℝ} (hc : sqrt (log p) ≤ c)
    (hx : 50 * c ≤ x0) (hD4 : log (50 * D) ^ 2 ≤ 4 * log p * x0 ^ 2) {k : ℕ}
    (hn : loA p c x0 k ≤ n) : 50 ≤ range' p D n := by
  have hs0 := sqrt_log_pos hp
  have hl := TwoPrimesEffective.log_pos' hp
  have hc0 : 0 ≤ c := le_trans hs0.le hc
  have hx0 : 0 ≤ x0 := by linarith
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h0 : x0 / sqrt (log p) ≤ (n : ℝ) := by
    have h1 : x0 / sqrt (log p) ≤ (loA p c x0 0 : ℝ) := by
      unfold loA; exact Nat.le_ceil _
    have h2 : loA p c x0 0 ≤ n := le_trans (loA_mono hp hc0 hx0 (Nat.zero_le k)) hn
    exact le_trans h1 (by exact_mod_cast h2)
  have h1 : x0 ^ 2 ≤ (n : ℝ) ^ 2 * log p := by
    have h2 : x0 ≤ n * sqrt (log p) := by
      rwa [div_le_iff₀ hs0] at h0
    have := pow_le_pow_left₀ hx0 h2 2
    rwa [mul_pow, sq_sqrt hl.le] at this
  have h2 : log (50 * D) ≤ 2 * n * log p := by
    have h3 : log (50 * (D : ℝ)) ^ 2 ≤ (2 * n * log p) ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 4 * log p by positivity)
      nlinarith
    have h4 : 0 ≤ log (50 * (D : ℝ)) := log_nonneg (by linarith)
    exact (pow_le_pow_iff_left₀ h4 (by positivity) two_ne_zero).mp h3
  have h5 : (50 * D : ℝ) ≤ (p : ℝ) ^ (2 * n) := by
    rw [pow_eq_exp hp, ← exp_log (show (0 : ℝ) < 50 * D by positivity)]
    apply exp_le_exp.mpr
    push_cast
    linarith
  have h6 : 50 * D ≤ p ^ (2 * n) := by exact_mod_cast h5
  have h7 : 100 * D ≤ p ^ (2 * n + 1) := by
    rw [pow_succ]
    calc 100 * D = 50 * D * 2 := by ring
      _ ≤ p ^ (2 * n) * p := Nat.mul_le_mul h6 hp
  unfold range'
  rw [Nat.le_div_iff_mul_le (by omega)]
  omega

/-- **Rigidity with the concentrated smoothing digits.** -/
theorem rigidity_smooth {p q D B Np Nq : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 12 ≤ D) {η c x0 θ : ℝ} (hη : 0 < η) (hB : (D : ℝ) ^ 2 / 4 * (-log η) < B + 1)
    (hcp : sqrt (log p) ≤ c) (hcq : sqrt (log q) ≤ c) (hx : 50 * c ≤ x0)
    (hDp : log (50 * D) ^ 2 ≤ 4 * log p * x0 ^ 2) (hDq : log (50 * D) ^ 2 ≤ 4 * log q * x0 ^ 2)
    (hNp : hiA p c x0 B ≤ Np) (hNq : hiA q c x0 B ≤ Nq)
    (h12 : η ≤ |prodPhi p D Np θ| * |prodPhi q D Nq θ|) :
    ∃ z : ℤ, |θ - z| ≤ exp (-(2 * x0 ^ 2)) / 2 := by
  classical
  have hc0 : 0 < c := lt_of_lt_of_le (sqrt_log_pos hp) hcp
  have hx0 : 0 ≤ x0 := by linarith
  set Mp := marked'' p D Np θ with hMp
  set Mq := marked'' q D Nq θ with hMq
  have hsum : Mp.card + Mq.card ≤ B := by
    have h := lt_of_le_of_lt (card_marked_joint'' hD hη h12) hB
    have : Mp.card + Mq.card < B + 1 := by exact_mod_cast h
    omega
  have hord : ∀ r : ℕ, 2 ≤ r → sqrt (log r) ≤ c → ∀ j k, j < k → hiA r c x0 j ≤ loA r c x0 k := by
    intro r hr hcr j k hjk
    exact le_trans (windowA hr hcr hx j).2.1
      (loA_mono hr hc0.le hx0 (show j + 1 ≤ k by omega))
  have hfree : ∃ k ∈ Finset.range (B + 1),
      (¬ ∃ n ∈ Mp, loA p c x0 k ≤ n ∧ n < hiA p c x0 k) ∧
      (¬ ∃ n ∈ Mq, loA q c x0 k ≤ n ∧ n < hiA q c x0 k) := by
    by_contra hcon
    have hsub : Finset.range (B + 1)
        ⊆ (Finset.range (B + 1)).filter (fun k => ∃ n ∈ Mp, loA p c x0 k ≤ n ∧ n < hiA p c x0 k)
          ∪ (Finset.range (B + 1)).filter
              (fun k => ∃ n ∈ Mq, loA q c x0 k ≤ n ∧ n < hiA q c x0 k) := by
      intro k hk
      rw [mem_union, mem_filter, mem_filter]
      by_cases hP : ∃ n ∈ Mp, loA p c x0 k ≤ n ∧ n < hiA p c x0 k
      · exact Or.inl ⟨hk, hP⟩
      by_cases hQ : ∃ n ∈ Mq, loA q c x0 k ≤ n ∧ n < hiA q c x0 k
      · exact Or.inr ⟨hk, hQ⟩
      exact absurd ⟨k, hk, hP, hQ⟩ hcon
    have h3 := le_trans (card_le_card hsub) (card_union_le _ _)
    have h4 := card_hit (loA p c x0) (hiA p c x0) (hord p hp hcp) Mp (B + 1)
    have h5 := card_hit (loA q c x0) (hiA q c x0) (hord q hq hcq) Mq (B + 1)
    rw [Finset.card_range] at h3
    omega
  obtain ⟨k, hk, hfp, hfq⟩ := hfree
  have hk' : k ≤ B := by rw [Finset.mem_range] at hk; omega
  have wp := windowA hp hcp hx k
  have wq := windowA hq hcq hx k
  set y : ℝ := xs c x0 k with hy
  have hyx : x0 ≤ y := (xs_mono hc0.le hx0 k).1
  have hy0 : 0 ≤ y := le_trans hx0 hyx
  set W : ℝ := (sqrt 2 * y + 3 * c) ^ 2 with hW
  set V : ℝ := (y + c) ^ 2 with hV
  have h2b := sqrt2_bounds
  have h22 : sqrt 2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hlog2 : (0.69 : ℝ) < log 2 := lt_trans (by norm_num) log_two_gt_d9
  have hc2 : 0.69 < c ^ 2 := by
    have h1 : log 2 ≤ log (p : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hp)
    have h2 := pow_le_pow_left₀ (sqrt_nonneg _) hcp 2
    rw [sq_sqrt (TwoPrimesEffective.log_pos' hp).le] at h2
    linarith
  have eW : W = 2 * y ^ 2 + 6 * sqrt 2 * y * c + 9 * c ^ 2 := by
    rw [hW]
    have : (sqrt 2 * y + 3 * c) ^ 2 = sqrt 2 ^ 2 * y ^ 2 + 6 * sqrt 2 * y * c + 9 * c ^ 2 := by
      ring
    rw [this, h22]
  have h6 : 4 * (y * c) ≤ 6 * sqrt 2 * (y * c) :=
    mul_le_mul_of_nonneg_right (by linarith [h2b.1]) (mul_nonneg hy0 hc0.le)
  have hgap : 2 * V + 4 < W := by
    have e2 : 2 * V = 2 * y ^ 2 + 4 * y * c + 2 * c ^ 2 := by rw [hV]; ring
    rw [eW, e2]; nlinarith
  have hW0 : 2 * x0 ^ 2 + 1 ≤ W := by
    have h1 := pow_le_pow_left₀ hx0 hyx 2
    have h2 : 0 ≤ 6 * sqrt 2 * y * c := by
      have := sqrt_nonneg (2 : ℝ)
      have := hc0.le
      positivity
    rw [eW]; linarith
  have chain : ∀ (r N : ℕ), 2 ≤ r → sqrt (log r) ≤ c →
      log (50 * D) ^ 2 ≤ 4 * log r * x0 ^ 2 →
      hiA r c x0 B ≤ N → (¬ ∃ n ∈ marked'' r D N θ, loA r c x0 k ≤ n ∧ n < hiA r c x0 k) →
      loA r c x0 k < hiA r c x0 k →
      ∃ a : ℤ, |θ - a / (r : ℝ) ^ ((loA r c x0 k) ^ 2)|
        ≤ 1 / (r : ℝ) ^ ((hiA r c x0 k) ^ 2) := by
    intro r N hr hcr hDr hN hfr hlt'
    have hhiN : hiA r c x0 k ≤ N := le_trans (hiA_mono hc0.le hx0 hk') hN
    have hJ : ∀ n, loA r c x0 k ≤ n → 50 ≤ range' r D n :=
      fun n hn => range_fifty hr (le_trans (by norm_num) hD) hcr hx hDr hn
    refine run_smooth hD hlt' (fun n hn _ => hJ n hn) (fun n hn hlt => ?_) (by omega)
    by_contra hcon
    refine hfr ⟨n, ?_, hn, hlt⟩
    rw [marked'', mem_filter, Finset.mem_range]
    exact ⟨lt_of_lt_of_le hlt hhiN, le_trans (by norm_num) (hJ n hn), not_lt.mp hcon⟩
  have hne : ∀ (r : ℕ), 2 ≤ r → sqrt (log r) ≤ c → loA r c x0 k < hiA r c x0 k := by
    intro r hr hcr
    have w := windowA hr hcr hx k
    refine lt_of_le_of_ne w.1 (fun h => ?_)
    have h1 := w.2.2.1
    have h2 := w.2.2.2.1
    rw [h] at h1
    have h3 := le_trans h2 h1
    change W ≤ V at h3
    have hV0 : 0 ≤ V := sq_nonneg _
    linarith
  obtain ⟨a, ha⟩ := chain p Np hp hcp hDp hNp hfp (hne p hp hcp)
  obtain ⟨a', ha'⟩ := chain q Nq hq hcq hDq hNq hfq (hne q hq hcq)
  set P : ℕ := p ^ ((loA p c x0 k) ^ 2) with hP
  set Q : ℕ := q ^ ((loA q c x0 k) ^ 2) with hQ
  have hPr : (p : ℝ) ^ ((loA p c x0 k) ^ 2) = (P : ℝ) := by rw [hP]; push_cast; rfl
  have hQr : (q : ℝ) ^ ((loA q c x0 k) ^ 2) = (Q : ℝ) := by rw [hQ]; push_cast; rfl
  have hPpos : (0 : ℝ) < P := by
    rw [← hPr]; exact pow_pos (by exact_mod_cast (show 0 < p by omega)) _
  have hQpos : (0 : ℝ) < Q := by
    rw [← hQr]; exact pow_pos (by exact_mod_cast (show 0 < q by omega)) _
  have hPle : (P : ℝ) ≤ exp V := by
    rw [← hPr, pow_eq_exp hp]; apply exp_le_exp.mpr; push_cast; exact wp.2.2.1
  have hQle : (Q : ℝ) ≤ exp V := by
    rw [← hQr, pow_eq_exp hq]; apply exp_le_exp.mpr; push_cast; exact wq.2.2.1
  have hbig : ∀ (r : ℕ), 2 ≤ r → W ≤ ((hiA r c x0 k : ℝ) ^ 2) * log r →
      1 / (r : ℝ) ^ ((hiA r c x0 k) ^ 2) ≤ exp (-W) := by
    intro r hr hw
    have h1 : exp W ≤ (r : ℝ) ^ ((hiA r c x0 k) ^ 2) := by
      rw [pow_eq_exp hr]; apply exp_le_exp.mpr; push_cast; exact hw
    rw [exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (exp_pos _) h1
  have hε1 : |θ - a / (P : ℝ)| ≤ exp (-W) := by
    rw [← hPr]; exact le_trans ha (hbig p hp wp.2.2.2.1)
  have hε2 : |θ - a' / (Q : ℝ)| ≤ exp (-W) := by
    rw [← hQr]; exact le_trans ha' (hbig q hq wq.2.2.2.1)
  have htwo : (2 : ℝ) < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  have hzero : a * (Q : ℤ) - a' * (P : ℤ) = 0 := by
    have hdiff : |(a : ℝ) / P - a' / Q| ≤ 2 * exp (-W) := by
      have t := abs_sub_le ((a : ℝ) / P) θ (a' / Q)
      rw [abs_sub_comm ((a : ℝ) / P) θ] at t
      linarith
    have e : (a : ℝ) / P - a' / Q = ((a * (Q : ℤ) - a' * (P : ℤ) : ℤ) : ℝ) / (P * Q) := by
      push_cast; field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hPpos hQpos), div_le_iff₀ (mul_pos hPpos hQpos)] at hdiff
    have h3 : 2 * exp (-W) * (P * Q) < 1 := by
      have h4 : (P : ℝ) * Q ≤ exp V * exp V := mul_le_mul hPle hQle hQpos.le (exp_pos _).le
      have h5 := mul_le_mul_of_nonneg_left h4
        (show (0 : ℝ) ≤ 2 * exp (-W) by have := exp_pos (-W); linarith)
      refine lt_of_le_of_lt h5 ?_
      have h7 : 2 * exp (-W) * (exp V * exp V) ≤ exp 1 * (exp (-W) * (exp V * exp V)) := by
        have h8 : 0 ≤ exp (-W) * (exp V * exp V) := by positivity
        have := mul_le_mul_of_nonneg_right htwo.le h8
        linarith
      refine lt_of_le_of_lt h7 ?_
      rw [← exp_add, ← exp_add, ← exp_add, exp_lt_one_iff]
      linarith
    have h9 : |((a * (Q : ℤ) - a' * (P : ℤ) : ℤ) : ℝ)| < 1 := lt_of_le_of_lt hdiff h3
    have h10 : |a * (Q : ℤ) - a' * (P : ℤ)| < 1 := by exact_mod_cast h9
    exact Int.abs_lt_one_iff.mp h10
  have hdvd : (P : ℤ) ∣ a := by
    have hcop : IsCoprime (P : ℤ) (Q : ℤ) := by
      apply Nat.Coprime.isCoprime
      exact Nat.Coprime.pow _ _ hpq
    have : (P : ℤ) ∣ a * (Q : ℤ) := ⟨a', by linear_combination hzero⟩
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨z, hz⟩ := hdvd
  refine ⟨z, ?_⟩
  have e : (a : ℝ) / P = z := by
    rw [hz]; push_cast; field_simp
  rw [e] at hε1
  refine le_trans hε1 ?_
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have h1 : exp (-W) * exp 1 ≤ exp (-(2 * x0 ^ 2)) := by
    rw [← exp_add]; apply exp_le_exp.mpr; linarith
  have h2 := mul_le_mul_of_nonneg_left htwo.le (exp_pos (-W)).le
  linarith

/-- **Density to witnesses** with `B = ⌊D² log(17K)/8⌋`. -/
theorem witness_of_density_smooth {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD12 : 12 ≤ D) {K c x0 s : ℝ} (hK : 1 ≤ K)
    (hcp : sqrt (log p) ≤ c) (hcq : sqrt (log q) ≤ c) (hx : 50 * c ≤ x0)
    (hDp : log (50 * D) ^ 2 ≤ 4 * log p * x0 ^ 2) (hDq : log (50 * D) ^ 2 ≤ 4 * log q * x0 ^ 2)
    {B : ℕ} (hB : B = ⌊(D : ℝ) ^ 2 * log (17 * K) / 8⌋₊)
    {X : ℕ} (hX : 64 * exp (xs c x0 (B + 1) ^ 2) ≤ X) (hX100 : 100 ≤ X)
    (V : Finset ℤ) (hV : (X : ℝ) ≤ K * V.card) (a b : ℤ → ℤ)
    (hdiff : ∀ v ∈ V, v = a v - b v)
    (haX : ∀ v ∈ V, |a v| ≤ (X : ℤ)) (hbX : ∀ v ∈ V, |b v| ≤ (X : ℤ))
    (ha : ∀ v ∈ V, Small p s (a v)) (hb : ∀ v ∈ V, Small q s (b v))
    (t : ℤ) (ht : |(t : ℝ)| ≤ exp (2 * x0 ^ 2) / 32) :
    ∃ k : ℤ, |k| ≤ 8 * (X : ℤ) ∧ Small p (4 * (s + 1 / D)) k
      ∧ Small q (4 * (s + 1 / D)) (k - t) := by
  classical
  have hD : 1 ≤ D := le_trans (by norm_num) hD12
  have hc0 : 0 < c := lt_of_lt_of_le (sqrt_log_pos hp) hcp
  have hx00 : 0 ≤ x0 := by linarith
  have hKpos : (0 : ℝ) < K := by linarith
  have hX100r : (100 : ℝ) ≤ X := by exact_mod_cast hX100
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hVpos : (0 : ℝ) < V.card := by
    by_contra h
    have h0 : (V.card : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [h0, mul_zero] at hV
    linarith
  set Np := hiA p c x0 B with hNp
  set Nq := hiA q c x0 B with hNq
  -- the digit sets are short
  have hfit : ∀ r : ℕ, 2 ≤ r → sqrt (log r) ≤ c → (r : ℝ) ^ ((hiA r c x0 B) ^ 2) ≤ X / 64 := by
    intro r hr hcr
    have h1 : (r : ℝ) ^ ((hiA r c x0 B) ^ 2) ≤ exp (xs c x0 (B + 1) ^ 2) := by
      rw [pow_eq_exp hr]
      apply exp_le_exp.mpr
      push_cast
      exact (windowA hr hcr hx B).2.2.2.2
    exact le_trans h1 (by linarith)
  set I' : Finset (ℤ × Idx p D Np × Idx q D Nq) :=
    V ×ˢ (idx p D Np ×ˢ idx q D Nq) with hI'
  set g : ℤ × Idx p D Np × Idx q D Nq → ℤ :=
    fun i => i.1 + val' p i.2.1 - val' q i.2.2 with hg
  have hVne : V.Nonempty := card_pos.mp (by exact_mod_cast hVpos)
  have hIne : I'.Nonempty :=
    hVne.product ((idx_nonempty p D Np).product (idx_nonempty q D Nq))
  have hcard : (I'.card : ℝ)
      = V.card * ((idx p D Np).card * (idx q D Nq).card) := by
    rw [hI', card_product, card_product]; push_cast; ring
  have hmem : ∀ i ∈ I', i.1 ∈ V ∧ i.2.1 ∈ idx p D Np ∧ i.2.2 ∈ idx q D Nq := by
    intro i hi'
    rw [hI', mem_product, mem_product] at hi'
    exact ⟨hi'.1, hi'.2.1, hi'.2.2⟩
  have svp : ∀ j ∈ idx p D Np, 64 * |val' p j| ≤ (X : ℤ) := by
    intro j hj
    have h1 := le_trans (abs_val'_le hp hD hj) (hfit p hp hcp)
    have h2 : 64 * |(val' p j : ℝ)| ≤ X := by linarith
    exact_mod_cast h2
  have svq : ∀ j ∈ idx q D Nq, 64 * |val' q j| ≤ (X : ℤ) := by
    intro j hj
    have h1 := le_trans (abs_val'_le hq hD hj) (hfit q hq hcq)
    have h2 : 64 * |(val' q j : ℝ)| ≤ X := by linarith
    exact_mod_cast h2
  have hvp : ∀ j ∈ idx p D Np, |val' p j| ≤ (X : ℤ) := by
    intro j hj
    have := svp j hj
    have := abs_nonneg (val' p j)
    omega
  have hvq : ∀ j ∈ idx q D Nq, |val' q j| ≤ (X : ℤ) := by
    intro j hj
    have := svq j hj
    have := abs_nonneg (val' q j)
    omega
  set M : ℕ := 2 * X + X / 32 with hM
  have hR : ∀ i ∈ I', |g i| ≤ ((M : ℕ) : ℤ) := by
    intro i hi'
    obtain ⟨h1, h2, h3⟩ := hmem i hi'
    have e1 := hdiff _ h1
    have a1 := haX _ h1
    have a2 := hbX _ h1
    have a3 := svp _ h2
    have a4 := svq _ h3
    have a5 : |val' p i.2.1| + |val' q i.2.2| ≤ ((X / 32 : ℕ) : ℤ) := by
      have := abs_nonneg (val' p i.2.1)
      have := abs_nonneg (val' q i.2.2)
      omega
    have a6 := le_abs_self (val' p i.2.1)
    have a7 := neg_le_abs (val' p i.2.1)
    have a8 := le_abs_self (val' q i.2.2)
    have a9 := neg_le_abs (val' q i.2.2)
    rw [abs_le] at a1 a2
    rw [abs_le]; simp only [hg, hM]; push_cast at a5 ⊢; omega
  -- collisions
  have hcoll : (((I' ×ˢ I').filter (fun x => g x.1 - g x.2 = 0)).card : ℝ)
      ≤ (1 / V.card) * (I'.card : ℝ) ^ 2 := by
    set W := idx p D Np ×ˢ idx q D Nq with hW
    have h1 : ((I' ×ˢ I').filter (fun x => g x.1 - g x.2 = 0)).card ≤ (I' ×ˢ W).card := by
      refine card_le_card_of_injOn (fun x => (x.1, x.2.2)) ?_ ?_
      · intro x hx
        rw [mem_coe, mem_filter, mem_product] at hx
        rw [mem_coe, mem_product]
        refine ⟨hx.1.1, ?_⟩
        have := hx.1.2
        rw [hI', mem_product] at this
        exact this.2
      · intro x hx y hy hxy
        rw [mem_coe, mem_filter] at hx hy
        simp only [Prod.mk.injEq] at hxy
        obtain ⟨e1, e2⟩ := hxy
        have e3 : x.2.1 = y.2.1 := by
          have gx := hx.2
          have gy := hy.2
          have e4 : g x.2 = g y.2 := by rw [e1] at gx; omega
          simp only [hg, e2] at e4
          omega
        exact Prod.ext e1 (Prod.ext e3 e2)
    have h2 : (((I' ×ˢ I').filter (fun x => g x.1 - g x.2 = 0)).card : ℝ)
        ≤ (I'.card : ℝ) * ((idx p D Np).card * (idx q D Nq).card) := by
      have h3 : (I' ×ˢ W).card = I'.card * ((idx p D Np).card * (idx q D Nq).card) := by
        rw [card_product I' W, hW, card_product (idx p D Np)]
      exact_mod_cast le_trans h1 (le_of_eq h3)
    refine le_trans h2 (le_of_eq ?_)
    rw [hcard]; field_simp
  have hsupp : ((I' ×ˢ I').image (fun x => g x.1 - g x.2)).card ≤ 4 * M + 1 := by
    have hsub : (I' ×ˢ I').image (fun x => g x.1 - g x.2)
        ⊆ Icc (-(2 * (M : ℤ))) (2 * (M : ℤ)) := by
      intro y hy
      rw [mem_image] at hy
      obtain ⟨x, hx', rfl⟩ := hy
      rw [mem_product] at hx'
      have a1 := hR _ hx'.1
      have a2 := hR _ hx'.2
      rw [abs_le] at a1 a2
      rw [mem_Icc]; omega
    refine le_trans (card_le_card hsub) ?_
    rw [Int.card_Icc]; omega
  -- the large values of the exponential sum
  set η : ℝ := sqrt (1 / (17 * K)) with hη
  have hηpos : 0 < η := sqrt_pos.mpr (by positivity)
  have hη2 : η ^ 2 = 1 / (17 * K) := sq_sqrt (by positivity)
  have hlogη : -log η = log (17 * K) / 2 := by
    rw [hη, log_sqrt (by positivity), one_div, log_inv]; ring
  have hBlt : (D : ℝ) ^ 2 / 4 * (-log η) < B + 1 := by
    have h := Nat.lt_floor_add_one ((D : ℝ) ^ 2 * log (17 * K) / 8)
    rw [← hB] at h
    rw [hlogη]
    linarith
  have hfactor : ∀ θ : ℝ, S I' g θ = (∑ v ∈ V, e ((v : ℝ) * θ))
      * ((∑ j ∈ idx p D Np, e ((val' p j : ℝ) * θ))
        * (∑ j ∈ idx q D Nq, e ((val' q j : ℝ) * (-θ)))) := by
    intro θ
    rw [S, hI', sum_product, sum_mul]
    refine sum_congr rfl (fun v _ => ?_)
    rw [sum_product, sum_mul_sum, mul_sum]
    refine sum_congr rfl (fun j _ => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun l _ => ?_)
    rw [← e_add, ← e_add]
    congr 1; simp only [hg]; push_cast; ring
  have heven : ∀ θ : ℝ, prodPhi q D Nq (-θ) = prodPhi q D Nq θ := by
    intro θ
    unfold prodPhi
    refine prod_congr rfl (fun n _ => ?_)
    rw [mul_neg, phi_neg]
  have hle1 : ∀ (r N : ℕ) (θ : ℝ), |prodPhi r D N θ| ≤ 1 := by
    intro r N θ
    unfold prodPhi
    rw [abs_prod]
    exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_phi_le_one _ _)
  have hspec : ∀ θ : ℝ, η * I'.card ≤ ‖S I' g θ‖ → 99 / 100 ≤ Real.cos (2 * π * (t * θ)) := by
    intro θ hθ
    have hnorm : ‖S I' g θ‖ ≤ (I'.card : ℝ)
        * (|prodPhi p D Np θ| * |prodPhi q D Nq θ|) := by
      rw [hfactor, norm_mul, norm_mul, sum_idx, sum_idx, heven,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
      have hVs : ‖∑ v ∈ V, e ((v : ℝ) * θ)‖ ≤ (V.card : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have : ∀ v ∈ V, ‖e ((v : ℝ) * θ)‖ = 1 := by
          intro v _
          unfold e
          exact Complex.norm_exp_ofReal_mul_I _
        rw [sum_congr rfl this]; simp
      refine le_trans (mul_le_mul_of_nonneg_right hVs (by positivity)) (le_of_eq ?_)
      rw [hcard]; ring
    have hIpos : (0 : ℝ) < I'.card := by exact_mod_cast card_pos.mpr hIne
    have hboth : η ≤ |prodPhi p D Np θ| * |prodPhi q D Nq θ| := by
      have := le_trans hθ hnorm
      rw [mul_comm η] at this
      exact le_of_mul_le_mul_left this hIpos
    obtain ⟨z, hz⟩ := rigidity_smooth hp hq hpq hD12 hηpos hBlt hcp hcq hx hDp hDq (le_of_eq hNp.symm)
      (le_of_eq hNq.symm) hboth
    set y : ℝ := t * (θ - z) with hy
    have hyabs : |y| ≤ 1 / 64 := by
      rw [hy, abs_mul]
      have h3 := mul_le_mul ht hz (abs_nonneg _) (by positivity)
      refine le_trans h3 (le_of_eq ?_)
      have e1 : exp (2 * x0 ^ 2) * exp (-(2 * x0 ^ 2)) = 1 := by
        rw [← exp_add, add_neg_cancel, exp_zero]
      rw [div_mul_div_comm, e1]; norm_num
    have hcos : Real.cos (2 * π * (t * θ)) = Real.cos (2 * π * y) := by
      have : 2 * π * ((t : ℝ) * θ) = 2 * π * y + ((t * z : ℤ) : ℝ) * (2 * π) := by
        rw [hy]; push_cast; ring
      rw [this, Real.cos_add_int_mul_two_pi]
    rw [hcos]
    refine le_trans ?_ (Real.one_sub_sq_div_two_le_cos)
    have h6 : |2 * π * y| ≤ 1 / 8 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have := mul_le_mul_of_nonneg_left hyabs (show (0 : ℝ) ≤ 2 * π by positivity)
      have hpi : π < 4 := pi_lt_four
      linarith
    have h7 : (2 * π * y) ^ 2 ≤ (1 / 8) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h6 2
    linarith [show ((1 : ℝ) / 8) ^ 2 = 1 / 64 by norm_num]
  have hnum : (1 + 99 / 100) * η ^ 2 * (1 / (V.card : ℝ))
      < (99 / 100) / ((4 * M + 1 : ℕ) : ℝ) := by
    rw [hη2]
    have h1 : 1 / (V.card : ℝ) ≤ K / X := by
      rw [div_le_div_iff₀ hVpos hXpos]; linarith
    have h2 : (1 + 99 / 100) * (1 / (17 * K)) * (1 / (V.card : ℝ))
        ≤ (1 + 99 / 100) * (1 / (17 * K)) * (K / X) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (1 + 99 / 100) * (1 / (17 * K)) * (K / X) = (199 / 1700) / X := by
      field_simp; ring
    have h4 : ((4 * M + 1 : ℕ) : ℝ) ≤ 1627 / 200 * X := by
      have h5 : ((X / 32 : ℕ) : ℝ) ≤ (X : ℝ) / 32 := Nat.cast_div_le
      have h6 : ((4 * M + 1 : ℕ) : ℝ) = 8 * X + 4 * ((X / 32 : ℕ) : ℝ) + 1 := by
        rw [hM]; push_cast; ring
      rw [h6]; linarith
    refine lt_of_le_of_lt (le_trans h2 (le_of_eq h3)) ?_
    have h7 : (0 : ℝ) < ((4 * M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (4 * M)
    rw [div_lt_div_iff₀ hXpos h7]
    linarith
  obtain ⟨i1, m1, i2, m2, i3, m3, i4, m4, hsum⟩ :=
    exists_four' I' g t M (4 * M + 1) η (1 / V.card) (99 / 100) (by norm_num) hIne hR hcoll
      hsupp hspec hnum
  obtain ⟨v1, x1, y1⟩ := hmem i1 m1
  obtain ⟨v2, x2, y2⟩ := hmem i2 m2
  obtain ⟨v3, x3, y3⟩ := hmem i3 m3
  obtain ⟨v4, x4, y4⟩ := hmem i4 m4
  set P : ℤ × Idx p D Np × Idx q D Nq → ℤ := fun i => a i.1 + val' p i.2.1 with hP
  set Q : ℤ × Idx p D Np × Idx q D Nq → ℤ := fun i => b i.1 + val' q i.2.2 with hQ
  have hPQ : ∀ i ∈ I', g i = P i - Q i := by
    intro i hi'
    have := hdiff _ (hmem i hi').1
    simp only [hg, hP, hQ]; omega
  set k := (P i1 - P i2) + (P i3 - P i4) with hk
  have hkt : k - t = (Q i1 - Q i2) + (Q i3 - Q i4) := by
    rw [hPQ _ m1, hPQ _ m2, hPQ _ m3, hPQ _ m4] at hsum
    omega
  have sP : ∀ i ∈ I', Small p (s + 1 / D) (P i) := fun i hi' =>
    (ha _ (hmem i hi').1).add (small_val' hp hD (hmem i hi').2.1)
  have sQ : ∀ i ∈ I', Small q (s + 1 / D) (Q i) := fun i hi' =>
    (hb _ (hmem i hi').1).add (small_val' hq hD (hmem i hi').2.2)
  have e4 : 4 * (s + 1 / (D : ℝ))
      = ((s + 1 / D) + (s + 1 / D)) + ((s + 1 / D) + (s + 1 / D)) := by ring
  refine ⟨k, ?_, ?_, ?_⟩
  · have bound : ∀ i ∈ I', |P i| ≤ 2 * (X : ℤ) := by
      intro i hi'
      have h1 := haX _ (hmem i hi').1
      have h2 := hvp _ (hmem i hi').2.1
      have := abs_add_le (a i.1) (val' p i.2.1)
      simp only [hP]; omega
    have b1 := bound _ m1
    have b2 := bound _ m2
    have b3 := bound _ m3
    have b4 := bound _ m4
    rw [abs_le] at b1 b2 b3 b4
    rw [abs_le, hk]; omega
  · rw [e4, hk]
    exact ((sP _ m1).sub (sP _ m2)).add ((sP _ m3).sub (sP _ m4))
  · rw [e4, hkt]
    exact ((sQ _ m1).sub (sQ _ m2)).add ((sQ _ m3).sub (sQ _ m4))

/-- **The critical density** with `a = D² log 2 / 8`. -/
theorem witness_of_critical_density_smooth {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD12 : 12 ≤ D) {s : ℝ} (t : ℤ)
    (dens : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧ ∃ K : ℝ, 1 ≤ K ∧
      K ≤ ε * (log X) ^ (1 / ((D : ℝ) ^ 2 * log 2 / 8)) ∧
      ∃ V : Finset ℤ, ∃ a b : ℤ → ℤ, (X : ℝ) ≤ K * V.card ∧ (∀ v ∈ V, v = a v - b v) ∧
        (∀ v ∈ V, |a v| ≤ (X : ℤ)) ∧ (∀ v ∈ V, |b v| ≤ (X : ℤ)) ∧
        (∀ v ∈ V, Small p s (a v)) ∧ (∀ v ∈ V, Small q s (b v))) :
    ∃ k : ℤ, Small p (4 * (s + 1 / D)) k ∧ Small q (4 * (s + 1 / D)) (k - t) := by
  classical
  have hD : 1 ≤ D := le_trans (by norm_num) hD12
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set e : ℝ := (D : ℝ) ^ 2 * log 2 / 8 with he
  have he0 : 0 < e := by
    have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have : (0 : ℝ) < (D : ℝ) ^ 2 := pow_pos (by linarith) 2
    exact div_pos (mul_pos this h2) (by norm_num)
  set c : ℝ := max (sqrt (log p)) (sqrt (log q)) with hc
  have hcp : sqrt (log p) ≤ c := le_max_left _ _
  have hcq : sqrt (log q) ≤ c := le_max_right _ _
  have hc0 : 0 < c := lt_of_lt_of_le (sqrt_log_pos hp) hcp
  set x0 : ℝ := max (50 * c) (max (log (50 * D) / (2 * sqrt (log p)))
    (max (log (50 * D) / (2 * sqrt (log q))) (sqrt (log (32 * (1 + |(t : ℝ)|)) / 2)))) with hx0
  have hx : 50 * c ≤ x0 := le_max_left _ _
  have hx00 : 0 ≤ x0 := le_trans (by positivity) hx
  have hx1 : log (50 * D) / (2 * sqrt (log p)) ≤ x0 :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hx2 : log (50 * D) / (2 * sqrt (log q)) ≤ x0 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hx3 : sqrt (log (32 * (1 + |(t : ℝ)|)) / 2) ≤ x0 :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hrange : ∀ r : ℕ, 2 ≤ r → log (50 * D) / (2 * sqrt (log r)) ≤ x0 →
      log (50 * D) ^ 2 ≤ 4 * log r * x0 ^ 2 := by
    intro r hr h
    have hs : 0 < sqrt (log (r : ℝ)) := sqrt_log_pos hr
    rw [div_le_iff₀ (by positivity)] at h
    have h0 : 0 ≤ log (50 * (D : ℝ)) := log_nonneg (by linarith)
    have h1 := pow_le_pow_left₀ h0 h 2
    have e1 : (x0 * (2 * sqrt (log r))) ^ 2 = 4 * log r * x0 ^ 2 := by
      rw [mul_pow, mul_pow, sq_sqrt (TwoPrimesEffective.log_pos' hr).le]; ring
    rwa [e1] at h1
  set M : ℝ := (x0 + 4 * c / (sqrt 2 - 1)) ^ 2 with hM
  have hM0 : 0 < M := by
    have h1 : 0 < 4 * c / (sqrt 2 - 1) :=
      div_pos (by linarith) (by linarith [sqrt2_bounds.1])
    have : 0 < x0 + 4 * c / (sqrt 2 - 1) := by linarith
    exact pow_pos this 2
  have h17 : (0 : ℝ) < 17 ^ e := rpow_pos_of_pos (by norm_num) _
  have hbase : (0 : ℝ) < 1 / (4 * 17 ^ e * M) :=
    div_pos one_pos (mul_pos (mul_pos (by norm_num) h17) hM0)
  set ε : ℝ := (1 / (4 * 17 ^ e * M)) ^ (1 / e) with hε
  have hε0 : 0 < ε := rpow_pos_of_pos hbase _
  obtain ⟨X, hX, K, hK, hKX, V, a, b, hV, hdiff, haX, hbX, ha, hb⟩ := dens ε hε0 4096
  have hXr : (4096 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hlX : 0 ≤ log (X : ℝ) := log_nonneg (by linarith)
  set B : ℕ := ⌊(D : ℝ) ^ 2 * log (17 * K) / 8⌋₊ with hB
  have hK0 : 0 < K := by linarith
  have h17K : (0 : ℝ) < 17 * K := by linarith
  have h2B : (2 : ℝ) ^ B ≤ (17 * K) ^ e := by
    have h1 : (B : ℝ) ≤ (D : ℝ) ^ 2 * log (17 * K) / 8 :=
      Nat.floor_le (div_nonneg (mul_nonneg (by positivity) (log_nonneg (by linarith)))
        (by norm_num))
    have e2 : (2 : ℝ) ^ B = exp (B * log 2) := by
      rw [exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [e2, rpow_def_of_pos h17K]
    apply exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right h1 (log_pos (by norm_num : (1 : ℝ) < 2)).le
    refine le_trans this (le_of_eq ?_)
    rw [he]; ring
  have hKe : K ^ e ≤ (1 / (4 * 17 ^ e * M)) * log X := by
    have h1 := rpow_le_rpow hK0.le hKX he0.le
    have e1 : (ε * (log X) ^ (1 / e)) ^ e = (1 / (4 * 17 ^ e * M)) * log X := by
      rw [mul_rpow hε0.le (rpow_nonneg hlX _), hε, ← rpow_mul hbase.le, ← rpow_mul hlX,
        one_div_mul_cancel he0.ne', rpow_one, rpow_one]
    rwa [e1] at h1
  have hΛ : xs c x0 (B + 1) ^ 2 ≤ log X / 2 := by
    have h1 : xs c x0 (B + 1) ^ 2 ≤ 2 ^ (B + 1) * M := xs_sq_le hc0.le hx00 (B + 1)
    have h2 : (2 : ℝ) ^ B ≤ 17 ^ e * ((1 / (4 * 17 ^ e * M)) * log X) := by
      refine le_trans h2B ?_
      rw [mul_rpow (by norm_num) hK0.le]
      exact mul_le_mul_of_nonneg_left hKe h17.le
    have e3 : 17 ^ e * ((1 / (4 * 17 ^ e * M)) * log X) = log X / (4 * M) := by
      field_simp
    rw [e3] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ 2 * M by linarith)
    have e4 : log (X : ℝ) / (4 * M) * (2 * M) = log X / 2 := by
      field_simp; ring
    have e5 : (2 : ℝ) ^ (B + 1) * M = 2 ^ B * (2 * M) := by rw [pow_succ]; ring
    rw [e4] at h3
    rw [e5] at h1
    exact le_trans h1 h3
  have hXbig : 64 * exp (xs c x0 (B + 1) ^ 2) ≤ X := by
    set r : ℝ := exp (log X / 2) with hr
    have hr2 : r ^ 2 = X := by
      rw [sq, hr, ← exp_add, add_halves, exp_log hXpos]
    have hr0 : 0 < r := exp_pos _
    have hr64 : 64 ≤ r := by
      have h1 : (64 : ℝ) ^ 2 ≤ r ^ 2 := by rw [hr2]; linarith
      exact (pow_le_pow_iff_left₀ (by norm_num) hr0.le two_ne_zero).mp h1
    have h2 : exp (xs c x0 (B + 1) ^ 2) ≤ r := exp_le_exp.mpr hΛ
    have h3 := mul_le_mul_of_nonneg_right hr64 hr0.le
    nlinarith
  have htx : |(t : ℝ)| ≤ exp (2 * x0 ^ 2) / 32 := by
    have ht1 : (1 : ℝ) ≤ 32 * (1 + |(t : ℝ)|) := by
      have := abs_nonneg (t : ℝ); linarith
    have hl : 0 ≤ log (32 * (1 + |(t : ℝ)|)) := log_nonneg ht1
    have h1 := pow_le_pow_left₀ (sqrt_nonneg _) hx3 2
    rw [sq_sqrt (by linarith)] at h1
    have h2 : 32 * (1 + |(t : ℝ)|) ≤ exp (2 * x0 ^ 2) := by
      have := exp_le_exp.mpr (show log (32 * (1 + |(t : ℝ)|)) ≤ 2 * x0 ^ 2 by linarith)
      rwa [exp_log (by linarith)] at this
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
    linarith
  have hX100 : 100 ≤ X := le_trans (by norm_num) hX
  obtain ⟨k, _, hkp, hkq⟩ := witness_of_density_smooth hp hq hpq hD12 (s := s) hK hcp hcq hx
    (hrange p hp hx1) (hrange q hq hx2) hB (X := X) hXbig hX100 V hV a b hdiff haX hbX ha hb
    t htx
  exact ⟨k, hkp, hkq⟩



/-- **Fixed radius** with `B = ⌊D² log(17K)/8⌋`. -/
theorem witness_of_free_heights_smooth {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : Nat.Coprime p q) (hD12 : 12 ≤ D) {K A0 XD β H c C : ℝ} (hK : 1 ≤ K)
    (hcp : sqrt (log p) ≤ c) (hcq : sqrt (log q) ≤ c)
    (hA0 : (50 * c) ^ 2 ≤ A0)
    (hDp : log (50 * D) ^ 2 ≤ 4 * log p * A0) (hDq : log (50 * D) ^ 2 ≤ 4 * log q * A0)
    (h32 : log 32 ≤ 2 * A0)
    {B : ℕ} (hB : B = ⌊(D : ℝ) ^ 2 * log (17 * K) / 8⌋₊)
    (hH : H = 2 * log (8 * D) + 1) (hC : C = 4 * c / (sqrt 2 - 1))
    (hβ : 0 < β) (hβp : β ≤ log p) (hβq : β ≤ log q)
    (hR0 : 8 * exp ((H + log (8 * D)) ^ 2 / (4 * β)) ≤ exp A0)
    (h100 : 100 ≤ exp A0) (hXD : XD ≤ exp A0)
    (dens : ∀ X : ℕ, Free {p, q} D X → XD ≤ X → ∃ V : Finset ℤ, ∃ a b : ℤ → ℤ,
      (X : ℝ) ≤ K * V.card ∧ (∀ v ∈ V, v = a v - b v) ∧
      (∀ v ∈ V, |a v| ≤ (X : ℤ)) ∧ (∀ v ∈ V, |b v| ≤ (X : ℤ)) ∧
      (∀ v ∈ V, Small p (2 / D) (a v)) ∧ (∀ v ∈ V, Small q (2 / D) (b v)))
    (t : ℤ) :
    ∃ k : ℤ, |(k : ℝ)| ≤ 1024 * exp (H + 2 ^ (B + 1) * (sqrt A0 + C) ^ 2)
          * (1 + |(t : ℝ)|) ^ (2 ^ B)
          * exp (2 ^ (B + 2) * C / sqrt 2 * sqrt (log (1 + |(t : ℝ)|)))
      ∧ Small p (12 / D) k ∧ Small q (12 / D) (k - t) := by
  classical
  have hD : 1 ≤ D := le_trans (by norm_num) hD12
  have hne : p ≠ q := by
    intro h
    rw [← h, Nat.coprime_self] at hpq
    omega
  have hcard : ({p, q} : Finset ℕ).card = 2 := card_pair hne
  have hc0 : 0 < c := lt_of_lt_of_le (sqrt_log_pos hp) hcp
  have hA00 : 0 ≤ A0 := le_trans (sq_nonneg _) hA0
  have ht1 : (1 : ℝ) ≤ 1 + |(t : ℝ)| := by
    have := abs_nonneg (t : ℝ); linarith
  have ht0 : (0 : ℝ) < 1 + |(t : ℝ)| := by linarith
  set T : ℝ := log (1 + |(t : ℝ)|) with hT
  have hT0 : 0 ≤ T := log_nonneg ht1
  set x0 : ℝ := sqrt (A0 + T / 2) with hx0def
  have hx0sq : x0 ^ 2 = A0 + T / 2 := sq_sqrt (by linarith)
  have hx00 : 0 ≤ x0 := sqrt_nonneg _
  have hx : 50 * c ≤ x0 := by
    have h1 : (50 * c) ^ 2 ≤ x0 ^ 2 := by rw [hx0sq]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hx00 two_ne_zero).mp h1
  have hAx : A0 ≤ x0 ^ 2 := by rw [hx0sq]; linarith
  set Λ : ℝ := xs c x0 (B + 1) ^ 2 with hΛ
  have hAΛ : A0 ≤ Λ := by
    refine le_trans hAx ?_
    exact pow_le_pow_left₀ hx00 (xs_mono hc0.le hx00 (B + 1)).1 2
  have heA : exp A0 ≤ 64 * exp Λ := by
    have h1 := exp_le_exp.mpr hAΛ
    have := exp_pos Λ
    linarith
  have hS : ∀ l ∈ ({p, q} : Finset ℕ), 2 ≤ l := by
    intro l hl
    rcases mem_insert.mp hl with h | h
    · omega
    · rw [mem_singleton] at h; omega
  have hlog : ∀ l ∈ ({p, q} : Finset ℕ), β ≤ log l := by
    intro l hl
    rcases mem_insert.mp hl with h | h
    · rw [h]; exact hβp
    · rw [mem_singleton] at h; rw [h]; exact hβq
  have hH2 : (({p, q} : Finset ℕ).card : ℝ) * log (8 * D) + 1 = H := by
    rw [hcard, hH]; push_cast; ring
  obtain ⟨X, hX1, hX2, hXfree⟩ := exists_free {p, q} hS hD (R := 64 * exp Λ) hβ hlog
    (by rw [hH2]; exact le_trans hR0 heA)
  rw [hH2] at hX2
  obtain ⟨V, a, b, hV, hdiff, haX, hbX, ha, hb⟩ :=
    dens X hXfree (le_trans hXD (le_trans heA hX1))
  have hX100 : 100 ≤ X := by
    have : (100 : ℝ) ≤ X := le_trans h100 (le_trans heA hX1)
    exact_mod_cast this
  have htx : |(t : ℝ)| ≤ exp (2 * x0 ^ 2) / 32 := by
    have e : exp (2 * x0 ^ 2) = exp (2 * A0) * (1 + |(t : ℝ)|) := by
      have e2 : 2 * x0 ^ 2 = 2 * A0 + T := by rw [hx0sq]; ring
      rw [e2, exp_add, hT, exp_log ht0]
    have h5 : (32 : ℝ) ≤ exp (2 * A0) := by
      have := exp_le_exp.mpr h32
      rwa [exp_log (by norm_num : (0 : ℝ) < 32)] at this
    have h6 := mul_le_mul_of_nonneg_right h5 ht0.le
    rw [e, le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
    linarith
  obtain ⟨k, hk, hkp, hkq⟩ := witness_of_density_smooth hp hq hpq hD12 (s := 2 / D) hK
    hcp hcq hx
    (le_trans hDp (mul_le_mul_of_nonneg_left hAx
      (mul_nonneg (by norm_num) (log_pos' hp).le)))
    (le_trans hDq (mul_le_mul_of_nonneg_left hAx
      (mul_nonneg (by norm_num) (log_pos' hq).le)))
    hB (X := X) hX1 hX100 V hV a b hdiff haX hbX ha hb t htx
  have er : 4 * (2 / (D : ℝ) + 1 / D) = 12 / D := by ring
  rw [er] at hkp hkq
  refine ⟨k, ?_, hkp, hkq⟩
  have h1 : |(k : ℝ)| ≤ 8 * (X : ℝ) := by exact_mod_cast hk
  have hC0 : 0 ≤ C := by
    rw [hC]; exact div_nonneg (by linarith) (by linarith [sqrt2_bounds.1])
  have hsq2 : (0 : ℝ) < sqrt 2 := sqrt_pos.mpr (by norm_num)
  -- the size of the last window
  have hΛle : Λ ≤ 2 ^ (B + 1) * (sqrt A0 + C) ^ 2 + 2 ^ B * T
      + 2 ^ (B + 2) * C / sqrt 2 * sqrt T := by
    have h2 : Λ ≤ 2 ^ (B + 1) * (x0 + C) ^ 2 := by
      rw [hC]; exact xs_sq_le hc0.le hx00 (B + 1)
    have hx0le : x0 ≤ sqrt A0 + sqrt T / sqrt 2 := by
      have e1 : sqrt T / sqrt 2 = sqrt (T / 2) := (sqrt_div hT0 2).symm
      rw [e1]
      have hu := sqrt_nonneg A0
      have hv := sqrt_nonneg (T / 2)
      have e3 : x0 ^ 2 ≤ (sqrt A0 + sqrt (T / 2)) ^ 2 := by
        rw [hx0sq, add_sq, sq_sqrt hA00, sq_sqrt (by linarith : (0 : ℝ) ≤ T / 2)]
        have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu) hv
        linarith
      exact (pow_le_pow_iff_left₀ hx00 (add_nonneg hu hv) two_ne_zero).mp e3
    have h3 : (x0 + C) ^ 2 ≤ (sqrt A0 + C) ^ 2 + T / 2 + 2 * C * (sqrt T / sqrt 2) := by
      have e : (x0 + C) ^ 2 = x0 ^ 2 + 2 * C * x0 + C ^ 2 := by ring
      have e2 : (sqrt A0 + C) ^ 2 = A0 + 2 * C * sqrt A0 + C ^ 2 := by
        rw [add_sq, sq_sqrt hA00]; ring
      have h4 := mul_le_mul_of_nonneg_left hx0le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0)
      rw [e, e2, hx0sq]; nlinarith
    refine le_trans h2 (le_trans (mul_le_mul_of_nonneg_left h3 (by positivity)) (le_of_eq ?_))
    have e4 : (2 : ℝ) ^ (B + 2) = 2 * 2 ^ (B + 1) := by rw [pow_succ]; ring
    have e5 : (2 : ℝ) ^ (B + 1) = 2 * 2 ^ B := by rw [pow_succ]; ring
    rw [e4, e5]; ring
  have epow : (1 + |(t : ℝ)|) ^ (2 ^ B) = exp (2 ^ B * T) := by
    have : (2 : ℝ) ^ B * T = ((2 ^ B : ℕ) : ℝ) * T := by push_cast; ring
    rw [this, exp_nat_mul, hT, exp_log ht0]
  calc |(k : ℝ)| ≤ 8 * (X : ℝ) := h1
    _ ≤ 8 * (2 * exp H * (64 * exp Λ)) := by linarith
    _ = 1024 * exp (H + Λ) := by rw [exp_add]; ring
    _ ≤ 1024 * exp (H + (2 ^ (B + 1) * (sqrt A0 + C) ^ 2 + 2 ^ B * T
          + 2 ^ (B + 2) * C / sqrt 2 * sqrt T)) := by
        refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
        linarith
    _ = _ := by
        rw [epow]
        simp only [exp_add]
        ring

end TwoPrimesSmoothing
