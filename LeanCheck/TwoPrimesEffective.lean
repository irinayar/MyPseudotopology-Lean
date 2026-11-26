import Mathlib

/-!
# Witnesses from a positive density of differences, with explicit constants

For a base `p ≥ 2` the levels have the weights `p^(n^2)`, `n = 0, 1, …`, and `Small p s k` says that
`k` is within `s` of `0` modulo `1` after division by every `p^(n^2)`.

* `abs_digit_le_of_far`: a digit factor whose argument is at least `σ/J` away from the integers has
  modulus at most `exp(-8σ²/3)`.
* `rigidity`: if the two digit products at `θ` both have modulus at least `η`, then `θ` is
  extremely close to an integer.  The two bases only have to be coprime.
* `exists_four`: a Fourier positivity criterion on a large cyclic group.
* `witness_of_density`: if a set `V` of at least `X/K` integers consists of differences `a - b`
  with `a` small for `p` and `b` small for `q`, and `X` is at least `exp(4^(2B+1) A₀)` with
  `B = ⌊12 D² log(50K)⌋`, then every target `|t| ≤ exp(3 A₀)` has a witness `|k| ≤ 8X` at the
  radius `4(s + 1/D)`.

The existence of such sets `V` for two primes (a uniform density estimate) is a hypothesis here.
-/

namespace TwoPrimesEffective

open Finset Real

/-! ## One digit factor -/

/-- The characteristic function of a uniform digit in `[-J, J]`. -/
noncomputable def digit (J : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ Icc (-(J : ℤ)) J, cos (2 * π * j * x)) / (2 * J + 1)

lemma Icc_succ_sum (J : ℕ) (f : ℤ → ℝ) :
    ∑ j ∈ Icc (-((J + 1 : ℕ) : ℤ)) ((J + 1 : ℕ) : ℤ), f j
      = ∑ j ∈ Icc (-(J : ℤ)) J, f j + f ((J : ℤ) + 1) + f (-((J : ℤ) + 1)) := by
  have h : Icc (-((J + 1 : ℕ) : ℤ)) ((J + 1 : ℕ) : ℤ)
      = insert ((J : ℤ) + 1) (insert (-((J : ℤ) + 1)) (Icc (-(J : ℤ)) J)) := by
    ext x
    simp only [mem_insert, mem_Icc]
    omega
  rw [h, sum_insert, sum_insert]
  · ring
  · simp only [mem_Icc]; omega
  · simp only [mem_insert, mem_Icc]; omega

lemma card_digits (J : ℕ) : (Icc (-(J : ℤ)) J).card = 2 * J + 1 := by
  rw [Int.card_Icc]; omega

lemma dirichlet (J : ℕ) (y : ℝ) :
    sin (π * y) * ∑ j ∈ Icc (-(J : ℤ)) J, cos (2 * π * j * y) = sin (π * (2 * J + 1) * y) := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Icc_succ_sum n (fun j => cos (2 * π * j * y))]
    have hneg : cos (2 * π * ((-((n : ℤ) + 1) : ℤ) : ℝ) * y)
        = cos (2 * π * ((n : ℤ) + 1 : ℤ) * y) := by
      rw [← cos_neg]; congr 1; push_cast; ring
    rw [hneg, mul_add, mul_add, ih]
    have key : sin (π * (2 * ((n + 1 : ℕ) : ℝ) + 1) * y) - sin (π * (2 * (n : ℝ) + 1) * y)
        = 2 * (sin (π * y) * cos (2 * π * (((n : ℤ) + 1 : ℤ) : ℝ) * y)) := by
      rw [sin_sub_sin]
      have e1 : (π * (2 * ((n + 1 : ℕ) : ℝ) + 1) * y - π * (2 * (n : ℝ) + 1) * y) / 2
          = π * y := by push_cast; ring
      have e2 : (π * (2 * ((n + 1 : ℕ) : ℝ) + 1) * y + π * (2 * (n : ℝ) + 1) * y) / 2
          = 2 * π * (((n : ℤ) + 1 : ℤ) : ℝ) * y := by push_cast; ring
      rw [e1, e2]; ring
    linarith

lemma digit_sub_int (J : ℕ) (x : ℝ) (z : ℤ) : digit J (x - z) = digit J x := by
  unfold digit
  congr 1
  refine sum_congr rfl (fun j _ => ?_)
  have : 2 * π * (j : ℝ) * (x - z) = 2 * π * j * x - ((j * z : ℤ) : ℝ) * (2 * π) := by
    push_cast; ring
  rw [this, cos_sub_int_mul_two_pi]

lemma digit_neg (J : ℕ) (x : ℝ) : digit J (-x) = digit J x := by
  unfold digit
  congr 1
  refine sum_congr rfl (fun j _ => ?_)
  rw [← cos_neg]; congr 1; ring

lemma digit_abs_arg (J : ℕ) (x : ℝ) : digit J |x| = digit J x := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, digit_neg]

lemma abs_digit_le_one (J : ℕ) (x : ℝ) : |digit J x| ≤ 1 := by
  unfold digit
  have hM : (0 : ℝ) < 2 * J + 1 := by positivity
  rw [abs_div, abs_of_pos hM, div_le_one hM]
  refine le_trans (abs_sum_le_sum_abs _ _) ?_
  refine le_trans (sum_le_sum (fun j _ => abs_cos_le_one _)) ?_
  rw [sum_const, card_digits]
  simp

lemma sum_sq (J : ℕ) :
    ∑ j ∈ Icc (-(J : ℤ)) J, (j : ℝ) ^ 2 = J * (J + 1) * (2 * J + 1) / 3 := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Icc_succ_sum n (fun j => (j : ℝ) ^ 2), ih]
    push_cast; ring

/-- Arguments away from `0`. -/
lemma digit_half {J : ℕ} {y : ℝ} (h1 : 1 / (2 * (J : ℝ) + 1) ≤ y) (h2 : y ≤ 1 / 2) :
    |digit J y| ≤ 1 / 2 := by
  have hM : (0 : ℝ) < 2 * J + 1 := by positivity
  have hy : 0 < y := lt_of_lt_of_le (by positivity) h1
  have hpi := pi_pos
  have hs : 2 * y ≤ sin (π * y) := by
    have := mul_le_sin (x := π * y) (by positivity) (by nlinarith)
    have e : 2 / π * (π * y) = 2 * y := by field_simp
    linarith
  have hspos : 0 < sin (π * y) := by linarith
  have hD := dirichlet J y
  have habs : sin (π * y) * |∑ j ∈ Icc (-(J : ℤ)) J, cos (2 * π * j * y)| ≤ 1 := by
    rw [← abs_of_pos hspos, ← abs_mul, hD]
    exact abs_sin_le_one _
  unfold digit
  rw [abs_div, abs_of_pos hM, div_le_iff₀ hM]
  have hyM : 1 ≤ y * (2 * (J : ℝ) + 1) := by
    rwa [div_le_iff₀ hM] at h1
  have hS := abs_nonneg (∑ j ∈ Icc (-(J : ℤ)) J, cos (2 * π * j * y))
  have h3 : 2 * y * |∑ j ∈ Icc (-(J : ℤ)) J, cos (2 * π * j * y)| ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right hs hS) habs
  nlinarith [mul_le_mul_of_nonneg_right hyM hS]

/-- Arguments near `0`. -/
lemma digit_near {J : ℕ} {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1 / (2 * (J : ℝ) + 1)) :
    0 ≤ digit J y ∧ digit J y ≤ 1 - 8 / 3 * (J * (J + 1)) * y ^ 2 := by
  have hM : (0 : ℝ) < 2 * J + 1 := by positivity
  have hyM : y * (2 * (J : ℝ) + 1) ≤ 1 := by
    rwa [le_div_iff₀ hM] at h1
  have hpi := pi_pos
  constructor
  · unfold digit
    refine div_nonneg ?_ hM.le
    rcases eq_or_lt_of_le h0 with hy | hy
    · subst hy
      exact sum_nonneg (fun j _ => by simp)
    · rcases eq_or_lt_of_le (Nat.zero_le J) with hJ | hJ
      · subst hJ; simp
      have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      have hylt : y < 1 := by nlinarith
      have hspos : 0 < sin (π * y) :=
        sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
      have hnum : 0 ≤ sin (π * (2 * J + 1) * y) := by
        refine sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_
        have e : π * (2 * (J : ℝ) + 1) * y = π * (y * (2 * J + 1)) := by ring
        rw [e]
        calc π * (y * (2 * J + 1)) ≤ π * 1 := mul_le_mul_of_nonneg_left hyM hpi.le
          _ = π := mul_one _
      rw [← dirichlet J y] at hnum
      exact nonneg_of_mul_nonneg_right hnum hspos
  · unfold digit
    rw [div_le_iff₀ hM]
    have hterm : ∀ j ∈ Icc (-(J : ℤ)) J,
        cos (2 * π * j * y) ≤ 1 - 8 * y ^ 2 * (j : ℝ) ^ 2 := by
      intro j hj
      rw [mem_Icc] at hj
      have hjJ : |(j : ℝ)| ≤ J := by
        rw [abs_le]
        exact ⟨by exact_mod_cast hj.1, by exact_mod_cast hj.2⟩
      have hx0 : 0 ≤ π * |(j : ℝ)| * y := by positivity
      have hjy : |(j : ℝ)| * y ≤ 1 / 2 := by
        have : |(j : ℝ)| * y ≤ J * y := mul_le_mul_of_nonneg_right hjJ h0
        nlinarith
      have hx1 : π * |(j : ℝ)| * y ≤ π / 2 := by
        have := mul_le_mul_of_nonneg_left hjy hpi.le
        nlinarith
      have hs := mul_le_sin hx0 hx1
      have e : 2 / π * (π * |(j : ℝ)| * y) = 2 * |(j : ℝ)| * y := by field_simp
      rw [e] at hs
      have hs2 : (2 * |(j : ℝ)| * y) ^ 2 ≤ sin (π * |(j : ℝ)| * y) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hs 2
      have hc : cos (2 * π * j * y) = 1 - 2 * sin (π * |(j : ℝ)| * y) ^ 2 := by
        have : cos (2 * π * j * y) = cos (2 * (π * |(j : ℝ)| * y)) := by
          rcases abs_cases (j : ℝ) with ⟨h, _⟩ | ⟨h, _⟩
          · rw [h]; congr 1; ring
          · rw [h, ← cos_neg]; congr 1; ring
        rw [this, cos_two_mul, cos_sq']; ring
      have hsq : (2 * |(j : ℝ)| * y) ^ 2 = 4 * (j : ℝ) ^ 2 * y ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs]; ring
      rw [hc]; nlinarith
    refine le_trans (sum_le_sum hterm) ?_
    rw [sum_sub_distrib, ← mul_sum, sum_sq, sum_const, card_digits]
    simp only [nsmul_eq_mul, mul_one]
    push_cast
    apply le_of_eq; ring

/-- A digit factor whose argument stays `σ/J` away from the integers. -/
lemma abs_digit_le_of_far {J : ℕ} {σ x : ℝ} (hJ : 1 ≤ J) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 2)
    (h : σ / J ≤ |x - round x|) : |digit J x| ≤ exp (-(8 / 3 * σ ^ 2)) := by
  have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  rw [← digit_sub_int J x (round x), ← digit_abs_arg]
  set y := |x - (round x : ℝ)| with hy
  have hy0 : 0 ≤ y := abs_nonneg _
  have hy2 : y ≤ 1 / 2 := abs_sub_round x
  have hσy : σ ≤ y * J := by
    rwa [div_le_iff₀ (by positivity)] at h
  rcases le_or_gt y (1 / (2 * (J : ℝ) + 1)) with hc | hc
  · obtain ⟨hn, hu⟩ := digit_near hy0 hc
    rw [abs_of_nonneg hn]
    refine le_trans hu ?_
    refine le_trans ?_ (add_one_le_exp _)
    have h1 : σ ^ 2 ≤ (y * J) ^ 2 := pow_le_pow_left₀ hσ0 hσy 2
    have h2 : (y * J) ^ 2 ≤ J * (J + 1) * y ^ 2 := by
      have : (0 : ℝ) ≤ J * y ^ 2 := by positivity
      nlinarith
    nlinarith
  · refine le_trans (digit_half hc.le hy2) ?_
    have h1 : σ ^ 2 ≤ 1 / 4 := by nlinarith
    have h2 : (1 : ℝ) / 2 = exp (-log 2) := by
      rw [exp_neg, exp_log (by norm_num), one_div]
    rw [h2]
    apply exp_le_exp.mpr
    have : (0.69 : ℝ) < log 2 := lt_trans (by norm_num) log_two_gt_d9
    nlinarith

/-! ## One chain of levels -/

/-- The digit range of level `n`. -/
def range' (p D n : ℕ) : ℕ := p ^ (2 * n + 1) / (2 * D)

/-- The product of the digit factors of the levels below `N`. -/
noncomputable def prodDigit (p D N : ℕ) (θ : ℝ) : ℝ :=
  ∏ n ∈ Finset.range N, digit (range' p D n) ((p : ℝ) ^ (n ^ 2) * θ)

/-- The levels at which the argument is visibly away from the integers. -/
noncomputable def marked (p D N : ℕ) (θ : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun n => 1 ≤ range' p D n ∧
    (1 / (8 * (D : ℝ))) / (range' p D n)
      ≤ |(p : ℝ) ^ (n ^ 2) * θ - round ((p : ℝ) ^ (n ^ 2) * θ)|)

lemma card_marked_le {p D N : ℕ} {θ η : ℝ} (hD : 1 ≤ D) (hη : 0 < η)
    (h : η ≤ |prodDigit p D N θ|) : ((marked p D N θ).card : ℝ) ≤ 24 * D ^ 2 * (-log η) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set σ : ℝ := 1 / (8 * (D : ℝ)) with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hσ2 : σ ≤ 1 / 2 := by
    rw [hσ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hprod : |prodDigit p D N θ| ≤ exp (-(8 / 3 * σ ^ 2) * (marked p D N θ).card) := by
    unfold prodDigit
    rw [abs_prod]
    have hsub : marked p D N θ ⊆ Finset.range N := filter_subset _ _
    rw [← prod_sdiff hsub]
    have h1 : ∏ n ∈ Finset.range N \ marked p D N θ,
        |digit (range' p D n) ((p : ℝ) ^ (n ^ 2) * θ)| ≤ 1 :=
      prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_digit_le_one _ _)
    have h2 : ∏ n ∈ marked p D N θ, |digit (range' p D n) ((p : ℝ) ^ (n ^ 2) * θ)|
        ≤ ∏ _n ∈ marked p D N θ, exp (-(8 / 3 * σ ^ 2)) := by
      refine prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun n hn => ?_)
      rw [marked, mem_filter] at hn
      exact abs_digit_le_of_far hn.2.1 hσ0 hσ2 hn.2.2
    refine le_trans (mul_le_mul h1 h2 (prod_nonneg (fun _ _ => abs_nonneg _)) zero_le_one) ?_
    rw [one_mul, prod_const, ← exp_nat_mul]
    apply le_of_eq; congr 1; ring
  have hlog := log_le_log hη (le_trans h hprod)
  rw [log_exp] at hlog
  have e : 8 / 3 * σ ^ 2 = 1 / (24 * (D : ℝ) ^ 2) := by
    rw [hσ]; field_simp; ring
  rw [e] at hlog
  have h24 : (0 : ℝ) < 24 * (D : ℝ) ^ 2 := by positivity
  have : ((marked p D N θ).card : ℝ) / (24 * (D : ℝ) ^ 2) ≤ -log η := by
    have e2 : -(1 / (24 * (D : ℝ) ^ 2)) * ((marked p D N θ).card : ℝ)
        = -(((marked p D N θ).card : ℝ) / (24 * (D : ℝ) ^ 2)) := by ring
    rw [e2] at hlog
    linarith
  rw [div_le_iff₀ h24] at this
  linarith

/-- Along a run of unmarked levels the phase only gets multiplied: no wrap-around occurs. -/
lemma run {p D n1 n2 : ℕ} {θ : ℝ} (hD : 1 ≤ D) (h12 : n1 ≤ n2)
    (hJ : ∀ n, n1 ≤ n → n < n2 → 1 ≤ range' p D n)
    (hu : ∀ n, n1 ≤ n → n < n2 →
      |(p : ℝ) ^ (n ^ 2) * θ - round ((p : ℝ) ^ (n ^ 2) * θ)|
        < (1 / (8 * (D : ℝ))) / (range' p D n)) (hp : 0 < p) :
    ∃ a : ℤ, |θ - a / (p : ℝ) ^ (n1 ^ 2)| ≤ 1 / (2 * (p : ℝ) ^ (n2 ^ 2)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set x : ℕ → ℝ := fun n => (p : ℝ) ^ (n ^ 2) * θ with hx
  set a : ℤ := round (x n1) with ha
  set ξ : ℝ := x n1 - a with hξ
  have main : ∀ n, n1 ≤ n → n ≤ n2 → ∃ c : ℤ,
      x n - c = (p : ℝ) ^ (n ^ 2) / (p : ℝ) ^ (n1 ^ 2) * ξ ∧ |x n - c| ≤ 1 / 2 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro _
      refine ⟨a, ?_, abs_sub_round _⟩
      rw [div_self (by positivity), one_mul]
    | succ n hn ih =>
      intro hle
      obtain ⟨c, hc, hhalf⟩ := ih (by omega)
      have hlt : n < n2 := by omega
      have hJn := hJ n hn hlt
      have hun := hu n hn hlt
      -- the unmarked bound for the representative `x n - c`
      have hJr : (1 : ℝ) ≤ (range' p D n : ℝ) := by exact_mod_cast hJn
      have hsmall : (1 / (8 * (D : ℝ))) / (range' p D n) ≤ 1 / 8 := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (1 : ℝ) ≤ D * range' p D n := one_le_mul_of_one_le_of_one_le hD' hJr
        nlinarith
      have hround : (round (x n) : ℤ) = c := by
        have h1 : |x n - round (x n)| < 1 / 8 := lt_of_lt_of_le hun hsmall
        have h2 : |((round (x n) : ℤ) : ℝ) - c| < 1 := by
          have t := abs_sub_le ((round (x n) : ℤ) : ℝ) (x n) c
          rw [abs_sub_comm ((round (x n) : ℤ) : ℝ) (x n)] at t
          linarith
        have h3 : |round (x n) - c| < 1 := by exact_mod_cast h2
        have h4 := Int.abs_lt_one_iff.mp h3
        omega
      have hξn : |x n - c| < (1 / (8 * (D : ℝ))) / (range' p D n) := by
        have := hun
        rwa [show (p : ℝ) ^ (n ^ 2) * θ = x n from rfl, hround] at this
      -- the size of the multiplier
      have hmul : p ^ (2 * n + 1) ≤ 4 * D * range' p D n := by
        have h1 := Nat.lt_mul_div_succ (p ^ (2 * n + 1)) (show 0 < 2 * D by omega)
        have h2 : 2 * D * (range' p D n + 1) ≤ 4 * D * range' p D n := by
          have : D ≤ D * range' p D n := Nat.le_mul_of_pos_right D hJn
          nlinarith
        exact le_of_lt (lt_of_lt_of_le h1 h2)
      have hmul' : (p : ℝ) ^ (2 * n + 1) ≤ 4 * D * range' p D n := by exact_mod_cast hmul
      have hstep : x (n + 1) = (p : ℝ) ^ (2 * n + 1) * x n := by
        show (p : ℝ) ^ ((n + 1) ^ 2) * θ = (p : ℝ) ^ (2 * n + 1) * ((p : ℝ) ^ (n ^ 2) * θ)
        rw [← mul_assoc, ← pow_add]; congr 2; ring
      have hpow : (p : ℝ) ^ ((n + 1) ^ 2) = (p : ℝ) ^ (2 * n + 1) * (p : ℝ) ^ (n ^ 2) := by
        rw [← pow_add]; congr 1; ring
      refine ⟨(p : ℤ) ^ (2 * n + 1) * c, ?_, ?_⟩
      · have e : x (n + 1) - (((p : ℤ) ^ (2 * n + 1) * c : ℤ) : ℝ)
            = (p : ℝ) ^ (2 * n + 1) * (x n - c) := by
          rw [hstep]; push_cast; ring
        rw [e, hc, hpow]; ring
      · have e : x (n + 1) - (((p : ℤ) ^ (2 * n + 1) * c : ℤ) : ℝ)
            = (p : ℝ) ^ (2 * n + 1) * (x n - c) := by
          rw [hstep]; push_cast; ring
        rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ (2 * n + 1))]
        have hJ0 : (0 : ℝ) < range' p D n := by linarith
        have := mul_le_mul hmul' hξn.le (abs_nonneg _) (by positivity)
        refine le_trans this ?_
        have e2 : 4 * (D : ℝ) * range' p D n * ((1 / (8 * (D : ℝ))) / (range' p D n)) = 1 / 2 := by
          field_simp; ring
        rw [e2]
  obtain ⟨c, hc, hhalf⟩ := main n2 h12 le_rfl
  refine ⟨a, ?_⟩
  rw [hc, abs_mul, abs_of_pos (by positivity :
    (0 : ℝ) < (p : ℝ) ^ (n2 ^ 2) / (p : ℝ) ^ (n1 ^ 2))] at hhalf
  have e : θ - a / (p : ℝ) ^ (n1 ^ 2) = ξ / (p : ℝ) ^ (n1 ^ 2) := by
    rw [hξ]
    show _ = ((p : ℝ) ^ (n1 ^ 2) * θ - a) / (p : ℝ) ^ (n1 ^ 2)
    field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ (n1 ^ 2))]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (p : ℝ) ^ (n2 ^ 2) / (p : ℝ) ^ (n1 ^ 2) * |ξ|
      = (p : ℝ) ^ (n2 ^ 2) * |ξ| / (p : ℝ) ^ (n1 ^ 2) := by ring
  rw [h2, div_le_iff₀ (by positivity)] at hhalf
  nlinarith

/-! ## The windows -/

/-- First level of the window `k`. -/
noncomputable def lo (p : ℕ) (A0 : ℝ) (k : ℕ) : ℕ := ⌈(2 : ℝ) ^ k * sqrt (A0 / log p)⌉₊

/-- Last level of the window `k`. -/
noncomputable def hi (p : ℕ) (A0 : ℝ) (k : ℕ) : ℕ := ⌊(2 : ℝ) ^ (k + 1) * sqrt (A0 / log p)⌋₊

lemma log_pos' {p : ℕ} (hp : 2 ≤ p) : 0 < log (p : ℝ) :=
  log_pos (by exact_mod_cast (show 1 < p by omega))

lemma ten_le_sqrt {p : ℕ} (hp : 2 ≤ p) {A0 : ℝ} (h : 100 * log p ≤ A0) :
    10 ≤ sqrt (A0 / log p) := by
  have hl := log_pos' hp
  have : (10 : ℝ) ^ 2 ≤ A0 / log p := by
    rw [le_div_iff₀ hl]; linarith
  calc (10 : ℝ) = sqrt (10 ^ 2) := (sqrt_sq (by norm_num)).symm
    _ ≤ _ := sqrt_le_sqrt this

lemma pow_eq_exp {p : ℕ} (hp : 2 ≤ p) (m : ℕ) : (p : ℝ) ^ m = exp (m * log p) := by
  have : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [exp_nat_mul, exp_log this]

/-- Facts about the levels of one window. -/
lemma window {p : ℕ} (hp : 2 ≤ p) {A0 : ℝ} (h : 100 * log p ≤ A0) (k : ℕ) :
    lo p A0 k ≤ hi p A0 k ∧ hi p A0 k ≤ lo p A0 (k + 1) ∧
    ((lo p A0 k : ℝ) ^ 2) * log p ≤ 121 / 100 * (4 ^ k * A0) ∧
    361 / 100 * (4 ^ k * A0) ≤ ((hi p A0 k : ℝ) ^ 2) * log p ∧
    ((hi p A0 k : ℝ) ^ 2) * log p ≤ 4 ^ (k + 1) * A0 := by
  have hl := log_pos' hp
  have hA : 0 ≤ A0 := le_trans (by positivity) h
  set s0 := sqrt (A0 / log p) with hs0
  have h10 : 10 ≤ s0 := ten_le_sqrt hp h
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  set s := (2 : ℝ) ^ k * s0 with hs
  have hs10 : 10 ≤ s := le_trans h10 (le_mul_of_one_le_left (by linarith) h2k)
  have hsq : s ^ 2 * log p = 4 ^ k * A0 := by
    have e : s0 ^ 2 = A0 / log p := sq_sqrt (div_nonneg hA hl.le)
    have e4 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [hs, mul_pow, e, e4]; field_simp
  have hlo1 : s ≤ (lo p A0 k : ℝ) := Nat.le_ceil _
  have hlo2 : (lo p A0 k : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith)
  have hs2 : (2 : ℝ) ^ (k + 1) * s0 = 2 * s := by rw [hs, pow_succ]; ring
  have hhi1 : (hi p A0 k : ℝ) ≤ 2 * s := by
    unfold hi; rw [← hs0, hs2]; exact Nat.floor_le (by linarith)
  have hhi2 : 2 * s - 1 < (hi p A0 k : ℝ) := by
    unfold hi; rw [← hs0, hs2]; exact Nat.sub_one_lt_floor _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (lo p A0 k : ℝ) ≤ hi p A0 k := by linarith
    exact_mod_cast this
  · have h1 : 2 * s ≤ (lo p A0 (k + 1) : ℝ) := by
      unfold lo; rw [← hs0, hs2]; exact Nat.le_ceil _
    have : (hi p A0 k : ℝ) ≤ lo p A0 (k + 1) := le_trans hhi1 h1
    exact_mod_cast this
  · have h1 : (lo p A0 k : ℝ) ≤ 11 / 10 * s := by linarith
    have h2 : (lo p A0 k : ℝ) ^ 2 ≤ (11 / 10 * s) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
    have := mul_le_mul_of_nonneg_right h2 hl.le
    nlinarith
  · have h1 : 19 / 10 * s ≤ (hi p A0 k : ℝ) := by linarith
    have h2 : (19 / 10 * s) ^ 2 ≤ (hi p A0 k : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h1 2
    have := mul_le_mul_of_nonneg_right h2 hl.le
    nlinarith
  · have h2 : (hi p A0 k : ℝ) ^ 2 ≤ (2 * s) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hhi1 2
    have := mul_le_mul_of_nonneg_right h2 hl.le
    have e4 : (4 : ℝ) ^ (k + 1) * A0 = 4 * (4 ^ k * A0) := by ring
    nlinarith

lemma lo_mono {p : ℕ} {A0 : ℝ} {j k : ℕ} (h : j ≤ k) : lo p A0 j ≤ lo p A0 k :=
  Nat.ceil_le_ceil (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) h) (sqrt_nonneg _))

/-- Levels inside a window have a nonzero digit range. -/
lemma range_pos {p D : ℕ} (hp : 2 ≤ p) (hD : 1 ≤ D) {A0 : ℝ} (h : 100 * log p ≤ A0)
    (hD2 : log (2 * D) ^ 2 ≤ 4 * log p * A0) {k n : ℕ} (hn : lo p A0 k ≤ n) :
    1 ≤ range' p D n := by
  have hl := log_pos' hp
  have hA : 0 ≤ A0 := le_trans (by positivity) h
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h0 : sqrt (A0 / log p) ≤ (n : ℝ) := by
    have h1 : sqrt (A0 / log p) ≤ (lo p A0 0 : ℝ) := by
      unfold lo; simp only [pow_zero, one_mul]; exact Nat.le_ceil _
    have h2 : lo p A0 0 ≤ n := le_trans (lo_mono (Nat.zero_le k)) hn
    exact le_trans h1 (by exact_mod_cast h2)
  have h1 : A0 ≤ (n : ℝ) ^ 2 * log p := by
    have := pow_le_pow_left₀ (sqrt_nonneg _) h0 2
    rw [sq_sqrt (div_nonneg hA hl.le), div_le_iff₀ hl] at this
    exact this
  have h2 : log (2 * D) ≤ 2 * n * log p := by
    have h3 : log (2 * (D : ℝ)) ^ 2 ≤ (2 * n * log p) ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 4 * log p by positivity)
      nlinarith
    have h4 : 0 ≤ log (2 * (D : ℝ)) := log_nonneg (by linarith)
    exact (pow_le_pow_iff_left₀ h4 (by positivity) two_ne_zero).mp h3
  have h5 : (2 * D : ℝ) ≤ (p : ℝ) ^ (2 * n + 1) := by
    rw [pow_eq_exp hp, ← exp_log (show (0 : ℝ) < 2 * D by positivity)]
    apply exp_le_exp.mpr
    push_cast
    nlinarith
  have h6 : 2 * D ≤ p ^ (2 * n + 1) := by exact_mod_cast h5
  exact (Nat.one_le_div_iff (by omega)).mpr h6

/-- At most `B` marked levels spoil at most `B` of the windows. -/
lemma card_bad {p : ℕ} {A0 : ℝ} (hp : 2 ≤ p) (h : 100 * log p ≤ A0) (S : Finset ℕ) (K : ℕ) :
    ((Finset.range K).filter (fun k => ∃ n ∈ S, lo p A0 k ≤ n ∧ n < hi p A0 k)).card
      ≤ S.card := by
  classical
  set T := (Finset.range K).filter (fun k => ∃ n ∈ S, lo p A0 k ≤ n ∧ n < hi p A0 k) with hT
  have hex : ∀ k ∈ T, ∃ n ∈ S, lo p A0 k ≤ n ∧ n < hi p A0 k := by
    intro k hk; rw [hT, mem_filter] at hk; exact hk.2
  choose f hfS hf1 hf2 using hex
  have key : ∀ j k (hj : j ∈ T) (hk : k ∈ T), j < k → f j hj < f k hk := by
    intro j k hj hk hlt
    have h1 : hi p A0 j ≤ lo p A0 k :=
      le_trans (window hp h j).2.1 (lo_mono (show j + 1 ≤ k by omega))
    exact lt_of_lt_of_le (hf2 j hj) (le_trans h1 (hf1 k hk))
  have hinj : Set.InjOn (fun k : {x // x ∈ T} => f k.1 k.2) (T.attach : Set {x // x ∈ T}) := by
    intro x _ y _ hxy
    rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
    · exact absurd hxy (ne_of_lt (key _ _ x.2 y.2 hlt))
    · exact Subtype.ext heq
    · exact absurd hxy.symm (ne_of_lt (key _ _ y.2 x.2 hgt))
  have := card_le_card_of_injOn (s := T.attach) (t := S)
    (fun k : {x // x ∈ T} => f k.1 k.2) (fun k _ => hfS k.1 k.2) hinj
  rwa [card_attach] at this

/-- **Rigidity.** If both digit products at `θ` have modulus at least `η`, then `θ` is extremely
close to an integer. -/
theorem rigidity {p q D B Np Nq : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) {η A0 θ : ℝ} (hη : 0 < η) (hB : 24 * (D : ℝ) ^ 2 * (-log η) < B + 1)
    (hAp : 100 * log p ≤ A0) (hAq : 100 * log q ≤ A0)
    (hDp : log (2 * D) ^ 2 ≤ 4 * log p * A0) (hDq : log (2 * D) ^ 2 ≤ 4 * log q * A0)
    (hNp : hi p A0 (2 * B) ≤ Np) (hNq : hi q A0 (2 * B) ≤ Nq)
    (h1 : η ≤ |prodDigit p D Np θ|) (h2 : η ≤ |prodDigit q D Nq θ|) :
    ∃ z : ℤ, |θ - z| ≤ exp (-(36 / 10) * A0) / 2 := by
  classical
  have hA : 0 ≤ A0 := le_trans (mul_nonneg (by norm_num) (log_pos' hp).le) hAp
  set Mp := marked p D Np θ with hMp
  set Mq := marked q D Nq θ with hMq
  have hcp : Mp.card ≤ B := by
    have h := lt_of_le_of_lt (card_marked_le hD hη h1) hB
    have : Mp.card < B + 1 := by exact_mod_cast h
    omega
  have hcq : Mq.card ≤ B := by
    have h := lt_of_le_of_lt (card_marked_le hD hη h2) hB
    have : Mq.card < B + 1 := by exact_mod_cast h
    omega
  -- a window without marked levels of either chain
  have hfree : ∃ k ∈ Finset.range (2 * B + 1),
      (¬ ∃ n ∈ Mp, lo p A0 k ≤ n ∧ n < hi p A0 k) ∧
      (¬ ∃ n ∈ Mq, lo q A0 k ≤ n ∧ n < hi q A0 k) := by
    by_contra hcon
    have hsub : Finset.range (2 * B + 1)
        ⊆ (Finset.range (2 * B + 1)).filter (fun k => ∃ n ∈ Mp, lo p A0 k ≤ n ∧ n < hi p A0 k)
          ∪ (Finset.range (2 * B + 1)).filter
              (fun k => ∃ n ∈ Mq, lo q A0 k ≤ n ∧ n < hi q A0 k) := by
      intro k hk
      rw [mem_union, mem_filter, mem_filter]
      by_cases hP : ∃ n ∈ Mp, lo p A0 k ≤ n ∧ n < hi p A0 k
      · exact Or.inl ⟨hk, hP⟩
      by_cases hQ : ∃ n ∈ Mq, lo q A0 k ≤ n ∧ n < hi q A0 k
      · exact Or.inr ⟨hk, hQ⟩
      exact absurd ⟨k, hk, hP, hQ⟩ hcon
    have h3 := le_trans (card_le_card hsub) (card_union_le _ _)
    have h4 := card_bad hp hAp Mp (2 * B + 1)
    have h5 := card_bad hq hAq Mq (2 * B + 1)
    rw [Finset.card_range] at h3
    omega
  obtain ⟨k, hk, hfp, hfq⟩ := hfree
  have hk' : k ≤ 2 * B := by rw [Finset.mem_range] at hk; omega
  -- the run for one chain
  have chain : ∀ (r N : ℕ), 2 ≤ r → 100 * log r ≤ A0 → log (2 * D) ^ 2 ≤ 4 * log r * A0 →
      hi r A0 (2 * B) ≤ N → (¬ ∃ n ∈ marked r D N θ, lo r A0 k ≤ n ∧ n < hi r A0 k) →
      ∃ a : ℤ, |θ - a / (r : ℝ) ^ ((lo r A0 k) ^ 2)|
        ≤ 1 / (2 * (r : ℝ) ^ ((hi r A0 k) ^ 2)) := by
    intro r N hr hAr hDr hN hfr
    have hhiN : hi r A0 k ≤ N := by
      refine le_trans ?_ hN
      exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by omega)) (sqrt_nonneg _))
    refine run hD (window hr hAr k).1 (fun n hn _ => range_pos hr hD hAr hDr hn)
      (fun n hn hlt => ?_) (by omega)
    by_contra hcon
    refine hfr ⟨n, ?_, hn, hlt⟩
    rw [marked, mem_filter, Finset.mem_range]
    exact ⟨lt_of_lt_of_le hlt hhiN, range_pos hr hD hAr hDr hn, not_lt.mp hcon⟩
  obtain ⟨a, ha⟩ := chain p Np hp hAp hDp hNp hfp
  obtain ⟨a', ha'⟩ := chain q Nq hq hAq hDq hNq hfq
  have wp := window hp hAp k
  have wq := window hq hAq k
  set A : ℝ := 4 ^ k * A0 with hAdef
  have hAA0 : A0 ≤ A := le_mul_of_one_le_left hA (one_le_pow₀ (by norm_num))
  have hA100 : 100 * log 2 ≤ A := by
    have : log 2 ≤ log (p : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hp)
    linarith
  set P : ℕ := p ^ ((lo p A0 k) ^ 2) with hP
  set Q : ℕ := q ^ ((lo q A0 k) ^ 2) with hQ
  have hPr : (p : ℝ) ^ ((lo p A0 k) ^ 2) = (P : ℝ) := by rw [hP]; push_cast; rfl
  have hQr : (q : ℝ) ^ ((lo q A0 k) ^ 2) = (Q : ℝ) := by rw [hQ]; push_cast; rfl
  have hPpos : (0 : ℝ) < P := by
    rw [← hPr]; exact pow_pos (by exact_mod_cast (show 0 < p by omega)) _
  have hQpos : (0 : ℝ) < Q := by
    rw [← hQr]; exact pow_pos (by exact_mod_cast (show 0 < q by omega)) _
  have hPle : (P : ℝ) ≤ exp (121 / 100 * A) := by
    rw [← hPr, pow_eq_exp hp]; apply exp_le_exp.mpr; push_cast; exact wp.2.2.1
  have hQle : (Q : ℝ) ≤ exp (121 / 100 * A) := by
    rw [← hQr, pow_eq_exp hq]; apply exp_le_exp.mpr; push_cast; exact wq.2.2.1
  have hbig : ∀ (r : ℕ), 2 ≤ r →
      361 / 100 * A ≤ ((hi r A0 k : ℝ) ^ 2) * log r →
      1 / (2 * (r : ℝ) ^ ((hi r A0 k) ^ 2)) ≤ exp (-(361 / 100) * A) / 2 := by
    intro r hr hw
    have h1 : exp (361 / 100 * A) ≤ (r : ℝ) ^ ((hi r A0 k) ^ 2) := by
      rw [pow_eq_exp hr]; apply exp_le_exp.mpr; push_cast; exact hw
    have e : exp (-(361 / 100) * A) / 2 = 1 / (2 * exp (361 / 100 * A)) := by
      rw [neg_mul, exp_neg]; field_simp
    rw [e]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hε1 : |θ - a / (P : ℝ)| ≤ exp (-(361 / 100) * A) / 2 := by
    rw [← hPr]; exact le_trans ha (hbig p hp wp.2.2.2.1)
  have hε2 : |θ - a' / (Q : ℝ)| ≤ exp (-(361 / 100) * A) / 2 := by
    rw [← hQr]; exact le_trans ha' (hbig q hq wq.2.2.2.1)
  have hzero : a * (Q : ℤ) - a' * (P : ℤ) = 0 := by
    have hdiff : |(a : ℝ) / P - a' / Q| ≤ exp (-(361 / 100) * A) := by
      have t := abs_sub_le ((a : ℝ) / P) θ (a' / Q)
      rw [abs_sub_comm ((a : ℝ) / P) θ] at t
      linarith
    have e : (a : ℝ) / P - a' / Q = ((a * (Q : ℤ) - a' * (P : ℤ) : ℤ) : ℝ) / (P * Q) := by
      push_cast; field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hPpos hQpos), div_le_iff₀ (mul_pos hPpos hQpos)] at hdiff
    have h3 : exp (-(361 / 100) * A) * (P * Q) < 1 := by
      have h4 : (P : ℝ) * Q ≤ exp (121 / 100 * A) * exp (121 / 100 * A) :=
        mul_le_mul hPle hQle hQpos.le (exp_pos _).le
      have h5 := mul_le_mul_of_nonneg_left h4 (exp_pos (-(361 / 100) * A)).le
      refine lt_of_le_of_lt h5 ?_
      rw [← exp_add, ← exp_add, exp_lt_one_iff]
      have : 0 < log (2 : ℝ) := log_pos (by norm_num)
      linarith
    have h6 : |((a * (Q : ℤ) - a' * (P : ℤ) : ℤ) : ℝ)| < 1 := lt_of_le_of_lt hdiff h3
    have h7 : |a * (Q : ℤ) - a' * (P : ℤ)| < 1 := by exact_mod_cast h6
    exact Int.abs_lt_one_iff.mp h7
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
  refine le_trans hε1 (div_le_div_of_nonneg_right (exp_le_exp.mpr ?_) (by norm_num))
  linarith

/-! ## Fourier positivity -/

section Fourier

open Complex

/-- `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp ((2 * π * x : ℝ) * I)

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma e_conj (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1; push_cast; ring

lemma e_re (x : ℝ) : (e x).re = Real.cos (2 * π * x) := by
  unfold e; rw [Complex.exp_ofReal_mul_I_re]

lemma e_int (z : ℤ) : e z = 1 := by
  unfold e
  have : ((2 * π * (z : ℝ) : ℝ) : ℂ) * I = z * (2 * π * I) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma e_nat_mul (x : ℝ) (n : ℕ) : e (n * x) = e x ^ n := by
  unfold e; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma e_eq_one_iff (x : ℝ) : e x = 1 ↔ ∃ z : ℤ, x = z := by
  constructor
  · intro h
    unfold e at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    nlinarith [pi_pos]
  · rintro ⟨z, rfl⟩; exact e_int z

/-- Orthogonality on `ZMod N`, for integers of absolute value below `N`. -/
lemma sum_e_eq {N : ℕ} (hN : 0 < N) (m : ℤ) (hm : |m| < N) :
    ∑ r ∈ Finset.range N, e (m * ((r : ℝ) / N)) = if m = 0 then (N : ℂ) else 0 := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hterm : ∀ r : ℕ, e (m * ((r : ℝ) / N)) = e ((m : ℝ) / N) ^ r := by
    intro r
    rw [← e_nat_mul]; congr 1; ring
  simp_rw [hterm]
  split_ifs with h
  · subst h
    have : e (((0 : ℤ) : ℝ) / N) = 1 := by
      have : (((0 : ℤ) : ℝ) / N) = ((0 : ℤ) : ℝ) := by simp
      rw [this, e_int]
    rw [sum_congr rfl (fun r _ => by rw [this, one_pow])]
    simp
  · have h1 : e ((m : ℝ) / N) ≠ 1 := by
      rw [Ne, e_eq_one_iff]
      rintro ⟨z, hz⟩
      rw [div_eq_iff hN'] at hz
      have hz' : m = z * N := by exact_mod_cast hz
      have hz0 : z ≠ 0 := by rintro rfl; simp at hz'; exact h hz'
      have : (N : ℤ) ≤ |m| := by
        rw [hz', abs_mul, Nat.abs_cast]
        exact le_mul_of_one_le_left (by positivity) (Int.one_le_abs hz0)
      omega
    have h2 : e ((m : ℝ) / N) ^ N = 1 := by
      rw [← e_nat_mul]
      have : (N : ℝ) * ((m : ℝ) / N) = (m : ℝ) := by field_simp
      rw [this, e_int]
    rw [geom_sum_eq h1, h2, sub_self, zero_div]

variable {ι : Type*} (I' : Finset ι) (g : ι → ℤ)

/-- The exponential sum. -/
noncomputable def S (θ : ℝ) : ℂ := ∑ i ∈ I', e (g i * θ)

/-- Counting the solutions of `h x = t` by orthogonality. -/
lemma count_eq {κ : Type*} (J : Finset κ) (h : κ → ℤ) (t : ℤ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ x ∈ J, |h x - t| < N) :
    ∑ r ∈ Finset.range N, ∑ x ∈ J, e (((h x - t : ℤ) : ℝ) * ((r : ℝ) / N))
      = (N : ℂ) * ((J.filter (fun x => h x = t)).card : ℂ) := by
  rw [sum_comm]
  have : ∀ x ∈ J, ∑ r ∈ Finset.range N, e (((h x - t : ℤ) : ℝ) * ((r : ℝ) / N))
      = if h x = t then (N : ℂ) else 0 := by
    intro x hx
    rw [sum_e_eq hN _ (hb x hx)]
    simp only [sub_eq_zero]
  rw [sum_congr rfl this, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm]

lemma norm_sq_S (θ : ℝ) :
    (((‖S I' g θ‖ ^ 2 : ℝ)) : ℂ) = ∑ p ∈ I' ×ˢ I', e (((g p.1 - g p.2 : ℤ) : ℝ) * θ) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', S, map_sum, sum_mul_sum, sum_product]
  refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
  rw [e_conj, ← e_add]; congr 1; push_cast; ring

lemma norm_four_S (θ : ℝ) :
    (((‖S I' g θ‖ ^ 4 : ℝ)) : ℂ)
      = ∑ p ∈ (I' ×ˢ I') ×ˢ (I' ×ˢ I'),
          e ((((g p.1.1 - g p.1.2) + (g p.2.1 - g p.2.2) : ℤ) : ℝ) * θ) := by
  have h : (‖S I' g θ‖ ^ 4 : ℝ) = ‖S I' g θ‖ ^ 2 * ‖S I' g θ‖ ^ 2 := by ring
  rw [h, Complex.ofReal_mul, norm_sq_S, sum_mul_sum]
  conv_rhs => rw [sum_product]
  refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
  rw [← e_add]; congr 1; push_cast; ring

/-- **Positivity.** If the large values of the exponential sum only occur where `t θ` is close to an
integer, and the collisions of `g` are few, then `t` is a sum of two differences. -/
theorem exists_four (t : ℤ) (R L : ℕ) (η E0 : ℝ) (hI : I'.Nonempty)
    (hR : ∀ i ∈ I', |g i| ≤ R)
    (hcoll : (((I' ×ˢ I').filter (fun p => g p.1 - g p.2 = 0)).card : ℝ)
      ≤ E0 * (I'.card : ℝ) ^ 2)
    (hsupp : ((I' ×ˢ I').image (fun p => g p.1 - g p.2)).card ≤ L)
    (hspec : ∀ θ : ℝ, η * I'.card ≤ ‖S I' g θ‖ → 4 / 5 ≤ Real.cos (2 * π * (t * θ)))
    (hnum : 2 * η ^ 2 * E0 < (4 / 5) / L) :
    ∃ i1 ∈ I', ∃ i2 ∈ I', ∃ i3 ∈ I', ∃ i4 ∈ I', (g i1 - g i2) + (g i3 - g i4) = t := by
  classical
  set J := (I' ×ˢ I') ×ˢ (I' ×ˢ I') with hJ
  set h4 : (ι × ι) × (ι × ι) → ℤ := fun p => (g p.1.1 - g p.1.2) + (g p.2.1 - g p.2.2) with hh4
  set N : ℕ := 4 * R + t.natAbs + 1 with hNdef
  have hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb4 : ∀ x ∈ J, |h4 x| ≤ 4 * (R : ℤ) := by
    intro x hx
    rw [hJ, mem_product, mem_product, mem_product] at hx
    have a := hR _ hx.1.1
    have b := hR _ hx.1.2
    have c := hR _ hx.2.1
    have d := hR _ hx.2.2
    rw [abs_le] at a b c d
    rw [abs_le]; simp only [hh4]; omega
  have hbt : ∀ x ∈ J, |h4 x - t| < N := by
    intro x hx
    have := hb4 x hx
    rw [abs_le] at this
    rw [abs_lt]; omega
  have hb0 : ∀ x ∈ J, |h4 x - 0| < N := by
    intro x hx
    have := hb4 x hx
    rw [abs_le] at this
    rw [abs_lt]; omega
  set F : ℕ → ℝ := fun r => ‖S I' g ((r : ℝ) / N)‖ with hF
  set Ct := (J.filter (fun x => h4 x = t)).card with hCt
  set C0 := (J.filter (fun x => h4 x = 0)).card with hC0
  set C2 := ((I' ×ˢ I').filter (fun p => g p.1 - g p.2 = 0)).card with hC2
  -- the three counting identities
  have idt : ∑ r ∈ Finset.range N, F r ^ 4 * Real.cos (2 * π * (t * ((r : ℝ) / N)))
      = N * Ct := by
    have hc := count_eq J h4 t hN hbt
    have : ∀ r : ℕ, ∑ x ∈ J, e (((h4 x - t : ℤ) : ℝ) * ((r : ℝ) / N))
        = (((F r ^ 4 : ℝ)) : ℂ) * e (-(t * ((r : ℝ) / N))) := by
      intro r
      simp only [hF]
      rw [norm_four_S, sum_mul]
      refine sum_congr rfl (fun x _ => ?_)
      rw [← e_add]; congr 1; simp only [hh4]; push_cast; ring
    simp_rw [this] at hc
    have := congrArg Complex.re hc
    rw [Complex.re_sum] at this
    simp only [Complex.re_ofReal_mul, e_re] at this
    have e2 : ((N : ℂ) * (Ct : ℂ)).re = (N : ℝ) * Ct := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    rw [← hCt, e2] at this
    rw [← this]
    refine sum_congr rfl (fun r _ => ?_)
    rw [mul_neg, Real.cos_neg]
  have id0 : ∑ r ∈ Finset.range N, F r ^ 4 = N * C0 := by
    have hc := count_eq J h4 0 hN hb0
    have : ∀ r : ℕ, ∑ x ∈ J, e (((h4 x - 0 : ℤ) : ℝ) * ((r : ℝ) / N))
        = (((F r ^ 4 : ℝ)) : ℂ) := by
      intro r
      simp only [hF, sub_zero]
      rw [norm_four_S]
    simp_rw [this] at hc
    rw [← hC0] at hc
    exact_mod_cast hc
  have id2 : ∑ r ∈ Finset.range N, F r ^ 2 = N * C2 := by
    have hb2 : ∀ x ∈ I' ×ˢ I', |(g x.1 - g x.2) - 0| < N := by
      intro x hx
      rw [mem_product] at hx
      have a := hR _ hx.1
      have b := hR _ hx.2
      rw [abs_le] at a b
      rw [abs_lt]; omega
    have hc := count_eq (I' ×ˢ I') (fun p => g p.1 - g p.2) 0 hN hb2
    have : ∀ r : ℕ, ∑ x ∈ I' ×ˢ I', e (((g x.1 - g x.2 - 0 : ℤ) : ℝ) * ((r : ℝ) / N))
        = (((F r ^ 2 : ℝ)) : ℂ) := by
      intro r
      simp only [hF, sub_zero]
      rw [norm_sq_S]
    simp_rw [this] at hc
    rw [← hC2] at hc
    exact_mod_cast hc
  -- the pointwise inequality
  have hpt : ∀ r ∈ Finset.range N,
      4 / 5 * F r ^ 4 - 2 * η ^ 2 * (I'.card : ℝ) ^ 2 * F r ^ 2
        ≤ F r ^ 4 * Real.cos (2 * π * (t * ((r : ℝ) / N))) := by
    intro r _
    have hF0 : 0 ≤ F r := norm_nonneg _
    by_cases h : η * I'.card ≤ F r
    · have hc := hspec _ h
      have h1 := mul_le_mul_of_nonneg_left hc (pow_nonneg hF0 4)
      have h2 : 0 ≤ 2 * η ^ 2 * (I'.card : ℝ) ^ 2 * F r ^ 2 := by positivity
      linarith
    · have h' : F r < η * I'.card := not_le.mp h
      have h1 : F r ^ 2 ≤ (η * I'.card) ^ 2 := pow_le_pow_left₀ hF0 h'.le 2
      have h2 := Real.neg_one_le_cos (2 * π * (t * ((r : ℝ) / N)))
      have h3 := mul_le_mul_of_nonneg_left h2 (pow_nonneg hF0 4)
      have h4' := mul_le_mul_of_nonneg_right h1 (sq_nonneg (F r))
      have e1 : F r ^ 2 * F r ^ 2 = F r ^ 4 := by ring
      have e2 : (η * (I'.card : ℝ)) ^ 2 * F r ^ 2 = η ^ 2 * (I'.card : ℝ) ^ 2 * F r ^ 2 := by
        ring
      have h5 : 0 ≤ F r ^ 4 := pow_nonneg hF0 4
      nlinarith
  have hsum := sum_le_sum hpt
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, id0, id2, idt] at hsum
  have hmain : 4 / 5 * (C0 : ℝ) - 2 * η ^ 2 * (I'.card : ℝ) ^ 2 * C2 ≤ Ct := by
    have : (N : ℝ) * (4 / 5 * (C0 : ℝ) - 2 * η ^ 2 * (I'.card : ℝ) ^ 2 * C2)
        ≤ N * Ct := by
      calc (N : ℝ) * (4 / 5 * (C0 : ℝ) - 2 * η ^ 2 * (I'.card : ℝ) ^ 2 * C2)
          = 4 / 5 * (N * C0) - 2 * η ^ 2 * (I'.card : ℝ) ^ 2 * (N * C2) := by ring
        _ ≤ _ := hsum
    exact le_of_mul_le_mul_left this hNr
  -- Cauchy-Schwarz for the zero count
  set d : ι × ι → ℤ := fun p => g p.1 - g p.2 with hd
  set T := (I' ×ˢ I').image d with hT
  set rep : ℤ → ℕ := fun x => ((I' ×ˢ I').filter (fun p => d p = x)).card with hrep
  have htot : ∑ x ∈ T, rep x = (I'.card) ^ 2 := by
    rw [sq, ← card_product]
    exact (card_eq_sum_card_image d (I' ×ˢ I')).symm
  have hneg : ∀ x, ((I' ×ˢ I').filter (fun p => d p = -x)).card = rep x := by
    intro x
    refine card_bij' (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_product, hd, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, by omega⟩
    · intro p hp
      simp only [mem_filter, mem_product, hd, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, by omega⟩
    · intro p _; simp
    · intro p _; simp
  have hC0eq : ∑ x ∈ T, rep x ^ 2 = C0 := by
    have hmaps : ∀ p ∈ J.filter (fun x => h4 x = 0), p.1 ∈ I' ×ˢ I' := by
      intro p hp
      rw [mem_filter, hJ, mem_product] at hp
      exact hp.1.1
    have h1 : C0 = ∑ a ∈ I' ×ˢ I', rep (d a) := by
      rw [hC0, card_eq_sum_card_fiberwise (f := fun p => p.1) (t := I' ×ˢ I')
        (fun p hp => hmaps p hp)]
      refine sum_congr rfl (fun a ha => ?_)
      rw [← hneg (d a)]
      refine card_bij' (fun p _ => p.2) (fun b _ => (a, b)) ?_ ?_ ?_ ?_
      · intro p hp
        rw [mem_filter, mem_filter, hJ, mem_product] at hp
        obtain ⟨⟨⟨_, hp2⟩, hz⟩, hpa⟩ := hp
        rw [mem_filter]
        refine ⟨hp2, ?_⟩
        simp only [hh4] at hz
        simp only [hd, ← hpa]
        omega
      · intro b hb
        rw [mem_filter] at hb
        rw [mem_filter, mem_filter, hJ, mem_product]
        refine ⟨⟨⟨ha, hb.1⟩, ?_⟩, rfl⟩
        have := hb.2
        simp only [hd] at this
        simp only [hh4]; omega
      · intro p hp
        rw [mem_filter] at hp
        exact Prod.ext hp.2.symm rfl
      · intro b _; rfl
    rw [h1, ← sum_fiberwise_of_maps_to (g := d) (t := T)
      (fun a ha => mem_image_of_mem d ha) (fun a => rep (d a))]
    refine sum_congr rfl (fun x _ => ?_)
    have : ∑ a ∈ (I' ×ˢ I').filter (fun a => d a = x), rep (d a)
        = ∑ _a ∈ (I' ×ˢ I').filter (fun a => d a = x), rep x :=
      sum_congr rfl (fun a ha => by rw [(mem_filter.mp ha).2])
    rw [this, sum_const, smul_eq_mul, sq]
  have hCS : ((I'.card : ℝ) ^ 2) ^ 2 ≤ L * C0 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := T) (f := fun x => (rep x : ℝ))
    have h2 : ∑ x ∈ T, (rep x : ℝ) = (I'.card : ℝ) ^ 2 := by exact_mod_cast htot
    have h3 : ∑ x ∈ T, (rep x : ℝ) ^ 2 = (C0 : ℝ) := by exact_mod_cast hC0eq
    rw [h2, h3] at h1
    refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    exact_mod_cast hsupp
  have hIpos : (0 : ℝ) < I'.card := by exact_mod_cast card_pos.mpr hI
  have hLpos : (0 : ℝ) < L := by
    have : 0 < T.card := by
      rw [hT]; exact card_pos.mpr ((hI.product hI).image d)
    exact_mod_cast lt_of_lt_of_le this hsupp
  have hpos : (0 : ℝ) < Ct := by
    have h1 : ((I'.card : ℝ) ^ 2) ^ 2 / L ≤ C0 := by
      rw [div_le_iff₀ hLpos]; linarith
    have h2 : 2 * η ^ 2 * (I'.card : ℝ) ^ 2 * C2
        ≤ 2 * η ^ 2 * (I'.card : ℝ) ^ 2 * (E0 * (I'.card : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hcoll (by positivity)
    have h3 : 0 < ((I'.card : ℝ) ^ 2) ^ 2 * ((4 / 5) / L - 2 * η ^ 2 * E0) :=
      mul_pos (by positivity) (by linarith)
    have e : ((I'.card : ℝ) ^ 2) ^ 2 * ((4 / 5) / L - 2 * η ^ 2 * E0)
        = 4 / 5 * (((I'.card : ℝ) ^ 2) ^ 2 / L)
          - 2 * η ^ 2 * (I'.card : ℝ) ^ 2 * (E0 * (I'.card : ℝ) ^ 2) := by ring
    rw [e] at h3
    linarith
  have hpos' : 0 < Ct := by exact_mod_cast hpos
  obtain ⟨x, hx⟩ := card_pos.mp hpos'
  rw [mem_filter, hJ, mem_product, mem_product, mem_product] at hx
  exact ⟨x.1.1, hx.1.1.1, x.1.2, hx.1.1.2, x.2.1, hx.1.2.1, x.2.2, hx.1.2.2, hx.2⟩

end Fourier

/-! ## Digit sets -/

/-- `k` is within `s` of `0` at every level of the base `p`. -/
def Small (p : ℕ) (s : ℝ) (k : ℤ) : Prop :=
  ∀ n : ℕ, |(k : ℝ) / (p : ℝ) ^ (n ^ 2) - round ((k : ℝ) / (p : ℝ) ^ (n ^ 2))| < s

lemma dist_add_le (x y : ℝ) :
    |x + y - round (x + y)| ≤ |x - round x| + |y - round y| := by
  refine le_trans (round_le (x + y) (round x + round y)) ?_
  have : x + y - ((round x + round y : ℤ) : ℝ) = (x - round x) + (y - round y) := by
    push_cast; ring
  rw [this]; exact abs_add_le _ _

lemma dist_neg (x : ℝ) : |-x - round (-x)| = |x - round x| := by
  have key : ∀ y : ℝ, |-y - round (-y)| ≤ |y - round y| := by
    intro y
    refine le_trans (round_le (-y) (-round y)) (le_of_eq ?_)
    rw [← abs_neg]; congr 1; push_cast; ring
  refine le_antisymm (key x) ?_
  have := key (-x)
  rwa [neg_neg] at this

lemma Small.add {p : ℕ} {s t : ℝ} {a b : ℤ} (ha : Small p s a) (hb : Small p t b) :
    Small p (s + t) (a + b) := by
  intro n
  have e : ((a + b : ℤ) : ℝ) / (p : ℝ) ^ (n ^ 2)
      = (a : ℝ) / (p : ℝ) ^ (n ^ 2) + (b : ℝ) / (p : ℝ) ^ (n ^ 2) := by push_cast; ring
  rw [e]
  exact lt_of_le_of_lt (dist_add_le _ _) (add_lt_add (ha n) (hb n))

lemma Small.neg {p : ℕ} {s : ℝ} {a : ℤ} (ha : Small p s a) : Small p s (-a) := by
  intro n
  have e : ((-a : ℤ) : ℝ) / (p : ℝ) ^ (n ^ 2) = -((a : ℝ) / (p : ℝ) ^ (n ^ 2)) := by
    push_cast; ring
  rw [e, dist_neg]; exact ha n

lemma Small.sub {p : ℕ} {s t : ℝ} {a b : ℤ} (ha : Small p s a) (hb : Small p t b) :
    Small p (s + t) (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

/-- The digit vectors of the levels below `N`. -/
def vectors (p D N : ℕ) : Finset (Fin N → ℤ) :=
  Fintype.piFinset (fun n : Fin N => Icc (-(range' p D n : ℤ)) (range' p D n))

/-- The integer with a given digit vector. -/
def value (p : ℕ) {N : ℕ} (j : Fin N → ℤ) : ℤ := ∑ n : Fin N, (p : ℤ) ^ ((n : ℕ) ^ 2) * j n

lemma vectors_nonempty (p D N : ℕ) : (vectors p D N).Nonempty := by
  refine ⟨0, ?_⟩
  rw [vectors, Fintype.mem_piFinset]
  intro n
  simp

lemma sum_levels {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    ∑ n ∈ Finset.range m, p ^ ((n + 1) ^ 2) < 2 * p ^ (m ^ 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h : 2 * p ^ (m ^ 2) ≤ p ^ ((m + 1) ^ 2) := by
      have e : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
      have h1 : p ≤ p ^ (2 * m + 1) := Nat.le_self_pow (by omega) p
      rw [e, pow_add, mul_comm 2]
      exact Nat.mul_le_mul le_rfl (le_trans hp h1)
    omega

/-- The terms of the lower levels, in absolute value. -/
lemma abs_low {p D N : ℕ} (hp : 2 ≤ p) (hD : 1 ≤ D) {j : Fin N → ℤ} (hj : j ∈ vectors p D N)
    (m : ℕ) :
    (D : ℝ) * |∑ n : Fin N, if (n : ℕ) < m then (p : ℝ) ^ ((n : ℕ) ^ 2) * (j n : ℝ) else 0|
      < (p : ℝ) ^ (m ^ 2) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [vectors, Fintype.mem_piFinset] at hj
  have hterm : ∀ n : Fin N,
      2 * (D : ℝ) * |if (n : ℕ) < m then (p : ℝ) ^ ((n : ℕ) ^ 2) * (j n : ℝ) else 0|
        ≤ if (n : ℕ) < m then (p : ℝ) ^ (((n : ℕ) + 1) ^ 2) else 0 := by
    intro n
    split_ifs with h
    · have hjn := hj n
      rw [mem_Icc, ← abs_le] at hjn
      have h1 : |(j n : ℝ)| ≤ (range' p D n : ℝ) := by exact_mod_cast hjn
      have h2 : 2 * D * range' p D n ≤ p ^ (2 * (n : ℕ) + 1) := Nat.mul_div_le _ _
      have h2' : 2 * (D : ℝ) * range' p D n ≤ (p : ℝ) ^ (2 * (n : ℕ) + 1) := by exact_mod_cast h2
      have hpow : (p : ℝ) ^ (((n : ℕ) + 1) ^ 2)
          = (p : ℝ) ^ ((n : ℕ) ^ 2) * (p : ℝ) ^ (2 * (n : ℕ) + 1) := by
        rw [← pow_add]; congr 1; ring
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ ((n : ℕ) ^ 2)), hpow]
      have h3 : 2 * (D : ℝ) * |(j n : ℝ)| ≤ (p : ℝ) ^ (2 * (n : ℕ) + 1) :=
        le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) h2'
      have := mul_le_mul_of_nonneg_left h3
        (show (0 : ℝ) ≤ (p : ℝ) ^ ((n : ℕ) ^ 2) by positivity)
      linarith
    · simp
  have h1 : 2 * (D : ℝ)
      * |∑ n : Fin N, if (n : ℕ) < m then (p : ℝ) ^ ((n : ℕ) ^ 2) * (j n : ℝ) else 0|
      ≤ ∑ n : Fin N, if (n : ℕ) < m then (p : ℝ) ^ (((n : ℕ) + 1) ^ 2) else 0 := by
    refine le_trans (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)) ?_
    rw [mul_sum]
    exact sum_le_sum (fun n _ => hterm n)
  have h2 : (∑ n : Fin N, if (n : ℕ) < m then (p : ℝ) ^ (((n : ℕ) + 1) ^ 2) else 0)
      ≤ ∑ n ∈ Finset.range m, (p : ℝ) ^ ((n + 1) ^ 2) := by
    rw [Fin.sum_univ_eq_sum_range (fun n => if n < m then (p : ℝ) ^ ((n + 1) ^ 2) else 0),
      ← sum_filter]
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro n hn
    rw [mem_filter] at hn
    exact Finset.mem_range.mpr hn.2
  have h3 : ∑ n ∈ Finset.range m, (p : ℝ) ^ ((n + 1) ^ 2) < 2 * (p : ℝ) ^ (m ^ 2) := by
    exact_mod_cast sum_levels hp m
  linarith

lemma small_value {p D N : ℕ} (hp : 2 ≤ p) (hD : 1 ≤ D) {j : Fin N → ℤ} (hj : j ∈ vectors p D N) :
    Small p (1 / D) (value p j) := by
  intro m
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set low : ℝ := ∑ n : Fin N, if (n : ℕ) < m then (p : ℝ) ^ ((n : ℕ) ^ 2) * (j n : ℝ) else 0
    with hlow
  set up : ℤ := ∑ n : Fin N,
    if (n : ℕ) < m then 0 else (p : ℤ) ^ ((n : ℕ) ^ 2 - m ^ 2) * j n with hup
  have hsplit : (value p j : ℝ) / (p : ℝ) ^ (m ^ 2) = low / (p : ℝ) ^ (m ^ 2) + up := by
    have h : (value p j : ℝ) = low + (p : ℝ) ^ (m ^ 2) * up := by
      rw [hlow, hup, value]
      push_cast
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl (fun n _ => ?_)
      split_ifs with h
      · ring
      · have hle : m ^ 2 ≤ (n : ℕ) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        rw [zero_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
    rw [h]; field_simp
  rw [hsplit]
  refine lt_of_le_of_lt (round_le _ up) ?_
  rw [add_sub_cancel_right, abs_div, abs_of_pos (pow_pos hp' _), div_lt_div_iff₀ (pow_pos hp' _) hD']
  have := abs_low hp hD hj m
  rw [← hlow] at this
  linarith

lemma abs_value_le {p D N : ℕ} (hp : 2 ≤ p) (hD : 1 ≤ D) {j : Fin N → ℤ}
    (hj : j ∈ vectors p D N) : |(value p j : ℝ)| ≤ (p : ℝ) ^ (N ^ 2) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h := abs_low hp hD hj N
  have e : (∑ n : Fin N, if (n : ℕ) < N then (p : ℝ) ^ ((n : ℕ) ^ 2) * (j n : ℝ) else 0)
      = (value p j : ℝ) := by
    rw [value]; push_cast
    exact sum_congr rfl (fun n _ => ite_eq_left n.isLt)
  rw [e] at h
  exact le_trans (le_mul_of_one_le_left (abs_nonneg _) hD') h.le

/-- The exponential sum over the digit vectors is a product. -/
lemma sum_vectors (p D N : ℕ) (θ : ℝ) :
    ∑ j ∈ vectors p D N, e ((value p j : ℝ) * θ)
      = (((vectors p D N).card : ℝ) * prodDigit p D N θ : ℝ) := by
  have hdig : ∀ (J : ℕ) (x : ℝ), ∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x)
      = ((((2 * J + 1 : ℕ) : ℝ) * digit J x : ℝ) : ℂ) := by
    intro J x
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
        · intro k hk; simp only [mem_coe, mem_Icc] at hk ⊢; omega
        · intro k hk; simp only [mem_coe, mem_Icc] at hk ⊢; omega
        · intro k _; simp
        · intro k _; simp
        · intro k _
          rw [e_conj]; congr 1; push_cast; ring
      exact Complex.conj_eq_iff_im.mp hc
    apply Complex.ext
    · rw [hre, Complex.ofReal_re]
    · rw [him, Complex.ofReal_im]
  have hprod : ∀ j : Fin N → ℤ, e ((value p j : ℝ) * θ)
      = ∏ n : Fin N, e ((j n : ℝ) * ((p : ℝ) ^ ((n : ℕ) ^ 2) * θ)) := by
    intro j
    unfold e
    rw [← Complex.exp_sum]
    congr 1
    rw [value]
    push_cast
    rw [sum_mul, mul_sum, sum_mul]
    exact sum_congr rfl (fun n _ => by ring)
  simp_rw [hprod]
  rw [vectors, ← prod_univ_sum (fun n : Fin N => Icc (-(range' p D n : ℤ)) (range' p D n))
    (fun (n : Fin N) (k : ℤ) => e ((k : ℝ) * ((p : ℝ) ^ ((n : ℕ) ^ 2) * θ)))]
  simp_rw [hdig]
  rw [← Complex.ofReal_prod, Fintype.card_piFinset]
  congr 1
  rw [prod_mul_distrib, prodDigit,
    ← Fin.prod_univ_eq_prod_range (fun n => digit (range' p D n) ((p : ℝ) ^ (n ^ 2) * θ))]
  push_cast
  congr 1
  refine prod_congr rfl (fun n _ => ?_)
  rw [card_digits]; push_cast; ring

/-! ## The theorem -/

/-- **Witnesses from a positive density of differences.** -/
theorem witness_of_density {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) {K A0 s : ℝ} (hK : 1 ≤ K)
    (hAp : 100 * log p ≤ A0) (hAq : 100 * log q ≤ A0)
    (hDp : log (2 * D) ^ 2 ≤ 4 * log p * A0) (hDq : log (2 * D) ^ 2 ≤ 4 * log q * A0)
    {B : ℕ} (hB : B = ⌊12 * (D : ℝ) ^ 2 * log (50 * K)⌋₊)
    {X : ℕ} (hX : exp (4 ^ (2 * B + 1) * A0) ≤ X)
    (V : Finset ℤ) (hV : (X : ℝ) ≤ K * V.card) (a b : ℤ → ℤ)
    (hdiff : ∀ v ∈ V, v = a v - b v)
    (haX : ∀ v ∈ V, |a v| ≤ (X : ℤ)) (hbX : ∀ v ∈ V, |b v| ≤ (X : ℤ))
    (ha : ∀ v ∈ V, Small p s (a v)) (hb : ∀ v ∈ V, Small q s (b v))
    (t : ℤ) (ht : |(t : ℝ)| ≤ exp (3 * A0)) :
    ∃ k : ℤ, |k| ≤ 8 * (X : ℤ) ∧ Small p (4 * (s + 1 / D)) k
      ∧ Small q (4 * (s + 1 / D)) (k - t) := by
  classical
  have hA : 0 ≤ A0 := le_trans (mul_nonneg (by norm_num) (log_pos' hp).le) hAp
  have hKpos : (0 : ℝ) < K := by linarith
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (exp_pos _) hX
  have hX1 : (1 : ℝ) ≤ X := by
    have : 0 < X := by exact_mod_cast hXpos
    exact_mod_cast this
  have hVpos : (0 : ℝ) < V.card := by
    by_contra h
    have h0 : (V.card : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [h0, mul_zero] at hV
    linarith
  set Np := hi p A0 (2 * B) with hNp
  set Nq := hi q A0 (2 * B) with hNq
  -- the digit sets fit below `X`
  have hfit : ∀ r : ℕ, 2 ≤ r → 100 * log r ≤ A0 → (r : ℝ) ^ ((hi r A0 (2 * B)) ^ 2) ≤ X := by
    intro r hr hAr
    refine le_trans ?_ hX
    rw [pow_eq_exp hr]
    apply exp_le_exp.mpr
    push_cast
    exact (window hr hAr (2 * B)).2.2.2.2
  set I' : Finset (ℤ × (Fin Np → ℤ) × (Fin Nq → ℤ)) :=
    V ×ˢ (vectors p D Np ×ˢ vectors q D Nq) with hI'
  set g : ℤ × (Fin Np → ℤ) × (Fin Nq → ℤ) → ℤ :=
    fun i => i.1 + value p i.2.1 - value q i.2.2 with hg
  have hVne : V.Nonempty := card_pos.mp (by exact_mod_cast hVpos)
  have hIne : I'.Nonempty :=
    hVne.product ((vectors_nonempty p D Np).product (vectors_nonempty q D Nq))
  have hcard : (I'.card : ℝ)
      = V.card * ((vectors p D Np).card * (vectors q D Nq).card) := by
    rw [hI', card_product, card_product]; push_cast; ring
  have hmem : ∀ i ∈ I', i.1 ∈ V ∧ i.2.1 ∈ vectors p D Np ∧ i.2.2 ∈ vectors q D Nq := by
    intro i hi'
    rw [hI', mem_product, mem_product] at hi'
    exact ⟨hi'.1, hi'.2.1, hi'.2.2⟩
  have hvp : ∀ j ∈ vectors p D Np, |value p j| ≤ (X : ℤ) := by
    intro j hj
    have := le_trans (abs_value_le hp hD hj) (hfit p hp hAp)
    exact_mod_cast this
  have hvq : ∀ j ∈ vectors q D Nq, |value q j| ≤ (X : ℤ) := by
    intro j hj
    have := le_trans (abs_value_le hq hD hj) (hfit q hq hAq)
    exact_mod_cast this
  have hR : ∀ i ∈ I', |g i| ≤ ((4 * X : ℕ) : ℤ) := by
    intro i hi'
    obtain ⟨h1, h2, h3⟩ := hmem i hi'
    have e1 := hdiff _ h1
    have a1 := haX _ h1
    have a2 := hbX _ h1
    have a3 := hvp _ h2
    have a4 := hvq _ h3
    rw [abs_le] at a1 a2 a3 a4
    rw [abs_le]; simp only [hg]; push_cast; omega
  -- collisions
  have hcoll : (((I' ×ˢ I').filter (fun x => g x.1 - g x.2 = 0)).card : ℝ)
      ≤ (1 / V.card) * (I'.card : ℝ) ^ 2 := by
    set W := vectors p D Np ×ˢ vectors q D Nq with hW
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
        ≤ (I'.card : ℝ) * ((vectors p D Np).card * (vectors q D Nq).card) := by
      have h3 : (I' ×ˢ W).card = I'.card * ((vectors p D Np).card * (vectors q D Nq).card) := by
        rw [card_product I' W, hW, card_product (vectors p D Np)]
      exact_mod_cast le_trans h1 (le_of_eq h3)
    refine le_trans h2 (le_of_eq ?_)
    rw [hcard]; field_simp
  have hsupp : ((I' ×ˢ I').image (fun x => g x.1 - g x.2)).card ≤ 16 * X + 1 := by
    have hsub : (I' ×ˢ I').image (fun x => g x.1 - g x.2)
        ⊆ Icc (-(8 * (X : ℤ))) (8 * (X : ℤ)) := by
      intro y hy
      rw [mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [mem_product] at hx
      have a1 := hR _ hx.1
      have a2 := hR _ hx.2
      rw [abs_le] at a1 a2
      push_cast at a1 a2
      rw [mem_Icc]; omega
    refine le_trans (card_le_card hsub) ?_
    rw [Int.card_Icc]; omega
  -- the large values of the exponential sum
  set η : ℝ := sqrt (1 / (50 * K)) with hη
  have hηpos : 0 < η := sqrt_pos.mpr (by positivity)
  have hη2 : η ^ 2 = 1 / (50 * K) := sq_sqrt (by positivity)
  have hlogη : -log η = log (50 * K) / 2 := by
    rw [hη, log_sqrt (by positivity), one_div, log_inv]; ring
  have hBlt : 24 * (D : ℝ) ^ 2 * (-log η) < B + 1 := by
    have h := Nat.lt_floor_add_one (12 * (D : ℝ) ^ 2 * log (50 * K))
    rw [← hB] at h
    rw [hlogη]
    linarith
  have hfactor : ∀ θ : ℝ, S I' g θ = (∑ v ∈ V, e ((v : ℝ) * θ))
      * ((∑ j ∈ vectors p D Np, e ((value p j : ℝ) * θ))
        * (∑ j ∈ vectors q D Nq, e ((value q j : ℝ) * (-θ)))) := by
    intro θ
    rw [S, hI', sum_product, sum_mul]
    refine sum_congr rfl (fun v _ => ?_)
    rw [sum_product, sum_mul_sum, mul_sum]
    refine sum_congr rfl (fun j _ => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun l _ => ?_)
    rw [← e_add, ← e_add]
    congr 1; simp only [hg]; push_cast; ring
  have heven : ∀ θ : ℝ, prodDigit q D Nq (-θ) = prodDigit q D Nq θ := by
    intro θ
    unfold prodDigit
    refine prod_congr rfl (fun n _ => ?_)
    rw [mul_neg, digit_neg]
  have hle1 : ∀ (r N : ℕ) (θ : ℝ), |prodDigit r D N θ| ≤ 1 := by
    intro r N θ
    unfold prodDigit
    rw [abs_prod]
    exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_digit_le_one _ _)
  have hspec : ∀ θ : ℝ, η * I'.card ≤ ‖S I' g θ‖ → 4 / 5 ≤ Real.cos (2 * π * (t * θ)) := by
    intro θ hθ
    have hnorm : ‖S I' g θ‖ ≤ (I'.card : ℝ)
        * (|prodDigit p D Np θ| * |prodDigit q D Nq θ|) := by
      rw [hfactor, norm_mul, norm_mul, sum_vectors, sum_vectors, heven,
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
    have hboth : η ≤ |prodDigit p D Np θ| * |prodDigit q D Nq θ| := by
      have := le_trans hθ hnorm
      rw [mul_comm η] at this
      exact le_of_mul_le_mul_left this hIpos
    have h1 : η ≤ |prodDigit p D Np θ| :=
      le_trans hboth (mul_le_of_le_one_right (abs_nonneg _) (hle1 q Nq θ))
    have h2 : η ≤ |prodDigit q D Nq θ| :=
      le_trans hboth (mul_le_of_le_one_left (abs_nonneg _) (hle1 p Np θ))
    obtain ⟨z, hz⟩ := rigidity hp hq hpq hD hηpos hBlt hAp hAq hDp hDq (le_of_eq hNp.symm)
      (le_of_eq hNq.symm) h1 h2
    set y : ℝ := t * (θ - z) with hy
    have hyabs : |y| ≤ 1 / 10 := by
      rw [hy, abs_mul]
      have h3 := mul_le_mul ht hz (abs_nonneg _) (exp_pos _).le
      refine le_trans h3 ?_
      have e1 : exp (3 * A0) * (exp (-(36 / 10) * A0) / 2) = exp (-(6 / 10) * A0) / 2 := by
        rw [mul_div_assoc', ← exp_add]; congr 2; ring
      rw [e1]
      have h4 : exp (-(6 / 10) * A0) ≤ 1 / 5 := by
        have hl2 : (0.69 : ℝ) < log 2 := lt_trans (by norm_num) log_two_gt_d9
        have hA60 : 60 ≤ A0 := by
          have : log 2 ≤ log (p : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hp)
          linarith
        rw [neg_mul, exp_neg]
        have h5 : (5 : ℝ) ≤ exp (6 / 10 * A0) :=
          le_trans (by linarith) (add_one_le_exp _)
        rw [one_div]
        exact inv_anti₀ (by norm_num) h5
      linarith
    have hcos : Real.cos (2 * π * (t * θ)) = Real.cos (2 * π * y) := by
      have : 2 * π * ((t : ℝ) * θ) = 2 * π * y + ((t * z : ℤ) : ℝ) * (2 * π) := by
        rw [hy]; push_cast; ring
      rw [this, Real.cos_add_int_mul_two_pi]
    rw [hcos]
    refine le_trans ?_ (Real.one_sub_sq_div_two_le_cos)
    have h6 : |2 * π * y| ≤ 0.63 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have := mul_le_mul_of_nonneg_left hyabs (show (0 : ℝ) ≤ 2 * π by positivity)
      have hpi : π < 3.15 := pi_lt_d2
      linarith
    have h7 : (2 * π * y) ^ 2 ≤ 0.63 ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h6 2
    linarith [show (0.63 : ℝ) ^ 2 ≤ 0.4 by norm_num]
  have hnum : 2 * η ^ 2 * (1 / (V.card : ℝ)) < (4 / 5) / ((16 * X + 1 : ℕ) : ℝ) := by
    rw [hη2]
    have h1 : 1 / (V.card : ℝ) ≤ K / X := by
      rw [div_le_div_iff₀ hVpos hXpos]; linarith
    have h2 : 2 * (1 / (50 * K)) * (1 / (V.card : ℝ)) ≤ 2 * (1 / (50 * K)) * (K / X) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * (1 / (50 * K)) * (K / X) = 1 / (25 * X) := by field_simp; ring
    refine lt_of_le_of_lt (le_trans h2 (le_of_eq h3)) ?_
    push_cast
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  obtain ⟨i1, m1, i2, m2, i3, m3, i4, m4, hsum⟩ :=
    exists_four I' g t (4 * X) (16 * X + 1) η (1 / V.card) hIne hR hcoll hsupp hspec hnum
  obtain ⟨v1, x1, y1⟩ := hmem i1 m1
  obtain ⟨v2, x2, y2⟩ := hmem i2 m2
  obtain ⟨v3, x3, y3⟩ := hmem i3 m3
  obtain ⟨v4, x4, y4⟩ := hmem i4 m4
  set P : ℤ × (Fin Np → ℤ) × (Fin Nq → ℤ) → ℤ := fun i => a i.1 + value p i.2.1 with hP
  set Q : ℤ × (Fin Np → ℤ) × (Fin Nq → ℤ) → ℤ := fun i => b i.1 + value q i.2.2 with hQ
  have hPQ : ∀ i ∈ I', g i = P i - Q i := by
    intro i hi'
    have := hdiff _ (hmem i hi').1
    simp only [hg, hP, hQ]; omega
  set k := (P i1 - P i2) + (P i3 - P i4) with hk
  have hkt : k - t = (Q i1 - Q i2) + (Q i3 - Q i4) := by
    rw [hPQ _ m1, hPQ _ m2, hPQ _ m3, hPQ _ m4] at hsum
    omega
  have sP : ∀ i ∈ I', Small p (s + 1 / D) (P i) := fun i hi' =>
    (ha _ (hmem i hi').1).add (small_value hp hD (hmem i hi').2.1)
  have sQ : ∀ i ∈ I', Small q (s + 1 / D) (Q i) := fun i hi' =>
    (hb _ (hmem i hi').1).add (small_value hq hD (hmem i hi').2.2)
  have e4 : 4 * (s + 1 / (D : ℝ))
      = ((s + 1 / D) + (s + 1 / D)) + ((s + 1 / D) + (s + 1 / D)) := by ring
  refine ⟨k, ?_, ?_, ?_⟩
  · have bound : ∀ i ∈ I', |P i| ≤ 2 * (X : ℤ) := by
      intro i hi'
      have h1 := haX _ (hmem i hi').1
      have h2 := hvp _ (hmem i hi').2.1
      have := abs_add_le (a i.1) (value p i.2.1)
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

end TwoPrimesEffective
