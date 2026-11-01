import Mathlib
import LeanCheck.JANonDeep
import LeanCheck.MixedPrimeAnalytic

/-!
# The central bound, step 7: the final product

Given the factors `f_i` of the sorted list of prime-square scales, the paper concludes: `1 ≤ f_i ≤ B_D` always, `f_i - 1 ≤ C t_i^{-3}`
on the deep levels above a start threshold, only boundedly many levels are exceptional, `∑ t_i^{-3} < ∞`, hence `∏ f_i` is bounded
independently of the number of levels.

Checked here (no axiom, no `sorry`):

* `product_final` (abstract): for a strictly increasing selection of periods `b_i^(n_i^2)`, `i < L`, factors with `1 ≤ f_i ≤ B`, a set `E`
  of at most `K` exceptional indices, and `f_i ≤ 1 + Cf (1/t_i)^3` for the non-exceptional levels with `t_i ≥ T`:
  `∏ f_i ≤ B^(K + 2⌊2T⌋) exp(Cf · 2((√log 2)^{-3} + (√log 3)^{-3}))`;
* `sep_cube`: the right-hand side of `separated_factor` is at most `Cs (1/t)^3` for `t ≥ 1`;
* `close_cube`: for `A ≥ 0` the right-hand side of `close_factor` is at most `Cc (1/t)^3` for `t ≥ T_A` (this includes the
  simplification `exp(3A log^2(2+t) - 3t) ≤ t^{-3}` of the paper's `Φ_{i+1}(u_i) ≤ C e^{-t}`).
-/

namespace LeanCheck
namespace JAProductFinal

open Finset

/-! ### Part A: the abstract product bound -/

/-- Distinct levels of a strictly increasing selection have distinct pairs `(b, n)`. -/
lemma period_inj (L : ℕ) (b n : ℕ → ℕ)
    (hmono : ∀ a c, a < c → c < L → JAMerged.lp (b a) (n a) < JAMerged.lp (b c) (n c)) :
    Set.InjOn (fun i => (b i, n i)) (↑(range L) : Set ℕ) := by
  intro a ha c hc h
  simp only [Finset.coe_range, Set.mem_Iio] at ha hc
  simp only [Prod.mk.injEq] at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hmono a c hlt hc
    rw [h.1, h.2] at this
    exact lt_irrefl _ this
  · have := hmono c a hgt ha
    rw [h.1, h.2] at this
    exact lt_irrefl _ this

/-- A small `t = sqrt (lp b n)` bounds `n`. -/
lemma n_le_of_sqrt_lt (b n : ℕ) (hb : 2 ≤ b) (T : ℝ) (h : Real.sqrt (JAMerged.lp b n) < T) :
    (n : ℝ) ≤ 2 * T := by
  rw [JAMerged.sqrt_lp] at h
  have h1 : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log b) := by
    apply Real.le_sqrt_of_sq_le
    have := JAMerged.log_ge_quarter hb
    nlinarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := mul_le_mul_of_nonneg_left h1 hn
  linarith

/-- **The final product bound** (abstract form). -/
theorem product_final (L : ℕ) (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3) (hn : ∀ i, i < L → 1 ≤ n i)
    (hmono : ∀ a c, a < c → c < L → JAMerged.lp (b a) (n a) < JAMerged.lp (b c) (n c))
    (f : ℕ → ℝ) (B Cf T : ℝ) (hB : 1 ≤ B) (hCf : 0 ≤ Cf)
    (hfB : ∀ i, i < L → 1 ≤ f i ∧ f i ≤ B)
    (E : Finset ℕ) (K : ℕ) (hEcard : E.card ≤ K)
    (hgood : ∀ i, i < L → i ∉ E → T ≤ Real.sqrt (JAMerged.lp (b i) (n i)) →
      f i ≤ 1 + Cf * (1 / Real.sqrt (JAMerged.lp (b i) (n i))) ^ 3) :
    ∏ i ∈ range L, f i ≤ B ^ (K + 2 * ⌊2 * T⌋₊) *
      Real.exp (Cf * (2 * (1 / (Real.sqrt (Real.log 2)) ^ 3 + 1 / (Real.sqrt (Real.log 3)) ^ 3))) := by
  classical
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h <;> omega
  set early : Finset ℕ := (range L).filter (fun i => Real.sqrt (JAMerged.lp (b i) (n i)) < T) with hearly
  set bad : Finset ℕ := E.filter (fun i => i < L) ∪ early with hbad
  have hbadsub : bad ⊆ range L := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact Finset.mem_range.mpr (Finset.mem_filter.mp h).2
    · exact (Finset.mem_filter.mp h).1
  have hinj := period_inj L b n hmono
  have hearly_card : early.card ≤ 2 * ⌊2 * T⌋₊ := by
    have hsub : early.image (fun i => (b i, n i)) ⊆ ({2, 3} : Finset ℕ) ×ˢ Finset.Icc 1 ⌊2 * T⌋₊ := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hiL, hit⟩ := Finset.mem_filter.mp hi
      rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rcases hb i with h | h <;> simp [h]
      · rw [Finset.mem_Icc]
        refine ⟨hn i (Finset.mem_range.mp hiL), ?_⟩
        apply Nat.le_floor
        exact n_le_of_sqrt_lt (b i) (n i) (hb2 i) T hit
    have h1 : (early.image (fun i => (b i, n i))).card = early.card :=
      Finset.card_image_of_injOn (hinj.mono (by
        intro i hi
        exact Finset.mem_coe.mpr (Finset.mem_filter.mp hi).1))
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_product, Nat.card_Icc] at h2
    simp at h2
    omega
  have hbad_card : bad.card ≤ K + 2 * ⌊2 * T⌋₊ := by
    calc bad.card ≤ (E.filter (fun i => i < L)).card + early.card := Finset.card_union_le _ _
      _ ≤ E.card + early.card := by
          have := Finset.card_filter_le E (fun i => i < L)
          omega
      _ ≤ K + 2 * ⌊2 * T⌋₊ := by omega
  have hsum : ∑ i ∈ range L \ bad, Cf * (1 / Real.sqrt (JAMerged.lp (b i) (n i))) ^ 3 ≤
      Cf * (2 * (1 / (Real.sqrt (Real.log 2)) ^ 3 + 1 / (Real.sqrt (Real.log 3)) ^ 3)) := by
    have hnn : ∀ i ∈ range L, 0 ≤ Cf * (1 / Real.sqrt (JAMerged.lp (b i) (n i))) ^ 3 :=
      fun i _ => by positivity
    calc ∑ i ∈ range L \ bad, Cf * (1 / Real.sqrt (JAMerged.lp (b i) (n i))) ^ 3
        ≤ ∑ i ∈ range L, Cf * (1 / Real.sqrt (JAMerged.lp (b i) (n i))) ^ 3 :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i hi _ => hnn i hi)
      _ = Cf * ∑ i ∈ range L, (1 / Real.sqrt (JAMerged.lp (b i) (n i))) ^ 3 := by
          rw [Finset.mul_sum]
      _ = Cf * ∑ p ∈ (range L).image (fun i => (b i, n i)),
            1 / (Real.sqrt (JAMerged.lp p.1 p.2)) ^ 3 := by
          rw [Finset.sum_image hinj]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [one_div_pow]
      _ ≤ Cf * (2 * (1 / (Real.sqrt (Real.log 2)) ^ 3 + 1 / (Real.sqrt (Real.log 3)) ^ 3)) := by
          apply mul_le_mul_of_nonneg_left _ hCf
          apply JAMerged.sum_inv_cube_le
          intro p hp
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
          exact ⟨hb i, hn i (Finset.mem_range.mp hi)⟩
  have key := MixedPrimeAnalytic.product_bound_with_exceptions (range L) bad hbadsub f
    (fun i => Cf * (1 / Real.sqrt (JAMerged.lp (b i) (n i))) ^ 3)
    (fun i hi => by linarith [(hfB i (Finset.mem_range.mp hi)).1])
    (fun i => by positivity) B
    (Cf * (2 * (1 / (Real.sqrt (Real.log 2)) ^ 3 + 1 / (Real.sqrt (Real.log 3)) ^ 3)))
    (K + 2 * ⌊2 * T⌋₊) hB hbad_card
    (fun i hi => (hfB i (Finset.mem_range.mp (hbadsub hi))).2)
    (fun i hi => by
      obtain ⟨hiL, hibad⟩ := Finset.mem_sdiff.mp hi
      have hiL' := Finset.mem_range.mp hiL
      apply hgood i hiL'
      · intro hiE
        exact hibad (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiE, hiL'⟩))
      · by_contra hlt
        push Not at hlt
        exact hibad (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiL, hlt⟩)))
    hsum
  exact key

/-! ### Part B: the per-level factor bounds in the form `C (1/t)^3` -/

/-- `exp(-3t) ≤ (1/t)^3` for `t ≥ 1`. -/
lemma exp_neg3_le (t : ℝ) (ht : 1 ≤ t) : Real.exp (-(3 * t)) ≤ (1 / t) ^ 3 := by
  have ht0 : 0 < t := by linarith
  have h1 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have h2 : t ^ 3 ≤ (Real.exp t) ^ 3 := pow_le_pow_left₀ ht0.le (by linarith) 3
  have h3 : (Real.exp t) ^ 3 = Real.exp (3 * t) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h3] at h2
  rw [Real.exp_neg, one_div_pow, ← one_div]
  exact one_div_le_one_div_of_le (pow_pos ht0 3) h2

/-- `(1/t)^6 ≤ (1/t)^3` for `t ≥ 1`. -/
lemma inv_pow6_le (t : ℝ) (ht : 1 ≤ t) : 1 / t ^ 6 ≤ (1 / t) ^ 3 := by
  have ht0 : 0 < t := by linarith
  rw [one_div_pow]
  apply one_div_le_one_div_of_le (pow_pos ht0 3)
  exact pow_le_pow_right₀ ht (by norm_num)

/-- The right-hand side of `separated_factor` is at most `Cs (1/t)^3`. -/
lemma sep_cube (D t : ℝ) (hD : 3 ≤ D) (ht : 1 ≤ t) :
    200 * D ^ 4 / t ^ 6 +
        30 * D / 7 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
          ((1 / t) ^ 3 + 4 * ((8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * t))))) ≤
      (200 * D ^ 4 + 30 * D / 7 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
        (1 + 4 * (8 * (30 * D / 7)) ^ 2))) * (1 / t) ^ 3 := by
  have hD0 : 0 < D := by linarith
  set B : ℝ := 30 * D / 7 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hC0 : 0 ≤ 200 * D ^ 4 + 8 * B := by positivity
  have hs0 : 0 ≤ (1 / t) ^ 3 := by positivity
  have he := exp_neg3_le t ht
  have h6 := inv_pow6_le t ht
  have e1 : 200 * D ^ 4 / t ^ 6 = 200 * D ^ 4 * (1 / t ^ 6) := by ring
  have h8 : 0 ≤ (8 * B) ^ 2 := by positivity
  have h9 : (8 * B) ^ 2 * Real.exp (-(3 * t)) ≤ (8 * B) ^ 2 * (1 / t) ^ 3 :=
    mul_le_mul_of_nonneg_left he h8
  have h10 : (1 / t) ^ 3 + 4 * ((8 * B) ^ 2 * Real.exp (-(3 * t))) ≤
      (1 + 4 * (8 * B) ^ 2) * (1 / t) ^ 3 := by nlinarith
  have h11 : 512 * (200 * D ^ 4 + 8 * B) * ((1 / t) ^ 3 + 4 * ((8 * B) ^ 2 * Real.exp (-(3 * t)))) ≤
      512 * (200 * D ^ 4 + 8 * B) * ((1 + 4 * (8 * B) ^ 2) * (1 / t) ^ 3) :=
    mul_le_mul_of_nonneg_left h10 (by positivity)
  have h12 := mul_le_mul_of_nonneg_left h11 hB0
  have h13 : 200 * D ^ 4 * (1 / t ^ 6) ≤ 200 * D ^ 4 * (1 / t) ^ 3 :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  rw [e1]
  nlinarith [h12, h13]

/-- Large-`t` elementary inequality: `A log^2(2+t) + log t ≤ t`. -/
lemma log_sq_add_le (A t : ℝ) (hA : 0 ≤ A) (ht : (16 * A + 6) ^ 2 ≤ t) :
    A * (Real.log (2 + t)) ^ 2 + Real.log t ≤ t := by
  have hA6 : 0 < 16 * A + 6 := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hlam := JANonDeep.log_sq_le t ht0.le
  set ρ : ℝ := Real.sqrt (2 + t) with hρ
  have hρ2 : ρ ^ 2 = 2 + t := Real.sq_sqrt (by linarith)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρA : 16 * A + 6 ≤ ρ := by
    rw [hρ]; apply Real.le_sqrt_of_sq_le; nlinarith
  have hρ1 : 1 ≤ ρ := by linarith
  -- log t ≤ log (2 + t) ≤ 4 sqrt (sqrt (2+t)) ≤ 4 ρ
  have hz : 1 ≤ 2 + t := by linarith
  have hlog1 : Real.log t ≤ Real.log (2 + t) := Real.log_le_log ht0 (by linarith)
  have hlog2 := JANonDeep.log_le_four_rootroot (2 + t) hz
  have hrr : Real.sqrt (Real.sqrt (2 + t)) ≤ Real.sqrt (2 + t) := by
    have h1 : 1 ≤ Real.sqrt (2 + t) := by rw [← hρ]; exact hρ1
    exact Real.sqrt_le_iff.mpr ⟨Real.sqrt_nonneg _, by nlinarith⟩
  have hAl : A * (Real.log (2 + t)) ^ 2 ≤ A * (16 * ρ) := mul_le_mul_of_nonneg_left hlam hA
  nlinarith

/-- `CloseGrowth` for the original profile `a(t) = A log^2(2+t)`. -/
theorem closeGrowth_A (A : ℝ) (hA : 0 ≤ A) : CloseGrowth (fun t => A * (Real.log (2 + t)) ^ 2) :=
  ⟨(16 * A + 6) ^ 2, fun t hT _ => log_sq_add_le A t hA hT⟩

/-- `exp(3 a(t) - 3t) ≤ (1/t)^3` once `a(t) + log t ≤ t`. -/
lemma exp_close_le_G (a t : ℝ) (ht0 : 0 < t) (hk : a + Real.log t ≤ t) :
    Real.exp (3 * a - 3 * t) ≤ (1 / t) ^ 3 := by
  have h3 : Real.exp (3 * Real.log t) = t ^ 3 := by
    have := Real.exp_log (pow_pos ht0 3)
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hle : Real.exp (3 * a - 3 * t) ≤ Real.exp (-(3 * Real.log t)) := by
    apply Real.exp_le_exp.mpr
    linarith
  refine hle.trans ?_
  rw [Real.exp_neg, h3, one_div_pow]
  simp

/-- `exp(3A log^2(2+t) - 3t) ≤ (1/t)^3` for large `t`. -/
lemma exp_close_le (A t : ℝ) (hA : 0 ≤ A) (ht : (16 * A + 6) ^ 2 ≤ t) :
    Real.exp (3 * (A * (Real.log (2 + t)) ^ 2) - 3 * t) ≤ (1 / t) ^ 3 := by
  have hA6 : 0 < 16 * A + 6 := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  exact exp_close_le_G _ t ht0 (log_sq_add_le A t hA ht)

/-- The right-hand side of `close_factor` is at most `Cc (1/t)^3` for `t ≥ T`, for a general close-growth profile `a`. -/
lemma close_cube_G (D : ℝ) (a : ℝ → ℝ) (hD : 3 ≤ D) (hG : CloseGrowth a) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t q : ℝ, T ≤ t → 0 < q →
      200 * D ^ 4 / t ^ 6 +
          30 * D / 7 * (200 * D ^ 4 / (4 * t ^ 3) ^ 3) +
          (30 * D / 7) ^ 2 * (2048 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
            (1 / (Real.exp (-(a t)) / q * q)) ^ 3 *
            ((8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * t)))) ≤
        (200 * D ^ 4 + 30 * D / 7 * (200 * D ^ 4) +
          (30 * D / 7) ^ 2 * (2048 * (200 * D ^ 4 + 8 * (30 * D / 7)) * (8 * (30 * D / 7)) ^ 2)) *
          (1 / t) ^ 3 := by
  obtain ⟨T₀, hT₀⟩ := hG
  have hD0 : 0 < D := by linarith
  refine ⟨max 1 T₀, le_max_left _ _, ?_⟩
  intro t q hT hq
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) hT
  have htA : T₀ ≤ t := le_trans (le_max_right _ _) hT
  have ht0 : 0 < t := by linarith
  set B : ℝ := 30 * D / 7 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hs0 : 0 ≤ (1 / t) ^ 3 := by positivity
  -- the Matveev term
  have hsimp : (1 / (Real.exp (-(a t)) / q * q)) ^ 3 = Real.exp (3 * a t) := by
    rw [div_mul_cancel₀ _ hq.ne', one_div, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul]
    norm_num
  have hexp := exp_close_le_G (a t) t ht0 (hT₀ t htA ht1)
  have hprod : Real.exp (3 * a t) * Real.exp (-(3 * t)) ≤ (1 / t) ^ 3 := by
    rw [← Real.exp_add]
    have : 3 * a t + -(3 * t) = 3 * a t - 3 * t := by ring
    rw [this]; exact hexp
  have hC : 0 ≤ 200 * D ^ 4 + 8 * B := by positivity
  have h3 : B ^ 2 * (2048 * (200 * D ^ 4 + 8 * B) *
        Real.exp (3 * a t) * ((8 * B) ^ 2 * Real.exp (-(3 * t)))) ≤
      B ^ 2 * (2048 * (200 * D ^ 4 + 8 * B) * (8 * B) ^ 2) * (1 / t) ^ 3 := by
    have e : B ^ 2 * (2048 * (200 * D ^ 4 + 8 * B) * Real.exp (3 * a t) *
        ((8 * B) ^ 2 * Real.exp (-(3 * t)))) =
        B ^ 2 * (2048 * (200 * D ^ 4 + 8 * B) * (8 * B) ^ 2) *
          (Real.exp (3 * a t) * Real.exp (-(3 * t))) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  have h6 := inv_pow6_le t ht1
  have e1 : 200 * D ^ 4 / t ^ 6 = 200 * D ^ 4 * (1 / t ^ 6) := by ring
  have h13 : 200 * D ^ 4 * (1 / t ^ 6) ≤ 200 * D ^ 4 * (1 / t) ^ 3 :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  have h4 : 200 * D ^ 4 / (4 * t ^ 3) ^ 3 ≤ 200 * D ^ 4 * (1 / t) ^ 3 := by
    rw [div_eq_mul_one_div, one_div_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply one_div_le_one_div_of_le (pow_pos ht0 3)
    have h1 : 1 ≤ t ^ 3 := one_le_pow₀ ht1
    nlinarith [pow_pos ht0 3, pow_pos ht0 9, pow_nonneg ht0.le 6]
  have h14 := mul_le_mul_of_nonneg_left h4 hB0
  rw [hsimp, e1]
  nlinarith [h3, h13, h14]

/-- The original `A log^2(2+t)` form of `close_cube_G`. -/
lemma close_cube (D A : ℝ) (hD : 3 ≤ D) (hA : 0 ≤ A) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t q : ℝ, T ≤ t → 0 < q →
      200 * D ^ 4 / t ^ 6 +
          30 * D / 7 * (200 * D ^ 4 / (4 * t ^ 3) ^ 3) +
          (30 * D / 7) ^ 2 * (2048 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
            (1 / (Real.exp (-(A * (Real.log (2 + t)) ^ 2)) / q * q)) ^ 3 *
            ((8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * t)))) ≤
        (200 * D ^ 4 + 30 * D / 7 * (200 * D ^ 4) +
          (30 * D / 7) ^ 2 * (2048 * (200 * D ^ 4 + 8 * (30 * D / 7)) * (8 * (30 * D / 7)) ^ 2)) *
          (1 / t) ^ 3 :=
  close_cube_G D (fun t => A * (Real.log (2 + t)) ^ 2) hD (closeGrowth_A A hA)

#print axioms product_final
#print axioms sep_cube
#print axioms closeGrowth_A
#print axioms exp_close_le_G
#print axioms close_cube_G
#print axioms close_cube

end JAProductFinal
end LeanCheck
