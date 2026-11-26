import Mathlib
import LeanCheck.PVGTwoCountable

/-!
# PVGtwo, Theorem 4.7 and Corollary 4.8: a coefficient group of Hausdorff dimension 1 (Lean check)

Scope. `sT n = sS (n+1) = 2^((n+1)²)`, the terms `s_1, s_2, …` of the article, and `dlt k = 2^{-(4^k+k)}`. `Agroup = A(δ)`.
Digits are indexed from `0`: `ofDigits d = Σ d_i 2^{-(i+1)}`, so the article's digit at position `i` is `d (i-1)`. `Zset` is the set of
forced zero positions in this indexing.

* `ofDigits_mem` : a number whose digits vanish on `Zset` belongs to `A(δ)`;
* `dimH_Agroup` : Theorem 4.7, `dimH A(δ) = 1`;
* `dyadic_mem` : `A(δ)` contains the dyadic rationals;
* `dimension_witness` : Theorem 4.7, the properties of `γ_δ`;
* `dilates_totally_bounded` : Corollary 4.8, total boundedness of `aS` (with `gam_not_precompact`: `γ_δ` is not precompact).

Not formalized in this module: that `A(δ)` is a null set; see `PVG.Two.Agroup_null` in `PVGTwoNoWitness`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set Real
open scoped Pointwise NNReal ENNReal

namespace PVG
namespace Two
open Q95 Lac

noncomputable def sT (n : ℕ) : ℝ := sS (n + 1)

noncomputable def dlt (k : ℕ) : ℝ := ((2 : ℝ) ^ (4 ^ k + k))⁻¹

/-- `A(δ)` for this sequence. -/
def Agroup : Set ℝ := {a | InA dlt sT a}

/-- The forced zero positions. -/
def Zset : Set ℕ := {j | ∃ k n : ℕ, 2 ^ k < n ∧ n ^ 2 ≤ j + 4 ^ k + k ∧ j + 4 ^ k < n ^ 2}

lemma four_pow (k : ℕ) : (4 : ℕ) ^ k = (2 ^ k) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

lemma window_start {k n : ℕ} (h : 2 ^ k < n) : 4 ^ k + k + 2 ^ k ≤ n ^ 2 := by
  have h1 : (2 ^ k + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left h 2
  have h2 : k < 2 ^ k := Nat.lt_two_pow_self
  rw [four_pow]
  nlinarith

lemma dlt_pos (k : ℕ) : 0 < dlt k := by unfold dlt; positivity

lemma dlt_tendsto : Tendsto dlt atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero (fun k => (dlt_pos k).le) (fun k => ?_) h1
  rw [inv_pow]
  unfold dlt
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_add_left k (4 ^ k)))

/-- Below the window start the product is small. -/
lemma small_index (a : ℝ) (k n : ℕ) (hn : n ≤ 2 ^ k) : |a * dlt k * sS n| ≤ |a| * ((2 : ℝ) ^ k)⁻¹ := by
  have hn2 : n ^ 2 ≤ 4 ^ k := by rw [four_pow]; exact Nat.pow_le_pow_left hn 2
  have h1 : dlt k * sS n ≤ ((2 : ℝ) ^ k)⁻¹ := by
    unfold dlt sS
    rw [inv_mul_le_iff₀ (by positivity), pow_add, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
    exact pow_le_pow_right₀ (by norm_num) hn2
  have h0 : 0 ≤ dlt k * sS n := mul_nonneg (dlt_pos k).le (by unfold sS; positivity)
  rw [mul_assoc, abs_mul, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg a)

/-- Above the window start the product is `a 2^m`. -/
lemma large_index (a : ℝ) (k n : ℕ) (hn : 2 ^ k < n) : a * dlt k * sS n = a * 2 ^ (n ^ 2 - (4 ^ k + k)) := by
  have h : 4 ^ k + k ≤ n ^ 2 := le_trans (Nat.le_add_right _ _) (window_start hn)
  have e2 : (2 : ℝ) ^ (n ^ 2) = 2 ^ (n ^ 2 - (4 ^ k + k)) * 2 ^ (4 ^ k + k) := by
    rw [← pow_add, Nat.sub_add_cancel h]
  unfold dlt sS
  rw [e2]
  field_simp

lemma sum_digits_int (d : ℕ → Fin 2) (m : ℕ) :
    ∃ z : ℤ, (2 : ℝ) ^ m * ∑ i ∈ Finset.range m, Real.ofDigitsTerm d i = z := by
  refine ⟨∑ i ∈ Finset.range m, ((d i : ℕ) : ℤ) * 2 ^ (m - (i + 1)), ?_⟩
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i + 1 ≤ m := by have := Finset.mem_range.1 hi; omega
  have e1 : (2 : ℝ) ^ m = 2 ^ (m - (i + 1)) * 2 ^ (i + 1) := by rw [← pow_add, Nat.sub_add_cancel him]
  unfold Real.ofDigitsTerm
  push_cast
  rw [e1]
  field_simp

/-- A number whose digits vanish on the forced positions satisfies `‖a δ_k s_n‖ ≤ 2^{-k}`. -/
lemma ofDigits_bound (d : ℕ → Fin 2) (hd : ∀ j ∈ Zset, d j = 0) (k n : ℕ) :
    dint (Real.ofDigits d * dlt k * sS n) ≤ ((2 : ℝ) ^ k)⁻¹ := by
  by_cases hn : n ≤ 2 ^ k
  · refine (dint_le_abs _).trans ((small_index _ k n hn).trans ?_)
    rw [abs_of_nonneg (Real.ofDigits_nonneg d)]
    exact mul_le_of_le_one_left (by positivity) (Real.ofDigits_le_one d)
  · have hn' : 2 ^ k < n := by omega
    rw [large_index _ k n hn']
    set m := n ^ 2 - (4 ^ k + k) with hm
    have hs := Real.ofDigits_eq_sum_add_ofDigits d m
    set d1 : ℕ → Fin 2 := fun i => d (i + m) with hd1
    have hzero : ∀ i < k, d1 i = 0 := by
      intro i hi
      have h : 4 ^ k + k ≤ n ^ 2 := le_trans (Nat.le_add_right _ _) (window_start hn')
      have hmv : m + (4 ^ k + k) = n ^ 2 := Nat.sub_add_cancel h
      refine hd (i + m) ⟨k, n, hn', ?_, ?_⟩ <;> omega
    have htail : Real.ofDigits d1 ≤ ((2 : ℝ) ^ k)⁻¹ := by
      rw [Real.ofDigits_eq_sum_add_ofDigits d1 k]
      have h0 : ∑ i ∈ Finset.range k, Real.ofDigitsTerm d1 i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          simp [Real.ofDigitsTerm, hzero i (Finset.mem_range.1 hi)]
      rw [h0, zero_add]
      exact_mod_cast mul_le_of_le_one_right (by positivity) (Real.ofDigits_le_one _)
    obtain ⟨z, hz⟩ := sum_digits_int d m
    have e1 : Real.ofDigits d * 2 ^ m = Real.ofDigits d1 - ((-z : ℤ) : ℝ) := by
      rw [hs]
      push_cast
      rw [← hz]
      field_simp
      ring
    rw [e1, dint_sub_int]
    refine (dint_le_abs _).trans ?_
    rw [abs_of_nonneg (Real.ofDigits_nonneg _)]
    exact htail

lemma ofDigits_mem (d : ℕ → Fin 2) (hd : ∀ j ∈ Zset, d j = 0) : Real.ofDigits d ∈ Agroup := by
  intro ε hε
  have h1 : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [h1.eventually (Iio_mem_nhds hε)] with k hk n
  refine (ofDigits_bound d hd k (n + 1)).trans ?_
  rw [← inv_pow]; exact le_of_lt hk

theorem dyadic_mem (p : ℤ) (j : ℕ) : (p : ℝ) / 2 ^ j ∈ Agroup := by
  intro ε hε
  set a : ℝ := (p : ℝ) / 2 ^ j with ha
  have h1 : Tendsto (fun k : ℕ => |a| * ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).const_mul |a|
    simpa using this
  filter_upwards [h1.eventually (Iio_mem_nhds hε), eventually_ge_atTop j] with k hk hjk n
  show dint (a * dlt k * sS (n + 1)) ≤ ε
  by_cases hn : n + 1 ≤ 2 ^ k
  · refine (dint_le_abs _).trans ((small_index _ k _ hn).trans ?_)
    rw [← inv_pow]; exact le_of_lt hk
  · have hn' : 2 ^ k < n + 1 := by omega
    rw [large_index _ k _ hn']
    set m := (n + 1) ^ 2 - (4 ^ k + k) with hm
    have hjm : j ≤ m := by
      have h := window_start hn'
      have h2 : k < 2 ^ k := Nat.lt_two_pow_self
      have hmv' : m + (4 ^ k + k) = (n + 1) ^ 2 :=
        Nat.sub_add_cancel (le_trans (Nat.le_add_right _ _) h)
      omega
    have e1 : a * 2 ^ m = (0 : ℝ) - ((-(p * 2 ^ (m - j)) : ℤ) : ℝ) := by
      have e2 : (2 : ℝ) ^ m = 2 ^ (m - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel hjm]
      rw [ha, e2]
      push_cast
      field_simp
      ring
    rw [e1, dint_sub_int, dint_zero]
    exact hε.le

/-! ## The forced positions have density zero -/

open Classical in
noncomputable def Zcount (M : ℕ) : ℕ := Nat.count (fun j => j ∈ Zset) M

lemma Zcount_le (M : ℕ) (hM : 1 ≤ M) :
    (Zcount M : ℝ) ≤ ((Nat.log 2 M : ℝ) + 1) ^ 2 * ((Nat.sqrt (2 * M) : ℝ) + 1) := by
  classical
  set L := Nat.log 2 M with hL
  set R := Nat.sqrt (2 * M) with hR
  set W : ℕ → ℕ → Finset ℕ := fun k i =>
    Finset.Ico ((2 ^ k + i) ^ 2 - (4 ^ k + k)) ((2 ^ k + i) ^ 2 - 4 ^ k) with hW
  have hsub : (Finset.range M).filter (fun j => j ∈ Zset) ⊆
      (Finset.range (L + 1)).biUnion (fun k => (Finset.range (R + 1)).biUnion (fun i => W k i)) := by
    intro j hj
    obtain ⟨hjM, k, n, hn, h1, h2⟩ := Finset.mem_filter.1 hj
    have hjM' : j < M := Finset.mem_range.1 hjM
    have hw := window_start hn
    have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2k : 2 ^ k ≤ M := by
      by_contra hc
      have hn2 : (2 ^ k + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
      rw [four_pow] at h1
      nlinarith
    have hkL : k ≤ L := Nat.le_log_of_pow_le one_lt_two h2k
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn.le
    have hiR : i ≤ R := by
      rw [hR, Nat.le_sqrt]
      rw [four_pow] at h1
      have : i * i ≤ j + k := by nlinarith
      omega
    refine Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 (by omega), Finset.mem_biUnion.2
      ⟨i, Finset.mem_range.2 (by omega), Finset.mem_Ico.2 ⟨?_, ?_⟩⟩⟩ <;> omega
  have hcard : Zcount M ≤ (L + 1) * ((R + 1) * L) := by
    unfold Zcount
    rw [Nat.count_eq_card_filter_range]
    refine (Finset.card_le_card hsub).trans ?_
    have hin : ∀ k ∈ Finset.range (L + 1), ((Finset.range (R + 1)).biUnion (fun i => W k i)).card ≤ (R + 1) * L := by
      intro k hk
      have hkL : k ≤ L := by have := Finset.mem_range.1 hk; omega
      refine Finset.card_biUnion_le.trans ?_
      have : ∀ i ∈ Finset.range (R + 1), (W k i).card ≤ L := by
        intro i _
        rw [hW, Nat.card_Ico]
        omega
      refine (Finset.sum_le_sum this).trans ?_
      simp
    refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum hin).trans ?_)
    simp
  have h1 : (Zcount M : ℝ) ≤ ((L : ℝ) + 1) * (((R : ℝ) + 1) * L) := by exact_mod_cast hcard
  refine h1.trans ?_
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ L + 1 by linarith) (show (0 : ℝ) ≤ R + 1 by linarith))
    (show (0 : ℝ) ≤ 1 by norm_num)]

lemma Zcount_small {c : ℝ} (hc : 0 < c) : ∀ᶠ M : ℕ in atTop, (Zcount M : ℝ) ≤ c * M := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 : ℝ) / 4)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hq : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 4)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have hg : Tendsto (fun x : ℝ => (Real.log x / Real.log 2 + 1) / x ^ ((1 : ℝ) / 4)) atTop (𝓝 0) := by
    have h1 := hlog.div_const (Real.log 2)
    have h2 : Tendsto (fun x : ℝ => (x ^ ((1 : ℝ) / 4))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hq
    have h3 := h1.add h2
    rw [zero_div, zero_add] at h3
    refine h3.congr fun x => ?_
    ring
  have hev := (hg.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (Iio_mem_nhds (show (0 : ℝ) < min 1 (c / 3) from lt_min one_pos (by linarith)))
  filter_upwards [hev, eventually_ge_atTop 1] with M hM hM1
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set q : ℝ := (M : ℝ) ^ ((1 : ℝ) / 4) with hqd
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by linarith) _
  have hq2 : q ^ 2 = Real.sqrt M := by
    rw [Real.sqrt_eq_rpow, hqd, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hsq : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt M := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hMr
  have hM' : (Real.log M / Real.log 2 + 1) / q < min 1 (c / 3) := hM
  rw [div_lt_iff₀ hq0] at hM'
  have hlogb : (Nat.log 2 M : ℝ) ≤ Real.log M / Real.log 2 := by
    have := Real.natLog_le_logb M 2
    simpa [Real.logb] using this
  have hL1 : (Nat.log 2 M : ℝ) + 1 ≤ min 1 (c / 3) * q := by linarith
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) + 1 := by positivity
  have hsq2 : (Nat.sqrt (2 * M) : ℝ) + 1 ≤ 3 * Real.sqrt M := by
    have h1 : (Nat.sqrt (2 * M) : ℝ) ≤ Real.sqrt ((2 * M : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    have h2 : Real.sqrt ((2 * M : ℕ) : ℝ) ≤ 2 * Real.sqrt M := by
      rw [Real.sqrt_le_left (by positivity)]
      push_cast
      nlinarith
    linarith
  have hmin1 : min 1 (c / 3) ≤ 1 := min_le_left _ _
  have hmin2 : min 1 (c / 3) ≤ c / 3 := min_le_right _ _
  have hmin0 : 0 ≤ min 1 (c / 3) := le_min zero_le_one (by linarith)
  have hsqL : ((Nat.log 2 M : ℝ) + 1) ^ 2 ≤ c / 3 * Real.sqrt M := by
    have h1 : ((Nat.log 2 M : ℝ) + 1) ^ 2 ≤ (min 1 (c / 3) * q) ^ 2 := pow_le_pow_left₀ hL0 hL1 2
    have h2 : min 1 (c / 3) ^ 2 ≤ c / 3 := by
      have : min 1 (c / 3) * min 1 (c / 3) ≤ 1 * (c / 3) := mul_le_mul hmin1 hmin2 hmin0 zero_le_one
      nlinarith
    rw [mul_pow, hq2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _))
  refine (Zcount_le M hM1).trans ?_
  have h3 := mul_le_mul hsqL hsq2 (by positivity) (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
  refine h3.trans (le_of_eq ?_)
  have e1 : c / 3 * Real.sqrt M * (3 * Real.sqrt M) = c * (Real.sqrt M * Real.sqrt M) := by ring
  rw [e1, hsq]

/-! ## The Hölder map -/

/-- Digits allowed on the Cantor set. -/
def Allowed (d : ℕ → Fin 2) : Prop := ∀ j ∈ Zset, d j = 0

lemma forced_after (j0 : ℕ) : ∃ j1 ∈ Zset, j0 < j1 ∧ j1 ≤ j0 + 2 * Nat.sqrt (j0 + 5) + 1 := by
  set r := Nat.sqrt (j0 + 5) with hr
  have h1 : r * r ≤ j0 + 5 := Nat.sqrt_le _
  have h2 : j0 + 5 < (r + 1) * (r + 1) := Nat.lt_succ_sqrt _
  have h3 : 2 ≤ r := by rw [hr, Nat.le_sqrt]; omega
  have e1 : (r + 1) ^ 2 = (r + 1) * (r + 1) := sq (r + 1)
  have e2 : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by ring
  refine ⟨(r + 1) ^ 2 - 5, ⟨1, r + 1, by omega, ?_, ?_⟩, by omega, by omega⟩ <;> omega

/-- Two allowed expansions that first differ at `j0` give numbers at distance at least `2^{-(j1+1)}`. -/
lemma separation (d d' : ℕ → Fin 2) (hd : Allowed d) (hd' : Allowed d') (j0 j1 : ℕ)
    (hagree : ∀ i < j0, d i = d' i) (h1 : d j0 = 1) (h0 : d' j0 = 0) (hj1 : j1 ∈ Zset) (hlt : j0 < j1) :
    ((2 : ℝ) ^ (j1 + 1))⁻¹ ≤ Real.ofDigits d - Real.ofDigits d' := by
  set e1 : ℕ → Fin 2 := fun i => d (i + (j0 + 1)) with he1
  set e0 : ℕ → Fin 2 := fun i => d' (i + (j0 + 1)) with he0
  set m := j1 - (j0 + 1) with hm
  have hz : e0 m = 0 := by
    have : m + (j0 + 1) = j1 := by omega
    show d' (m + (j0 + 1)) = 0
    rw [this]; exact hd' j1 hj1
  have hup : Real.ofDigits e0 ≤ 1 - ((2 : ℝ) ^ (m + 1))⁻¹ := by
    rw [Real.ofDigits_eq_sum_add_ofDigits e0 (m + 1)]
    have hsum : ∑ i ∈ Finset.range (m + 1), Real.ofDigitsTerm e0 i ≤ 1 - ((2 : ℝ) ^ m)⁻¹ := by
      rw [Finset.sum_range_succ]
      have hlast : Real.ofDigitsTerm e0 m = 0 := by simp [Real.ofDigitsTerm, hz]
      rw [hlast, add_zero]
      have hgeo : ∀ N : ℕ, ∑ i ∈ Finset.range N, Real.ofDigitsTerm e0 i ≤ 1 - ((2 : ℝ) ^ N)⁻¹ := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Finset.sum_range_succ]
          have hb : Real.ofDigitsTerm e0 N ≤ ((2 : ℝ) ^ (N + 1))⁻¹ := by
            have h := Real.ofDigitsTerm_le (digits := e0) (n := N)
            norm_num at h ⊢
            exact h
          have e2 : ((2 : ℝ) ^ N)⁻¹ = 2 * ((2 : ℝ) ^ (N + 1))⁻¹ := by
            rw [pow_succ]; field_simp
          linarith
      exact hgeo m
    have htail : (((2 : ℕ) : ℝ) ^ (m + 1))⁻¹ * Real.ofDigits (fun i => e0 (i + (m + 1))) ≤ ((2 : ℝ) ^ (m + 1))⁻¹ := by
      exact_mod_cast mul_le_of_le_one_right (by positivity) (Real.ofDigits_le_one _)
    have e2 : ((2 : ℝ) ^ m)⁻¹ = 2 * ((2 : ℝ) ^ (m + 1))⁻¹ := by
      rw [pow_succ]; field_simp
    linarith
  have hs := Real.ofDigits_eq_sum_add_ofDigits d (j0 + 1)
  have hs' := Real.ofDigits_eq_sum_add_ofDigits d' (j0 + 1)
  have hpre : ∑ i ∈ Finset.range (j0 + 1), Real.ofDigitsTerm d i =
      ∑ i ∈ Finset.range (j0 + 1), Real.ofDigitsTerm d' i + ((2 : ℝ) ^ (j0 + 1))⁻¹ := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hsame : ∑ i ∈ Finset.range j0, Real.ofDigitsTerm d i = ∑ i ∈ Finset.range j0, Real.ofDigitsTerm d' i :=
      Finset.sum_congr rfl fun i hi => by simp [Real.ofDigitsTerm, hagree i (Finset.mem_range.1 hi)]
    have ha : Real.ofDigitsTerm d j0 = ((2 : ℝ) ^ (j0 + 1))⁻¹ := by simp [Real.ofDigitsTerm, h1]
    have hb : Real.ofDigitsTerm d' j0 = 0 := by simp [Real.ofDigitsTerm, h0]
    rw [hsame, ha, hb, add_zero]
  have hdiff : Real.ofDigits d - Real.ofDigits d' =
      ((2 : ℝ) ^ (j0 + 1))⁻¹ * (1 + Real.ofDigits e1 - Real.ofDigits e0) := by
    rw [hs, hs', hpre, he1, he0]
    push_cast
    ring
  have hpow : ((2 : ℝ) ^ (j1 + 1))⁻¹ = ((2 : ℝ) ^ (j0 + 1))⁻¹ * ((2 : ℝ) ^ (m + 1))⁻¹ := by
    rw [← mul_inv, ← pow_add]; congr 2; omega
  rw [hdiff, hpow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := Real.ofDigits_nonneg e1
  linarith

lemma free_infinite : {j : ℕ | j ∉ Zset}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨M, hM⟩ := eventually_atTop.1 (Zcount_small (show (0 : ℝ) < 1 / 2 by norm_num))
  classical
  set P := max M (2 * (N + 1) + 1) with hP
  have h1 := hM P (le_max_left _ _)
  have h2 : P - (N + 1) ≤ Zcount P := by
    unfold Zcount
    rw [Nat.count_eq_card_filter_range]
    have hsub : Finset.Ico (N + 1) P ⊆ (Finset.range P).filter (fun j => j ∈ Zset) := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hj2, ?_⟩
      by_contra hc
      have := hN hc
      omega
    have := Finset.card_le_card hsub
    rwa [Nat.card_Ico] at this
  have h3 : 2 * (N + 1) + 1 ≤ P := le_max_right _ _
  have h4 : ((P - (N + 1) : ℕ) : ℝ) ≤ (Zcount P : ℝ) := by exact_mod_cast h2
  rw [Nat.cast_sub (by omega)] at h4
  have h5 : (2 : ℝ) * ((N : ℝ) + 1) + 1 ≤ (P : ℝ) := by exact_mod_cast h3
  push_cast at h4
  linarith

/-- The enumeration of the free positions. -/
noncomputable def freePos (i : ℕ) : ℕ := Nat.nth (fun j => j ∉ Zset) i

lemma freePos_mem (i : ℕ) : freePos i ∉ Zset := Nat.nth_mem_of_infinite free_infinite i

open Classical in
noncomputable def freeCount (j : ℕ) : ℕ := Nat.count (fun j => j ∉ Zset) j

lemma freePos_lt {i j : ℕ} (h : i < freeCount j) : freePos i < j := by
  classical
  exact Nat.nth_lt_of_lt_count h

lemma freeCount_add (M : ℕ) : freeCount M + Zcount M = M := by
  classical
  unfold freeCount Zcount
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range, add_comm]
  have := Finset.card_filter_add_card_filter_not (s := Finset.range M) (fun j => j ∈ Zset)
  simpa using this

lemma exponent_bound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ c : ℝ, ∀ j0 : ℕ, s * ((j0 : ℝ) + 2 * (Nat.sqrt (j0 + 5) : ℝ) + 2) - c ≤ freeCount j0 := by
  have hgap : 0 < (1 - s) / 2 := by linarith
  have hev : ∀ᶠ j0 : ℕ in atTop, s * ((j0 : ℝ) + 2 * (Nat.sqrt (j0 + 5) : ℝ) + 2) ≤ freeCount j0 := by
    have h1 := Zcount_small hgap
    have h2 : ∀ᶠ j0 : ℕ in atTop, 2 * (Nat.sqrt (j0 + 5) : ℝ) + 2 ≤ (1 - s) / 2 * j0 := by
      have hsq : Tendsto (fun j0 : ℕ => Real.sqrt (j0 : ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      filter_upwards [hsq.eventually_ge_atTop (8 / ((1 - s) / 2)), eventually_ge_atTop 5] with j hj hj5
      have hj5' : (5 : ℝ) ≤ j := by exact_mod_cast hj5
      have hsj : Real.sqrt j * Real.sqrt j = j := Real.mul_self_sqrt (by linarith)
      have h3 : (Nat.sqrt (j + 5) : ℝ) ≤ 2 * Real.sqrt j := by
        have h4 : (Nat.sqrt (j + 5) : ℝ) ≤ Real.sqrt ((j + 5 : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
        have h5 : Real.sqrt ((j + 5 : ℕ) : ℝ) ≤ 2 * Real.sqrt j := by
          rw [Real.sqrt_le_left (by positivity)]
          push_cast
          nlinarith
        linarith
      have h6 : 1 ≤ Real.sqrt j := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
      have h7 : 8 ≤ (1 - s) / 2 * Real.sqrt j := by
        have := mul_le_mul_of_nonneg_left hj hgap.le
        rwa [mul_div_cancel₀ _ hgap.ne'] at this
      have h8 := mul_le_mul_of_nonneg_right h7 (Real.sqrt_nonneg j)
      rw [mul_assoc, hsj] at h8
      linarith
    filter_upwards [h1, h2] with j hj1 hj2
    have h3 : (freeCount j : ℝ) + (Zcount j : ℝ) = j := by exact_mod_cast freeCount_add j
    have hz0 : (0 : ℝ) ≤ Nat.sqrt (j + 5) := Nat.cast_nonneg _
    have h4 : s * (2 * (Nat.sqrt (j + 5) : ℝ) + 2) ≤ 2 * (Nat.sqrt (j + 5) : ℝ) + 2 :=
      mul_le_of_le_one_left (by linarith) hs1.le
    nlinarith
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
  set g : ℕ → ℝ := fun j0 => s * ((j0 : ℝ) + 2 * (Nat.sqrt (j0 + 5) : ℝ) + 2) with hg
  have hg0 : ∀ j, 0 ≤ g j := fun j => mul_nonneg hs0.le (by positivity)
  refine ⟨∑ j ∈ Finset.range J, g j, fun j0 => ?_⟩
  have hsum : 0 ≤ ∑ j ∈ Finset.range J, g j := Finset.sum_nonneg fun j _ => hg0 j
  by_cases h : J ≤ j0
  · have := hJ j0 h
    linarith
  · have h1 : g j0 ≤ ∑ j ∈ Finset.range J, g j :=
      Finset.single_le_sum (fun j _ => hg0 j) (Finset.mem_range.2 (by omega))
    have h2 : (0 : ℝ) ≤ freeCount j0 := Nat.cast_nonneg _
    have h3 : g j0 = s * ((j0 : ℝ) + 2 * (Nat.sqrt (j0 + 5) : ℝ) + 2) := rfl
    linarith

/-- The Cantor set of numbers with allowed digits. -/
def Cset : Set ℝ := {a | ∃ d, Allowed d ∧ Real.ofDigits d = a}

open Classical in
noncomputable def holderMap (a : ℝ) : ℝ :=
  if h : a ∈ Cset then Real.ofDigits (fun i => Classical.choose h (freePos i)) else 0

lemma holder_estimate (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (c : ℝ)
    (hc : ∀ j0 : ℕ, s * ((j0 : ℝ) + 2 * (Nat.sqrt (j0 + 5) : ℝ) + 2) - c ≤ freeCount j0)
    (d d' : ℕ → Fin 2) (hd : Allowed d) (hd' : Allowed d') :
    |Real.ofDigits (fun i => d (freePos i)) - Real.ofDigits (fun i => d' (freePos i))| ≤
      (2 : ℝ) ^ c * |Real.ofDigits d - Real.ofDigits d'| ^ s := by
  by_cases heq : d = d'
  · subst heq
    simp only [sub_self, abs_zero]
    positivity
  have hex : ∃ i, d i ≠ d' i := Function.ne_iff.1 heq
  classical
  set j0 := Nat.find hex with hj0
  have hne : d j0 ≠ d' j0 := Nat.find_spec hex
  have hagree : ∀ i < j0, d i = d' i := fun i hi => not_not.1 (Nat.find_min hex hi)
  obtain ⟨j1, hj1, hlt, hle⟩ := forced_after j0
  have hsep : ((2 : ℝ) ^ (j1 + 1))⁻¹ ≤ |Real.ofDigits d - Real.ofDigits d'| := by
    have htwo : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases htwo (d j0) with h | h <;> rcases htwo (d' j0) with h' | h'
    · exact absurd (h.trans h'.symm) hne
    · rw [abs_sub_comm]
      exact (separation d' d hd' hd j0 j1 (fun i hi => (hagree i hi).symm) h' h hj1 hlt).trans (le_abs_self _)
    · exact (separation d d' hd hd' j0 j1 hagree h h' hj1 hlt).trans (le_abs_self _)
    · exact absurd (h.trans h'.symm) hne
  have hup : |Real.ofDigits (fun i => d (freePos i)) - Real.ofDigits (fun i => d' (freePos i))| ≤
      (((2 : ℕ) : ℝ) ^ freeCount j0)⁻¹ :=
    Real.abs_ofDigits_sub_ofDigits_le fun i hi => hagree _ (freePos_lt hi)
  refine hup.trans ?_
  have h2 : (0 : ℝ) < 2 := two_pos
  have e1 : (((2 : ℕ) : ℝ) ^ freeCount j0)⁻¹ = (2 : ℝ) ^ (-(freeCount j0 : ℝ)) := by
    rw [Real.rpow_neg h2.le, Real.rpow_natCast]; norm_num
  have e2 : ((2 : ℝ) ^ (j1 + 1))⁻¹ = (2 : ℝ) ^ (-((j1 : ℝ) + 1)) := by
    rw [Real.rpow_neg h2.le]
    congr 1
    rw [← Real.rpow_natCast]; push_cast; rfl
  have h3 : ((2 : ℝ) ^ (-((j1 : ℝ) + 1))) ^ s ≤ |Real.ofDigits d - Real.ofDigits d'| ^ s := by
    rw [← e2]
    exact Real.rpow_le_rpow (by positivity) hsep hs0.le
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg h2.le c))
  rw [e1, ← Real.rpow_mul h2.le, ← Real.rpow_add h2]
  refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
  have h4 := hc j0
  have h5 : (j1 : ℝ) + 1 ≤ (j0 : ℝ) + 2 * (Nat.sqrt (j0 + 5) : ℝ) + 2 := by
    have : j1 + 1 ≤ j0 + 2 * Nat.sqrt (j0 + 5) + 2 := by omega
    exact_mod_cast this
  have h6 := mul_le_mul_of_nonneg_left h5 hs0.le
  nlinarith

lemma Ico_subset_image : Ico (0 : ℝ) 1 ⊆ holderMap '' Cset := by
  intro y hy
  classical
  set g : ℕ → Fin 2 := Real.digits y 2 with hg
  set d : ℕ → Fin 2 := fun j => if j ∈ Zset then 0 else g (freeCount j) with hd
  have hdA : Allowed d := fun j hj => by simp [hd, hj]
  have hmem : Real.ofDigits d ∈ Cset := ⟨d, hdA, rfl⟩
  refine ⟨Real.ofDigits d, hmem, ?_⟩
  unfold holderMap
  rw [dif_pos hmem]
  obtain ⟨hA, hval⟩ := Classical.choose_spec hmem
  have hsame : Classical.choose hmem = d := by
    by_contra hne
    have hex : ∃ i, Classical.choose hmem i ≠ d i := Function.ne_iff.1 hne
    set j0 := Nat.find hex with hj0
    have h1 : Classical.choose hmem j0 ≠ d j0 := Nat.find_spec hex
    have h2 : ∀ i < j0, Classical.choose hmem i = d i := fun i hi => not_not.1 (Nat.find_min hex hi)
    obtain ⟨j1, hj1, hlt, _⟩ := forced_after j0
    have htwo : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ (j1 + 1))⁻¹ := by positivity
    rcases htwo (Classical.choose hmem j0) with h | h <;> rcases htwo (d j0) with h' | h'
    · exact h1 (h.trans h'.symm)
    · have := separation d _ hdA hA j0 j1 (fun i hi => (h2 i hi).symm) h' h hj1 hlt
      rw [hval] at this
      linarith
    · have := separation _ d hA hdA j0 j1 h2 h h' hj1 hlt
      rw [hval] at this
      linarith
    · exact h1 (h.trans h'.symm)
  rw [hsame]
  have hcomp : (fun i => d (freePos i)) = g := by
    funext i
    have h1 : freePos i ∉ Zset := freePos_mem i
    have h2 : freeCount (freePos i) = i := Nat.count_nth_of_infinite free_infinite i
    simp [hd, h1, h2]
  rw [hcomp]
  exact Real.ofDigits_digits one_lt_two hy

lemma one_le_dimH_Cset : (1 : ℝ≥0∞) ≤ dimH Cset := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  have hr1 : r < 1 := by exact_mod_cast hr
  by_cases hr0 : r = 0
  · simp [hr0]
  have hr0' : 0 < r := pos_iff_ne_zero.2 hr0
  have hs0 : (0 : ℝ) < r := by exact_mod_cast hr0'
  have hs1 : (r : ℝ) < 1 := by exact_mod_cast hr1
  obtain ⟨c, hc⟩ := exponent_bound r hs0 hs1
  have hH : HolderOnWith ((2 : ℝ) ^ c).toNNReal r holderMap Cset := by
    intro x hx y hy
    have hxv := Classical.choose_spec hx
    have hyv := Classical.choose_spec hy
    have hest := holder_estimate r hs0 hs1 c hc _ _ hxv.1 hyv.1
    rw [hxv.2, hyv.2] at hest
    have hfx : holderMap x = Real.ofDigits (fun i => Classical.choose hx (freePos i)) := dif_pos hx
    have hfy : holderMap y = Real.ofDigits (fun i => Classical.choose hy (freePos i)) := dif_pos hy
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, hfx, hfy,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs0.le]
    have e1 : ((((2 : ℝ) ^ c).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ c) := rfl
    rw [e1, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hest
  have himg := hH.dimH_image_le hr0'
  have h1 : (1 : ℝ≥0∞) ≤ dimH (holderMap '' Cset) := by
    have h2 : dimH (Ico (0 : ℝ) 1) = 1 := by
      have h3 : Ico (0 : ℝ) 1 ∈ 𝓝 (1 / 2 : ℝ) := Ico_mem_nhds (by norm_num) (by norm_num)
      rw [Real.dimH_of_mem_nhds h3]
      simp
    rw [← h2]
    exact dimH_mono Ico_subset_image
  have h4 := h1.trans himg
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hr0)) (Or.inl ENNReal.coe_ne_top), one_mul] at h4
  exact h4

/-- Theorem 4.7: `A(δ)` has Hausdorff dimension `1`. -/
theorem dimH_Agroup : dimH Agroup = 1 := by
  refine le_antisymm ?_ ?_
  · rw [← Real.dimH_univ]
    exact dimH_mono (subset_univ _)
  · refine one_le_dimH_Cset.trans (dimH_mono ?_)
    rintro a ⟨d, hd, rfl⟩
    exact ofDigits_mem d hd

/-- Theorem 4.7: the properties of `γ_δ`. -/
theorem dimension_witness :
    @IsTopologicalAddGroup ℝ (gamTop dlt) _ ∧ LQC (gamTop dlt) ∧ gamTop dlt ≤ bohrTop ∧ gamTop dlt ≠ bohrTop ∧
      (∀ x : ℝ, euclidNhds x ≤ @nhds ℝ (gamTop dlt) x) ∧
      ∀ (m : ℝ) (l : List ℝ), (∀ a ∈ l, a ∈ Agroup) → ∀ J : Set ℝ, J ⊆ Icc (-m) m + sumT sT l →
        TopologicalSpace.induced (Subtype.val : J → ℝ) (gamTop dlt) =
          TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop := by
  have hinf := infinite_range_of_tendsto dlt (fun k => (dlt_pos k).ne') dlt_tendsto
  have hM : ∀ k, |dlt k| ≤ 1 := by
    intro k
    rw [abs_of_pos (dlt_pos k)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  exact ⟨gam_group _, gam_lqc _, gam_le_bohr _, gam_ne_bohr _ hinf, gam_coarser_euclid _ 1 hM,
    fun m l hl J hJ => trace_eq dlt sT dlt_tendsto m l hl J hJ⟩

lemma Agroup_neg {a : ℝ} (ha : a ∈ Agroup) : -a ∈ Agroup := by
  intro ε hε
  filter_upwards [ha ε hε] with k hk n
  have e1 : -a * dlt k * sT n = -(a * dlt k * sT n) := by ring
  rw [e1, dint_neg]
  exact hk n

lemma Sset_subset_Tset : Sset ⊆ Tset sT := by
  rintro x (rfl | ⟨n, hn, h⟩)
  · exact Or.inl rfl
  · refine Or.inr ⟨n - 1, ?_⟩
    have e1 : sT (n - 1) = sS n := by
      unfold sT; rw [Nat.sub_add_cancel hn]
    rw [e1]; exact h

/-- Corollary 4.8: `aS` is `γ_δ`-totally bounded for `a ∈ A(δ)`. -/
theorem dilates_totally_bounded (a : ℝ) (ha : a ∈ Agroup) (W : Set ℝ) (hW : W ∈ @nhds ℝ (gamTop dlt) 0) :
    ∃ F : Finset ℝ, ∀ s ∈ Sset, ∃ f ∈ F, a * s - f ∈ W := by
  have hsub : Ja a ⊆ Icc (-0 : ℝ) 0 + sumT sT [a, -a] := by
    rintro x ⟨s, hs, t, ht, rfl⟩
    refine Set.mem_add.2 ⟨0, by norm_num, a * s + (-a) * t, ?_, zero_add _⟩
    refine Set.mem_add.2 ⟨a * s, ⟨s, Sset_subset_Tset hs, rfl⟩, (-a) * t, ?_, rfl⟩
    exact Set.mem_add.2 ⟨(-a) * t, ⟨t, Sset_subset_Tset ht, rfl⟩, 0, rfl, add_zero _⟩
  have hl : ∀ b ∈ [a, -a], InA dlt sT b := by
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ha
    · rw [List.mem_singleton] at hb
      rw [hb]; exact Agroup_neg ha
  exact totbdd (gamTop dlt) a (trace_eq dlt sT dlt_tendsto 0 [a, -a] hl (Ja a) hsub) W hW

end Two
end PVG
