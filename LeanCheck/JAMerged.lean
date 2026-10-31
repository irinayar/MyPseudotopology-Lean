import Mathlib
import LeanCheck.MixedPrimeAnalytic

/-!
# Merged growth of the two period chains (components 12 and 13 of the JA proof)

The periods of the normalized-product argument are the numbers `b^(n^2)` with `b ∈ {2,3}` and `n ≥ 1`.
Write `lp b n = n^2 * log b` for the logarithm of the period and `t = sqrt (lp b n)`.

Checked here (no axiom, no `sorry`):

* `same_chain_gap`: two distinct periods of the same base differ in logarithm by more than `sqrt` of the smaller
  logarithm (this is the numerical spacing `square_level_gap` of `MixedPrimeAnalytic`, applied to the real chain);
* `merged_gap3`: among three increasing periods of the two chains, the span is at least `sqrt (lp)` of the smallest
  (pigeonhole over the two colours, via `two_colour_three_level_span`), i.e. `Q_{i+2}/Q_i ≥ e^{t_i}`;
* `merged_gap_seq`, `merged_gap_seq_odd`: `Q_{i+m}/Q_i ≥ e^{t_i ⌊m/2⌋}` for every increasing selection of periods,
  with no condition on which periods are selected (equation (merged-growth) of the paper);
* `chain_window_one`, `window_card_le_two`: a logarithmic window of width at most `sqrt u` above `u` contains at most
  one period of each base, hence at most two periods (the count of non-deep levels);
* `inv_cube_sum_le`, `sum_inv_cube_le`: for every finite set of distinct periods the sum of `t^(-3)` is bounded by
  `2 ((log 2)^(-3/2) + (log 3)^(-3/2))`, uniformly in the number of periods.

Not checked here: the asymptotic statement that the non-deep window has width `O((log log X)^2)`, and the lifting of
these counts to the products of the factors `f_i` (that needs the window-kernel bounds).
-/

namespace LeanCheck
namespace JAMerged

open MixedPrimeAnalytic

/-- Logarithm of the period `b^(n^2)`. -/
noncomputable def lp (b n : ℕ) : ℝ := (n : ℝ) ^ 2 * Real.log b

lemma log_ge_quarter {b : ℕ} (hb : 2 ≤ b) : (1 / 4 : ℝ) ≤ Real.log b := by
  have h2 : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) (by exact_mod_cast hb)
  have := Real.log_two_gt_d9
  linarith

lemma sqrt_lp (b n : ℕ) : Real.sqrt (lp b n) = n * Real.sqrt (Real.log b) := by
  unfold lp
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

lemma lp_nonneg {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : 0 ≤ lp b n := by
  unfold lp
  have := log_ge_quarter hb
  positivity

lemma lp_mono {b : ℕ} (hb : 2 ≤ b) {n m : ℕ} (h : m ≤ n) : lp b m ≤ lp b n := by
  unfold lp
  have := log_ge_quarter hb
  have hh : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    have : (m : ℝ) ≤ n := by exact_mod_cast h
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  exact mul_le_mul_of_nonneg_right hh (by linarith)

lemma lp_strict {b : ℕ} (hb : 2 ≤ b) {n m : ℕ} (h : lp b n < lp b m) : n < m := by
  by_contra hc
  push Not at hc
  exact absurd (lp_mono hb hc) (not_le.mpr h)

/-- Two distinct periods of the same base: the logarithms differ by more than `sqrt` of the smaller one. -/
theorem same_chain_gap {b n m : ℕ} (hb : 2 ≤ b) (hnm : n < m) :
    Real.sqrt (lp b n) < lp b m - lp b n := by
  have ha := log_ge_quarter hb
  have h1 := square_level_gap (Real.log b) ha n
  rw [sqrt_lp]
  have hm : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnm
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h2 : (((n : ℝ) + 1) ^ 2 - (n : ℝ) ^ 2) * Real.log b ≤ ((m : ℝ) ^ 2 - (n : ℝ) ^ 2) * Real.log b :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  unfold lp
  nlinarith

/-- **Three increasing periods of the two chains span at least `sqrt (lp)` of the smallest.** -/
theorem merged_gap3 (b n : Fin 3 → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3)
    (h01 : lp (b 0) (n 0) < lp (b 1) (n 1)) (h12 : lp (b 1) (n 1) < lp (b 2) (n 2)) :
    Real.sqrt (lp (b 0) (n 0)) ≤ lp (b 2) (n 2) - lp (b 0) (n 0) := by
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h <;> omega
  have hle : ∀ i, lp (b 0) (n 0) ≤ lp (b i) (n i) := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact h01.le
    · exact (h01.trans h12).le
  apply two_colour_three_level_span (fun i => decide (b i = 2)) (fun i => lp (b i) (n i)) _
    h01.le h12.le
  intro i j hij hc
  have hbij : b i = b j := by
    rcases hb i with hi | hi <;> rcases hb j with hj | hj <;> simp_all
  have hlt : lp (b i) (n i) < lp (b j) (n j) := by
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | skip
    · exact h01
    · exact h01.trans h12
    · exact h12
  have hnm : n i < n j := by
    rw [hbij] at hlt
    exact lp_strict (hb2 j) hlt
  have hgap := same_chain_gap (hb2 i) hnm
  have hs : Real.sqrt (lp (b 0) (n 0)) ≤ Real.sqrt (lp (b i) (n i)) :=
    Real.sqrt_le_sqrt (hle i)
  have hbj : lp (b j) (n j) = lp (b i) (n j) := by rw [hbij]
  show Real.sqrt (lp (b 0) (n 0)) ≤ lp (b j) (n j) - lp (b i) (n i)
  rw [hbj]
  linarith

/-- **Merged growth for every increasing selection**: `log Q_{i+2j} - log Q_i ≥ j sqrt (log Q_i)`. -/
theorem merged_gap_seq (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3)
    (hmono : StrictMono (fun i => lp (b i) (n i))) (i j : ℕ) :
    (j : ℝ) * Real.sqrt (lp (b i) (n i)) ≤ lp (b (i + 2 * j)) (n (i + 2 * j)) - lp (b i) (n i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep := merged_gap3 (fun k : Fin 3 => b (i + 2 * j + k)) (fun k : Fin 3 => n (i + 2 * j + k))
      (fun k => hb _) (hmono (by simp)) (hmono (by simp))
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero] at hstep
    have hge : Real.sqrt (lp (b i) (n i)) ≤ Real.sqrt (lp (b (i + 2 * j)) (n (i + 2 * j))) :=
      Real.sqrt_le_sqrt (hmono.monotone (by omega))
    have e : i + 2 * (j + 1) = i + 2 * j + 2 := by ring
    rw [e]
    push_cast
    nlinarith

/-- The same, for an arbitrary offset `m` (the exponent is `⌊m/2⌋`). -/
theorem merged_gap_seq_odd (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3)
    (hmono : StrictMono (fun i => lp (b i) (n i))) (i m : ℕ) :
    ((m / 2 : ℕ) : ℝ) * Real.sqrt (lp (b i) (n i)) ≤ lp (b (i + m)) (n (i + m)) - lp (b i) (n i) := by
  have h1 := merged_gap_seq b n hb hmono i (m / 2)
  have h2 : lp (b (i + 2 * (m / 2))) (n (i + 2 * (m / 2))) ≤ lp (b (i + m)) (n (i + m)) :=
    hmono.monotone (by omega)
  linarith

/-- Exponential form: `Q_{i+m} ≥ Q_i * exp (t_i ⌊m/2⌋)` for `Q = exp ∘ lp`, `t_i = sqrt (log Q_i)`. -/
theorem merged_growth_exp (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3)
    (hmono : StrictMono (fun i => lp (b i) (n i))) (i m : ℕ) :
    Real.exp (lp (b i) (n i)) * Real.exp (Real.sqrt (lp (b i) (n i)) * ((m / 2 : ℕ) : ℝ)) ≤
      Real.exp (lp (b (i + m)) (n (i + m))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := merged_gap_seq_odd b n hb hmono i m
  linarith

/-- In a logarithmic window of width at most `sqrt u`, one base contributes at most one period. -/
theorem chain_window_one {b n m : ℕ} (hb : 2 ≤ b) (u v : ℝ) (hu : u ≤ lp b n) (hm : lp b m ≤ v)
    (hnm : n < m) : Real.sqrt u < v - u := by
  have h1 := same_chain_gap hb hnm
  have h2 : Real.sqrt u ≤ Real.sqrt (lp b n) := Real.sqrt_le_sqrt hu
  linarith

/-- **At most two periods in a window** `[u, v]` with `v - u ≤ sqrt u`: the number of non-deep levels is bounded. -/
theorem window_card_le_two (s : Finset (ℕ × ℕ)) (u v : ℝ) (hw : v - u ≤ Real.sqrt u)
    (hs : ∀ p ∈ s, (p.1 = 2 ∨ p.1 = 3) ∧ u ≤ lp p.1 p.2 ∧ lp p.1 p.2 ≤ v) : s.card ≤ 2 := by
  have hcard : s.card ≤ ({2, 3} : Finset ℕ).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      have := (hs p hp).1
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact this
    · intro p hp q hq hpq
      have hp' := hs p hp
      have hq' := hs q hq
      have hb2 : 2 ≤ p.1 := by rcases hp'.1 with h | h <;> omega
      by_contra hne
      have hn : p.2 ≠ q.2 := fun h => hne (Prod.ext hpq h)
      rcases lt_or_gt_of_ne hn with h | h
      · have := chain_window_one (b := p.1) (n := p.2) (m := q.2) hb2 u v hp'.2.1
          (by rw [hpq]; exact hq'.2.2) h
        linarith
      · have := chain_window_one (b := q.1) (n := q.2) (m := p.2) (by rw [← hpq]; exact hb2) u v hq'.2.1
          (by rw [← hpq]; exact hp'.2.2) h
        linarith
  simpa using hcard

lemma icc_cube (N : ℕ) (hN : 1 ≤ N) : ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) ^ 3 ≤ 2 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have key : 1 / ((N + 1 : ℕ) : ℝ) ^ 3 ≤ 1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hN0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hN0 hN0, mul_pos (mul_pos hN0 hN0) hN0, sq_nonneg ((N : ℝ) + 1)]
    linarith

/-- `sum n^(-3) ≤ 2` over any finite set of positive integers. -/
lemma inv_cube_sum_set (t : Finset ℕ) (ht : ∀ n ∈ t, 1 ≤ n) : ∑ n ∈ t, 1 / (n : ℝ) ^ 3 ≤ 2 := by
  have hsub : t ⊆ Finset.Icc 1 (t.sup id) := by
    intro n hn
    rw [Finset.mem_Icc]
    exact ⟨ht n hn, Finset.le_sup (f := id) hn⟩
  calc ∑ n ∈ t, 1 / (n : ℝ) ^ 3 ≤ ∑ n ∈ Finset.Icc 1 (t.sup id), 1 / (n : ℝ) ^ 3 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ ≤ 2 := by
        rcases Nat.eq_zero_or_pos (t.sup id) with h0 | h0
        · rw [h0]; simp
        · have := icc_cube (t.sup id) h0
          have : (0 : ℝ) ≤ 1 / ((t.sup id : ℕ) : ℝ) := by positivity
          linarith

/-- **Summability of `t^(-3)`**, uniformly in the number of periods: for every finite set of distinct periods
(pairs `(b,n)` with `b ∈ {2,3}`, `n ≥ 1`), `∑ (sqrt (lp b n))^(-3) ≤ 2 ((sqrt log 2)^(-3) + (sqrt log 3)^(-3))`. -/
theorem sum_inv_cube_le (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, (p.1 = 2 ∨ p.1 = 3) ∧ 1 ≤ p.2) :
    ∑ p ∈ s, 1 / (Real.sqrt (lp p.1 p.2)) ^ 3 ≤
      2 * (1 / (Real.sqrt (Real.log 2)) ^ 3 + 1 / (Real.sqrt (Real.log 3)) ^ 3) := by
  classical
  have hterm : ∀ p ∈ s, 1 / (Real.sqrt (lp p.1 p.2)) ^ 3 =
      1 / (Real.sqrt (Real.log p.1)) ^ 3 * (1 / (p.2 : ℝ) ^ 3) := by
    intro p hp
    rw [sqrt_lp]
    have hn : (0 : ℝ) < p.2 := by exact_mod_cast (hs p hp).2
    have hb : (0 : ℝ) < Real.sqrt (Real.log p.1) := by
      apply Real.sqrt_pos.mpr
      have : (1 / 4 : ℝ) ≤ Real.log p.1 := log_ge_quarter (by rcases (hs p hp).1 with h | h <;> omega)
      linarith
    field_simp
  -- split by base
  have hsplit : ∑ p ∈ s, 1 / (Real.sqrt (lp p.1 p.2)) ^ 3 =
      ∑ p ∈ s.filter (fun p => p.1 = 2), 1 / (Real.sqrt (lp p.1 p.2)) ^ 3 +
      ∑ p ∈ s.filter (fun p => ¬ p.1 = 2), 1 / (Real.sqrt (lp p.1 p.2)) ^ 3 :=
    (Finset.sum_filter_add_sum_filter_not s _ _).symm
  have h2 : ∑ p ∈ s.filter (fun p => p.1 = 2), 1 / (Real.sqrt (lp p.1 p.2)) ^ 3 ≤
      2 * (1 / (Real.sqrt (Real.log 2)) ^ 3) := by
    have : ∑ p ∈ s.filter (fun p => p.1 = 2), 1 / (Real.sqrt (lp p.1 p.2)) ^ 3 =
        1 / (Real.sqrt (Real.log 2)) ^ 3 * ∑ p ∈ s.filter (fun p => p.1 = 2), 1 / (p.2 : ℝ) ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [hterm p hp.1, hp.2]
      norm_num
    rw [this]
    have hinj : Set.InjOn Prod.snd (s.filter (fun p => p.1 = 2) : Set (ℕ × ℕ)) := by
      intro p hp q hq h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      exact Prod.ext (by rw [hp.2, hq.2]) h
    rw [← Finset.sum_image (f := fun n : ℕ => 1 / (n : ℝ) ^ 3) hinj]
    have hb : (0 : ℝ) ≤ 1 / (Real.sqrt (Real.log 2)) ^ 3 := by positivity
    have := inv_cube_sum_set ((s.filter (fun p => p.1 = 2)).image Prod.snd) (by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨p, hp, rfl⟩ := hn
      exact (hs p (Finset.mem_filter.mp hp).1).2)
    nlinarith
  have h3 : ∑ p ∈ s.filter (fun p => ¬ p.1 = 2), 1 / (Real.sqrt (lp p.1 p.2)) ^ 3 ≤
      2 * (1 / (Real.sqrt (Real.log 3)) ^ 3) := by
    have : ∑ p ∈ s.filter (fun p => ¬ p.1 = 2), 1 / (Real.sqrt (lp p.1 p.2)) ^ 3 =
        1 / (Real.sqrt (Real.log 3)) ^ 3 * ∑ p ∈ s.filter (fun p => ¬ p.1 = 2), 1 / (p.2 : ℝ) ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mem_filter] at hp
      have h3' : p.1 = 3 := by rcases (hs p hp.1).1 with h | h; exact absurd h hp.2; exact h
      rw [hterm p hp.1, h3']
      norm_num
    rw [this]
    have hinj : Set.InjOn Prod.snd (s.filter (fun p => ¬ p.1 = 2) : Set (ℕ × ℕ)) := by
      intro p hp q hq h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      have hp3 : p.1 = 3 := by rcases (hs p hp.1).1 with h | h; exact absurd h hp.2; exact h
      have hq3 : q.1 = 3 := by rcases (hs q hq.1).1 with h | h; exact absurd h hq.2; exact h
      exact Prod.ext (by rw [hp3, hq3]) h
    rw [← Finset.sum_image (f := fun n : ℕ => 1 / (n : ℝ) ^ 3) hinj]
    have hb : (0 : ℝ) ≤ 1 / (Real.sqrt (Real.log 3)) ^ 3 := by positivity
    have := inv_cube_sum_set ((s.filter (fun p => ¬ p.1 = 2)).image Prod.snd) (by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨p, hp, rfl⟩ := hn
      exact (hs p (Finset.mem_filter.mp hp).1).2)
    nlinarith
  rw [hsplit]
  linarith

#print axioms same_chain_gap
#print axioms merged_gap3
#print axioms merged_gap_seq
#print axioms merged_gap_seq_odd
#print axioms merged_growth_exp
#print axioms window_card_le_two
#print axioms sum_inv_cube_le

end JAMerged
end LeanCheck
