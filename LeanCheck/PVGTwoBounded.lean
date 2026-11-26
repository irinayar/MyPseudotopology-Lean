import Mathlib

/-!
# PVGtwo, Section 8: bounded signed sums of a rapidly increasing sequence (Lean check)

`bounded_sum`: let `s` be a positive sequence with `s (n+1) / s n → ∞`, and `c` finitely many real coefficients.
For every `R` there is `J` such that, whenever `∑ c_i ε_i s_{m_i}` with `ε_i ∈ {-1,0,1}` has absolute value at most `R`,
the signed coefficients belonging to each index `n > J` add up to `0`.

The argument is the one suggested in ChatGPT's audit of Section 8; it replaces the use of the independence theorem there.
A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Two

lemma eventually_gap (s : ℕ → ℝ) (hpos : ∀ n, 0 < s n) (hr : Tendsto (fun n => s (n + 1) / s n) atTop atTop)
    (δ C R : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) :
    ∃ J : ℕ, ∀ L, J < L → (∀ m < L, s m ≤ s (L - 1)) ∧ R < δ * s L - C * s (L - 1) := by
  set ρ : ℝ := max 2 ((C + 1) / δ) with hρ
  have hρ2 : 2 ≤ ρ := le_max_left _ _
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 (hr.eventually_ge_atTop ρ)
  have hstep : ∀ n, n0 ≤ n → ρ * s n ≤ s (n + 1) := fun n hn => by
    have := hn0 n hn
    rwa [le_div_iff₀ (hpos n)] at this
  have hdouble : ∀ n, n0 ≤ n → 2 * s n ≤ s (n + 1) := fun n hn =>
    (mul_le_mul_of_nonneg_right hρ2 (hpos n).le).trans (hstep n hn)
  have hmono : ∀ a b, n0 ≤ a → a ≤ b → s a ≤ s b := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih =>
      have := hdouble b (ha.trans hab)
      have := hpos b
      linarith
  have hgrow : ∀ k, (2 : ℝ) ^ k * s n0 ≤ s (n0 + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := hdouble (n0 + k) (Nat.le_add_right _ _)
      rw [pow_succ, ← add_assoc]
      linarith
  have htop : Tendsto s atTop atTop := by
    have h1 : Tendsto (fun k => s (n0 + k)) atTop atTop :=
      tendsto_atTop_mono hgrow
        ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const (hpos n0))
    have h2 : Tendsto (fun k => s (k + n0)) atTop atTop := by simpa [add_comm] using h1
    exact (tendsto_add_atTop_iff_nat n0).1 h2
  set M : ℝ := ∑ m ∈ Finset.range n0, s m with hM
  obtain ⟨J, hJ⟩ := eventually_atTop.1 ((htop.eventually_ge_atTop M).and (htop.eventually_gt_atTop R))
  refine ⟨max J n0 + 1, fun L hL => ?_⟩
  have hL1 : n0 ≤ L - 1 := by omega
  have hLJ : J ≤ L - 1 := by omega
  obtain ⟨hM1, hR1⟩ := hJ (L - 1) hLJ
  refine ⟨fun m hm => ?_, ?_⟩
  · by_cases h : n0 ≤ m
    · exact hmono m (L - 1) h (by omega)
    · have h1 : s m ≤ M :=
        Finset.single_le_sum (fun i _ => (hpos i).le) (Finset.mem_range.2 (not_le.1 h))
      exact h1.trans hM1
  · have h1 := hstep (L - 1) hL1
    have e1 : L - 1 + 1 = L := by omega
    rw [e1] at h1
    have h2 : C + 1 ≤ δ * ρ := by
      have := le_max_right 2 ((C + 1) / δ)
      rw [← hρ, div_le_iff₀ hδ] at this
      linarith
    have h3 : (C + 1) * s (L - 1) ≤ δ * ρ * s (L - 1) := mul_le_mul_of_nonneg_right h2 (hpos _).le
    have h4 : δ * (ρ * s (L - 1)) ≤ δ * s L := mul_le_mul_of_nonneg_left h1 hδ.le
    nlinarith

theorem bounded_sum (s : ℕ → ℝ) (hpos : ∀ n, 0 < s n) (hr : Tendsto (fun n => s (n + 1) / s n) atTop atTop)
    {r : ℕ} (c : Fin r → ℝ) (R : ℝ) :
    ∃ J : ℕ, ∀ (m : Fin r → ℕ) (ε : Fin r → ℝ), (∀ i, ε i ∈ ({-1, 0, 1} : Finset ℝ)) →
      |∑ i, c i * ε i * s (m i)| ≤ R → ∀ n, J < n → ∑ i ∈ Finset.univ.filter (fun i => m i = n), c i * ε i = 0 := by
  classical
  set D : Finset ℝ := (Fintype.piFinset fun _ : Fin r => ({-1, 0, 1} : Finset ℝ)).biUnion
    (fun ε => Finset.univ.powerset.image fun I : Finset (Fin r) => ∑ i ∈ I, c i * ε i) with hD
  -- a positive lower bound for the nonzero signed sums
  obtain ⟨δ, hδ, hmin⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ D, d ≠ 0 → δ ≤ |d| := by
    set E := (D.filter (· ≠ 0)).image (fun d => |d|) with hE
    by_cases h : E.Nonempty
    · refine ⟨E.min' h, ?_, fun d hd hd0 => Finset.min'_le _ _ ?_⟩
      · obtain ⟨d, hd, e⟩ := Finset.mem_image.1 (E.min'_mem h)
        rw [← e]
        exact abs_pos.2 (Finset.mem_filter.1 hd).2
      · exact Finset.mem_image.2 ⟨d, Finset.mem_filter.2 ⟨hd, hd0⟩, rfl⟩
    · refine ⟨1, one_pos, fun d hd hd0 => absurd ?_ h⟩
      exact ⟨|d|, Finset.mem_image.2 ⟨d, Finset.mem_filter.2 ⟨hd, hd0⟩, rfl⟩⟩
  set C : ℝ := ∑ i, |c i| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => abs_nonneg _
  obtain ⟨J, hJ⟩ := eventually_gap s hpos hr δ C R hδ hC0
  refine ⟨J, fun m ε hε hsum n hn => ?_⟩
  set d : ℕ → ℝ := fun n => ∑ i ∈ Finset.univ.filter (fun i => m i = n), c i * ε i with hd
  by_contra hne
  set T := (Finset.univ.image m).filter (fun n => d n ≠ 0) with hT
  have hmemT : n ∈ T := by
    refine Finset.mem_filter.2 ⟨?_, hne⟩
    obtain ⟨i, hi, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, (Finset.mem_filter.1 hi).2⟩
  have hTne : T.Nonempty := ⟨n, hmemT⟩
  set L := T.max' hTne with hL
  have hLJ : J < L := lt_of_lt_of_le hn (T.le_max' n hmemT)
  have hLT : L ∈ T := T.max'_mem hTne
  obtain ⟨hmax, hgap⟩ := hJ L hLJ
  have hsplit : ∑ i, c i * ε i * s (m i) = ∑ k ∈ T, d k * s k := by
    have h1 : ∑ i, c i * ε i * s (m i) = ∑ k ∈ Finset.univ.image m, d k * s k := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := m) (t := Finset.univ.image m)
        (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hd]
      simp only []
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
    rw [h1, hT, Finset.sum_filter_of_ne]
    intro k _ hk h0
    exact hk (by rw [h0, zero_mul])
  have hdL : δ ≤ |d L| := by
    refine hmin _ ?_ (Finset.mem_filter.1 hLT).2
    rw [hD]
    refine Finset.mem_biUnion.2 ⟨ε, Fintype.mem_piFinset.2 hε,
      Finset.mem_image.2 ⟨Finset.univ.filter (fun i => m i = L), Finset.mem_powerset.2 (Finset.subset_univ _), rfl⟩⟩
  have hrest : |∑ k ∈ T.erase L, d k * s k| ≤ C * s (L - 1) := by
    have h1 : ∀ k ∈ T.erase L, |d k * s k| ≤ |d k| * s (L - 1) := by
      intro k hk
      obtain ⟨hkL, hkT⟩ := Finset.mem_erase.1 hk
      have hlt : k < L := lt_of_le_of_ne (T.le_max' k hkT) hkL
      rw [abs_mul, abs_of_pos (hpos k)]
      exact mul_le_mul_of_nonneg_left (hmax k hlt) (abs_nonneg _)
    have h2 : ∑ k ∈ T.erase L, |d k| ≤ C := by
      have h3 : ∑ k ∈ T.erase L, |d k| ≤ ∑ k ∈ Finset.univ.image m, ∑ i ∈ Finset.univ.filter (fun i => m i = k), |c i| := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
          ((Finset.erase_subset _ _).trans (Finset.filter_subset _ _)) (fun k _ _ => abs_nonneg _))
          (Finset.sum_le_sum fun k _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]
        refine mul_le_of_le_one_right (abs_nonneg _) ?_
        have := hε i
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h | h <;> rw [h] <;> norm_num
      rwa [Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))] at h3
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum h1).trans ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right h2 (hpos _).le
  have htotal : δ * s L - C * s (L - 1) ≤ |∑ i, c i * ε i * s (m i)| := by
    rw [hsplit, ← Finset.add_sum_erase T (fun k => d k * s k) hLT]
    have h1 : δ * s L ≤ |d L * s L| := by
      rw [abs_mul, abs_of_pos (hpos L)]
      exact mul_le_mul_of_nonneg_right hdL (hpos L).le
    have h2 := abs_sub_abs_le_abs_add (d L * s L) (∑ k ∈ T.erase L, d k * s k)
    linarith
  linarith

end Two
end PVG
