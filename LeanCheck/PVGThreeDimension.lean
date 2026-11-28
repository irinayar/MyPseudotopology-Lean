import LeanCheck.PVGTwoDimension

/-!
# Dimension one for sparse forced digits

The argument of `PVGTwoDimension` for an arbitrary set `Z` of forced zero digits that has density zero and
meets every interval `(j, j + 2 sqrt (j+5) + 1]`: the numbers with these digits zero have Hausdorff dimension `1`.
-/

open Filter Topology Set Real
open scoped Pointwise NNReal ENNReal

namespace PVG
namespace Three
namespace Dim

open Classical in
/-- A sparse set of forced positions that is met by every short interval. -/
class ZD where
  Z : Set ℕ
  small : ∀ c : ℝ, 0 < c → ∀ᶠ M : ℕ in atTop, (Nat.count (fun j => j ∈ Z) M : ℝ) ≤ c * M
  after : ∀ j0 : ℕ, ∃ j1 ∈ Z, j0 < j1 ∧ j1 ≤ j0 + 2 * Nat.sqrt (j0 + 5) + 1

variable [S : ZD]

def Allowed (d : ℕ → Fin 2) : Prop := ∀ j ∈ ZD.Z, d j = 0

open Classical in
noncomputable def Zcount (M : ℕ) : ℕ := Nat.count (fun j => j ∈ ZD.Z) M

open Classical in
lemma small' {c : ℝ} (hc : 0 < c) : ∀ᶠ M : ℕ in atTop, (Zcount M : ℝ) ≤ c * M := ZD.small c hc

/-- Two allowed expansions that first differ at `j0` give numbers at distance at least `2^{-(j1+1)}`. -/
lemma separation (d d' : ℕ → Fin 2) (hd : Allowed d) (hd' : Allowed d') (j0 j1 : ℕ)
    (hagree : ∀ i < j0, d i = d' i) (h1 : d j0 = 1) (h0 : d' j0 = 0) (hj1 : j1 ∈ ZD.Z) (hlt : j0 < j1) :
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

lemma free_infinite : {j : ℕ | j ∉ ZD.Z}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  obtain ⟨M, hM⟩ := eventually_atTop.1 (small' (show (0 : ℝ) < 1 / 2 by norm_num))
  classical
  set P := max M (2 * (N + 1) + 1) with hP
  have h1 := hM P (le_max_left _ _)
  have h2 : P - (N + 1) ≤ Zcount P := by
    unfold Zcount
    rw [Nat.count_eq_card_filter_range]
    have hsub : Finset.Ico (N + 1) P ⊆ (Finset.range P).filter (fun j => j ∈ ZD.Z) := by
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
noncomputable def freePos (i : ℕ) : ℕ := Nat.nth (fun j => j ∉ ZD.Z) i

lemma freePos_mem (i : ℕ) : freePos i ∉ ZD.Z := Nat.nth_mem_of_infinite free_infinite i

open Classical in
noncomputable def freeCount (j : ℕ) : ℕ := Nat.count (fun j => j ∉ ZD.Z) j

lemma freePos_lt {i j : ℕ} (h : i < freeCount j) : freePos i < j := by
  classical
  exact Nat.nth_lt_of_lt_count h

lemma freeCount_add (M : ℕ) : freeCount M + Zcount M = M := by
  classical
  unfold freeCount Zcount
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range, add_comm]
  have := Finset.card_filter_add_card_filter_not (s := Finset.range M) (fun j => j ∈ ZD.Z)
  simpa using this

lemma exponent_bound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ c : ℝ, ∀ j0 : ℕ, s * ((j0 : ℝ) + 2 * (Nat.sqrt (j0 + 5) : ℝ) + 2) - c ≤ freeCount j0 := by
  have hgap : 0 < (1 - s) / 2 := by linarith
  have hev : ∀ᶠ j0 : ℕ in atTop, s * ((j0 : ℝ) + 2 * (Nat.sqrt (j0 + 5) : ℝ) + 2) ≤ freeCount j0 := by
    have h1 := small' hgap
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
  obtain ⟨j1, hj1, hlt, hle⟩ := ZD.after j0
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
  set d : ℕ → Fin 2 := fun j => if j ∈ ZD.Z then 0 else g (freeCount j) with hd
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
    obtain ⟨j1, hj1, hlt, _⟩ := ZD.after j0
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
    have h1 : freePos i ∉ ZD.Z := freePos_mem i
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

omit S

open Classical in
/-- The numbers whose digits vanish on a sparse set have Hausdorff dimension `1`. -/
theorem dimH_one (Z : Set ℕ)
    (small : ∀ c : ℝ, 0 < c → ∀ᶠ M : ℕ in atTop, (Nat.count (fun j => j ∈ Z) M : ℝ) ≤ c * M)
    (after : ∀ j0 : ℕ, ∃ j1 ∈ Z, j0 < j1 ∧ j1 ≤ j0 + 2 * Nat.sqrt (j0 + 5) + 1)
    (A : Set ℝ) (hA : ∀ d : ℕ → Fin 2, (∀ j ∈ Z, d j = 0) → Real.ofDigits d ∈ A) : dimH A = 1 := by
  letI : ZD := ⟨Z, small, after⟩
  refine le_antisymm ?_ ?_
  · rw [← Real.dimH_univ]
    exact dimH_mono (subset_univ _)
  · refine one_le_dimH_Cset.trans (dimH_mono ?_)
    rintro a ⟨d, hd, rfl⟩
    exact hA d hd

end Dim
end Three
end PVG
