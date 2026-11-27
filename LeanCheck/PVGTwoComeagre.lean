import Mathlib
import LeanCheck.PVGTwoAlmost

/-!
# PVGtwo, Remark 7.10: a comeagre set of added points (Lean check)

Notation of `PVGTwoAlmost`.

* `cover_of_patterns` : if for arbitrarily large `K` every pattern of level `K` occurs in the digits of the fractional part
  of `c`, then `c` has the covering property;
* `residual_patterns` : this happens for all `c` in a comeagre subset of the line;
* `comeagre_point` : hence for all `c` in a comeagre set, no non-precompact group topology below the usual one makes `aS`,
  `a ∈ A(δ)`, and `cS` totally bounded.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set

namespace PVG
namespace Two
open Q95 Lac

/-- Every pattern of level `K` occurs. -/
def AllPat (c : ℝ) (K : ℕ) : Prop := ∀ w : Places K → Fin 2, ∃ n ∈ Finset.Ico (Lv K) (2 * Lv K), Match c K n w

lemma cover_of_patterns (c : ℝ) (hpat : ∀ K0 : ℕ, ∃ K, K0 ≤ K ∧ AllPat (Int.fract c) K) (x : ℝ) :
    ∃ m : ℕ, ∀ k, dint ((x - c * sT m) / 2 ^ Lv k) ≤ ((2 : ℝ) ^ (k + 4))⁻¹ := by
  obtain ⟨K1, hK1⟩ : ∃ K : ℕ, max |x| |c| ≤ K := exists_nat_ge _
  obtain ⟨K, hKK, hall⟩ := hpat K1
  have hKx : |x| ≤ K := (le_max_left _ _).trans (hK1.trans (by exact_mod_cast hKK))
  have hKc : |c| ≤ K := (le_max_right _ _).trans (hK1.trans (by exact_mod_cast hKK))
  set f := Int.fract c with hf
  have hf01 : f ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  set e : ℕ → Fin 2 := Real.digits f 2 with he
  have hfe : Real.ofDigits e = f := Real.ofDigits_digits one_lt_two hf01
  set θ : ℕ → ℝ := fun k => Int.fract (x / 2 ^ Lv k) with hθ
  set w : Places K → Fin 2 := fun q => Real.digits (θ q.1.val) 2 q.2.val with hw
  obtain ⟨n, hn, hm⟩ := hall w
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.1 hn
  have hLK := Lv_big K
  have hsT : sT (n - 1) = (2 : ℝ) ^ (n ^ 2) := by
    show (2 : ℝ) ^ ((n - 1 + 1) ^ 2) = _
    congr 2; omega
  have hnn : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero _
  refine ⟨n - 1, fun k => ?_⟩
  rw [hsT]
  have hpos : (0 : ℝ) < 2 ^ Lv k := by positivity
  rcases le_or_gt k K with hk | hk
  · have hLk : Lv k ≤ Lv K := Lv_mono hk
    set M := n ^ 2 - Lv k with hM
    have hMn : (2 : ℝ) ^ (n ^ 2) = 2 ^ M * 2 ^ Lv k := by rw [← pow_add]; congr 1; omega
    obtain ⟨z, hz⟩ := shift_digits e M
    have hθ01 : θ k ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have hθd : Real.ofDigits (Real.digits (θ k) 2) = θ k := Real.ofDigits_digits one_lt_two hθ01
    have hagree : ∀ i < k + 5, (fun i => e (i + M)) i = Real.digits (θ k) 2 i := by
      intro i hi
      have h := hm ⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨i, hi⟩⟩
      have e1 : pos K n ⟨⟨k, Nat.lt_succ_of_le hk⟩, ⟨i, hi⟩⟩ = i + M := by
        show n ^ 2 - Lv k + i = i + M
        omega
      rw [e1] at h
      exact h
    have hclose : |θ k - Real.ofDigits (fun i => e (i + M))| ≤ ((2 : ℝ) ^ (k + 5))⁻¹ := by
      have h1 := Real.abs_ofDigits_sub_ofDigits_le (b := 2) (x := Real.digits (θ k) 2)
        (y := fun i => e (i + M)) (n := k + 5) (fun i hi => (hagree i hi).symm)
      rw [hθd] at h1
      exact_mod_cast h1
    have e1 : (x - c * 2 ^ (n ^ 2)) / 2 ^ Lv k =
        (θ k - Real.ofDigits (fun i => e (i + M))) - ((z + 2 ^ M * ⌊c⌋ - ⌊x / 2 ^ Lv k⌋ : ℤ) : ℝ) := by
      have h1 : (x - c * 2 ^ (n ^ 2)) / 2 ^ Lv k = x / 2 ^ Lv k - 2 ^ M * c := by
        rw [hMn]; field_simp
      have h2 : x / 2 ^ Lv k = ⌊x / 2 ^ Lv k⌋ + θ k := (Int.floor_add_fract _).symm
      have h3 : (2 : ℝ) ^ M * c = 2 ^ M * ⌊c⌋ + (z + Real.ofDigits (fun i => e (i + M))) := by
        rw [← hz, hfe, ← mul_add]
        congr 1
        exact (Int.floor_add_fract c).symm
      rw [h1, h3]
      conv_lhs => rw [h2]
      push_cast
      ring
    rw [e1, dint_sub_int]
    refine (dint_le_abs _).trans (hclose.trans ?_)
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (by omega))
  · have hLk := Lv_big k
    have h4 : Lv K ^ 4 ≤ Lv k := (Lv_pow4 K).trans (Lv_mono (Nat.succ_le_of_lt hk))
    have hL72 := Lv_ge K
    have hn4 : n ^ 2 ≤ 4 * Lv K ^ 2 := by
      have : n ≤ 2 * Lv K := by omega
      have := Nat.pow_le_pow_left this 2
      rw [mul_pow] at this
      simpa using this
    have h8 : 16 * Lv K ^ 2 ≤ Lv K ^ 4 := by
      have e1 : Lv K ^ 4 = Lv K ^ 2 * Lv K ^ 2 := by ring
      have h6 : 72 * 72 ≤ Lv K ^ 2 := by rw [sq]; exact Nat.mul_le_mul hL72 hL72
      rw [e1]
      exact Nat.mul_le_mul_right _ (le_trans (by omega) h6)
    have hKsq : K ≤ Lv K ^ 2 := (show K ≤ Lv K by omega).trans (Nat.le_self_pow two_ne_zero _)
    have hbig : K + n ^ 2 + (k + 5) ≤ Lv k := by omega
    have hxk : K + (k + 5) ≤ Lv k := by omega
    refine (dint_le_abs _).trans ?_
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hK2 : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast (Nat.lt_two_pow_self).le
    have h1 : |x - c * 2 ^ (n ^ 2)| ≤ |x| + 2 ^ (K + n ^ 2) := by
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (n ^ 2)), pow_add]
      exact mul_le_mul_of_nonneg_right (hKc.trans hK2) (by positivity)
    have h2 : |x| ≤ 2 ^ K := hKx.trans hK2
    have h5 : ∀ a : ℕ, a + (k + 5) ≤ Lv k → (2 : ℝ) ^ a ≤ ((2 : ℝ) ^ (k + 4))⁻¹ * 2 ^ Lv k / 2 := by
      intro a ha
      have e1 : (2 : ℝ) ^ (a + (k + 5)) ≤ 2 ^ Lv k := pow_le_pow_right₀ one_le_two ha
      have e2 : (2 : ℝ) ^ (a + (k + 5)) = 2 ^ a * (2 ^ (k + 4) * 2) := by
        rw [← pow_succ, ← pow_add]
      rw [e2] at e1
      rw [le_div_iff₀ two_pos, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      nlinarith
    have h6 := h5 K hxk
    have h7 := h5 (K + n ^ 2) hbig
    linarith

/-! ## Digits on short intervals -/

/-- The first `k` digits of `d` read as a natural number. -/
def pref (d : ℕ → Fin 2) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 * pref d k + (d k).val

noncomputable def psum (d : ℕ → Fin 2) (M : ℕ) : ℝ := ∑ i ∈ Finset.range M, ((d i).val : ℝ) / 2 ^ (i + 1)

lemma psum_eq (d : ℕ → Fin 2) (k : ℕ) : psum d k = (pref d k : ℝ) / 2 ^ k := by
  induction k with
  | zero => simp [psum, pref]
  | succ k ih =>
    unfold psum at ih ⊢
    rw [Finset.sum_range_succ, ih]
    simp only [pref]
    push_cast
    rw [pow_succ]
    field_simp

lemma psum_gap (d : ℕ → Fin 2) (k M : ℕ) (h : k ≤ M) :
    psum d k ≤ psum d M ∧ psum d M + ((2 : ℝ) ^ M)⁻¹ ≤ psum d k + ((2 : ℝ) ^ k)⁻¹ := by
  induction M, h using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl⟩
  | succ M _ ih =>
    have e1 : psum d (M + 1) = psum d M + ((d M).val : ℝ) / 2 ^ (M + 1) := by
      unfold psum; rw [Finset.sum_range_succ]
    have h0 : (0 : ℝ) ≤ ((d M).val : ℝ) / 2 ^ (M + 1) := by positivity
    have h1 : ((d M).val : ℝ) ≤ 1 := by
      have := (d M).isLt
      have : (d M).val ≤ 1 := by omega
      exact_mod_cast this
    have h2 : ((d M).val : ℝ) / 2 ^ (M + 1) + ((2 : ℝ) ^ (M + 1))⁻¹ ≤ ((2 : ℝ) ^ M)⁻¹ := by
      have e2 : ((2 : ℝ) ^ M)⁻¹ = 1 / 2 ^ (M + 1) + ((2 : ℝ) ^ (M + 1))⁻¹ := by
        rw [pow_succ]; field_simp; norm_num
      rw [e2]
      exact add_le_add (div_le_div_of_nonneg_right h1 (by positivity)) le_rfl
    rw [e1]
    exact ⟨ih.1.trans (le_add_of_nonneg_right h0), by linarith [ih.2]⟩

lemma digits_on (d : ℕ → Fin 2) (M : ℕ) (y : ℝ) (hy : y ∈ Ico (psum d M) (psum d M + ((2 : ℝ) ^ M)⁻¹)) :
    ∀ j < M, Real.digits y 2 j = d j := by
  intro j hj
  obtain ⟨g1, g2⟩ := psum_gap d (j + 1) M hj
  have h1 : psum d (j + 1) ≤ y := g1.trans hy.1
  have h2 : y < psum d (j + 1) + ((2 : ℝ) ^ (j + 1))⁻¹ := lt_of_lt_of_le hy.2 g2
  rw [psum_eq] at h1 h2
  have hp : (0 : ℝ) < 2 ^ (j + 1) := by positivity
  have hfl : ⌊y * ((2 : ℕ) : ℝ) ^ (j + 1)⌋₊ = pref d (j + 1) := by
    have h3 : (pref d (j + 1) : ℝ) ≤ y * 2 ^ (j + 1) := by
      rwa [div_le_iff₀ hp] at h1
    have h4 : y * 2 ^ (j + 1) < (pref d (j + 1) : ℝ) + 1 := by
      have := mul_lt_mul_of_pos_right h2 hp
      rwa [add_mul, div_mul_cancel₀ _ hp.ne', inv_mul_cancel₀ hp.ne'] at this
    have h5 : (0 : ℝ) ≤ y * 2 ^ (j + 1) := le_trans (Nat.cast_nonneg _) h3
    rw [Nat.cast_ofNat, Nat.floor_eq_iff h5]
    exact ⟨h3, h4⟩
  unfold Real.digits
  rw [hfl]
  refine Fin.ext ?_
  rw [Fin.val_ofNat]
  have := (d j).isLt
  simp only [pref]
  omega

/-- For all `K0`, the numbers with all patterns at some level `K ≥ K0` contain a dense open set. -/
lemma dense_patterns (K0 : ℕ) : Dense (⋃ K, ⋃ _ : K0 ≤ K, interior {c : ℝ | AllPat (Int.fract c) K}) := by
  classical
  rw [dense_iff_inter_open]
  rintro U hU ⟨y0, hy0⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y0 hy0
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  rw [one_div, inv_pow] at hm
  set f0 := Int.fract y0 with hf0
  have hf01 : f0 ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  set g := Real.digits f0 2 with hg
  set K := max K0 m with hK
  have hmK : m ≤ K := le_max_right _ _
  have hLK := Lv_big K
  have hcard : Fintype.card (Places K → Fin 2) = 2 ^ off (K + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, card_places]
  set idx := Fintype.equivFinOfCardEq hcard with hidx
  set nn : (Places K → Fin 2) → ℕ := fun w => Lv K + (idx w).val with hnn
  have hnnI : ∀ w, nn w ∈ Finset.Ico (Lv K) (2 * Lv K) := by
    intro w
    have h1 := (idx w).isLt
    have h2 := few K
    exact Finset.mem_Ico.2 ⟨Nat.le_add_right _ _, by simp only [hnn]; omega⟩
  set M := (2 * Lv K) ^ 2 + (K + 5) + m with hM
  have hpos_lt : ∀ w q, pos K (nn w) q < M := by
    intro w q
    have h1 := (Finset.mem_Ico.1 (hnnI w)).2
    have h2 : nn w ^ 2 ≤ (2 * Lv K) ^ 2 := Nat.pow_le_pow_left h1.le 2
    have h3 := q.2.isLt
    have h4 := q.1.isLt
    unfold pos; omega
  have hpos_ge : ∀ w q, m ≤ pos K (nn w) q := by
    intro w q
    have h1 := (Finset.mem_Ico.1 (hnnI w)).1
    have h2 : Lv q.1.val ≤ Lv K := Lv_mono (Nat.lt_succ_iff.1 q.1.isLt)
    have h3 : 2 * nn w ≤ nn w ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul_right _ (by omega)
    unfold pos; omega
  set d : ℕ → Fin 2 := fun j =>
    if j < m then g j
    else if h : ∃ p : (Places K → Fin 2) × Places K, pos K (nn p.1) p.2 = j then h.choose.1 h.choose.2 else 0 with hd
  have hdg : ∀ j < m, d j = g j := fun j hj => by simp only [hd, if_pos hj]
  have hdw : ∀ w q, d (pos K (nn w) q) = w q := by
    intro w q
    have h1 : ¬ pos K (nn w) q < m := not_lt.2 (hpos_ge w q)
    have h2 : ∃ p : (Places K → Fin 2) × Places K, pos K (nn p.1) p.2 = pos K (nn w) q := ⟨(w, q), rfl⟩
    simp only [hd, if_neg h1, dif_pos h2]
    have h3 := h2.choose_spec
    obtain ⟨h4, h5⟩ := pos_inj (Finset.mem_Ico.1 (hnnI _)).1 (Finset.mem_Ico.1 (hnnI w)).1 h3
    have h6 : h2.choose.1 = w := by
      have : idx h2.choose.1 = idx w := Fin.ext (by simp only [hnn] at h4; omega)
      exact idx.injective this
    rw [h6, h5]
  set a := (⌊y0⌋ : ℝ) + psum d M with ha
  set V := Ioo a (a + ((2 : ℝ) ^ M)⁻¹) with hV
  have hVne : V.Nonempty := nonempty_Ioo.2 (lt_add_of_pos_right _ (by positivity))
  have hsame : psum d m = psum g m := by
    unfold psum
    exact Finset.sum_congr rfl fun i hi => by rw [hdg i (Finset.mem_range.1 hi)]
  have hgm : psum g m ≤ f0 ∧ f0 ≤ psum g m + ((2 : ℝ) ^ m)⁻¹ := by
    have h1 := Real.sum_ofDigitsTerm_digits_le (b := 2) (x := f0) hf01 m
    have h2 := Real.le_sum_ofDigitsTerm_digits (b := 2) (x := f0) hf01 m
    have e1 : ∑ i ∈ Finset.range m, Real.ofDigitsTerm (Real.digits f0 2) i = psum g m := by
      unfold psum
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold Real.ofDigitsTerm
      rw [← hg, div_eq_mul_inv]
      push_cast
      rfl
    rw [e1] at h1 h2
    have e2 : ((((2 : ℕ) : ℝ))⁻¹) ^ m = ((2 : ℝ) ^ m)⁻¹ := by
      rw [inv_pow]; norm_num
    rw [e2] at h2
    exact ⟨h1, by linarith⟩
  have hVU : V ⊆ U := by
    intro y hy
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    obtain ⟨g1, g2⟩ := psum_gap d m M (by omega)
    rw [hsame] at g1 g2
    have e0 : y0 = ⌊y0⌋ + f0 := (Int.floor_add_fract y0).symm
    have hy1 := hy.1
    have hy2 := hy.2
    rw [ha] at hy1 hy2
    refine lt_of_le_of_lt ?_ hm
    rw [abs_le]
    constructor <;> linarith [hgm.1, hgm.2]
  have hVA : V ⊆ {c : ℝ | AllPat (Int.fract c) K} := by
    intro y hy w
    have h1 : y - (⌊y0⌋ : ℝ) ∈ Ico (psum d M) (psum d M + ((2 : ℝ) ^ M)⁻¹) := by
      have y1 := hy.1
      have y2 := hy.2
      rw [ha] at y1 y2
      exact ⟨by linarith, by linarith⟩
    have h0 : (0 : ℝ) ≤ psum d M := by
      unfold psum; exact Finset.sum_nonneg fun i _ => by positivity
    have h2 : psum d M + ((2 : ℝ) ^ M)⁻¹ ≤ 1 := by
      have := (psum_gap d 0 M (Nat.zero_le _)).2
      simpa [psum] using this
    have hfr : Int.fract y = y - ⌊y0⌋ := by
      rw [← Int.fract_sub_intCast y ⌊y0⌋]
      exact Int.fract_eq_self.2 ⟨h0.trans h1.1, lt_of_lt_of_le h1.2 h2⟩
    refine ⟨nn w, hnnI w, fun q => ?_⟩
    rw [hfr, digits_on d M _ h1 _ (hpos_lt w q), hdw]
  obtain ⟨y, hy⟩ := hVne
  refine ⟨y, hVU hy, mem_iUnion₂.2 ⟨K, le_max_left _ _, ?_⟩⟩
  exact interior_maximal hVA isOpen_Ioo hy

theorem residual_patterns : ∀ᶠ c in residual ℝ, ∀ K0 : ℕ, ∃ K, K0 ≤ K ∧ AllPat (Int.fract c) K := by
  have h : ∀ K0 : ℕ, ∀ᶠ c in residual ℝ, c ∈ ⋃ K, ⋃ _ : K0 ≤ K, interior {c : ℝ | AllPat (Int.fract c) K} :=
    fun K0 => residual_of_dense_open (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_interior)
      (dense_patterns K0)
  refine (eventually_countable_forall.2 h).mono fun c hc K0 => ?_
  obtain ⟨K, hK, hm⟩ := mem_iUnion₂.1 (hc K0)
  exact ⟨K, hK, interior_subset (s := {c : ℝ | AllPat (Int.fract c) K}) hm⟩

/-- **Remark 7.10, comeagre part.** -/
theorem comeagre_point : ∀ᶠ c in residual ℝ,
    ∀ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ → euclidNhds 0 ≤ @nhds ℝ γ 0 →
      (∀ a : ℝ, InA dlt2 sT a → Tb (@nhds ℝ γ 0) (dil a Sset)) → Tb (@nhds ℝ γ 0) (dil c Sset) →
      ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W := by
  refine residual_patterns.mono fun c hc γ hg heu hA hcS => ?_
  exact point_core c (cover_of_patterns c hc) _ (group_half γ hg) heu (fun d hd => hA _ (inA_of_Cdig d hd)) hcS

end Two
end PVG
