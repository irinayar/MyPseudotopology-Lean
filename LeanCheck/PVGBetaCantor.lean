import Mathlib
import LeanCheck.PVGBetaMain

/-!
# PVG: the measure of a stage system (Lean check)

Scope. The measure of the proof of Theorem `thm:betaexists` of PVG_v22. A *stage system* is a family of centers `x n a` (`a < 2^n`) and radii `r n`
such that the closed intervals `I(n,a) = [x n a - r n, x n a + r n]` are nested (the children of `(n,a)` are `(n+1, 2a)` and `(n+1, 2a+1)`),
pairwise disjoint at each level, inside `[1,2]` at level `0`, and have the witness property `P`. From such a system the Cantor-type measure is
the image of the Lebesgue measure on `[0,1)` under the map that sends the dyadic digits of `u` to the nested intervals.

* `Stages`: the axioms;
* `exists_measure_of_stages`: a stage system gives a probability measure `μ` without atoms, carried by `[1,2]`, with `StageProperty μ`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open MeasureTheory Filter Topology Set

namespace PVG
namespace Beta

/-- The distance to the nearest integer is at most the absolute value. -/
lemma norm_coe_le_abs (θ : ℝ) : ‖(θ : AddCircle (1 : ℝ))‖ ≤ |θ| := by
  have := AddCircle.norm_eq (p := (1 : ℝ)) (x := θ)
  rw [this]
  simpa using round_le θ 0

structure Stages (x : ℕ → ℕ → ℝ) (r : ℕ → ℝ) : Prop where
  r_pos : ∀ n, 0 < r n
  r_le : ∀ n, r n ≤ (1 / 2 : ℝ) ^ n
  root : x 0 0 = 3 / 2 ∧ r 0 = 1 / 2
  nest : ∀ n a, a < 2 ^ (n + 1) → |x (n + 1) a - x n (a / 2)| + r (n + 1) < r n
  sib : ∀ n c, c < 2 ^ n → 2 * r (n + 1) < |x (n + 1) (2 * c) - x (n + 1) (2 * c + 1)|
  P : ∀ n, 1 ≤ n → ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ n) →
    ∃ (k : ℤ) (E : Finset ℕ), E.card ≤ n ∧ ∀ a, a < 2 ^ n → a ∉ E →
      ∀ l ∈ Icc (x n a - r n) (x n a + r n), ∀ i : Fin n,
        ‖((c i * ((k : ℝ) + 1 / 2) * l : ℝ) : AddCircle (1 : ℝ))‖ < 1 / n

variable {x : ℕ → ℕ → ℝ} {r : ℕ → ℝ}

/-- Distinct intervals of the same level are disjoint (the centers are more than `2 r n` apart). -/
lemma Stages.sep (h : Stages x r) : ∀ n a a', a < 2 ^ n → a' < 2 ^ n → a ≠ a' →
    2 * r n < |x n a - x n a'| := by
  intro n
  induction n with
  | zero => intro a a' ha ha' hne; simp at ha ha'; omega
  | succ n ih =>
    intro a a' ha ha' hne
    by_cases hp : a / 2 = a' / 2
    · -- siblings
      obtain ⟨c, rfl | rfl⟩ : ∃ c, a = 2 * c ∨ a = 2 * c + 1 := ⟨a / 2, by omega⟩ <;>
      obtain ⟨c', rfl | rfl⟩ : ∃ c', a' = 2 * c' ∨ a' = 2 * c' + 1 := ⟨a' / 2, by omega⟩
      · exfalso; apply hne; have : c = c' := by omega
        rw [this]
      · have hcc : c = c' := by omega
        subst hcc
        exact h.sib n c (by omega)
      · have hcc : c = c' := by omega
        subst hcc
        rw [abs_sub_comm]; exact h.sib n c (by omega)
      · exfalso; apply hne; have : c = c' := by omega
        rw [this]
    · have h2 := ih (a / 2) (a' / 2) (by omega) (by omega) hp
      have h3 := h.nest n a ha
      have h4 := h.nest n a' ha'
      have h5 : |x n (a / 2) - x n (a' / 2)| ≤
          |x n (a / 2) - x (n + 1) a| + |x (n + 1) a - x (n + 1) a'| + |x (n + 1) a' - x n (a' / 2)| := by
        have := abs_sub_le (x n (a / 2)) (x (n + 1) a) (x n (a' / 2))
        have h6 := abs_sub_le (x (n + 1) a) (x (n + 1) a') (x n (a' / 2))
        have := abs_sub_le (x n (a / 2)) (x (n + 1) a') (x n (a' / 2))
        have h7 := abs_sub_le (x n (a / 2)) (x (n + 1) a) (x (n + 1) a')
        linarith [abs_sub_comm (x n (a / 2)) (x (n + 1) a'), abs_sub_comm (x (n + 1) a') (x n (a' / 2))]
      rw [abs_sub_comm (x n (a / 2)) (x (n + 1) a)] at h5
      linarith

/-- The closed interval of the node `(n,a)`. -/
def Iv (x : ℕ → ℕ → ℝ) (r : ℕ → ℝ) (n a : ℕ) : Set ℝ := Icc (x n a - r n) (x n a + r n)

lemma Stages.iv_child (h : Stages x r) (n a : ℕ) (ha : a < 2 ^ (n + 1)) :
    Iv x r (n + 1) a ⊆ Iv x r n (a / 2) := by
  intro l hl
  have h1 := h.nest n a ha
  have h2 := neg_abs_le (x (n + 1) a - x n (a / 2))
  have h3 := le_abs_self (x (n + 1) a - x n (a / 2))
  have h4 := h.r_pos (n + 1)
  simp only [Iv, mem_Icc] at hl ⊢
  constructor <;> linarith [hl.1, hl.2]

lemma Stages.mem_self (h : Stages x r) (n a : ℕ) : x n a ∈ Iv x r n a := by
  have := h.r_pos n
  simp only [Iv, mem_Icc]; constructor <;> linarith

/-- The dyadic index of `u` at level `n`. -/
noncomputable def dig (n : ℕ) (u : ℝ) : ℕ := ⌊(2 : ℝ) ^ n * u⌋₊

lemma dig_succ_div (n : ℕ) (u : ℝ) : dig (n + 1) u / 2 = dig n u := by
  unfold dig
  have : (2 : ℝ) ^ (n + 1) * u / ((2 : ℕ) : ℝ) = 2 ^ n * u := by push_cast; ring
  rw [← Nat.floor_div_natCast, this]

lemma dig_lt {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) (n : ℕ) : dig n u < 2 ^ n := by
  unfold dig
  rw [Nat.floor_lt (by have := hu.1; positivity)]
  have : (2 : ℝ) ^ n * u < 2 ^ n * 1 := mul_lt_mul_of_pos_left hu.2 (by positivity)
  simpa using this

lemma Stages.iv_mono (h : Stages x r) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) {n m : ℕ} (hnm : n ≤ m) :
    Iv x r m (dig m u) ⊆ Iv x r n (dig n u) := by
  induction m, hnm using Nat.le_induction with
  | base => exact subset_rfl
  | succ m hnm ih =>
    refine (h.iv_child m (dig (m + 1) u) (dig_lt hu _)).trans ?_
    rw [dig_succ_div]; exact ih

/-- The limit point of the digits of `u`. -/
noncomputable def psi (x : ℕ → ℕ → ℝ) (u : ℝ) : ℝ := limUnder atTop (fun n => x n (dig n u))

lemma Stages.seq_tendsto (h : Stages x r) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun n => x n (dig n u)) atTop (𝓝 (psi x u)) := by
  have hc : CauchySeq (fun n => x n (dig n u)) := by
    refine cauchySeq_of_le_geometric_two (C := 2) (fun n => ?_)
    have h1 := h.nest n (dig (n + 1) u) (dig_lt hu _)
    rw [dig_succ_div] at h1
    rw [Real.dist_eq]
    have h2 := h.r_le n
    have h3 := h.r_pos (n + 1)
    have h4 : (1 / 2 : ℝ) ^ n = 2 / 2 / 2 ^ n := by rw [one_div_pow]; ring
    rw [abs_sub_comm]
    linarith
  exact hc.tendsto_limUnder

lemma Stages.psi_mem (h : Stages x r) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) (n : ℕ) :
    psi x u ∈ Iv x r n (dig n u) := by
  refine isClosed_Icc.mem_of_tendsto (h.seq_tendsto hu) ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  exact h.iv_mono hu hm (h.mem_self m _)

lemma Stages.psi_aemeasurable (h : Stages x r) : AEMeasurable (psi x) (volume.restrict (Ico (0 : ℝ) 1)) := by
  refine aemeasurable_of_tendsto_metrizable_ae' (f := fun n u => x n (dig n u)) (fun n => ?_) ?_
  · exact (measurable_from_nat.comp (Nat.measurable_floor.comp
      (measurable_const.mul measurable_id))).aemeasurable
  · rw [ae_restrict_iff' measurableSet_Ico]
    exact Filter.Eventually.of_forall (fun u hu => h.seq_tendsto hu)

/-- The Cantor-type measure of a stage system. -/
noncomputable def cantorMeasure (x : ℕ → ℕ → ℝ) : Measure ℝ :=
  Measure.map (psi x) (volume.restrict (Ico (0 : ℝ) 1))

lemma Stages.isProb (h : Stages x r) : IsProbabilityMeasure (cantorMeasure x) := by
  haveI : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) := ⟨by simp⟩
  refine ⟨?_⟩
  unfold cantorMeasure
  rw [Measure.map_apply_of_aemeasurable h.psi_aemeasurable MeasurableSet.univ]
  simp

lemma Stages.disjoint (h : Stages x r) (n : ℕ) {a a' : ℕ} (ha : a < 2 ^ n) (ha' : a' < 2 ^ n) (hne : a ≠ a') :
    Disjoint (Iv x r n a) (Iv x r n a') := by
  rw [Set.disjoint_left]
  intro l hl hl'
  have h1 := h.sep n a a' ha ha' hne
  simp only [Iv, mem_Icc] at hl hl'
  have := abs_sub_le (x n a) l (x n a')
  have h2 : |x n a - l| ≤ r n := abs_le.2 ⟨by linarith [hl.2], by linarith [hl.1]⟩
  have h3 : |l - x n a'| ≤ r n := abs_le.2 ⟨by linarith [hl'.2], by linarith [hl'.1]⟩
  linarith

lemma dyadic_sub {u : ℝ} (n a : ℕ) (hu : u ∈ Ico ((a : ℝ) / 2 ^ n) (((a : ℝ) + 1) / 2 ^ n)) : dig n u = a := by
  unfold dig
  have hP : (0 : ℝ) < 2 ^ n := by positivity
  have h1 : (a : ℝ) ≤ u * 2 ^ n := (div_le_iff₀ hP).1 hu.1
  have h2 : u * 2 ^ n < (a : ℝ) + 1 := (lt_div_iff₀ hP).1 hu.2
  have e : (2 : ℝ) ^ n * u = u * 2 ^ n := mul_comm _ _
  have h0 : (0 : ℝ) ≤ 2 ^ n * u := by rw [e]; exact le_trans (Nat.cast_nonneg a) h1
  rw [Nat.floor_eq_iff h0, e]
  exact ⟨h1, h2⟩

lemma Iv_meas (x : ℕ → ℕ → ℝ) (r : ℕ → ℝ) (n a : ℕ) : MeasurableSet (Iv x r n a) := measurableSet_Icc

lemma dyadic_len (n a : ℕ) : ((a : ℝ) + 1) / 2 ^ n - (a : ℝ) / 2 ^ n = (1 / 2 : ℝ) ^ n := by
  rw [one_div_pow]; ring

lemma Stages.mass_ge (h : Stages x r) (n a : ℕ) (ha : a < 2 ^ n) :
    ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ≤ cantorMeasure x (Iv x r n a) := by
  unfold cantorMeasure
  rw [Measure.map_apply_of_aemeasurable h.psi_aemeasurable (Iv_meas x r n a),
    Measure.restrict_apply' measurableSet_Ico]
  have hsub : Ico ((a : ℝ) / 2 ^ n) (((a : ℝ) + 1) / 2 ^ n) ⊆ psi x ⁻¹' Iv x r n a ∩ Ico (0 : ℝ) 1 := by
    intro u hu
    have hd := dyadic_sub n a hu
    have hu01 : u ∈ Ico (0 : ℝ) 1 := by
      refine ⟨le_trans (by positivity) hu.1, lt_of_lt_of_le hu.2 ?_⟩
      rw [div_le_one (by positivity)]
      have : ((a + 1 : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt ha
      push_cast at this; exact this
    refine ⟨?_, hu01⟩
    have := h.psi_mem hu01 n
    rwa [hd] at this
  refine le_trans ?_ (measure_mono hsub)
  rw [Real.volume_Ico, dyadic_len]

lemma Stages.supp (h : Stages x r) : cantorMeasure x (Icc (1 : ℝ) 2)ᶜ = 0 := by
  unfold cantorMeasure
  rw [Measure.map_apply_of_aemeasurable h.psi_aemeasurable isClosed_Icc.measurableSet.compl,
    Measure.restrict_apply' measurableSet_Ico]
  have : psi x ⁻¹' (Icc (1 : ℝ) 2)ᶜ ∩ Ico (0 : ℝ) 1 = ∅ := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    intro hu hu01
    apply hu
    have h1 := h.psi_mem hu01 0
    have hd : dig 0 u = 0 := by have := dig_lt hu01 0; simpa using this
    rw [hd] at h1
    have h0 : x 0 0 = 3 / 2 := h.root.1
    have h2 : r 0 = 1 / 2 := h.root.2
    simp only [Iv, mem_Icc, h0, h2] at h1
    constructor <;> linarith [h1.1, h1.2]
  rw [this]; simp

lemma Stages.null_single (h : Stages x r) (y : ℝ) : cantorMeasure x {y} = 0 := by
  have hle : ∀ n, cantorMeasure x {y} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    intro n
    unfold cantorMeasure
    rw [Measure.map_apply_of_aemeasurable h.psi_aemeasurable (measurableSet_singleton y),
      Measure.restrict_apply' measurableSet_Ico]
    by_cases hne : (psi x ⁻¹' {y} ∩ Ico (0 : ℝ) 1).Nonempty
    · obtain ⟨u0, hu0, hu01⟩ := hne
      have ha : dig n u0 < 2 ^ n := dig_lt hu01 n
      have hsub : psi x ⁻¹' {y} ∩ Ico (0 : ℝ) 1 ⊆
          Ico ((dig n u0 : ℝ) / 2 ^ n) (((dig n u0 : ℝ) + 1) / 2 ^ n) := by
        rintro u ⟨hu, hu01'⟩
        have hy1 : y ∈ Iv x r n (dig n u) := by
          have := h.psi_mem hu01' n
          rwa [show psi x u = y from hu] at this
        have hy0 : y ∈ Iv x r n (dig n u0) := by
          have := h.psi_mem hu01 n
          rwa [show psi x u0 = y from hu0] at this
        have hdeq : dig n u = dig n u0 := by
          by_contra hne'
          exact Set.disjoint_left.1 (h.disjoint n (dig_lt hu01' n) ha hne') hy1 hy0
        have hP : (0 : ℝ) < 2 ^ n := by positivity
        have h0 : 0 ≤ (2 : ℝ) ^ n * u := by have := hu01'.1; positivity
        have hfl := (Nat.floor_eq_iff h0).1 hdeq
        have e : (2 : ℝ) ^ n * u = u * 2 ^ n := mul_comm _ _
        rw [e] at hfl
        constructor
        · rw [div_le_iff₀ hP]; exact hfl.1
        · rw [lt_div_iff₀ hP]; exact hfl.2
      refine le_trans (measure_mono hsub) ?_
      rw [Real.volume_Ico, dyadic_len]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]; simp
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    simpa using this
  exact le_antisymm (ge_of_tendsto' hlim hle) bot_le

theorem Stages.stageProperty (h : Stages x r) : StageProperty (cantorMeasure x) := by
  haveI := h.isProb
  intro n hn c hc
  obtain ⟨k, E, hE, hP⟩ := h.P n hn c hc
  set S : Finset ℕ := Finset.range (2 ^ n) \ E with hS
  have hSlt : ∀ a ∈ S, a < 2 ^ n := fun a ha => by simpa [hS] using (Finset.mem_sdiff.1 ha).1
  have hGmeas : MeasurableSet (⋃ a ∈ S, Iv x r n a) :=
    Finset.measurableSet_biUnion _ (fun a _ => Iv_meas x r n a)
  refine ⟨k, ⋃ a ∈ S, Iv x r n a, hGmeas, ?_, ?_⟩
  · have hdisj : (↑S : Set ℕ).PairwiseDisjoint (Iv x r n) := by
      intro a ha a' ha' hne
      exact h.disjoint n (hSlt a ha) (hSlt a' ha') hne
    have hsum : cantorMeasure x (⋃ a ∈ S, Iv x r n a) = ∑ a ∈ S, cantorMeasure x (Iv x r n a) :=
      measure_biUnion_finset hdisj (fun a _ => Iv_meas x r n a)
    have hcompl : cantorMeasure x (⋃ a ∈ S, Iv x r n a)ᶜ = 1 - cantorMeasure x (⋃ a ∈ S, Iv x r n a) :=
      prob_compl_eq_one_sub hGmeas
    have hfin : ∀ a, cantorMeasure x (Iv x r n a) ≠ ⊤ := fun a => measure_ne_top _ _
    have hreal : (cantorMeasure x (⋃ a ∈ S, Iv x r n a)).toReal =
        ∑ a ∈ S, (cantorMeasure x (Iv x r n a)).toReal := by
      rw [hsum, ENNReal.toReal_sum (fun a _ => hfin a)]
    have hge : ∀ a ∈ S, (1 / 2 : ℝ) ^ n ≤ (cantorMeasure x (Iv x r n a)).toReal := fun a ha =>
      (ENNReal.ofReal_le_iff_le_toReal (hfin a)).1 (h.mass_ge n a (hSlt a ha))
    have hcard : 2 ^ n ≤ S.card + n := by
      have := Finset.card_le_card_sdiff_add_card (s := Finset.range (2 ^ n)) (t := E)
      simp only [Finset.card_range] at this
      rw [← hS] at this
      omega
    have hsumge : (S.card : ℝ) * (1 / 2) ^ n ≤ ∑ a ∈ S, (cantorMeasure x (Iv x r n a)).toReal := by
      calc (S.card : ℝ) * (1 / 2) ^ n = ∑ _a ∈ S, (1 / 2 : ℝ) ^ n := by simp
        _ ≤ _ := Finset.sum_le_sum hge
    have htoReal : (cantorMeasure x (⋃ a ∈ S, Iv x r n a)ᶜ).toReal =
        1 - (cantorMeasure x (⋃ a ∈ S, Iv x r n a)).toReal := by
      rw [hcompl, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]; simp
    rw [htoReal, hreal]
    have hpow : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
    have hc' : (2 : ℝ) ^ n ≤ S.card + n := by exact_mod_cast hcard
    have hpos : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    have h2 : ((2 : ℝ) ^ n - n) * (1 / 2) ^ n ≤ (S.card : ℝ) * (1 / 2) ^ n :=
      mul_le_mul_of_nonneg_right (by linarith) hpos
    nlinarith
  · intro l hl i
    obtain ⟨a, haS, hla⟩ := Set.mem_iUnion₂.1 hl
    have haE : a ∉ E := (Finset.mem_sdiff.1 haS).2
    exact hP a (hSlt a haS) haE l hla i

theorem exists_measure_of_stages (h : Stages x r) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ NullSingletonClass μ ∧ μ (Icc (1 : ℝ) 2)ᶜ = 0 ∧
      StageProperty μ :=
  ⟨cantorMeasure x, h.isProb, ⟨h.null_single⟩, h.supp, h.stageProperty⟩

end Beta
end PVG
