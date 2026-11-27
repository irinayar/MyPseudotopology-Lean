import Mathlib
import LeanCheck.PVGTwoClassical
import LeanCheck.PVGTwoUnion
import LeanCheck.PVGTwoAlmost

/-!
# PVGtwo: statements that the earlier files left out (Lean check)

* `step1` : a locally quasi-convex group topology strictly between the Bohr and the usual one has a bounded infinite
  equicontinuous set of frequencies, hence a convergent sequence of distinct ones (Step 1 of PVGfull Proposition 16.1);
* `criterion`, `not_lqc_Lambda`, `lqc_below_av`, `av_not_lqc` : Corollary 4.3 (a) ⇒ (b) and Corollary 6.6;
* `Lambda_uncountable` : Remark 6.7;
* `Serves`, `servable_countable`, `serves_dil`, `servable_group` : Section 7 in the words "can be served";
* `countable_base` : Proposition 7.3;
* `not_servable_two`, `not_servable_point` : Corollaries 7.5 and 7.9;
* `not_servable_union`, `maximal_servable`, `union_finest`, `two_finest` : Corollaries 7.13 and 7.5 (b).

Order of topologies as in Mathlib: `γ₁ ≤ γ₂` means that `γ₁` is finer. Sequences are indexed from `0`.
A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set MeasureTheory
open scoped Pointwise BoundedContinuousFunction

namespace PVG
namespace Two
open Q95 Lac

/-! ## Facts about the usual topology, stated away from variable topologies -/

lemma exists_seq_of_infinite_bounded (C : Set ℝ) (hC : C.Infinite) (R : ℝ) (hR : C ⊆ Icc (-R) R) :
    ∃ c : ℕ → ℝ, ∃ c0 : ℝ, (∀ k, c k ∈ C) ∧ (∀ k, c k ≠ c0) ∧ Tendsto c atTop (euclidNhds c0) := by
  obtain ⟨c0, -, hacc⟩ := hC.exists_accPt_of_subset_isCompact isCompact_Icc hR
  have hcl := mem_closure_iff_clusterPt.2 (accPt_principal_iff_clusterPt.1 hacc)
  obtain ⟨c, hc, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  exact ⟨c, c0, fun k => (hc k).1, fun k => (hc k).2, hlim⟩

lemma ball_of_euclid {W : Set ℝ} (h : W ∈ euclidNhds 0) : ∃ η : ℝ, 0 < η ∧ ∀ x : ℝ, |x| < η → x ∈ W := by
  obtain ⟨η, hη, hs⟩ := Metric.mem_nhds_iff.1 h
  exact ⟨η, hη, fun x hx => hs (by simpa [Metric.mem_ball, Real.dist_eq] using hx)⟩

/-- The usual closure. -/
def ecl (s : Set ℝ) : Set ℝ := closure s

lemma ecl_closed (s : Set ℝ) : EClosed (ecl s) := isClosed_closure

lemma subset_ecl (s : Set ℝ) : s ⊆ ecl s := subset_closure

lemma ecl_sub {V : Set ℝ} (hV : V ∈ euclidNhds 0) {x : ℝ} (hx : x ∈ ecl V) : ∃ u ∈ V, ∃ v ∈ V, x = u + v := by
  obtain ⟨η, hη, hb⟩ := ball_of_euclid hV
  obtain ⟨v, hv, hd⟩ := Metric.mem_closure_iff.1 hx η hη
  rw [Real.dist_eq] at hd
  exact ⟨v, hv, x - v, hb _ hd, by ring⟩

lemma closed_cond (F : Finset ℚ) (D : Set ℝ) (hD : EClosed D) :
    EClosed {a : ℝ | ∀ s ∈ Sset, ∃ f ∈ F, a * s - (f : ℝ) ∈ D} := by
  have h : {a : ℝ | ∀ s ∈ Sset, ∃ f ∈ F, a * s - (f : ℝ) ∈ D} =
      ⋂ s ∈ Sset, ⋃ f ∈ F, (fun a : ℝ => a * s - (f : ℝ)) ⁻¹' D := by
    ext a; simp
  rw [h]
  refine isClosed_biInter fun s _ => ?_
  refine Set.Finite.isClosed_biUnion F.finite_toSet fun f _ => ?_
  exact IsClosed.preimage (by fun_prop) hD

lemma rat_near (x η : ℝ) (hη : 0 < η) : ∃ q : ℚ, |x - (q : ℝ)| < η := exists_rat_near x hη

lemma shift_closed_null (D : Set ℝ) (hD : EClosed D) (h0 : volume D = 0) (t : ℝ) :
    EClosed ((fun x : ℝ => x + t) ⁻¹' D) ∧ volume ((fun x : ℝ => x + t) ⁻¹' D) = 0 :=
  ⟨IsClosed.preimage (by fun_prop) hD, by rw [measure_preimage_add_right]; exact h0⟩

lemma map_mul_euclid (c : ℝ) : Filter.map (fun x : ℝ => c * x) (euclidNhds 0) ≤ euclidNhds 0 := by
  have h : Tendsto (fun x : ℝ => c * x) (𝓝 0) (𝓝 (c * 0)) := (continuous_const.mul continuous_id).tendsto 0
  rwa [mul_zero] at h

/-! ## Group topologies -/

lemma le_of_nhds_zero (t1 t2 : TopologicalSpace ℝ) (h1 : @IsTopologicalAddGroup ℝ t1 _)
    (h2 : @IsTopologicalAddGroup ℝ t2 _) (h : @nhds ℝ t1 0 ≤ @nhds ℝ t2 0) : t1 ≤ t2 := by
  refine le_of_nhds_le_nhds fun x => ?_
  have key : ∀ t : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ t _ →
      @nhds ℝ t x = Filter.map (fun y => x + y) (@nhds ℝ t 0) := by
    intro t ht
    letI := t
    haveI := ht
    exact (map_add_left_nhds_zero x).symm
  rw [key t1 h1, key t2 h2]
  exact Filter.map_mono h

/-! ## Step 1 and Corollary 6.6 -/

lemma nsmul_nhds (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) (U : Set ℝ) (hU : U ∈ @nhds ℝ γ 0)
    (m : ℕ) : {x : ℝ | ∀ k ∈ Finset.range (m + 1), (k : ℝ) * x ∈ U} ∈ @nhds ℝ γ 0 := by
  have h : ∀ k ∈ Finset.range (m + 1), {x : ℝ | (k : ℝ) * x ∈ U} ∈ @nhds ℝ γ 0 := by
    intro k _
    have hc : @Continuous ℝ ℝ γ γ (fun x : ℝ => k • x) := by
      letI := γ
      haveI := hg
      exact continuous_nsmul k
    have h0 := @Continuous.tendsto ℝ ℝ γ γ _ hc 0
    rw [smul_zero] at h0
    refine Filter.mem_of_superset (h0 hU) fun x hx => ?_
    simpa [nsmul_eq_mul] using hx
  have := (Filter.biInter_finset_mem (Finset.range (m + 1))).2 h
  refine Filter.mem_of_superset this fun x hx k hk => ?_
  exact mem_iInter₂.1 hx k hk

theorem step1 (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) (hfine : γ ≤ bohrTop)
    (hne : γ ≠ bohrTop) (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (hq : LQC γ) :
    ∃ E : Set ℝ, (∀ ε : ℝ, 0 < ε → {x : ℝ | ∀ c ∈ E, dint (c * x) ≤ ε} ∈ @nhds ℝ γ 0) ∧
      ∃ c : ℕ → ℝ, ∃ c0 : ℝ, (∀ k, c k ∈ E) ∧ (∀ k, c k ≠ c0) ∧ Tendsto c atTop (euclidNhds c0) := by
  classical
  have key : ∃ S : Set (ℝ →+ AddCircle (1 : ℝ)),
      (∀ χ ∈ S, @Continuous ℝ (AddCircle (1 : ℝ)) γ circleTop χ) ∧ {x | ∀ χ ∈ S, ‖χ x‖ ≤ 1 / 4} ∈ @nhds ℝ γ 0 ∧
      {c : ℝ | ∃ χ ∈ S, ∀ x : ℝ, χ x = ((c * x : ℝ) : AddCircle (1 : ℝ))}.Infinite := by
    by_contra hcon
    refine hne (le_antisymm hfine (le_of_nhds_zero _ _ bohr_group hg fun W hW => ?_))
    obtain ⟨S, hS, hU, hUW⟩ := hq W hW
    set C := {c : ℝ | ∃ χ ∈ S, ∀ x : ℝ, χ x = ((c * x : ℝ) : AddCircle (1 : ℝ))} with hC
    have hfin : C.Finite := by
      by_contra h
      exact hcon ⟨S, hS, hU, h⟩
    refine Filter.mem_of_superset (bset_mem hfin.toFinset (η := 1 / 4) (by norm_num)) fun x hx => hUW ?_
    intro χ hχ
    have h0 : Tendsto χ (euclidNhds 0) (@nhds (AddCircle (1 : ℝ)) circleTop 0) := by
      have h := (@Continuous.tendsto ℝ (AddCircle (1 : ℝ)) γ circleTop _ (hS χ hχ) 0).mono_left heu
      rwa [map_zero] at h
    obtain ⟨c, hc⟩ := char_of_tendsto χ h0
    have hcC : c ∈ C := ⟨χ, hχ, hc⟩
    rw [hc x]
    exact le_of_lt (hx c (hfin.mem_toFinset.2 hcC))
  obtain ⟨S, hS, hU, hinf⟩ := key
  set C := {c : ℝ | ∃ χ ∈ S, ∀ x : ℝ, χ x = ((c * x : ℝ) : AddCircle (1 : ℝ))} with hC
  have hmem : ∀ x : ℝ, (∀ χ ∈ S, ‖χ x‖ ≤ 1 / 4) → ∀ c ∈ C, dint (c * x) ≤ 1 / 4 := by
    rintro x hx c ⟨χ, hχ, hc⟩
    have := hx χ hχ
    rw [hc x] at this
    exact this
  refine ⟨C, fun ε hε => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
    have hm0 : 0 < m := by
      have : (0 : ℝ) < m := lt_trans (by positivity) hm
      exact_mod_cast this
    refine Filter.mem_of_superset (nsmul_nhds γ hg _ hU m) fun x hx c hc => ?_
    have h1 : ∀ k : ℕ, 1 ≤ k → k ≤ m → dint (k * (c * x)) ≤ 1 / 4 := by
      intro k _ hk
      have h2 := hmem _ (hx k (Finset.mem_range.2 (Nat.lt_succ_of_le hk))) c hc
      rwa [mul_left_comm] at h2
    have h3 := dint_le_of_multiples m hm0 (c * x) h1
    refine h3.trans ?_
    have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
    rw [div_lt_iff₀ hε] at hm
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · obtain ⟨η, hη, hb⟩ := ball_of_euclid (heu hU)
    have hbd : C ⊆ Icc (-(1 / η)) (1 / η) := by
      intro c hc
      rw [mem_Icc, ← abs_le]
      by_contra h
      push Not at h
      have hc0 : c ≠ 0 := by
        intro h1
        rw [h1, abs_zero] at h
        exact absurd h (not_lt.2 (by positivity))
      have hx : |(2 * c)⁻¹| < η := by
        rw [abs_inv, abs_mul, abs_two, inv_lt_iff_one_lt_mul₀ (by positivity)]
        rw [div_lt_iff₀ hη] at h
        nlinarith [abs_nonneg c]
      have h2 := hmem _ (hb _ hx) c hc
      have e1 : c * (2 * c)⁻¹ = 1 / 2 := by field_simp
      rw [e1, dint_half] at h2
      norm_num at h2
    exact exists_seq_of_infinite_bounded C hinf _ hbd

/-- The trace condition at `0` for a set `J` that contains `0`. -/
lemma trace_nhds (γ : TopologicalSpace ℝ) (J : Set ℝ) (h0 : (0 : ℝ) ∈ J)
    (h : TopologicalSpace.induced (Subtype.val : J → ℝ) γ = TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop) :
    ∀ W ∈ @nhds ℝ γ 0, ∃ B ∈ @nhds ℝ bohrTop 0, B ∩ J ⊆ W := by
  intro W hW
  have key : ∀ s : TopologicalSpace ℝ, @nhds J (TopologicalSpace.induced (Subtype.val : J → ℝ) s) ⟨0, h0⟩ =
      Filter.comap (Subtype.val : J → ℝ) (@nhds ℝ s 0) := by
    intro s
    letI := s
    exact nhds_induced _ _
  have e1 : Filter.comap (Subtype.val : J → ℝ) (@nhds ℝ γ 0) =
      Filter.comap (Subtype.val : J → ℝ) (@nhds ℝ bohrTop 0) := by
    rw [← key γ, ← key bohrTop, h]
  have h1 : (Subtype.val : J → ℝ) ⁻¹' W ∈ Filter.comap (Subtype.val : J → ℝ) (@nhds ℝ bohrTop 0) := by
    rw [← e1]; exact Filter.preimage_mem_comap hW
  obtain ⟨B, hB, hs⟩ := Filter.mem_comap.1 h1
  exact ⟨B, hB, fun x hx => hs (a := ⟨x, hx.2⟩) hx.1⟩

def Jt (a : ℝ) : Set ℝ := Icc (-1 : ℝ) 1 + sumT sT [a, -a]

lemma Jt_eq (a : ℝ) : Jt a = Icc (-1 : ℝ) 1 + (a • Tset sT + (-a) • Tset sT) := by
  unfold Jt
  simp only [sumT]
  rw [singleton_zero, add_zero]

lemma zero_mem_Jt (a : ℝ) : (0 : ℝ) ∈ Jt a := by
  rw [Jt_eq]
  have h0 : (0 : ℝ) ∈ Tset sT := Or.inl rfl
  have h1 : (0 : ℝ) ∈ a • Tset sT := ⟨0, h0, by simp⟩
  have h2 : (0 : ℝ) ∈ (-a) • Tset sT := ⟨0, h0, by simp⟩
  have h3 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have := add_mem_add h3 (add_mem_add h1 h2)
  simpa using this

/-- Corollary 4.3, (a) ⇒ (b): from any locally quasi-convex group topology strictly between, one sequence `δ`. -/
theorem criterion (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) (hfine : γ ≤ bohrTop)
    (hne : γ ≠ bohrTop) (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (hq : LQC γ) (t : ℕ → ℝ) :
    ∃ δ : ℕ → ℝ, (∀ k, δ k ≠ 0) ∧ Tendsto δ atTop (euclidNhds 0) ∧ ∀ a : ℝ,
      (∀ W ∈ @nhds ℝ γ 0, ∃ B ∈ @nhds ℝ bohrTop 0,
        B ∩ (Icc (-1 : ℝ) 1 + (a • Tset t + (-a) • Tset t)) ⊆ W) → InA δ t a := by
  obtain ⟨E, hE, c, c0, hc, hne', hlim⟩ := step1 γ hg hfine hne heu hq
  exact ⟨fun k => c k - c0, fun k => sub_ne_zero.2 (hne' k), tendsto_sub_euclid c c0 hlim,
    fun a ha => inA_of_step1 γ hfine E hE c c0 hc hlim t a ha⟩

/-- Corollary 6.6 (a), second part. -/
theorem not_lqc_Lambda (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) (hfine : γ ≤ bohrTop)
    (hne : γ ≠ bohrTop) (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (hq : LQC γ) :
    ¬ ∀ a : ℝ, InL a → TopologicalSpace.induced (Subtype.val : Jt a → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Jt a → ℝ) bohrTop := by
  intro htr
  obtain ⟨E, hE, c, c0, hc, hne', hlim⟩ := step1 γ hg hfine hne heu hq
  obtain ⟨a, ha, hn⟩ := av_no_step1_witness γ hfine E hE c c0 hc hne' hlim
  refine hn ?_
  rw [← Jt_eq]
  exact trace_nhds γ (Jt a) (zero_mem_Jt a) (htr a ha)

lemma gam_zero : gamTop (fun _ => (0 : ℝ)) = bohrTop := by
  rw [gamTop_eq]
  have h : Phi (fun _ => (0 : ℝ)) = (0 : ℝ →+ (ℕ →ᵇ AddCircle (1 : ℝ))) := by
    refine AddMonoidHom.ext fun x => ?_
    refine BoundedContinuousFunction.ext fun k => ?_
    rw [Phi_apply]
    simp
  rw [h]
  have h2 : TopologicalSpace.induced ((0 : ℝ →+ (ℕ →ᵇ AddCircle (1 : ℝ))) : ℝ → (ℕ →ᵇ AddCircle (1 : ℝ)))
      inferInstance = ⊤ := by
    have h3 : ((0 : ℝ →+ (ℕ →ᵇ AddCircle (1 : ℝ))) : ℝ → (ℕ →ᵇ AddCircle (1 : ℝ))) = fun _ => 0 := rfl
    rw [h3]
    exact induced_const
  rw [h2, inf_top_eq]

lemma lqc_bohr : LQC bohrTop := by
  have h := gam_lqc (fun _ => (0 : ℝ))
  rwa [gam_zero] at h

lemma lqc_inf (t1 t2 : TopologicalSpace ℝ) (h1 : LQC t1) (h2 : LQC t2) : LQC (t1 ⊓ t2) := by
  intro W hW
  have e1 : @nhds ℝ (t1 ⊓ t2) 0 = @nhds ℝ t1 0 ⊓ @nhds ℝ t2 0 := @nhds_inf ℝ t1 t2 0
  rw [e1] at hW
  obtain ⟨A, hA, B, hB, rfl⟩ := Filter.mem_inf_iff.1 hW
  obtain ⟨S1, c1, m1, s1⟩ := h1 A hA
  obtain ⟨S2, c2, m2, s2⟩ := h2 B hB
  refine ⟨S1 ∪ S2, ?_, ?_, ?_⟩
  · rintro χ (h | h)
    · exact continuous_le_dom inf_le_left (c1 χ h)
    · exact continuous_le_dom inf_le_right (c2 χ h)
  · rw [e1]
    refine Filter.mem_of_superset (Filter.inter_mem_inf m1 m2) fun x hx χ hχ => ?_
    rcases hχ with h | h
    · exact hx.1 χ h
    · exact hx.2 χ h
  · intro x hx
    exact ⟨s1 fun χ h => hx χ (Or.inl h), s2 fun χ h => hx χ (Or.inr h)⟩

/-- Corollary 6.6 (b). -/
theorem lqc_below_av (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) (hq : LQC γ) (hav : avTop ≤ γ) :
    bohrTop ≤ γ := by
  set γ' := γ ⊓ bohrTop with hγ'
  have hle : avTop ≤ γ' := le_inf hav av_le_bohr
  have hfine : γ' ≤ bohrTop := inf_le_right
  have hg' : @IsTopologicalAddGroup ℝ γ' _ := isTopologicalAddGroup_inf hg bohr_group
  have hq' : LQC γ' := lqc_inf γ bohrTop hq lqc_bohr
  have heu : euclidNhds 0 ≤ @nhds ℝ γ' 0 := le_trans (av_coarser_euclid 0) (nhds_mono hle)
  have htr : ∀ a : ℝ, InL a → TopologicalSpace.induced (Subtype.val : Jt a → ℝ) γ' =
      TopologicalSpace.induced (Subtype.val : Jt a → ℝ) bohrTop := by
    intro a ha
    have hl : ∀ b ∈ [a, -a], InL b := by
      intro b hb
      rcases List.mem_cons.1 hb with h | h
      · rw [h]; exact ha
      · rw [List.mem_singleton.1 h]; exact inL_neg ha
    have h := av_trace 1 [a, -a] hl (Jt a) subset_rfl
    refine le_antisymm (induced_mono hfine) ?_
    rw [← h]
    exact induced_mono hle
  by_cases hne : γ' = bohrTop
  · rw [← hne]; exact inf_le_left
  · exact absurd htr (not_lqc_Lambda γ' hg' hfine hne heu hq')

theorem av_not_lqc : ¬ LQC avTop := by
  intro h
  exact av_ne_bohr (le_antisymm av_le_bohr (lqc_below_av avTop av_group h le_rfl))

lemma sT_ratio' : Tendsto (fun n => |sT (n + 1) / sT n|) atTop atTop := by
  simpa only [abs_div] using sT_ratio

/-- Remark 6.7. -/
theorem Lambda_uncountable : ¬ {a : ℝ | InL a}.Countable := by
  intro h
  obtain ⟨δ, h0, hlim, hA⟩ := exists_seq sT sT_ne sT_ratio' _ h
  obtain ⟨a, ha, hn⟩ := exists_not_inA δ h0 hlim
  exact hn (hA a ha)

/-! ## Section 7 in the words "can be served" -/

/-- `γ` serves `A`: a group topology strictly between the Bohr and the usual one that makes every `aS`, `a ∈ A`,
totally bounded (by `trace_of_tb` and `tb_of_trace` this is the trace condition). -/
def Serves (γ : TopologicalSpace ℝ) (A : Set ℝ) : Prop :=
  @IsTopologicalAddGroup ℝ γ _ ∧ γ ≤ bohrTop ∧ γ ≠ bohrTop ∧ euclidNhds 0 ≤ @nhds ℝ γ 0 ∧
    ∀ a ∈ A, Tb (@nhds ℝ γ 0) (dil a Sset)

def Servable (A : Set ℝ) : Prop := ∃ γ : TopologicalSpace ℝ, Serves γ A

def Hg (γ : TopologicalSpace ℝ) : Set ℝ := {a | Tb (@nhds ℝ γ 0) (dil a Sset)}

lemma serves_not_pre {γ : TopologicalSpace ℝ} {A : Set ℝ} (h : Serves γ A) : ¬ Pre γ :=
  not_precompact_between γ h.1 h.2.2.2.1 h.2.1 h.2.2.1

lemma serves_Hg {γ : TopologicalSpace ℝ} {A : Set ℝ} (h : Serves γ A) : Serves γ (Hg γ) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun _ ha => ha⟩

lemma servable_mono {A B : Set ℝ} (h : A ⊆ B) (hB : Servable B) : Servable A := by
  obtain ⟨γ, h1, h2, h3, h4, h5⟩ := hB
  exact ⟨γ, h1, h2, h3, h4, fun a ha => h5 a (h ha)⟩

lemma neg_mem_Sset {s : ℝ} (hs : s ∈ Sset) : -s ∈ Sset := by
  rcases hs with h | ⟨n, hn, h | h⟩
  · exact Or.inl (by rw [h, neg_zero])
  · exact Or.inr ⟨n, hn, Or.inr (by rw [h])⟩
  · exact Or.inr ⟨n, hn, Or.inl (by rw [h, neg_neg])⟩

lemma Hg_zero (γ : TopologicalSpace ℝ) : (0 : ℝ) ∈ Hg γ := by
  intro W hW
  refine ⟨{0}, ?_⟩
  rintro y ⟨s, _, rfl⟩
  refine ⟨0, Finset.mem_singleton_self _, ?_⟩
  simpa using mem_of_mem_nhds hW

lemma Hg_neg (γ : TopologicalSpace ℝ) {a : ℝ} (ha : a ∈ Hg γ) : -a ∈ Hg γ := by
  have h : dil (-a) Sset ⊆ dil a Sset := by
    rintro y ⟨s, hs, rfl⟩
    exact ⟨-s, neg_mem_Sset hs, by ring⟩
  intro W hW
  obtain ⟨F, hF⟩ := ha W hW
  exact ⟨F, fun y hy => hF y (h hy)⟩

/-- A set that can be served lies in a subgroup that is served by the same topology. -/
theorem servable_group (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) :
    ∃ H : AddSubgroup ℝ, (H : Set ℝ) = Hg γ :=
  ⟨{ carrier := Hg γ
     zero_mem' := Hg_zero γ
     add_mem' := fun ha hb => tb_sum γ hg _ _ ha hb
     neg_mem' := fun ha => Hg_neg γ ha }, rfl⟩

lemma bohr_dil_cont (c : ℝ) : @Continuous ℝ ℝ bohrTop bohrTop (fun x : ℝ => c * x) := by
  refine continuous_induced_rng.2 ?_
  have h : (e ∘ fun x : ℝ => c * x) = (fun κ : K => c • κ) ∘ e := by
    funext x
    refine AddMonoidHom.ext fun b => ?_
    show e (c * x) b = (c • e x) b
    rw [smul_apply, e_apply, e_apply]
    congr 1
    ring
  rw [h]
  have h2 : Continuous (fun κ : K => c • κ) := by
    refine continuous_induced_rng.2 (continuous_pi fun b => ?_)
    exact continuous_eval_circ (c * b)
  exact @Continuous.comp ℝ K K bohrTop _ _ e (fun κ => c • κ) h2 continuous_induced_dom

lemma bohr_dil (c : ℝ) (hc : c ≠ 0) :
    TopologicalSpace.induced (fun x : ℝ => c * x) bohrTop = bohrTop := by
  have h1 : ∀ d : ℝ, bohrTop ≤ TopologicalSpace.induced (fun x : ℝ => d * x) bohrTop :=
    fun d => continuous_iff_le_induced.1 (bohr_dil_cont d)
  refine le_antisymm ?_ (h1 c)
  have h2 := induced_mono (g := fun x : ℝ => c * x) (h1 c⁻¹)
  rw [induced_compose] at h2
  have e1 : ((fun x : ℝ => c⁻¹ * x) ∘ fun x : ℝ => c * x) = id := by
    funext x; simp [hc]
  rw [e1] at h2
  exact h2.trans (le_of_eq (@induced_id ℝ bohrTop))

lemma induced_dil_inv (γ : TopologicalSpace ℝ) (c : ℝ) (hc : c ≠ 0) :
    TopologicalSpace.induced (fun x : ℝ => c⁻¹ * x) (TopologicalSpace.induced (fun x : ℝ => c * x) γ) = γ := by
  rw [induced_compose]
  have e1 : ((fun x : ℝ => c * x) ∘ fun x : ℝ => c⁻¹ * x) = id := by
    funext x; simp [hc]
  rw [e1, induced_id]

/-- Every dilate of a set that can be served can be served. -/
theorem serves_dil (γ : TopologicalSpace ℝ) (A : Set ℝ) (h : Serves γ A) (c : ℝ) (hc : c ≠ 0) :
    Serves (TopologicalSpace.induced (fun x : ℝ => c * x) γ) {a | c * a ∈ A} := by
  obtain ⟨hg, hf, hne, heu, htb⟩ := h
  have hn : @nhds ℝ (TopologicalSpace.induced (fun x : ℝ => c * x) γ) 0 =
      Filter.comap (fun x : ℝ => c * x) (@nhds ℝ γ 0) := by
    have := @nhds_induced ℝ ℝ γ (fun x : ℝ => c * x) 0
    rwa [mul_zero] at this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · letI := γ
    haveI := hg
    exact isTopologicalAddGroup_induced (AddMonoidHom.mulLeft c)
  · rw [← bohr_dil c hc]
    exact induced_mono hf
  · intro h1
    refine hne ?_
    have h2 := congrArg (TopologicalSpace.induced (fun x : ℝ => c⁻¹ * x)) h1
    rw [induced_dil_inv γ c hc, bohr_dil c⁻¹ (inv_ne_zero hc)] at h2
    exact h2
  · rw [hn, ← Filter.map_le_iff_le_comap]
    exact (map_mul_euclid c).trans heu
  · intro a ha V hV
    rw [hn] at hV
    obtain ⟨W, hW, hs⟩ := Filter.mem_comap.1 hV
    obtain ⟨F, hF⟩ := htb (c * a) ha W hW
    refine ⟨F.image fun f => c⁻¹ * f, ?_⟩
    rintro y ⟨s, hs', rfl⟩
    obtain ⟨f, hf', h⟩ := hF (c * a * s) ⟨s, hs', rfl⟩
    refine ⟨c⁻¹ * f, Finset.mem_image_of_mem _ hf', hs ?_⟩
    show c * (a * s - c⁻¹ * f) ∈ W
    rw [mul_sub, mul_inv_cancel_left₀ hc, ← mul_assoc]
    exact h

lemma Tset_sT : Tset sT = Sset := by
  ext x
  constructor
  · rintro (h | ⟨n, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨n + 1, Nat.le_add_left 1 n, h⟩
  · rintro (h | ⟨n, hn, h⟩)
    · exact Or.inl h
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact Or.inr ⟨m, h⟩

/-- Every countable set can be served. -/
theorem servable_countable (A : Set ℝ) (hA : A.Countable) : Servable A := by
  set Λ := A ∪ (fun a : ℝ => -a) '' A with hΛ
  obtain ⟨γ, hg, -, hf, hne, heu, htr⟩ := countable_witness sT sT_ne sT_ratio' Λ (hA.union (hA.image _))
  refine ⟨γ, hg, hf, hne, heu 0, fun a ha => ?_⟩
  have hl : ∀ b ∈ [a, -a], b ∈ Λ := by
    intro b hb
    rcases List.mem_cons.1 hb with h | h
    · rw [h]; exact Or.inl ha
    · rw [List.mem_singleton.1 h]; exact Or.inr ⟨a, ha, rfl⟩
  have hJ : Ja a ⊆ Icc (-1 : ℝ) 1 + sumT sT [a, -a] := by
    rintro x ⟨s, hs, t, ht, rfl⟩
    rw [← Tset_sT] at hs ht
    have h3 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
    have h4 : a * s + -a * t ∈ sumT sT [a, -a] := by
      simp only [sumT]
      rw [singleton_zero, add_zero]
      exact add_mem_add ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    have := add_mem_add h3 h4
    rwa [zero_add] at this
  exact tb_of_trace γ a (htr 1 [a, -a] hl (Ja a) hJ)

/-! ## Proposition 7.3 -/

lemma exists_chain (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) (U : ℕ → Set ℝ)
    (hU : ∀ k, U k ∈ @nhds ℝ γ 0) :
    ∃ V : ℕ → Set ℝ, (∀ k, V k ∈ @nhds ℝ γ 0) ∧ (∀ k, ∀ x ∈ V k, -x ∈ V k) ∧ (∀ k, V k ⊆ U k) ∧
      ∀ k, ∀ x ∈ V (k + 1), ∀ y ∈ V (k + 1), x + y ∈ V k := by
  have step : ∀ W : Set ℝ, W ∈ @nhds ℝ γ 0 → ∃ V : Set ℝ, V ∈ @nhds ℝ γ 0 ∧ (∀ x ∈ V, -x ∈ V) ∧
      ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W := fun W hW => group_half γ hg W hW
  choose! h h1 h2 h3 using step
  have sym : ∀ W : Set ℝ, W ∈ @nhds ℝ γ 0 → h W ⊆ W := by
    intro W hW x hx
    have := h3 W hW x hx 0 (mem_of_mem_nhds (h1 W hW))
    rwa [add_zero] at this
  let V : ℕ → Set ℝ := fun k => Nat.rec (h (U 0)) (fun n Vn => h (Vn ∩ U (n + 1))) k
  have hV : ∀ k, V k ∈ @nhds ℝ γ 0 := by
    intro k
    induction k with
    | zero => exact h1 _ (hU 0)
    | succ k ih => exact h1 _ (Filter.inter_mem ih (hU (k + 1)))
  have hW : ∀ k, V k ∩ U (k + 1) ∈ @nhds ℝ γ 0 := fun k => Filter.inter_mem (hV k) (hU (k + 1))
  refine ⟨V, hV, ?_, ?_, ?_⟩
  · intro k
    cases k with
    | zero => exact h2 _ (hU 0)
    | succ k => exact h2 _ (hW k)
  · intro k
    cases k with
    | zero => exact sym _ (hU 0)
    | succ k => exact (sym _ (hW k)).trans inter_subset_right
  · intro k x hx y hy
    exact (h3 _ (hW k) x hx y hy).1

lemma chain_anti (γ : TopologicalSpace ℝ) (V : ℕ → Set ℝ) (hV : ∀ k, V k ∈ @nhds ℝ γ 0)
    (hadd : ∀ k, ∀ x ∈ V (k + 1), ∀ y ∈ V (k + 1), x + y ∈ V k) : Antitone V := by
  refine antitone_nat_of_succ_le fun k x hx => ?_
  have := hadd k x hx 0 (mem_of_mem_nhds (hV (k + 1)))
  rwa [add_zero] at this

/-- A chain of symmetric neighbourhoods is a base at `0` of a group topology. -/
lemma topology_of_chain (V : ℕ → Set ℝ) (h0 : ∀ k, (0 : ℝ) ∈ V k) (hsym : ∀ k, ∀ x ∈ V k, -x ∈ V k)
    (hadd : ∀ k, ∀ x ∈ V (k + 1), ∀ y ∈ V (k + 1), x + y ∈ V k) :
    ∃ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ ∧ (@nhds ℝ γ 0).HasBasis (fun _ => True) V := by
  have anti : Antitone V := by
    refine antitone_nat_of_succ_le fun k x hx => ?_
    have := hadd k x hx 0 (h0 (k + 1))
    rwa [add_zero] at this
  let B : AddGroupFilterBasis ℝ := addGroupFilterBasisOfComm (range V) (range_nonempty V)
    (by
      rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
      exact ⟨V (max i j), mem_range_self _, subset_inter (anti (le_max_left i j)) (anti (le_max_right i j))⟩)
    (by
      rintro _ ⟨i, rfl⟩
      exact h0 i)
    (by
      rintro _ ⟨i, rfl⟩
      refine ⟨V (i + 1), mem_range_self _, ?_⟩
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact hadd i x hx y hy)
    (by
      rintro _ ⟨i, rfl⟩
      exact ⟨V i, mem_range_self _, fun x hx => hsym i x hx⟩)
  refine ⟨B.topology, B.isTopologicalAddGroup, ?_⟩
  have hb := B.nhds_zero_hasBasis
  refine hb.to_hasBasis ?_ ?_
  · rintro s hs
    obtain ⟨i, rfl⟩ := hs
    exact ⟨i, trivial, subset_rfl⟩
  · intro i _
    exact ⟨V i, mem_range_self i, subset_rfl⟩

/-- Proposition 7.3, the equivalence. -/
theorem countable_base_iff (A : Set ℝ) : Servable A ↔
    ∃ γ0 : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ0 _ ∧ euclidNhds 0 ≤ @nhds ℝ γ0 0 ∧ ¬ Pre γ0 ∧
      (@nhds ℝ γ0 0).IsCountablyGenerated ∧ ∀ a ∈ A, Tb (@nhds ℝ γ0 0) (dil a Sset) := by
  constructor
  · rintro ⟨γ1, h⟩
    have hnp := serves_not_pre h
    obtain ⟨hg, hf, hne, heu, htb⟩ := h
    unfold Pre at hnp
    push Not at hnp
    obtain ⟨W, hW, hnf⟩ := hnp
    obtain ⟨V, hV, hsym, hsub, hadd⟩ := exists_chain γ1 hg (fun _ => W) (fun _ => hW)
    obtain ⟨γ0, hg0, hb⟩ := topology_of_chain V (fun k => mem_of_mem_nhds (hV k)) hsym hadd
    have hle : @nhds ℝ γ1 0 ≤ @nhds ℝ γ0 0 := by
      intro s hs
      obtain ⟨i, -, hi⟩ := hb.mem_iff.1 hs
      exact Filter.mem_of_superset (hV i) hi
    refine ⟨γ0, hg0, heu.trans hle, ?_, hb.isCountablyGenerated, fun a ha W' hW' => htb a ha W' (hle hW')⟩
    intro hpre
    obtain ⟨F, hF⟩ := hpre (V 0) (hb.mem_of_mem trivial)
    obtain ⟨x, hx⟩ := hnf F
    obtain ⟨f, hf', h⟩ := hF x
    exact hx f hf' (hsub 0 h)
  · rintro ⟨γ0, hg0, heu, hnp, -, htb⟩
    refine ⟨γ0 ⊓ bohrTop, isTopologicalAddGroup_inf hg0 bohr_group, inf_le_right, ?_, usual_le_nhds γ0 heu, ?_⟩
    · intro h
      apply hnp
      have hle : bohrTop ≤ γ0 := by rw [← h]; exact inf_le_left
      intro W hW
      exact pre_bohr W (nhds_mono hle hW)
    · intro a ha
      refine tb_join γ0 bohrTop hg0 bohr_group _ (htb a ha) ?_
      intro W hW
      obtain ⟨F, hF⟩ := pre_bohr W hW
      exact ⟨F, fun y _ => hF y⟩

/-- Proposition 7.3, the second part: `H_γ` for the join is `F_{σδ}`, and lies in countably many closed null sets. -/
theorem countable_base_Hg (γ0 : TopologicalSpace ℝ) (hg0 : @IsTopologicalAddGroup ℝ γ0 _)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ0 0) (hnp : ¬ Pre γ0) (hc : (@nhds ℝ γ0 0).IsCountablyGenerated) :
    Hg (γ0 ⊓ bohrTop) = Hg γ0 ∧
    (∃ D : ℕ → Finset ℚ → Set ℝ, (∀ k F, EClosed (D k F)) ∧ Hg γ0 = ⋂ k, ⋃ F, D k F) ∧
    (∃ C : Finset ℤ → Set ℝ, (∀ G, EClosed (C G)) ∧ (∀ G, volume (C G) = 0) ∧ Hg γ0 ⊆ ⋃ G, C G) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · ext a
    constructor
    · intro h W hW
      exact h W (nhds_mono inf_le_left hW)
    · intro h
      refine tb_join γ0 bohrTop hg0 bohr_group _ h ?_
      intro W hW
      obtain ⟨F, hF⟩ := pre_bohr W hW
      exact ⟨F, fun y _ => hF y⟩
  · obtain ⟨U, hU⟩ := (@nhds ℝ γ0 0).exists_antitone_basis
    obtain ⟨V, hV, hsym, hsub, hadd⟩ := exists_chain γ0 hg0 U (fun k => hU.toHasBasis.mem_of_mem trivial)
    refine ⟨fun k F => {a : ℝ | ∀ s ∈ Sset, ∃ f ∈ F, a * s - (f : ℝ) ∈ ecl (V k)},
      fun k F => closed_cond F _ (ecl_closed _), ?_⟩
    ext a
    rw [mem_iInter]
    constructor
    · intro ha k
      obtain ⟨F, hF⟩ := ha (V (k + 1)) (hV (k + 1))
      obtain ⟨η, hη, hb⟩ := ball_of_euclid (heu (hV (k + 1)))
      choose q hq using fun f : ℝ => rat_near f η hη
      refine mem_iUnion.2 ⟨F.image q, fun s hs => ?_⟩
      obtain ⟨f, hf, h⟩ := hF (a * s) ⟨s, hs, rfl⟩
      refine ⟨q f, Finset.mem_image_of_mem _ hf, subset_ecl _ ?_⟩
      have := hadd k _ h _ (hb _ (hq f))
      rwa [sub_add_sub_cancel] at this
    · intro ha W hW
      obtain ⟨k, -, hk⟩ := hU.toHasBasis.mem_iff.1 hW
      obtain ⟨F, hF⟩ := mem_iUnion.1 (ha (k + 1))
      refine ⟨F.image fun f : ℚ => (f : ℝ), ?_⟩
      rintro y ⟨s, hs, rfl⟩
      obtain ⟨f, hf, h⟩ := hF s hs
      refine ⟨f, Finset.mem_image_of_mem _ hf, hk (hsub k ?_)⟩
      obtain ⟨u, hu, v, hv, huv⟩ := ecl_sub (heu (hV (k + 1))) h
      rw [huv]
      exact hadd k u hu v hv
  · exact group_null_cover γ0 hg0 heu Sset Sset_unbounded hnp

/-! ## Corollaries 7.5, 7.9 and 7.13 -/

def A2 : Set ℝ := {a | InA dlt2 sT a}

lemma dlt2_le_one (k : ℕ) : |dlt2 k| ≤ 1 := by
  unfold dlt2
  rw [abs_of_pos (by positivity)]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)

lemma serves_dlt2 : Serves (gamTop dlt2) A2 := by
  obtain ⟨c, -, htb, -, hne⟩ := exists_point_unservable
  exact ⟨gam_group _, gam_le_bohr _, hne, gam_coarser_euclid dlt2 1 dlt2_le_one 0, htb⟩

theorem not_servable_two : ∃ lam : ℝ, lam ∈ Icc (1 : ℝ) 2 ∧ Servable Agroup ∧
    Servable ((fun a => lam * a) '' Agroup) ∧ ¬ Servable (Agroup ∪ (fun a => lam * a) '' Agroup) := by
  obtain ⟨lam, hl, hun, -⟩ := exists_two_unservable
  have hlam : lam ≠ 0 := (lt_of_lt_of_le one_pos hl.1).ne'
  have hinf := infinite_range_of_tendsto dlt (fun k => (dlt_pos k).ne') dlt_tendsto
  have hM : ∀ k, |dlt k| ≤ 1 := by
    intro k
    rw [abs_of_pos (dlt_pos k)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h1 : Serves (gamTop dlt) Agroup := by
    refine ⟨gam_group _, gam_le_bohr _, gam_ne_bohr _ hinf, gam_coarser_euclid dlt 1 hM 0, fun a ha => ?_⟩
    intro W hW
    obtain ⟨F, hF⟩ := dilates_totally_bounded a ha W hW
    refine ⟨F, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    exact hF s hs
  refine ⟨lam, hl, ⟨_, h1⟩, ?_, ?_⟩
  · have h2 := serves_dil _ _ h1 lam⁻¹ (inv_ne_zero hlam)
    refine servable_mono ?_ ⟨_, h2⟩
    rintro _ ⟨a, ha, rfl⟩
    show lam⁻¹ * (lam * a) ∈ Agroup
    rwa [inv_mul_cancel_left₀ hlam]
  · rintro ⟨γ, h⟩
    refine serves_not_pre h (hun γ h.1 h.2.2.2.1 (fun a ha => h.2.2.2.2 a (Or.inl ha)) ?_)
    exact fun a ha => h.2.2.2.2 _ (Or.inr ⟨a, ha, rfl⟩)

lemma dint_add_le' (u v : ℝ) : dint (u + v) ≤ dint u + dint v := by
  unfold dint
  rw [AddCircle.coe_add]
  exact norm_add_le _ _

lemma inA_add2 {a b : ℝ} (ha : InA dlt2 sT a) (hb : InA dlt2 sT b) : InA dlt2 sT (a + b) := by
  intro ε hε
  filter_upwards [ha (ε / 2) (by positivity), hb (ε / 2) (by positivity)] with k h1 h2 n
  have e1 : (a + b) * dlt2 k * sT n = a * dlt2 k * sT n + b * dlt2 k * sT n := by ring
  rw [e1]
  exact (dint_add_le' _ _).trans (by linarith [h1 n, h2 n])

lemma inA_neg2 {a : ℝ} (ha : InA dlt2 sT a) : InA dlt2 sT (-a) := by
  intro ε hε
  filter_upwards [ha ε hε] with k h n
  have e1 : -a * dlt2 k * sT n = -(a * dlt2 k * sT n) := by ring
  have e2 : ∀ u : ℝ, dint (-u) = dint u := by
    intro u
    unfold dint
    rw [AddCircle.coe_neg, norm_neg]
  rw [e1, e2]
  exact h n

lemma inA_zero2 : InA dlt2 sT 0 := by
  intro ε hε
  refine Eventually.of_forall fun k n => ?_
  simp [dint_zero, hε.le]

def A2group : AddSubgroup ℝ where
  carrier := A2
  zero_mem' := inA_zero2
  add_mem' := inA_add2
  neg_mem' := inA_neg2

/-- Corollary 7.9: adding one point leaves the family, and the subgroup `A(δ) + ℤc` lies in countably many closed null
sets. -/
theorem not_servable_point : ∃ c : ℝ, Servable A2 ∧ Servable {c} ∧ ¬ Servable (insert c A2) ∧
    ¬ Servable ((A2group ⊔ AddSubgroup.zmultiples c : AddSubgroup ℝ) : Set ℝ) ∧
    ∃ C : ℤ × Finset ℤ → Set ℝ, (∀ i, EClosed (C i)) ∧ (∀ i, volume (C i) = 0) ∧
      ((A2group ⊔ AddSubgroup.zmultiples c : AddSubgroup ℝ) : Set ℝ) ⊆ ⋃ i, C i := by
  obtain ⟨c, hun, htb, -, hne⟩ := exists_point_unservable
  have hns : ¬ Servable (insert c A2) := by
    rintro ⟨γ, h⟩
    exact serves_not_pre h (hun γ h.1 h.2.2.2.1 (fun a ha => h.2.2.2.2 a (mem_insert_of_mem _ ha))
      (h.2.2.2.2 c (mem_insert _ _)))
  refine ⟨c, ⟨_, serves_dlt2⟩, servable_countable _ (countable_singleton c), hns, ?_, ?_⟩
  · intro h
    refine hns (servable_mono ?_ h)
    rintro x (rfl | hx)
    · exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples _)
    · exact AddSubgroup.mem_sup_left hx
  · have hs := serves_dlt2
    obtain ⟨C, hcl, hnull, hsub⟩ := group_null_cover (gamTop dlt2) hs.1 hs.2.2.2.1 Sset Sset_unbounded
      (serves_not_pre hs)
    refine ⟨fun i => (fun x : ℝ => x + -(i.1 • c)) ⁻¹' C i.2,
      fun i => (shift_closed_null _ (hcl _) (hnull _) _).1,
      fun i => (shift_closed_null _ (hcl _) (hnull _) _).2, ?_⟩
    intro x hx
    obtain ⟨a, ha, y, hy, rfl⟩ := AddSubgroup.mem_sup.1 hx
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hy
    obtain ⟨G, hG⟩ := mem_iUnion.1 (hsub (htb a ha))
    refine mem_iUnion.2 ⟨(k, G), ?_⟩
    show a + k • c + -(k • c) ∈ C G
    rwa [add_neg_cancel_right]

/-- Corollary 7.13 (a). -/
theorem not_servable_union : (∀ m : ℕ, Servable {a | (2 : ℝ) ^ m * a ∈ A2}) ∧
    Monotone (fun m : ℕ => {a : ℝ | (2 : ℝ) ^ m * a ∈ A2}) ∧
    ¬ Servable (⋃ m : ℕ, {a : ℝ | (2 : ℝ) ^ m * a ∈ A2}) := by
  refine ⟨fun m => ⟨_, serves_dil _ _ serves_dlt2 ((2 : ℝ) ^ m) (by positivity)⟩, ?_, ?_⟩
  · refine monotone_nat_of_le_succ fun m a ha => ?_
    show (2 : ℝ) ^ (m + 1) * a ∈ A2
    have e1 : (2 : ℝ) ^ (m + 1) * a = 2 ^ m * a + 2 ^ m * a := by rw [pow_succ]; ring
    rw [e1]
    exact inA_add2 ha ha
  · rintro ⟨γ, h⟩
    refine serves_not_pre h (exists_union_unservable.1 γ h.1 h.2.2.2.1 (fun a ha => ?_) fun M => ⟨M, le_rfl, ?_⟩)
    · refine h.2.2.2.2 a (mem_iUnion.2 ⟨0, ?_⟩)
      show (2 : ℝ) ^ 0 * a ∈ A2
      rwa [pow_zero, one_mul]
    · intro a ha
      refine h.2.2.2.2 _ (mem_iUnion.2 ⟨M, ?_⟩)
      show (2 : ℝ) ^ M * (a / 2 ^ M) ∈ A2
      rwa [mul_div_cancel₀ _ (by positivity)]

/-- Corollary 7.13 (c): a maximal set that can be served is a vector space over `ℚ`, and does not contain `A(δ)`. -/
theorem maximal_servable (M : Set ℝ) (hM : Servable M) (hmax : ∀ N : Set ℝ, M ⊆ N → Servable N → N = M) :
    (∀ a ∈ M, ∀ b ∈ M, a + b ∈ M) ∧ (∀ q : ℚ, ∀ a ∈ M, (q : ℝ) * a ∈ M) ∧ ¬ A2 ⊆ M := by
  obtain ⟨γ, h⟩ := hM
  have hH : Hg γ = M := hmax _ h.2.2.2.2 ⟨γ, serves_Hg h⟩
  have hadd : ∀ a ∈ M, ∀ b ∈ M, a + b ∈ M := by
    intro a ha b hb
    rw [← hH] at ha hb ⊢
    exact tb_sum γ h.1 a b ha hb
  have hzero : (0 : ℝ) ∈ M := by rw [← hH]; exact Hg_zero γ
  have hneg : ∀ a ∈ M, -a ∈ M := by
    intro a ha
    rw [← hH] at ha ⊢
    exact Hg_neg γ ha
  let G : AddSubgroup ℝ :=
    { carrier := M, zero_mem' := hzero, add_mem' := fun ha hb => hadd _ ha _ hb, neg_mem' := fun ha => hneg _ ha }
  have hz : ∀ (z : ℤ), ∀ a ∈ M, (z : ℝ) * a ∈ M := by
    intro z a ha
    have : z • a ∈ G := G.zsmul_mem ha z
    rwa [zsmul_eq_mul] at this
  have hdiv : ∀ q : ℕ, 0 < q → ∀ a : ℝ, (q : ℝ) * a ∈ M → a ∈ M := by
    intro q hq a ha
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have h2 := serves_dil γ M ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun b hb => by rw [← hH] at hb; exact hb⟩ (q : ℝ) hq0
    have h3 : {b : ℝ | (q : ℝ) * b ∈ M} = M := by
      refine hmax _ (fun b hb => ?_) ⟨_, h2⟩
      have := hz (q : ℤ) b hb
      simpa using this
    rw [← h3]; exact ha
  refine ⟨hadd, fun q a ha => ?_, fun hsub => ?_⟩
  · refine hdiv q.den q.den_pos _ ?_
    have e1 : (q.den : ℝ) * ((q : ℝ) * a) = (q.num : ℝ) * a := by
      have : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
        have h0 : ((q.den : ℚ) * q) = (q.num : ℚ) := by rw [mul_comm]; exact Rat.mul_den_eq_num q
        exact_mod_cast congrArg (fun r : ℚ => (r : ℝ)) h0
      rw [← mul_assoc, this]
    rw [e1]
    exact hz _ a ha
  · have hm : ∀ m : ℕ, ∀ a ∈ A2, a / 2 ^ m ∈ M := by
      intro m a ha
      refine hdiv (2 ^ m) (by positivity) _ ?_
      have e1 : (((2 ^ m : ℕ) : ℝ)) * (a / 2 ^ m) = a := by
        push_cast
        exact mul_div_cancel₀ _ (by positivity)
      rw [e1]
      exact hsub ha
    refine serves_not_pre h (exists_union_unservable.1 γ h.1 h.2.2.2.1 (fun a ha => ?_) fun N => ⟨N, le_rfl, ?_⟩)
    · exact h.2.2.2.2 a (hsub ha)
    · exact fun a ha => h.2.2.2.2 _ (hm N a ha)

/-- Corollary 7.13 (b): `τ_B` is the finest group topology contained in all the `γ_{2^m δ}`. -/
theorem union_finest (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (h : ∀ m : ℕ, gamTop (fun k => dlt2 k * 2 ^ m) ≤ γ) : bohrTop ≤ γ := by
  refine below_bohr γ hg ?_ (exists_union_unservable.2 γ hg h)
  have h0 := h 0
  have e1 : (fun k => dlt2 k * 2 ^ 0) = dlt2 := by
    funext k; rw [pow_zero, mul_one]
  rw [e1] at h0
  exact le_trans (gam_coarser_euclid dlt2 1 dlt2_le_one 0) (nhds_mono h0)

/-- Corollary 7.5 (b). -/
theorem two_finest : ∃ lam : ℝ, lam ∈ Icc (1 : ℝ) 2 ∧
    ∀ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ → gamTop dlt ≤ γ → gamTop (fun k => dlt k / lam) ≤ γ →
      bohrTop ≤ γ := by
  obtain ⟨lam, hl, -, h2⟩ := exists_two_unservable
  have hM : ∀ k, |dlt k| ≤ 1 := by
    intro k
    rw [abs_of_pos (dlt_pos k)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  refine ⟨lam, hl, fun γ hg ha hb => below_bohr γ hg ?_ (h2 γ hg ha hb)⟩
  exact le_trans (gam_coarser_euclid dlt 1 hM 0) (nhds_mono ha)

end Two
end PVG
