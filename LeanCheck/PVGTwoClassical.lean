import Mathlib
import LeanCheck.ChainPW7
import LeanCheck.ChainHamelStrict
import LeanCheck.PVGTwoNoWitness

/-!
# PVGtwo: precompact group topologies below the usual one (Lean check)

The step that the article quotes from Comfort and Ross, proved here for the real line from the Peter–Weyl theorem already
in this repository (`LeanCheck.generatedFact`).

* `tb_join` : a set totally bounded for two group topologies is totally bounded for their join;
* `below_bohr` : a precompact group topology contained in the usual one is contained in the Bohr topology;
* `bohr_of_dilates` : Corollary 5.2: if all dilates of an unbounded set are totally bounded, the topology is contained in
  the Bohr topology;
* `not_precompact_between`, `trace_null_between` : Theorem 5.3 for `τ_B ⊊ γ ⊆ τ_E`;
* `no_dilated_convergence` : no Hausdorff group topology contained in the usual one makes `a t_n → 0` for every `a`.

Order of topologies as in Mathlib: `γ₁ ≤ γ₂` means that `γ₁` is finer.
A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set MeasureTheory
open scoped Pointwise

namespace PVG
namespace Two
open Q95 Lac

/-- Finitely many translates of every neighbourhood of `0` cover the line. -/
def Pre (γ : TopologicalSpace ℝ) : Prop := ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W

lemma pre_iff_tb (γ : TopologicalSpace ℝ) : Pre γ ↔ Tb (@nhds ℝ γ 0) univ := by
  constructor
  · intro h W hW
    obtain ⟨F, hF⟩ := h W hW
    exact ⟨F, fun y _ => hF y⟩
  · intro h W hW
    obtain ⟨F, hF⟩ := h W hW
    exact ⟨F, fun x => hF x (mem_univ _)⟩

/-- A character that is continuous at `0` for the usual topology is `x ↦ c x` modulo `1`. -/
lemma char_of_tendsto (χ : ℝ →+ AddCircle (1 : ℝ))
    (h0 : Tendsto χ (euclidNhds 0) (@nhds (AddCircle (1 : ℝ)) LeanCheck.circTop' 0)) :
    ∃ c : ℝ, ∀ x : ℝ, χ x = ((c * x : ℝ) : AddCircle (1 : ℝ)) := by
  have h1 : Tendsto χ (𝓝 (0 : ℝ)) (𝓝 (χ 0)) := by
    rw [map_zero]; exact h0
  have hu : Continuous (χ : ℝ → AddCircle (1 : ℝ)) := continuous_of_continuousAt_zero χ h1
  exact LeanCheck.usual_char χ hu

/-- If `|t_n| → ∞`, it is not true that `y t_n → 0` modulo `1` for every `y`. -/
lemma not_all_dilates_null (t : ℕ → ℝ) (ht : Tendsto (fun n => |t n|) atTop atTop)
    (hy : ∀ y : ℝ, Tendsto (fun n => ((y * t n : ℝ) : AddCircle (1 : ℝ))) atTop (𝓝 0)) : False := by
  -- integrate the cosine
  have hlim : Tendsto (fun n => ∫ y in (0 : ℝ)..1, Real.cos (2 * Real.pi * (y * t n))) atTop
      (𝓝 (∫ _ in (0 : ℝ)..1, (1 : ℝ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
      intervalIntegrable_const ?_
    · exact Eventually.of_forall fun n => (Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall fun n => Eventually.of_forall fun y _ => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    · refine Eventually.of_forall fun y _ => ?_
      have hcos : Continuous (fun z : AddCircle (1 : ℝ) => (fourier 1 z).re) :=
        Complex.continuous_re.comp (fourier 1).continuous
      have h1 := (hcos.tendsto 0).comp (hy y)
      have h2 : (fourier 1 (0 : AddCircle (1 : ℝ))).re = 1 := by
        rw [fourier_eval_zero]; simp
      rw [h2] at h1
      refine h1.congr fun n => ?_
      show (fourier 1 ((y * t n : ℝ) : AddCircle (1 : ℝ))).re = _
      rw [fourier_coe_apply]
      have e1 : (2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * ((y * t n : ℝ) : ℂ) / ((1 : ℝ) : ℂ)) =
          ((2 * Real.pi * (y * t n) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [e1, Complex.exp_ofReal_mul_I_re]
  have hzero : Tendsto (fun n => ∫ y in (0 : ℝ)..1, Real.cos (2 * Real.pi * (y * t n))) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => (2 * Real.pi * |t n|)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (ht.const_mul_atTop (by positivity))
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [ht.eventually_gt_atTop 0] with n hn
    have htn : t n ≠ 0 := abs_pos.1 hn
    have hk : 2 * Real.pi * t n ≠ 0 := mul_ne_zero (by positivity) htn
    have e1 : (∫ y in (0 : ℝ)..1, Real.cos (2 * Real.pi * (y * t n))) =
        (2 * Real.pi * t n)⁻¹ * Real.sin (2 * Real.pi * t n) := by
      have e2 : (fun y => Real.cos (2 * Real.pi * (y * t n))) = fun y => Real.cos ((2 * Real.pi * t n) * y) := by
        funext y; ring_nf
      rw [e2, intervalIntegral.integral_comp_mul_left (f := Real.cos) hk, integral_cos]
      simp
    rw [e1, norm_mul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs]
    have e3 : |2 * Real.pi * t n| = 2 * Real.pi * |t n| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    rw [e3]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  have := tendsto_nhds_unique hlim hzero
  simp at this

lemma continuous_eval_circ (c : ℝ) : Continuous (fun p : K => p c) := continuous_eval c

lemma exists_sub_half (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) {W : Set ℝ}
    (hW : W ∈ @nhds ℝ γ 0) : ∃ V ∈ @nhds ℝ γ 0, ∀ x ∈ V, ∀ y ∈ V, x - y ∈ W := by
  obtain ⟨V, hV, hsym, hadd⟩ := group_half γ hg W hW
  exact ⟨V, hV, fun x hx y hy => by rw [sub_eq_add_neg]; exact hadd x hx _ (hsym y hy)⟩

/-- A set totally bounded for two group topologies is totally bounded for their join. -/
lemma tb_join (γ₁ γ₂ : TopologicalSpace ℝ) (h1 : @IsTopologicalAddGroup ℝ γ₁ _) (h2 : @IsTopologicalAddGroup ℝ γ₂ _)
    (Y : Set ℝ) (t1 : Tb (@nhds ℝ γ₁ 0) Y) (t2 : Tb (@nhds ℝ γ₂ 0) Y) : Tb (@nhds ℝ (γ₁ ⊓ γ₂) 0) Y := by
  classical
  intro W hW
  have e1 : @nhds ℝ (γ₁ ⊓ γ₂) 0 = @nhds ℝ γ₁ 0 ⊓ @nhds ℝ γ₂ 0 := @nhds_inf ℝ γ₁ γ₂ 0
  rw [e1] at hW
  obtain ⟨A, hA, B, hB, rfl⟩ := Filter.mem_inf_iff.1 hW
  obtain ⟨A', hA', hAs⟩ := exists_sub_half γ₁ h1 hA
  obtain ⟨B', hB', hBs⟩ := exists_sub_half γ₂ h2 hB
  obtain ⟨F1, hF1⟩ := t1 A' hA'
  obtain ⟨F2, hF2⟩ := t2 B' hB'
  let good : ℝ × ℝ → Prop := fun q => ∃ p, p - q.1 ∈ A' ∧ p - q.2 ∈ B'
  let pick : ℝ × ℝ → ℝ := fun q => if h : good q then h.choose else 0
  refine ⟨(F1 ×ˢ F2).image pick, fun y hy => ?_⟩
  obtain ⟨f1, hf1, hy1⟩ := hF1 y hy
  obtain ⟨f2, hf2, hy2⟩ := hF2 y hy
  have hq : good (f1, f2) := ⟨y, hy1, hy2⟩
  have hp : pick (f1, f2) = hq.choose := dif_pos hq
  refine ⟨pick (f1, f2), Finset.mem_image_of_mem _ (Finset.mk_mem_product hf1 hf2), ?_⟩
  rw [hp]
  have hs := hq.choose_spec
  constructor
  · have := hAs _ hy1 _ hs.1
    simpa using this
  · have := hBs _ hy2 _ hs.2
    simpa using this

lemma bohr_group : @IsTopologicalAddGroup ℝ bohrTop _ := by
  rw [bohrTop_eq]
  exact isTopologicalAddGroup_induced eHom

lemma pre_bohr : Pre bohrTop := by
  intro W hW
  obtain ⟨F, η, hη, hF⟩ := exists_bset_subset hW
  obtain ⟨X, hX⟩ := bohr_tb F hη
  exact ⟨X, fun x => by
    obtain ⟨f, hf, h⟩ := hX x
    exact ⟨f, hf, hF h⟩⟩

lemma bohr_t2 : @T2Space ℝ bohrTop := by
  have hinj : Function.Injective e := by
    intro x y hxy
    have h : e (x - y) = 0 := by
      have h1 := e_add (x - y) y
      rw [sub_add_cancel, hxy] at h1
      exact add_right_cancel (a := e (x - y)) (b := e y) (c := 0) (by rw [zero_add]; exact h1.symm)
    by_contra hne
    have hd : x - y ≠ 0 := sub_ne_zero.2 hne
    have h2 := DFunLike.congr_fun h ((x - y)⁻¹ / 2)
    rw [e_apply, AddMonoidHom.zero_apply, div_mul_eq_mul_div, inv_mul_cancel₀ hd] at h2
    have h3 : dint (1 / 2) = 0 := by
      unfold dint
      rw [h2]; simp
    rw [dint_half] at h3
    norm_num at h3
  letI : TopologicalSpace ℝ := bohrTop
  exact T2Space.of_injective_continuous hinj continuous_induced_dom

lemma usual_le_nhds (γ : TopologicalSpace ℝ) (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) :
    euclidNhds 0 ≤ @nhds ℝ (γ ⊓ bohrTop) 0 := by
  have e1 : @nhds ℝ (γ ⊓ bohrTop) 0 = @nhds ℝ γ 0 ⊓ @nhds ℝ bohrTop 0 := @nhds_inf ℝ γ bohrTop 0
  rw [e1]
  refine le_inf heu ?_
  have := continuous_e.le_induced
  exact nhds_mono this

/-- **A precompact group topology contained in the usual one is contained in the Bohr topology.** -/
theorem below_bohr (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (hpc : Pre γ) : bohrTop ≤ γ := by
  set γ' := γ ⊓ bohrTop with hγ'
  have hg' : @IsTopologicalAddGroup ℝ γ' _ := isTopologicalAddGroup_inf hg bohr_group
  have hpc' : Pre γ' := (pre_iff_tb _).2
    (tb_join γ bohrTop hg bohr_group univ ((pre_iff_tb _).1 hpc) ((pre_iff_tb _).1 pre_bohr))
  have ht2 : @T2Space ℝ γ' := by
    have hle : γ' ≤ bohrTop := inf_le_right
    have hc : @Continuous ℝ ℝ γ' bohrTop id := continuous_id_of_le hle
    exact @T2Space.of_injective_continuous ℝ ℝ γ' bohrTop bohr_t2 id Function.injective_id hc
  have hgen := LeanCheck.generatedFact γ' hg' ht2 hpc'
  refine le_trans ?_ (inf_le_left : γ' ≤ γ)
  refine le_trans ?_ (le_of_eq hgen.symm)
  refine le_iInf fun χ => continuous_iff_le_induced.1 ?_
  have hχ : @Continuous ℝ (AddCircle (1 : ℝ)) γ' LeanCheck.circTop' χ.1 := χ.2
  have h0 : Tendsto χ.1 (euclidNhds 0) (@nhds (AddCircle (1 : ℝ)) LeanCheck.circTop' 0) := by
    have h := (@Continuous.tendsto ℝ (AddCircle (1 : ℝ)) γ' LeanCheck.circTop' _ hχ 0).mono_left (usual_le_nhds γ heu)
    rwa [map_zero] at h
  obtain ⟨c, hc⟩ := char_of_tendsto χ.1 h0
  have h1 : @Continuous K (AddCircle (1 : ℝ)) _ LeanCheck.circTop' (fun p : K => p c) := by
    exact continuous_eval_circ c
  have h2 : @Continuous ℝ K bohrTop _ e := continuous_induced_dom
  have h3 : ((χ.1 : ℝ →+ AddCircle (1 : ℝ)) : ℝ → AddCircle (1 : ℝ)) = (fun p : K => p c) ∘ e := by
    funext x
    show χ.1 x = e x c
    rw [e_apply]
    exact hc x
  rw [h3]
  exact @Continuous.comp ℝ K (AddCircle (1 : ℝ)) bohrTop _ LeanCheck.circTop' e (fun p => p c) h1 h2

/-- Corollary 5.2 with its conclusion `γ ⊆ τ_B`. -/
theorem bohr_of_dilates (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (T : Set ℝ) (hT : ∀ M : ℝ, ∃ t ∈ T, M < |t|)
    (h : ∀ a : ℝ, Tb (@nhds ℝ γ 0) (dil a T)) : bohrTop ≤ γ :=
  below_bohr γ hg heu (group_tb_of_dilates γ hg heu T hT h)

/-- A group topology strictly between the Bohr and the usual one is not precompact. -/
theorem not_precompact_between (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (hfine : γ ≤ bohrTop) (hne : γ ≠ bohrTop) : ¬ Pre γ :=
  fun h => hne (le_antisymm hfine (below_bohr γ hg heu h))

/-- Theorem 5.3 for a topology strictly between. -/
theorem trace_null_between (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (hfine : γ ≤ bohrTop) (hne : γ ≠ bohrTop) :
    ∃ C : Finset ℤ → Set ℝ, (∀ G, EClosed (C G)) ∧ (∀ G, volume (C G) = 0) ∧
      {a : ℝ | TopologicalSpace.induced (Subtype.val : Ja a → ℝ) γ =
        TopologicalSpace.induced (Subtype.val : Ja a → ℝ) bohrTop} ⊆ ⋃ G, C G :=
  trace_null γ hg heu (not_precompact_between γ hg heu hfine hne)

/-- No Hausdorff group topology contained in the usual one satisfies `a t_n → 0` for every `a`, if `|t_n| → ∞`. -/
theorem no_dilated_convergence (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (ht2 : @T2Space ℝ γ) (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (t : ℕ → ℝ) (ht : Tendsto (fun n => |t n|) atTop atTop)
    (h : ∀ a : ℝ, Tendsto (fun n => a * t n) atTop (@nhds ℝ γ 0)) : False := by
  classical
  -- all dilates of the tail are totally bounded
  have htb : ∀ a : ℝ, Tb (@nhds ℝ γ 0) (dil a (range t)) := by
    intro a W hW
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((h a).eventually_mem hW)
    refine ⟨insert 0 ((Finset.range N).image fun n => a * t n), ?_⟩
    rintro y ⟨s, ⟨n, rfl⟩, rfl⟩
    by_cases hn : n < N
    · refine ⟨a * t n, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.2 hn)), ?_⟩
      simpa using mem_of_mem_nhds hW
    · refine ⟨0, Finset.mem_insert_self _ _, ?_⟩
      simpa using hN n (not_lt.1 hn)
  have hunb : ∀ M : ℝ, ∃ s ∈ range t, M < |s| := by
    intro M
    obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop M).exists
    exact ⟨t n, mem_range_self n, hn⟩
  have hpc : Pre γ := group_tb_of_dilates γ hg heu _ hunb htb
  have hgen := LeanCheck.generatedFact γ hg ht2 hpc
  -- a Hausdorff precompact topology has a nonzero continuous character
  have hex : ∃ χ : ℝ →+ AddCircle (1 : ℝ), @Continuous ℝ (AddCircle (1 : ℝ)) γ LeanCheck.circTop' χ ∧ χ ≠ 0 := by
    by_contra hno
    push Not at hno
    have htop : (⊤ : TopologicalSpace ℝ) ≤ γ := by
      rw [hgen]
      refine le_iInf fun χ => ?_
      have h0 : (χ.1 : ℝ →+ AddCircle (1 : ℝ)) = 0 := hno χ.1 χ.2
      refine continuous_iff_le_induced.1 ?_
      rw [h0]
      exact @continuous_const ℝ (AddCircle (1 : ℝ)) ⊤ LeanCheck.circTop' 0
    have hγ : γ = ⊤ := top_le_iff.1 htop
    subst hγ
    obtain ⟨U, V, hU, hV, h0U, h1V, hd⟩ := @t2_separation ℝ ⊤ ht2 0 1 zero_ne_one
    have hU' : U = univ := by
      rcases (TopologicalSpace.isOpen_top_iff U).1 hU with h2 | h2
      · rw [h2] at h0U; exact absurd h0U (notMem_empty _)
      · exact h2
    rw [hU'] at hd
    exact Set.disjoint_left.1 hd (mem_univ 1) h1V
  obtain ⟨χ, hχ, hne⟩ := hex
  have h0 : Tendsto χ (euclidNhds 0) (@nhds (AddCircle (1 : ℝ)) LeanCheck.circTop' 0) := by
    have h := (@Continuous.tendsto ℝ (AddCircle (1 : ℝ)) γ LeanCheck.circTop' _ hχ 0).mono_left heu
    rwa [map_zero] at h
  obtain ⟨c, hc⟩ := char_of_tendsto χ h0
  have hc0 : c ≠ 0 := by
    intro h1
    refine hne (AddMonoidHom.ext fun x => ?_)
    rw [hc x, h1, zero_mul]
    rfl
  -- hence `y t_n → 0` modulo `1` for every `y`
  have hy : ∀ y : ℝ, Tendsto (fun n => ((y * t n : ℝ) : AddCircle (1 : ℝ))) atTop
      (@nhds (AddCircle (1 : ℝ)) LeanCheck.circTop' 0) := by
    intro y
    have h1 : Tendsto (fun n => χ (y / c * t n)) atTop (@nhds (AddCircle (1 : ℝ)) LeanCheck.circTop' (χ 0)) :=
      (@Continuous.tendsto ℝ (AddCircle (1 : ℝ)) γ LeanCheck.circTop' _ hχ 0).comp (h (y / c))
    rw [map_zero] at h1
    refine h1.congr fun n => ?_
    have e1 : c * (y / c * t n) = y * t n := by
      rw [← mul_assoc, mul_div_cancel₀ y hc0]
    rw [hc, e1]
  exact not_all_dilates_null t ht hy

end Two
end PVG
