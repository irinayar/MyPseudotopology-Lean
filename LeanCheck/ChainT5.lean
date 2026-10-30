import LeanCheck.ChainT4

/-!
# Comparison with arbitrary TVG topologies
(HamelCharactersTVG_v18 Proposition 7.1 `criteria`)

For a TVG topology `τ` on `ℝ` (an additive group topology with every real dilation continuous):

1. `τ ⊆ tu` (Mathlib: `uR ≤ τ`) iff every `τ`-neighbourhood of zero contains an open interval about zero;
2. `tu ⊆ τ` (Mathlib: `τ ≤ uR`) iff some `τ`-neighbourhood of zero is bounded in absolute value;
3. every zero-neighbourhood in a strictly weaker TVG topology (`uR < τ`) is unbounded;
4. every topology weaker than the usual one is path connected.

(Internally the topology is carried in the wrapper `TopW` so that no local instance captures the topology of `ℝ`.)
-/

namespace LeanCheck

open Filter Topology

/-- A TVG topology: additive group topology with all real dilations continuous. -/
def IsTVG (τ : TopologicalSpace ℝ) : Prop :=
  @IsTopologicalAddGroup ℝ τ _ ∧ ∀ c : ℝ, Continuous[τ, τ] (fun x : ℝ => c * x)

lemma uR_group' : @IsTopologicalAddGroup ℝ uR _ := (inferInstance : IsTopologicalAddGroup ℝ)

/-- Two additive group topologies compare as their neighbourhood filters at zero. -/
lemma le_of_nhds_zero_le (s t : TopologicalSpace ℝ) (hs : @IsTopologicalAddGroup ℝ s _)
    (ht : @IsTopologicalAddGroup ℝ t _) (h : ∀ U ∈ @nhds ℝ t 0, U ∈ @nhds ℝ s 0) : s ≤ t := by
  rw [le_iff_nhds]
  intro x
  rw [← @map_add_left_nhds_zero ℝ s _ hs x, ← @map_add_left_nhds_zero ℝ t _ ht x]
  exact map_mono (fun U hU => h U hU)

lemma usual_le_iff_W (W : TopW) (hτ : @IsTopologicalAddGroup ℝ W.t _) :
    uR ≤ W.t ↔ ∀ U ∈ @nhds ℝ W.t 0, U ∈ @nhds ℝ uR 0 := by
  constructor
  · intro h U hU
    exact (nhds_mono h) hU
  · exact le_of_nhds_zero_le uR W.t uR_group' hτ

lemma tvg_coarser_iff_W (W : TopW) (hτ : IsTVG W.t) :
    uR ≤ W.t ↔ ∀ U ∈ @nhds ℝ W.t 0, ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (-ε) ε ⊆ U := by
  rw [usual_le_iff_W W hτ.1]
  constructor
  · intro h U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (show U ∈ 𝓝 (0 : ℝ) from h U hU)
    refine ⟨ε, hε, fun x hx => hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact hx
  · intro h U hU
    obtain ⟨ε, hε, hsub⟩ := h U hU
    have hI : Set.Ioo (-ε) ε ∈ (𝓝 (0 : ℝ)) := Ioo_mem_nhds (by linarith) hε
    exact Filter.mem_of_superset (show Set.Ioo (-ε) ε ∈ @nhds ℝ uR 0 from hI) hsub

lemma tvg_finer_iff_W (W : TopW) (hτ : IsTVG W.t) :
    W.t ≤ uR ↔ ∃ U ∈ @nhds ℝ W.t 0, ∃ M : ℝ, U ⊆ Set.Icc (-M) M := by
  constructor
  · intro h
    exact ⟨Set.Ioo (-1 : ℝ) 1, (nhds_mono h) Ioo_nhds_uR, 1, fun x hx => ⟨hx.1.le, hx.2.le⟩⟩
  · rintro ⟨U, hU, M, hUM⟩
    refine le_of_nhds_zero_le W.t uR hτ.1 uR_group' (fun V hV => ?_)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (show V ∈ 𝓝 (0 : ℝ) from hV)
    set c : ℝ := ε / (2 * (|M| + 1)) with hc
    have hcpos : 0 < c := by positivity
    have hpre : (fun x : ℝ => c⁻¹ * x) ⁻¹' U ∈ @nhds ℝ W.t 0 := by
      have h0 := (@Continuous.continuousAt ℝ ℝ W.t W.t _ 0 (hτ.2 c⁻¹))
      have h1 : U ∈ @nhds ℝ W.t ((fun x : ℝ => c⁻¹ * x) 0) := by simpa using hU
      exact h0 h1
    refine mem_of_superset hpre (fun x hx => hball ?_)
    have hxM := hUM hx
    have h1 : |c⁻¹ * x| ≤ |M| := by
      rw [abs_le]; constructor <;> cases abs_cases M <;> linarith [hxM.1, hxM.2]
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have : x = c * (c⁻¹ * x) := by field_simp
    rw [this, abs_mul, abs_of_pos hcpos]
    calc c * |c⁻¹ * x| ≤ c * |M| := by gcongr
      _ < ε := by
        rw [hc, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg M]

lemma tvg_weaker_consequences_W (W : TopW) (hτ : IsTVG W.t) (hlt : uR < W.t) :
    (∀ U ∈ @nhds ℝ W.t 0, ∀ M : ℝ, ¬ U ⊆ Set.Icc (-M) M) ∧ @PathConnectedSpace ℝ W.t := by
  constructor
  · intro U hU M hUM
    have h1 : W.t ≤ uR := (tvg_finer_iff_W W hτ).2 ⟨U, hU, M, hUM⟩
    exact absurd (le_antisymm hlt.le h1) hlt.ne
  · have hid : Continuous[uR, W.t] (id : ℝ → ℝ) := continuous_id_iff_le.2 hlt.le
    haveI : @PathConnectedSpace ℝ uR := (inferInstance : PathConnectedSpace ℝ)
    exact @Function.Surjective.pathConnectedSpace ℝ ℝ uR W.t _ (id : ℝ → ℝ)
      Function.surjective_id hid

/-- **Proposition 7.1(1).** -/
theorem tvg_coarser_iff (τ : TopologicalSpace ℝ) (hτ : IsTVG τ) :
    uR ≤ τ ↔ ∀ U ∈ @nhds ℝ τ 0, ∃ ε : ℝ, 0 < ε ∧ Set.Ioo (-ε) ε ⊆ U :=
  tvg_coarser_iff_W ⟨τ⟩ hτ

/-- **Proposition 7.1(2).** -/
theorem tvg_finer_iff (τ : TopologicalSpace ℝ) (hτ : IsTVG τ) :
    τ ≤ uR ↔ ∃ U ∈ @nhds ℝ τ 0, ∃ M : ℝ, U ⊆ Set.Icc (-M) M :=
  tvg_finer_iff_W ⟨τ⟩ hτ

/-- **Proposition 7.1, consequences.**  In a strictly weaker TVG topology every zero-neighbourhood is ordinarily
unbounded; every TVG topology weaker than the usual one is path connected. -/
theorem tvg_weaker_consequences (τ : TopologicalSpace ℝ) (hτ : IsTVG τ) (hlt : uR < τ) :
    (∀ U ∈ @nhds ℝ τ 0, ∀ M : ℝ, ¬ U ⊆ Set.Icc (-M) M) ∧ @PathConnectedSpace ℝ τ :=
  tvg_weaker_consequences_W ⟨τ⟩ hτ hlt

end LeanCheck
