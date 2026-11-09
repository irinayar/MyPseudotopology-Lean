import Mathlib
import LeanCheck.PVGBetaDense

/-!
# PVG: the group topology of a family of dilated pseudonorms, and half-integers (Lean check)

Scope. Step "the topology of a measure" and the proofs of (a) and (c) of Theorem `thm:betaexists` of PVG_v22, for an abstract function
`ρ : ℝ → ℝ`. `IsPseudoNorm ρ K` says: `ρ 0 = 0`, `ρ ≥ 0`, `ρ` even, subadditive, `ρ t ≤ K |t|`, and `ρ t > 0` for `t ≠ 0` (for the
article, `ρ t = ∫ min(1, 2π ‖tλ‖) dν(λ)` with `ν` atomless on `[1,2]`). The sets `V(F,δ) = {t : ρ(ct) < δ for all c ∈ F}`, `F` finite,
`δ > 0`, are a base at `0` of the topology `betaTop`.

* `betaTop_isTopologicalAddGroup`, `betaTop_t2`, `eT_le_betaTop`, `betaTop_constSMul` (part (a)): `betaTop` is a Hausdorff group topology inside
  the Euclidean topology with all dilations continuous;
* `half_in_nhds`: if for every finite `F` and `δ > 0` some half-integer `t` has `ρ(ct) < δ` for all `c ∈ F` (hypothesis `HalfInt`), then
  every neighbourhood of `0` contains a half-integer (part (b));
* `chi_one_not_continuous`, `chi_not_continuous` (part (c)): the characters `t ↦ bt + ℤ`, `b ≠ 0`, are not continuous;
* `int_dense`: `ℤ` is dense (through `PVG.Gen.range_subset_closure`).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Pointwise

namespace PVG
namespace Beta

/-- The Euclidean topology of `ℝ`. -/
abbrev eT : TopologicalSpace ℝ := inferInstance

structure IsPseudoNorm (ρ : ℝ → ℝ) (K : ℝ) : Prop where
  zero : ρ 0 = 0
  nonneg : ∀ t, 0 ≤ ρ t
  neg : ∀ t, ρ (-t) = ρ t
  add_le : ∀ t s, ρ (t + s) ≤ ρ t + ρ s
  le_lin : ∀ t, ρ t ≤ K * |t|
  pos : ∀ t, t ≠ 0 → 0 < ρ t
  K_pos : 0 < K

def baseSet (ρ : ℝ → ℝ) (F : Finset ℝ) (δ : ℝ) : Set ℝ := {t | ∀ c ∈ F, ρ (c * t) < δ}

variable {ρ : ℝ → ℝ} {K : ℝ}

noncomputable def basis (h : IsPseudoNorm ρ K) : AddGroupFilterBasis ℝ :=
  addGroupFilterBasisOfComm {V | ∃ (F : Finset ℝ) (δ : ℝ), 0 < δ ∧ V = baseSet ρ F δ}
    ⟨baseSet ρ ∅ 1, ∅, 1, one_pos, rfl⟩
    (by
      rintro _ _ ⟨F, δ, hδ, rfl⟩ ⟨F', δ', hδ', rfl⟩
      refine ⟨baseSet ρ (F ∪ F') (min δ δ'), ⟨F ∪ F', min δ δ', lt_min hδ hδ', rfl⟩, fun t ht => ⟨?_, ?_⟩⟩
      · intro c hc
        exact lt_of_lt_of_le (ht c (Finset.mem_union_left _ hc)) (min_le_left _ _)
      · intro c hc
        exact lt_of_lt_of_le (ht c (Finset.mem_union_right _ hc)) (min_le_right _ _))
    (by
      rintro _ ⟨F, δ, hδ, rfl⟩ c hc
      simp [h.zero, hδ])
    (by
      rintro _ ⟨F, δ, hδ, rfl⟩
      refine ⟨baseSet ρ F (δ / 2), ⟨F, δ / 2, by positivity, rfl⟩, ?_⟩
      rintro _ ⟨t, ht, s, hs, rfl⟩ c hc
      have h1 := ht c hc
      have h2 := hs c hc
      calc ρ (c * (t + s)) = ρ (c * t + c * s) := by rw [mul_add]
        _ ≤ ρ (c * t) + ρ (c * s) := h.add_le _ _
        _ < δ := by linarith)
    (by
      rintro _ ⟨F, δ, hδ, rfl⟩
      refine ⟨baseSet ρ F δ, ⟨F, δ, hδ, rfl⟩, fun t ht c hc => ?_⟩
      have := ht c hc
      simpa [mul_neg, h.neg] using this)

/-- The topology with base `V(F,δ)` at `0`. -/
noncomputable def betaTop (h : IsPseudoNorm ρ K) : TopologicalSpace ℝ := (basis h).topology

theorem betaTop_isTopologicalAddGroup (h : IsPseudoNorm ρ K) : @IsTopologicalAddGroup ℝ (betaTop h) _ :=
  (basis h).isTopologicalAddGroup

theorem mem_nhds_zero_iff (h : IsPseudoNorm ρ K) {W : Set ℝ} :
    W ∈ @nhds ℝ (betaTop h) 0 ↔ ∃ (F : Finset ℝ) (δ : ℝ), 0 < δ ∧ baseSet ρ F δ ⊆ W := by
  unfold betaTop
  rw [(basis h).nhds_zero_hasBasis.mem_iff]
  constructor
  · rintro ⟨V, ⟨F, δ, hδ, rfl⟩, hV⟩
    exact ⟨F, δ, hδ, hV⟩
  · rintro ⟨F, δ, hδ, hV⟩
    exact ⟨_, ⟨F, δ, hδ, rfl⟩, hV⟩

/-- Every base set contains a Euclidean interval around `0`. -/
theorem baseSet_mem_nhds (h : IsPseudoNorm ρ K) (F : Finset ℝ) {δ : ℝ} (hδ : 0 < δ) :
    baseSet ρ F δ ∈ @nhds ℝ eT 0 := by
  set M : ℝ := ∑ c ∈ F, |c| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun c _ => abs_nonneg c)
  have hKM : 0 < K * (M + 1) := mul_pos h.K_pos (by linarith)
  set r : ℝ := δ / (K * (M + 1)) with hr
  have hrpos : 0 < r := div_pos hδ hKM
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) hrpos) (fun t ht c hc => ?_)
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  have hc' : |c| ≤ M := Finset.single_le_sum (f := fun c => |c|) (fun c _ => abs_nonneg c) hc
  calc ρ (c * t) ≤ K * |c * t| := h.le_lin _
    _ = K * |c| * |t| := by rw [abs_mul]; ring
    _ ≤ K * (M + 1) * |t| := by
        have : |c| ≤ M + 1 := by linarith
        have := mul_le_mul_of_nonneg_left this h.K_pos.le
        exact mul_le_mul_of_nonneg_right this (abs_nonneg t)
    _ < K * (M + 1) * r := mul_lt_mul_of_pos_left ht hKM
    _ = δ := by rw [hr]; have hK : K ≠ 0 := h.K_pos.ne'; field_simp

/-- `betaTop` is inside the Euclidean topology. -/
theorem eT_le_betaTop (h : IsPseudoNorm ρ K) : eT ≤ betaTop h := by
  refine le_of_nhds_le_nhds (fun x => ?_)
  unfold betaTop
  rw [((basis h).nhds_hasBasis x).ge_iff]
  rintro V ⟨F, δ, hδ, rfl⟩
  have h0 := baseSet_mem_nhds h F hδ
  rw [← map_add_left_nhds_zero x]
  exact Filter.image_mem_map h0

theorem betaTop_t2 (h : IsPseudoNorm ρ K) : @T2Space ℝ (betaTop h) := by
  letI : TopologicalSpace ℝ := betaTop h
  haveI : IsTopologicalAddGroup ℝ := betaTop_isTopologicalAddGroup h
  refine IsTopologicalAddGroup.t2Space_of_zero_sep (fun x hx => ?_)
  refine ⟨baseSet ρ {1} (ρ x), (mem_nhds_zero_iff h).2 ⟨{1}, ρ x, h.pos x hx, subset_rfl⟩, ?_⟩
  intro hxU
  have := hxU 1 (Finset.mem_singleton_self 1)
  simp at this

theorem betaTop_constSMul (h : IsPseudoNorm ρ K) : @ContinuousConstSMul ℝ ℝ (betaTop h) _ := by
  letI : TopologicalSpace ℝ := betaTop h
  haveI : IsTopologicalAddGroup ℝ := betaTop_isTopologicalAddGroup h
  refine ⟨fun a => ?_⟩
  have key : ContinuousAt (AddMonoidHom.mulLeft a : ℝ →+ ℝ) 0 := by
    rw [ContinuousAt, map_zero]
    intro W hW
    obtain ⟨F, δ, hδ, hFW⟩ := (mem_nhds_zero_iff h).1 hW
    refine (mem_nhds_zero_iff h).2 ⟨F.image (fun c => c * a), δ, hδ, fun t ht => ?_⟩
    show (AddMonoidHom.mulLeft a : ℝ →+ ℝ) t ∈ W
    apply hFW
    intro c hc
    have := ht (c * a) (Finset.mem_image_of_mem _ hc)
    simpa [smul_eq_mul, mul_assoc] using this
  have := continuous_of_continuousAt_zero (AddMonoidHom.mulLeft a : ℝ →+ ℝ) key
  simpa [smul_eq_mul] using this

/-- **Hypothesis of part (b)**: every basic neighbourhood contains a half-integer. -/
def HalfInt (ρ : ℝ → ℝ) : Prop :=
  ∀ (F : Finset ℝ) (δ : ℝ), 0 < δ → ∃ k : ℤ, ∀ c ∈ F, ρ (c * ((k : ℝ) + 1 / 2)) < δ

theorem half_in_nhds (h : IsPseudoNorm ρ K) (hH : HalfInt ρ) :
    ∀ V ∈ @nhds ℝ (betaTop h) 0, ∃ k : ℤ, ((k : ℝ) + 1 / 2) ∈ V := by
  intro V hV
  obtain ⟨F, δ, hδ, hFV⟩ := (mem_nhds_zero_iff h).1 hV
  obtain ⟨k, hk⟩ := hH F δ hδ
  exact ⟨k, hFV hk⟩

/-- The character `t ↦ bt + ℤ`. -/
noncomputable def chi (b : ℝ) (t : ℝ) : AddCircle (1 : ℝ) := ((b * t : ℝ) : AddCircle (1 : ℝ))

theorem chi_one_not_continuous (h : IsPseudoNorm ρ K) (hH : HalfInt ρ) :
    ¬ @Continuous ℝ (AddCircle (1 : ℝ)) (betaTop h) _ (chi 1) := by
  intro hc
  have hU : Metric.ball (0 : AddCircle (1 : ℝ)) (1 / 4) ∈ 𝓝 (chi 1 0) := by
    have : chi 1 0 = 0 := by simp [chi]
    rw [this]; exact Metric.ball_mem_nhds _ (by norm_num)
  have hcont : @ContinuousAt ℝ (AddCircle (1 : ℝ)) (betaTop h) _ (chi 1) 0 :=
    @Continuous.continuousAt ℝ (AddCircle (1 : ℝ)) (betaTop h) _ (chi 1) 0 hc
  have hpre := @ContinuousAt.preimage_mem_nhds ℝ (AddCircle (1 : ℝ)) (betaTop h) _ (chi 1) 0 _ hcont hU
  obtain ⟨k, hk⟩ := half_in_nhds h hH _ hpre
  have hk' : ‖(((k : ℝ) + 1 / 2 : ℝ) : AddCircle (1 : ℝ))‖ < 1 / 4 := by
    have := hk
    simpa [chi, Metric.mem_ball, dist_zero_right] using this
  have h0 : (((k : ℝ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    have : (k : ℝ) = k • (1 : ℝ) := by simp
    rw [this, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
  have h1 : (((k : ℝ) + 1 / 2 : ℝ) : AddCircle (1 : ℝ)) = (((1 : ℝ) / 2 : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_add, h0, zero_add]
  rw [h1, AddCircle.norm_half_period_eq] at hk'
  norm_num at hk'

theorem chi_not_continuous (h : IsPseudoNorm ρ K) (hH : HalfInt ρ) {b : ℝ} (hb : b ≠ 0) :
    ¬ @Continuous ℝ (AddCircle (1 : ℝ)) (betaTop h) _ (chi b) := by
  intro hc
  apply chi_one_not_continuous h hH
  have hsm := betaTop_constSMul h
  have hd := @continuous_const_smul ℝ ℝ (betaTop h) _ hsm b⁻¹
  have : (chi 1) = (chi b) ∘ (fun t : ℝ => b⁻¹ • t) := by
    funext t; simp [chi, smul_eq_mul, hb]
  rw [this]
  exact @Continuous.comp ℝ ℝ (AddCircle (1 : ℝ)) (betaTop h) (betaTop h) _ _ _ hc hd

/-- `ℤ` is dense in `(ℝ, betaTop)`. -/
theorem int_dense (h : IsPseudoNorm ρ K) (hH : HalfInt ρ) (x : ℝ) :
    x ∈ @closure ℝ (betaTop h) (Set.range (fun k : ℤ => (k : ℝ))) := by
  have hg := betaTop_isTopologicalAddGroup h
  have hsm := betaTop_constSMul h
  have hι : @Continuous ℝ ℝ eT (betaTop h) (LinearMap.id : ℝ →ₗ[ℝ] ℝ) :=
    continuous_id_iff_le.2 (eT_le_betaTop h)
  have := @PVG.Gen.range_subset_closure ℝ _ _ (betaTop h) hg hsm (LinearMap.id) hι
    (fun V hV => half_in_nhds h hH V hV) x
  simpa using this

end Beta
end PVG
