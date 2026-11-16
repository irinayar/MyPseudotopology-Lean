import Mathlib
import LeanCheck.PVGNTrace

/-!
# PVG: the pseudo-norm criterion for condition (N), sufficiency (Lean check)

Scope. Proposition (pseudo-norm criterion) of `PVG_v47`, the direction "criterion ⟹ (N)". Let `Φ : ℝ → ℝ` be symmetric and subadditive (nonnegativity is not needed) with
`Φ 0 = 0`, and assume

* (a) `Φ x → 0` as `x → 0` in the Euclidean topology;
* (b) for every `J ∈ I_S` and `ε > 0` there is an open set `Y` of `K = Hom(ℝ,𝕋)` with `e 0 ∈ Y` and `Φ z < ε` for all `z ∈ J` with `e z ∈ Y`
  (`Φ` tends to `0` along every Bohr-null net inside a member of `I_S`);
* (c) there is `θ > 0` such that every open `Y ∋ e 0` contains some `e x` with `Φ x ≥ θ` (`Φ` does not tend to `0` along some Bohr-null net).

Then condition (N) holds: `ConditionN` below is the statement of `N_of_group` (a group topology `γ` that is finer than `τ_B`, not equal to it, contained in `τ_E`,
with the Bohr trace on every member of `I_S`). The topology is `γ = τ_B ⊓ τ_Φ` (join of the topologies as families of open sets; `⊓` in Mathlib's order), where `τ_Φ` is
the group topology with base `{x | Φ x < ε}`, built with `AddGroupFilterBasis`. The converse (a witness gives a continuous invariant pseudometric by the Birkhoff–Kakutani
theorem) is not formalized.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter Topology
open scoped Classical

namespace PVG
namespace Lac
open Q95

/-- The statement of condition (N), in the form used by `N_of_group`. -/
def ConditionN : Prop :=
  ∃ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ ∧
    (∀ U : Set ℝ, @IsOpen ℝ bohrTop U → @IsOpen ℝ γ U) ∧
    (∃ U : Set ℝ, @IsOpen ℝ γ U ∧ ¬ @IsOpen ℝ bohrTop U) ∧
    (∀ U : Set ℝ, @IsOpen ℝ γ U → @IsOpen ℝ euclidTop U) ∧
    ∀ J ∈ IS, TopologicalSpace.induced (Subtype.val : J → ℝ) γ = TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop

section Norm

variable (Φ : ℝ → ℝ)

/-- The sets `{x | Φ x < ε}`, `ε > 0`, form a filter basis of a group topology (`Φ` symmetric, subadditive, `Φ 0 = 0`). -/
noncomputable def phiBasis (h0 : Φ 0 = 0) (hneg : ∀ x, Φ (-x) = Φ x) (hsub : ∀ x y, Φ (x + y) ≤ Φ x + Φ y) :
    AddGroupFilterBasis ℝ :=
  addGroupFilterBasisOfComm {s | ∃ ε : ℝ, 0 < ε ∧ s = {x | Φ x < ε}}
    ⟨{x | Φ x < 1}, 1, one_pos, rfl⟩
    (by
      rintro _ _ ⟨ε₁, h₁, rfl⟩ ⟨ε₂, h₂, rfl⟩
      refine ⟨{x | Φ x < min ε₁ ε₂}, ⟨min ε₁ ε₂, lt_min h₁ h₂, rfl⟩, ?_⟩
      intro x hx
      have hx' : Φ x < min ε₁ ε₂ := hx
      exact ⟨show Φ x < ε₁ from lt_of_lt_of_le hx' (min_le_left _ _), show Φ x < ε₂ from lt_of_lt_of_le hx' (min_le_right _ _)⟩)
    (by
      rintro _ ⟨ε, hε, rfl⟩
      simpa [h0] using hε)
    (by
      rintro _ ⟨ε, hε, rfl⟩
      refine ⟨{x | Φ x < ε / 2}, ⟨ε / 2, by positivity, rfl⟩, ?_⟩
      rintro _ ⟨x, hx, y, hy, rfl⟩
      have h1 : Φ x < ε / 2 := hx
      have h2 : Φ y < ε / 2 := hy
      have := hsub x y
      show Φ (x + y) < ε
      linarith)
    (by
      rintro _ ⟨ε, hε, rfl⟩
      refine ⟨{x | Φ x < ε}, ⟨ε, hε, rfl⟩, ?_⟩
      intro x hx
      show Φ (-x) < ε
      rw [hneg]; exact hx)

variable {Φ}

/-- The topology `τ_Φ`. -/
noncomputable def phiTop (h0 : Φ 0 = 0) (hneg : ∀ x, Φ (-x) = Φ x) (hsub : ∀ x y, Φ (x + y) ≤ Φ x + Φ y) :
    TopologicalSpace ℝ := (phiBasis Φ h0 hneg hsub).topology

theorem phiTop_isTopologicalAddGroup (h0 : Φ 0 = 0) (hneg : ∀ x, Φ (-x) = Φ x) (hsub : ∀ x y, Φ (x + y) ≤ Φ x + Φ y) :
    @IsTopologicalAddGroup ℝ (phiTop h0 hneg hsub) _ :=
  (phiBasis Φ h0 hneg hsub).isTopologicalAddGroup

/-- Neighbourhoods in `τ_Φ`: `V` is a neighbourhood of `x` iff it contains some `{y | Φ (y - x) < ε}`. -/
theorem mem_nhds_phiTop (h0 : Φ 0 = 0) (hneg : ∀ x, Φ (-x) = Φ x) (hsub : ∀ x y, Φ (x + y) ≤ Φ x + Φ y)
    {x : ℝ} {V : Set ℝ} :
    V ∈ @nhds ℝ (phiTop h0 hneg hsub) x ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, Φ (y - x) < ε → y ∈ V := by
  have hb := (phiBasis Φ h0 hneg hsub).nhds_hasBasis x
  unfold phiTop
  rw [hb.mem_iff]
  constructor
  · rintro ⟨s, ⟨ε, hε, rfl⟩, hsV⟩
    refine ⟨ε, hε, fun y hy => hsV ⟨y - x, hy, by ring⟩⟩
  · rintro ⟨ε, hε, h⟩
    refine ⟨{z | Φ z < ε}, ⟨ε, hε, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact h _ (by simpa using hz)

end Norm

lemma bohr_open_euclid {U : Set ℝ} (hU : @IsOpen ℝ bohrTop U) : @IsOpen ℝ euclidTop U := by
  show IsOpen U
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact bohr_coarser_euclid x (@IsOpen.mem_nhds ℝ bohrTop _ _ hU hx)

/-- **Sufficiency of the pseudo-norm criterion.** -/
theorem N_of_norm (Φ : ℝ → ℝ) (h0 : Φ 0 = 0) (hneg : ∀ x, Φ (-x) = Φ x)
    (hsub : ∀ x y, Φ (x + y) ≤ Φ x + Φ y)
    (ha : ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x| < δ → Φ x < ε)
    (hb : ∀ J ∈ IS, ∀ ε > 0, ∃ Y : Set K, IsOpen Y ∧ e 0 ∈ Y ∧ ∀ z ∈ J, e z ∈ Y → Φ z < ε)
    (hc : ∃ θ > 0, ∀ Y : Set K, IsOpen Y → e 0 ∈ Y → ∃ x : ℝ, e x ∈ Y ∧ θ ≤ Φ x) :
    ConditionN := by
  have hτg : @IsTopologicalAddGroup ℝ (phiTop h0 hneg hsub) _ := phiTop_isTopologicalAddGroup h0 hneg hsub
  have hmem : ∀ {x : ℝ} {V : Set ℝ}, V ∈ @nhds ℝ (phiTop h0 hneg hsub) x ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℝ, Φ (y - x) < ε → y ∈ V :=
    fun {x V} => mem_nhds_phiTop h0 hneg hsub (x := x) (V := V)
  refine ⟨bohrTop ⊓ phiTop h0 hneg hsub, isTopologicalAddGroup_inf bohr_isTopologicalAddGroup hτg, ?_, ?_, ?_, ?_⟩
  · intro U hU
    exact (inf_le_left : bohrTop ⊓ phiTop h0 hneg hsub ≤ bohrTop) U hU
  · obtain ⟨θ, hθ, hY⟩ := hc
    refine ⟨{x | Φ x < θ}, ?_, ?_⟩
    · have hU : @IsOpen ℝ (phiTop h0 hneg hsub) {x | Φ x < θ} := by
        rw [@isOpen_iff_mem_nhds ℝ (phiTop h0 hneg hsub) _]
        intro x hx
        rw [hmem]
        refine ⟨θ - Φ x, by have : Φ x < θ := hx; linarith, fun y hy => ?_⟩
        show Φ y < θ
        have := hsub (y - x) x
        simp only [sub_add_cancel] at this
        linarith
      exact (inf_le_right : bohrTop ⊓ phiTop h0 hneg hsub ≤ phiTop h0 hneg hsub) _ hU
    · intro hbo
      have h0mem : (0 : ℝ) ∈ {x | Φ x < θ} := by show Φ 0 < θ; rw [h0]; exact hθ
      have hnh : {x | Φ x < θ} ∈ @nhds ℝ bohrTop 0 := @IsOpen.mem_nhds ℝ bohrTop _ _ hbo h0mem
      rw [nhds_bohr] at hnh
      obtain ⟨O, hO, hOV⟩ := Filter.mem_comap.1 hnh
      obtain ⟨Y, hYO, hYopen, h0Y⟩ := mem_nhds_iff.1 hO
      obtain ⟨x, hxY, hxΦ⟩ := hY Y hYopen h0Y
      have : x ∈ {x | Φ x < θ} := hOV (hYO hxY)
      have hlt : Φ x < θ := this
      linarith
  · intro U hU
    show IsOpen U
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hnh : U ∈ @nhds ℝ (bohrTop ⊓ phiTop h0 hneg hsub) x :=
      @IsOpen.mem_nhds ℝ (bohrTop ⊓ phiTop h0 hneg hsub) _ _ hU hx
    rw [@nhds_inf ℝ bohrTop (phiTop h0 hneg hsub) x, Filter.mem_inf_iff] at hnh
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := hnh
    obtain ⟨ε, hε, hQε⟩ := hmem.1 hQ
    obtain ⟨δ, hδ, hδε⟩ := ha ε hε
    have hP' : P ∈ 𝓝 x := bohr_coarser_euclid x hP
    have hball : Metric.ball x δ ∈ 𝓝 x := Metric.ball_mem_nhds x hδ
    filter_upwards [hP', hball] with y hyP hyb
    rw [hPQ]
    refine ⟨hyP, hQε y ?_⟩
    apply hδε
    have := Metric.mem_ball.1 hyb
    rwa [Real.dist_eq] at this
  · intro J hJ
    apply le_antisymm
    · exact induced_mono (inf_le_left : bohrTop ⊓ phiTop h0 hneg hsub ≤ bohrTop)
    · refine le_of_nhds_le_nhds (fun x => ?_)
      rw [@nhds_induced ℝ J bohrTop Subtype.val x, @nhds_induced ℝ J (bohrTop ⊓ phiTop h0 hneg hsub) Subtype.val x]
      intro s hs
      obtain ⟨V, hV, hVs⟩ := Filter.mem_comap.1 hs
      rw [@nhds_inf ℝ bohrTop (phiTop h0 hneg hsub) x.1, Filter.mem_inf_iff] at hV
      obtain ⟨P, hP, Q, hQ, hPQ⟩ := hV
      obtain ⟨ε, hε, hQε⟩ := hmem.1 hQ
      have hJJ : J + (-1 : ℝ) • J ∈ IS := IS_isIdeal.add hJ (IS_isIdeal.smul (-1) hJ)
      obtain ⟨Y, hY, h0Y, hYε⟩ := hb _ hJJ ε hε
      have hshift : {y : ℝ | e y - e x.1 ∈ Y} ∈ @nhds ℝ bohrTop x.1 := by
        rw [nhds_bohr]
        refine Filter.mem_comap.2 ⟨{κ : K | κ - e x.1 ∈ Y}, ?_, fun y hy => hy⟩
        have hopen : IsOpen {κ : K | κ - e x.1 ∈ Y} := hY.preimage (continuous_id.sub continuous_const)
        refine hopen.mem_nhds ?_
        simpa [e_zero] using h0Y
      refine Filter.mem_comap.2 ⟨P ∩ {y : ℝ | e y - e x.1 ∈ Y}, Filter.inter_mem hP hshift, ?_⟩
      rintro ⟨y, hyJ⟩ ⟨hyP, hyY⟩
      apply hVs
      show y ∈ V
      rw [hPQ]
      refine ⟨hyP, hQε y ?_⟩
      have hyJJ : y - x.1 ∈ J + (-1 : ℝ) • J := ⟨y, hyJ, -x.1, ⟨x.1, x.2, by simp⟩, by ring⟩
      have : e (y - x.1) ∈ Y := by rw [e_sub]; exact hyY
      exact hYε _ hyJJ this

#print axioms N_of_norm

end Lac
end PVG
