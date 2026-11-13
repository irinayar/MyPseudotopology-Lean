import Mathlib
import LeanCheck.PVGBohr

/-!
# PVG: a Euclidean-dense set cannot carry the Bohr trace (Lean check)

Scope. Proposition 8.92 of `PVG_v43` (Part II). Let `γ` be a group topology on `ℝ` that is coarser than the Euclidean topology, and let
`D ⊆ ℝ` be Euclidean-dense with `0 ∈ D`. Suppose that the topology induced by `γ` on `D` is contained in the one induced by the Bohr
topology (every `γ|_D`-open set is `bohr|_D`-open). Then `γ` is contained in the Bohr topology.

Conventions. In Mathlib's order on topologies `s ≤ t` means that `s` is *finer*; "`γ` is contained in the Bohr topology" is
`bohrTop ≤ γ`, and the hypothesis on the traces reads `induced val bohrTop ≤ induced val γ`. Since a local variable of type
`TopologicalSpace ℝ` is used by Lean as the topology of `ℝ`, the two properties of the Euclidean topology that are used are stated
concretely and no Euclidean `Dense` or `𝓝` occurs in a statement with `γ` in scope:

* `hE` : every `γ`-neighbourhood of `0` contains an open interval around `0` (that is, `γ` is coarser than the Euclidean topology at `0`);
* `hDd` : `D` is Euclidean-dense (`∀ z δ, 0 < δ → ∃ q ∈ D, |z - q| < δ`).

* `denseTrace_core` : every `γ`-neighbourhood of `0` is a Bohr neighbourhood of `0`;
* `denseTrace` : `bohrTop ≤ γ` for a group topology `γ`.

Note. The hypothesis `0 ∈ D` is used in the proof (the neighbourhood `V₁ ∩ D` of `0` for the trace topology); it was missing in the
statement of Proposition 8.92 in `PVG_v43` and has to be added. A dense subgroup such as `ℚ` contains `0`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set

namespace PVG
namespace Lac
open Q95

/-- A Bohr neighbourhood of a point contains a Euclidean interval around it (from `bohr_coarser_euclid`). -/
lemma bohr_nhds_ball {s : Set ℝ} {z : ℝ} (h : s ∈ @nhds ℝ bohrTop z) : ∃ r > 0, ∀ w : ℝ, |w - z| < r → w ∈ s := by
  have h' : s ∈ 𝓝 z := bohr_coarser_euclid z h
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 h'
  exact ⟨r, hr, fun w hw => hsub (by rwa [Metric.mem_ball, Real.dist_eq])⟩

/-- Neighbourhoods of a point are the translates of the neighbourhoods of `0` in a group topology. -/
lemma nhds_eq_map_zero (t : TopologicalSpace ℝ) (ht : @IsTopologicalAddGroup ℝ t _) (x : ℝ) :
    @nhds ℝ t x = Filter.map (fun y => x + y) (@nhds ℝ t 0) := by
  letI : TopologicalSpace ℝ := t
  haveI := ht
  exact (map_add_left_nhds_zero x).symm

/-- Core of Proposition 8.92: every `γ`-neighbourhood of `0` is a Bohr neighbourhood of `0`. -/
theorem denseTrace_core (γ : TopologicalSpace ℝ)
    (hadd : ∀ V ∈ @nhds ℝ γ 0, ∃ V1 ∈ @nhds ℝ γ 0, ∀ x ∈ V1, ∀ y ∈ V1, x + y ∈ V)
    (hE : ∀ V ∈ @nhds ℝ γ 0, ∃ δ > 0, ∀ w : ℝ, |w| < δ → w ∈ V)
    (D : Set ℝ) (hD0 : (0 : ℝ) ∈ D) (hDd : ∀ z : ℝ, ∀ δ : ℝ, 0 < δ → ∃ q ∈ D, |z - q| < δ)
    (hDt : TopologicalSpace.induced (Subtype.val : D → ℝ) bohrTop ≤
      TopologicalSpace.induced (Subtype.val : D → ℝ) γ)
    (V : Set ℝ) (hV : V ∈ @nhds ℝ γ 0) : V ∈ @nhds ℝ bohrTop 0 := by
  obtain ⟨V1, hV1, hV1V⟩ := hadd V hV
  obtain ⟨δ, hδ, hball⟩ := hE V1 hV1
  -- the trace of `V1` on `D` is a neighbourhood of `0` for the Bohr trace
  set z0 : D := ⟨0, hD0⟩ with hz0
  have h1 : (Subtype.val : D → ℝ) ⁻¹' V1 ∈
      @nhds D (TopologicalSpace.induced Subtype.val γ) z0 := by
    rw [@nhds_induced ℝ D γ Subtype.val z0]
    exact Filter.preimage_mem_comap hV1
  have h2 : (Subtype.val : D → ℝ) ⁻¹' V1 ∈
      @nhds D (TopologicalSpace.induced Subtype.val bohrTop) z0 := _root_.nhds_mono hDt h1
  rw [@nhds_induced ℝ D bohrTop Subtype.val z0] at h2
  obtain ⟨B, hB, hBV1⟩ := Filter.mem_comap.1 h2
  -- the Bohr interior of `B`
  have hB' : (@interior ℝ bohrTop B) ∈ @nhds ℝ bohrTop 0 := by
    letI : TopologicalSpace ℝ := bohrTop
    exact interior_mem_nhds.2 hB
  have hB'open : @IsOpen ℝ bohrTop ((@interior ℝ bohrTop B)) := @isOpen_interior ℝ bohrTop B
  have hsub : (@interior ℝ bohrTop B) ⊆ V := by
    intro z hz
    have hzB' : (@interior ℝ bohrTop B) ∈ @nhds ℝ bohrTop z := @IsOpen.mem_nhds ℝ bohrTop z _ hB'open hz
    obtain ⟨r, hr, hrsub⟩ := bohr_nhds_ball hzB'
    obtain ⟨q, hqD, hq⟩ := hDd z (min r δ) (lt_min hr hδ)
    have hqB' : q ∈ (@interior ℝ bohrTop B) := hrsub q (by
      rw [abs_sub_comm]; exact lt_of_lt_of_le hq (min_le_left _ _))
    have hqB : q ∈ B := by
      letI : TopologicalSpace ℝ := bohrTop
      exact interior_subset hqB'
    have hq1 : q ∈ V1 := hBV1 (show (⟨q, hqD⟩ : D) ∈ (Subtype.val : D → ℝ) ⁻¹' B from hqB)
    have hzq : z - q ∈ V1 := hball (z - q) (lt_of_lt_of_le hq (min_le_right _ _))
    have := hV1V q hq1 (z - q) hzq
    simpa using this
  exact Filter.mem_of_superset hB' hsub

/-- Proposition 8.92: if `γ` is a group topology coarser than the Euclidean topology and its trace on a dense set `D ∋ 0` is coarser
than the Bohr trace, then `γ` is coarser than the Bohr topology. -/
theorem denseTrace (γ : TopologicalSpace ℝ) (hγ : @IsTopologicalAddGroup ℝ γ _)
    (hE : ∀ V ∈ @nhds ℝ γ 0, ∃ δ > 0, ∀ w : ℝ, |w| < δ → w ∈ V)
    (D : Set ℝ) (hD0 : (0 : ℝ) ∈ D) (hDd : ∀ z : ℝ, ∀ δ : ℝ, 0 < δ → ∃ q ∈ D, |z - q| < δ)
    (hDt : TopologicalSpace.induced (Subtype.val : D → ℝ) bohrTop ≤
      TopologicalSpace.induced (Subtype.val : D → ℝ) γ) :
    bohrTop ≤ γ := by
  have hadd : ∀ V ∈ @nhds ℝ γ 0, ∃ V1 ∈ @nhds ℝ γ 0, ∀ x ∈ V1, ∀ y ∈ V1, x + y ∈ V := by
    intro V hV
    letI : TopologicalSpace ℝ := γ
    haveI := hγ
    have hcont : Tendsto (fun p : ℝ × ℝ => p.1 + p.2) (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 (0 + 0)) :=
      continuous_add.tendsto ((0 : ℝ), (0 : ℝ))
    rw [add_zero] at hcont
    have hpre : (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' V ∈ 𝓝 ((0 : ℝ), (0 : ℝ)) := hcont hV
    rw [nhds_prod_eq, Filter.mem_prod_iff] at hpre
    obtain ⟨t1, ht1, t2, ht2, hsub⟩ := hpre
    refine ⟨t1 ∩ t2, Filter.inter_mem ht1 ht2, fun x hx y hy => ?_⟩
    exact hsub (show (x, y) ∈ t1 ×ˢ t2 from ⟨hx.1, hy.2⟩)
  -- every `γ`-open set is Bohr-open
  intro s hs
  rw [@isOpen_iff_mem_nhds ℝ bohrTop]
  intro x hx
  have hsγ : s ∈ @nhds ℝ γ x := (@isOpen_iff_mem_nhds ℝ γ).1 hs x hx
  rw [nhds_eq_map_zero γ hγ x, Filter.mem_map] at hsγ
  have h0 : (fun y => x + y) ⁻¹' s ∈ @nhds ℝ bohrTop 0 :=
    denseTrace_core γ hadd hE D hD0 hDd hDt _ hsγ
  rw [nhds_eq_map_zero bohrTop bohr_isTopologicalAddGroup x, Filter.mem_map]
  exact h0

end Lac
end PVG
