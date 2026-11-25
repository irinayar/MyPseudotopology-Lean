import Mathlib
import LeanCheck.PVGCyclicCore
import LeanCheck.PVGBohr

/-!
# PVG: the Bohr trace on one cyclic subgroup (Lean check)

Scope. A group topology `γ` on `ℝ` that is coarser than the Euclidean topology and whose trace on one cyclic subgroup `aℤ`,
`a ≠ 0`, is coarser than the Bohr trace, is coarser than the Bohr topology. Consequently a group topology between the Bohr and the
Euclidean topology that induces the Bohr topology on some `aℤ`, `a ≠ 0`, is the Bohr topology. Local quasi-convexity is not used.
This replaces the conditional statement `cyclic_core` (countability of the set of such `a` for locally quasi-convex `γ`).
The argument is an instance of the Merson lemma on subgroups and quotients.

"`γ` is coarser than the Euclidean topology" is stated as: every `γ`-neighbourhood of `0` contains an interval `(-δ, δ)` (for a
group topology this is equivalent to the comparison of the topologies). In Mathlib's order `t₁ ≤ t₂` means that `t₁` is finer, so
`bohrTop ≤ γ` says that `γ` is coarser than the Bohr topology.

* `cyclicTrace_le` : trace on `aℤ` coarser than the Bohr trace and `γ` coarser than Euclid give `bohrTop ≤ γ`;
* `cyclicTrace_eq` : if moreover `γ` is finer than the Bohr topology and the two traces coincide, then `γ = bohrTop`;
* `cyclicTrace_zero` : for a `γ ≠ bohrTop` between the two bounds, `γ` and the Bohr topology induce the same topology on `aℤ` only
  for `a = 0`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set

namespace PVG
namespace Lac
open Q95

/-- A Bohr neighbourhood of `0` contains `-t` for all Euclidean-small `t`. -/
lemma small_neg_mem_bohr {B : Set ℝ} (hB : B ∈ @nhds ℝ bohrTop 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → -t ∈ B := by
  have hE : B ∈ 𝓝 (0 : ℝ) := bohr_coarser_euclid 0 hB
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hE
  refine ⟨δ, hδ, fun t ht => hball ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using ht

/-- `{x : ‖x / a‖ < r}` is a Bohr neighbourhood of `0`. -/
lemma dint_mem_nhds_bohr (b : ℝ) {r : ℝ} (hr : 0 < r) : {x : ℝ | dint (b * x) < r} ∈ @nhds ℝ bohrTop 0 := by
  have h1 : Tendsto e (@nhds ℝ bohrTop 0) (𝓝 (e 0)) := by
    rw [nhds_bohr]; exact tendsto_comap
  have hc : Tendsto (fun x : ℝ => ‖e x b‖) (@nhds ℝ bohrTop 0) (𝓝 ‖e 0 b‖) :=
    ((continuous_norm.comp (continuous_eval b)).tendsto (e 0)).comp h1
  have h2 : ‖e 0 b‖ = 0 := by simp
  rw [h2] at hc
  exact hc (Iio_mem_nhds hr)

/-- Trace on one cyclic subgroup: a group topology coarser than the Euclidean one whose trace on `aℤ` is coarser than the Bohr
trace is coarser than the Bohr topology. -/
theorem cyclicTrace_le (γ : TopologicalSpace ℝ) (hγ : @IsTopologicalAddGroup ℝ γ _)
    (heuc : ∀ W ∈ @nhds ℝ γ 0, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → t ∈ W) (a : ℝ) (ha : a ≠ 0)
    (htr : ∀ V ∈ @nhds ℝ γ 0, ∃ B ∈ @nhds ℝ bohrTop 0, B ∩ Zmul a ⊆ V) :
    bohrTop ≤ γ := by
  have hB : @IsTopologicalAddGroup ℝ bohrTop _ := bohr_isTopologicalAddGroup
  -- the inclusion of neighbourhood filters at `0`
  have h0 : @nhds ℝ bohrTop 0 ≤ @nhds ℝ γ 0 := by
    intro W hW
    obtain ⟨V, hV, hVW⟩ : ∃ V ∈ @nhds ℝ γ 0, ∀ u ∈ V, ∀ v ∈ V, u + v ∈ W := by
      letI : TopologicalSpace ℝ := γ
      haveI : IsTopologicalAddGroup ℝ := hγ
      obtain ⟨V, hVo, h0V, hVV⟩ := exists_open_nhds_zero_add_subset hW
      exact ⟨V, hVo.mem_nhds h0V, fun u hu v hv => hVV (Set.add_mem_add hu hv)⟩
    obtain ⟨B, hB0, hBV⟩ := htr V hV
    obtain ⟨B1, hB1, hB1B⟩ : ∃ B1 ∈ @nhds ℝ bohrTop 0, ∀ u ∈ B1, ∀ v ∈ B1, u + v ∈ B := by
      letI : TopologicalSpace ℝ := bohrTop
      haveI : IsTopologicalAddGroup ℝ := hB
      obtain ⟨B1, hBo, h0B, hBB⟩ := exists_open_nhds_zero_add_subset hB0
      exact ⟨B1, hBo.mem_nhds h0B, fun u hu v hv => hBB (Set.add_mem_add hu hv)⟩
    -- Euclidean smallness: inside `V`, and the negative inside `B1`
    obtain ⟨δ1, hδ1, hV1⟩ := heuc V hV
    obtain ⟨δ2, hδ2, hneg⟩ := small_neg_mem_bohr hB1
    obtain ⟨δ, hδ, hδ1', hδ2'⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ1 ∧ δ ≤ δ2 :=
      ⟨min δ1 δ2, lt_min hδ1 hδ2, min_le_left _ _, min_le_right _ _⟩
    -- the Bohr neighbourhood controlling the distance to `aℤ`
    have ha' : 0 < |a| := abs_pos.2 ha
    have hchar := dint_mem_nhds_bohr a⁻¹ (div_pos hδ ha')
    refine Filter.mem_of_superset (Filter.inter_mem hB1 hchar) ?_
    rintro x ⟨hx1, hx2⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, n = round (a⁻¹ * x) := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = x - n * a := ⟨_, rfl⟩
    have htabs : |t| < δ := by
      have h1 : t = a * (a⁻¹ * x - n) := by
        rw [ht, mul_sub, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, mul_comm a (n : ℝ)]
      have h2 : |a⁻¹ * x - n| < δ / |a| := by
        have h3 : dint (a⁻¹ * x) < δ / |a| := hx2
        rwa [dint_eq, ← hn] at h3
      rw [h1, abs_mul]
      calc |a| * |a⁻¹ * x - n| < |a| * (δ / |a|) := mul_lt_mul_of_pos_left h2 ha'
        _ = δ := by field_simp
    have hnaB : (n : ℝ) * a ∈ B := by
      have := hB1B x hx1 (-t) (hneg t (lt_of_lt_of_le htabs hδ2'))
      have hxt : x + -t = (n : ℝ) * a := by rw [ht]; ring
      rwa [hxt] at this
    have hnaV : (n : ℝ) * a ∈ V := hBV ⟨hnaB, ⟨n, rfl⟩⟩
    have hfin := hVW _ hnaV t (hV1 t (lt_of_lt_of_le htabs hδ1'))
    have hxt : (n : ℝ) * a + t = x := by rw [ht]; ring
    rwa [hxt] at hfin
  -- translate to every point
  refine le_of_nhds_le_nhds fun x => ?_
  have e1 : @nhds ℝ bohrTop x = Filter.map (fun y => x + y) (@nhds ℝ bohrTop 0) := by
    letI : TopologicalSpace ℝ := bohrTop
    haveI : IsTopologicalAddGroup ℝ := hB
    exact (map_add_left_nhds_zero x).symm
  have e2 : @nhds ℝ γ x = Filter.map (fun y => x + y) (@nhds ℝ γ 0) := by
    letI : TopologicalSpace ℝ := γ
    haveI : IsTopologicalAddGroup ℝ := hγ
    exact (map_add_left_nhds_zero x).symm
  rw [e1, e2]
  exact Filter.map_mono h0

/-- A group topology between the Bohr and the Euclidean topology that induces the Bohr topology on one `aℤ`, `a ≠ 0`, is the
Bohr topology. -/
theorem cyclicTrace_eq (γ : TopologicalSpace ℝ) (hγ : @IsTopologicalAddGroup ℝ γ _)
    (hfine : γ ≤ bohrTop) (heuc : ∀ W ∈ @nhds ℝ γ 0, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → t ∈ W)
    (a : ℝ) (ha : a ≠ 0)
    (hind : TopologicalSpace.induced (Subtype.val : Zmul a → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Zmul a → ℝ) bohrTop) :
    γ = bohrTop := by
  refine le_antisymm hfine (cyclicTrace_le γ hγ heuc a ha fun V hV => ?_)
  obtain ⟨z0, hz0⟩ : ∃ z0 : Zmul a, z0 = ⟨0, zero_mem_Zmul a⟩ := ⟨_, rfl⟩
  have hz : (z0 : ℝ) = 0 := by rw [hz0]
  have h1 : (Subtype.val : Zmul a → ℝ) ⁻¹' V ∈ @nhds (Zmul a) (TopologicalSpace.induced Subtype.val γ) z0 := by
    rw [@nhds_induced ℝ (Zmul a) γ Subtype.val z0, hz]
    exact Filter.preimage_mem_comap hV
  rw [hind, @nhds_induced ℝ (Zmul a) bohrTop Subtype.val z0, hz] at h1
  obtain ⟨B, hB0, hBV⟩ := Filter.mem_comap.1 h1
  refine ⟨B, hB0, ?_⟩
  rintro y ⟨hyB, hyZ⟩
  exact hBV (show (⟨y, hyZ⟩ : Zmul a) ∈ (Subtype.val : Zmul a → ℝ) ⁻¹' B from hyB)

/-- For a group topology strictly between the bounds, the only `a` with the Bohr trace on `aℤ` is `a = 0`. -/
theorem cyclicTrace_zero (γ : TopologicalSpace ℝ) (hγ : @IsTopologicalAddGroup ℝ γ _)
    (hfine : γ ≤ bohrTop) (heuc : ∀ W ∈ @nhds ℝ γ 0, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → t ∈ W)
    (hne : γ ≠ bohrTop) (a : ℝ)
    (hind : TopologicalSpace.induced (Subtype.val : Zmul a → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Zmul a → ℝ) bohrTop) :
    a = 0 := by
  by_contra ha
  exact hne (cyclicTrace_eq γ hγ hfine heuc a ha hind)

end Lac
end PVG
