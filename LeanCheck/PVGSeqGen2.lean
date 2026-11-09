import Mathlib
import LeanCheck.PVGSeqGen

/-!
# PVG: convergent sequences for group topologies inside the Euclidean one (Lean check)

Scope. Parts (b) and (c) of Proposition `prop:betaseq` of PVG_v21, in the abstract form of `PVGSeqGen`: `X` is a real vector space with a
Hausdorff group topology in which every fixed dilation is continuous, and `ι : ℝ →ₗ[ℝ] X` is a Euclidean-continuous linear injection (for
`X = (ℝ, β)` and `ι = id` the hypotheses say that `β` is a Hausdorff group topology inside the Euclidean topology with continuous
dilations).

* `seq_conv_euclid` (part (b)): if `ι(x_k) → ι(a)` in `X` then `x_k → a` in `ℝ`.
* `isEmbedding_of_sequential` (part (c)): if the subspace `ι(ℝ)` of `X` is a sequential space, then `ι` is a topological embedding
  (for `X = (ℝ, β)`, `ι = id`: `β` equals the Euclidean topology).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Gen

/-- **Part (b).** -/
theorem seq_conv_euclid
    {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [ContinuousConstSMul ℝ X]
    (ι : ℝ →ₗ[ℝ] X) (hι : Continuous ι) (hinj : Function.Injective ι)
    (x : ℕ → ℝ) (a : ℝ) (h : Tendsto (fun k => ι (x k)) atTop (𝓝 (ι a))) :
    Tendsto x atTop (𝓝 a) := by
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  -- the null sequence `w k = x (ns k) - a`
  set w : ℕ → ℝ := fun k => x (ns k) - a with hw
  have hv : Tendsto (fun k => ι (x (ns k))) atTop (𝓝 (ι a)) := h.comp hns
  have hw0 : Tendsto (fun k => ι (w k)) atTop (𝓝 0) := by
    have := hv.sub_const (ι a)
    simpa [hw, map_sub] using this
  by_cases hb : ∃ R : ℝ, ∃ᶠ k in atTop, |w k| ≤ R
  · obtain ⟨R, hR⟩ := hb
    obtain ⟨c, -, φ, hφ, hc⟩ := tendsto_subseq_of_frequently_bounded
      (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := R))
      (hR.mono fun k hk => by simpa [Metric.mem_closedBall, Real.dist_eq] using hk)
    have h1 : Tendsto (fun n => ι (w (φ n))) atTop (𝓝 (ι c)) := (hι.tendsto c).comp hc
    have h2 : Tendsto (fun n => ι (w (φ n))) atTop (𝓝 0) := hw0.comp hφ.tendsto_atTop
    have h3 : ι c = 0 := tendsto_nhds_unique h1 h2
    have hc0 : c = 0 := hinj (by rw [h3, map_zero])
    refine ⟨φ, ?_⟩
    have h4 : Tendsto (fun n => w (φ n) + a) atTop (𝓝 (c + a)) := hc.add_const a
    rw [hc0, zero_add] at h4
    simpa [hw] using h4
  · exfalso
    push Not at hb
    have hlarge : Tendsto (fun k => |w k|) atTop atTop := by
      refine Filter.tendsto_atTop.2 (fun R => ?_)
      exact (hb R).mono fun k hk => hk.le
    exact no_unbounded_null_seq ι hι hinj w hlarge hw0

/-- **Part (c).** If the subspace `ι(ℝ)` of `X` is sequential, then `ι` is a topological embedding. -/
theorem isEmbedding_of_sequential
    {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [ContinuousConstSMul ℝ X]
    (ι : ℝ →ₗ[ℝ] X) (hι : Continuous ι) (hinj : Function.Injective ι)
    [SequentialSpace (Set.range ι)] : Topology.IsEmbedding ι := by
  set ι' : ℝ → Set.range ι := Set.rangeFactorization ι with hι'
  have hc' : Continuous ι' := hι.rangeFactorization
  have hinj' : Function.Injective ι' := fun a b hab => hinj (by simpa [hι'] using congrArg Subtype.val hab)
  have hcl : IsClosedMap ι' := by
    intro F hF
    rw [← isSeqClosed_iff_isClosed]
    intro y z hy hyz
    have hy' : ∀ k, ∃ a ∈ F, ι' a = y k := fun k => hy k
    choose a haF ha using hy'
    obtain ⟨b, hb⟩ : ∃ b : ℝ, ι' b = z := by
      obtain ⟨_, ⟨b, rfl⟩⟩ := z
      exact ⟨b, rfl⟩
    have h1 : Tendsto (fun k => ι (a k)) atTop (𝓝 (ι b)) := by
      have := (continuous_subtype_val.tendsto z).comp hyz
      have e1 : (fun k => ι (a k)) = (fun k => (y k : X)) := by
        funext k; simpa [hι'] using congrArg Subtype.val (ha k)
      have e2 : (z : X) = ι b := by simpa [hι'] using (congrArg Subtype.val hb).symm
      rw [e1, ← e2]; exact this
    have h2 := seq_conv_euclid ι hι hinj a b h1
    have hbF : b ∈ F := hF.mem_of_tendsto h2 (Filter.Eventually.of_forall haF)
    exact ⟨b, hbF, hb⟩
  have hce : Topology.IsClosedEmbedding ι' := Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hc' hinj' hcl
  exact Topology.IsEmbedding.subtypeVal.comp hce.isEmbedding

end Gen
end PVG
