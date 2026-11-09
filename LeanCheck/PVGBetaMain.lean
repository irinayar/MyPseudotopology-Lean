import Mathlib
import LeanCheck.PVGBetaRho
import LeanCheck.PVGBetaStage

/-!
# PVG: the existence theorem, from a measure with the stage property (Lean check)

Scope. Theorem `thm:betaexists` of PVG_v22, assembled from `PVGBetaTop`, `PVGBetaRho` and `PVGBetaDense`. The Cantor-type construction of the
measure (nested intervals around algebraically independent centers, with the finite families of witnesses of `PVGBetaStage`) is NOT
formalized; its output enters as the hypothesis `StageProperty μ`: for every `n ≥ 1` and every vector `c` of the box `[-n, n]ⁿ` there are an
integer `k` and a measurable set `G` with `μ(Gᶜ) ≤ n 2^{-n}` such that `‖c_i (k + 1/2) λ‖ < 1/n` for all `i ≤ n` and `λ ∈ G`.

* `halfInt_of_stages`: for a probability measure `μ` with the stage property, `HalfInt (rho μ)` (the proof of (b): pad a finite set of dilations to
  a vector of the box, apply `rho_le_of_good`);
* `exists_beta_of_stage_measure`: if `μ` is an atomless probability measure carried by `[1,2]` with the stage property, the topology
  `betaTop` of `rho μ` is a Hausdorff group topology inside the Euclidean topology with continuous dilations, every neighbourhood of `0`
  contains a half-integer, no character `t ↦ bt + ℤ` with `b ≠ 0` is continuous, and `ℤ` is dense.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open MeasureTheory Filter Topology

namespace PVG
namespace Beta

/-- The topology of the circle, named so that it is not captured by a variable topology on `ℝ`. -/
abbrev cT : TopologicalSpace (AddCircle (1 : ℝ)) := inferInstance

/-- The output of the construction: a measure with small phases on large sets, for every vector of the box. -/
def StageProperty (μ : Measure ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ n) →
    ∃ (k : ℤ) (G : Set ℝ), MeasurableSet G ∧ (μ Gᶜ).toReal ≤ n * (1 / 2 : ℝ) ^ n ∧
      ∀ l ∈ G, ∀ i : Fin n, ‖((c i * ((k : ℝ) + 1 / 2) * l : ℝ) : AddCircle (1 : ℝ))‖ < 1 / n

theorem halfInt_of_stages (μ : Measure ℝ) [IsProbabilityMeasure μ] (hst : StageProperty μ) :
    HalfInt (rho μ) := by
  classical
  intro F δ hδ
  set M : ℝ := ∑ c ∈ F, |c| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun c _ => abs_nonneg c)
  -- a large `n`
  have h1 : Tendsto (fun n : ℕ => 2 * Real.pi / (n : ℝ) + n * (1 / 2 : ℝ) ^ n) atTop (𝓝 (0 + 0)) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi)).add
      (tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num))
  rw [add_zero] at h1
  have hev : ∀ᶠ n : ℕ in atTop, 2 * Real.pi / (n : ℝ) + n * (1 / 2 : ℝ) ^ n < δ :=
    h1.eventually (gt_mem_nhds hδ)
  have hall : ∀ᶠ n : ℕ in atTop, (2 * Real.pi / (n : ℝ) + n * (1 / 2 : ℝ) ^ n < δ) ∧ 1 ≤ n ∧
      F.card ≤ n ∧ ⌈M⌉₊ ≤ n := by
    filter_upwards [hev, eventually_ge_atTop 1, eventually_ge_atTop F.card,
      eventually_ge_atTop ⌈M⌉₊] with n a b c d using ⟨a, b, c, d⟩
  obtain ⟨n, hnδ, hn1, hnF, hnM⟩ := hall.exists
  -- the vector of dilations, padded with zeros
  let c : Fin n → ℝ := fun i =>
    if h : i.val < F.card then ((F.equivFin).symm ⟨i.val, h⟩ : ℝ) else 0
  have hbox : ∀ i, |c i| ≤ n := by
    intro i
    simp only [c]
    split_ifs with h
    · have hmem : ((F.equivFin).symm ⟨i.val, h⟩ : ℝ) ∈ F := ((F.equivFin).symm ⟨i.val, h⟩).2
      have : |((F.equivFin).symm ⟨i.val, h⟩ : ℝ)| ≤ M :=
        Finset.single_le_sum (f := fun c => |c|) (fun c _ => abs_nonneg c) hmem
      have hM' : M ≤ n := (Nat.le_ceil M).trans (by exact_mod_cast hnM)
      linarith
    · simp
  obtain ⟨k, G, hG, hGμ, hgood⟩ := hst n hn1 c hbox
  refine ⟨k, fun c₀ hc₀ => ?_⟩
  -- the index of `c₀`
  let j : ℕ := (F.equivFin ⟨c₀, hc₀⟩).val
  have hjF : j < F.card := (F.equivFin ⟨c₀, hc₀⟩).2
  have hjn : j < n := lt_of_lt_of_le hjF hnF
  have hcj : c ⟨j, hjn⟩ = c₀ := by
    simp [c, j, hjF]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hrho := rho_le_of_good μ (a := c₀ * ((k : ℝ) + 1 / 2)) (ε := 1 / n) (by positivity) hG
    (fun l hl => by
      have := hgood l hl ⟨j, hjn⟩
      rwa [hcj] at this)
  calc rho μ (c₀ * ((k : ℝ) + 1 / 2)) ≤ 2 * Real.pi * (1 / n) + (μ Gᶜ).toReal := hrho
    _ ≤ 2 * Real.pi / n + n * (1 / 2 : ℝ) ^ n := by
        have : 2 * Real.pi * (1 / (n : ℝ)) = 2 * Real.pi / n := by ring
        linarith
    _ < δ := hnδ

/-- **The existence theorem from a measure with the stage property.** -/
theorem exists_beta_of_stage_measure (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupp : μ (Set.Icc (1 : ℝ) 2)ᶜ = 0) (hst : StageProperty μ) :
    ∃ β : TopologicalSpace ℝ,
      @IsTopologicalAddGroup ℝ β _ ∧ @T2Space ℝ β ∧ eT ≤ β ∧ @ContinuousConstSMul ℝ ℝ β _ ∧
      (∀ V ∈ @nhds ℝ β 0, ∃ k : ℤ, ((k : ℝ) + 1 / 2) ∈ V) ∧
      (∀ b : ℝ, b ≠ 0 → ¬ @Continuous ℝ (AddCircle (1 : ℝ)) β cT (chi b)) ∧
      (∀ x : ℝ, x ∈ @closure ℝ β (Set.range (fun k : ℤ => (k : ℝ)))) := by
  have hps := isPseudoNorm_rho μ hsupp
  have hH := halfInt_of_stages μ hst
  exact ⟨betaTop hps, betaTop_isTopologicalAddGroup hps, betaTop_t2 hps, eT_le_betaTop hps,
    betaTop_constSMul hps, half_in_nhds hps hH, fun b hb => chi_not_continuous hps hH hb,
    int_dense hps hH⟩

end Beta
end PVG
