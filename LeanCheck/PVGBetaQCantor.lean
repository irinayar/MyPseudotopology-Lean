import Mathlib
import LeanCheck.PVGBetaQStage
import LeanCheck.PVGBetaCantor
import LeanCheck.PVGBetaRho

/-!
# PVG: the stage system with the recurrence field, and the recurrence of `ρ` (Lean check)

Scope. Addendum H of the research note (the variant of Theorem `thm:betaexists`). `StagesQ x r` is `Stages x r` with one more field `Q`:
the recurrence property `Qprop n` of `PVGBetaQStage` at every level `n ≥ 1`.

* `StagesQ.recurProp`: the Cantor-type measure of a `StagesQ` system is carried by the intervals of every level, so for every vector `c`
  of the box `[-n,n]ⁿ` there are `p > q ≥ n` and a measurable set `G` of full measure with `‖c_i (s_p - s_q) λ‖ < 1/n` for all `λ ∈ G`;
* `recur_rho`: for such a measure `μ`, property `(Q)`: for every finite `F ⊂ ℝ`, `δ > 0` and `N` there are `p > q ≥ N` with
  `ρ_μ(c (s_p - s_q)) < δ` for all `c ∈ F`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open MeasureTheory Filter Topology Set

namespace PVG
namespace Beta

/-- A stage system with the recurrence property at every level. -/
structure StagesQ (x : ℕ → ℕ → ℝ) (r : ℕ → ℝ) : Prop extends Stages x r where
  Q : ∀ n, 1 ≤ n → Qprop n ⟨x n, r n⟩

/-- The output of the variant of the construction: a measure carried by `G`, with a recurrence time for every vector of the box. -/
def RecurProp (μ : Measure ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ n) → ∃ p q : ℕ, n ≤ q ∧ q < p ∧
    ∃ G : Set ℝ, MeasurableSet G ∧ μ Gᶜ = 0 ∧
      ∀ l ∈ G, ∀ i : Fin n, ‖((c i * (PVG.Lac.sS p - PVG.Lac.sS q) * l : ℝ) : AddCircle (1 : ℝ))‖ < 1 / n

variable {x : ℕ → ℕ → ℝ} {r : ℕ → ℝ}

theorem StagesQ.recurProp (h : StagesQ x r) : RecurProp (cantorMeasure x) := by
  intro n hn c hc
  obtain ⟨p, q, hq, hpq, hQ⟩ := h.Q n hn c hc
  have hS : Stages x r := h.toStages
  refine ⟨p, q, hq, hpq, ⋃ a ∈ Finset.range (2 ^ n), Iv x r n a,
    Finset.measurableSet_biUnion _ (fun a _ => Iv_meas x r n a), ?_, ?_⟩
  · unfold cantorMeasure
    rw [Measure.map_apply_of_aemeasurable hS.psi_aemeasurable
      (Finset.measurableSet_biUnion _ (fun a _ => Iv_meas x r n a)).compl,
      Measure.restrict_apply' measurableSet_Ico]
    have : psi x ⁻¹' (⋃ a ∈ Finset.range (2 ^ n), Iv x r n a)ᶜ ∩ Ico (0 : ℝ) 1 = ∅ := by
      ext u
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
      intro hu hu01
      apply hu
      refine mem_iUnion₂.2 ⟨dig n u, Finset.mem_range.2 (dig_lt hu01 n), hS.psi_mem hu01 n⟩
    rw [this]; simp
  · intro l hl i
    obtain ⟨a, haS, hla⟩ := mem_iUnion₂.1 hl
    exact hQ a (Finset.mem_range.1 haS) l hla i

/-- **Property `(Q)`** for `ρ_μ`. -/
theorem recur_rho (μ : Measure ℝ) [IsProbabilityMeasure μ] (hst : RecurProp μ) :
    ∀ (F : Finset ℝ) (δ : ℝ), 0 < δ → ∀ N : ℕ, ∃ p q : ℕ, N ≤ q ∧ q < p ∧
      ∀ c ∈ F, rho μ (c * (PVG.Lac.sS p - PVG.Lac.sS q)) < δ := by
  classical
  intro F δ hδ N
  set M : ℝ := ∑ c ∈ F, |c| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun c _ => abs_nonneg c)
  have h1 : Tendsto (fun n : ℕ => 2 * Real.pi / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi)
  have hev : ∀ᶠ n : ℕ in atTop, 2 * Real.pi / (n : ℝ) < δ := h1.eventually (gt_mem_nhds hδ)
  have hall : ∀ᶠ n : ℕ in atTop, (2 * Real.pi / (n : ℝ) < δ) ∧ 1 ≤ n ∧
      F.card ≤ n ∧ ⌈M⌉₊ ≤ n ∧ N ≤ n := by
    filter_upwards [hev, eventually_ge_atTop 1, eventually_ge_atTop F.card,
      eventually_ge_atTop ⌈M⌉₊, eventually_ge_atTop N] with n a b c d e using ⟨a, b, c, d, e⟩
  obtain ⟨n, hnδ, hn1, hnF, hnM, hnN⟩ := hall.exists
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
  obtain ⟨p, q, hq, hpq, G, hG, hGμ, hgood⟩ := hst n hn1 c hbox
  refine ⟨p, q, hnN.trans hq, hpq, fun c₀ hc₀ => ?_⟩
  let j : ℕ := (F.equivFin ⟨c₀, hc₀⟩).val
  have hjF : j < F.card := (F.equivFin ⟨c₀, hc₀⟩).2
  have hjn : j < n := lt_of_lt_of_le hjF hnF
  have hcj : c ⟨j, hjn⟩ = c₀ := by
    simp [c, j, hjF]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hrho := rho_le_of_good μ (a := c₀ * (PVG.Lac.sS p - PVG.Lac.sS q)) (ε := 1 / n) (by positivity) hG
    (fun l hl => by
      have := hgood l hl ⟨j, hjn⟩
      rwa [hcj] at this)
  calc rho μ (c₀ * (PVG.Lac.sS p - PVG.Lac.sS q)) ≤ 2 * Real.pi * (1 / n) + (μ Gᶜ).toReal := hrho
    _ = 2 * Real.pi / n := by rw [hGμ]; simp; ring
    _ < δ := hnδ

end Beta
end PVG
