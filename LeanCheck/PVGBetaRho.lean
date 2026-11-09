import Mathlib
import LeanCheck.PVGBetaTop

/-!
# PVG: the pseudonorm of an atomless measure (Lean check)

Scope. The step "the topology of a measure" of the proof of Theorem `thm:betaexists` of PVG_v22. For a function
`gf θ = min 1 (2π ‖θ‖)` (`‖θ‖` the distance to the nearest integer) and a probability measure `μ` on `ℝ` carried by `[1,2]` without atoms,
`rho μ t = ∫ gf(tλ) dμ(λ)`.

* `isPseudoNorm_rho`: `rho μ` satisfies `IsPseudoNorm` of `PVGBetaTop` with `K = 4π` (even, subadditive, `rho t ≤ 4π|t|`, and `rho t > 0` for
  `t ≠ 0` because `μ` has no atoms);
* `rho_le_of_good`: if `‖aλ‖ < ε` for all `λ` in a measurable set `G`, then `rho μ a ≤ 2π ε + μ(Gᶜ)` (the estimate in the proof of (b)).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open MeasureTheory Filter Topology

namespace PVG
namespace Beta

noncomputable def gf (θ : ℝ) : ℝ := min 1 (2 * Real.pi * ‖(θ : AddCircle (1 : ℝ))‖)

lemma gf_nonneg (θ : ℝ) : 0 ≤ gf θ := by
  unfold gf
  exact le_min zero_le_one (by positivity)

lemma gf_le_one (θ : ℝ) : gf θ ≤ 1 := min_le_left _ _

lemma gf_zero : gf 0 = 0 := by simp [gf]

lemma gf_neg (θ : ℝ) : gf (-θ) = gf θ := by
  simp [gf, AddCircle.coe_neg]

lemma gf_add_le (θ φ : ℝ) : gf (θ + φ) ≤ gf θ + gf φ := by
  unfold gf
  have h1 : ‖((θ + φ : ℝ) : AddCircle (1 : ℝ))‖ ≤ ‖(θ : AddCircle (1 : ℝ))‖ + ‖(φ : AddCircle (1 : ℝ))‖ := by
    rw [AddCircle.coe_add]; exact norm_add_le _ _
  set a := 2 * Real.pi * ‖(θ : AddCircle (1 : ℝ))‖ with ha
  set b := 2 * Real.pi * ‖(φ : AddCircle (1 : ℝ))‖ with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have h2 : 2 * Real.pi * ‖((θ + φ : ℝ) : AddCircle (1 : ℝ))‖ ≤ a + b := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    rw [mul_add] at this; exact this
  calc min 1 (2 * Real.pi * ‖((θ + φ : ℝ) : AddCircle (1 : ℝ))‖) ≤ min 1 (a + b) := min_le_min_left _ h2
    _ ≤ min 1 a + min 1 b := by
        rcases le_total a 1 with h | h
        · rcases le_total b 1 with h' | h'
          · rw [min_eq_right h, min_eq_right h']; exact min_le_right _ _
          · rw [min_eq_right h, min_eq_left h']; exact (min_le_left _ _).trans (by linarith)
        · rw [min_eq_left h]; exact (min_le_left _ _).trans (by have := le_min zero_le_one hb0; linarith [min_le_left 1 b, this])

lemma gf_le_lin (θ : ℝ) : gf θ ≤ 2 * Real.pi * |θ| := by
  unfold gf
  refine (min_le_right _ _).trans ?_
  have h : ‖(θ : AddCircle (1 : ℝ))‖ ≤ |θ| := by
    have := AddCircle.norm_eq (p := (1 : ℝ)) (x := θ)
    rw [this]
    have := round_le (θ * 1⁻¹ ) 0
    simpa using round_le θ 0
  exact mul_le_mul_of_nonneg_left h (by positivity)

lemma gf_eq_zero {θ : ℝ} (h : gf θ = 0) : ∃ n : ℤ, (n : ℝ) = θ := by
  unfold gf at h
  have h1 : 2 * Real.pi * ‖(θ : AddCircle (1 : ℝ))‖ = 0 := by
    rcases min_choice 1 (2 * Real.pi * ‖(θ : AddCircle (1 : ℝ))‖) with h' | h'
    · rw [h'] at h; exact absurd h one_ne_zero
    · rw [h'] at h; exact h
  have h2 : ‖(θ : AddCircle (1 : ℝ))‖ = 0 := by
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    simpa [hpi] using h1
  have h3 : (θ : AddCircle (1 : ℝ)) = 0 := norm_eq_zero.1 h2
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).1 h3
  exact ⟨n, by simpa using hn⟩

lemma continuous_gf : Continuous gf := by
  unfold gf
  exact continuous_const.min (continuous_const.mul (continuous_norm.comp (AddCircle.continuous_mk' 1)))

/-- The pseudonorm of a measure. -/
noncomputable def rho (μ : Measure ℝ) (t : ℝ) : ℝ := ∫ l, gf (t * l) ∂μ

section
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

lemma integrable_gf (t : ℝ) : Integrable (fun l => gf (t * l)) μ := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (continuous_gf.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun l => by
      rw [Real.norm_of_nonneg (gf_nonneg _)]; exact gf_le_one _)

lemma rho_nonneg (t : ℝ) : 0 ≤ rho μ t := integral_nonneg (fun l => gf_nonneg _)

lemma rho_zero : rho μ 0 = 0 := by simp [rho, gf_zero]

lemma rho_neg (t : ℝ) : rho μ (-t) = rho μ t := by
  unfold rho
  congr 1
  funext l
  rw [neg_mul, gf_neg]

lemma rho_add_le (t s : ℝ) : rho μ (t + s) ≤ rho μ t + rho μ s := by
  unfold rho
  rw [← integral_add (integrable_gf μ t) (integrable_gf μ s)]
  refine integral_mono (integrable_gf μ _) ((integrable_gf μ t).add (integrable_gf μ s)) (fun l => ?_)
  show gf ((t + s) * l) ≤ gf (t * l) + gf (s * l)
  rw [add_mul]; exact gf_add_le _ _

lemma rho_le_lin (hsupp : μ (Set.Icc (1 : ℝ) 2)ᶜ = 0) (t : ℝ) : rho μ t ≤ 4 * Real.pi * |t| := by
  unfold rho
  have hae : ∀ᵐ l ∂μ, l ∈ Set.Icc (1 : ℝ) 2 := by
    rw [ae_iff]
    show μ {l | ¬ (l ∈ Set.Icc (1 : ℝ) 2)} = 0
    exact hsupp
  calc ∫ l, gf (t * l) ∂μ ≤ ∫ l, 4 * Real.pi * |t| ∂μ := by
        refine integral_mono_ae (integrable_gf μ t) (integrable_const _) ?_
        filter_upwards [hae] with l hl
        calc gf (t * l) ≤ 2 * Real.pi * |t * l| := gf_le_lin _
          _ = 2 * Real.pi * |t| * |l| := by rw [abs_mul]; ring
          _ ≤ 2 * Real.pi * |t| * 2 := by
              have : |l| ≤ 2 := by rw [abs_of_pos (by linarith [hl.1])]; exact hl.2
              exact mul_le_mul_of_nonneg_left this (by positivity)
          _ = 4 * Real.pi * |t| := by ring
    _ = 4 * Real.pi * |t| := by simp

lemma rho_pos [NullSingletonClass μ] {t : ℝ} (ht : t ≠ 0) : 0 < rho μ t := by
  refine lt_of_le_of_ne (rho_nonneg μ t) (fun h0 => ?_)
  have hint : (rho μ t) = 0 := h0.symm
  unfold rho at hint
  have hzero := (integral_eq_zero_iff_of_nonneg (fun l => gf_nonneg _) (integrable_gf μ t)).1 hint
  have hcount : ({l | gf (t * l) = 0} : Set ℝ).Countable := by
    refine (Set.countable_range (fun n : ℤ => (n : ℝ) / t)).mono ?_
    intro l hl
    obtain ⟨n, hn⟩ := gf_eq_zero hl
    refine ⟨n, ?_⟩
    show (n : ℝ) / t = l
    rw [hn]; field_simp
  have h1 : μ {l | gf (t * l) = 0} = 0 := hcount.measure_zero μ
  have h2 : μ {l | gf (t * l) = 0}ᶜ = 0 := by
    have := hzero
    rw [Filter.EventuallyEq, ae_iff] at this
    exact this
  have h3 : μ Set.univ = 0 := by
    have : (Set.univ : Set ℝ) = {l | gf (t * l) = 0} ∪ {l | gf (t * l) = 0}ᶜ := (Set.union_compl_self _).symm
    rw [this]
    exact measure_union_null h1 h2
  simp at h3

theorem isPseudoNorm_rho [NullSingletonClass μ] (hsupp : μ (Set.Icc (1 : ℝ) 2)ᶜ = 0) :
    IsPseudoNorm (rho μ) (4 * Real.pi) where
  zero := rho_zero μ
  nonneg := rho_nonneg μ
  neg := rho_neg μ
  add_le := rho_add_le μ
  le_lin := rho_le_lin μ hsupp
  pos := fun t ht => rho_pos μ ht
  K_pos := by positivity

/-- The estimate of the proof of (b): small phases on a set of large measure. -/
lemma rho_le_of_good {a ε : ℝ} (hε : 0 ≤ ε) {G : Set ℝ} (hG : MeasurableSet G)
    (hgood : ∀ l ∈ G, ‖((a * l : ℝ) : AddCircle (1 : ℝ))‖ < ε) :
    rho μ a ≤ 2 * Real.pi * ε + (μ Gᶜ).toReal := by
  unfold rho
  have hf : ∀ l, gf (a * l) ≤ 2 * Real.pi * ε + Gᶜ.indicator (fun _ => (1 : ℝ)) l := by
    intro l
    by_cases hl : l ∈ G
    · have := hgood l hl
      have h1 : gf (a * l) ≤ 2 * Real.pi * ‖((a * l : ℝ) : AddCircle (1 : ℝ))‖ := min_le_right _ _
      have h2 : 2 * Real.pi * ‖((a * l : ℝ) : AddCircle (1 : ℝ))‖ ≤ 2 * Real.pi * ε :=
        mul_le_mul_of_nonneg_left this.le (by positivity)
      have h3 : Gᶜ.indicator (fun _ => (1 : ℝ)) l = 0 := Set.indicator_of_notMem (by simpa using hl) _
      rw [h3]; linarith
    · have h3 : Gᶜ.indicator (fun _ => (1 : ℝ)) l = 1 := Set.indicator_of_mem (by simpa using hl) _
      rw [h3]
      have := gf_le_one (a * l)
      have : 0 ≤ 2 * Real.pi * ε := by positivity
      linarith
  have hind : Integrable (Gᶜ.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hG.compl
  calc ∫ l, gf (a * l) ∂μ ≤ ∫ l, (2 * Real.pi * ε + Gᶜ.indicator (fun _ => (1 : ℝ)) l) ∂μ :=
        integral_mono (integrable_gf μ a) ((integrable_const _).add hind) hf
    _ = 2 * Real.pi * ε + (μ Gᶜ).toReal := by
        rw [integral_add (integrable_const _) hind, integral_const, integral_indicator_const _ hG.compl]
        simp [Measure.real]

end

end Beta
end PVG
