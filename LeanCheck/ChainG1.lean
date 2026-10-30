import LeanCheck.ChainF3
import LeanCheck.ChainUniversal

/-!
# Sequences converging for every coefficient functional
(TVGadd-v2 Theorem `seq:universal`; the case of a single functional is HamelCharactersTVG_v18 Theorem 14.6)

For a sequence `x : ℕ → ℝ`:
* `τ_f`-null for every nonzero `f` iff the rational span is finite-dimensional and the coordinates in a rational basis tend to zero;
* `σ_f`-null (equivalently `β_f`-null) for every nonzero `f` iff the span is finite-dimensional, `x → 0` usually, and the modular
  conditions `‖q_{n,j}/d‖ → 0` hold.
-/

namespace LeanCheck

open Filter Topology

section Universal

variable {m : ℕ}

lemma exists_coeff_ne_zero : ∃ f : ℝ →+ ℚ, f ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_coefficient
  exact ⟨f, fun h => by rw [h] at hf; simp at hf⟩

/-- A sequence with finite-dimensional rational span is a combination of a linearly independent family with rational
coordinates. -/
lemma exists_coords (x : ℕ → ℝ) (hfd : FiniteDimensional ℚ (Submodule.span ℚ (Set.range x))) :
    ∃ (m : ℕ) (b : Fin m → ℝ) (_ : LinearIndependent ℚ b) (q : ℕ → Fin m → ℚ),
      ∀ n, x n = ∑ j, ((q n j : ℚ) : ℝ) * b j := by
  set W := Submodule.span ℚ (Set.range x) with hW
  let B := Module.finBasis ℚ W
  refine ⟨Module.finrank ℚ W, fun j => ((B j : W) : ℝ), ?_,
    fun n j => B.repr ⟨x n, Submodule.subset_span ⟨n, rfl⟩⟩ j, fun n => ?_⟩
  · exact (B.linearIndependent).map' W.subtype W.ker_subtype
  · have h := B.sum_repr ⟨x n, Submodule.subset_span ⟨n, rfl⟩⟩
    have h2 := congrArg (fun v : W => (v : ℝ)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Rat.smul_def]

/-- **Theorem (TVGadd-v2 `seq:universal`), `τ` part.** -/
theorem seq_universal_tau (x : ℕ → ℝ) :
    (∀ f : ℝ →+ ℚ, f ≠ 0 → Tendsto x atTop (@nhds ℝ (tauT f ⊤) 0)) ↔
      ∃ (m : ℕ) (b : Fin m → ℝ) (_ : LinearIndependent ℚ b) (q : ℕ → Fin m → ℚ),
        (∀ n, x n = ∑ j, ((q n j : ℚ) : ℝ) * b j) ∧ ∀ j, Tendsto (fun n => ((q n j : ℚ) : ℝ)) atTop (𝓝 0) := by
  constructor
  · intro h
    have hσ : ∀ g : ℝ →+ ℚ, g ≠ 0 → Tendsto x atTop (@nhds ℝ (sigmaT g ⊤) 0) := fun g hg =>
      (@Continuous.tendsto ℝ ℝ (tauT g ⊤) (sigmaT g ⊤) id
        (@continuous_id_of_le ℝ (tauT g ⊤) (sigmaT g ⊤) (tauT_le_sigmaT g ⊤)) 0).comp (h g hg)
    have hfd := finite_universal ⊤ ⟨1, Submodule.mem_top, one_ne_zero⟩ x hσ
    obtain ⟨m, b, hb, q, hx⟩ := exists_coords x hfd
    obtain ⟨f, hf⟩ := exists_coeff_ne_zero
    refine ⟨m, b, hb, q, hx, ?_⟩
    have hxf : x = fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j := funext hx
    have := h f hf
    rw [hxf] at this
    exact (finite_span_tau f hf b hb q).1 this
  · rintro ⟨m, b, hb, q, hx, hq⟩ f hf
    have hxf : x = fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j := funext hx
    rw [hxf]
    exact (finite_span_tau f hf b hb q).2 hq

/-- **Theorem (TVGadd-v2 `seq:universal`), `σ` / `β` part.** -/
theorem seq_universal_sigma (x : ℕ → ℝ) :
    (∀ f : ℝ →+ ℚ, f ≠ 0 → Tendsto x atTop (@nhds ℝ (sigmaT f ⊤) 0)) ↔
      ∃ (m : ℕ) (b : Fin m → ℝ) (_ : LinearIndependent ℚ b) (q : ℕ → Fin m → ℚ),
        (∀ n, x n = ∑ j, ((q n j : ℚ) : ℝ) * b j) ∧ Tendsto x atTop (𝓝 0) ∧
          ∀ j, ∀ d : ℕ, 1 ≤ d → Tendsto (fun n => (((q n j / d : ℚ) : ℝ) : Circ)) atTop (𝓝 0) := by
  constructor
  · intro h
    have hfd := finite_universal ⊤ ⟨1, Submodule.mem_top, one_ne_zero⟩ x h
    obtain ⟨m, b, hb, q, hx⟩ := exists_coords x hfd
    obtain ⟨f, hf⟩ := exists_coeff_ne_zero
    have hxf : x = fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j := funext hx
    have := h f hf
    rw [hxf] at this
    obtain ⟨h1, h2⟩ := (finite_span_sigma f hf b hb q).1 this
    exact ⟨m, b, hb, q, hx, by rw [hxf]; exact h1, h2⟩
  · rintro ⟨m, b, hb, q, hx, h1, h2⟩ f hf
    have hxf : x = fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j := funext hx
    rw [hxf] at h1 ⊢
    exact (finite_span_sigma f hf b hb q).2 ⟨h1, h2⟩

theorem seq_universal_beta (x : ℕ → ℝ) :
    (∀ f : ℝ →+ ℚ, f ≠ 0 → Tendsto x atTop (@nhds ℝ (betaT f ⊤) 0)) ↔
      (∀ f : ℝ →+ ℚ, f ≠ 0 → Tendsto x atTop (@nhds ℝ (sigmaT f ⊤) 0)) :=
  ⟨fun h f hf => (beta_null_iff_sigma_null f ⊤ x).1 (h f hf),
    fun h f hf => (beta_null_iff_sigma_null f ⊤ x).2 (h f hf)⟩

end Universal

end LeanCheck
