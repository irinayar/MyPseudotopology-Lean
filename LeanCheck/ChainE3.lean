import LeanCheck.ChainE2
import LeanCheck.ChainX3

/-!
# A rational target with unchanged characters, and a strictly finer compatible TVG
(HamelCharactersTVG_v18 Lemma 16.2 `lem:rational-target`, Theorem 16.4 `thm:finer-compatible`)

The TVGQ file `ChainX3` already constructs `δ = γ_λ` on `ℚ` from the explicit factorial-chain topology `λ` on `ℚ/ℤ`
(`delta2`), with `δ ∈ 𝒬_Γ` (Hausdorff, locally quasi-convex, rational scalars continuous, dual exactly `Γ`),
`δ` not precompact and `δ ⊊ γ₀` (`delta2_mem`, `delta2_not_precompact`, `delta2_lt_gamma0`).  These are exactly the
assertions of Lemma 16.2 (with an explicit `λ` instead of the cited one).  Here we transfer to `ℝ`:
`η_f = T_f(δ) ∈ 𝒞_f`, `η_f ⊊ σ_f` and `η_f` is nondiscrete.
-/

namespace LeanCheck

open Filter Topology

section Strict

/-- **Lemma 16.2** (assembled for the explicit topology `delta2`). -/
theorem rational_target_lemma :
    delta2 ∈ Ccls Gam ∧ ¬ PrecompactG delta2 ∧ delta2 < gamma0 :=
  ⟨delta2_mem, delta2_not_precompact, delta2_lt_gamma0⟩

lemma sigmaT_top_eq_Tf (f : ℝ →+ ℚ) : sigmaT f ⊤ = Tf f gamma0 := by
  unfold sigmaT TfS Tf
  refine le_antisymm (inf_le_inf_left _ (le_iInf fun a => iInf_le (fun a : (⊤ : Submodule ℚ ℝ) => TopologicalSpace.induced (fa f (a : ℝ)) gamma0) ⟨a, trivial⟩))
    (inf_le_inf_left _ (le_iInf fun a : (⊤ : Submodule ℚ ℝ) => iInf_le _ (a : ℝ)))

/-- The character `x ↦ p(√2 f(x))` is not in `H_f`. -/
lemma sqrt2_f_not_mem (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    ¬ ∃ c a : ℝ, ∀ x : ℝ, ((((Real.sqrt 2 * (f x : ℝ) : ℝ))) : Circ) = chiH f c a x := by
  rintro ⟨c, a, h⟩
  let g : ℝ →+ ℝ := (AddMonoidHom.mulLeft (Real.sqrt 2)).comp ((Rat.castHom ℝ).toAddMonoidHom.comp f)
  let hh : ℝ →+ ℝ := (AddMonoidHom.mulLeft c) + faR f a
  have hgh : ∀ x : ℝ, ((g x : ℝ) : Circ) = ((hh x : ℝ) : Circ) := by
    intro x
    have := h x
    unfold chiH at this
    simpa [g, hh, faR_apply] using this
  have heq := lift_unique g hh hgh
  have hform : ∀ x : ℝ, Real.sqrt 2 * (f x : ℝ) = c * x + (f (a * x) : ℝ) := by
    intro x
    have := congrArg (fun m : ℝ →+ ℝ => m x) heq
    simpa [g, hh, faR_apply] using this
  have hc0 : c = 0 := by
    by_contra hc
    apply Cardinal.not_countable_real
    have : (Set.univ : Set ℝ) ⊆ Set.range (fun p : ℚ × ℚ => ((p.1 : ℝ) - Real.sqrt 2 * (p.2 : ℝ)) / c) := by
      intro t _
      refine ⟨(-(f (a * t)), -(f t)), ?_⟩
      have := hform t
      simp only
      push_cast
      field_simp
      linarith
    exact (Set.countable_range _).mono this
  have hf0 : ∀ x : ℝ, f x = 0 := by
    intro x
    by_contra hne
    have := hform x
    rw [hc0, zero_mul, zero_add] at this
    have hne' : ((f x : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hne
    apply irrational_sqrt_two
    refine ⟨f (a * x) / f x, ?_⟩
    rw [Rat.cast_div]
    field_simp
    linarith
  have := hf0 u
  rw [hu] at this
  exact one_ne_zero this

/-- **Theorem 16.4.**  For a coefficient function `f` (`f u = 1`) there is a topology `η_f = T_f(δ)` in `𝒞_f` that is
nondiscrete and strictly finer than `σ_f`; in particular `σ_f` is not the finest member of `𝒞_f`. -/
theorem strictly_finer_compatible (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    Tf f delta2 ∈ Kcls (Hset f ⊤ : Set Chars) realDil ∧ Tf f delta2 < sigmaT f ⊤ ∧
      ({0} : Set ℝ) ∉ @nhds ℝ (Tf f delta2) 0 := by
  have hmem := Tf_mem_Kcls f delta2 delta2_mem
  refine ⟨hmem, ?_, ?_⟩
  · rw [sigmaT_top_eq_Tf]
    refine lt_of_le_of_ne (Tf_mono f delta2_le_gamma0) (fun h => ?_)
    have := (Tf_le_iff f u hu gamma0 delta2 (by rw [gamma0_eq_gam]; exact gam_group _ circT_group)
      (fun s => gamma0_scalar s) delta2_mem.1.1 (fun s => by
        have := delta2_mem.2 s
        have e : (⇑(mq s : ℚ →+ ℚ)) = fun x : ℚ => s * x := by funext x; simp [mq_apply]
        rw [e] at this; exact this)).1 h.symm.le
    exact delta2_ne_gamma0 (le_antisymm delta2_le_gamma0 this)
  · intro hnd
    let ψ0 : Chars := (psiQ (Real.sqrt 2)).comp f
    have hdisc : @DiscreteTopology ℝ (Tf f delta2) := by
      letI := Tf f delta2
      haveI := hmem.1
      exact discreteTopology_of_isOpen_singleton_zero (isOpen_iff_mem_nhds.2 (fun x hx => by
        rw [Set.mem_singleton_iff] at hx; subst hx; exact hnd))
    have hcont : @Continuous ℝ Circ (Tf f delta2) circTop ψ0 :=
      @continuous_of_discreteTopology ℝ (Tf f delta2) hdisc Circ circTop ψ0
    obtain ⟨c, a, -, h⟩ := (hmem.2.2.2.1 ψ0).1 hcont
    exact sqrt2_f_not_mem f u hu ⟨c, a, fun x => by simpa [ψ0, psiQ_apply] using h x⟩

end Strict

end LeanCheck
