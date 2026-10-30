import LeanCheck.ChainE4

/-!
# First countability, completeness and local compactness
(HamelCharactersTVG_v18 Theorem 12.1 `thm:nonmetric`, the part not about connectedness of the completions)

For a nonzero rational-valued additive `f` and `S = ℝ`:

* `sigma_not_firstCountable`  : `σ_f` is not first countable (hence not metrizable); the case of `β_f` is
                                `beta_not_firstCountable`;
* `sigma_not_complete`, `beta_not_complete` : neither `σ_f` nor `β_f` is complete (a dense proper image in the
                                completion; the completion has cardinality `2^𝔠 > 𝔠`);
* `sigma_not_locallyCompact`, `beta_not_locallyCompact` : neither is locally compact (a locally compact group is complete);
* `completion_sigma_not_firstCountable` : the completion `ℝ × K` is not first countable (it contains `(ℝ, σ_f)`).
-/

namespace LeanCheck

open Filter Topology Cardinal

section FirstCountable

/-- **`σ_f` is not first countable.** -/
theorem sigma_not_firstCountable (f : ℝ →+ ℚ) (hf : f ≠ 0) :
    ¬ @FirstCountableTopology ℝ (sigmaT f ⊤) := by
  intro hfc
  obtain ⟨u, hu⟩ := exists_unit f hf
  have hnhds := @FirstCountableTopology.nhds_generated_countable ℝ (sigmaT f ⊤) hfc 0
  obtain ⟨B, hB⟩ := @Filter.exists_antitone_basis ℝ (@nhds ℝ (sigmaT f ⊤) 0) hnhds
  have hdata : ∀ n, ∃ ε : ℝ, 0 < ε ∧ ∃ I : Finset ℝ, (∀ a ∈ I, a ∈ (⊤ : Submodule ℚ ℝ)) ∧
      ∃ W : ℝ → Set Circ, (∀ a ∈ I, W a ∈ 𝓝 (0 : Circ)) ∧
      {x : ℝ | |x| < ε ∧ ∀ a ∈ I, (((f (a * x) : ℚ) : ℝ) : Circ) ∈ W a} ⊆ B n :=
    fun n => sigma_nhds_sub f ⊤ (B n) (hB.mem n)
  choose ε hε I hI W hW hsub using hdata
  -- the countably many parameters used
  let P : Set ℝ := ⋃ n, (I n : Set ℝ)
  have hPc : P.Countable := Set.countable_iUnion fun n => (I n).finite_toSet.countable
  let S' : Submodule ℚ ℝ := Submodule.span ℚ P
  have hS'c : (S' : Set ℝ).Countable := by
    haveI : Countable P := hPc.to_subtype
    have h1 : Countable (Submodule.span ℚ (Set.range (Subtype.val : P → ℝ))) := inferInstance
    rw [Subtype.range_coe] at h1
    exact Set.countable_coe_iff.1 h1
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℝ, a0 ∉ S' := by
    by_contra hall
    push Not at hall
    exact Cardinal.not_countable_real (hS'c.mono (fun x _ => hall x))
  -- `p ∘ f_{a0}` would be `σ_{f,S'}`-continuous
  have hcont : @Continuous ℝ Circ (sigmaT f S') circTop (pfHom f a0) := by
    have hat : @ContinuousAt ℝ Circ (sigmaT f S') circTop (pfHom f a0) 0 := by
      intro V hV
      have hσ : @Continuous ℝ Circ (sigmaT f ⊤) circTop (pfHom f a0) :=
        continuous_le_dom (sigmaT_le_betaT f ⊤) (pfHom_cont_beta f ⊤ ⟨a0, trivial⟩)
      have h1 : (pfHom f a0) ⁻¹' V ∈ @nhds ℝ (sigmaT f ⊤) 0 :=
        (@Continuous.continuousAt ℝ Circ (sigmaT f ⊤) circTop (pfHom f a0) 0 hσ) hV
      obtain ⟨n, -, hn⟩ := hB.toHasBasis.mem_iff.1 h1
      have hcyl : {x : ℝ | |x| < ε n ∧ ∀ a ∈ I n, (((f (a * x) : ℚ) : ℝ) : Circ) ∈ W n a} ∈
          @nhds ℝ (sigmaT f S') 0 := by
        have e : {x : ℝ | |x| < ε n ∧ ∀ a ∈ I n, (((f (a * x) : ℚ) : ℝ) : Circ) ∈ W n a} =
            Set.Ioo (-ε n) (ε n) ∩ ⋂ a ∈ I n, (pfHom f a) ⁻¹' (W n a) := by
          ext x
          simp [abs_lt, pfHom_apply, and_assoc]
        rw [e]
        refine Filter.inter_mem ?_ ?_
        · have h2 : Set.Ioo (-ε n) (ε n) ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith [hε n]) (hε n)
          exact (nhds_mono (sigmaT_le_usual f S')) h2
        · refine (Filter.biInter_finset_mem (I n)).2 (fun a ha => ?_)
          have haS' : a ∈ S' := Submodule.subset_span (Set.mem_iUnion.2 ⟨n, ha⟩)
          have hc : @Continuous ℝ Circ (sigmaT f S') circTop (pfHom f a) :=
            continuous_le_dom (sigmaT_le_betaT f S') (pfHom_cont_beta f S' ⟨a, haS'⟩)
          exact (@Continuous.continuousAt ℝ Circ (sigmaT f S') circTop (pfHom f a) 0 hc)
            (by rw [map_zero]; exact hW n a ha)
      show (pfHom f a0 : ℝ → Circ) ⁻¹' V ∈ @nhds ℝ (sigmaT f S') 0
      exact Filter.mem_of_superset hcyl ((hsub n).trans hn)
    exact @continuous_of_continuousAt_zero ℝ (sigmaT f S') _ (sigmaT_group f S') Circ Chars _
      circTop' _ _ _ (pfHom f a0) hat
  obtain ⟨c, a', ha', h⟩ := (dual_sigma f S' (pfHom f a0)).1 hcont
  have := chiH_unique f u hu 0 a0 c a' (fun x => by
    have hx := h x
    rw [pfHom_apply] at hx
    unfold chiH
    rw [zero_mul, zero_add]
    exact hx)
  rw [this.2] at ha0
  exact ha0 ha'

theorem sigma_not_metrizable (f : ℝ →+ ℚ) (hf : f ≠ 0) :
    ¬ @TopologicalSpace.MetrizableSpace ℝ (sigmaT f ⊤) := by
  intro hm
  exact sigma_not_firstCountable f hf (@TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology ℝ
    (sigmaT f ⊤) (@TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace ℝ (sigmaT f ⊤) hm))

end FirstCountable

section Complete

lemma card_PD_top : 2 ^ 𝔠 ≤ Cardinal.mk (PD (↥(⊤ : Submodule ℚ ℝ))) := by
  let Λ : (ℝ →+ ℚ) → PD (↥(⊤ : Submodule ℚ ℝ)) := fun g =>
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
      ((Rat.castHom ℝ).toAddMonoidHom.comp (g.comp (⊤ : Submodule ℚ ℝ).subtype.toAddMonoidHom))
  have hinj : Function.Injective Λ := by
    intro g g' h
    have hall : ∀ x : ℝ, (((g x : ℚ) : ℝ) : Circ) = (((g' x : ℚ) : ℝ) : Circ) := by
      intro x
      have := congrArg (fun m : PD (↥(⊤ : Submodule ℚ ℝ)) => m ⟨x, trivial⟩) h
      simpa [Λ] using this
    have := lift_unique ((Rat.castHom ℝ).toAddMonoidHom.comp g) ((Rat.castHom ℝ).toAddMonoidHom.comp g')
      (fun x => by simpa using hall x)
    ext x
    have := congrArg (fun m : ℝ →+ ℝ => m x) this
    simpa using this
  have := Cardinal.mk_le_of_injective hinj
  rwa [card_addHom] at this

/-- A complete `RT η` surjects under an inducing dense homomorphism. -/
lemma surj_of_complete (η : TopologicalSpace ℝ) [IsTopologicalAddGroup (RT η)] [CompleteSpace (RT η)]
    {X : Type} [AddCommGroup X] [UniformSpace X] [IsUniformAddGroup X] [T2Space X]
    (J : RT η →+ X) (hind : IsInducing (J : RT η → X)) (hdense : DenseRange J) : Function.Surjective J := by
  have hu : IsUniformInducing (J : RT η → X) := AddMonoidHom.isUniformInducing_of_isInducing hind
  have hc : IsComplete (Set.range (J : RT η → X)) := hu.isComplete_range
  have hcl : IsClosed (Set.range (J : RT η → X)) := hc.isClosed
  have : Set.range (J : RT η → X) = Set.univ := by
    rw [← hcl.closure_eq, hdense.closure_range]
  intro x
  have hx : x ∈ Set.range (J : RT η → X) := by rw [this]; trivial
  exact hx

theorem sigma_not_complete (f : ℝ →+ ℚ) (hf : f ≠ 0) : ¬ CompleteSpace (RT (sigmaT f ⊤)) := by
  intro hcomp
  obtain ⟨u, hu⟩ := exists_unit f hf
  have hsurj := surj_of_complete (sigmaT f ⊤) (ISigma f ⊤) (ISigma_inducing f ⊤) (ISigma_denseRange f u hu ⊤)
  have h1 : Cardinal.mk (ℝ × PD (↥(⊤ : Submodule ℚ ℝ))) ≤ Cardinal.mk (RT (sigmaT f ⊤)) :=
    Cardinal.mk_le_of_surjective hsurj
  have h2 : Cardinal.mk (PD (↥(⊤ : Submodule ℚ ℝ))) ≤ Cardinal.mk (ℝ × PD (↥(⊤ : Submodule ℚ ℝ))) := by
    haveI : Nonempty ℝ := ⟨0⟩
    exact Cardinal.mk_le_of_injective (f := fun p => ((0 : ℝ), p)) (fun a b h => by simpa using h)
  have h3 : Cardinal.mk (RT (sigmaT f ⊤)) = 𝔠 := Cardinal.mk_real
  have h4 := card_PD_top
  have := h4.trans (h2.trans (h1.trans h3.le))
  exact absurd this (not_le.2 (Cardinal.cantor 𝔠))

theorem beta_not_complete (f : ℝ →+ ℚ) (hf : f ≠ 0) : ¬ CompleteSpace (RT (betaT f ⊤)) := by
  intro hcomp
  obtain ⟨u, hu⟩ := exists_unit f hf
  have hsurj := surj_of_complete (betaT f ⊤) (JBeta f ⊤) (JBeta_inducing f ⊤) (JBeta_denseRange f u hu ⊤)
  have h1 : Cardinal.mk (PD ℝ × PD (↥(⊤ : Submodule ℚ ℝ))) ≤ Cardinal.mk (RT (betaT f ⊤)) :=
    Cardinal.mk_le_of_surjective hsurj
  have h2 : Cardinal.mk (PD (↥(⊤ : Submodule ℚ ℝ))) ≤ Cardinal.mk (PD ℝ × PD (↥(⊤ : Submodule ℚ ℝ))) := by
    exact Cardinal.mk_le_of_injective (f := fun p => ((0 : PD ℝ), p)) (fun a b h => by simpa using h)
  have h3 : Cardinal.mk (RT (betaT f ⊤)) = 𝔠 := Cardinal.mk_real
  have h4 := card_PD_top
  have := h4.trans (h2.trans (h1.trans h3.le))
  exact absurd this (not_le.2 (Cardinal.cantor 𝔠))

theorem sigma_not_locallyCompact (f : ℝ →+ ℚ) (hf : f ≠ 0) : ¬ LocallyCompactSpace (RT (sigmaT f ⊤)) := by
  intro hlc
  apply sigma_not_complete f hf
  haveI : WeaklyLocallyCompactSpace (RT (sigmaT f ⊤)) := inferInstance
  exact IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace (RT (sigmaT f ⊤))

theorem beta_not_locallyCompact (f : ℝ →+ ℚ) (hf : f ≠ 0) : ¬ LocallyCompactSpace (RT (betaT f ⊤)) := by
  intro hlc
  apply beta_not_complete f hf
  haveI : WeaklyLocallyCompactSpace (RT (betaT f ⊤)) := inferInstance
  exact IsLeftUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace (RT (betaT f ⊤))

end Complete

section CompletionNonmetrizable

/-- The completion `ℝ × K` of `(ℝ, σ_f)` is not first countable, hence not metrizable. -/
theorem sigma_completion_not_firstCountable (f : ℝ →+ ℚ) (hf : f ≠ 0) :
    ¬ FirstCountableTopology (ℝ × PD (↥(⊤ : Submodule ℚ ℝ))) := by
  intro h
  exact sigma_not_firstCountable f hf
    (@Topology.IsInducing.firstCountableTopology ℝ (sigmaT f ⊤) (ℝ × PD (↥(⊤ : Submodule ℚ ℝ))) _ h
      (ISigma f ⊤) (ISigma_inducing f ⊤))

/-- The completion `K_ℝ × K` of `(ℝ, β_f)` is not first countable, hence not metrizable. -/
theorem beta_completion_not_firstCountable (f : ℝ →+ ℚ) (hf : f ≠ 0) :
    ¬ FirstCountableTopology (PD ℝ × PD (↥(⊤ : Submodule ℚ ℝ))) := by
  intro h
  exact beta_not_firstCountable f hf ⊤
    (@Topology.IsInducing.firstCountableTopology ℝ (betaT f ⊤) (PD ℝ × PD (↥(⊤ : Submodule ℚ ℝ))) _ h
      (JBeta f ⊤) (JBeta_inducing f ⊤))

end CompletionNonmetrizable

end LeanCheck
