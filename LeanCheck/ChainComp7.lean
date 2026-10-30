import LeanCheck.ChainComp6

/-!
# Uniqueness of completions, and the literal isomorphisms of the completion theorems

`completion_unique`: two dense uniform embeddings of the same uniform abelian group into complete Hausdorff
uniform abelian groups are related by a unique uniform isomorphism compatible with the embeddings.
Taking one of the targets to be Mathlib's `UniformSpace.Completion` gives
`Comp(ℝ, η) ≅ X` *literally* for each of the completion theorems (`σ`, `β`, `τ`, `θ_S`).
-/

namespace LeanCheck

open Topology UniformSpace

/-- **Uniqueness of the completion of a uniform abelian group.** -/
theorem completion_unique {α X₁ X₂ : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
    [AddCommGroup X₁] [UniformSpace X₁] [IsUniformAddGroup X₁] [CompleteSpace X₁] [T2Space X₁]
    [AddCommGroup X₂] [UniformSpace X₂] [IsUniformAddGroup X₂] [CompleteSpace X₂] [T2Space X₂]
    (J₁ : α →+ X₁) (J₂ : α →+ X₂) (h₁ : IsUniformInducing J₁) (d₁ : DenseRange J₁)
    (h₂ : IsUniformInducing J₂) (d₂ : DenseRange J₂) :
    ∃ e : X₁ ≃+ X₂, UniformContinuous e ∧ UniformContinuous e.symm ∧ ∀ a, e (J₁ a) = J₂ a := by
  have di₁ := h₁.isDenseInducing d₁
  have di₂ := h₂.isDenseInducing d₂
  have u₁ : UniformContinuous J₁ := h₁.uniformContinuous
  have u₂ : UniformContinuous J₂ := h₂.uniformContinuous
  let φ : X₁ → X₂ := di₁.extend J₂
  let ψ : X₂ → X₁ := di₂.extend J₁
  have hφu : UniformContinuous φ := uniformContinuous_uniformly_extend h₁ d₁ u₂
  have hψu : UniformContinuous ψ := uniformContinuous_uniformly_extend h₂ d₂ u₁
  have hφJ : ∀ a, φ (J₁ a) = J₂ a := di₁.extend_eq u₂.continuous
  have hψJ : ∀ a, ψ (J₂ a) = J₁ a := di₂.extend_eq u₁.continuous
  have hψφ : ∀ x, ψ (φ x) = x := by
    have := d₁.equalizer (hψu.continuous.comp hφu.continuous) continuous_id
      (funext fun a => by simp [hφJ, hψJ])
    exact congrFun this
  have hφψ : ∀ y, φ (ψ y) = y := by
    have := d₂.equalizer (hφu.continuous.comp hψu.continuous) continuous_id
      (funext fun a => by simp [hφJ, hψJ])
    exact congrFun this
  have hadd : ∀ x y, φ (x + y) = φ x + φ y := by
    have hc1 : Continuous fun p : X₁ × X₁ => φ (p.1 + p.2) :=
      hφu.continuous.comp continuous_add
    have hc2 : Continuous fun p : X₁ × X₁ => φ p.1 + φ p.2 :=
      (hφu.continuous.comp continuous_fst).add (hφu.continuous.comp continuous_snd)
    have := (d₁.prodMap d₁).equalizer hc1 hc2 (funext fun p => by
      simp only [Function.comp, Prod.map, ← map_add, hφJ])
    intro x y
    exact congrFun this (x, y)
  refine ⟨{ toFun := φ, invFun := ψ, left_inv := hψφ, right_inv := hφψ, map_add' := hadd },
    hφu, hψu, hφJ⟩

/-- The canonical embedding of a uniform abelian group into its completion, as a homomorphism. -/
def coeAddHom' (α : Type*) [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α] :
    α →+ Completion α where
  toFun := fun a => (a : Completion α)
  map_zero' := Completion.coe_zero
  map_add' := Completion.coe_add

/-- **Any dense uniform embedding into a complete Hausdorff group is the completion**:
`Completion α ≃+ X`, uniformly bicontinuous, compatible with the embeddings. -/
theorem completion_iso_completion {α X : Type*} [AddCommGroup α] [UniformSpace α]
    [IsUniformAddGroup α] [AddCommGroup X] [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X]
    [T2Space X] (J : α →+ X) (h : IsUniformInducing J) (d : DenseRange J) :
    ∃ e : Completion α ≃+ X, UniformContinuous e ∧ UniformContinuous e.symm ∧
      ∀ a : α, e (a : Completion α) = J a :=
  completion_unique (coeAddHom' α) J (Completion.isUniformInducing_coe α) Completion.denseRange_coe h d

/-! ### The real line with a topology `η`, as a uniform group -/

/-- `ℝ` carrying the additive group topology `η`. -/
def RT (_η : TopologicalSpace ℝ) : Type := ℝ

noncomputable instance (η : TopologicalSpace ℝ) : AddCommGroup (RT η) := inferInstanceAs (AddCommGroup ℝ)

instance (η : TopologicalSpace ℝ) : TopologicalSpace (RT η) := η

noncomputable instance RT.uniformSpace (η : TopologicalSpace ℝ) [IsTopologicalAddGroup (RT η)] :
    UniformSpace (RT η) := IsTopologicalAddGroup.rightUniformSpace (RT η)

instance RT.uniformAddGroup (η : TopologicalSpace ℝ) [IsTopologicalAddGroup (RT η)] :
    IsUniformAddGroup (RT η) := isUniformAddGroup_of_addCommGroup

/-- If an embedding `J` induces `η`, then `η` is a group topology. -/
theorem RT.isTopologicalAddGroup_of_inducing {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (η : TopologicalSpace ℝ) (J : ℝ →+ X) (h : @IsInducing ℝ X η _ J) :
    IsTopologicalAddGroup (RT η) :=
  IsInducing.isTopologicalAddGroup (G := X) (F := RT η →+ X) (J : RT η →+ X) h

instance RT.sigma_group (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : IsTopologicalAddGroup (RT (sigmaT f S)) :=
  RT.isTopologicalAddGroup_of_inducing _ (ISigma f S) (ISigma_inducing f S)

instance RT.beta_group (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : IsTopologicalAddGroup (RT (betaT f S)) :=
  RT.isTopologicalAddGroup_of_inducing _ (JBeta f S) (JBeta_inducing f S)

/-- Every rational subspace has a rational basis. -/
theorem exists_basis_of_submodule (S : Submodule ℚ ℝ) :
    ∃ (κ : Type) (b : κ → ℝ), LinearIndependent ℚ b ∧ Submodule.span ℚ (Set.range b) = S := by
  let B := Module.Basis.ofVectorSpace ℚ S
  refine ⟨_, fun j => ((B j : S) : ℝ), ?_, ?_⟩
  · have := B.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
    exact this
  · have h1 : Submodule.span ℚ (Set.range B) = ⊤ := B.span_eq
    have h2 := congrArg (Submodule.map S.subtype) h1
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at h2
    have h3 : (⇑S.subtype '' Set.range ⇑B) = Set.range fun j => ((B j : S) : ℝ) := by
      rw [← Set.range_comp]; rfl
    rw [← h3]; exact h2

instance RT.tau_group (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : IsTopologicalAddGroup (RT (tauT f S)) := by
  obtain ⟨κ, b, -, hS⟩ := exists_basis_of_submodule S
  exact RT.isTopologicalAddGroup_of_inducing _ (GTau f b) (GTau_inducing f S b hS)

/-! ### The literal isomorphisms with `UniformSpace.Completion` -/

/-- **`Comp(ℝ, σ_{f,S}) ≅ ℝ × K_S`**, literally: the abstract completion of the topological group
`(ℝ, σ_{f,S})` is isomorphic (as a uniform group) to `ℝ × K_S`, by an isomorphism extending `I_S`. -/
theorem completion_literal_sigma (f : ℝ →+ ℚ) (hf : f ≠ 0) (S : Submodule ℚ ℝ) :
    ∃ e : Completion (RT (sigmaT f S)) ≃+ (ℝ × PD S), UniformContinuous e ∧ UniformContinuous e.symm ∧
      ∀ x : ℝ, e ((show RT (sigmaT f S) from x : RT (sigmaT f S)) : Completion (RT (sigmaT f S))) =
        ISigma f S x := by
  obtain ⟨u, hu⟩ := exists_unit f hf
  let J : RT (sigmaT f S) →+ ℝ × PD S := ISigma f S
  have hind : IsInducing (J : RT (sigmaT f S) → ℝ × PD S) := ISigma_inducing f S
  exact completion_iso_completion J (AddMonoidHom.isUniformInducing_of_isInducing hind)
    (ISigma_denseRange f u hu S)

/-- **`Comp(ℝ, β_{f,S}) ≅ K_ℝ × K_S`**, literally. -/
theorem completion_literal_beta (f : ℝ →+ ℚ) (hf : f ≠ 0) (S : Submodule ℚ ℝ) :
    ∃ e : Completion (RT (betaT f S)) ≃+ (PD ℝ × PD S), UniformContinuous e ∧ UniformContinuous e.symm ∧
      ∀ x : ℝ, e ((show RT (betaT f S) from x : RT (betaT f S)) : Completion (RT (betaT f S))) =
        JBeta f S x := by
  obtain ⟨u, hu⟩ := exists_unit f hf
  let J : RT (betaT f S) →+ PD ℝ × PD S := JBeta f S
  have hind : IsInducing (J : RT (betaT f S) → PD ℝ × PD S) := JBeta_inducing f S
  exact completion_iso_completion J (AddMonoidHom.isUniformInducing_of_isInducing hind)
    (JBeta_denseRange f u hu S)

/-- **`Comp(ℝ, τ_{f,S}) ≅ ℝ × ℝ^B`**, literally, for a rational basis `B` of `S`. -/
theorem completion_literal_tau (f : ℝ →+ ℚ) (hf : f ≠ 0) (S : Submodule ℚ ℝ) {κ : Type} (b : κ → ℝ)
    (hli : LinearIndependent ℚ b) (hS : Submodule.span ℚ (Set.range b) = S) :
    ∃ e : Completion (RT (tauT f S)) ≃+ (ℝ × (κ → ℝ)), UniformContinuous e ∧ UniformContinuous e.symm ∧
      ∀ x : ℝ, e ((show RT (tauT f S) from x : RT (tauT f S)) : Completion (RT (tauT f S))) =
        GTau f b x := by
  let J : RT (tauT f S) →+ ℝ × (κ → ℝ) := GTau f b
  have hind : IsInducing (J : RT (tauT f S) → ℝ × (κ → ℝ)) := GTau_inducing f S b hS
  exact completion_iso_completion J (AddMonoidHom.isUniformInducing_of_isInducing hind)
    (GTau_denseRange f hf b hli)

instance RT.theta_group (S : Submodule ℚ ℝ) : IsTopologicalAddGroup (RT (thetaS S)) :=
  RT.isTopologicalAddGroup_of_inducing _ (eS S) (eS_inducing S)

/-- **`Comp(ℝ, θ_S) ≅ K_S`**, literally (in particular `Comp(ℝ, θ_ℚ) ≅ K_ℚ`). -/
theorem completion_literal_thetaS (S : Submodule ℚ ℝ) :
    ∃ e : Completion (RT (thetaS S)) ≃+ PD S, UniformContinuous e ∧ UniformContinuous e.symm ∧
      ∀ x : ℝ, e ((show RT (thetaS S) from x : RT (thetaS S)) : Completion (RT (thetaS S))) =
        eS S x := by
  let J : RT (thetaS S) →+ PD S := eS S
  have hind : IsInducing (J : RT (thetaS S) → PD S) := eS_inducing S
  exact completion_iso_completion J (AddMonoidHom.isUniformInducing_of_isInducing hind)
    (eS_denseRange S)

end LeanCheck
