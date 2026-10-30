import LeanCheck.ChainIso7
import LeanCheck.ChainKronecker

/-!
# Completions (TVGQ-v7, Section "Completions and the full modular character groups")

`PD A = Hom(A_d, 𝕋)` is the Pontryagin dual of the discrete group `A`, with the topology of pointwise
convergence; `K_S = PD S`, `K_ℝ = PD ℝ`.  This file sets up `PD` as a compact Hausdorff (hence complete)
uniform additive group, the embeddings
`e(x)(b) = p(bx)`, `j_S(x)(a) = p(f(ax))`, and shows that they induce exactly `β_{f,S}` and `σ_{f,S}`.
-/

namespace LeanCheck

open Filter Topology

/-! ### The dual of a discrete group -/

/-- Pontryagin dual of the discrete group `A`: all homomorphisms `A → 𝕋`. -/
abbrev PD (A : Type) [AddCommGroup A] : Type := A →+ Circ

/-- Pointwise evaluation. -/
def pdFun {A : Type} [AddCommGroup A] (φ : PD A) : A → Circ := fun a => φ a

noncomputable instance PD.instUniformSpace (A : Type) [AddCommGroup A] : UniformSpace (PD A) :=
  UniformSpace.comap pdFun inferInstance

/-- Evaluation as a homomorphism into the product of circles. -/
def pdHom (A : Type) [AddCommGroup A] : PD A →+ (A → Circ) where
  toFun := pdFun
  map_zero' := rfl
  map_add' _ _ := rfl

lemma pdHom_apply {A : Type} [AddCommGroup A] (φ : PD A) (a : A) : pdHom A φ a = φ a := rfl

lemma pd_isInducing (A : Type) [AddCommGroup A] : IsInducing (pdFun : PD A → (A → Circ)) := ⟨rfl⟩

lemma pd_injective (A : Type) [AddCommGroup A] : Function.Injective (pdFun : PD A → (A → Circ)) := by
  intro φ ψ h
  ext a
  exact congrFun h a

instance PD.isUniformAddGroup (A : Type) [AddCommGroup A] : IsUniformAddGroup (PD A) :=
  IsUniformAddGroup.comap (pdHom A)

instance PD.t2 (A : Type) [AddCommGroup A] : T2Space (PD A) :=
  (Topology.IsEmbedding.mk (pd_isInducing A) (pd_injective A)).t2Space

lemma pd_isClosedEmbedding (A : Type) [AddCommGroup A] : IsClosedEmbedding (pdFun : PD A → (A → Circ)) := by
  refine ⟨⟨pd_isInducing A, pd_injective A⟩, ?_⟩
  have : Set.range (pdFun : PD A → (A → Circ)) =
      ⋂ p : A × A, {g : A → Circ | g (p.1 + p.2) = g p.1 + g p.2} := by
    ext g
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨φ, rfl⟩ p
      exact map_add φ p.1 p.2
    · intro h
      exact ⟨AddMonoidHom.mk' g (fun a b => h (a, b)), rfl⟩
  rw [this]
  exact isClosed_iInter fun p =>
    isClosed_eq (continuous_apply (p.1 + p.2)) ((continuous_apply p.1).add (continuous_apply p.2))

instance PD.compact (A : Type) [AddCommGroup A] : CompactSpace (PD A) :=
  (pd_isClosedEmbedding A).compactSpace

instance PD.complete (A : Type) [AddCommGroup A] : CompleteSpace (PD A) := complete_of_compact

/-! ### The embeddings `e` and `j_S` -/

/-- `e(x)(b) = p(b x)`. -/
noncomputable def eFun (x : ℝ) : PD ℝ :=
  AddMonoidHom.mk' (fun b : ℝ => ((b * x : ℝ) : Circ)) (fun a b => by
    rw [add_mul]; exact AddCircle.coe_add (𝕜 := ℝ) (p := (1 : ℝ)) _ _)

lemma eFun_apply (x b : ℝ) : eFun x b = ((b * x : ℝ) : Circ) := rfl

noncomputable def eHom : ℝ →+ PD ℝ where
  toFun := eFun
  map_zero' := by ext b; simp [eFun_apply]
  map_add' x y := by
    ext b
    simp only [eFun_apply, AddMonoidHom.add_apply, mul_add]
    exact AddCircle.coe_add (𝕜 := ℝ) (p := (1 : ℝ)) _ _

lemma eHom_apply (x b : ℝ) : eHom x b = ((b * x : ℝ) : Circ) := rfl

/-- `j_S(x)(a) = p(f(a x))`. -/
noncomputable def jFun (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (x : ℝ) : PD S :=
  AddMonoidHom.mk' (fun a : S => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) (fun a b => by
    simp only [Submodule.coe_add, add_mul, map_add, Rat.cast_add]
    exact AddCircle.coe_add (𝕜 := ℝ) (p := (1 : ℝ)) _ _)

lemma jFun_apply (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (x : ℝ) (a : S) :
    jFun f S x a = (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ) := rfl

noncomputable def jHom (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : ℝ →+ PD S where
  toFun := jFun f S
  map_zero' := by ext a; simp [jFun_apply]
  map_add' x y := by
    ext a
    simp only [jFun_apply, AddMonoidHom.add_apply, mul_add, map_add, Rat.cast_add]
    exact AddCircle.coe_add (𝕜 := ℝ) (p := (1 : ℝ)) _ _

lemma jHom_apply (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (x : ℝ) (a : S) :
    jHom f S x a = (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ) := rfl

/-- `I_S(x) = (x, j_S(x))`, the embedding for `σ_{f,S}`. -/
noncomputable def ISigma (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : ℝ →+ ℝ × PD S :=
  AddMonoidHom.prod (AddMonoidHom.id ℝ) (jHom f S)

/-- `J_S(x) = (e(x), j_S(x))`, the embedding for `β_{f,S}`. -/
noncomputable def JBeta (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : ℝ →+ PD ℝ × PD S :=
  AddMonoidHom.prod eHom (jHom f S)

/-! ### The embeddings induce `σ_{f,S}` and `β_{f,S}` -/

lemma iInf_sigma_form (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    sigmaT f S = (inferInstance : TopologicalSpace ℝ) ⊓
      ⨅ a : S, TopologicalSpace.induced (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop := by
  unfold sigmaT TfS
  rw [iInf_gamma0_eq]

lemma induced_jHom (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    TopologicalSpace.induced (jHom f S) (inferInstance : TopologicalSpace (PD S)) =
      ⨅ a : S, TopologicalSpace.induced (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop := by
  show TopologicalSpace.induced (jHom f S) (TopologicalSpace.induced pdFun inferInstance) = _
  rw [induced_compose]
  show TopologicalSpace.induced (fun x a => jHom f S x a) (Pi.topologicalSpace) = _
  rw [Pi.topologicalSpace, induced_iInf]
  refine iInf_congr fun a => ?_
  rw [induced_compose]
  rfl

lemma induced_eHom :
    TopologicalSpace.induced eHom (inferInstance : TopologicalSpace (PD ℝ)) =
      ⨅ b : ℝ, TopologicalSpace.induced (fun x : ℝ => ((b * x : ℝ) : Circ)) circTop := by
  show TopologicalSpace.induced eHom (TopologicalSpace.induced pdFun inferInstance) = _
  rw [induced_compose]
  show TopologicalSpace.induced (fun x b => eHom x b) (Pi.topologicalSpace) = _
  rw [Pi.topologicalSpace, induced_iInf]
  refine iInf_congr fun b => ?_
  rw [induced_compose]
  rfl

/-- The embedding `I_S` induces `σ_{f,S}`. -/
theorem ISigma_inducing (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    @IsInducing ℝ (ℝ × PD S) (sigmaT f S) _ (ISigma f S) := by
  refine @IsInducing.mk ℝ (ℝ × PD S) (sigmaT f S) _ _ ?_
  rw [iInf_sigma_form, ← induced_jHom]
  show _ = TopologicalSpace.induced (ISigma f S)
    (TopologicalSpace.induced Prod.fst _ ⊓ TopologicalSpace.induced Prod.snd _)
  rw [induced_inf, induced_compose, induced_compose]
  rw [show (Prod.fst ∘ ⇑(ISigma f S)) = id from rfl, induced_id]
  rfl

/-- The embedding `J_S` induces `β_{f,S}`. -/
theorem JBeta_inducing (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    @IsInducing ℝ (PD ℝ × PD S) (betaT f S) _ (JBeta f S) := by
  refine @IsInducing.mk ℝ (PD ℝ × PD S) (betaT f S) _ _ ?_
  unfold betaT
  rw [← induced_jHom, ← induced_eHom]
  show _ = TopologicalSpace.induced (JBeta f S)
    (TopologicalSpace.induced Prod.fst _ ⊓ TopologicalSpace.induced Prod.snd _)
  rw [induced_inf, induced_compose, induced_compose]
  rfl

end LeanCheck
