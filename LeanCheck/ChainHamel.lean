import LeanCheck.ChainSaturation

/-!
# The Hamel-side topologies `β_{f,S}`, `σ_{f,S}`, `τ_{f,S}` (TVGQ-v7, §§ "Three topologies", "Characters",
"Strict separation", "Exact continuous scalar rings", "Order of the parameter spaces")

`f : ℝ →+ ℚ` is nonzero (`f u = 1`), `S` a nonzero `ℚ`-subspace of `ℝ`, `f_a(x) = f(a x)`.

* `β_{f,S} = init{ x ↦ p(b x), x ↦ p(f(a x)) : b ∈ ℝ, a ∈ S }`   (`betaT`)
* `σ_{f,S} = tu ∨ β_{f,S}`                                      (`sigmaT = TfS f S γ₀`)
* `τ_{f,S} = init{ id : ℝ → ℝ_usual, f_a : ℝ → ℚ_usual : a ∈ S }` (`tauT = TfS f S (usual ℚ)`)

Mathlib's `⊓` of topologies is the join, so `β ⊆ σ ⊆ τ` reads `τ ≤ σ ≤ β`.
-/

namespace LeanCheck

open Filter Topology

/-- The usual topology on `ℚ`. -/
noncomputable def usualQ : TopologicalSpace ℚ := inferInstance

/-- The circle-subspace topology on `ℚ/ℤ`. -/
noncomputable def circT : TopologicalSpace TorsA := inferInstance

/-- `γ₀ = gam` of the circle topology (the topology of `Γ`-observations on `ℚ`). -/
lemma gamma0_eq_gam : gamma0 = gam circT := by
  unfold gamma0 gam circT
  refine iInf_congr fun r => ?_
  rw [show (inferInstance : TopologicalSpace TorsA) = TopologicalSpace.induced Subtype.val circTop from rfl,
    induced_compose]
  rfl

lemma circT_group : @IsTopologicalAddGroup TorsA circT _ := by
  unfold circT; infer_instance

lemma gamma0_group : @IsTopologicalAddGroup ℚ gamma0 _ := by
  rw [gamma0_eq_gam]; exact gam_group circT circT_group

lemma gamma0_scalar (s : ℚ) : Continuous[gamma0, gamma0] (fun x : ℚ => s * x) := by
  rw [gamma0_eq_gam]; exact gam_scalar circT s

lemma usualQ_group : @IsTopologicalAddGroup ℚ usualQ _ := by unfold usualQ; infer_instance

lemma usualQ_scalar (s : ℚ) : Continuous[usualQ, usualQ] (fun x : ℚ => s * x) := by
  unfold usualQ; exact continuous_const.mul continuous_id

/-- `usualQ` is finer than `γ₀` (the characters `p(r ·)` are usual-continuous). -/
lemma usualQ_le_gamma0 : usualQ ≤ gamma0 := by
  unfold gamma0
  refine le_iInf fun r => ?_
  rw [← continuous_iff_le_induced]
  unfold usualQ
  exact continuous_coe_circ.comp (Rat.continuous_coe_real.comp (continuous_const.mul continuous_id))

/-! ### The family `TfS` -/

/-- `init{ id, f_a : a ∈ S }` with target `(ℚ, δ)`. -/
noncomputable def TfS (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ) : TopologicalSpace ℝ :=
  (inferInstance : TopologicalSpace ℝ) ⊓ ⨅ a : S, TopologicalSpace.induced (fa f (a : ℝ)) δ

/-- `τ_{f,S}`. -/
noncomputable def tauT (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : TopologicalSpace ℝ := TfS f S usualQ

/-- `σ_{f,S}`. -/
noncomputable def sigmaT (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : TopologicalSpace ℝ := TfS f S gamma0

/-- `β_{f,S}`. -/
noncomputable def betaT (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : TopologicalSpace ℝ :=
  (⨅ b : ℝ, TopologicalSpace.induced (fun x : ℝ => ((b * x : ℝ) : Circ)) circTop) ⊓
    ⨅ a : S, TopologicalSpace.induced (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop

lemma TfS_le_usual (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ) :
    TfS f S δ ≤ (inferInstance : TopologicalSpace ℝ) := inf_le_left

lemma faS_cont (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ) (a : S) :
    Continuous[TfS f S δ, δ] (fa f (a : ℝ)) :=
  continuous_iff_le_induced.mpr (inf_le_right.trans (iInf_le _ a))

lemma TfS_group (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ)
    (h : @IsTopologicalAddGroup ℚ δ _) : @IsTopologicalAddGroup ℝ (TfS f S δ) _ := by
  unfold TfS
  letI : TopologicalSpace ℚ := δ
  haveI : IsTopologicalAddGroup ℚ := h
  exact isTopologicalAddGroup_inf inferInstance
    (isTopologicalAddGroup_iInf (fun a => isTopologicalAddGroup_induced (fa f (a : ℝ))))

lemma TfS_t2 (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ) : @T2Space ℝ (TfS f S δ) := by
  have hc : Continuous[TfS f S δ, (inferInstance : TopologicalSpace ℝ)] (id : ℝ → ℝ) :=
    continuous_iff_le_induced.mpr (by rw [induced_id]; exact TfS_le_usual f S δ)
  exact @T2Space.of_injective_continuous ℝ ℝ (TfS f S δ) _ _ id Function.injective_id hc

/-- If `c S ⊆ S` then the real dilation `x ↦ c x` is continuous. -/
lemma TfS_dilation (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ) (c : ℝ)
    (hc : ∀ a ∈ S, a * c ∈ S) : Continuous[TfS f S δ, TfS f S δ] (fun x : ℝ => c * x) := by
  have h1 : Continuous[TfS f S δ, (inferInstance : TopologicalSpace ℝ)] (fun x : ℝ => c * x) :=
    continuous_inf_dom_left (continuous_const.mul continuous_id)
  have h2 : Continuous[TfS f S δ, ⨅ a : S, TopologicalSpace.induced (fa f (a : ℝ)) δ]
      (fun x : ℝ => c * x) := by
    refine continuous_iInf_rng.2 (fun a => continuous_induced_rng.2 ?_)
    have : (fa f (a : ℝ) ∘ fun x : ℝ => c * x) = fa f ((a : ℝ) * c) := by
      funext x; simp only [Function.comp, fa_apply]; rw [mul_assoc]
    rw [this]
    exact faS_cont f S δ ⟨(a : ℝ) * c, hc a a.2⟩
  exact continuous_inf_rng.2 ⟨h1, h2⟩

lemma TfS_mono (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) {δ δ' : TopologicalSpace ℚ} (h : δ ≤ δ') :
    TfS f S δ ≤ TfS f S δ' :=
  inf_le_inf_left _ (iInf_mono fun a => induced_mono h)

/-- Larger parameter space, finer topology. -/
lemma TfS_mono_S (f : ℝ →+ ℚ) {S T : Submodule ℚ ℝ} (h : S ≤ T) (δ : TopologicalSpace ℚ) :
    TfS f T δ ≤ TfS f S δ :=
  inf_le_inf_left _ (le_iInf fun a : S => iInf_le (fun b : T => TopologicalSpace.induced (fa f (b : ℝ)) δ) ⟨(a : ℝ), h a.2⟩)

/-! ### Relations between `β`, `σ`, `τ` -/

/-- The character `ℚ → 𝕋`, `s ↦ s mod 1`, as a homomorphism. -/
noncomputable def psi0 : ℚ →+ Circ := (AddCommGroup.torsion Circ).subtype.comp piHom

lemma psi0_apply (s : ℚ) : psi0 s = ((s : ℝ) : Circ) := by simp [psi0, piHom_coe]

/-- `x ↦ p(f(a x))` as a homomorphism `ℝ →+ 𝕋`. -/
noncomputable def pfHom (f : ℝ →+ ℚ) (a : ℝ) : ℝ →+ Circ := psi0.comp (fa f a)

lemma pfHom_apply (f : ℝ →+ ℚ) (a x : ℝ) : pfHom f a x = (((f (a * x) : ℚ) : ℝ) : Circ) := by
  simp [pfHom, psi0_apply, fa_apply]

lemma iInf_gamma0_eq (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    (⨅ a : S, TopologicalSpace.induced (fa f (a : ℝ)) gamma0) =
      ⨅ a : S, TopologicalSpace.induced (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop := by
  have step : ∀ a : S, TopologicalSpace.induced (fa f (a : ℝ)) gamma0 =
      ⨅ r : ℚ, TopologicalSpace.induced (fun x : ℝ => (((r * f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop := by
    intro a
    unfold gamma0
    rw [induced_iInf]
    refine iInf_congr fun r => ?_
    rw [induced_compose]
    rfl
  simp_rw [step]
  apply le_antisymm
  · refine le_iInf fun a => ?_
    refine iInf_le_of_le a (iInf_le_of_le 1 ?_)
    have : (fun x : ℝ => (((1 * f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) =
        fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ) := by funext x; simp
    rw [this]
  · refine le_iInf fun a => le_iInf fun r => ?_
    have hmem : (r : ℝ) * (a : ℝ) ∈ S := by
      have := S.smul_mem r a.2
      simpa [Rat.smul_def] using this
    refine iInf_le_of_le ⟨(r : ℝ) * (a : ℝ), hmem⟩ ?_
    have : (fun x : ℝ => (((f (((r : ℝ) * (a : ℝ)) * x) : ℚ) : ℝ) : Circ)) =
        fun x : ℝ => (((r * f ((a : ℝ) * x) : ℚ) : ℝ) : Circ) := by
      funext x
      rw [mul_assoc, f_ratmul]
    simp only [this]
    exact le_rfl

/-- `σ_{f,S} = tu ∨ β_{f,S}`. -/
theorem sigmaT_eq (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    sigmaT f S = (inferInstance : TopologicalSpace ℝ) ⊓ betaT f S := by
  have hB : (inferInstance : TopologicalSpace ℝ) ≤
      ⨅ b : ℝ, TopologicalSpace.induced (fun x : ℝ => ((b * x : ℝ) : Circ)) circTop :=
    le_iInf fun b => continuous_iff_le_induced.mp
      (continuous_coe_circ.comp (continuous_const.mul continuous_id))
  unfold sigmaT TfS betaT
  rw [iInf_gamma0_eq, ← inf_assoc, inf_eq_left.mpr hB]

theorem tauT_le_sigmaT (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : tauT f S ≤ sigmaT f S :=
  TfS_mono f S usualQ_le_gamma0

theorem sigmaT_le_betaT (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : sigmaT f S ≤ betaT f S := by
  rw [sigmaT_eq]; exact inf_le_right

theorem sigmaT_le_usual (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    sigmaT f S ≤ (inferInstance : TopologicalSpace ℝ) := TfS_le_usual f S _ 

theorem tauT_le_betaT (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : tauT f S ≤ betaT f S :=
  (tauT_le_sigmaT f S).trans (sigmaT_le_betaT f S)

/-- `p ∘ f_a` is `β_{f,S}`-continuous for `a ∈ S` (and hence `σ`- and `τ`-continuous). -/
lemma pfHom_cont_beta (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (a : S) :
    @Continuous ℝ Circ (betaT f S) circTop (pfHom f (a : ℝ)) :=
  continuous_iff_le_induced.mpr (inf_le_right.trans (iInf_le (fun a : S => TopologicalSpace.induced
    (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop) a))

lemma cmulHom_cont_beta (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (b : ℝ) :
    @Continuous ℝ Circ (betaT f S) circTop (cmulHom b) :=
  continuous_iff_le_induced.mpr (inf_le_left.trans (iInf_le (fun b : ℝ => TopologicalSpace.induced
    (fun x : ℝ => ((b * x : ℝ) : Circ)) circTop) b))

lemma betaT_group (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : @IsTopologicalAddGroup ℝ (betaT f S) _ := by
  unfold betaT
  exact isTopologicalAddGroup_inf
    (isTopologicalAddGroup_iInf (fun b => isTopologicalAddGroup_induced (cmulHom b)))
    (isTopologicalAddGroup_iInf (fun a : S => isTopologicalAddGroup_induced (pfHom f (a : ℝ))))

/-- `β_{f,S}` is Hausdorff: the ordinary characters `x ↦ p(b x)` separate points. -/
lemma betaT_t2 (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : @T2Space ℝ (betaT f S) := by
  have hc : Continuous[betaT f S, Pi.topologicalSpace]
      (fun x : ℝ => fun b : ℝ => ((b * x : ℝ) : Circ)) := by
    exact @continuous_pi ℝ ℝ (fun _ : ℝ => Circ) (betaT f S) (fun _ => circTop) _
      (fun b => cmulHom_cont_beta f S b)
  have hinj : Function.Injective (fun x : ℝ => fun b : ℝ => ((b * x : ℝ) : Circ)) := by
    intro x y hxy
    by_contra hne
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h := congrFun hxy (1 / (2 * (x - y)))
    have h0 : ((1 / (2 * (x - y)) * (x - y) : ℝ) : Circ) = 0 := by
      rw [mul_sub, AddCircle.coe_sub]
      simp only at h
      rw [h, sub_self]
    have : 1 / (2 * (x - y)) * (x - y) = 1 / 2 := by field_simp
    rw [this] at h0
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h0
    rw [zsmul_eq_mul, mul_one] at hn
    have h3 : (2 : ℝ) * n = 1 := by linarith
    have h4 : (2 : ℤ) * n = 1 := by exact_mod_cast h3
    omega
  exact @T2Space.of_injective_continuous ℝ _ (betaT f S) _ _ _ hinj hc

/-- Rational dilations are continuous for all three topologies (TVGQ). -/
theorem TfS_ratdil (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ) (q : ℚ) :
    Continuous[TfS f S δ, TfS f S δ] (fun x : ℝ => (q : ℝ) * x) :=
  TfS_dilation f S δ (q : ℝ) (fun a ha => by
    have := S.smul_mem q ha
    simpa [Rat.smul_def, mul_comm] using this)

end LeanCheck
