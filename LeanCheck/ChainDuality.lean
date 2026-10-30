import LeanCheck.ChainDualityCore

/-!
# The duality fact (F1): the dual of `θ_H` is exactly `H`

`fourier_reduction`: a character `χ` of an abelian group `G` that is small on the preimage of a neighbourhood of
`0` under `Φ : G → 𝕋^I` is an integer combination of the coordinates of `Φ`.  (Closure of the image of `(Φ, χ)` is a
compact subgroup of `𝕋^I × 𝕋` on which the coordinates of `Φ` separate points; apply `char_in_span`.)

`dual_theta_iff`: for every subgroup `H` of `𝒜 = Hom(ℝ, 𝕋)`, a character is `θ_H`-continuous iff it lies in `H`.
This proves the first of the two standard facts assumed in `PrecompactDuality`.
-/

namespace LeanCheck

open Filter Topology MeasureTheory

theorem fourier_reduction {G : Type} [AddCommGroup G] {I : Type} [Fintype I]
    (Φ : G →+ (I → Circ)) (χ : G →+ Circ) (U : Set (I → Circ)) (hU : U ∈ 𝓝 (0 : I → Circ))
    (hχ : ∀ x, Φ x ∈ U → ‖χ x‖ < 1 / 4) :
    ∃ k : I → ℤ, ∀ x, χ x = ∑ i, k i • Φ x i := by
  classical
  let Ψ : G →+ ((I → Circ) × Circ) := AddMonoidHom.prod Φ χ
  let Λ : AddSubgroup ((I → Circ) × Circ) := Ψ.range.topologicalClosure
  have hΛ : IsClosed (Λ : Set ((I → Circ) × Circ)) := AddSubgroup.isClosed_topologicalClosure _
  haveI : CompactSpace Λ := isCompact_iff_compactSpace.mp hΛ.isCompact
  -- the closure lies in `C = {e | e.1 ∈ interior U → ‖e.2‖ ≤ 1/4}`
  let C : Set ((I → Circ) × Circ) := {e | e.1 ∈ interior U → ‖e.2‖ ≤ 1 / 4}
  have hCclosed : IsClosed C := by
    have : C = {e : (I → Circ) × Circ | e.1 ∉ interior U} ∪ {e | ‖e.2‖ ≤ 1 / 4} := by
      ext e; simp [C, imp_iff_not_or]
    rw [this]
    exact IsClosed.union (isOpen_interior.preimage continuous_fst).isClosed_compl
      (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)
  have hrangeC : (Ψ.range : Set ((I → Circ) × Circ)) ⊆ C := by
    rintro _ ⟨x, rfl⟩ h
    exact (hχ x (interior_subset h)).le
  have hΛC : (Λ : Set ((I → Circ) × Circ)) ⊆ C := by
    have : (Λ : Set ((I → Circ) × Circ)) = closure (Ψ.range : Set ((I → Circ) × Circ)) :=
      AddSubgroup.topologicalClosure_coe
    rw [this]
    exact closure_minimal hrangeC hCclosed
  have h0 : (0 : I → Circ) ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  -- coordinates
  let z : I → (Λ →+ Circ) := fun i =>
    (Pi.evalAddMonoidHom (fun _ : I => Circ) i).comp ((AddMonoidHom.fst _ _).comp Λ.subtype)
  let w : Λ →+ Circ := (AddMonoidHom.snd _ _).comp Λ.subtype
  have hz : ∀ i, Continuous (z i) := fun i =>
    (continuous_apply i).comp (continuous_fst.comp continuous_subtype_val)
  have hw : Continuous w := continuous_snd.comp continuous_subtype_val
  have hsep : ∀ p q : Λ, (∀ i, z i p = z i q) → p = q := by
    intro p q hpq
    have hd1 : ((p - q : Λ) : (I → Circ) × Circ).1 = 0 := by
      funext i
      have := hpq i
      simp only [z, AddMonoidHom.coe_comp, Function.comp_apply, Pi.evalAddMonoidHom_apply,
        AddMonoidHom.coe_fst, AddSubgroup.coe_subtype] at this
      simp [this]
    have hbound : ∀ n : ℕ, ‖(n : ℕ) • ((p - q : Λ) : (I → Circ) × Circ).2‖ ≤ 1 / 4 := by
      intro n
      have := hΛC (n • (p - q) : Λ).2
      have h1 : (((n • (p - q) : Λ)) : (I → Circ) × Circ).1 = 0 := by
        simp only [AddSubgroup.coe_nsmul, Prod.smul_fst, hd1, smul_zero]
      have h2 := this (by rw [h1]; exact h0)
      simpa only [AddSubgroup.coe_nsmul, Prod.smul_snd] using h2
    have hd2 : ((p - q : Λ) : (I → Circ) × Circ).2 = 0 := by
      by_contra hne
      have hpos : 0 < ‖((p - q : Λ) : (I → Circ) × Circ).2‖ := norm_pos_iff.mpr hne
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (4 * ‖((p - q : Λ) : (I → Circ) × Circ).2‖))
      have hm := mult_le _ n (fun j _ => hbound j)
      have hn' : 1 / 4 < (n : ℝ) * ‖((p - q : Λ) : (I → Circ) × Circ).2‖ := by
        rw [div_lt_iff₀ (by positivity)] at hn
        nlinarith
      linarith
    have : p - q = 0 := by
      apply Subtype.ext
      exact Prod.ext hd1 hd2
    exact sub_eq_zero.mp this
  obtain ⟨k, hk⟩ := char_in_span z hz hsep w hw
  refine ⟨k, fun x => ?_⟩
  have := hk ⟨Ψ x, subset_closure ⟨x, rfl⟩⟩
  simpa [z, w, Ψ] using this

/-- **(F1)**: a character of `ℝ` is `θ_H`-continuous iff it lies in the subgroup `H` of `𝒜`. -/
theorem dual_theta_iff (H : AddSubgroup Chars) (χ : Chars) :
    @Continuous ℝ Circ (theta (H : Set Chars)) circTop χ ↔ χ ∈ H := by
  constructor
  · intro hχ
    have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (χ 0) := by
      rw [map_zero]
      exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
    have hpre : χ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} ∈ @nhds ℝ (theta (H : Set Chars)) 0 :=
      (@Continuous.continuousAt ℝ Circ (theta (H : Set Chars)) circTop χ 0 hχ) hS
    obtain ⟨I, W, hW, hsub⟩ := theta_nhds_sub (H : Set Chars) _ hpre
    let Φ : ℝ →+ (I → Circ) :=
      { toFun := fun x i => (i.1.1 : Chars) x
        map_zero' := by ext; simp
        map_add' := by intro x y; ext; simp }
    let U : Set (I → Circ) := Set.pi Set.univ (fun i : I => W i.1)
    have hU : U ∈ 𝓝 (0 : I → Circ) := set_pi_mem_nhds Set.finite_univ (fun i _ => hW i.1)
    obtain ⟨k, hk⟩ := fourier_reduction Φ χ U hU (fun x hx => by
      have : x ∈ {x : ℝ | ∀ i ∈ I, (i : Chars) x ∈ W i} := fun i hi => hx ⟨i, hi⟩ (Set.mem_univ _)
      exact hsub this)
    have heq : χ = ∑ i : I, k i • (i.1.1 : Chars) := by
      ext x
      rw [hk x]
      simp [Φ]
    rw [heq]
    exact AddSubgroup.sum_mem _ (fun i _ => AddSubgroup.zsmul_mem _ i.1.2 _)
  · intro h
    exact theta_cont_of_mem _ χ h

/-- The first field of `PrecompactDuality` holds unconditionally. -/
theorem dual_theta_all (H : AddSubgroup Chars) (_hs : Separates (H : Set Chars)) (χ : Chars) :
    @Continuous ℝ Circ (theta (H : Set Chars)) circTop χ ↔ χ ∈ H := dual_theta_iff H χ

/-- Only (F2) remains an assumption: it implies the full `PrecompactDuality`. -/
theorem PrecompactDuality.of_generated
    (hg : ∀ (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _), @T2Space ℝ τ →
      Precompact τ → τ = theta (dualGroup τ hτ : Set Chars)) : PrecompactDuality :=
  ⟨dual_theta_all, hg⟩

/-- **(F1) holds unconditionally.** -/
theorem dualThetaFact : DualThetaFact := dual_theta_all

/-- Unconditional forms of the theorems that only used (F1). -/
theorem theta_injective_unc (H H' : AddSubgroup Chars) (hs : Separates (H : Set Chars))
    (hs' : Separates (H' : Set Chars)) (h : theta (H : Set Chars) = theta (H' : Set Chars)) : H = H' :=
  theta_injective dualThetaFact H H' hs hs' h

theorem theta_le_iff_unc (H H' : AddSubgroup Chars) (hs : Separates (H : Set Chars))
    (hs' : Separates (H' : Set Chars)) :
    theta (H' : Set Chars) ≤ theta (H : Set Chars) ↔ H ≤ H' :=
  theta_le_iff dualThetaFact H H' hs hs'

theorem theta_scalar_unc (H : AddSubgroup Chars) (hs : Separates (H : Set Chars)) (a : ℝ) :
    Continuous[theta (H : Set Chars), theta (H : Set Chars)] (fun x : ℝ => a * x) ↔
      ∀ χ ∈ H, χ.comp (AddMonoidHom.mulLeft a) ∈ H :=
  theta_scalar dualThetaFact H hs a

/-- `C_{θ_ℚ} = ℚ`, unconditionally. -/
theorem thetaQ_scalar_unc (a : ℝ) :
    Continuous[thetaQ, thetaQ] (fun x : ℝ => a * x) ↔ ∃ q : ℚ, a = q :=
  thetaQ_scalar dualThetaFact a

/-- `θ_ℚ` is strictly coarser than the Bohr topology, unconditionally. -/
theorem thetaQ_lt_bohr_unc : theta (HR : Set Chars) < thetaQ := thetaQ_lt_bohr dualThetaFact

/-! ### The real-scalar (TVG) classification -/

/-- Invariance of a character set under all real rescalings of the argument. -/
def RealInv (H : Set Chars) : Prop := ∀ χ ∈ H, ∀ a : ℝ, χ.comp (AddMonoidHom.mulLeft a) ∈ H

/-- A Hausdorff precompact TVG topology (all fixed real dilations continuous). -/
def PTVG (τ : TopologicalSpace ℝ) : Prop :=
  @IsTopologicalAddGroup ℝ τ _ ∧ @T2Space ℝ τ ∧ Precompact τ ∧
    ∀ a : ℝ, Continuous[τ, τ] (fun x : ℝ => a * x)

theorem theta_realdil (H : Set Chars) (hH : RealInv H) (a : ℝ) :
    Continuous[theta H, theta H] (fun x : ℝ => a * x) := by
  unfold theta
  refine continuous_iInf_rng.2 (fun χ => continuous_induced_rng.2 ?_)
  exact theta_cont_of_mem H (χ.1.comp (AddMonoidHom.mulLeft a)) (hH _ χ.2 a)

theorem theta_ptvg (H : Set Chars) (hs : Separates H) (hH : RealInv H) : PTVG (theta H) :=
  ⟨theta_group H, theta_t2 H hs, theta_precompact H, theta_realdil H hH⟩

theorem dualGroup_realInv (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _)
    (hq : ∀ a : ℝ, Continuous[τ, τ] (fun x : ℝ => a * x)) : RealInv (dualGroup τ hτ : Set Chars) := by
  intro χ hχ a
  have hχ' : @Continuous ℝ Circ τ circTop' χ := (mem_dualGroup τ hτ χ).1 hχ
  exact (mem_dualGroup τ hτ _).2
    (@Continuous.comp ℝ ℝ Circ τ τ circTop' (fun x : ℝ => a * x) (χ : ℝ → Circ) hχ' (hq a))

/-- **Classification of Hausdorff precompact TVG topologies** (real scalars): point-separating real vector
subspaces of `𝒜` correspond bijectively and order-preservingly to Hausdorff precompact TVG topologies.
Only the generation fact (F2) is assumed; (F1) is proved. -/
theorem classification_TVG (hF2 : GeneratedFact) :
    (∀ H : AddSubgroup Chars, Separates (H : Set Chars) → RealInv (H : Set Chars) →
      PTVG (theta (H : Set Chars))) ∧
    (∀ τ : TopologicalSpace ℝ, PTVG τ → ∃ H : AddSubgroup Chars,
      Separates (H : Set Chars) ∧ RealInv (H : Set Chars) ∧ τ = theta (H : Set Chars)) ∧
    (∀ H H' : AddSubgroup Chars, Separates (H : Set Chars) → Separates (H' : Set Chars) →
      (theta (H : Set Chars) = theta (H' : Set Chars) ↔ H = H')) ∧
    (∀ H H' : AddSubgroup Chars, Separates (H : Set Chars) → Separates (H' : Set Chars) →
      (theta (H' : Set Chars) ≤ theta (H : Set Chars) ↔ H ≤ H')) := by
  refine ⟨fun H hs hr => theta_ptvg _ hs hr, ?_, ?_, ?_⟩
  · rintro τ ⟨hg, ht, hp, hq⟩
    have hgen := hF2 τ hg ht hp
    refine ⟨dualGroup τ hg, ?_, dualGroup_realInv τ hg hq, hgen⟩
    apply sep_of_theta_t2
    rw [← hgen]; exact ht
  · intro H H' hs hs'
    constructor
    · exact theta_injective_unc H H' hs hs'
    · rintro rfl; rfl
  · intro H H' hs hs'
    exact theta_le_iff_unc H H' hs hs'

/-- **No greatest compatible TVG topology** for the real Hamel pair `(ℝ, H_f)`: the class of Hausdorff locally
quasi-convex TVG topologies with character group exactly `H_f` has no greatest member. -/
theorem no_greatest_compatible_TVG (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    ¬ ∃ μ : TopologicalSpace ℝ, (μ ∈ Lcls (Hset f ⊤ : Set Chars) ∧ ∀ a : ℝ, Continuous[μ, μ] (fun x : ℝ => a * x)) ∧
      ∀ τ : TopologicalSpace ℝ, (τ ∈ Lcls (Hset f ⊤ : Set Chars) ∧
        ∀ a : ℝ, Continuous[τ, τ] (fun x : ℝ => a * x)) → μ ≤ τ := by
  obtain ⟨T₁, T₂, hg1, hg2, ht1, ht2, hl1, hl2, -, -, hd1, hd2, hdu1, hdu2, φ, hφ, hφne⟩ :=
    transfer_capstone_Cf f u hu
  have hmem : ∀ χ : Chars, (∃ c a : ℝ, ∀ x : ℝ, χ x = chiH f c a x) ↔ χ ∈ (Hset f ⊤ : Set Chars) :=
    fun χ => ⟨fun ⟨c, a, h⟩ => ⟨c, a, Submodule.mem_top, h⟩, fun ⟨c, a, _, h⟩ => ⟨c, a, h⟩⟩
  have hL1 : T₁ ∈ Lcls (Hset f ⊤ : Set Chars) := ⟨hg1, ht1, hl1, fun χ => (hdu1 χ).trans (hmem χ)⟩
  have hL2 : T₂ ∈ Lcls (Hset f ⊤ : Set Chars) := ⟨hg2, ht2, hl2, fun χ => (hdu2 χ).trans (hmem χ)⟩
  rintro ⟨μ, ⟨hμ, -⟩, hgr⟩
  have hle : μ ≤ T₁ ⊓ T₂ := le_inf (hgr _ ⟨hL1, hd1⟩) (hgr _ ⟨hL2, hd2⟩)
  have hcont : @Continuous ℝ Circ μ circTop φ := continuous_le_dom hle hφ
  obtain ⟨c, a, -, h⟩ := (hμ.2.2.2 φ).mp hcont
  exact hφne ⟨c, a, h⟩

end LeanCheck
