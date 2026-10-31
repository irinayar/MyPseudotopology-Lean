import Mathlib
import LeanCheck.JAWeilB

/-!
# Weil's theorem for `ℤ`, part C: the eigencharacter

For a compact normed abelian group `G`, `g ∈ G` and `m : ℤ` with `m • g ≠ 0` there is `ζ` of modulus one with `ζ^m ≠ 1`
and a continuous function `F ≢ 0` with `F (x + g) = ζ F x`.

Proof: with `a = m • g`, `P = 1 - ½ tau a - ½ tau (-a)` and `T = C* P C` (compact, symmetric, `≠ 0` because `C` does not commute
with ... `tau a`-invariance fails, and `⟪P w, w⟫ = ½‖tau a w - w‖²`), a nonzero eigenvalue of `T` has a finite-dimensional
eigenspace, invariant under `tau g`, hence a joint eigenvector `h`.  If `ζ^m = 1` then `P h = 0` and `T h = 0`, a contradiction;
`F = C h` is continuous, nonzero, and satisfies `F (x + g) = ζ F x`.
-/

namespace LeanCheck
namespace JAWeil

open MeasureTheory Filter
open scoped BoundedContinuousFunction ComplexConjugate

variable {G : Type*} [NormedAddCommGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

noncomputable def tauL (a : G) : H G →L[ℂ] H G := (tau a).toContinuousLinearMap

lemma tauL_apply (a : G) (f : H G) : tauL a f = tau a f := rfl

/-- `P = 1 - ½ tau a - ½ tau (-a)`. -/
noncomputable def Pop (a : G) : H G →L[ℂ] H G :=
  ContinuousLinearMap.id ℂ _ - (1 / 2 : ℂ) • tauL a - (1 / 2 : ℂ) • tauL (-a)

lemma Pop_apply (a : G) (f : H G) :
    Pop a f = f - (1 / 2 : ℂ) • tau a f - (1 / 2 : ℂ) • tau (-a) f := rfl

/-- `T = C* P C`. -/
noncomputable def Top (a : G) : H G →L[ℂ] H G :=
  (ContinuousLinearMap.adjoint (Cop (G := G))).comp ((Pop a).comp Cop)

lemma tau_comm (a b : G) (f : H G) : tau a (tau b f) = tau b (tau a f) := by
  rw [tau_add, tau_add, add_comm]

lemma Pop_symm (a : G) (x y : H G) : inner ℂ (Pop a x) y = inner ℂ x (Pop a y) := by
  rw [Pop_apply, Pop_apply, inner_sub_left, inner_sub_left, inner_smul_left, inner_smul_left,
    inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right, tau_inner, tau_inner (-a),
    neg_neg]
  simp only [map_ofNat, map_inv₀, map_one, one_div]
  ring

lemma Pop_Cop (a : G) (x : H G) : Pop a (Cop x) = Cop (Pop a x) := by
  rw [Pop_apply, Pop_apply, map_sub, map_sub, map_smul, map_smul, Cop_tau, Cop_tau]

lemma Pop_tau (a g : G) (x : H G) : Pop a (tau g x) = tau g (Pop a x) := by
  rw [Pop_apply, Pop_apply, map_sub, map_sub, map_smul, map_smul, tau_comm a g, tau_comm (-a) g]

lemma Cop_adj_tau (a : G) (f : H G) :
    ContinuousLinearMap.adjoint (Cop (G := G)) (tau a f) =
      tau a (ContinuousLinearMap.adjoint (Cop (G := G)) f) := by
  apply ext_inner_right ℂ
  intro y
  calc inner ℂ (ContinuousLinearMap.adjoint (Cop (G := G)) (tau a f)) y
      = inner ℂ (tau a f) (Cop y) := ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = inner ℂ f (tau (-a) (Cop y)) := tau_inner _ _ _
    _ = inner ℂ f (Cop (tau (-a) y)) := by rw [Cop_tau]
    _ = inner ℂ (ContinuousLinearMap.adjoint (Cop (G := G)) f) (tau (-a) y) :=
        (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    _ = inner ℂ (tau a (ContinuousLinearMap.adjoint (Cop (G := G)) f)) y := (tau_inner a _ y).symm

lemma Top_symm (a : G) (x y : H G) : inner ℂ (Top a x) y = inner ℂ x (Top a y) := by
  unfold Top
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left, Pop_symm, ContinuousLinearMap.adjoint_inner_right]

lemma Top_compact (a : G) : IsCompactOperator (Top a : H G →L[ℂ] H G) := by
  have h := (Cop_compact (G := G)).clm_comp
    ((ContinuousLinearMap.adjoint (Cop (G := G))).comp (Pop a))
  have e : (Top a : H G → H G) =
      ⇑((ContinuousLinearMap.adjoint (Cop (G := G))).comp (Pop a)) ∘ ⇑(Cop (G := G)) := by
    funext x; rfl
  rw [e]; exact h

lemma Top_tau (a g : G) (x : H G) : Top a (tau g x) = tau g (Top a x) := by
  unfold Top
  simp only [ContinuousLinearMap.comp_apply]
  rw [Cop_tau, Pop_tau, Cop_adj_tau]

lemma Top_ne_zero (a : G) (ha : a ≠ 0) : Top a ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := Cop_tau_ne a ha
  intro hT
  set w := Cop g₀ with hw
  have h1 : tau a w ≠ w := by rw [hw, ← Cop_tau]; exact hg₀
  have h2 : inner ℂ (Top a g₀) g₀ = inner ℂ (Pop a w) w := by
    unfold Top; simp only [ContinuousLinearMap.comp_apply]; rw [ContinuousLinearMap.adjoint_inner_left]
  rw [hT] at h2
  simp only [ContinuousLinearMap.zero_apply, inner_zero_left] at h2
  have h3 : inner ℂ (Pop a w) w = (‖w‖ ^ 2 : ℝ) - (1 / 2 : ℂ) * inner ℂ (tau a w) w
      - (1 / 2 : ℂ) * (starRingEnd ℂ) (inner ℂ (tau a w) w) := by
    rw [Pop_apply, inner_sub_left, inner_sub_left, inner_smul_left, inner_smul_left, tau_inner (-a),
      neg_neg, inner_self_eq_norm_sq_to_K, inner_conj_symm]
    simp [map_ofNat]
  have h4 : ‖tau a w - w‖ ^ 2 = 2 * ‖w‖ ^ 2 - 2 * RCLike.re (inner ℂ (tau a w) w) := by
    rw [norm_sub_sq (𝕜 := ℂ), (tau a).norm_map]; ring
  have h5 : RCLike.re (inner ℂ (Pop a w) w) = ‖w‖ ^ 2 - RCLike.re (inner ℂ (tau a w) w) := by
    have hc : (inner ℂ w (tau a w)).re = (inner ℂ (tau a w) w).re := by
      have := inner_conj_symm (𝕜 := ℂ) w (tau a w)
      rw [← this]; exact Complex.conj_re _
    have hn : ((‖w‖ : ℂ) ^ 2).re = ‖w‖ ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
    rw [h3]
    simp
    linarith [hc, hn]
  have h6 : ‖tau a w - w‖ ^ 2 = 0 := by
    have : RCLike.re (inner ℂ (Pop a w) w) = 0 := by rw [← h2]; simp
    linarith
  have : tau a w - w = 0 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h6
    exact norm_eq_zero.mp this
  exact h1 (sub_eq_zero.mp this)

lemma tau_zsmul_eigen (g : G) (v : H G) (ζ : ℂ) (hζ : ζ ≠ 0) (hv : tau g v = ζ • v) (n : ℤ) :
    tau (n • g) v = ζ ^ n • v := by
  have hneg : tau (-g) v = ζ⁻¹ • v := by
    have h : tau (-g) (tau g v) = v := tau_neg_tau g v
    rw [hv, map_smul] at h
    have : ζ • tau (-g) v = v := h
    calc tau (-g) v = ζ⁻¹ • (ζ • tau (-g) v) := by rw [smul_smul, inv_mul_cancel₀ hζ, one_smul]
      _ = ζ⁻¹ • v := by rw [this]
  induction n using Int.induction_on with
  | zero => simp [tau_zero]
  | succ n ih =>
    have : ((n : ℤ) + 1) • g = (n : ℤ) • g + g := by rw [add_smul, one_smul]
    rw [this, ← tau_add, hv, map_smul, ih, smul_smul, zpow_add_one₀ hζ, mul_comm]
  | pred n ih =>
    have : (-(n : ℤ) - 1) • g = (-(n : ℤ)) • g + (-g) := by
      rw [sub_smul, one_smul, sub_eq_add_neg]
    rw [this, ← tau_add, hneg, map_smul, ih, smul_smul, zpow_sub_one₀ hζ, mul_comm]

/-- **Weil's theorem, abstract form.**  For `m • g ≠ 0` there is an eigencharacter `ζ` of the translation by `g` with
`ζ^m ≠ 1`, realised by a continuous function `F ≢ 0` with `F (x + g) = ζ F x`. -/
theorem weil_abstract (g : G) (m : ℤ) (hm : m • g ≠ 0) :
    ∃ (ζ : ℂ) (F : G → ℂ), ‖ζ‖ = 1 ∧ ζ ^ m ≠ 1 ∧ Continuous F ∧ (∃ x₀, F x₀ ≠ 0) ∧
      ∀ x, F (x + g) = ζ * F x := by
  classical
  set a : G := m • g with ha
  have hTc := Top_compact a
  have hTs : (Top a : H G →ₗ[ℂ] H G).IsSymmetric := fun x y => Top_symm a x y
  obtain ⟨μ, hμev, hμ0⟩ : ∃ μ, Module.End.HasEigenvalue (Top a : Module.End ℂ (H G)) μ ∧ μ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact Top_ne_zero a hm
      ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hTc hTs).mp hcon)
  haveI hfd : FiniteDimensional ℂ (Module.End.eigenspace (Top a : Module.End ℂ (H G)) μ) :=
    ContinuousLinearMap.finite_dimensional_eigenspace hTc μ hμ0
  obtain ⟨v₀, hv₀⟩ := hμev.exists_hasEigenvector
  haveI : Nontrivial (Module.End.eigenspace (Top a : Module.End ℂ (H G)) μ) :=
    ⟨⟨⟨v₀, hv₀.1⟩, 0, fun h => hv₀.2 (by simpa using congrArg Subtype.val h)⟩⟩
  have hmaps : ∀ x ∈ Module.End.eigenspace (Top a : Module.End ℂ (H G)) μ,
      tau g x ∈ Module.End.eigenspace (Top a : Module.End ℂ (H G)) μ := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    show Top a (tau g x) = μ • tau g x
    rw [Top_tau]
    have hx' : Top a x = μ • x := hx
    rw [hx', map_smul]
  let S : Module.End.eigenspace (Top a : Module.End ℂ (H G)) μ →ₗ[ℂ]
      Module.End.eigenspace (Top a : Module.End ℂ (H G)) μ := (tau g).toLinearMap.restrict hmaps
  obtain ⟨ζ, hζ⟩ := Module.End.exists_eigenvalue S
  obtain ⟨v, hv⟩ := hζ.exists_hasEigenvector
  have hv1 : tau g (v : H G) = ζ • (v : H G) := by
    have := Module.End.mem_eigenspace_iff.mp hv.1
    exact congrArg Subtype.val this
  have hh0 : (v : H G) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hTh : Top a (v : H G) = μ • (v : H G) := Module.End.mem_eigenspace_iff.mp v.2
  set h' : H G := (v : H G) with hh'
  have hnorm : ‖ζ‖ = 1 := by
    have h1 := (tau g).norm_map h'
    rw [hv1, norm_smul] at h1
    have hpos : 0 < ‖h'‖ := norm_pos_iff.mpr hh0
    exact mul_right_cancel₀ hpos.ne' (by rw [h1, one_mul])
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact zero_ne_one hnorm
  have hζm : ζ ^ m ≠ 1 := by
    intro h1
    have hA : tau a h' = h' := by rw [ha, tau_zsmul_eigen g h' ζ hζ0 hv1 m, h1, one_smul]
    have hA' : tau (-a) h' = h' := by
      have : -a = (-m) • g := by rw [ha, neg_smul]
      rw [this, tau_zsmul_eigen g h' ζ hζ0 hv1 (-m), zpow_neg, h1, inv_one, one_smul]
    have hP : Pop a h' = 0 := by
      rw [Pop_apply, hA, hA']
      module
    have hT0 : Top a h' = 0 := by
      unfold Top
      simp only [ContinuousLinearMap.comp_apply]
      rw [Pop_Cop, hP, map_zero, map_zero]
    rw [hTh] at hT0
    exact hh0 ((smul_eq_zero.mp hT0).resolve_left hμ0)
  have hCh : Cop h' ≠ 0 := by
    intro h
    have hT0 : Top a h' = 0 := by
      unfold Top
      simp only [ContinuousLinearMap.comp_apply]
      rw [h, map_zero, map_zero]
    rw [hTh] at hT0
    exact hh0 ((smul_eq_zero.mp hT0).resolve_left hμ0)
  have hCF : (Cop h' : G → ℂ) =ᵐ[mu G] ⇑(RL h') :=
    BoundedContinuousFunction.coeFn_toLp 2 (mu G) ℂ (RL h')
  have hFc : Continuous ⇑(RL h') := (RL h').continuous
  have h1 : (tau g (Cop h') : G → ℂ) =ᵐ[mu G] fun x => RL h' (x + g) := by
    have e1 := tau_ae g (Cop h')
    have e2 := (measurePreserving_add_right (mu G) g).quasiMeasurePreserving.ae_eq_comp hCF
    filter_upwards [e1, e2] with x hx1 hx2
    simp only [Function.comp] at hx2
    rw [hx1, hx2]
  have h2 : (tau g (Cop h') : G → ℂ) =ᵐ[mu G] fun x => ζ * RL h' x := by
    rw [← Cop_tau, hv1, map_smul]
    filter_upwards [Lp.coeFn_smul ζ (Cop h'), hCF] with x hx1 hx2
    rw [hx1]
    simp [hx2]
  have h3 := (Continuous.ae_eq_iff_eq (mu G) (hFc.comp (continuous_id.add continuous_const))
    (continuous_const.mul hFc)).mp (h1.symm.trans h2)
  refine ⟨ζ, ⇑(RL h'), hnorm, hζm, hFc, ?_, fun x => congrFun h3 x⟩
  by_contra hcon
  push Not at hcon
  apply hCh
  apply Lp.ext
  refine hCF.trans ?_
  filter_upwards with x
  simp [hcon x]

#print axioms weil_abstract

end JAWeil
end LeanCheck
