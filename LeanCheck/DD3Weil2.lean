import Mathlib
import LeanCheck.JAWeilD

/-!
# Weil's theorem for two generators (Lean check)

Scope. First part of the compact-quotient step for `ℤ²` in the Lean version of the conditional proof of `DD({2,3,5})`
(research note `TVGplus_conditional_DD235_2026-11-07.md`, item 7). `JAWeilC.weil_abstract` gives, in a compact normed abelian
group `G`, for one element `g` with `m • g ≠ 0` an eigencharacter `ζ` of the translation by `g` with `ζ^m ≠ 1`. Here:

* `weil_abstract2`: for two elements `g₁, g₂` with `m₁ • g₁ + m₂ • g₂ ≠ 0` there are `ζ₁, ζ₂` of modulus one with
  `ζ₁^{m₁} ζ₂^{m₂} ≠ 1` and one continuous `F ≢ 0` with `F (x + g_i) = ζ_i F x` (a joint eigenfunction; the eigenspace of the
  compact operator `T` is finite dimensional and invariant under both commuting translations);
* `weil_seminorm2`: if `S` is a precompact additive group seminorm on `ℤ × ℤ` and `S m > 0`, there are `α, β ∈ ℝ` such that
  `(n₁, n₂) ↦ e(n₁ α + n₂ β)` is `S`-continuous at `0` and `‖m₁ α + m₂ β‖ > 0`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Weil2

open MixedPrime JAWeil MeasureTheory

section abstract

variable {G : Type*} [NormedAddCommGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- A translation eigenvector of `H G` gives a translation eigenfunction. -/
lemma RL_translate (g : G) (h' : H G) (ζ : ℂ) (hv1 : tau g h' = ζ • h') :
    ∀ x, RL h' (x + g) = ζ * RL h' x := by
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
  exact fun x => congrFun h3 x

lemma RL_ne_zero (h' : H G) (hCh : Cop h' ≠ 0) : ∃ x₀, RL h' x₀ ≠ 0 := by
  have hCF : (Cop h' : G → ℂ) =ᵐ[mu G] ⇑(RL h') :=
    BoundedContinuousFunction.coeFn_toLp 2 (mu G) ℂ (RL h')
  by_contra hcon
  push Not at hcon
  apply hCh
  apply Lp.ext
  refine hCF.trans ?_
  filter_upwards with x
  simp [hcon x]

/-- **Weil's theorem, abstract form, two generators.** -/
theorem weil_abstract2 (g₁ g₂ : G) (m₁ m₂ : ℤ) (hm : m₁ • g₁ + m₂ • g₂ ≠ 0) :
    ∃ (ζ₁ ζ₂ : ℂ) (F : G → ℂ), ‖ζ₁‖ = 1 ∧ ‖ζ₂‖ = 1 ∧ ζ₁ ^ m₁ * ζ₂ ^ m₂ ≠ 1 ∧ Continuous F ∧
      (∃ x₀, F x₀ ≠ 0) ∧ (∀ x, F (x + g₁) = ζ₁ * F x) ∧ (∀ x, F (x + g₂) = ζ₂ * F x) := by
  classical
  set a : G := m₁ • g₁ + m₂ • g₂ with ha
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
  set E : Submodule ℂ (H G) := Module.End.eigenspace (Top a : Module.End ℂ (H G)) μ with hE
  have hmapsE : ∀ (g : G), ∀ x ∈ E, tau g x ∈ E := by
    intro g x hx
    rw [hE, Module.End.mem_eigenspace_iff] at hx ⊢
    show Top a (tau g x) = μ • tau g x
    rw [Top_tau]
    have hx' : Top a x = μ • x := hx
    rw [hx', map_smul]
  haveI : Nontrivial E :=
    ⟨⟨⟨v₀, hv₀.1⟩, 0, fun h => hv₀.2 (by simpa using congrArg Subtype.val h)⟩⟩
  -- first generator
  let S₁ : E →ₗ[ℂ] E := (tau g₁).toLinearMap.restrict (hmapsE g₁)
  obtain ⟨ζ₁, hζ₁⟩ := Module.End.exists_eigenvalue S₁
  obtain ⟨w₁, hw₁⟩ := hζ₁.exists_hasEigenvector
  have hw₁E : (w₁ : H G) ∈ E := w₁.2
  have hw₁v : tau g₁ (w₁ : H G) = ζ₁ • (w₁ : H G) := by
    have := Module.End.mem_eigenspace_iff.mp hw₁.1
    exact congrArg Subtype.val this
  have hw₁0 : (w₁ : H G) ≠ 0 := fun h => hw₁.2 (Subtype.ext h)
  -- the joint eigenspace of the first generator inside `E`
  set N : Submodule ℂ (H G) := E ⊓ LinearMap.ker ((tau g₁).toLinearMap - ζ₁ • LinearMap.id) with hN
  have hmemN : ∀ x, x ∈ N ↔ x ∈ E ∧ tau g₁ x = ζ₁ • x := by
    intro x
    rw [hN, Submodule.mem_inf, LinearMap.mem_ker]
    refine and_congr Iff.rfl ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le (inf_le_left : N ≤ E)
  have hmapsN : ∀ x ∈ N, tau g₂ x ∈ N := by
    intro x hx
    rw [hmemN] at hx ⊢
    refine ⟨hmapsE g₂ x hx.1, ?_⟩
    rw [tau_comm g₁ g₂ x, hx.2, map_smul]
  haveI : Nontrivial N :=
    ⟨⟨⟨(w₁ : H G), (hmemN _).2 ⟨hw₁E, hw₁v⟩⟩, 0, fun h => hw₁0 (by simpa using congrArg Subtype.val h)⟩⟩
  let S₂ : N →ₗ[ℂ] N := (tau g₂).toLinearMap.restrict hmapsN
  obtain ⟨ζ₂, hζ₂⟩ := Module.End.exists_eigenvalue S₂
  obtain ⟨v, hv⟩ := hζ₂.exists_hasEigenvector
  have hvN := (hmemN _).1 v.2
  have hv2 : tau g₂ (v : H G) = ζ₂ • (v : H G) := by
    have := Module.End.mem_eigenspace_iff.mp hv.1
    exact congrArg Subtype.val this
  have hv1 : tau g₁ (v : H G) = ζ₁ • (v : H G) := hvN.2
  have hh0 : (v : H G) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hTh : Top a (v : H G) = μ • (v : H G) := Module.End.mem_eigenspace_iff.mp hvN.1
  set h' : H G := (v : H G) with hh'
  have hnorm : ∀ (g : G) (ζ : ℂ), tau g h' = ζ • h' → ‖ζ‖ = 1 := by
    intro g ζ hζ
    have h1 := (tau g).norm_map h'
    rw [hζ, norm_smul] at h1
    have hpos : 0 < ‖h'‖ := norm_pos_iff.mpr hh0
    exact mul_right_cancel₀ hpos.ne' (by rw [h1, one_mul])
  have hn₁ := hnorm g₁ ζ₁ hv1
  have hn₂ := hnorm g₂ ζ₂ hv2
  have hζ₁0 : ζ₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hn₁; exact zero_ne_one hn₁
  have hζ₂0 : ζ₂ ≠ 0 := by
    intro h; rw [h, norm_zero] at hn₂; exact zero_ne_one hn₂
  have hζm : ζ₁ ^ m₁ * ζ₂ ^ m₂ ≠ 1 := by
    intro h1
    have hA0 : tau a h' = (ζ₁ ^ m₁ * ζ₂ ^ m₂) • h' := by
      rw [ha, ← tau_add, tau_zsmul_eigen g₂ h' ζ₂ hζ₂0 hv2 m₂, map_smul,
        tau_zsmul_eigen g₁ h' ζ₁ hζ₁0 hv1 m₁, smul_smul, mul_comm (ζ₂ ^ m₂)]
    have hA : tau a h' = h' := by rw [hA0, h1, one_smul]
    have hA' : tau (-a) h' = h' := by
      have := tau_neg_tau a h'
      rwa [hA] at this
    have hP : Pop a h' = 0 := by
      rw [Pop_apply, hA, hA']
      module
    have hT0 : Top a h' = 0 := by
      unfold JAWeil.Top
      simp only [ContinuousLinearMap.comp_apply]
      rw [Pop_Cop, hP, map_zero, map_zero]
    rw [hTh] at hT0
    exact hh0 ((smul_eq_zero.mp hT0).resolve_left hμ0)
  have hCh : Cop h' ≠ 0 := by
    intro h
    have hT0 : Top a h' = 0 := by
      unfold JAWeil.Top
      simp only [ContinuousLinearMap.comp_apply]
      rw [h, map_zero, map_zero]
    rw [hTh] at hT0
    exact hh0 ((smul_eq_zero.mp hT0).resolve_left hμ0)
  exact ⟨ζ₁, ζ₂, ⇑(RL h'), hn₁, hn₂, hζm, (RL h').continuous, RL_ne_zero h' hCh,
    RL_translate g₁ h' ζ₁ hv1, RL_translate g₂ h' ζ₂ hv2⟩

end abstract

#print axioms weil_abstract2

end DD3Weil2
end LeanCheck
