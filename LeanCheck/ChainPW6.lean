import LeanCheck.ChainPW5

/-!
# Peter–Weyl, part 6: the main theorem

**Continuous characters separate the points of a compact Hausdorff abelian group** (the abelian case of the
Peter–Weyl theorem), proved from the spectral theorem for compact self-adjoint operators on `L²(Haar)`.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace LeanCheck
namespace PW

variable {K : Type} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
  [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem exists_char_ne (x₀ : K) (hx₀ : x₀ ≠ 0) :
    ∃ c : K → ℂ, Continuous c ∧ (∀ a b, c (a + b) = c a * c b) ∧ (∀ a, ‖c a‖ = 1) ∧ c x₀ ≠ 1 := by
  classical
  let μ : Measure K := Measure.addHaar
  -- a function with `f 0 = 1`, `f x₀ = 0`
  obtain ⟨g, hg0, hg1, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := x₀)) (isClosed_singleton (x := (0 : K)))
    (Set.disjoint_singleton.2 hx₀)
  let f : C(K, ℂ) := ⟨fun z => ((g z : ℝ) : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
  have hf0 : f 0 = 1 := by
    show ((g 0 : ℝ) : ℂ) = 1
    rw [hg1 (Set.mem_singleton 0)]; simp
  have hfx : f x₀ = 0 := by
    show ((g x₀ : ℝ) : ℂ) = 0
    rw [hg0 (Set.mem_singleton x₀)]; simp
  have hfne : f x₀ ≠ f 0 := by rw [hf0, hfx]; exact zero_ne_one
  let D := Dop μ f x₀
  let B := Bop μ f x₀
  have hD : D ≠ 0 := Dop_ne_zero μ f x₀ hfne
  have hBne : B ≠ 0 := by
    intro hB0
    apply hD
    obtain ⟨h, hh⟩ : ∃ h, D h ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hD (ContinuousLinearMap.ext hcon)
    have : ⟪B h, h⟫_ℂ = ⟪D h, D h⟫_ℂ := by
      show ⟪ContinuousLinearMap.adjoint D (D h), h⟫_ℂ = _
      rw [ContinuousLinearMap.adjoint_inner_left]
    rw [hB0] at this
    simp only [ContinuousLinearMap.zero_apply, inner_zero_left] at this
    exact absurd (inner_self_eq_zero.1 this.symm) hh
  have hBc : IsCompactOperator B := Bop_compact μ f x₀
  have hBs := Bop_symm μ f x₀
  -- a nonzero eigenvalue
  obtain ⟨μ₀, hμ₀, hμ₀ne⟩ : ∃ μ₀ : ℂ, Module.End.HasEigenvalue (B : Module.End ℂ (Lp ℂ 2 μ)) μ₀ ∧ μ₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hBne ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hBc hBs).1 hcon)
  let E : Submodule ℂ (Lp ℂ 2 μ) := Module.End.eigenspace (B : Module.End ℂ (Lp ℂ 2 μ)) μ₀
  haveI : FiniteDimensional ℂ E := ContinuousLinearMap.finite_dimensional_eigenspace hBc μ₀ hμ₀ne
  haveI : Nontrivial E := by
    obtain ⟨v, hv, hv0⟩ := hμ₀.exists_hasEigenvector
    exact ⟨⟨⟨v, hv⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  have hE : ∀ x, x ∈ E ↔ B x = μ₀ • x := fun x => by
    simp [E, Module.End.mem_eigenspace_iff]
  have hmaps : ∀ a, ∀ x ∈ E, tr μ a x ∈ E := by
    intro a x hx
    rw [hE] at hx ⊢
    rw [show B (tr μ a x) = tr μ a (B x) from Bop_comm μ f x₀ a x, hx, map_smul]
  let Tt : K → E →ₗ[ℂ] E := fun a =>
    (tr μ a).toLinearMap.restrict (fun x hx => hmaps a x hx)
  have hcomm : ∀ a b x, Tt a (Tt b x) = Tt b (Tt a x) := by
    intro a b x
    apply Subtype.ext
    exact tr_comm μ a b x
  obtain ⟨w, hw0, hw⟩ := PW.exists_common_eigenvector Tt hcomm
  set w' : Lp ℂ 2 μ := (w : Lp ℂ 2 μ) with hw'def
  have hw'ne : w' ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hBw : B w' = μ₀ • w' := (hE _).1 w.2
  choose c hc using fun a => (hw a)
  have hcw : ∀ a, tr μ a w' = c a • w' := fun a => by
    have := congrArg Subtype.val (hc a)
    simpa [Tt] using this
  have hDw : D w' ≠ 0 := by
    intro h0
    have : B w' = 0 := by
      show ContinuousLinearMap.adjoint D (D w') = 0
      rw [h0, map_zero]
    rw [hBw] at this
    exact hw'ne ((smul_eq_zero.1 this).resolve_left hμ₀ne)
  -- the continuous function `F = T w'`
  let F : C(K, ℂ) := Gam μ (convK f) w'
  have hTw : Tk μ (convK f) w' = ι μ F := rfl
  have htrv : ∀ a, tr μ a (ι μ F) = c a • ι μ F := by
    intro a
    rw [← hTw, ← Tconv_comm, hcw, map_smul]
  have hDw' : D w' = (c x₀ - 1) • ι μ F := by
    show tr μ x₀ (Tk μ (convK f) w') - Tk μ (convK f) w' = _
    rw [hTw, htrv, sub_smul, one_smul]
  have hcx : c x₀ ≠ 1 := by
    intro h
    apply hDw
    rw [hDw', h, sub_self, zero_smul]
  have hFne : F ≠ 0 := by
    intro h
    apply hDw
    rw [hDw', h, map_zero, smul_zero]
  have hper : ∀ a x, F (x + a) = c a * F x := by
    intro a x
    have h1 : tr μ a (ι μ F) = ι μ (c a • F) := by rw [htrv, map_smul]
    rw [tr_ι] at h1
    have h2 := ContinuousMap.toLp_injective (p := 2) (μ := μ) (𝕜 := ℂ) h1
    have h3 := congrArg (fun G : C(K, ℂ) => G x) h2
    simpa using h3
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, F x₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hFne (ContinuousMap.ext hcon)
  have hcform : ∀ a, c a = F (x₁ + a) / F x₁ := by
    intro a
    rw [hper a x₁]
    field_simp
  refine ⟨c, ?_, ?_, ?_, hcx⟩
  · have : c = fun a => F (x₁ + a) / F x₁ := funext hcform
    rw [this]
    exact (F.continuous.comp (continuous_const.add continuous_id)).div_const _
  · intro a b
    have : c (a + b) * F x₁ = c a * c b * F x₁ := by
      calc c (a + b) * F x₁ = F (x₁ + (a + b)) := (hper (a + b) x₁).symm
        _ = F ((x₁ + a) + b) := by rw [add_assoc]
        _ = c b * F (x₁ + a) := hper b (x₁ + a)
        _ = c b * (c a * F x₁) := by rw [hper a x₁]
        _ = c a * c b * F x₁ := by ring
    exact mul_right_cancel₀ hx₁ this
  · intro a
    have h1 : ‖tr μ a w'‖ = ‖w'‖ := (tr μ a).norm_map w'
    rw [hcw, norm_smul] at h1
    have hpos : 0 < ‖w'‖ := norm_pos_iff.2 hw'ne
    have : ‖c a‖ * ‖w'‖ = 1 * ‖w'‖ := by rw [h1, one_mul]
    exact mul_right_cancel₀ hpos.ne' this

end PW
end LeanCheck
