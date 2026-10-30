import LeanCheck.ChainPW4

/-!
# Peter–Weyl, part 5: continuous characters separate the points of a compact Hausdorff abelian group

For `x₀ ≠ 0` choose `f ∈ C(K)` with `f(0) = 1`, `f(x₀) = 0`; the convolution operator `T = T_f` is compact
and commutes with translations, `D = (tr x₀ - 1) T ≠ 0` (otherwise `f(· + x₀) = f`), and `B = D†D` is a
nonzero compact self-adjoint operator.  A common eigenvector `w` of all translations in a (finite-dimensional)
eigenspace of `B` with nonzero eigenvalue gives a continuous character `c` with `c(x₀) ≠ 1`: the function
`T w` is continuous, satisfies `(T w)(x + a) = c(a) (T w)(x)`, and `D w = (c(x₀) - 1) T w ≠ 0`.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace LeanCheck
namespace PW

variable {K : Type} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
  [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsAddHaarMeasure]

/-- Translation as a continuous linear map. -/
noncomputable def trL (a : K) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := (tr μ a).toContinuousLinearMap

lemma trL_apply (a : K) (h : Lp ℂ 2 μ) : trL μ a h = tr μ a h := rfl

/-- `D = (tr x₀ - 1) ∘ T_f`. -/
noncomputable def Dop (f : C(K, ℂ)) (x₀ : K) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (trL μ x₀ - 1) ∘L Tk μ (convK f)

lemma Dop_apply (f : C(K, ℂ)) (x₀ : K) (h : Lp ℂ 2 μ) :
    Dop μ f x₀ h = tr μ x₀ (Tk μ (convK f) h) - Tk μ (convK f) h := rfl

lemma Dop_comm (f : C(K, ℂ)) (x₀ a : K) (h : Lp ℂ 2 μ) :
    Dop μ f x₀ (tr μ a h) = tr μ a (Dop μ f x₀ h) := by
  rw [Dop_apply, Dop_apply, Tconv_comm, map_sub, tr_comm]

lemma Dstar_comm (f : C(K, ℂ)) (x₀ a : K) (u : Lp ℂ 2 μ) :
    ContinuousLinearMap.adjoint (Dop μ f x₀) (tr μ a u) =
      tr μ a (ContinuousLinearMap.adjoint (Dop μ f x₀) u) := by
  apply ext_inner_right ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, tr_inner_left, tr_inner_left,
    ← Dop_comm, ContinuousLinearMap.adjoint_inner_left]

/-- `B = D†D`. -/
noncomputable def Bop (f : C(K, ℂ)) (x₀ : K) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  ContinuousLinearMap.adjoint (Dop μ f x₀) ∘L Dop μ f x₀

lemma Bop_comm (f : C(K, ℂ)) (x₀ a : K) (h : Lp ℂ 2 μ) :
    Bop μ f x₀ (tr μ a h) = tr μ a (Bop μ f x₀ h) := by
  show ContinuousLinearMap.adjoint (Dop μ f x₀) (Dop μ f x₀ (tr μ a h)) = _
  rw [Dop_comm, Dstar_comm]
  rfl

lemma Bop_symm (f : C(K, ℂ)) (x₀ : K) : ((Bop μ f x₀ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).IsSymmetric := by
  intro x y
  show ⟪ContinuousLinearMap.adjoint (Dop μ f x₀) (Dop μ f x₀ x), y⟫_ℂ =
    ⟪x, ContinuousLinearMap.adjoint (Dop μ f x₀) (Dop μ f x₀ y)⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

lemma Bop_compact (f : C(K, ℂ)) (x₀ : K) : IsCompactOperator (Bop μ f x₀) := by
  have hD : IsCompactOperator (Dop μ f x₀) :=
    show IsCompactOperator (⇑(trL μ x₀ - 1) ∘ ⇑(Tk μ (convK f))) from
      (Tk_compact μ (convK f)).clm_comp (trL μ x₀ - 1)
  exact hD.continuous_comp (ContinuousLinearMap.adjoint (Dop μ f x₀)).continuous

/-- If `f(0) ≠ f(x₀)` then `D ≠ 0`. -/
lemma Dop_ne_zero (f : C(K, ℂ)) (x₀ : K) (hf : f x₀ ≠ f 0) : Dop μ f x₀ ≠ 0 := by
  intro hD
  have key : ∀ x : K, Ak μ (convK f) (x + x₀) = Ak μ (convK f) x := by
    intro x
    set u : Lp ℂ 2 μ := Ak μ (convK f) (x + x₀) - Ak μ (convK f) x with hu
    have h0 : Dop μ f x₀ u = 0 := by rw [hD]; rfl
    rw [Dop_apply, Tk_apply, tr_ι, sub_eq_zero] at h0
    have h1 := ContinuousMap.toLp_injective (p := 2) (μ := μ) (𝕜 := ℂ) h0
    have h2 := congrArg (fun F : C(K, ℂ) => F x) h1
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight, Gam_apply] at h2
    have h3 : ⟪u, u⟫_ℂ = 0 := by
      rw [hu]
      conv_lhs => rw [inner_sub_left]
      rw [h2, sub_self]
    have : u = 0 := inner_self_eq_zero.1 h3
    exact sub_eq_zero.1 this
  have h4 := key 0
  rw [zero_add] at h4
  simp only [Ak_apply] at h4
  have h5 := ContinuousMap.toLp_injective (p := 2) (μ := μ) (𝕜 := ℂ) h4
  have h6 := congrArg (fun F : C(K, ℂ) => F 0) h5
  simp only [ContinuousMap.star_apply, ContinuousMap.curry_apply, convK_apply, sub_zero, zero_sub,
    sub_self] at h6
  have h7 : (starRingEnd ℂ) (f x₀) = (starRingEnd ℂ) (f 0) := by simpa using h6
  exact hf ((starRingEnd ℂ).injective h7)

end PW
end LeanCheck
