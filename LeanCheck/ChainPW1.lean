import Mathlib

/-!
# Peter–Weyl, part 1: integral operators with continuous kernel on `L²(K, μ)`

For a compact Hausdorff space `K` with a finite Borel measure `μ`, a continuous kernel `k : K × K → ℂ`
defines an operator `T_k` on `L²(μ)` with `T_k h = ∫ k(·, y) h(y) dμ(y)`.  To avoid Fubini and
product-measurability (which fail to be automatic when `K` is not second countable), `T_k h` is defined as
the continuous function `x ↦ ⟪ι(conj k(x,·)), h⟫` (inner product in `L²`), where `ι : C(K,ℂ) → L²` is
the canonical map.  We prove `T_k` is a bounded linear operator, depends linearly and boundedly on `k`,
and is *compact* (rank-one for tensors `a(x) b(y)`, whose span is dense by Stone–Weierstrass).
-/

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace LeanCheck
namespace PW

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

/-- The canonical map `C(K,ℂ) → L²(μ)`. -/
noncomputable abbrev ι : C(K, ℂ) →L[ℂ] Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ

/-- `x ↦ ι(conj k(x, ·))`, a continuous map `K → L²`. -/
noncomputable def Ak (k : C(K × K, ℂ)) : C(K, Lp ℂ 2 μ) :=
  ⟨fun x => ι μ (star (k.curry x)),
    (ι μ).continuous.comp (continuous_star.comp k.curry.continuous)⟩

lemma Ak_apply (k : C(K × K, ℂ)) (x : K) : Ak μ k x = ι μ (star (k.curry x)) := rfl

lemma Ak_add (k₁ k₂ : C(K × K, ℂ)) : Ak μ (k₁ + k₂) = Ak μ k₁ + Ak μ k₂ := by
  ext x : 1
  simp [Ak_apply]

lemma Ak_smul (c : ℂ) (k : C(K × K, ℂ)) : Ak μ (c • k) = (starRingEnd ℂ c) • Ak μ k := by
  ext x : 1
  simp [Ak_apply]

lemma Ak_norm_le (k : C(K × K, ℂ)) : ‖Ak μ k‖ ≤ ‖ι μ‖ * ‖k‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 (fun x => ?_)
  rw [Ak_apply]
  refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [norm_star]
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 (fun y => ?_)
  simpa using ContinuousMap.norm_coe_le_norm k (x, y)

/-- `h ↦ (x ↦ ⟪Ak x, h⟫)` as a linear map `L² → C(K,ℂ)`. -/
noncomputable def Gam (k : C(K × K, ℂ)) : Lp ℂ 2 μ →ₗ[ℂ] C(K, ℂ) where
  toFun h := ⟨fun x => ⟪Ak μ k x, h⟫_ℂ, (Ak μ k).continuous.inner continuous_const⟩
  map_add' h₁ h₂ := by ext x; simp [inner_add_right]
  map_smul' c h := by ext x; simp [inner_smul_right]

lemma Gam_apply (k : C(K × K, ℂ)) (h : Lp ℂ 2 μ) (x : K) : Gam μ k h x = ⟪Ak μ k x, h⟫_ℂ := rfl

lemma Gam_norm_le (k : C(K × K, ℂ)) (h : Lp ℂ 2 μ) : ‖Gam μ k h‖ ≤ ‖Ak μ k‖ * ‖h‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 (fun x => ?_)
  rw [Gam_apply]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm (Ak μ k) x) (norm_nonneg _))

/-- **The integral operator with continuous kernel `k`.** -/
noncomputable def Tk (k : C(K × K, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (((ι μ : C(K, ℂ) →L[ℂ] Lp ℂ 2 μ) : C(K, ℂ) →ₗ[ℂ] Lp ℂ 2 μ) ∘ₗ Gam μ k).mkContinuous
    (‖ι μ‖ * ‖Ak μ k‖) (fun h => by
      show ‖ι μ (Gam μ k h)‖ ≤ _
      refine ((ι μ).le_opNorm (Gam μ k h)).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (Gam_norm_le μ k h) (norm_nonneg _))

lemma Tk_apply (k : C(K × K, ℂ)) (h : Lp ℂ 2 μ) : Tk μ k h = ι μ (Gam μ k h) := rfl

lemma Tk_add (k₁ k₂ : C(K × K, ℂ)) : Tk μ (k₁ + k₂) = Tk μ k₁ + Tk μ k₂ := by
  ext h : 1
  simp only [Tk_apply, ContinuousLinearMap.add_apply, ← map_add]
  congr 1
  ext x : 1
  simp [Gam_apply, Ak_add, inner_add_left]

lemma Tk_smul (c : ℂ) (k : C(K × K, ℂ)) : Tk μ (c • k) = c • Tk μ k := by
  ext h : 1
  simp only [Tk_apply, ContinuousLinearMap.smul_apply, ← map_smul]
  congr 1
  ext x : 1
  simp [Gam_apply, Ak_smul, inner_smul_left]

lemma Tk_norm_le (k : C(K × K, ℂ)) : ‖Tk μ k‖ ≤ ‖ι μ‖ * (‖ι μ‖ * ‖k‖) := by
  refine (ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun h => ?_))
  rw [Tk_apply]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ((Gam_norm_le μ k h).trans ?_) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_right (Ak_norm_le μ k) (norm_nonneg _)

/-- `k ↦ T_k` is a bounded linear map. -/
noncomputable def Theta : C(K × K, ℂ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  LinearMap.mkContinuous
    { toFun := Tk μ
      map_add' := Tk_add μ
      map_smul' := fun c k => Tk_smul μ c k }
    (‖ι μ‖ * ‖ι μ‖) (fun k => by
      refine (Tk_norm_le μ k).trans (le_of_eq ?_)
      ring)

lemma Theta_apply (k : C(K × K, ℂ)) : Theta μ k = Tk μ k := rfl

/-! ### Rank-one operators and compactness -/

/-- The tensor `a(x) b(y)` as a continuous function on `K × K`. -/
def tensor (a b : C(K, ℂ)) : C(K × K, ℂ) :=
  ⟨fun p => a p.1 * b p.2, (a.continuous.comp continuous_fst).mul (b.continuous.comp continuous_snd)⟩

lemma tensor_apply (a b : C(K, ℂ)) (p : K × K) : tensor a b p = a p.1 * b p.2 := rfl

lemma Tk_tensor (a b : C(K, ℂ)) (h : Lp ℂ 2 μ) :
    Tk μ (tensor a b) h = ⟪ι μ (star b), h⟫_ℂ • ι μ a := by
  rw [Tk_apply]
  have : Gam μ (tensor a b) h = ⟪ι μ (star b), h⟫_ℂ • a := by
    ext x
    simp only [Gam_apply, Ak_apply, ContinuousMap.smul_apply, smul_eq_mul]
    have : star ((tensor a b).curry x) = (starRingEnd ℂ (a x)) • star b := by
      ext y; simp [tensor_apply]
    rw [this, map_smul, inner_smul_left]
    simp [mul_comm]
  rw [this, map_smul]

lemma isCompact_Tk_tensor (a b : C(K, ℂ)) : IsCompactOperator (Tk μ (tensor a b)) := by
  have hfun : (Tk μ (tensor a b) : Lp ℂ 2 μ → Lp ℂ 2 μ) =
      (fun z : ℂ => z • ι μ a) ∘ (fun h => ⟪ι μ (star b), h⟫_ℂ) := by
    funext h; exact Tk_tensor μ a b h
  rw [hfun]
  have hg : IsCompactOperator (fun z : ℂ => z • ι μ a) := by
    let g : ℂ →L[ℂ] Lp ℂ 2 μ := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) (ι μ a)
    exact isCompactOperator_of_locallyCompactSpace_rng g
  exact hg.comp_clm (innerSL ℂ (ι μ (star b)))

end PW
end LeanCheck
