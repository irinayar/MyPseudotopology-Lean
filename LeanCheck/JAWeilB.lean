import Mathlib
import LeanCheck.JAWeilA

/-!
# Weil's theorem for `ℤ`, part B: the convolution operator `C`

`K x ∈ H` is the class of the continuous function `y ↦ ‖x - y‖`.  The operator `C g = (x ↦ ⟪K x, g⟫)` (as an element of `H`)
is a compact operator on `H` commuting with all translations `tau a`, and `C ∘ tau a ≠ C` for `a ≠ 0`.
-/

namespace LeanCheck
namespace JAWeil

open MeasureTheory Filter
open scoped BoundedContinuousFunction

variable {G : Type*} [NormedAddCommGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The continuous function `y ↦ ‖x - y‖`. -/
noncomputable def kfun (x : G) : C(G, ℂ) :=
  ⟨fun y => ((‖x - y‖ : ℝ) : ℂ), by fun_prop⟩

/-- Its class in `H`. -/
noncomputable def K (x : G) : H G := ContinuousMap.toLp 2 (mu G) ℂ (kfun x)

lemma kfun_sub_norm_le (x x' : G) : ‖kfun x - kfun x'‖ ≤ ‖x - x'‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro y
  simp only [ContinuousMap.sub_apply, kfun, ContinuousMap.coe_mk]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have := abs_norm_sub_norm_le (x - y) (x' - y)
  simpa using this

/-- `K` is Lipschitz. -/
lemma K_lipschitz : ∃ L : ℝ, 0 ≤ L ∧ ∀ x x' : G, ‖K x - K x'‖ ≤ L * ‖x - x'‖ := by
  refine ⟨‖(ContinuousMap.toLp 2 (mu G) ℂ : C(G, ℂ) →L[ℂ] H G)‖, norm_nonneg _, fun x x' => ?_⟩
  have : K x - K x' = ContinuousMap.toLp 2 (mu G) ℂ (kfun x - kfun x') := by
    simp [K]
  rw [this]
  calc ‖ContinuousMap.toLp 2 (mu G) ℂ (kfun x - kfun x')‖
      ≤ ‖(ContinuousMap.toLp 2 (mu G) ℂ : C(G, ℂ) →L[ℂ] H G)‖ * ‖kfun x - kfun x'‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by gcongr; exact kfun_sub_norm_le x x'

lemma K_continuous : Continuous (K : G → H G) := by
  obtain ⟨L, hL, h⟩ := K_lipschitz (G := G)
  have : LipschitzWith L.toNNReal (K : G → H G) := by
    apply LipschitzWith.of_dist_le_mul
    intro x x'
    rw [dist_eq_norm, dist_eq_norm]
    simpa [Real.coe_toNNReal _ hL] using h x x'
  exact this.continuous

lemma K_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : G, ‖K x‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (K_continuous (G := G)).continuousOn
  exact ⟨max M 0, le_max_right _ _, fun x => (hM x (Set.mem_univ x)).trans (le_max_left _ _)⟩

/-- `x ↦ ⟪K x, g⟫` as a bounded continuous function. -/
noncomputable def Rb (g : H G) : G →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => inner ℂ (K x) g,
    (K_continuous (G := G)).inner continuous_const⟩

lemma Rb_apply (g : H G) (x : G) : Rb g x = inner ℂ (K x) g := rfl

/-- `R` as a continuous linear map. -/
noncomputable def RL : H G →L[ℂ] (G →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := Rb
      map_add' := fun g g' => by ext x; simp [Rb_apply, inner_add_right]
      map_smul' := fun c g => by ext x; simp [Rb_apply, inner_smul_right] }
    (K_bound (G := G)).choose
    (fun g => by
      obtain ⟨hM0, hM⟩ := (K_bound (G := G)).choose_spec
      show ‖Rb g‖ ≤ _ * ‖g‖
      rw [BoundedContinuousFunction.norm_le (mul_nonneg hM0 (norm_nonneg _))]
      intro x
      rw [Rb_apply]
      exact (norm_inner_le_norm _ _).trans (by gcongr; exact hM x))

/-- The convolution operator. -/
noncomputable def Cop : H G →L[ℂ] H G :=
  (BoundedContinuousFunction.toLp 2 (mu G) ℂ).comp RL

lemma Cop_ae (g : H G) : (Cop g : G → ℂ) =ᵐ[mu G] fun x => inner ℂ (K x) g :=
  BoundedContinuousFunction.coeFn_toLp 2 (mu G) ℂ (RL g)

/-- `tau (-a) (K x) = K (x + a)`. -/
lemma tau_K (a x : G) : tau (-a) (K x) = K (x + a) := by
  unfold K
  rw [tau_toLp]
  congr 1
  ext y
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_addRight, kfun, ContinuousMap.coe_mk]
  congr 2
  abel

/-- `C` commutes with translations. -/
theorem Cop_tau (a : G) (g : H G) : Cop (tau a g) = tau a (Cop g) := by
  apply Lp.ext
  have h1 := Cop_ae (tau a g)
  have h2 := tau_ae a (Cop g)
  have h3 := (measurePreserving_add_right (mu G) a).quasiMeasurePreserving.ae_eq_comp (Cop_ae g)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  simp only [Function.comp] at hx3
  rw [hx1, hx2, hx3]
  have := tau_inner (-a) (K x) g
  rw [tau_K, neg_neg] at this
  exact this.symm

/-- `C` does not annihilate all `tau a g - g` when `a ≠ 0`. -/
theorem Cop_tau_ne (a : G) (ha : a ≠ 0) : ∃ g : H G, Cop (tau a g) ≠ Cop g := by
  by_contra hcon
  push Not at hcon
  have key : ∀ g : H G, inner ℂ (K a) g = inner ℂ (K 0) g := by
    intro g
    have h := hcon g
    have h1 := Cop_ae (tau a g)
    have h2 := Cop_ae g
    have h3 : (fun x : G => inner ℂ (K x) (tau a g)) =ᵐ[mu G] fun x => inner ℂ (K x) g := by
      filter_upwards [h1, h2] with x hx1 hx2
      rw [← hx1, ← hx2, h]
    have hc1 : Continuous fun x : G => inner ℂ (K x) (tau a g) :=
      (K_continuous (G := G)).inner continuous_const
    have hc2 : Continuous fun x : G => inner ℂ (K x) g :=
      (K_continuous (G := G)).inner continuous_const
    have h4 := (Continuous.ae_eq_iff_eq (mu G) hc1 hc2).mp h3
    have h5 := congrFun h4 0
    have e : inner ℂ (K 0) (tau a g) = inner ℂ (K a) g := by
      have := tau_inner (-a) (K 0) g
      rw [tau_K, neg_neg, zero_add] at this
      exact this.symm
    rw [e] at h5
    exact h5
  have hK : K a = K 0 := by
    apply ext_inner_right ℂ
    intro g
    exact key g
  have h6 : (kfun a : G → ℂ) = kfun 0 := by
    have e1 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (mu G) (kfun a)
    have e2 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (mu G) (kfun 0)
    have e3 : (ContinuousMap.toLp 2 (mu G) ℂ (kfun a) : G → ℂ) =ᵐ[mu G]
        (ContinuousMap.toLp 2 (mu G) ℂ (kfun 0) : G → ℂ) := by
      have := hK
      unfold K at this
      rw [this]
    have e4 : (kfun a : G → ℂ) =ᵐ[mu G] (kfun 0 : G → ℂ) := e1.symm.trans (e3.trans e2)
    exact (Continuous.ae_eq_iff_eq (mu G) (kfun a).continuous (kfun 0).continuous).mp e4
  have h7 := congrFun h6 0
  simp [kfun] at h7
  exact ha (by simpa using h7)

/-- The set `A` of bounded continuous functions with sup bound `M` and Lipschitz constant `L`. -/
def Aset (L M : ℝ) : Set (G →ᵇ ℂ) :=
  {f | (∀ x, ‖f x‖ ≤ M) ∧ ∀ x x' : G, ‖f x - f x'‖ ≤ L * ‖x - x'‖}

lemma Aset_closed (L M : ℝ) : IsClosed (Aset (G := G) L M) := by
  have h1 : IsClosed {f : G →ᵇ ℂ | ∀ x, ‖f x‖ ≤ M} := by
    have : {f : G →ᵇ ℂ | ∀ x, ‖f x‖ ≤ M} = ⋂ x, {f | ‖f x‖ ≤ M} := by ext; simp
    rw [this]
    exact isClosed_iInter fun x => isClosed_le (by fun_prop) continuous_const
  have h2 : IsClosed {f : G →ᵇ ℂ | ∀ x x' : G, ‖f x - f x'‖ ≤ L * ‖x - x'‖} := by
    have : {f : G →ᵇ ℂ | ∀ x x' : G, ‖f x - f x'‖ ≤ L * ‖x - x'‖} =
        ⋂ x, ⋂ x', {f | ‖f x - f x'‖ ≤ L * ‖x - x'‖} := by ext; simp
    rw [this]
    exact isClosed_iInter fun x => isClosed_iInter fun x' => isClosed_le (by fun_prop) continuous_const
  exact h1.inter h2

lemma Aset_equicont (L M : ℝ) (hL0 : 0 ≤ L) :
    Equicontinuous ((↑) : Aset (G := G) L M → G → ℂ) := by
  have hlip : UniformEquicontinuous (fun f : Aset (G := G) L M => ((f : G →ᵇ ℂ) : G → ℂ)) :=
    LipschitzWith.uniformEquicontinuous _ L.toNNReal (fun f =>
      LipschitzWith.of_dist_le_mul (fun x x' => by
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0]
        exact f.2.2 x x'))
  exact hlip.equicontinuous

lemma Aset_compact (L M : ℝ) (hL0 : 0 ≤ L) : IsCompact (Aset (G := G) L M) := by
  have := BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℂ) M)
    (isCompact_closedBall _ _) (Aset (G := G) L M)
    (fun f x hf => by simpa using hf.1 x) (Aset_equicont L M hL0)
  rwa [(Aset_closed (G := G) L M).closure_eq] at this

lemma RL_mem (L M : ℝ) (hL0 : 0 ≤ L) (hM0 : 0 ≤ M) (hL : ∀ x x' : G, ‖K x - K x'‖ ≤ L * ‖x - x'‖) (hM : ∀ x : G, ‖K x‖ ≤ M)
    (g : H G) (hg : ‖g‖ ≤ 1) : RL g ∈ Aset (G := G) L M := by
  refine ⟨fun x => ?_, fun x x' => ?_⟩
  · show ‖Rb g x‖ ≤ M
    rw [Rb_apply]
    calc ‖inner ℂ (K x) g‖ ≤ ‖K x‖ * ‖g‖ := norm_inner_le_norm _ _
      _ ≤ M * 1 := mul_le_mul (hM x) hg (norm_nonneg _) hM0
      _ = M := mul_one M
  · show ‖Rb g x - Rb g x'‖ ≤ _
    rw [Rb_apply, Rb_apply, ← inner_sub_left]
    calc ‖inner ℂ (K x - K x') g‖ ≤ ‖K x - K x'‖ * ‖g‖ := norm_inner_le_norm _ _
      _ ≤ (L * ‖x - x'‖) * 1 := mul_le_mul (hL x x') hg (norm_nonneg _) (mul_nonneg hL0 (norm_nonneg _))
      _ = L * ‖x - x'‖ := mul_one _

/-- **`C` is compact.** -/
theorem Cop_compact : IsCompactOperator (Cop : H G →L[ℂ] H G) := by
  obtain ⟨L, hL0, hL⟩ := K_lipschitz (G := G)
  obtain ⟨M, hM0, hM⟩ := K_bound (G := G)
  have hsub : (Cop : H G →L[ℂ] H G) '' Metric.ball (0 : H G) 1 ⊆
      (BoundedContinuousFunction.toLp 2 (mu G) ℂ : (G →ᵇ ℂ) →L[ℂ] H G) '' Aset (G := G) L M := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨RL g, RL_mem L M hL0 hM0 hL hM g (mem_ball_zero_iff.mp hg).le, rfl⟩
  have himg : IsCompact ((BoundedContinuousFunction.toLp 2 (mu G) ℂ : (G →ᵇ ℂ) →L[ℂ] H G) '' Aset (G := G) L M) :=
    (Aset_compact L M hL0).image (BoundedContinuousFunction.toLp 2 (mu G) ℂ).continuous
  have hcl : IsCompact (closure ((Cop : H G →L[ℂ] H G) '' Metric.ball (0 : H G) 1)) :=
    himg.of_isClosed_subset isClosed_closure (closure_minimal hsub himg.isClosed)
  exact (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image (Cop : H G → H G)).mpr
    ⟨Metric.ball (0 : H G) 1, Metric.ball_mem_nhds _ one_pos, hcl⟩

#print axioms Cop_tau
#print axioms Cop_tau_ne
#print axioms Cop_compact

end JAWeil
end LeanCheck
