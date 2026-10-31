import Mathlib
import LeanCheck.JAWeilC
import LeanCheck.MixedPrimeBasics

/-!
# Weil's theorem for `ℤ`, part D: precompact seminorms on `ℤ`

`weil_seminorm`: if `S` is an additive group seminorm on `ℤ` which is precompact (for every `ε` there is a finite `F` with
`ℤ = F + {S < ε}`) and `S m > 0`, then there is `α ∈ ℝ` such that `n ↦ e(nα)` is `S`-continuous at `0` and `‖mα‖ > 0`.

Proof: the completion `G` of `(ℤ, S)` is a compact normed abelian group; apply `weil_abstract` to `g = 1`.
-/

namespace LeanCheck
namespace JAWeil

open MixedPrime

/-- `ℤ` with the group seminorm `S`. -/
def ZS (_ : AddGroupSeminorm ℤ) : Type := ℤ

instance (S : AddGroupSeminorm ℤ) : AddCommGroup (ZS S) := inferInstanceAs (AddCommGroup ℤ)

/-- The seminorm as a seminorm on `ZS S`. -/
def ZS.sem (S : AddGroupSeminorm ℤ) : AddGroupSeminorm (ZS S) where
  toFun := fun m => S (show ℤ from m)
  map_zero' := S.map_zero'
  add_le' := S.add_le'
  neg' := S.neg'

instance (S : AddGroupSeminorm ℤ) : SeminormedAddCommGroup (ZS S) :=
  (ZS.sem S).toSeminormedAddCommGroup

lemma ZS.norm_def (S : AddGroupSeminorm ℤ) (m : ZS S) : ‖m‖ = S (show ℤ from m) := rfl

/-- `4 ‖θ‖_{ℝ/ℤ} ≤ |e(θ) - 1|` (Jordan's inequality). -/
lemma jordan_nrm (θ : ℝ) :
    4 * nrm θ ≤ ‖Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) - 1‖ := by
  set t : ℝ := θ - round θ with ht
  have ht2 : |t| ≤ 1 / 2 := abs_sub_round θ
  have e : Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    have h1 : Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ) =
        Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) + (round θ : ℤ) * (2 * Real.pi * Complex.I) := by
      simp only [ht]; push_cast; ring
    rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [e, Complex.norm_exp_I_mul_ofReal_sub_one, nrm_eq]
  have h2 : (2 * Real.pi * t) / 2 = Real.pi * t := by ring
  rw [h2, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hpos : 0 ≤ Real.sin (Real.pi * |t|) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos, abs_nonneg t])
  have hsin : 2 / Real.pi * (Real.pi * |t|) ≤ Real.sin (Real.pi * |t|) := by
    apply Real.mul_le_sin (by positivity)
    nlinarith [Real.pi_pos, abs_nonneg t]
  have hsimp : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by
    field_simp
  have habs : |Real.sin (Real.pi * t)| = Real.sin (Real.pi * |t|) := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h] at hpos ⊢
      exact abs_of_nonneg hpos
    · rw [h] at hpos ⊢
      rw [mul_neg, Real.sin_neg] at hpos ⊢
      exact abs_of_nonpos (by linarith)
  rw [habs, abs_two]
  nlinarith [hsin, hsimp]

lemma exp_eq_one_of_nrm_zero (θ : ℝ) (h : nrm θ = 0) :
    Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) = 1 := by
  have h0 : θ = ((round θ : ℤ) : ℝ) := by
    rw [nrm_eq] at h
    linarith [abs_eq_zero.mp h]
  have : Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ) = (round θ : ℤ) * (2 * Real.pi * Complex.I) := by
    conv_lhs => rw [h0]
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- The completion of `(ℤ, S)`. -/
abbrev ZG (S : AddGroupSeminorm ℤ) : Type := UniformSpace.Completion (ZS S)

instance (S : AddGroupSeminorm ℤ) : MeasurableSpace (ZG S) := borel _
instance (S : AddGroupSeminorm ℤ) : BorelSpace (ZG S) := ⟨rfl⟩

/-- The embedding `ℤ → ZG S`. -/
noncomputable def ZG.ι (S : AddGroupSeminorm ℤ) : ℤ →+ ZG S where
  toFun n := ((show ZS S from n : ZS S) : UniformSpace.Completion (ZS S))
  map_zero' := UniformSpace.Completion.coe_zero
  map_add' a b := UniformSpace.Completion.coe_add (show ZS S from a) (show ZS S from b)

lemma ZG.norm_ι (S : AddGroupSeminorm ℤ) (n : ℤ) : ‖ZG.ι S n‖ = S n := by
  show ‖((show ZS S from n : ZS S) : UniformSpace.Completion (ZS S))‖ = S n
  rw [UniformSpace.Completion.norm_coe]
  rfl

lemma ZG_compact (S : AddGroupSeminorm ℤ)
    (hF : ∀ ε > 0, ∃ F : Finset ℤ, ∀ z : ℤ, ∃ f ∈ F, S (z - f) < ε) : CompactSpace (ZG S) := by
  have htb : TotallyBounded (Set.univ : Set (ZS S)) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨F, hF'⟩ := hF ε hε
    refine ⟨(fun f : ℤ => (f : ZS S)) '' (F : Set ℤ), (Finset.finite_toSet F).image _, ?_⟩
    intro z _
    obtain ⟨f, hf, hzf⟩ := hF' (show ℤ from z)
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Metric.mem_ball]
    refine ⟨(f : ZS S), ⟨f, hf, rfl⟩, ?_⟩
    rw [@dist_eq_norm (ZS S) _ z (show ZS S from f)]
    exact hzf
  have h1 : TotallyBounded (Set.range ((↑) : ZS S → UniformSpace.Completion (ZS S))) := by
    rw [← Set.image_univ]
    exact htb.image (UniformSpace.Completion.uniformContinuous_coe (ZS S))
  have h2 : TotallyBounded (Set.univ : Set (UniformSpace.Completion (ZS S))) := by
    have := h1.closure
    rwa [(UniformSpace.Completion.denseRange_coe).closure_range] at this
  exact ⟨h2.isCompact_of_isClosed isClosed_univ⟩

/-- **Weil's theorem for `ℤ`, seminorm form.** -/
theorem weil_seminorm (S : AddGroupSeminorm ℤ)
    (hF : ∀ ε > 0, ∃ F : Finset ℤ, ∀ z : ℤ, ∃ f ∈ F, S (z - f) < ε) (m : ℤ) (hm : 0 < S m) :
    ∃ α : ℝ, (∀ η > 0, ∃ δ > 0, ∀ n : ℤ, S n < δ → nrm ((n : ℝ) * α) < η) ∧
      0 < nrm ((m : ℝ) * α) := by
  classical
  haveI := ZG_compact S hF
  have hnsmul : ∀ n : ℤ, n • ZG.ι S 1 = ZG.ι S n := by
    intro n; rw [← map_zsmul, smul_eq_mul, mul_one]
  have hmg : m • ZG.ι S 1 ≠ 0 := by
    rw [hnsmul]
    intro h
    have := ZG.norm_ι S m
    rw [h, norm_zero] at this
    exact hm.ne this
  obtain ⟨ζ, F, hζ, hζm, hFc, ⟨x₀, hx₀⟩, hFg⟩ := JAWeil.weil_abstract (ZG.ι S 1) m hmg
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, norm_zero] at hζ; exact zero_ne_one hζ
  have hFn : ∀ n : ℤ, F (x₀ + n • ZG.ι S 1) = ζ ^ n * F x₀ := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih =>
      have : x₀ + ((n : ℤ) + 1) • ZG.ι S 1 = (x₀ + (n : ℤ) • ZG.ι S 1) + ZG.ι S 1 := by
        rw [add_smul, one_smul]; abel
      rw [this, hFg, ih, zpow_add_one₀ hζ0]; ring
    | pred n ih =>
      have h1 : x₀ + (-(n : ℤ)) • ZG.ι S 1 =
          (x₀ + (-(n : ℤ) - 1) • ZG.ι S 1) + ZG.ι S 1 := by
        rw [sub_smul, one_smul]; abel
      have h2 := hFg (x₀ + (-(n : ℤ) - 1) • ZG.ι S 1)
      rw [← h1, ih] at h2
      rw [zpow_sub_one₀ hζ0]
      have : F (x₀ + (-(n : ℤ) - 1) • ZG.ι S 1) = ζ⁻¹ * (ζ ^ (-(n : ℤ)) * F x₀) := by
        rw [← inv_mul_cancel_left₀ hζ0 (F (x₀ + (-(n : ℤ) - 1) • ZG.ι S 1)), ← h2]
      rw [this]; ring
  set α : ℝ := Complex.arg ζ / (2 * Real.pi) with hα
  have hζα : ∀ n : ℤ, ζ ^ n = Complex.exp (Complex.I * ((2 * Real.pi * ((n : ℝ) * α) : ℝ) : ℂ)) := by
    intro n
    have h1 : ζ = Complex.exp (Complex.arg ζ * Complex.I) := by
      have := Complex.norm_mul_exp_arg_mul_I ζ
      rw [hζ] at this
      simpa using this.symm
    conv_lhs => rw [h1]
    rw [← Complex.exp_int_mul]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    rw [hα]
    push_cast
    field_simp
  have hFK : 0 < ‖F x₀‖ := norm_pos_iff.mpr hx₀
  refine ⟨α, ?_, ?_⟩
  · intro η hη
    have huc := (CompactSpace.uniformContinuous_of_continuous hFc)
    rw [Metric.uniformContinuous_iff] at huc
    obtain ⟨δ, hδ, hδ'⟩ := huc (4 * η * ‖F x₀‖) (by positivity)
    refine ⟨δ, hδ, fun n hn => ?_⟩
    have hdist : dist (x₀ + n • ZG.ι S 1) x₀ < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, hnsmul, ZG.norm_ι]
      exact hn
    have h1 := hδ' hdist
    rw [dist_eq_norm, hFn] at h1
    have h2 : ‖ζ ^ n - 1‖ * ‖F x₀‖ < 4 * η * ‖F x₀‖ := by
      have : ζ ^ n * F x₀ - F x₀ = (ζ ^ n - 1) * F x₀ := by ring
      rw [this, norm_mul] at h1
      exact h1
    have h3 : ‖ζ ^ n - 1‖ < 4 * η := lt_of_mul_lt_mul_right h2 hFK.le
    have h4 := jordan_nrm ((n : ℝ) * α)
    rw [← hζα n] at h4
    linarith
  · by_contra hcon
    have h0 : nrm ((m : ℝ) * α) = 0 := le_antisymm (not_lt.mp hcon) (nrm_nonneg _)
    exact hζm (by rw [hζα m]; exact exp_eq_one_of_nrm_zero _ h0)

#print axioms weil_seminorm

end JAWeil
end LeanCheck
