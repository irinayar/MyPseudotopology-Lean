import Mathlib
import LeanCheck.DD3Weil2

/-!
# Weil's theorem for `ℤ × ℤ`, seminorm form (Lean check)

Scope. Second part of the compact-quotient step for `ℤ²` in the Lean version of the conditional proof of `DD({2,3,5})`
(research note `TVGplus_conditional_DD235_2026-11-07.md`, item 7); the counterpart of `JAWeilD.weil_seminorm`.

`weil_seminorm2`: if `S` is an additive group seminorm on `ℤ × ℤ` which is precompact (for every `ε` there is a finite `F`
with `ℤ² = F + {S < ε}`) and `S m > 0`, then there are `α, β ∈ ℝ` such that `(n₁, n₂) ↦ e(n₁ α + n₂ β)` is `S`-continuous at
`0` (for every `η > 0` there is `δ > 0` with `‖n₁ α + n₂ β‖ < η` whenever `S n < δ`) and `‖m₁ α + m₂ β‖ > 0`.

Proof: the completion `G` of `(ℤ², S)` is a compact normed abelian group; apply `DD3Weil2.weil_abstract2` to the images of
`(1,0)` and `(0,1)`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3WeilZ2

open MixedPrime JAWeil

/-- `ℤ × ℤ` with the group seminorm `S`. -/
def ZS2 (_ : AddGroupSeminorm (ℤ × ℤ)) : Type := ℤ × ℤ

instance (S : AddGroupSeminorm (ℤ × ℤ)) : AddCommGroup (ZS2 S) := inferInstanceAs (AddCommGroup (ℤ × ℤ))

/-- The seminorm as a seminorm on `ZS2 S`. -/
def ZS2.sem (S : AddGroupSeminorm (ℤ × ℤ)) : AddGroupSeminorm (ZS2 S) where
  toFun := fun m => S (show ℤ × ℤ from m)
  map_zero' := S.map_zero'
  add_le' := S.add_le'
  neg' := S.neg'

instance (S : AddGroupSeminorm (ℤ × ℤ)) : SeminormedAddCommGroup (ZS2 S) :=
  (ZS2.sem S).toSeminormedAddCommGroup

lemma ZS2.norm_def (S : AddGroupSeminorm (ℤ × ℤ)) (m : ZS2 S) : ‖m‖ = S (show ℤ × ℤ from m) := rfl

/-- The completion of `(ℤ × ℤ, S)`. -/
abbrev ZG2 (S : AddGroupSeminorm (ℤ × ℤ)) : Type := UniformSpace.Completion (ZS2 S)

instance (S : AddGroupSeminorm (ℤ × ℤ)) : MeasurableSpace (ZG2 S) := borel _
instance (S : AddGroupSeminorm (ℤ × ℤ)) : BorelSpace (ZG2 S) := ⟨rfl⟩

/-- The embedding `ℤ × ℤ → ZG2 S`. -/
noncomputable def ZG2.ι (S : AddGroupSeminorm (ℤ × ℤ)) : ℤ × ℤ →+ ZG2 S where
  toFun n := ((show ZS2 S from n : ZS2 S) : UniformSpace.Completion (ZS2 S))
  map_zero' := UniformSpace.Completion.coe_zero
  map_add' a b := UniformSpace.Completion.coe_add (show ZS2 S from a) (show ZS2 S from b)

lemma ZG2.norm_ι (S : AddGroupSeminorm (ℤ × ℤ)) (n : ℤ × ℤ) : ‖ZG2.ι S n‖ = S n := by
  show ‖((show ZS2 S from n : ZS2 S) : UniformSpace.Completion (ZS2 S))‖ = S n
  rw [UniformSpace.Completion.norm_coe]
  rfl

lemma ZG2_compact (S : AddGroupSeminorm (ℤ × ℤ))
    (hF : ∀ ε > 0, ∃ F : Finset (ℤ × ℤ), ∀ z : ℤ × ℤ, ∃ f ∈ F, S (z - f) < ε) : CompactSpace (ZG2 S) := by
  have htb : TotallyBounded (Set.univ : Set (ZS2 S)) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨F, hF'⟩ := hF ε hε
    refine ⟨(fun f : ℤ × ℤ => (f : ZS2 S)) '' (F : Set (ℤ × ℤ)), (Finset.finite_toSet F).image _, ?_⟩
    intro z _
    obtain ⟨f, hf, hzf⟩ := hF' (show ℤ × ℤ from z)
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Metric.mem_ball]
    refine ⟨(f : ZS2 S), ⟨f, hf, rfl⟩, ?_⟩
    rw [@dist_eq_norm (ZS2 S) _ z (show ZS2 S from f)]
    exact hzf
  have h1 : TotallyBounded (Set.range ((↑) : ZS2 S → UniformSpace.Completion (ZS2 S))) := by
    rw [← Set.image_univ]
    exact htb.image (UniformSpace.Completion.uniformContinuous_coe (ZS2 S))
  have h2 : TotallyBounded (Set.univ : Set (UniformSpace.Completion (ZS2 S))) := by
    have := h1.closure
    rwa [(UniformSpace.Completion.denseRange_coe).closure_range] at this
  exact ⟨h2.isCompact_of_isClosed isClosed_univ⟩

/-- A unit complex number as an exponential. -/
lemma zpow_eq_exp (ζ : ℂ) (hζ : ‖ζ‖ = 1) (n : ℤ) :
    ζ ^ n = Complex.exp (Complex.I * ((2 * Real.pi * ((n : ℝ) * (Complex.arg ζ / (2 * Real.pi))) : ℝ) : ℂ)) := by
  have h1 : ζ = Complex.exp (Complex.arg ζ * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I ζ
    rw [hζ] at this
    simpa using this.symm
  conv_lhs => rw [h1]
  rw [← Complex.exp_int_mul]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- `F (x + n • g) = ζ^n F x`. -/
lemma F_zsmul {G : Type*} [AddCommGroup G] (F : G → ℂ) (g : G) (ζ : ℂ) (hζ0 : ζ ≠ 0)
    (hFg : ∀ x, F (x + g) = ζ * F x) (n : ℤ) (x : G) : F (x + n • g) = ζ ^ n * F x := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have : x + ((n : ℤ) + 1) • g = (x + (n : ℤ) • g) + g := by
      rw [add_smul, one_smul]; abel
    rw [this, hFg, ih, zpow_add_one₀ hζ0]; ring
  | pred n ih =>
    have h1 : x + (-(n : ℤ)) • g = (x + (-(n : ℤ) - 1) • g) + g := by
      rw [sub_smul, one_smul]; abel
    have h2 := hFg (x + (-(n : ℤ) - 1) • g)
    rw [← h1, ih] at h2
    rw [zpow_sub_one₀ hζ0]
    have : F (x + (-(n : ℤ) - 1) • g) = ζ⁻¹ * (ζ ^ (-(n : ℤ)) * F x) := by
      rw [← inv_mul_cancel_left₀ hζ0 (F (x + (-(n : ℤ) - 1) • g)), ← h2]
    rw [this]; ring

/-- **Weil's theorem for `ℤ × ℤ`, seminorm form.** -/
theorem weil_seminorm2 (S : AddGroupSeminorm (ℤ × ℤ))
    (hF : ∀ ε > 0, ∃ F : Finset (ℤ × ℤ), ∀ z : ℤ × ℤ, ∃ f ∈ F, S (z - f) < ε) (m : ℤ × ℤ) (hm : 0 < S m) :
    ∃ α β : ℝ, (∀ η > 0, ∃ δ > 0, ∀ n : ℤ × ℤ, S n < δ → nrm ((n.1 : ℝ) * α + (n.2 : ℝ) * β) < η) ∧
      0 < nrm ((m.1 : ℝ) * α + (m.2 : ℝ) * β) := by
  classical
  haveI := ZG2_compact S hF
  set g₁ : ZG2 S := ZG2.ι S (1, 0) with hg₁
  set g₂ : ZG2 S := ZG2.ι S (0, 1) with hg₂
  have hι : ∀ n : ℤ × ℤ, ZG2.ι S n = n.1 • g₁ + n.2 • g₂ := by
    intro n
    have : n = n.1 • ((1 : ℤ), (0 : ℤ)) + n.2 • ((0 : ℤ), (1 : ℤ)) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_zsmul, map_zsmul]
  have hmg : m.1 • g₁ + m.2 • g₂ ≠ 0 := by
    rw [← hι]
    intro h
    have := ZG2.norm_ι S m
    rw [h, norm_zero] at this
    exact hm.ne this
  obtain ⟨ζ₁, ζ₂, F, hζ₁, hζ₂, hζm, hFc, ⟨x₀, hx₀⟩, hF1, hF2⟩ :=
    DD3Weil2.weil_abstract2 g₁ g₂ m.1 m.2 hmg
  have hζ₁0 : ζ₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hζ₁; exact zero_ne_one hζ₁
  have hζ₂0 : ζ₂ ≠ 0 := by
    intro h; rw [h, norm_zero] at hζ₂; exact zero_ne_one hζ₂
  have hFn : ∀ n : ℤ × ℤ, F (x₀ + ZG2.ι S n) = ζ₁ ^ n.1 * ζ₂ ^ n.2 * F x₀ := by
    intro n
    rw [hι, show x₀ + (n.1 • g₁ + n.2 • g₂) = (x₀ + n.2 • g₂) + n.1 • g₁ by abel,
      F_zsmul F g₁ ζ₁ hζ₁0 hF1 n.1, F_zsmul F g₂ ζ₂ hζ₂0 hF2 n.2]
    ring
  set α : ℝ := Complex.arg ζ₁ / (2 * Real.pi) with hα
  set β : ℝ := Complex.arg ζ₂ / (2 * Real.pi) with hβ
  have hprod : ∀ n : ℤ × ℤ, ζ₁ ^ n.1 * ζ₂ ^ n.2 =
      Complex.exp (Complex.I * ((2 * Real.pi * ((n.1 : ℝ) * α + (n.2 : ℝ) * β) : ℝ) : ℂ)) := by
    intro n
    rw [zpow_eq_exp ζ₁ hζ₁ n.1, zpow_eq_exp ζ₂ hζ₂ n.2, ← Complex.exp_add]
    congr 1
    rw [hα, hβ]
    push_cast
    ring
  have hFK : 0 < ‖F x₀‖ := norm_pos_iff.mpr hx₀
  refine ⟨α, β, ?_, ?_⟩
  · intro η hη
    have huc := (CompactSpace.uniformContinuous_of_continuous hFc)
    rw [Metric.uniformContinuous_iff] at huc
    obtain ⟨δ, hδ, hδ'⟩ := huc (4 * η * ‖F x₀‖) (by positivity)
    refine ⟨δ, hδ, fun n hn => ?_⟩
    have hdist : dist (x₀ + ZG2.ι S n) x₀ < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, ZG2.norm_ι]
      exact hn
    have h1 := hδ' hdist
    rw [dist_eq_norm, hFn] at h1
    have h2 : ‖ζ₁ ^ n.1 * ζ₂ ^ n.2 - 1‖ * ‖F x₀‖ < 4 * η * ‖F x₀‖ := by
      have : ζ₁ ^ n.1 * ζ₂ ^ n.2 * F x₀ - F x₀ = (ζ₁ ^ n.1 * ζ₂ ^ n.2 - 1) * F x₀ := by ring
      rw [this, norm_mul] at h1
      exact h1
    have h3 : ‖ζ₁ ^ n.1 * ζ₂ ^ n.2 - 1‖ < 4 * η := lt_of_mul_lt_mul_right h2 hFK.le
    have h4 := jordan_nrm ((n.1 : ℝ) * α + (n.2 : ℝ) * β)
    rw [← hprod n] at h4
    linarith
  · by_contra hcon
    have h0 : nrm ((m.1 : ℝ) * α + (m.2 : ℝ) * β) = 0 := le_antisymm (not_lt.mp hcon) (nrm_nonneg _)
    apply hζm
    rw [hprod m]
    exact exp_eq_one_of_nrm_zero _ h0

#print axioms weil_seminorm2

end DD3WeilZ2
end LeanCheck
