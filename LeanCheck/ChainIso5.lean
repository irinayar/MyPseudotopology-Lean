import LeanCheck.ChainIso4

/-!
# Isomorphism classification, part 5: isomorphism types of `τ_{f,S}`
(TVGQ-v7 Corollary `tauiso:types`)

`(ℝ, τ_{f,S}) ≅ (ℝ, τ_{g,T})` iff `FsetScaled g c T = Fset f S` for some `c ≠ 0`; a scalar isomorphism
then exists, so the continuous scalar rings agree; distinct subalgebras give non-isomorphic groups.
-/

namespace LeanCheck

open Filter Topology

lemma tau_scale_cont_iff (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (c : ℝ) :
    Continuous[tauT f S, tauT g T] (fun x : ℝ => c * x) ↔ FsetScaled g c T ⊆ Fset f S := by
  constructor
  · intro h
    exact tau_hom_necessary f g S T (AddMonoidHom.mulLeft c) c (κ := Empty) Empty.elim Empty.elim
      (fun j => j.elim) (fun x => by simp) h
  · intro h
    exact tau_hom_sufficient f g S T (AddMonoidHom.mulLeft c) c (κ := Empty) Empty.elim Empty.elim
      (fun j => j.elim) (fun x => by simp) h

/-- Every isomorphism has the form `L x = c (x + Λ x)` with `c ≠ 0` (a countable-image argument). -/
lemma tau_iso_rep (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (L : ℝ ≃+ ℝ)
    (h1 : Continuous[tauT f S, tauT g T] L) :
    ∃ (c : ℝ) (κ : Type) (_ : Fintype κ) (b σ : κ → ℝ), c ≠ 0 ∧ (∀ j, b j ∈ S) ∧
      ∀ x, L x = c * (x + LamHom f b σ x) := by
  have hU : Continuous[tauT f S, uR'] (L : ℝ →+ ℝ) :=
    continuous_le_rng (TfS_le_usual g T usualQ) h1
  obtain ⟨c, κ, hκ, b, d, hb, hform⟩ := (tau_real_iff f S (L : ℝ →+ ℝ)).1 hU
  have hc : c ≠ 0 := by
    intro hc0
    have h01 : (1 : ℝ) ≠ 0 := one_ne_zero
    apply h01
    refine eq_zero_of_span (1 : ℝ) d (fun y => ?_)
    refine ⟨fun j => f (b j * L.symm y), ?_⟩
    have := hform (L.symm y)
    rw [hc0, zero_mul, zero_add] at this
    show 1 * y = ∑ i, d i * ((f (b i * L.symm y) : ℚ) : ℝ)
    rw [one_mul]
    exact (L.apply_symm_apply y).symm.trans this
  refine ⟨c, κ, hκ, b, fun j => d j / c, hc, hb, fun x => ?_⟩
  show (L : ℝ →+ ℝ) x = _
  rw [hform x, LamHom_apply, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by field_simp)

/-- **Isomorphism types of the real-valued observation spaces** (TVGQ-v7 Corollary `tauiso:types`). -/
theorem tau_iso_iff (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) :
    IsoTop (tauT f S) (tauT g T) ↔ ∃ c : ℝ, c ≠ 0 ∧ FsetScaled g c T = Fset f S := by
  constructor
  · rintro ⟨L, h1, h2⟩
    obtain ⟨c, κ, hκ, b, σ, hc, hb, hL⟩ := tau_iso_rep f g S T L h1
    obtain ⟨-, heq⟩ := (tau_iso_criterion f g S T c hc b σ hb (L : ℝ →+ ℝ) hL).1
      ⟨L, fun x => rfl, h1, h2⟩
    exact ⟨c, hc, heq⟩
  · rintro ⟨c, hc, h⟩
    refine ⟨{ toFun := fun x => c * x, invFun := fun x => c⁻¹ * x,
              left_inv := fun x => by field_simp, right_inv := fun x => by field_simp,
              map_add' := fun x y => by ring }, ?_, ?_⟩
    · exact (tau_scale_cont_iff f g S T c).2 h.subset
    · exact (tau_scale_cont_iff g f T S c⁻¹).2 (fscaled_sub_inv f g S T c hc h)

/-- A scalar isomorphism exists whenever an isomorphism does, so the scalar ring is invariant. -/
theorem scalarCont_eq_of_iso_tau (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ)
    (h : IsoTop (tauT f S) (tauT g T)) : scalarCont (tauT f S) = scalarCont (tauT g T) := by
  obtain ⟨c, hc, heq⟩ := (tau_iso_iff f g S T).1 h
  have h1 : Continuous[tauT f S, tauT g T] (fun x : ℝ => c * x) :=
    (tau_scale_cont_iff f g S T c).2 heq.subset
  have h2 : Continuous[tauT g T, tauT f S] (fun x : ℝ => c⁻¹ * x) :=
    (tau_scale_cont_iff g f T S c⁻¹).2 (fscaled_sub_inv f g S T c hc heq)
  refine Set.Subset.antisymm (scalarCont_subset_of_scale _ _ c hc h1 h2) ?_
  have h2' : Continuous[tauT f S, tauT g T] (fun x : ℝ => (c⁻¹)⁻¹ * x) := by
    rw [inv_inv]; exact h1
  exact scalarCont_subset_of_scale _ _ c⁻¹ (inv_ne_zero hc) h2 h2'

lemma scalarCont_tau_alg (f : ℝ →+ ℚ) (hf : f ≠ 0) (A : Subalgebra ℚ ℝ) :
    scalarCont (tauT f (Subalgebra.toSubmodule A)) = (A : Set ℝ) := by
  obtain ⟨u, hu⟩ := exists_unit f hf
  ext r
  show Continuous[tauT f (Subalgebra.toSubmodule A), tauT f (Subalgebra.toSubmodule A)]
      (fun x : ℝ => r * x) ↔ r ∈ (A : Set ℝ)
  rw [scalar_tau f u hu _ r, scalarRing_algebra]

/-- Distinct subalgebras (in particular intermediate fields) give non-isomorphic `τ`-groups. -/
theorem iso_algebra_tau (f g : ℝ →+ ℚ) (hf : f ≠ 0) (hg : g ≠ 0) (A A' : Subalgebra ℚ ℝ)
    (h : IsoTop (tauT f (Subalgebra.toSubmodule A)) (tauT g (Subalgebra.toSubmodule A'))) :
    A = A' := by
  have := scalarCont_eq_of_iso_tau f g _ _ h
  rw [scalarCont_tau_alg f hf, scalarCont_tau_alg g hg] at this
  exact SetLike.coe_injective this

theorem iso_fixed_tau (f : ℝ →+ ℚ) (hf : f ≠ 0) (S T : Submodule ℚ ℝ) :
    IsoTop (tauT f S) (tauT f T) ↔
      ∃ c : ℝ, c ≠ 0 ∧ ∀ y : ℝ, y ∈ S ↔ ∃ a ∈ T, y = c * a := by
  rw [tau_iso_iff]
  exact exists_congr fun c => and_congr_right fun _ => fscaled_eq_iff f hf S T c

theorem iso_Q_tau (f g : ℝ →+ ℚ) (hf : f ≠ 0) :
    IsoTop (tauT f ratSub) (tauT g ratSub) ↔
      ∃ c : ℝ, c ≠ 0 ∧ ∃ r : ℚ, r ≠ 0 ∧ ∀ x : ℝ, g (c * x) = r * f x := by
  rw [tau_iso_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨r, hr, hh⟩ := (fscaled_Q_iff f g hf c).1 h
    exact ⟨c, hc, r, hr, hh⟩
  · rintro ⟨c, hc, r, hr, hh⟩
    exact ⟨c, hc, (fscaled_Q_iff f g hf c).2 ⟨r, hr, hh⟩⟩

end LeanCheck
