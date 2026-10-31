import Mathlib

/-!
# Weil's theorem for `ℤ`, part A: Haar measure, `L²`, translations

Setting: `G` is a compact normed abelian group with its Borel `σ`-algebra.  `mu G` is the Haar probability measure,
`H = L²(G, mu)`.  We construct the translation operators `tau a : H →ₗᵢ H` and prove the algebra needed later:
`tau (a+b) = tau a ∘ tau b`, `tau 0 = id`, the adjoint of `tau a` is `tau (-a)`, and `tau a` acts on continuous functions by
translation.
-/

namespace LeanCheck
namespace JAWeil

open MeasureTheory Filter

variable (G : Type*) [NormedAddCommGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar probability measure. -/
noncomputable def mu : Measure G := Measure.addHaarMeasure ⊤

instance : (mu G).IsAddHaarMeasure := by unfold mu; infer_instance

instance : IsProbabilityMeasure (mu G) := by
  constructor
  have := Measure.addHaarMeasure_self (G := G) (K₀ := ⊤)
  simpa [mu] using this

instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

/-- The Hilbert space `L²(G, mu)`. -/
abbrev H : Type _ := Lp ℂ 2 (mu G)

variable {G}

/-- Translation by `a`: `(tau a f)(x) = f(x + a)`. -/
noncomputable def tau (a : G) : H G →ₗᵢ[ℂ] H G :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : G => x + a) (measurePreserving_add_right (mu G) a)

lemma tau_ae (a : G) (f : H G) : (tau a f : G → ℂ) =ᵐ[mu G] fun x => f (x + a) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right (mu G) a)

lemma tau_comp_ae (a b : G) (f : H G) :
    (tau a (tau b f) : G → ℂ) =ᵐ[mu G] fun x => f (x + a + b) := by
  have h2 := tau_ae b f
  have h3 := (measurePreserving_add_right (mu G) a).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [tau_ae a (tau b f), h3] with x hx1 hx2
  simp only [Function.comp] at hx2
  exact hx1.trans hx2

lemma tau_add (a b : G) (f : H G) : tau a (tau b f) = tau (a + b) f := by
  apply Lp.ext
  refine (tau_comp_ae a b f).trans ?_
  refine EventuallyEq.trans ?_ (tau_ae (a + b) f).symm
  filter_upwards with x
  simp [add_assoc, add_comm b a]

lemma tau_zero (f : H G) : tau 0 f = f := by
  apply Lp.ext
  refine (tau_ae 0 f).trans ?_
  filter_upwards with x
  simp

lemma tau_neg_tau (a : G) (f : H G) : tau (-a) (tau a f) = f := by
  rw [tau_add, neg_add_cancel, tau_zero]

lemma tau_tau_neg (a : G) (f : H G) : tau a (tau (-a) f) = f := by
  rw [tau_add, add_neg_cancel, tau_zero]

lemma tau_inner (a : G) (f g : H G) : inner ℂ (tau a f) g = inner ℂ f (tau (-a) g) := by
  have h : inner ℂ (tau a f) (tau a (tau (-a) g)) = inner ℂ f (tau (-a) g) :=
    (tau a).inner_map_map f (tau (-a) g)
  rw [tau_tau_neg] at h
  exact h

/-- `tau` of the class of a continuous function is the class of the translated function. -/
lemma tau_toLp (a : G) (w : C(G, ℂ)) :
    tau a (ContinuousMap.toLp 2 (mu G) ℂ w) =
      ContinuousMap.toLp 2 (mu G) ℂ (w.comp (ContinuousMap.addRight a)) := by
  apply Lp.ext
  refine (tau_ae a _).trans ?_
  have h1 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (mu G) w
  have h2 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (mu G) (w.comp (ContinuousMap.addRight a))
  have h3 : (fun x => (ContinuousMap.toLp 2 (mu G) ℂ w : G → ℂ) (x + a)) =ᵐ[mu G] fun x => w (x + a) :=
    (measurePreserving_add_right (mu G) a).quasiMeasurePreserving.ae_eq_comp h1
  refine h3.trans ?_
  refine EventuallyEq.trans ?_ h2.symm
  filter_upwards with x
  rfl

#print axioms tau_inner
#print axioms tau_toLp

end JAWeil
end LeanCheck
