import LeanCheck.ChainPW2
import LeanCheck.ChainPW3

/-!
# Peter–Weyl, part 4: translations on `L²` of a compact abelian group, and convolution operators

`tr a` is translation by `a` on `L²(μ)` (a linear isometry for a Haar measure `μ`); convolution kernels
`f(x - y)` give integral operators commuting with all translations.  `D = (tr x₀ - 1) ∘ T_f` and
`B = D†D` are used in part 5 to produce a character that is nontrivial at `x₀`.
-/

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace LeanCheck
namespace PW

variable {K : Type} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
  [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsAddHaarMeasure]

/-- Translation by `a`, a linear isometry of `L²(μ)`. -/
noncomputable def tr (a : K) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : K => x + a) (measurePreserving_add_right μ a)

lemma tr_coe (a : K) (h : Lp ℂ 2 μ) : (tr μ a h : K → ℂ) =ᵐ[μ] (h : K → ℂ) ∘ (fun x => x + a) :=
  Lp.coeFn_compMeasurePreserving h (measurePreserving_add_right μ a)

lemma tr_ι (a : K) (F : C(K, ℂ)) :
    tr μ a (ι μ F) = ι μ (F.comp (ContinuousMap.addRight a)) := by
  refine Lp.ext ?_
  have h1 := tr_coe μ a (ι μ F)
  have h2 : (ι μ F : K → ℂ) =ᵐ[μ] F := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ F
  have h3 : ((ι μ F : K → ℂ) ∘ (fun x => x + a)) =ᵐ[μ] (F : K → ℂ) ∘ (fun x => x + a) :=
    (measurePreserving_add_right μ a).quasiMeasurePreserving.ae_eq_comp h2
  have h4 : (ι μ (F.comp (ContinuousMap.addRight a)) : K → ℂ) =ᵐ[μ]
      (F.comp (ContinuousMap.addRight a) : K → ℂ) :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ _
  exact h1.trans (h3.trans h4.symm)

lemma tr_add (a b : K) (h : Lp ℂ 2 μ) : tr μ a (tr μ b h) = tr μ (a + b) h := by
  refine Lp.ext ?_
  have h1 := tr_coe μ a (tr μ b h)
  have h2 := tr_coe μ b h
  have h3 : ((tr μ b h : K → ℂ) ∘ (fun x => x + a)) =ᵐ[μ]
      ((h : K → ℂ) ∘ (fun x => x + b)) ∘ (fun x => x + a) :=
    (measurePreserving_add_right μ a).quasiMeasurePreserving.ae_eq_comp h2
  have h4 := tr_coe μ (a + b) h
  refine h1.trans (h3.trans (Filter.EventuallyEq.trans ?_ h4.symm))
  exact Filter.Eventually.of_forall (fun x => by simp [Function.comp, add_assoc])

lemma tr_zero (h : Lp ℂ 2 μ) : tr μ 0 h = h := by
  refine Lp.ext ?_
  refine (tr_coe μ 0 h).trans (Filter.Eventually.of_forall (fun x => by simp))

lemma tr_comm (a b : K) (h : Lp ℂ 2 μ) : tr μ a (tr μ b h) = tr μ b (tr μ a h) := by
  rw [tr_add, tr_add, add_comm]

lemma tr_inner (a : K) (u h : Lp ℂ 2 μ) : ⟪u, tr μ a h⟫_ℂ = ⟪tr μ (-a) u, h⟫_ℂ := by
  have : ⟪tr μ (-a) u, h⟫_ℂ = ⟪tr μ a (tr μ (-a) u), tr μ a h⟫_ℂ :=
    ((tr μ a).inner_map_map _ _).symm
  rw [this, tr_add, add_neg_cancel, tr_zero]

lemma tr_inner_left (a : K) (u h : Lp ℂ 2 μ) : ⟪tr μ a u, h⟫_ℂ = ⟪u, tr μ (-a) h⟫_ℂ := by
  rw [tr_inner, neg_neg]

/-! ### Convolution operators -/

/-- The kernel `f(x - y)`. -/
def convK (f : C(K, ℂ)) : C(K × K, ℂ) :=
  ⟨fun p => f (p.1 - p.2), f.continuous.comp (continuous_fst.sub continuous_snd)⟩

lemma convK_apply (f : C(K, ℂ)) (p : K × K) : convK f p = f (p.1 - p.2) := rfl

/-- Convolution operators commute with translations. -/
theorem Tconv_comm (f : C(K, ℂ)) (a : K) (h : Lp ℂ 2 μ) :
    Tk μ (convK f) (tr μ a h) = tr μ a (Tk μ (convK f) h) := by
  rw [Tk_apply, Tk_apply, tr_ι]
  congr 1
  ext x
  show Gam μ (convK f) (tr μ a h) x = Gam μ (convK f) h (x + a)
  rw [Gam_apply, Gam_apply, Ak_apply, Ak_apply, tr_inner, tr_ι]
  have : (star ((convK f).curry x)).comp (ContinuousMap.addRight (-a)) =
      star ((convK f).curry (x + a)) := by
    ext y
    simp only [ContinuousMap.comp_apply, ContinuousMap.star_apply, ContinuousMap.curry_apply,
      convK_apply, ContinuousMap.coe_addRight]
    congr 2
    abel
  rw [this]

end PW
end LeanCheck
