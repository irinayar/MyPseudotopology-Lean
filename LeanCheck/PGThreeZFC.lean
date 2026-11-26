import Mathlib
import LeanCheck.PGThreeBohr
import LeanCheck.PGThreeExact

/-!
# PGthree: the cofinite filter at zero is a vicinity filter, without set-theoretic hypotheses (Lean check)

Scope. Section 4 of the third article (`PGthree.tex`).

* `integral_ev`, `finite_large_coeff` : on the compact group of all characters, the coefficients of a measurable set
  along the evaluations tend to `0`;
* `both_sides` : for a set of characters of positive measure and all but finitely many `a`, the real part of `χ (n a)`
  is above `1/8` on a set of positive measure and below `-1/8` on another;
* `interpolation` : every infinite subset of `H` has a sequence along which these signs can be chosen freely;
* `exists_exponents` : the condition (E) on `H`;
* `vicinity_without_hypotheses` : if `H` is an infinite subgroup of an abelian group `G` with at most `2 ^ 𝔠` elements
  satisfying (E), there is a set of ultrafilters whose PG has unique limits and whose vicinity filter consists of the
  sets that contain `0` and all but finitely many points of `H`;
* `card_le_of_vicinity` : that cardinality bound is necessary;
* `vicinity_iff` : the filter above is the vicinity filter of some PG exactly when the bound and (E) hold;
* `int_cofinite` : the case of the cofinite filter at `0` on `ℤ`.

No set-theoretic hypothesis is used. A Lean proof verifies its formal statement under its hypotheses; the
correspondence with the article requires mathematical review.
-/

open Filter Set Topology MeasureTheory

open scoped ComplexConjugate Cardinal

namespace PG

namespace ZFC

open Sel PG.Bohr

variable {G : Type} [AddCommGroup G]

/-! ### The compact group of characters -/

/-- All characters of `G`, with the topology of pointwise convergence. -/
def Dual (G : Type) [AddCommGroup G] : AddSubgroup (G → UnitAddCircle) where
  carrier := {f | ∀ a b, f (a + b) = f a + f b}
  zero_mem' := fun a b => by simp
  add_mem' := by
    intro f g hf hg a b
    simp only [Pi.add_apply, hf a b, hg a b]
    abel
  neg_mem' := by
    intro f hf a b
    simp only [Pi.neg_apply, hf a b, neg_add]

theorem isClosed_Dual : IsClosed ((Dual G : AddSubgroup (G → UnitAddCircle)) : Set (G → UnitAddCircle)) := by
  have e : ((Dual G : AddSubgroup (G → UnitAddCircle)) : Set (G → UnitAddCircle))
      = ⋂ a : G, ⋂ b : G, {f | f (a + b) = f a + f b} := by
    ext f
    simp only [mem_iInter]
    exact Iff.rfl
  rw [e]
  exact isClosed_iInter (fun a => isClosed_iInter (fun b =>
    isClosed_eq (continuous_apply _) ((continuous_apply a).add (continuous_apply b))))

instance : CompactSpace (Dual G) := isCompact_iff_compactSpace.1 isClosed_Dual.isCompact

instance : MeasurableSpace (Dual G) := borel _

instance : BorelSpace (Dual G) := ⟨rfl⟩

/-- The character as a homomorphism. -/
def toHom (χ : Dual G) : G →+ UnitAddCircle := AddMonoidHom.mk' χ.1 χ.2

/-- The normalized Haar measure. -/
noncomputable def μ (G : Type) [AddCommGroup G] : Measure (Dual G) := Measure.addHaarMeasure ⊤

instance : (μ G).IsAddHaarMeasure := by
  unfold μ
  infer_instance

instance : IsProbabilityMeasure (μ G) := ⟨by
  have h := Measure.addHaarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Dual G)))
  exact h⟩

/-- Evaluation at `a`, as a complex function. -/
noncomputable def ev (a : G) (χ : Dual G) : ℂ := (AddCircle.toCircle (χ.1 a) : ℂ)

theorem continuous_ev (a : G) : Continuous (ev a) :=
  continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp
    ((continuous_apply a).comp continuous_subtype_val))

theorem norm_ev (a : G) (χ : Dual G) : ‖ev a χ‖ = 1 := Circle.norm_coe _

theorem ev_add (a b : G) (χ : Dual G) : ev (a + b) χ = ev a χ * ev b χ := by
  unfold ev
  rw [χ.2 a b, AddCircle.toCircle_add, Circle.coe_mul]

theorem ev_zero (χ : Dual G) : ev (0 : G) χ = 1 := by
  have h : χ.1 0 = 0 := map_zero (toHom χ)
  unfold ev
  rw [h, AddCircle.toCircle_zero, Circle.coe_one]

theorem conj_ev (a : G) (χ : Dual G) : conj (ev a χ) = ev (-a) χ := by
  have h1 : ev a χ * ev (-a) χ = 1 := by rw [← ev_add, add_neg_cancel, ev_zero]
  have h2 : ev a χ * conj (ev a χ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_ev]
    norm_num
  have h3 : ev a χ ≠ 0 := fun h => by
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ h3 (h2.trans h1.symm)

theorem ev_arg_add (a : G) (χ ψ : Dual G) : ev a (χ + ψ) = ev a χ * ev a ψ := by
  unfold ev
  have h : (χ + ψ).1 a = χ.1 a + ψ.1 a := rfl
  rw [h, AddCircle.toCircle_add, Circle.coe_mul]

theorem integrable_ev (a : G) : Integrable (ev a) (μ G) :=
  (continuous_ev a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_ev (a : G) (ha : a ≠ 0) : ∫ χ, ev a χ ∂(μ G) = 0 := by
  have h1 : iota a ≠ 0 := fun h => ha (iota_injective (h.trans (map_zero iota).symm))
  obtain ⟨f, hf⟩ := Function.ne_iff.1 h1
  have hf' : f a ≠ 0 := hf
  set χ0 : Dual G := ⟨f, fun x y => map_add f x y⟩ with hχ0
  have h2 : ev a χ0 ≠ 1 := by
    intro h
    apply hf'
    have h3 : AddCircle.toCircle (f a) = 1 := by
      exact Circle.ext h
    have h4 : AddCircle.toCircle (f a) = AddCircle.toCircle (0 : UnitAddCircle) := by
      rw [h3, AddCircle.toCircle_zero]
    exact AddCircle.injective_toCircle one_ne_zero h4
  have h5 := integral_add_left_eq_self (μ := μ G) (ev a) χ0
  simp only [ev_arg_add] at h5
  rw [integral_const_mul] at h5
  have h6 : (ev a χ0 - 1) * ∫ χ, ev a χ ∂(μ G) = 0 := by rw [sub_mul, one_mul, h5, sub_self]
  exact (mul_eq_zero.1 h6).resolve_left (sub_ne_zero.2 h2)

/-! ### Bessel's inequality -/

noncomputable def evC (a : G) : C(Dual G, ℂ) := ⟨ev a, continuous_ev a⟩

noncomputable def evL (a : G) : Lp ℂ 2 (μ G) := ContinuousMap.toLp 2 (μ G) ℂ (evC a)

theorem orthonormal_evL : Orthonormal ℂ (evL (G := G)) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  unfold evL
  rw [ContinuousMap.inner_toLp]
  have e : ∀ χ : Dual G, evC b χ * conj (evC a χ) = ev (b + -a) χ := by
    intro χ
    show ev b χ * conj (ev a χ) = ev (b + -a) χ
    rw [conj_ev, ev_add]
  simp only [e]
  by_cases h : a = b
  · rw [if_pos h, h, add_neg_cancel]
    simp only [ev_zero]
    simp
  · rw [if_neg h]
    refine integral_ev _ (fun h' => h ?_)
    exact (add_neg_eq_zero.1 h').symm

theorem sum_sq_coeff_le (E : Set (Dual G)) (hE : MeasurableSet E) (s : Finset G) :
    ∑ a ∈ s, ‖∫ χ in E, ev a χ ∂(μ G)‖ ^ 2 ≤ (μ G).real E := by
  set x : Lp ℂ 2 (μ G) := indicatorConstLp 2 hE (measure_ne_top (μ G) E) (1 : ℂ) with hx
  have h1 := Orthonormal.sum_inner_products_le (𝕜 := ℂ) x (s := s) (orthonormal_evL (G := G))
  have h2 : ∀ a : G, ‖inner ℂ (evL a) x‖ = ‖∫ χ in E, ev a χ ∂(μ G)‖ := by
    intro a
    rw [norm_inner_symm, hx, MeasureTheory.L2.inner_indicatorConstLp_one]
    congr 1
    refine setIntegral_congr_ae hE ?_
    have h3 : (evL a : Dual G → ℂ) =ᵐ[μ G] ev a := ContinuousMap.coeFn_toLp (μ G) (evC a)
    filter_upwards [h3] with χ hχ _ using hχ
  have h4 : ‖x‖ ^ 2 = (μ G).real E := by
    rw [hx, norm_indicatorConstLp (by norm_num) (by norm_num)]
    rw [norm_one, one_mul, ← Real.rpow_natCast, ← Real.rpow_mul measureReal_nonneg]
    norm_num
  simp only [h2] at h1
  rwa [h4] at h1

theorem finite_large_coeff (E : Set (Dual G)) (hE : MeasurableSet E) (ε : ℝ) (hε : 0 < ε) :
    {a : G | ε ≤ ‖∫ χ in E, ev a χ ∂(μ G)‖}.Finite := by
  by_contra h
  have hinf : {a : G | ε ≤ ‖∫ χ in E, ev a χ ∂(μ G)‖}.Infinite := h
  obtain ⟨N, hN⟩ := exists_nat_gt ((μ G).real E / ε ^ 2)
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq N
  have h1 := sum_sq_coeff_le E hE s
  have h2 : (s.card : ℝ) * ε ^ 2 ≤ ∑ a ∈ s, ‖∫ χ in E, ev a χ ∂(μ G)‖ ^ 2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun a ha => pow_le_pow_left₀ hε.le (hs ha) 2)
  rw [hcard] at h2
  have h3 : (μ G).real E < N * ε ^ 2 := (div_lt_iff₀ (by positivity)).1 hN
  linarith

/-! ### Both signs occur -/

theorem sq_re_ev (a : G) (χ : Dual G) : (ev a χ).re ^ 2 = (1 + (ev (a + a) χ).re) / 2 := by
  rw [ev_add]
  have h : (ev a χ).re * (ev a χ).re + (ev a χ).im * (ev a χ).im = 1 := by
    have h1 : Complex.normSq (ev a χ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_ev]
      norm_num
    rwa [Complex.normSq_apply] at h1
  rw [Complex.mul_re]
  linear_combination (1 / 2 : ℝ) * h

theorem abs_re_ev (a : G) (χ : Dual G) : -1 ≤ (ev a χ).re ∧ (ev a χ).re ≤ 1 := by
  have h := Complex.abs_re_le_norm (ev a χ)
  rw [norm_ev] at h
  exact abs_le.1 h

variable (H : AddSubgroup G)

theorem both_sides (n : ℕ) (hfib : ∀ y : G, {x : G | x ∈ H ∧ n • x = y}.Finite)
    (h2 : (∀ y : G, {x : G | x ∈ H ∧ (2 * n) • x = y}.Finite) ∨ (∀ x ∈ H, (2 * n) • x = 0))
    (A : Set G) (hA : A ⊆ H) (E : Set (Dual G)) (hE : MeasurableSet E) (hpos : 0 < (μ G) E) :
    {a ∈ A | ¬ (0 < (μ G) (E ∩ {χ | 1 / 8 < (ev (n • a) χ).re}) ∧
      0 < (μ G) (E ∩ {χ | (ev (n • a) χ).re < -(1 / 8)}))}.Finite := by
  set m : ℝ := (μ G).real E with hm
  have hmpos : 0 < m := by
    rw [hm, measureReal_def]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hfin : ∀ k : ℕ, (∀ y : G, {x : G | x ∈ H ∧ k • x = y}.Finite) →
      {a ∈ A | m / 8 ≤ ‖∫ χ in E, ev (k • a) χ ∂(μ G)‖}.Finite := by
    intro k hk
    have h1 := finite_large_coeff E hE (m / 8) (by positivity)
    have h3 : {a ∈ A | m / 8 ≤ ‖∫ χ in E, ev (k • a) χ ∂(μ G)‖}
        ⊆ ⋃ y ∈ {y : G | m / 8 ≤ ‖∫ χ in E, ev y χ ∂(μ G)‖}, {x : G | x ∈ H ∧ k • x = y} := by
      intro a ha
      exact mem_iUnion₂.2 ⟨k • a, ha.2, hA ha.1, rfl⟩
    exact (h1.biUnion (fun y _ => hk y)).subset h3
  have hbad2 : ∃ T : Set G, T.Finite ∧ ∀ a ∈ A, a ∉ T →
      m / 2 - m / 16 ≤ ∫ χ in E, (ev (n • a) χ).re ^ 2 ∂(μ G) := by
    have hrew : ∀ a : G, ∫ χ in E, (ev (n • a) χ).re ^ 2 ∂(μ G)
        = m / 2 + (∫ χ in E, ev ((2 * n) • a) χ ∂(μ G)).re / 2 := by
      intro a
      have e1 : ∀ χ : Dual G, (ev (n • a) χ).re ^ 2 = 1 / 2 + (ev ((2 * n) • a) χ).re / 2 := by
        intro χ
        rw [sq_re_ev, ← add_nsmul, ← two_mul]
        ring
      simp only [e1]
      have hi : IntegrableOn (fun χ => (ev ((2 * n) • a) χ).re) E (μ G) :=
        (integrable_ev _).re.integrableOn
      rw [integral_add (integrable_const _).integrableOn (hi.div_const 2), setIntegral_const,
        integral_div]
      have e2 : ∫ χ in E, (ev ((2 * n) • a) χ).re ∂(μ G) = (∫ χ in E, ev ((2 * n) • a) χ ∂(μ G)).re :=
        integral_re (integrable_ev _).integrableOn
      rw [e2, smul_eq_mul, ← hm]
      ring
    rcases h2 with h2 | h2
    · refine ⟨_, hfin (2 * n) h2, fun a ha hnot => ?_⟩
      have h3 : ‖∫ χ in E, ev ((2 * n) • a) χ ∂(μ G)‖ < m / 8 := not_le.1 (fun h => hnot ⟨ha, h⟩)
      have h4 := (abs_le.1 (Complex.abs_re_le_norm (∫ χ in E, ev ((2 * n) • a) χ ∂(μ G)))).1
      rw [hrew]
      linarith
    · refine ⟨∅, finite_empty, fun a ha _ => ?_⟩
      rw [hrew, h2 a (hA ha)]
      simp only [ev_zero]
      rw [setIntegral_const, ← hm]
      simp
      linarith
  obtain ⟨T, hT, hT2⟩ := hbad2
  refine ((hfin n hfib).union hT).subset (fun a ha => ?_)
  by_contra hnot
  rw [mem_union, not_or] at hnot
  have h1 : ‖∫ χ in E, ev (n • a) χ ∂(μ G)‖ < m / 8 := not_le.1 (fun h => hnot.1 ⟨ha.1, h⟩)
  have h2' := hT2 a ha.1 hnot.2
  set f : Dual G → ℝ := fun χ => (ev (n • a) χ).re with hf
  have hfc : Continuous f := Complex.continuous_re.comp (continuous_ev _)
  have hfi : IntegrableOn f E (μ G) := (integrable_ev _).re.integrableOn
  have hf2i : IntegrableOn (fun χ => f χ ^ 2) E (μ G) :=
    ((hfc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integrableOn
  have hif : |∫ χ in E, f χ ∂(μ G)| < m / 8 := by
    have e2 : ∫ χ in E, f χ ∂(μ G) = (∫ χ in E, ev (n • a) χ ∂(μ G)).re :=
      integral_re (integrable_ev _).integrableOn
    rw [e2]
    exact lt_of_le_of_lt (Complex.abs_re_le_norm _) h1
  have hif' := abs_lt.1 hif
  apply ha.2
  constructor
  · rw [pos_iff_ne_zero]
    intro h0
    have hae : ∀ᵐ χ ∂(μ G).restrict E, f χ ^ 2 ≤ 1 / 8 + (-(7 / 8)) * f χ := by
      rw [ae_restrict_iff' hE, ae_iff]
      refine measure_mono_null (fun χ hχ => ?_) h0
      simp only [mem_setOf_eq, Classical.not_imp, not_le] at hχ
      refine ⟨hχ.1, ?_⟩
      show 1 / 8 < f χ
      by_contra h
      have h' : f χ ≤ 1 / 8 := not_lt.1 h
      have h5 := (abs_re_ev (n • a) χ).1
      have h6 : -1 ≤ f χ := h5
      nlinarith [hχ.2]
    have h7 := integral_mono_ae hf2i ((integrable_const _).integrableOn.add (hfi.const_mul _)) hae
    simp only [Pi.add_apply] at h7
    rw [integral_add (integrable_const _).integrableOn (hfi.const_mul _), setIntegral_const,
      integral_const_mul, smul_eq_mul, ← hm] at h7
    linarith [hif'.1, hif'.2]
  · rw [pos_iff_ne_zero]
    intro h0
    have hae : ∀ᵐ χ ∂(μ G).restrict E, f χ ^ 2 ≤ 1 / 8 + (7 / 8) * f χ := by
      rw [ae_restrict_iff' hE, ae_iff]
      refine measure_mono_null (fun χ hχ => ?_) h0
      simp only [mem_setOf_eq, Classical.not_imp, not_le] at hχ
      refine ⟨hχ.1, ?_⟩
      show f χ < -(1 / 8)
      by_contra h
      have h' : -(1 / 8) ≤ f χ := not_lt.1 h
      have h5 := (abs_re_ev (n • a) χ).2
      have h6 : f χ ≤ 1 := h5
      nlinarith [hχ.2]
    have h7 := integral_mono_ae hf2i ((integrable_const _).integrableOn.add (hfi.const_mul _)) hae
    simp only [Pi.add_apply] at h7
    rw [integral_add (integrable_const _).integrableOn (hfi.const_mul _), setIntegral_const,
      integral_const_mul, smul_eq_mul, ← hm] at h7
    linarith [hif'.1, hif'.2]

/-! ### Interpolation sequences -/

/-- The characters with the real part of `χ (n a)` on the side given by `s`, strictly. -/
def Up (n : ℕ) (a : G) (s : Bool) : Set (Dual G) :=
  {χ | if s then 1 / 8 < (ev (n • a) χ).re else (ev (n • a) χ).re < -(1 / 8)}

/-- The same, not strictly. -/
def Cl (n : ℕ) (a : G) (s : Bool) : Set (Dual G) :=
  {χ | if s then 1 / 8 ≤ (ev (n • a) χ).re else (ev (n • a) χ).re ≤ -(1 / 8)}

theorem isOpen_Up (n : ℕ) (a : G) (s : Bool) : IsOpen (Up n a s) := by
  have h : Continuous (fun χ : Dual G => (ev (n • a) χ).re) := Complex.continuous_re.comp (continuous_ev _)
  cases s
  · exact isOpen_lt h continuous_const
  · exact isOpen_lt continuous_const h

theorem isClosed_Cl (n : ℕ) (a : G) (s : Bool) : IsClosed (Cl n a s) := by
  have h : Continuous (fun χ : Dual G => (ev (n • a) χ).re) := Complex.continuous_re.comp (continuous_ev _)
  cases s
  · exact isClosed_le h continuous_const
  · exact isClosed_le continuous_const h

theorem Up_subset_Cl (n : ℕ) (a : G) (s : Bool) : Up n a s ⊆ Cl n a s := by
  intro χ hχ
  cases s
  · exact le_of_lt (show (ev (n • a) χ).re < -(1 / 8) from hχ)
  · exact le_of_lt (show 1 / 8 < (ev (n • a) χ).re from hχ)

def Pat (b : ℕ → G) (n j : ℕ) (σ : ℕ → Bool) : Set (Dual G) := ⋂ i ∈ Finset.Ico n j, Up n (b i) (σ i)

theorem Pat_congr (b b' : ℕ → G) (n j : ℕ) (σ σ' : ℕ → Bool) (hb : ∀ i < j, b i = b' i)
    (hσ : ∀ i < j, σ i = σ' i) : Pat b n j σ = Pat b' n j σ' := by
  unfold Pat
  refine iInter₂_congr (fun i hi => ?_)
  rw [Finset.mem_Ico] at hi
  rw [hb i hi.2, hσ i hi.2]

variable (M : Set ℕ)

def Good (b : ℕ → G) (j : ℕ) : Prop := ∀ n ∈ M, n ≤ j → ∀ σ : ℕ → Bool, 0 < (μ G) (Pat b n j σ)

theorem step (hfib : ∀ n ∈ M, ∀ y : G, {x : G | x ∈ H ∧ n • x = y}.Finite)
    (h2 : ∀ n ∈ M, (∀ y : G, {x : G | x ∈ H ∧ (2 * n) • x = y}.Finite) ∨ (∀ x ∈ H, (2 * n) • x = 0))
    (A : Set G) (hA : A ⊆ H) (hAinf : A.Infinite) (b : ℕ → G) (j : ℕ) (hb : Good M b j) :
    ∃ a ∈ A, (∀ i < j, b i ≠ a) ∧ Good M (Function.update b j a) (j + 1) := by
  classical
  let σ' : (Fin j → Bool) → ℕ → Bool := fun τ i => if h : i < j then τ ⟨i, h⟩ else false
  let Bad : ℕ → (Fin j → Bool) → Set G := fun n τ =>
    {a ∈ A | n ∈ M ∧ n ≤ j ∧ ¬ (0 < (μ G) (Pat b n j (σ' τ) ∩ {χ | 1 / 8 < (ev (n • a) χ).re}) ∧
      0 < (μ G) (Pat b n j (σ' τ) ∩ {χ | (ev (n • a) χ).re < -(1 / 8)}))}
  have hBad : ∀ n τ, (Bad n τ).Finite := by
    intro n τ
    by_cases hn : n ∈ M ∧ n ≤ j
    · have hmeas : MeasurableSet (Pat b n j (σ' τ)) :=
        (Finset.measurableSet_biInter _ (fun i _ => (isOpen_Up _ _ _).measurableSet))
      refine (both_sides H n (hfib n hn.1) (h2 n hn.1) A hA _ hmeas (hb n hn.1 hn.2 _)).subset ?_
      exact fun a ha => ⟨ha.1, ha.2.2.2⟩
    · refine Set.finite_empty.subset (fun a ha => ?_)
      exact absurd ⟨ha.2.1, ha.2.2.1⟩ hn
  have hall : (⋃ n ∈ Finset.range (j + 1), ⋃ τ : Fin j → Bool, Bad n τ).Finite :=
    (Finset.range (j + 1)).finite_toSet.biUnion (fun n _ => finite_iUnion (fun τ => hBad n τ))
  have himg : (b '' Set.Iio j).Finite := (finite_Iio j).image b
  obtain ⟨a, haA, hnot⟩ := (hAinf.diff (hall.union himg)).nonempty
  rw [mem_union, not_or] at hnot
  refine ⟨a, haA, fun i hi h => hnot.2 ⟨i, hi, h⟩, fun n hn hnj σ => ?_⟩
  rcases Nat.lt_or_ge j n with h | h
  · have e : Pat (Function.update b j a) n (j + 1) σ = univ := by
      have e0 : Finset.Ico n (j + 1) = ∅ := Finset.Ico_eq_empty (by omega)
      unfold Pat
      rw [e0]
      simp
    rw [e, measure_univ]
    exact one_pos
  · set τ : Fin j → Bool := fun i => σ i with hτ
    have hgood : ¬ (a ∈ Bad n τ) := fun h' => hnot.1
      (mem_iUnion₂.2 ⟨n, Finset.mem_range.2 (by omega), mem_iUnion.2 ⟨τ, h'⟩⟩)
    have hboth : 0 < (μ G) (Pat b n j (σ' τ) ∩ {χ | 1 / 8 < (ev (n • a) χ).re}) ∧
        0 < (μ G) (Pat b n j (σ' τ) ∩ {χ | (ev (n • a) χ).re < -(1 / 8)}) := by
      by_contra hc
      exact hgood ⟨haA, hn, h, hc⟩
    have e1 : Pat (Function.update b j a) n (j + 1) σ = Pat b n j (σ' τ) ∩ Up n a (σ j) := by
      have e2 : Finset.Ico n (j + 1) = insert j (Finset.Ico n j) := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_Ico]
        omega
      have e3 : Pat (Function.update b j a) n j σ = Pat b n j (σ' τ) := by
        refine Pat_congr _ _ _ _ _ _ (fun i hi => ?_) (fun i hi => ?_)
        · rw [Function.update_of_ne (by omega : i ≠ j)]
        · show σ i = if h : i < j then τ ⟨i, h⟩ else false
          rw [dif_pos hi]
      rw [← e3]
      unfold Pat
      rw [e2, Finset.set_biInter_insert, Function.update_self, inter_comm]
    rw [e1]
    cases hs : σ j
    · exact hboth.2
    · exact hboth.1

theorem interpolation (hpos : ∀ n ∈ M, 0 < n) (hfib : ∀ n ∈ M, ∀ y : G, {x : G | x ∈ H ∧ n • x = y}.Finite)
    (h2 : ∀ n ∈ M, (∀ y : G, {x : G | x ∈ H ∧ (2 * n) • x = y}.Finite) ∨ (∀ x ∈ H, (2 * n) • x = 0))
    (A : Set G) (hA : A ⊆ H) (hAinf : A.Infinite) :
    ∃ b : ℕ → G, Function.Injective b ∧ (∀ i, b i ∈ A) ∧
      ∀ n ∈ M, ∀ s : ℕ → Bool, ∃ χ : Dual G, ∀ j, n ≤ j → χ ∈ Cl n (b j) (s j) := by
  classical
  let St : ℕ → Type := fun j => {b : ℕ → G // Good M b j ∧ (∀ i < j, b i ∈ A) ∧
    ∀ i < j, ∀ k < j, b i = b k → i = k}
  have h0 : Good M (fun _ : ℕ => (0 : G)) 0 := by
    intro n hn hn0 σ
    exact absurd hn0 (not_le.2 (hpos n hn))
  have hnext : ∀ j (s : St j), ∃ t : St (j + 1), ∀ i < j, t.1 i = s.1 i := by
    intro j s
    obtain ⟨a, ha, hne, hg⟩ := step H M hfib h2 A hA hAinf s.1 j s.2.1
    have hupd : ∀ i < j, Function.update s.1 j a i = s.1 i := fun i hi =>
      Function.update_of_ne (by omega : i ≠ j) _ _
    have hmem : ∀ i < j + 1, Function.update s.1 j a i ∈ A := by
      intro i hi
      by_cases h : i = j
      · rw [h, Function.update_self]
        exact ha
      · rw [hupd i (by omega)]
        exact s.2.2.1 i (by omega)
    have hinj : ∀ i < j + 1, ∀ k < j + 1, Function.update s.1 j a i = Function.update s.1 j a k → i = k := by
      intro i hi k hk h
      by_cases h1 : i = j
      · by_cases h3 : k = j
        · rw [h1, h3]
        · rw [h1, Function.update_self, hupd k (by omega)] at h
          exact absurd h.symm (hne k (by omega))
      · by_cases h3 : k = j
        · rw [h3, Function.update_self, hupd i (by omega)] at h
          exact absurd h (hne i (by omega))
        · rw [hupd i (by omega), hupd k (by omega)] at h
          exact s.2.2.2 i (by omega) k (by omega) h
    exact ⟨⟨Function.update s.1 j a, hg, hmem, hinj⟩, hupd⟩
  choose next hnext' using hnext
  let state : (j : ℕ) → St j := fun j =>
    Nat.rec (motive := St) ⟨fun _ => 0, h0, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩ (fun k s => next k s) j
  have hstate : ∀ j, state (j + 1) = next j (state j) := fun _ => rfl
  have hagree : ∀ j k, j ≤ k → ∀ i < j, (state k).1 i = (state j).1 i := by
    intro j k hjk
    induction hjk with
    | refl => exact fun _ _ => rfl
    | step h ih =>
      intro i hi
      rw [hstate, hnext' _ _ i (lt_of_lt_of_le hi h)]
      exact ih i hi
  set b : ℕ → G := fun i => (state (i + 1)).1 i with hb
  have hbj : ∀ j, ∀ i < j, b i = (state j).1 i := fun j i hi =>
    (hagree (i + 1) j hi i (Nat.lt_succ_self i)).symm
  have hGood : ∀ j, Good M b j := by
    intro j n hn hnj σ
    rw [Pat_congr b (state j).1 n j σ σ (hbj j) (fun _ _ => rfl)]
    exact (state j).2.1 n hn hnj σ
  refine ⟨b, fun i k h => ?_, fun i => ?_, fun n hn s => ?_⟩
  · have h1 := hbj (max i k + 1) i (by omega)
    have h3 := hbj (max i k + 1) k (by omega)
    exact (state (max i k + 1)).2.2.2 i (by omega) k (by omega) (h1.symm.trans (h.trans h3))
  · exact (state (i + 1)).2.2.1 i (Nat.lt_succ_self i)
  · set C : ℕ → Set (Dual G) := fun J => ⋂ i ∈ Finset.Ico n J, Cl n (b i) (s i) with hC
    have hclosed : ∀ J, IsClosed (C J) := fun J => isClosed_biInter (fun i _ => isClosed_Cl _ _ _)
    have hanti : ∀ J, C (J + 1) ⊆ C J := by
      intro J x hx
      simp only [hC, mem_iInter] at hx ⊢
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact hx i (Finset.mem_Ico.2 ⟨hi.1, by omega⟩)
    have hne : ∀ J, (C J).Nonempty := by
      intro J
      by_cases h : n ≤ J
      · have h1 := hGood J n hn h s
        obtain ⟨χ, hχ⟩ := nonempty_of_measure_ne_zero h1.ne'
        refine ⟨χ, ?_⟩
        simp only [Pat, mem_iInter] at hχ
        simp only [hC, mem_iInter]
        exact fun i hi => Up_subset_Cl _ _ _ (hχ i hi)
      · have e : Finset.Ico n J = ∅ := Finset.Ico_eq_empty (by omega)
        refine ⟨0, ?_⟩
        simp only [hC, e]
        simp
    obtain ⟨χ, hχ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hanti hne
      (hclosed 0).isCompact hclosed
    refine ⟨χ, fun j hj => ?_⟩
    have h1 := mem_iInter.1 hχ (j + 1)
    simp only [hC, mem_iInter] at h1
    exact h1 j (Finset.mem_Ico.2 ⟨hj, Nat.lt_succ_self j⟩)

/-! ### Many ultrafilters with different limits -/

theorem lam_apply (b : ℕ → G) (v : Ultrafilter ℕ) (n : ℕ) (χ : Dual G) :
    Tendsto (fun j => ev (n • b j) χ) (v : Filter ℕ)
      (𝓝 ((AddCircle.toCircle ((n • lam (v.map b)) (toHom χ)) : Circle) : ℂ)) := by
  have h1 : Tendsto iota (Filter.map b (v : Filter ℕ)) (𝓝 (lam (v.map b))) := by
    have h := lim_lam (v.map b)
    unfold Lim at h
    rwa [Ultrafilter.coe_map] at h
  have h2 : Tendsto (fun j => (iota (b j)) (toHom χ)) (v : Filter ℕ) (𝓝 (lam (v.map b) (toHom χ))) := by
    have h3 := (continuous_apply (toHom χ)).continuousAt.tendsto.comp (tendsto_map'_iff.1 h1)
    exact h3
  have h4 : Tendsto (fun j => n • (iota (b j)) (toHom χ)) (v : Filter ℕ)
      (𝓝 (n • lam (v.map b) (toHom χ))) := h2.const_smul n
  have h5 := (continuous_subtype_val.comp AddCircle.continuous_toCircle).continuousAt.tendsto.comp h4
  have e : ∀ j, ev (n • b j) χ = ((AddCircle.toCircle (n • (iota (b j)) (toHom χ)) : Circle) : ℂ) := by
    intro j
    have h6 : χ.1 (n • b j) = n • χ.1 (b j) := map_nsmul (toHom χ) n (b j)
    unfold ev
    rw [h6]
    rfl
  simp only [e]
  exact h5

theorem nsmul_lam_injective (b : ℕ → G) (n : ℕ)
    (hint : ∀ s : ℕ → Bool, ∃ χ : Dual G, ∀ j, n ≤ j → χ ∈ Cl n (b j) (s j))
    (v w : Ultrafilter ℕ) (hv : (v : Filter ℕ) ≤ cofinite) (hw : (w : Filter ℕ) ≤ cofinite)
    (h : n • lam (v.map b) = n • lam (w.map b)) : v = w := by
  classical
  by_contra hne
  obtain ⟨S, hSv, hSw⟩ : ∃ S : Set ℕ, S ∈ v ∧ Sᶜ ∈ w := by
    by_contra hc
    apply hne
    refine (Ultrafilter.coe_le_coe.1 (fun S hS => ?_)).symm
    show S ∈ w
    by_contra hSw
    exact hc ⟨S, hS, Ultrafilter.compl_mem_iff_notMem.2 hSw⟩
  obtain ⟨χ, hχ⟩ := hint (fun j => decide (j ∈ S))
  have hev : ∀ z : Ultrafilter ℕ, (z : Filter ℕ) ≤ cofinite → ∀ᶠ j in (z : Filter ℕ), n ≤ j := by
    intro z hz
    refine hz ?_
    rw [Nat.cofinite_eq_atTop]
    exact eventually_ge_atTop n
  have hx : 1 / 8 ≤ (((AddCircle.toCircle ((n • lam (v.map b)) (toHom χ)) : Circle) : ℂ)).re := by
    have ht := (Complex.continuous_re.continuousAt).tendsto.comp (lam_apply b v n χ)
    refine ge_of_tendsto ht ?_
    filter_upwards [show S ∈ (v : Filter ℕ) from hSv, hev v hv] with j hj hj2
    have h1 := hχ j hj2
    simp only [Cl, decide_eq_true hj, if_true, mem_setOf_eq] at h1
    exact h1
  have hy : (((AddCircle.toCircle ((n • lam (w.map b)) (toHom χ)) : Circle) : ℂ)).re ≤ -(1 / 8) := by
    have ht := (Complex.continuous_re.continuousAt).tendsto.comp (lam_apply b w n χ)
    refine le_of_tendsto ht ?_
    filter_upwards [show Sᶜ ∈ (w : Filter ℕ) from hSw, hev w hw] with j hj hj2
    have h1 := hχ j hj2
    have hj' : j ∉ S := hj
    simp only [Cl, decide_eq_false hj', Bool.false_eq_true, if_false, mem_setOf_eq] at h1
    exact h1
  rw [h] at hx
  linarith

theorem aleph0_lt_two_pow_c : ℵ₀ < (2 : Cardinal.{0}) ^ 𝔠 :=
  Cardinal.aleph0_lt_continuum.trans (Cardinal.cantor _)

/-- There are `2 ^ 𝔠` nonprincipal ultrafilters on `ℕ`. -/
theorem le_mk_free : (2 : Cardinal.{0}) ^ 𝔠 ≤ #{v : Ultrafilter ℕ // (v : Filter ℕ) ≤ cofinite} := by
  classical
  have hall : #(Ultrafilter ℕ) = (2 : Cardinal.{0}) ^ 𝔠 := by
    rw [Cardinal.mk_ultrafilter_of_infinite, Cardinal.mk_nat, Cardinal.two_power_aleph0]
  by_contra hc
  rw [not_le] at hc
  have hsub : (univ : Set (Ultrafilter ℕ)) ⊆ {v : Ultrafilter ℕ | (v : Filter ℕ) ≤ cofinite} ∪ range pure := by
    intro v _
    by_cases h : (v : Filter ℕ) ≤ cofinite
    · exact Or.inl h
    · refine Or.inr ?_
      rcases v.le_cofinite_or_eq_pure with h1 | ⟨a, ha⟩
      · exact absurd h1 h
      · exact ⟨a, ha.symm⟩
  have h1 : #(Ultrafilter ℕ) < (2 : Cardinal.{0}) ^ 𝔠 := by
    rw [← Cardinal.mk_univ]
    refine lt_of_le_of_lt ((Cardinal.mk_le_mk_of_subset hsub).trans (Cardinal.mk_union_le _ _)) ?_
    refine Cardinal.add_lt_of_lt aleph0_lt_two_pow_c.le hc ?_
    exact lt_of_le_of_lt (Cardinal.mk_range_le.trans Cardinal.mk_nat.le) aleph0_lt_two_pow_c
  rw [hall] at h1
  exact lt_irrefl _ h1

/-! ### The closure of a subgroup in the Bohr compactification -/

/-- Only the points of `B` lie in the closure of `B` in the Bohr compactification. -/
theorem mem_of_iota_mem_closure (B : AddSubgroup G) (g : G)
    (h : iota g ∈ (B.map (iota (G := G))).topologicalClosure) : g ∈ B := by
  by_contra hg
  have hne : (QuotientAddGroup.mk' B) g ≠ 0 := fun h0 => hg ((QuotientAddGroup.eq_zero_iff g).1 h0)
  have h1 : iota ((QuotientAddGroup.mk' B) g) ≠ 0 := fun h0 => hne (iota_injective (h0.trans (map_zero iota).symm))
  obtain ⟨f, hf⟩ := Function.ne_iff.1 h1
  set χ : G →+ UnitAddCircle := f.comp (QuotientAddGroup.mk' B) with hχ
  have hclosed : IsClosed {x : Circles G | x χ = 0} := isClosed_eq (continuous_apply χ) continuous_const
  have hsub : ((B.map (iota (G := G))) : Set (Circles G)) ⊆ {x : Circles G | x χ = 0} := by
    rintro _ ⟨c, hc, rfl⟩
    show f ((QuotientAddGroup.mk' B) c) = 0
    have h2 : (QuotientAddGroup.mk' B) c = 0 := (QuotientAddGroup.eq_zero_iff c).2 hc
    rw [h2, map_zero]
  have h3 : iota g ∈ {x : Circles G | x χ = 0} := by
    have h4 : (iota g) ∈ closure ((B.map (iota (G := G))) : Set (Circles G)) := by
      rw [← AddSubgroup.topologicalClosure_coe]
      exact h
    exact closure_minimal hsub hclosed h4
  exact hf h3

theorem lam_mem_closure (B : AddSubgroup G) (b : ℕ → G) (hb : ∀ j, b j ∈ B) (v : Ultrafilter ℕ) (n : ℕ) :
    n • lam (v.map b) ∈ (B.map (iota (G := G))).topologicalClosure := by
  refine AddSubgroup.nsmul_mem _ ?_ n
  have h1 : Tendsto iota (Filter.map b (v : Filter ℕ)) (𝓝 (lam (v.map b))) := by
    have h := lim_lam (v.map b)
    unfold Lim at h
    rwa [Ultrafilter.coe_map] at h
  have h2 : lam (v.map b) ∈ closure ((B.map (iota (G := G))) : Set (Circles G)) := by
    refine mem_closure_of_tendsto (tendsto_map'_iff.1 h1) (Filter.univ_mem' (fun j => ?_))
    exact ⟨b j, hb j, rfl⟩
  rw [← AddSubgroup.topologicalClosure_coe] at h2
  exact h2

/-- A translate of `H` meets the closure of a countable subgroup of `H` in a countable set. -/
theorem countable_translate_inter (H B : AddSubgroup G) (hBH : B ≤ H) (hB : (B : Set G).Countable)
    (k : Circles G) :
    {x : Circles G | x ∈ (B.map (iota (G := G))).topologicalClosure ∧ ∃ h ∈ H, x = iota h + k}.Countable := by
  set T : Set (Circles G) :=
    {x : Circles G | x ∈ (B.map (iota (G := G))).topologicalClosure ∧ ∃ h ∈ H, x = iota h + k} with hT
  rcases Set.eq_empty_or_nonempty T with h0 | ⟨x0, hx0⟩
  · rw [h0]
    exact countable_empty
  · refine (hB.image (fun c => x0 + iota c)).mono (fun x hx => ?_)
    obtain ⟨h0, hh0, e0⟩ := hx0.2
    obtain ⟨h1, hh1, e1⟩ := hx.2
    have e : x - x0 = iota (h1 - h0) := by
      rw [e0, e1, map_sub]
      abel
    have h2 : iota (h1 - h0) ∈ (B.map (iota (G := G))).topologicalClosure := by
      rw [← e]
      exact AddSubgroup.sub_mem _ hx.1 hx0.1
    refine ⟨h1 - h0, mem_of_iota_mem_closure B _ h2, ?_⟩
    show x0 + iota (h1 - h0) = x
    rw [← e]
    abel

/-! ### The theorem -/

theorem mk_closure_le {P : Type} [AddCommGroup P] (T : Set P) :
    #(AddSubgroup.closure T) ≤ max ℵ₀ #T := by
  set g : T ⊕ T → P := Sum.elim (fun t : T => (t : P)) (fun t : T => -(t : P)) with hg
  have hswap : ∀ a : T ⊕ T, g a.swap = -g a := by
    rintro (a | a) <;> simp [hg, Sum.swap]
  have h : ((AddSubgroup.closure T : AddSubgroup P) : Set P)
      ⊆ range (fun l : List (T ⊕ T) => (l.map g).sum) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx => exact ⟨[Sum.inl ⟨x, hx⟩], by simp [hg]⟩
    | zero => exact ⟨[], rfl⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨l1, h1⟩ := ihx
      obtain ⟨l2, h2⟩ := ihy
      refine ⟨l1 ++ l2, ?_⟩
      show ((l1 ++ l2).map g).sum = x + y
      rw [List.map_append, List.sum_append]
      exact congrArg₂ (· + ·) h1 h2
    | neg x _ ih =>
      obtain ⟨l, hl⟩ := ih
      refine ⟨l.map Sum.swap, ?_⟩
      have e : ∀ l : List (T ⊕ T), ((l.map Sum.swap).map g).sum = -(l.map g).sum := by
        intro l
        induction l with
        | nil => simp
        | cons a l ih =>
          rw [List.map_cons, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, hswap, neg_add]
      show ((l.map Sum.swap).map g).sum = -x
      rw [e]
      exact congrArg Neg.neg hl
  refine (Cardinal.mk_le_mk_of_subset h).trans (Cardinal.mk_range_le.trans ?_)
  refine (Cardinal.mk_list_le_max _).trans (max_le (le_max_left _ _) ?_)
  rw [Cardinal.mk_sum, Cardinal.lift_id]
  exact Cardinal.add_le_of_le (le_max_left _ _) (le_max_right _ _) (le_max_right _ _)

/-- The condition (E) gives the set of multipliers used in the construction. -/
theorem exists_exponents [Infinite H]
    (hE : ∀ m : ℕ, 1 ≤ m → {x : G | x ∈ H ∧ m • x = 0}.Finite ∨ ∀ x ∈ H, m • x = 0) :
    ∃ M : Set ℕ, (∀ n ∈ M, 0 < n) ∧ (∀ n ∈ M, ∀ y : G, {x : G | x ∈ H ∧ n • x = y}.Finite) ∧
      (∀ n ∈ M, (∀ y : G, {x : G | x ∈ H ∧ (2 * n) • x = y}.Finite) ∨ (∀ x ∈ H, (2 * n) • x = 0)) ∧
      (∀ m : ℤ, (∀ x ∈ H, m • x = 0) ∨ ∃ n ∈ M, (∀ x ∈ H, m • x = n • x) ∨ (∀ x ∈ H, m • x = -(n • x))) := by
  classical
  have hfibre : ∀ k : ℕ, {x : G | x ∈ H ∧ k • x = 0}.Finite → ∀ y : G, {x : G | x ∈ H ∧ k • x = y}.Finite := by
    intro k hk y
    rcases Set.eq_empty_or_nonempty {x : G | x ∈ H ∧ k • x = y} with h | ⟨x0, hx0⟩
    · rw [h]
      exact finite_empty
    · refine (hk.image (fun z => z + x0)).subset (fun x hx => ⟨x - x0, ⟨H.sub_mem hx.1 hx0.1, ?_⟩, ?_⟩)
      · rw [nsmul_sub, hx.2, hx0.2, sub_self]
      · exact sub_add_cancel x x0
  have hHinf : (H : Set G).Infinite := Set.infinite_coe_iff.1 (inferInstanceAs (Infinite H))
  by_cases hall : ∀ m : ℕ, 1 ≤ m → {x : G | x ∈ H ∧ m • x = 0}.Finite
  · refine ⟨{n | 1 ≤ n}, fun n hn => hn, fun n hn => hfibre n (hall n hn), fun n hn => Or.inl ?_, fun m => ?_⟩
    · exact hfibre _ (hall _ (le_trans hn (by omega)))
    · rcases eq_or_ne m 0 with h | h
      · exact Or.inl (fun x _ => by rw [h, zero_zsmul])
      · refine Or.inr ⟨m.natAbs, show 1 ≤ m.natAbs by omega, ?_⟩
        rcases Int.natAbs_eq m with h1 | h1
        · exact Or.inl (fun x _ => by conv_lhs => rw [h1]
                                      rw [natCast_zsmul])
        · exact Or.inr (fun x _ => by conv_lhs => rw [h1]
                                      rw [neg_zsmul, natCast_zsmul])
  · have hex : ∃ m : ℕ, 1 ≤ m ∧ ∀ x ∈ H, m • x = 0 := by
      by_contra h
      refine hall (fun m hm => ?_)
      rcases hE m hm with h1 | h1
      · exact h1
      · exact absurd ⟨m, hm, h1⟩ h
    set p := Nat.find hex with hp
    have hp1 : 1 ≤ p := (Nat.find_spec hex).1
    have hp0 : ∀ x ∈ H, p • x = 0 := (Nat.find_spec hex).2
    have hmod : ∀ k : ℕ, ∀ x ∈ H, k • x = (k % p) • x := by
      intro k x hx
      conv_lhs => rw [← Nat.div_add_mod k p]
      rw [add_nsmul, mul_nsmul, hp0 x hx, nsmul_zero, zero_add]
    have hsmall : ∀ n, 0 < n → n < p → {x : G | x ∈ H ∧ n • x = 0}.Finite := by
      intro n hn hnp
      rcases hE n hn with h | h
      · exact h
      · exact absurd ⟨hn, h⟩ (Nat.find_min hex hnp)
    have hdvd : ∀ k : ℕ, (∀ x ∈ H, k • x = 0) → p ∣ k := by
      intro k hk
      refine Nat.dvd_of_mod_eq_zero (by_contra (fun h => ?_))
      have h1 : k % p < p := Nat.mod_lt _ hp1
      exact Nat.find_min hex h1 ⟨Nat.pos_of_ne_zero h, fun x hx => (hmod k x hx).symm.trans (hk x hx)⟩
    have hp2 : 2 ≤ p := by
      by_contra h
      have h1 : p = 1 := by omega
      have h2 : (H : Set G) ⊆ {0} := fun x hx => by
        have h3 := hp0 x hx
        rw [h1, one_nsmul] at h3
        exact h3
      exact hHinf ((finite_singleton 0).subset h2)
    have hprime : p.Prime := by
      refine Nat.prime_def_lt.2 ⟨hp2, fun a ha hdiv => ?_⟩
      by_contra ha1
      obtain ⟨c, hc⟩ := hdiv
      have ha0 : 0 < a := by
        refine Nat.pos_of_ne_zero (fun h => ?_)
        rw [h, zero_mul] at hc
        omega
      have hc0 : 0 < c := by
        refine Nat.pos_of_ne_zero (fun h => ?_)
        rw [h, mul_zero] at hc
        omega
      have hcp : c < p := by
        have h1 : 1 < a := by omega
        calc c < a * c := lt_mul_of_one_lt_left hc0 h1
          _ = p := hc.symm
      have hfa := hsmall a ha0 ha
      have hfc := hsmall c hc0 hcp
      have hsub : (H : Set G) ⊆ ⋃ y ∈ {x : G | x ∈ H ∧ a • x = 0}, {x : G | x ∈ H ∧ c • x = y} := by
        intro x hx
        refine mem_iUnion₂.2 ⟨c • x, ⟨H.nsmul_mem hx _, ?_⟩, hx, rfl⟩
        rw [← mul_nsmul, mul_comm, ← hc]
        exact hp0 x hx
      exact hHinf ((hfa.biUnion (fun y _ => hfibre c hfc y)).subset hsub)
    refine ⟨{n | 0 < n ∧ n < p}, fun n hn => hn.1, fun n hn => hfibre n (hsmall n hn.1 hn.2),
      fun n hn => ?_, fun m => ?_⟩
    · by_cases h : p = 2
      · refine Or.inr (fun x hx => ?_)
        have h1 : n = 1 := by
          have h2 := hn.2
          have h3 := hn.1
          omega
        rw [h1, mul_one, ← h]
        exact hp0 x hx
      · refine Or.inl (hfibre _ ?_)
        rcases hE (2 * n) (by have := hn.1; omega) with h1 | h1
        · exact h1
        · exfalso
          rcases (Nat.Prime.dvd_mul hprime).1 (hdvd _ h1) with h2 | h2
          · have h3 := Nat.le_of_dvd two_pos h2
            omega
          · have h3 := Nat.le_of_dvd hn.1 h2
            have h4 := hn.2
            omega
    · have hpz : (0 : ℤ) < p := by exact_mod_cast hp1
      have hr0 : 0 ≤ m % (p : ℤ) := Int.emod_nonneg _ hpz.ne'
      have hrp : m % (p : ℤ) < p := Int.emod_lt_of_pos _ hpz
      have hred : ∀ x ∈ H, m • x = ((m % (p : ℤ)).toNat) • x := by
        intro x hx
        conv_lhs => rw [← Int.mul_ediv_add_emod m p]
        rw [add_zsmul, mul_comm, mul_zsmul, natCast_zsmul, hp0 x hx, zsmul_zero, zero_add]
        conv_lhs => rw [← Int.toNat_of_nonneg hr0]
        rw [natCast_zsmul]
      rcases Nat.eq_zero_or_pos (m % (p : ℤ)).toNat with h | h
      · exact Or.inl (fun x hx => by rw [hred x hx, h, zero_nsmul])
      · refine Or.inr ⟨_, ⟨h, ?_⟩, Or.inl hred⟩
        omega

/-- Without set-theoretic hypotheses: the vicinity filter, for subgroups of cardinality at most `2 ^ 𝔠`. -/
theorem vicinity_without_hypotheses [Infinite H] (hcard : #H ≤ (2 : Cardinal.{0}) ^ 𝔠)
    (hE : ∀ m : ℕ, 1 ≤ m → {x : G | x ∈ H ∧ m • x = 0}.Finite ∨ ∀ x ∈ H, m • x = 0) :
    ∃ S : Set (Ultrafilter G), (∀ g : G, (pure g : Filter G) ∈ genFam (ultraGen S) → g = 0) ∧
      ∀ s : Set G, s ∈ vic (genFam (ultraGen S)) ↔ (0 : G) ∈ s ∧ ((H : Set G) \ s).Finite := by
  classical
  obtain ⟨M, hpos, hfib, h2, hred⟩ := exists_exponents H hE
  set κ : Cardinal.{0} := (2 : Cardinal.{0}) ^ 𝔠 with hκ
  have hκ0 : ℵ₀ < κ := aleph0_lt_two_pow_c
  set I : Type := {A : Set G // A ⊆ H ∧ A.Infinite ∧ A.Countable} with hI
  have hIc : #I ≤ κ := by
    have h1 : #I ≤ #{t : Set H // #t ≤ ℵ₀} := by
      have hcount : ∀ A : I, #(Subtype.val ⁻¹' A.1 : Set H) ≤ ℵ₀ := fun A =>
        Cardinal.le_aleph0_iff_set_countable.2 (A.2.2.2.preimage Subtype.val_injective)
      refine Cardinal.mk_le_of_injective
        (f := fun A : I => (⟨(Subtype.val ⁻¹' A.1 : Set H), hcount A⟩ : {t : Set H // #t ≤ ℵ₀}))
        (fun A B h => ?_)
      have h' : (Subtype.val ⁻¹' A.1 : Set H) = Subtype.val ⁻¹' B.1 := Subtype.ext_iff.1 h
      refine Subtype.ext (Set.ext (fun x => ?_))
      constructor
      · intro hx
        exact (Set.ext_iff.1 h' ⟨x, A.2.1 hx⟩).1 hx
      · intro hx
        exact (Set.ext_iff.1 h' ⟨x, B.2.1 hx⟩).2 hx
    refine h1.trans ((Cardinal.mk_bounded_set_le H ℵ₀).trans ?_)
    have h3 : max #H ℵ₀ ≤ κ := max_le hcard hκ0.le
    refine (Cardinal.power_le_power_right h3).trans (le_of_eq ?_)
    rw [hκ, ← Cardinal.power_mul, Cardinal.continuum_mul_aleph0]
  have hb : ∀ A : I, ∃ b : ℕ → G, Function.Injective b ∧ (∀ i, b i ∈ A.1) ∧
      ∀ n ∈ M, ∀ s : ℕ → Bool, ∃ χ : Dual G, ∀ j, n ≤ j → χ ∈ Cl n (b j) (s j) :=
    fun A => interpolation H M hpos hfib h2 A.1 A.2.1 A.2.2.1
  choose b hbinj hbmem hbint using hb
  obtain ⟨r, wo, hr⟩ := Cardinal.exists_ord_eq I
  haveI := wo
  have hseg : ∀ i : I, #{j : I // r j i} < κ := by
    intro i
    have h1 : (Ordinal.typein r i).card < #I := Cardinal.card_typein_lt i hr
    exact lt_of_lt_of_le (lt_of_eq_of_lt (Ordinal.card_typein (r := r) i).symm h1) hIc
  have hchoose : ∀ (i : I) (prev : ∀ j : I, r j i → Circles G),
      ∃ v : {v : Ultrafilter ℕ // (v : Filter ℕ) ≤ cofinite},
        ∀ n ∈ M, n • lam (v.1.map (b i)) ∉
          AddSubgroup.closure ((iota (G := G)) '' (H : Set G) ∪ range (fun j : {j : I // r j i} => prev j.1 j.2)) := by
    intro i prev
    set P : Set (Circles G) := range (fun j : {j : I // r j i} => prev j.1 j.2) with hP
    set Kp : AddSubgroup (Circles G) := AddSubgroup.closure P with hKp
    have hKc : #Kp < κ :=
      lt_of_le_of_lt (mk_closure_le P) (max_lt hκ0 (lt_of_le_of_lt Cardinal.mk_range_le (hseg i)))
    set B : AddSubgroup G := AddSubgroup.closure (range (b i)) with hB
    have hBH : B ≤ H := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨j, rfl⟩
      exact i.2.1 (hbmem i j)
    have hBc : (B : Set G).Countable := countable_closure _ (countable_range _)
    have hbB : ∀ j, b i j ∈ B := fun j => AddSubgroup.subset_closure ⟨j, rfl⟩
    set Tk : Kp → Set (Circles G) := fun k =>
      {x : Circles G | x ∈ (B.map (iota (G := G))).topologicalClosure ∧ ∃ h ∈ H, x = iota h + (k : Circles G)}
      with hTk
    have hTkc : ∀ k, #(Tk k) ≤ ℵ₀ := fun k =>
      Cardinal.le_aleph0_iff_set_countable.2 (countable_translate_inter H B hBH hBc k)
    by_contra hno
    have h1 : ∀ v : {v : Ultrafilter ℕ // (v : Filter ℕ) ≤ cofinite},
        ∃ n : M, ∃ k : Kp, (n : ℕ) • lam (v.1.map (b i)) ∈ Tk k := by
      intro v
      have h3 : ∃ n ∈ M, n • lam (v.1.map (b i)) ∈
          AddSubgroup.closure ((iota (G := G)) '' (H : Set G) ∪ P) := by
        by_contra h
        exact hno ⟨v, fun n hn hmem => h ⟨n, hn, hmem⟩⟩
      obtain ⟨n, hn, hmem⟩ := h3
      have h4 : AddSubgroup.closure ((iota (G := G)) '' (H : Set G) ∪ P) = H.map (iota (G := G)) ⊔ Kp := by
        rw [AddSubgroup.closure_union, ← AddSubgroup.coe_map, AddSubgroup.closure_eq]
      rw [h4] at hmem
      obtain ⟨y, hy, k, hk, e⟩ := AddSubgroup.mem_sup.1 hmem
      obtain ⟨h, hh, rfl⟩ := hy
      exact ⟨⟨n, hn⟩, ⟨k, hk⟩, lam_mem_closure B (b i) hbB v.1 n, h, hh, e.symm⟩
    choose nv kv hv using h1
    have hinj : Function.Injective (fun v : {v : Ultrafilter ℕ // (v : Filter ℕ) ≤ cofinite} =>
        ((nv v, ⟨kv v, ⟨(nv v : ℕ) • lam (v.1.map (b i)), hv v⟩⟩) : M × Σ k : Kp, Tk k)) := by
      intro v w h
      obtain ⟨hn, hs⟩ := Prod.ext_iff.1 h
      have hn' : (nv v : ℕ) = nv w := congrArg Subtype.val hn
      have hval : (nv v : ℕ) • lam (v.1.map (b i)) = (nv w : ℕ) • lam (w.1.map (b i)) :=
        congrArg (fun z : Σ k : Kp, Tk k => (z.2 : Circles G)) hs
      rw [← hn'] at hval
      exact Subtype.ext (nsmul_lam_injective (b i) _ (hbint i _ (nv v).2) v.1 w.1 v.2 w.2 hval)
    have h5 : #(M × Σ k : Kp, Tk k) < κ := by
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_sigma]
      refine Cardinal.mul_lt_of_lt hκ0.le (lt_of_le_of_lt (Cardinal.mk_le_aleph0 (α := M)) hκ0) ?_
      refine lt_of_le_of_lt (Cardinal.sum_le_mk_mul_iSup _) ?_
      refine Cardinal.mul_lt_of_lt hκ0.le hKc (lt_of_le_of_lt (ciSup_le' hTkc) hκ0)
    exact absurd (lt_of_le_of_lt (le_mk_free.trans (Cardinal.mk_le_of_injective hinj)) h5) (lt_irrefl _)
  choose pick hpick using hchoose
  have wf : WellFounded r := wo.wf
  let lims : I → Circles G := wf.fix (fun i prev => lam ((pick i prev).1.map (b i)))
  have hlims : ∀ i, lims i = lam ((pick i (fun j _ => lims j)).1.map (b i)) := fun i => wf.fix_eq _ i
  set u : I → Ultrafilter G := fun i => (pick i (fun j _ => lims j)).1.map (b i) with hu
  have hlu : ∀ i, lam (u i) = lims i := fun i => (hlims i).symm
  have hind : ∀ i, ∀ n ∈ M, n • lam (u i) ∉
      AddSubgroup.closure ((iota (G := G)) '' (H : Set G) ∪ range (fun j : {j : I // r j i} => lam (u j.1))) := by
    intro i n hn
    have e : (fun j : {j : I // r j i} => lam (u j.1)) = (fun j : {j : I // r j i} => lims j.1) := by
      funext j
      exact hlu j.1
    rw [e]
    exact hpick i (fun j _ => lims j) n hn
  have huH : ∀ i, (H : Set G) ∈ u i := by
    intro i
    show b i ⁻¹' (H : Set G) ∈ (pick i (fun j _ => lims j)).1
    exact Filter.univ_mem' (fun k => i.2.1 (hbmem i k))
  have huA : ∀ i : I, i.1 ∈ u i := by
    intro i
    show b i ⁻¹' i.1 ∈ (pick i (fun j _ => lims j)).1
    exact Filter.univ_mem' (fun k => hbmem i k)
  have hufree : ∀ i a, u i ≠ pure a := by
    intro i a h
    have h1 : ({a} : Set G) ∈ u i := by
      rw [h]
      exact rfl
    have h3 : b i ⁻¹' {a} ∈ (pick i (fun j _ => lims j)).1 := h1
    have h4 : (b i ⁻¹' {a}).Finite := (finite_singleton a).preimage (hbinj i).injOn
    have h5 : (b i ⁻¹' {a})ᶜ ∈ (pick i (fun j _ => lims j)).1 :=
      (pick i (fun j _ => lims j)).2 h4.compl_mem_cofinite
    exact Ultrafilter.compl_mem_iff_notMem.1 h5 h3
  have hsmul : ∀ (i : I) (m k : ℤ), (∀ x ∈ H, m • x = k • x) → m • lam (u i) = k • lam (u i) := by
    intro i m k h
    have h1 := lim_lam (u i)
    unfold Lim at h1
    have h3 : Tendsto (fun a => m • iota a) (u i : Filter G) (𝓝 (m • lam (u i))) := h1.const_smul m
    have h4 : Tendsto (fun a => k • iota a) (u i : Filter G) (𝓝 (k • lam (u i))) := h1.const_smul k
    refine tendsto_nhds_unique (h3.congr' ?_) h4
    filter_upwards [show (H : Set G) ∈ (u i : Filter G) from huH i] with a ha
    rw [← map_zsmul, ← map_zsmul, h a ha]
  have hmax : ∀ s : Finset I, s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, x ≠ a → r x a := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a =>
      exact ⟨a, Finset.mem_singleton_self a, fun x hx hne => absurd (Finset.mem_singleton.1 hx) hne⟩
    | cons a s ha hs ih =>
      obtain ⟨m, hm, h⟩ := ih
      rcases trichotomous_of r a m with h1 | h1 | h1
      · refine ⟨m, Finset.mem_cons_of_mem hm, fun x hx hne => ?_⟩
        rcases Finset.mem_cons.1 hx with rfl | hx
        · exact h1
        · exact h x hx hne
      · exact absurd (h1 ▸ hm) ha
      · refine ⟨a, Finset.mem_cons_self a s, fun x hx hne => ?_⟩
        rcases Finset.mem_cons.1 hx with rfl | hx
        · exact absurd rfl hne
        · by_cases hxm : x = m
          · rw [hxm]
            exact h1
          · exact _root_.trans (r := r) (h x hx hxm) h1
  have hindep : ∀ (s : Finset I) (c : I → ℤ), ∀ g ∈ H, ∑ i ∈ s, c i • lam (u i) = iota g → g = 0 := by
    intro s c
    induction s using Finset.strongInduction with
    | H s ih =>
      intro g hg h
      rcases s.eq_empty_or_nonempty with hs0 | hsne
      · rw [hs0, Finset.sum_empty] at h
        exact iota_injective (h.symm.trans (map_zero iota).symm)
      obtain ⟨a, has, ha⟩ := hmax s hsne
      rw [← Finset.insert_erase has, Finset.sum_insert (Finset.notMem_erase a s)] at h
      set W : AddSubgroup (Circles G) :=
        AddSubgroup.closure ((iota (G := G)) '' (H : Set G) ∪ range (fun j : {j : I // r j a} => lam (u j.1)))
        with hW
      have hrest : ∑ i ∈ s.erase a, c i • lam (u i) ∈ W := by
        refine AddSubgroup.sum_mem _ (fun i hi => AddSubgroup.zsmul_mem _ ?_ _)
        have hi' := Finset.mem_erase.1 hi
        exact AddSubgroup.subset_closure (Or.inr ⟨⟨i, ha i hi'.2 hi'.1⟩, rfl⟩)
      have hg' : iota g ∈ W := AddSubgroup.subset_closure (Or.inl ⟨g, hg, rfl⟩)
      have hdiff : c a • lam (u a) ∈ W := by
        have e : c a • lam (u a) = iota g - ∑ i ∈ s.erase a, c i • lam (u i) := eq_sub_of_add_eq h
        rw [e]
        exact W.sub_mem hg' hrest
      rcases hred (c a) with h0 | ⟨n, hn, h0 | h0⟩
      · have e : c a • lam (u a) = 0 := by
          have h1 := hsmul a (c a) 0 (fun x hx => by rw [h0 x hx, zero_zsmul])
          rwa [zero_zsmul] at h1
        rw [e, zero_add] at h
        exact ih _ (Finset.erase_ssubset has) g hg h
      · have h1 := hsmul a (c a) n (fun x hx => by rw [h0 x hx, natCast_zsmul])
        rw [natCast_zsmul] at h1
        exact absurd (h1 ▸ hdiff) (hind a n hn)
      · have h1 := hsmul a (c a) (-(n : ℤ)) (fun x hx => by rw [h0 x hx, neg_zsmul, natCast_zsmul])
        rw [neg_zsmul, natCast_zsmul] at h1
        refine absurd ?_ (hind a n hn)
        rw [h1] at hdiff
        simpa using W.neg_mem hdiff
  set S : Set (Ultrafilter G) := range u with hS
  have hnullH : ∀ σ : Filter G, SumClosure (ultraGen S) σ → (H : Set G) ∈ σ := by
    intro σ hσ
    have hgen : ∀ F : Filter G, F ∈ ultraGen S → (H : Set G) ∈ F := by
      rintro F ⟨v, ⟨i, rfl⟩, rfl⟩
      exact huH i
    induction hσ with
    | zero => exact Filter.mem_pure.2 H.zero_mem
    | gen hF => exact hgen _ hF
    | neg hF =>
      refine Filter.mem_map.2 (Filter.mem_of_superset (hgen _ hF) (fun x hx => ?_))
      exact H.neg_mem hx
    | add _ _ ih1 ih2 =>
      refine Filter.mem_of_superset (Filter.image2_mem_map₂ ih1 ih2) ?_
      rintro _ ⟨x, hx, y, hy, rfl⟩
      exact H.add_mem hx hy
  have hhaus : ∀ g : G, (pure g : Filter G) ∈ genFam (ultraGen S) → g = 0 := by
    intro g hg
    have hgH : g ∈ H := by
      have h1 : ((pure g : Ultrafilter G) : Filter G) ≤ (pure g : Filter G) := by
        rw [Ultrafilter.coe_pure]
      obtain ⟨σ, hσ, h3⟩ := hg.2 (pure g) h1
      have h4 : (H : Set G) ∈ (pure g : Ultrafilter G) := h3 (hnullH σ hσ)
      exact h4
    have h5 : iota g ∈ K (ultraGen S) := iota_mem_K _ g hg
    have h6 : K (ultraGen S) ≤ (Submodule.span ℤ (range (fun i => lam (u i)))).toAddSubgroup := by
      refine (AddSubgroup.closure_le _).2 (fun y hy => ?_)
      obtain ⟨v, ⟨i, rfl⟩, rfl⟩ := L_ultraGen _ hy
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 (h6 h5)
    exact hindep c.support c g hgH hc
  refine ⟨S, hhaus, fun s => ?_⟩
  refine mem_vic_iff_of_dense S H ?_ ?_ ?_ hhaus s
  · rintro v ⟨i, rfl⟩ a
    exact hufree i a
  · rintro v ⟨i, rfl⟩
    exact huH i
  · intro A hA hAinf
    set e := hAinf.natEmbedding with he
    set A' : Set G := range (fun n => ((e n : A) : G)) with hA'
    have hinj : Function.Injective (fun n => ((e n : A) : G)) := fun a c h => e.injective (Subtype.ext h)
    have hsub : A' ⊆ A := by
      rintro _ ⟨n, rfl⟩
      exact (e n).2
    have hA'I : A' ⊆ H ∧ A'.Infinite ∧ A'.Countable :=
      ⟨hsub.trans hA, infinite_range_of_injective hinj, countable_range _⟩
    refine ⟨u ⟨A', hA'I⟩, ⟨_, rfl⟩, ?_⟩
    exact Filter.mem_of_superset (f := (u ⟨A', hA'I⟩ : Filter G)) (huA ⟨A', hA'I⟩) hsub

/-! ### The cardinality is necessary -/

/-- If the filter is a vicinity filter, then `H` has at most `2 ^ 𝔠` elements. -/
theorem card_le_of_vicinity {C : Set (Filter G)} (hC : NullFamily C)
    (hV : ∀ s : Set G, s ∈ vic C ↔ (0 : G) ∈ s ∧ ((H : Set G) \ s).Finite) :
    #H ≤ (2 : Cardinal.{0}) ^ 𝔠 := by
  classical
  have hκ0 : ℵ₀ < (2 : Cardinal.{0}) ^ 𝔠 := aleph0_lt_two_pow_c
  rcases finite_or_infinite H with hfin | hinf
  · exact (Cardinal.lt_aleph0_of_finite H).le.trans hκ0.le
  have hhaus : ∀ g : G, (pure g : Filter G) ∈ C → g = 0 := by
    intro g hg
    by_contra hne
    have hs : ({g}ᶜ : Set G) ∈ vic C := by
      refine (hV _).2 ⟨fun h => hne (mem_singleton_iff.1 h).symm, (finite_singleton g).subset (fun x hx => ?_)⟩
      exact not_not.1 hx.2
    exact (mem_vic.1 hs _ hg) rfl
  have hnull : ∀ X : Set G, X ⊆ H → X.Infinite → ∃ U : Ultrafilter G, X ∈ U ∧ (U : Filter G) ∈ C := by
    intro X hXH hX
    have hX' : (X \ {0}).Infinite := hX.diff (finite_singleton 0)
    have hs : ((X \ {0})ᶜ : Set G) ∉ vic C := by
      intro h
      have h1 := ((hV _).1 h).2
      exact hX' (h1.subset (fun x hx => ⟨hXH hx.1, fun hc => hc hx⟩))
    rw [mem_vic] at hs
    push Not at hs
    obtain ⟨F, hF, hsF⟩ := hs
    have : F.NeBot := hC.ne F hF
    obtain ⟨U, hUF, hUX⟩ := exists_ultra_compl_mem F hsF
    rw [compl_compl] at hUX
    exact ⟨U, Filter.mem_of_superset (f := (U : Filter G)) hUX (fun x hx => hx.1),
      hC.finer F hF _ hUF U.neBot⟩
  set f0 := Infinite.natEmbedding H with hf0
  set B : AddSubgroup H := AddSubgroup.closure (range f0) with hB
  have hBc : (B : Set H).Countable := countable_closure _ (countable_range _)
  have hBi : (B : Set H).Infinite :=
    (infinite_range_of_injective f0.injective).mono AddSubgroup.subset_closure
  set BG : Set G := Subtype.val '' (B : Set H) with hBG
  have hBGc : BG.Countable := hBc.image _
  have hBGi : BG.Infinite := hBi.image Subtype.val_injective.injOn
  set rep : H ⧸ B → G := fun c => ((c.out : H) : G) with hrep
  have hpick : ∀ c : H ⧸ B, ∃ U : Ultrafilter G, (fun x => rep c + x) '' BG ∈ U ∧ (U : Filter G) ∈ C := by
    intro c
    refine hnull _ ?_ (hBGi.image (fun a _ d _ h => add_left_cancel h))
    rintro _ ⟨_, ⟨y, _, rfl⟩, rfl⟩
    exact H.add_mem (c.out).2 y.2
  choose U hUm hUC using hpick
  set v : H ⧸ B → Ultrafilter G := fun c => (U c).map (fun x => x - rep c) with hv
  have hvB : ∀ c, BG ∈ v c := by
    intro c
    show (fun x => x - rep c) ⁻¹' BG ∈ U c
    refine Filter.mem_of_superset (f := (U c : Filter G)) (hUm c) ?_
    rintro _ ⟨y, hy, rfl⟩
    show rep c + y - rep c ∈ BG
    rwa [add_sub_cancel_left]
  have hinj : Function.Injective v := by
    intro c d h
    have hle : (pure (rep c - rep d) : Filter G)
        ≤ Filter.map₂ (· + ·) (U c : Filter G) (Filter.map (fun x : G => -x) (U d : Filter G)) := by
      intro s hs
      obtain ⟨t1, ht1, t2, ht2, h12⟩ := Filter.mem_map₂_iff.1 hs
      have h1 : (fun y => rep c + y) ⁻¹' t1 ∈ v c := by
        show (fun x => x - rep c) ⁻¹' ((fun y => rep c + y) ⁻¹' t1) ∈ U c
        refine Filter.mem_of_superset (f := (U c : Filter G)) ht1 (fun x hx => ?_)
        show rep c + (x - rep c) ∈ t1
        rwa [add_sub_cancel]
      have h3 : (fun y => rep d + y) ⁻¹' ((fun x : G => -x) ⁻¹' t2) ∈ v d := by
        show (fun x => x - rep d) ⁻¹' ((fun y => rep d + y) ⁻¹' ((fun x : G => -x) ⁻¹' t2)) ∈ U d
        refine Filter.mem_of_superset (f := (U d : Filter G)) (Filter.mem_map.1 ht2) (fun x hx => ?_)
        show rep d + (x - rep d) ∈ (fun x : G => -x) ⁻¹' t2
        rwa [add_sub_cancel]
      rw [← h] at h3
      obtain ⟨y, hy1, hy2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (v c : Filter G)) h1 h3)
      have e : (rep c + y) + -(rep d + y) = rep c - rep d := by abel
      refine Filter.mem_pure.2 ?_
      rw [← e]
      exact h12 (mem_image2_of_mem hy1 hy2)
    have hsum := hC.add _ (hUC c) _ (hC.neg _ (hUC d))
    have h0 := hhaus _ (hC.finer _ hsum _ hle inferInstance)
    have h4 : (c.out : H) = d.out := Subtype.ext (sub_eq_zero.1 h0)
    rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' d, h4]
  have : Infinite BG := hBGi.to_subtype
  have : Countable BG := hBGc.to_subtype
  have hq : #(H ⧸ B) ≤ (2 : Cardinal.{0}) ^ 𝔠 := by
    have hcm : ∀ c, range (Subtype.val : BG → G) ∈ v c := fun c => by
      rw [Subtype.range_coe]
      exact hvB c
    set w : H ⧸ B → Ultrafilter BG := fun c => (v c).comap Subtype.val_injective (hcm c) with hw
    have hwinj : Function.Injective w := by
      intro c d h
      refine hinj (Ultrafilter.coe_injective ?_)
      have e : ∀ c, Filter.map (Subtype.val : BG → G) (w c : Filter BG) = (v c : Filter G) := by
        intro c
        rw [hw, Ultrafilter.coe_comap]
        exact Filter.map_comap_of_mem (hcm c)
      rw [← e c, ← e d, h]
    refine (Cardinal.mk_le_of_injective hwinj).trans (le_of_eq ?_)
    rw [Cardinal.mk_ultrafilter_of_infinite, Cardinal.mk_eq_aleph0 BG, Cardinal.two_power_aleph0]
  have hBle : #B ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.2 hBc
  rw [Cardinal.mk_congr (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := B)), Cardinal.mk_prod,
    Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.mul_le_of_le hκ0.le hq (hBle.trans hκ0.le)

/-- The exact condition, without set-theoretic hypotheses. -/
theorem vicinity_iff [Infinite H] :
    (∃ C : Set (Filter G), NullFamily C ∧ ∀ s : Set G, s ∈ vic C ↔ (0 : G) ∈ s ∧ ((H : Set G) \ s).Finite) ↔
      #H ≤ (2 : Cardinal.{0}) ^ 𝔠 ∧
        ∀ m : ℕ, 1 ≤ m → {x : G | x ∈ H ∧ m • x = 0}.Finite ∨ ∀ x ∈ H, m • x = 0 := by
  constructor
  · rintro ⟨C, hC, hV⟩
    exact ⟨card_le_of_vicinity H hC hV, fun m hm => finite_or_zero_of_vicinity hC H hV m hm⟩
  · rintro ⟨hcard, hE⟩
    obtain ⟨S, _, hV⟩ := vicinity_without_hypotheses H hcard hE
    exact ⟨genFam (ultraGen S), genFam_nullFamily _, hV⟩

/-- The cofinite filter at `0` on `ℤ` is the vicinity filter of a PG with unique limits. -/
theorem int_cofinite :
    ∃ C : Set (Filter ℤ), NullFamily C ∧ (∀ g : ℤ, (pure g : Filter ℤ) ∈ C → g = 0) ∧
      ∀ s : Set ℤ, s ∈ vic C ↔ (0 : ℤ) ∈ s ∧ sᶜ.Finite := by
  have : Infinite (⊤ : AddSubgroup ℤ) := Infinite.of_injective (fun n : ℤ => (⟨n, trivial⟩ : (⊤ : AddSubgroup ℤ)))
    (fun a b h => Subtype.ext_iff.1 h)
  have hcard : #(⊤ : AddSubgroup ℤ) ≤ (2 : Cardinal.{0}) ^ 𝔠 :=
    (Cardinal.mk_le_aleph0 (α := (⊤ : AddSubgroup ℤ))).trans aleph0_lt_two_pow_c.le
  obtain ⟨S, hh, hV⟩ := vicinity_without_hypotheses (⊤ : AddSubgroup ℤ) hcard (fun m hm => Or.inl (by
    refine (finite_singleton (0 : ℤ)).subset (fun x hx => ?_)
    have h1 : (m : ℤ) * x = 0 := by
      rw [← nsmul_eq_mul]
      exact hx.2
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast (show m ≠ 0 by omega))))
  refine ⟨genFam (ultraGen S), genFam_nullFamily _, hh, fun s => ?_⟩
  rw [hV]
  have e : ((⊤ : AddSubgroup ℤ) : Set ℤ) \ s = sᶜ := by
    ext x
    simp
  rw [e]

end ZFC

end PG
