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
* `vicinity_without_hypotheses` : if `H` is a countably infinite subgroup of an abelian group `G` satisfying (E),
  there is a set of ultrafilters whose PG has unique limits and whose vicinity filter consists of the sets that
  contain `0` and all but finitely many points of `H`.
* `vicinity_iff` : for a countably infinite subgroup `H`, the filter above is the vicinity filter of some PG exactly
  when (E) holds;
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

/-! ### Continuum many ultrafilters with different limits -/

/-- The codes of the initial segments of `x`. -/
def Br (x : ℕ → Bool) : Set ℕ := range (fun k => Encodable.encode ((List.range k).map x))

theorem Br_infinite (x : ℕ → Bool) : (Br x).Infinite := by
  refine infinite_range_of_injective (fun k l h => ?_)
  have h1 := congrArg List.length (Encodable.encode_injective h)
  simpa using h1

theorem Br_inter_finite (x y : ℕ → Bool) (h : x ≠ y) : (Br x ∩ Br y).Finite := by
  obtain ⟨m, hm⟩ := Function.ne_iff.1 h
  refine ((finite_Iio (m + 1)).image (fun k => Encodable.encode ((List.range k).map x))).subset ?_
  rintro c ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have h1 : (List.range k).map x = (List.range l).map y := Encodable.encode_injective (hk.trans hl.symm)
  have h2 : k = l := by simpa using congrArg List.length h1
  subst h2
  refine ⟨k, ?_, hk⟩
  by_contra hkm
  have h3 : m < k := by
    rw [mem_Iio] at hkm
    omega
  have h4 := congrArg (fun L => L[m]?) h1
  simp [h3] at h4
  exact hm h4

noncomputable def vb (x : ℕ → Bool) : Ultrafilter ℕ :=
  haveI : (cofinite ⊓ 𝓟 (Br x)).NeBot := (Br_infinite x).cofinite_inf_principal_neBot
  Ultrafilter.of (cofinite ⊓ 𝓟 (Br x))

theorem vb_le (x : ℕ → Bool) : (vb x : Filter ℕ) ≤ cofinite ⊓ 𝓟 (Br x) := by
  haveI : (cofinite ⊓ 𝓟 (Br x)).NeBot := (Br_infinite x).cofinite_inf_principal_neBot
  exact Ultrafilter.of_le _

noncomputable def ub (b : ℕ → G) (x : ℕ → Bool) : Ultrafilter G := (vb x).map b

theorem lam_apply (b : ℕ → G) (x : ℕ → Bool) (n : ℕ) (χ : Dual G) :
    Tendsto (fun j => ev (n • b j) χ) (vb x : Filter ℕ)
      (𝓝 ((AddCircle.toCircle ((n • lam (ub b x)) (toHom χ)) : Circle) : ℂ)) := by
  have h1 : Tendsto iota (Filter.map b (vb x : Filter ℕ)) (𝓝 (lam (ub b x))) := by
    have h := lim_lam (ub b x)
    unfold Lim at h
    rwa [ub, Ultrafilter.coe_map] at h
  have h2 : Tendsto (fun j => (iota (b j)) (toHom χ)) (vb x : Filter ℕ) (𝓝 (lam (ub b x) (toHom χ))) := by
    have h3 := (continuous_apply (toHom χ)).continuousAt.tendsto.comp (tendsto_map'_iff.1 h1)
    exact h3
  have h4 : Tendsto (fun j => n • (iota (b j)) (toHom χ)) (vb x : Filter ℕ)
      (𝓝 (n • lam (ub b x) (toHom χ))) := h2.const_smul n
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
    (hint : ∀ s : ℕ → Bool, ∃ χ : Dual G, ∀ j, n ≤ j → χ ∈ Cl n (b j) (s j)) :
    Function.Injective (fun x : ℕ → Bool => n • lam (ub b x)) := by
  classical
  intro x y h
  by_contra hxy
  obtain ⟨χ, hχ⟩ := hint (fun j => decide (j ∈ Br x))
  have hbig : ∀ z : ℕ → Bool, ∀ᶠ j in (vb z : Filter ℕ), j ∈ Br z ∧ n ≤ j := by
    intro z
    have h1 : ∀ᶠ j in (vb z : Filter ℕ), j ∈ Br z :=
      (vb_le z).trans inf_le_right (mem_principal_self _)
    have h2 : ∀ᶠ j in (vb z : Filter ℕ), n ≤ j := by
      refine (vb_le z).trans inf_le_left ?_
      rw [Nat.cofinite_eq_atTop]
      exact eventually_ge_atTop n
    exact h1.and h2
  have hx : 1 / 8 ≤ (((AddCircle.toCircle ((n • lam (ub b x)) (toHom χ)) : Circle) : ℂ)).re := by
    have ht := (Complex.continuous_re.continuousAt).tendsto.comp (lam_apply b x n χ)
    refine ge_of_tendsto ht ?_
    filter_upwards [hbig x] with j hj
    have h1 := hχ j hj.2
    simp only [Cl, decide_eq_true hj.1, if_true, mem_setOf_eq] at h1
    exact h1
  have hy : (((AddCircle.toCircle ((n • lam (ub b y)) (toHom χ)) : Circle) : ℂ)).re ≤ -(1 / 8) := by
    have ht := (Complex.continuous_re.continuousAt).tendsto.comp (lam_apply b y n χ)
    refine le_of_tendsto ht ?_
    have h3 : ∀ᶠ j in (vb y : Filter ℕ), j ∉ Br x := by
      have h4 : (Br x ∩ Br y)ᶜ ∈ (vb y : Filter ℕ) :=
        (vb_le y).trans inf_le_left (Br_inter_finite x y hxy).compl_mem_cofinite
      filter_upwards [h4, hbig y] with j hj hj2
      exact fun h => hj ⟨h, hj2.1⟩
    filter_upwards [h3, hbig y] with j hj hj2
    have h1 := hχ j hj2.2
    simp only [Cl, decide_eq_false hj, Bool.false_eq_true, if_false, mem_setOf_eq] at h1
    exact h1
  have e : n • lam (ub b x) = n • lam (ub b y) := h
  rw [e] at hx
  linarith

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

/-- Without set-theoretic hypotheses: the vicinity filter. -/
theorem vicinity_without_hypotheses [Countable H] [Infinite H]
    (hE : ∀ m : ℕ, 1 ≤ m → {x : G | x ∈ H ∧ m • x = 0}.Finite ∨ ∀ x ∈ H, m • x = 0) :
    ∃ S : Set (Ultrafilter G), (∀ g : G, (pure g : Filter G) ∈ genFam (ultraGen S) → g = 0) ∧
      ∀ s : Set G, s ∈ vic (genFam (ultraGen S)) ↔ (0 : G) ∈ s ∧ ((H : Set G) \ s).Finite := by
  classical
  obtain ⟨M, hpos, hfib, h2, hred⟩ := exists_exponents H hE
  set I : Type := {A : Set G // A ⊆ H ∧ A.Infinite} with hI
  have hIc : #I ≤ 𝔠 := by
    have h1 : #I ≤ #(Set H) := by
      refine Cardinal.mk_le_of_injective (f := fun A : I => (Subtype.val ⁻¹' A.1 : Set H)) (fun A B h => ?_)
      refine Subtype.ext (Set.ext (fun x => ?_))
      constructor
      · intro hx
        exact (Set.ext_iff.1 h ⟨x, A.2.1 hx⟩).1 hx
      · intro hx
        exact (Set.ext_iff.1 h ⟨x, B.2.1 hx⟩).2 hx
    refine h1.trans ?_
    rw [Cardinal.mk_set]
    exact Cardinal.power_le_power_left two_ne_zero (Cardinal.mk_le_aleph0 (α := H))
  have hb : ∀ A : I, ∃ b : ℕ → G, Function.Injective b ∧ (∀ i, b i ∈ A.1) ∧
      ∀ n ∈ M, ∀ s : ℕ → Bool, ∃ χ : Dual G, ∀ j, n ≤ j → χ ∈ Cl n (b j) (s j) :=
    fun A => interpolation H M hpos hfib h2 A.1 A.2.1 A.2.2
  choose b hbinj hbmem hbint using hb
  obtain ⟨r, wo, hr⟩ := Cardinal.exists_ord_eq I
  haveI := wo
  have hseg : ∀ i : I, #{j : I // r j i} < 𝔠 := by
    intro i
    have h1 : (Ordinal.typein r i).card < #I := Cardinal.card_typein_lt i hr
    exact lt_of_lt_of_le (lt_of_eq_of_lt (Ordinal.card_typein (r := r) i).symm h1) hIc
  have hchoose : ∀ (i : I) (prev : ∀ j : I, r j i → Circles G), ∃ x : ℕ → Bool,
      ∀ n ∈ M, n • lam (ub (b i) x) ∉
        AddSubgroup.closure ((iota (G := G)) '' (H : Set G) ∪ range (fun j : {j : I // r j i} => prev j.1 j.2)) := by
    intro i prev
    set T : Set (Circles G) := (iota (G := G)) '' (H : Set G) ∪ range (fun j : {j : I // r j i} => prev j.1 j.2)
      with hT
    have hTc : #T < 𝔠 := by
      refine lt_of_le_of_lt (Cardinal.mk_union_le _ _) (Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum ?_ ?_)
      · refine lt_of_le_of_lt ?_ Cardinal.aleph0_lt_continuum
        exact Cardinal.mk_le_aleph0_iff.2 ((Set.countable_coe_iff.1 (inferInstanceAs (Countable H))).image _).to_subtype
      · exact lt_of_le_of_lt Cardinal.mk_range_le (hseg i)
    have hWc : #(AddSubgroup.closure T) < 𝔠 :=
      lt_of_le_of_lt (mk_closure_le T) (max_lt Cardinal.aleph0_lt_continuum hTc)
    by_contra hno
    have h1 : ∀ x : ℕ → Bool, ∃ n : M, (n : ℕ) • lam (ub (b i) x) ∈ AddSubgroup.closure T := by
      intro x
      by_contra h
      exact hno ⟨x, fun n hn hmem => h ⟨⟨n, hn⟩, hmem⟩⟩
    choose nx hnx using h1
    have hinj : Function.Injective (fun x : ℕ → Bool =>
        ((nx x, ⟨(nx x : ℕ) • lam (ub (b i) x), hnx x⟩) : M × AddSubgroup.closure T)) := by
      intro x y h
      obtain ⟨hn, hv⟩ := Prod.ext_iff.1 h
      have hv' : (nx x : ℕ) • lam (ub (b i) x) = (nx y : ℕ) • lam (ub (b i) y) := Subtype.ext_iff.1 hv
      have hn' : (nx x : ℕ) = nx y := congrArg Subtype.val hn
      rw [← hn'] at hv'
      exact nsmul_lam_injective (b i) _ (hbint i _ (nx x).2) hv'
    have h3 : #(ℕ → Bool) ≤ #(M × AddSubgroup.closure T) := Cardinal.mk_le_of_injective hinj
    have h4 : #(ℕ → Bool) = 𝔠 := by
      rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
    have h5 : #(M × AddSubgroup.closure T) < 𝔠 := by
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
      refine Cardinal.mul_lt_of_lt Cardinal.aleph0_le_continuum ?_ hWc
      exact lt_of_le_of_lt (Cardinal.mk_le_aleph0 (α := M)) Cardinal.aleph0_lt_continuum
    rw [h4] at h3
    exact absurd (lt_of_le_of_lt h3 h5) (lt_irrefl _)
  choose pick hpick using hchoose
  have wf : WellFounded r := wo.wf
  let lims : I → Circles G := wf.fix (fun i prev => lam (ub (b i) (pick i prev)))
  have hlims : ∀ i, lims i = lam (ub (b i) (pick i (fun j _ => lims j))) := fun i => wf.fix_eq _ i
  set u : I → Ultrafilter G := fun i => ub (b i) (pick i (fun j _ => lims j)) with hu
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
    show b i ⁻¹' (H : Set G) ∈ vb _
    exact Filter.univ_mem' (fun k => i.2.1 (hbmem i k))
  have huA : ∀ i : I, i.1 ∈ u i := by
    intro i
    show b i ⁻¹' i.1 ∈ vb _
    exact Filter.univ_mem' (fun k => hbmem i k)
  have hufree : ∀ i a, u i ≠ pure a := by
    intro i a h
    have h1 : ({a} : Set G) ∈ u i := by
      rw [h]
      exact rfl
    have h3 : b i ⁻¹' {a} ∈ vb (pick i (fun j _ => lims j)) := h1
    have h4 : (b i ⁻¹' {a}).Finite := (finite_singleton a).preimage (hbinj i).injOn
    have h5 : (b i ⁻¹' {a})ᶜ ∈ vb (pick i (fun j _ => lims j)) :=
      (vb_le _).trans inf_le_left h4.compl_mem_cofinite
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
    exact ⟨u ⟨A, hA, hAinf⟩, ⟨_, rfl⟩, huA ⟨A, hA, hAinf⟩⟩

/-- The exact condition, without set-theoretic hypotheses. -/
theorem vicinity_iff [Countable H] [Infinite H] :
    (∃ C : Set (Filter G), NullFamily C ∧ ∀ s : Set G, s ∈ vic C ↔ (0 : G) ∈ s ∧ ((H : Set G) \ s).Finite) ↔
      ∀ m : ℕ, 1 ≤ m → {x : G | x ∈ H ∧ m • x = 0}.Finite ∨ ∀ x ∈ H, m • x = 0 := by
  constructor
  · rintro ⟨C, hC, hV⟩ m hm
    exact finite_or_zero_of_vicinity hC H hV m hm
  · intro hE
    obtain ⟨S, _, hV⟩ := vicinity_without_hypotheses H hE
    exact ⟨genFam (ultraGen S), genFam_nullFamily _, hV⟩

/-- The cofinite filter at `0` on `ℤ` is the vicinity filter of a PG with unique limits. -/
theorem int_cofinite :
    ∃ C : Set (Filter ℤ), NullFamily C ∧ (∀ g : ℤ, (pure g : Filter ℤ) ∈ C → g = 0) ∧
      ∀ s : Set ℤ, s ∈ vic C ↔ (0 : ℤ) ∈ s ∧ sᶜ.Finite := by
  have : Infinite (⊤ : AddSubgroup ℤ) := Infinite.of_injective (fun n : ℤ => (⟨n, trivial⟩ : (⊤ : AddSubgroup ℤ)))
    (fun a b h => Subtype.ext_iff.1 h)
  obtain ⟨S, hh, hV⟩ := vicinity_without_hypotheses (⊤ : AddSubgroup ℤ) (fun m hm => Or.inl (by
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
