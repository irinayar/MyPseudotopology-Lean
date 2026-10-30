import LeanCheck.ChainDualityCore

/-!
# Kronecker's theorem for subgroups of a finite torus

Let `T = I → 𝕋` (`I` finite).  If `C ≤ T` is a closed subgroup and `s₀ ∈ T` satisfies every integer relation
`∑ kᵢ tᵢ = 0` that holds on all of `C`, then `s₀ ∈ C` (`kronecker_mem`).  Consequently the closure of the
image of a homomorphism `Ψ : G → T` contains every point obeying the integer relations of `Ψ`
(`kronecker_range`).  The proof averages trigonometric polynomials over the Haar measure of `C`
(Stone–Weierstrass plus orthogonality, as in `char_in_span`).  This is the density tool for the completion
theorems.
-/

namespace LeanCheck

open Filter Topology MeasureTheory

section Kronecker

variable {I : Type} [Fintype I]

/-- The exponential `𝕋 → ℂ`. -/
noncomputable def ecC (s : Circ) : ℂ := ((AddCircle.toCircle s : Circle) : ℂ)

lemma ecC_add (s t : Circ) : ecC (s + t) = ecC s * ecC t := by
  simp [ecC, AddCircle.toCircle_add]

lemma ecC_norm (s : Circ) : ‖ecC s‖ = 1 := by simp [ecC]

lemma ecC_conj (s : Circ) : (starRingEnd ℂ) (ecC s) = ecC (-s) := by
  simp only [ecC, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

lemma ecC_cont : Continuous ecC := continuous_subtype_val.comp AddCircle.continuous_toCircle

lemma ecC_inj : Function.Injective ecC :=
  Subtype.coe_injective.comp (AddCircle.injective_toCircle one_ne_zero)

lemma ecC_zero : ecC 0 = 1 := by simp [ecC]

/-- `t ↦ ∑ kᵢ tᵢ`. -/
def skT (k : I → ℤ) (t : I → Circ) : Circ := ∑ i, k i • t i

lemma skT_cont (k : I → ℤ) : Continuous (skT k) :=
  continuous_finset_sum _ (fun i _ => (continuous_zsmul (k i)).comp (continuous_apply i))

lemma skT_add (k : I → ℤ) (p q : I → Circ) : skT k (p + q) = skT k p + skT k q := by
  simp [skT, smul_add, Finset.sum_add_distrib]

lemma skT_addk (k l : I → ℤ) (p : I → Circ) : skT (k + l) p = skT k p + skT l p := by
  simp [skT, add_smul, Finset.sum_add_distrib]

lemma skT_neg (k : I → ℤ) (p : I → Circ) : skT (-k) p = - skT k p := by
  simp [skT, neg_smul, Finset.sum_neg_distrib]

lemma skT_zero (p : I → Circ) : skT (0 : I → ℤ) p = 0 := by simp [skT]

lemma skT_single [DecidableEq I] (i : I) (p : I → Circ) : skT (Pi.single i 1) p = p i := by
  simp only [skT]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The monomial `t ↦ e(∑ kᵢ tᵢ)`. -/
noncomputable def monoT (k : I → ℤ) : C(I → Circ, ℂ) :=
  ⟨fun t => ecC (skT k t), ecC_cont.comp (skT_cont k)⟩

lemma monoT_apply (k : I → ℤ) (t : I → Circ) : monoT k t = ecC (skT k t) := rfl

/-- The span of the monomials. -/
noncomputable def trigSpan (I : Type) [Fintype I] : Submodule ℂ C(I → Circ, ℂ) :=
  Submodule.span ℂ (Set.range (monoT (I := I)))

/-- **Trigonometric polynomials are dense in `C(𝕋^I, ℂ)`** (Stone–Weierstrass). -/
theorem trig_dense [DecidableEq I] (G : C(I → Circ, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P ∈ trigSpan I, dist P G < ε := by
  have mono_mul : ∀ k l, monoT k * monoT l = monoT (I := I) (k + l) := by
    intro k l; ext p
    simp only [ContinuousMap.mul_apply, monoT_apply, skT_addk, ecC_add]
  have mono_star : ∀ k, star (monoT k) = monoT (I := I) (-k) := by
    intro k; ext p
    simp only [ContinuousMap.star_apply, monoT_apply, skT_neg]
    exact ecC_conj _
  have mono_zero : monoT (0 : I → ℤ) = 1 := by
    ext p; simp [monoT_apply, skT_zero, ecC_zero]
  let S : Submodule ℂ C(I → Circ, ℂ) := trigSpan I
  have S_mul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    intro a ha b hb
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, rfl⟩ := hy
        rw [mono_mul]; exact Submodule.subset_span ⟨_, rfl⟩
      | zero => simp
      | add y y' _ _ ihy ihy' => rw [mul_add]; exact S.add_mem ihy ihy'
      | smul c y _ ihy => rw [mul_smul_comm]; exact S.smul_mem c ihy
    | zero => simp
    | add x x' _ _ ihx ihx' => rw [add_mul]; exact S.add_mem ihx ihx'
    | smul c x _ ihx => rw [smul_mul_assoc]; exact S.smul_mem c ihx
  have S_star : ∀ a ∈ S, star a ∈ S := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [mono_star]; exact Submodule.subset_span ⟨_, rfl⟩
    | zero => simp
    | add x x' _ _ ihx ihx' => rw [star_add]; exact S.add_mem ihx ihx'
    | smul c x _ ihx =>
      rw [star_smul]
      exact S.smul_mem _ ihx
  have S_one : (1 : C(I → Circ, ℂ)) ∈ S := by
    rw [← mono_zero]; exact Submodule.subset_span ⟨_, rfl⟩
  let D : StarSubalgebra ℂ C(I → Circ, ℂ) :=
    { carrier := (S : Set C(I → Circ, ℂ))
      mul_mem' := fun {a b} ha hb => S_mul a ha b hb
      one_mem' := S_one
      add_mem' := fun {a b} ha hb => S.add_mem ha hb
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => by
        have : algebraMap ℂ C(I → Circ, ℂ) c = c • (1 : C(I → Circ, ℂ)) := by
          ext p; simp [Algebra.algebraMap_eq_smul_one]
        rw [this]; exact S.smul_mem c S_one
      star_mem' := fun {a} ha => S_star a ha }
  have hDsep : D.SeparatesPoints := by
    intro p q hpq
    by_contra hcon
    push_neg at hcon
    apply hpq
    funext i
    have hmem : (fun f : C(I → Circ, ℂ) => (f : (I → Circ) → ℂ)) (monoT (Pi.single i 1)) ∈
        (fun f : C(I → Circ, ℂ) => (f : (I → Circ) → ℂ)) '' (D : Set C(I → Circ, ℂ)) :=
      ⟨monoT (Pi.single i 1), Submodule.subset_span ⟨_, rfl⟩, rfl⟩
    have h3 := hcon _ hmem
    have h4 : ecC (p i) = ecC (q i) := by simpa [monoT_apply, skT_single] using h3
    exact ecC_inj h4
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints D hDsep
  have hG : G ∈ closure (D : Set C(I → Circ, ℂ)) := by
    have : G ∈ D.topologicalClosure := by rw [htop]; trivial
    exact this
  obtain ⟨b, hbD, hb⟩ := Metric.mem_closure_iff.mp hG ε hε
  exact ⟨b, hbD, by rwa [dist_comm]⟩

/-- **Kronecker (closed-subgroup form).** -/
theorem kronecker_mem [DecidableEq I] (C : AddSubgroup (I → Circ)) (hC : IsClosed (C : Set (I → Circ)))
    (s0 : I → Circ)
    (hs0 : ∀ k : I → ℤ, (∀ c ∈ C, skT k c = 0) → skT k s0 = 0) : s0 ∈ C := by
  by_contra hs
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  let μ : Measure C := Measure.addHaar
  have hint : ∀ f : C(C, ℂ), Integrable f μ := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hμpos : 0 < (μ Set.univ).toReal := by
    apply ENNReal.toReal_pos
    · exact (IsOpen.measure_pos μ isOpen_univ ⟨0, trivial⟩).ne'
    · exact measure_ne_top μ _
  -- shifted evaluation as a continuous map on `C`
  let shift : C(I → Circ, ℂ) → C(C, ℂ) := fun P =>
    ⟨fun c => P (s0 + (c : I → Circ)),
      P.continuous.comp (continuous_const.add continuous_subtype_val)⟩
  let incl : C(I → Circ, ℂ) → C(C, ℂ) := fun P =>
    ⟨fun c => P (c : I → Circ), P.continuous.comp continuous_subtype_val⟩
  have key : ∀ P ∈ trigSpan I, ∫ c, shift P c ∂μ = ∫ c, incl P c ∂μ := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      by_cases hk : ∀ c ∈ C, skT k c = 0
      · have h1 : skT k s0 = 0 := hs0 k hk
        have : ∀ c : C, shift (monoT k) c = incl (monoT k) c := by
          intro c
          simp only [shift, incl, ContinuousMap.coe_mk, monoT_apply, skT_add, h1, hk c c.2, zero_add]
        exact integral_congr_ae (Filter.Eventually.of_forall this)
      · push_neg at hk
        obtain ⟨c0, hc0C, hc0⟩ := hk
        let ψ : C → ℂ := fun c => monoT k (c : I → Circ)
        have hmul : ∀ p q, ψ (p + q) = ψ p * ψ q := by
          intro p q
          simp only [ψ, monoT_apply, AddSubgroup.coe_add, skT_add, ecC_add]
        have h0 : ψ ⟨c0, hc0C⟩ ≠ 1 := by
          intro h
          apply hc0
          have : ecC (skT k c0) = ecC 0 := by
            simpa [ψ, monoT_apply, ecC_zero] using h
          exact ecC_inj this
        have hψ : ∫ c, ψ c ∂μ = 0 := integral_char_eq_zero μ ψ hmul ⟨c0, hc0C⟩ h0
        have h2 : ∫ c, incl (monoT k) c ∂μ = 0 := hψ
        have h3 : ∫ c, shift (monoT k) c ∂μ = 0 := by
          have : ∀ c : C, shift (monoT k) c = monoT k s0 * ψ c := by
            intro c
            simp only [shift, ψ, ContinuousMap.coe_mk, monoT_apply, skT_add, ecC_add]
          simp_rw [this]
          rw [integral_const_mul, hψ, mul_zero]
        rw [h2, h3]
    | zero => simp [shift, incl]
    | add x x' _ _ ihx ihx' =>
      have e1 : shift (x + x') = shift x + shift x' := by ext c; rfl
      have e2 : incl (x + x') = incl x + incl x' := by ext c; rfl
      rw [e1, e2]
      simp only [ContinuousMap.add_apply]
      rw [integral_add (hint _) (hint _), integral_add (hint _) (hint _), ihx, ihx']
    | smul a x _ ihx =>
      have e1 : shift (a • x) = a • shift x := by ext c; rfl
      have e2 : incl (a • x) = a • incl x := by ext c; rfl
      rw [e1, e2]
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      rw [integral_const_mul, integral_const_mul, ihx]
  -- extension to all continuous functions
  have key2 : ∀ G : C(I → Circ, ℂ), ∫ c, shift G c ∂μ = ∫ c, incl G c ∂μ := by
    intro G
    by_contra hne
    have hpos : 0 < ‖(∫ c, shift G c ∂μ) - ∫ c, incl G c ∂μ‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 hne)
    set δ := ‖(∫ c, shift G c ∂μ) - ∫ c, incl G c ∂μ‖ with hδ
    set m := (μ Set.univ).toReal with hm
    have hε : 0 < δ / (4 * m) := by positivity
    obtain ⟨P, hP, hPG⟩ := trig_dense G (δ / (4 * m)) hε
    have hk := key P hP
    have b1 : ‖∫ c, (shift G c - shift P c) ∂μ‖ ≤ (δ / (4 * m)) * m := by
      refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun c => ?_)
      have := ContinuousMap.dist_apply_le_dist (f := P) (g := G) (s0 + (c : I → Circ))
      rw [dist_eq_norm] at this
      simp only [shift, ContinuousMap.coe_mk]
      rw [norm_sub_rev]
      linarith
    have b2 : ‖∫ c, (incl P c - incl G c) ∂μ‖ ≤ (δ / (4 * m)) * m := by
      refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun c => ?_)
      have := ContinuousMap.dist_apply_le_dist (f := P) (g := G) (c : I → Circ)
      rw [dist_eq_norm] at this
      simp only [incl, ContinuousMap.coe_mk]
      linarith
    have hd : (∫ c, shift G c ∂μ) - ∫ c, incl G c ∂μ =
        (∫ c, (shift G c - shift P c) ∂μ) + (∫ c, (incl P c - incl G c) ∂μ) := by
      rw [integral_sub (hint _) (hint _), integral_sub (hint _) (hint _), hk]; ring
    have h4 : δ ≤ (δ / (4 * m)) * m + (δ / (4 * m)) * m := by
      calc δ = ‖(∫ c, shift G c ∂μ) - ∫ c, incl G c ∂μ‖ := rfl
        _ = ‖(∫ c, (shift G c - shift P c) ∂μ) + (∫ c, (incl P c - incl G c) ∂μ)‖ := by rw [hd]
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add b1 b2)
    have h5 : (δ / (4 * m)) * m + (δ / (4 * m)) * m = δ / 2 := by field_simp; ring
    linarith
  -- the test function: distance to `C`
  let Gd : C(I → Circ, ℂ) :=
    ⟨fun t => ((Metric.infDist t (C : Set (I → Circ)) : ℝ) : ℂ),
      Complex.continuous_ofReal.comp (Metric.continuous_infDist_pt _)⟩
  have hGC : ∫ c, incl Gd c ∂μ = 0 := by
    have : ∀ c : C, incl Gd c = 0 := by
      intro c
      simp only [incl, Gd, ContinuousMap.coe_mk]
      rw [Metric.infDist_zero_of_mem c.2]; simp
    simp_rw [this]; simp
  have hpos : ∀ c : C, 0 < Metric.infDist (s0 + (c : I → Circ)) (C : Set (I → Circ)) := by
    intro c
    rw [← hC.notMem_iff_infDist_pos ⟨0, C.zero_mem⟩]
    intro hmem
    apply hs
    have := C.sub_mem hmem c.2
    simpa using this
  have hh : 0 < ∫ c : C, Metric.infDist (s0 + (c : I → Circ)) (C : Set (I → Circ)) ∂μ := by
    have hcont : Continuous fun c : C => Metric.infDist (s0 + (c : I → Circ)) (C : Set (I → Circ)) :=
      (Metric.continuous_infDist_pt _).comp (continuous_const.add continuous_subtype_val)
    rw [integral_pos_iff_support_of_nonneg (fun c => (hpos c).le)
      (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have : Function.support (fun c : C => Metric.infDist (s0 + (c : I → Circ)) (C : Set (I → Circ)))
        = Set.univ := by
      ext c; simp [(hpos c).ne']
    rw [this]
    exact IsOpen.measure_pos μ isOpen_univ ⟨0, trivial⟩
  have := key2 Gd
  rw [hGC] at this
  have h6 : ∫ c, shift Gd c ∂μ =
      ((∫ c : C, Metric.infDist (s0 + (c : I → Circ)) (C : Set (I → Circ)) ∂μ : ℝ) : ℂ) := by
    have e : ∀ c : C, shift Gd c = ((Metric.infDist (s0 + (c : I → Circ)) (C : Set (I → Circ)) : ℝ) : ℂ) := fun c => rfl
    simp_rw [e]
    exact integral_ofReal
  rw [h6] at this
  have := Complex.ofReal_eq_zero.1 this
  linarith

/-- **Kronecker (range form).** If every integer relation killing `Ψ` also kills `s₀`, then `s₀` lies in the
closure of the image of `Ψ`. -/
theorem kronecker_range [DecidableEq I] {G : Type} [AddCommGroup G] (Ψ : G →+ (I → Circ))
    (s0 : I → Circ) (hs0 : ∀ k : I → ℤ, (∀ g, skT k (Ψ g) = 0) → skT k s0 = 0) :
    s0 ∈ closure (Set.range Ψ) := by
  let C : AddSubgroup (I → Circ) := (AddMonoidHom.range Ψ).topologicalClosure
  have hC : IsClosed (C : Set (I → Circ)) := AddSubgroup.isClosed_topologicalClosure _
  have hmem : s0 ∈ C := by
    refine kronecker_mem C hC s0 (fun k hk => hs0 k (fun g => hk _ ?_))
    exact AddSubgroup.le_topologicalClosure _ ⟨g, rfl⟩
  have : (C : Set (I → Circ)) = closure (Set.range Ψ) := by
    simp only [C, AddSubgroup.topologicalClosure_coe]
    rfl
  rw [← this]; exact hmem

end Kronecker

end LeanCheck
