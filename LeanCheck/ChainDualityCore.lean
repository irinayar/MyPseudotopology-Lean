import LeanCheck.ChainPrecompact

/-!
# Characters of a compact abelian group of tori are integer combinations of coordinates

`char_in_span`: let `T` be a compact Hausdorff abelian topological group, `z_i : T → 𝕋` finitely many continuous
characters that separate the points of `T`.  Then every continuous character `w : T → 𝕋` is an integer combination
`w = ∑ k_i z_i`.  The proof is by Fourier analysis (Stone-Weierstrass for the span of the monomials, orthogonality
of characters for Haar measure).  This is the heart of the duality fact (F1).
-/

namespace LeanCheck

open Filter Topology MeasureTheory

/-- Orthogonality: a multiplicative function that is `≠ 1` somewhere integrates to `0` against an invariant measure. -/
lemma integral_char_eq_zero {T : Type} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [MeasurableSpace T] [BorelSpace T] (μ : Measure T) [μ.IsAddRightInvariant]
    (ψ : T → ℂ) (hmul : ∀ p q, ψ (p + q) = ψ p * ψ q) (p0 : T) (h0 : ψ p0 ≠ 1) :
    ∫ p, ψ p ∂μ = 0 := by
  have h := integral_add_right_eq_self (μ := μ) ψ p0
  have e : (∫ p, ψ (p + p0) ∂μ) = (∫ p, ψ p ∂μ) * ψ p0 := by
    simp_rw [hmul]; exact integral_mul_const _ _
  rw [e] at h
  have : (∫ p, ψ p ∂μ) * (ψ p0 - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.mp this with h1 | h1
  · exact h1
  · exact absurd (sub_eq_zero.mp h1) h0

theorem char_in_span {T : Type} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [CompactSpace T] [T2Space T] [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T]
    {I : Type} [Fintype I] (z : I → (T →+ Circ)) (hz : ∀ i, Continuous (z i))
    (hsep : ∀ p q, (∀ i, z i p = z i q) → p = q) (w : T →+ Circ) (hw : Continuous w) :
    ∃ k : I → ℤ, ∀ p, w p = ∑ i, k i • z i p := by
  classical
  let ec : Circ → ℂ := fun s => ((AddCircle.toCircle s : Circle) : ℂ)
  have ec_add : ∀ s t, ec (s + t) = ec s * ec t := by
    intro s t; simp [ec, AddCircle.toCircle_add]
  have ec_norm : ∀ s, ‖ec s‖ = 1 := fun s => by simp [ec]
  have ec_conj : ∀ s, (starRingEnd ℂ) (ec s) = ec (-s) := by
    intro s
    simp only [ec, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]
  have ec_cont : Continuous ec := continuous_subtype_val.comp AddCircle.continuous_toCircle
  have ec_inj : Function.Injective ec :=
    Subtype.coe_injective.comp (AddCircle.injective_toCircle one_ne_zero)
  have ec_zero : ec 0 = 1 := by simp [ec]
  have ec_mul_conj : ∀ s, ec s * (starRingEnd ℂ) (ec s) = 1 := by
    intro s
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ec_norm]; simp
  -- coordinate sums
  let sk : (I → ℤ) → T → Circ := fun k p => ∑ i, k i • z i p
  have sk_cont : ∀ k, Continuous (sk k) := fun k =>
    continuous_finset_sum _ (fun i _ => (continuous_zsmul (k i)).comp (hz i))
  have sk_add : ∀ k p q, sk k (p + q) = sk k p + sk k q := by
    intro k p q; simp [sk, smul_add, Finset.sum_add_distrib]
  have sk_addk : ∀ k l p, sk (k + l) p = sk k p + sk l p := by
    intro k l p; simp [sk, add_smul, Finset.sum_add_distrib]
  have sk_neg : ∀ k p, sk (-k) p = - sk k p := by
    intro k p; simp [sk, neg_smul, Finset.sum_neg_distrib]
  have sk_zero : ∀ p, sk 0 p = 0 := by intro p; simp [sk]
  have sk_single : ∀ i p, sk (Pi.single i 1) p = z i p := by
    intro i p
    simp only [sk]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_apply, hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  let mono : (I → ℤ) → C(T, ℂ) := fun k => ⟨fun p => ec (sk k p), ec_cont.comp (sk_cont k)⟩
  have mono_apply : ∀ k p, mono k p = ec (sk k p) := fun k p => rfl
  have mono_mul : ∀ k l, mono k * mono l = mono (k + l) := by
    intro k l; ext p
    simp only [ContinuousMap.mul_apply, mono_apply, sk_addk, ec_add]
  have mono_star : ∀ k, star (mono k) = mono (-k) := by
    intro k; ext p
    simp only [ContinuousMap.star_apply, mono_apply, sk_neg]
    exact ec_conj _
  have mono_zero : mono 0 = 1 := by
    ext p; simp [mono_apply, sk_zero, ec_zero]
  -- the span of the monomials is a star subalgebra
  let S : Submodule ℂ C(T, ℂ) := Submodule.span ℂ (Set.range mono)
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
  have S_one : (1 : C(T, ℂ)) ∈ S := by
    rw [← mono_zero]; exact Submodule.subset_span ⟨_, rfl⟩
  let D : StarSubalgebra ℂ C(T, ℂ) :=
    { carrier := (S : Set C(T, ℂ))
      mul_mem' := fun {a b} ha hb => S_mul a ha b hb
      one_mem' := S_one
      add_mem' := fun {a b} ha hb => S.add_mem ha hb
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => by
        have : algebraMap ℂ C(T, ℂ) c = c • (1 : C(T, ℂ)) := by
          ext p; simp [Algebra.algebraMap_eq_smul_one]
        rw [this]; exact S.smul_mem c S_one
      star_mem' := fun {a} ha => S_star a ha }
  have hDsep : D.SeparatesPoints := by
    intro p q hpq
    by_contra hcon
    push_neg at hcon
    apply hpq
    apply hsep
    intro i
    have hmem : (fun f : C(T, ℂ) => (f : T → ℂ)) (mono (Pi.single i 1)) ∈
        (fun f : C(T, ℂ) => (f : T → ℂ)) '' (D : Set C(T, ℂ)) :=
      ⟨mono (Pi.single i 1), Submodule.subset_span ⟨_, rfl⟩, rfl⟩
    have h3 := hcon _ hmem
    have h4 : ec (z i p) = ec (z i q) := by simpa [mono_apply, sk_single] using h3
    exact ec_inj h4
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints D hDsep
  let wc : C(T, ℂ) := ⟨fun p => ec (w p), ec_cont.comp hw⟩
  have hwc : wc ∈ closure (D : Set C(T, ℂ)) := by
    have : wc ∈ D.topologicalClosure := by rw [htop]; trivial
    exact this
  obtain ⟨b, hbD, hb⟩ := Metric.mem_closure_iff.mp hwc (1 / 2) (by norm_num)
  -- Haar measure
  let μ : Measure T := Measure.addHaar
  have hint : ∀ f : C(T, ℂ), Integrable f μ := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hint' : ∀ f g : C(T, ℂ), Integrable (fun p => f p * star (g p)) μ := fun f g => by
    exact hint (f * star g)
  by_cases hex : ∃ k, ∀ p, ec (sk k p) = ec (w p)
  · obtain ⟨k, hk⟩ := hex
    exact ⟨k, fun p => (ec_inj (hk p)).symm⟩
  · exfalso
    push_neg at hex
    -- every monomial is orthogonal to `w`
    have horth : ∀ k, ∫ p, mono k p * star (wc p) ∂μ = 0 := by
      intro k
      obtain ⟨p0, hp0⟩ := hex k
      refine integral_char_eq_zero μ (fun p => mono k p * star (wc p)) ?_ p0 ?_
      · intro p q
        simp only [mono_apply, wc, ContinuousMap.coe_mk, map_add, sk_add, ec_add, star_mul']
        ring
      · intro h1
        apply hp0
        simp only [mono_apply, wc, ContinuousMap.coe_mk] at h1
        calc ec (sk k p0) = ec (sk k p0) * (star (ec (w p0)) * ec (w p0)) := by
              rw [mul_comm (star (ec (w p0))), show star (ec (w p0)) = (starRingEnd ℂ) (ec (w p0)) from rfl,
                ec_mul_conj, mul_one]
          _ = (ec (sk k p0) * star (ec (w p0))) * ec (w p0) := by ring
          _ = ec (w p0) := by rw [h1, one_mul]
    have hspan : ∀ a ∈ S, ∫ p, a p * star (wc p) ∂μ = 0 := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem x hx => obtain ⟨k, rfl⟩ := hx; exact horth k
      | zero => simp
      | add x x' _ _ ihx ihx' =>
        simp only [ContinuousMap.add_apply, add_mul]
        rw [integral_add (hint' x wc) (hint' x' wc), ihx, ihx', add_zero]
      | smul c x _ ihx =>
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
        rw [integral_const_mul, ihx, mul_zero]
    have hb0 := hspan b hbD
    have hμpos : 0 < (μ Set.univ).toReal := by
      apply ENNReal.toReal_pos
      · exact (IsOpen.measure_pos μ isOpen_univ ⟨0, trivial⟩).ne'
      · exact measure_ne_top μ _
    have hww : ∫ p, wc p * star (wc p) ∂μ = ((μ Set.univ).toReal : ℂ) := by
      have : ∀ p, wc p * star (wc p) = (1 : ℂ) := by
        intro p
        simp only [wc, ContinuousMap.coe_mk]
        exact ec_mul_conj _
      simp_rw [this]
      simp [MeasureTheory.measureReal_def]
    have hdiff : ‖∫ p, (b p - wc p) * star (wc p) ∂μ‖ ≤ (1 / 2) * (μ Set.univ).toReal := by
      refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun p => ?_)
      have h1 : ‖wc p‖ = 1 := by simp [wc, ec_norm]
      rw [norm_mul, norm_star, h1, mul_one, norm_sub_rev]
      have h2 := ContinuousMap.dist_apply_le_dist (f := wc) (g := b) p
      rw [dist_eq_norm] at h2
      linarith
    have hsplit : ∫ p, b p * star (wc p) ∂μ =
        ∫ p, wc p * star (wc p) ∂μ + ∫ p, (b p - wc p) * star (wc p) ∂μ := by
      rw [← integral_add (hint' wc wc) (by simpa using hint' (b - wc) wc)]
      congr 1; ext p; ring
    rw [hb0, hww] at hsplit
    have h5 : ∫ p, (b p - wc p) * star (wc p) ∂μ = -((μ Set.univ).toReal : ℂ) :=
      (eq_neg_of_add_eq_zero_right hsplit.symm)
    rw [h5, norm_neg, Complex.norm_real, Real.norm_of_nonneg hμpos.le] at hdiff
    linarith

end LeanCheck
