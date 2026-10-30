import LeanCheck.ChainIso3

/-!
# Isomorphism classification, part 4: exact isomorphism criterion for `τ_{f,S}`
(TVGQ-v7 Theorem `tauiso:iso`, Corollary `tauiso:types`)

A map `L = m_c ∘ (id + Λ)` with `c ≠ 0` and `Λ x = ∑ σ_j f(b_j x)` is a topological group isomorphism
iff `A = (id + Λ)|_W` is invertible on `W = span_ℚ{σ_j}` and `FsetScaled g c T = Fset f S`; the inverse is
`L⁻¹ y = y/c − ∑ (A⁻¹σ_j) f(b_j y / c)`.
-/

namespace LeanCheck

open Filter Topology

/-- `Λ x = ∑ σ_j f(b_j x)`, as an additive map. -/
noncomputable def LamHom (f : ℝ →+ ℚ) {κ : Type} [Fintype κ] (b σ : κ → ℝ) : ℝ →+ ℝ where
  toFun x := ∑ j, σ j * ((f (b j * x) : ℚ) : ℝ)
  map_zero' := by simp
  map_add' x y := by
    simp only [mul_add, map_add, Rat.cast_add, Finset.sum_add_distrib]

lemma LamHom_apply (f : ℝ →+ ℚ) {κ : Type} [Fintype κ] (b σ : κ → ℝ) (x : ℝ) :
    LamHom f b σ x = ∑ j, σ j * ((f (b j * x) : ℚ) : ℝ) := rfl

lemma LamHom_smul (f : ℝ →+ ℚ) {κ : Type} [Fintype κ] (b σ : κ → ℝ) (q : ℚ) (x : ℝ) :
    LamHom f b σ ((q : ℝ) * x) = (q : ℝ) * LamHom f b σ x := by
  rw [LamHom_apply, LamHom_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show b j * ((q : ℝ) * x) = (q : ℝ) * (b j * x) by ring, f_ratmul]
  push_cast
  ring

/-- The `ℚ`-span `W` of the coefficients. -/
noncomputable def Wsp {κ : Type} (σ : κ → ℝ) : Submodule ℚ ℝ := Submodule.span ℚ (Set.range σ)

lemma Lam_mem (f : ℝ →+ ℚ) {κ : Type} [Fintype κ] (b σ : κ → ℝ) (x : ℝ) :
    LamHom f b σ x ∈ Wsp σ := by
  rw [LamHom_apply]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  have h : σ j ∈ Wsp σ := Submodule.subset_span ⟨j, rfl⟩
  have := (Wsp σ).smul_mem (f (b j * x)) h
  simpa [Rat.smul_def, mul_comm] using this

/-- `A = (id + Λ)|_W : W → W` is invertible. -/
noncomputable def AInv (f : ℝ →+ ℚ) {κ : Type} [Fintype κ] (b σ : κ → ℝ) : Prop :=
  (∀ w ∈ Wsp σ, w + LamHom f b σ w = 0 → w = 0) ∧
  (∀ w ∈ Wsp σ, ∃ w' ∈ Wsp σ, w' + LamHom f b σ w' = w)

lemma eq_zero_of_span (C : ℝ) {ι : Type} [Fintype ι] (ρ : ι → ℝ)
    (h : ∀ y : ℝ, ∃ q : ι → ℚ, C * y = ∑ i, ρ i * ((q i : ℚ) : ℝ)) : C = 0 := by
  by_contra hC
  apply Cardinal.not_countable_real
  have : (Set.univ : Set ℝ) ⊆
      Set.range (fun q : ι → ℚ => (∑ i, ρ i * ((q i : ℚ) : ℝ)) / C) := by
    intro t _
    obtain ⟨q, hq⟩ := h t
    refine ⟨q, ?_⟩
    show (∑ i, ρ i * ((q i : ℚ) : ℝ)) / C = t
    rw [← hq]; field_simp
  exact (Set.countable_range _).mono this

/-- The "representation" lemma: `L x = c (x + Λ x)` is of the form of `tauiso:hom`. -/
lemma L_form (f : ℝ →+ ℚ) {κ : Type} [Fintype κ] (b σ : κ → ℝ) (c : ℝ) (L : ℝ →+ ℝ)
    (hL : ∀ x, L x = c * (x + LamHom f b σ x)) :
    ∀ x, L x = c * x + ∑ j, (c * σ j) * ((f (b j * x) : ℚ) : ℝ) := by
  intro x
  rw [hL x, LamHom_apply, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- The candidate inverse of `id + Λ`: `N z = z − ∑ τ_j f(b_j z)`. -/
noncomputable def Ninv (f : ℝ →+ ℚ) {κ : Type} [Fintype κ] (b τ : κ → ℝ) (z : ℝ) : ℝ :=
  z - ∑ j, τ j * ((f (b j * z) : ℚ) : ℝ)

lemma Ninv_spec (f : ℝ →+ ℚ) {κ : Type} [Fintype κ] (b σ τ : κ → ℝ)
    (hτ : ∀ j, τ j + LamHom f b σ (τ j) = σ j) (z : ℝ) :
    Ninv f b τ z + LamHom f b σ (Ninv f b τ z) = z := by
  have hNz : Ninv f b τ z = z - ∑ j, ((f (b j * z) : ℚ) : ℝ) * τ j := by
    unfold Ninv
    congr 1
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hLN : LamHom f b σ (Ninv f b τ z) =
      LamHom f b σ z - ∑ j, ((f (b j * z) : ℚ) : ℝ) * LamHom f b σ (τ j) := by
    rw [hNz, map_sub, map_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => LamHom_smul f b σ _ _)
  have hLamz : LamHom f b σ z = ∑ j, ((f (b j * z) : ℚ) : ℝ) * σ j := by
    rw [LamHom_apply]; exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hsum : ∑ j, ((f (b j * z) : ℚ) : ℝ) * σ j =
      ∑ j, ((f (b j * z) : ℚ) : ℝ) * τ j + ∑ j, ((f (b j * z) : ℚ) : ℝ) * LamHom f b σ (τ j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by rw [← mul_add, hτ])
  rw [hLN, hNz]
  linarith

/-- **Inverse formula** `L⁻¹ y = y/c − ∑ τ_j f(b_j y / c)`, with `τ_j = A⁻¹ σ_j`. -/
theorem tau_iso_inverse (f : ℝ →+ ℚ) (c : ℝ) (hc : c ≠ 0) {κ : Type} [Fintype κ]
    (b σ τ : κ → ℝ) (hτ : ∀ j, τ j + LamHom f b σ (τ j) = σ j) (L : ℝ →+ ℝ)
    (hL : ∀ x, L x = c * (x + LamHom f b σ x)) (e : ℝ ≃+ ℝ) (he : ∀ x, e x = L x) (y : ℝ) :
    e.symm y = y / c - ∑ j, τ j * ((f (b j * (y / c)) : ℚ) : ℝ) := by
  apply e.injective
  rw [e.apply_symm_apply, he, hL]
  have := Ninv_spec f b σ τ hτ (y / c)
  unfold Ninv at this
  rw [this]
  field_simp

/-- **Exact isomorphism criterion** (TVGQ-v7 Theorem `tauiso:iso`). -/
theorem tau_iso_criterion (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (c : ℝ) (hc : c ≠ 0)
    {κ : Type} [Fintype κ] (b σ : κ → ℝ) (hb : ∀ j, b j ∈ S) (L : ℝ →+ ℝ)
    (hL : ∀ x, L x = c * (x + LamHom f b σ x)) :
    (∃ e : ℝ ≃+ ℝ, (∀ x, e x = L x) ∧ Continuous[tauT f S, tauT g T] e ∧
        Continuous[tauT g T, tauT f S] e.symm) ↔
      AInv f b σ ∧ FsetScaled g c T = Fset f S := by
  have hLd := L_form f b σ c L hL
  constructor
  · rintro ⟨e, he, hcont, hcont'⟩
    have hU' : Continuous[tauT g T, uR'] (e.symm : ℝ →+ ℝ) :=
      continuous_le_rng (TfS_le_usual f S usualQ) hcont'
    obtain ⟨c'', κ', hκ', b', d', hb', hform'⟩ := (tau_real_iff g T (e.symm : ℝ →+ ℝ)).1 hU'
    have hsub1 : FsetScaled g c T ⊆ Fset f S :=
      tau_hom_necessary f g S T L c b (fun j => c * σ j) hb hLd
        (by
          have : (L : ℝ → ℝ) = (e : ℝ → ℝ) := funext fun x => (he x).symm
          rw [this]; exact hcont)
    have hc'' : c'' = c⁻¹ := by
      have hC : c * c'' - 1 = 0 := by
        refine eq_zero_of_span (c * c'' - 1) (Sum.elim (fun j : κ' => -(c * d' j))
          (fun i : κ => -(c * σ i))) (fun y => ?_)
        refine ⟨Sum.elim (fun j : κ' => g (b' j * y))
          (fun i : κ => f (b i * e.symm y)), ?_⟩
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        have h1 : L (e.symm y) = y := by
          have := e.apply_symm_apply y
          rw [he] at this; exact this
        have hy : y = c * (e.symm y + ∑ i, σ i * ((f (b i * e.symm y) : ℚ) : ℝ)) := by
          have := hL (e.symm y)
          rw [h1, LamHom_apply] at this
          exact this
        have h3 : e.symm y = c'' * y + ∑ j, d' j * ((g (b' j * y) : ℚ) : ℝ) := hform' y
        have h3c : c * e.symm y =
            c * c'' * y + c * ∑ j, d' j * ((g (b' j * y) : ℚ) : ℝ) := by
          rw [h3]; ring
        have e1 : ∑ j : κ', (-(c * d' j)) * ((g (b' j * y) : ℚ) : ℝ) =
            -c * ∑ j, d' j * ((g (b' j * y) : ℚ) : ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
        have e2 : ∑ i : κ, (-(c * σ i)) * ((f (b i * e.symm y) : ℚ) : ℝ) =
            -c * ∑ i, σ i * ((f (b i * e.symm y) : ℚ) : ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [e1, e2]
        have hy' : y = c * e.symm y + c * ∑ i, σ i * ((f (b i * e.symm y) : ℚ) : ℝ) := by
          rw [← mul_add]; exact hy
        linarith
      exact eq_inv_of_mul_eq_one_right (by linarith)
    have hsub2 : FsetScaled f c⁻¹ S ⊆ Fset g T := by
      rw [← hc'']
      exact tau_hom_necessary g f T S (e.symm : ℝ →+ ℝ) c'' b' d' hb' hform' hcont'
    refine ⟨⟨?_, ?_⟩, fscaled_fwd f g S T c hc hsub1 hsub2⟩
    · intro w _ hw
      have : L w = L 0 := by rw [hL w, hw, mul_zero, map_zero]
      have h2 : e w = e 0 := by rw [he, he]; exact this
      exact e.injective h2
    · intro w hw
      obtain ⟨x, hx⟩ := e.surjective (c * w)
      have hx2 : c * w = c * (x + LamHom f b σ x) := by rw [← hL x, ← he x]; exact hx.symm
      have h3 : w = x + LamHom f b σ x := mul_left_cancel₀ hc hx2
      refine ⟨x, ?_, h3.symm⟩
      have h1 : x = w - LamHom f b σ x := by linarith
      rw [h1]
      exact (Wsp σ).sub_mem hw (Lam_mem f b σ x)
  · rintro ⟨⟨hinj, hsurj⟩, heq⟩
    have hsub : FsetScaled g c T ⊆ Fset f S := heq.subset
    have hMinj : ∀ x, x + LamHom f b σ x = 0 → x = 0 := by
      intro x hx
      have hxW : x ∈ Wsp σ := by
        have : x = -LamHom f b σ x := by linarith
        rw [this]; exact (Wsp σ).neg_mem (Lam_mem f b σ x)
      exact hinj x hxW hx
    choose τ hτW hτ using fun j : κ => hsurj (σ j) (Submodule.subset_span ⟨j, rfl⟩)
    have hLinj : Function.Injective L := by
      intro x y hxy
      have h1 : L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      rw [hL] at h1
      have h2 := (mul_eq_zero.1 h1).resolve_left hc
      rw [map_sub] at h2
      have h3 : (x - y) + LamHom f b σ (x - y) = 0 := by rw [map_sub]; exact h2
      exact sub_eq_zero.1 (hMinj _ h3)
    have hLsurj : Function.Surjective L := by
      intro y
      refine ⟨Ninv f b τ (y / c), ?_⟩
      rw [hL, Ninv_spec f b σ τ hτ]
      field_simp
    let e : ℝ ≃+ ℝ := AddEquiv.ofBijective L ⟨hLinj, hLsurj⟩
    have he : ∀ x, e x = L x := fun x => rfl
    have hsymm := tau_iso_inverse f c hc b σ τ hτ L hL e he
    have hcont : Continuous[tauT f S, tauT g T] e :=
      tau_hom_sufficient f g S T L c b (fun j => c * σ j) hb hLd hsub
    have hβ : ∀ j, ∃ β ∈ T, fa f (b j) = fa g (c * β) := by
      intro j
      have hm : fa f (b j) ∈ Fset f S := ⟨b j, hb j, rfl⟩
      rw [← heq] at hm
      obtain ⟨β, hβT, hβe⟩ := hm
      exact ⟨β, hβT, hβe⟩
    choose β hβT hβe using hβ
    have hform : ∀ y, e.symm y = c⁻¹ * y + ∑ j, (-τ j) * ((g (β j * y) : ℚ) : ℝ) := by
      intro y
      rw [hsymm y]
      have hfg : ∀ j, f (b j * (y / c)) = g (β j * y) := by
        intro j
        have := congrArg (fun m : ℝ →+ ℚ => m (y / c)) (hβe j)
        simp only [fa_apply] at this
        rw [this]; congr 1; field_simp
      simp only [hfg]
      rw [div_eq_inv_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hcont' : Continuous[tauT g T, tauT f S] e.symm :=
      tau_hom_sufficient g f T S (e.symm : ℝ →+ ℝ) c⁻¹ β (fun j => -τ j) hβT hform
        (fscaled_sub_inv f g S T c hc heq)
    exact ⟨e, he, hcont, hcont'⟩

end LeanCheck
