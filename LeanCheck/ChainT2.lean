import LeanCheck.ChainT1

/-!
# The modular topologies with real parameters: comparison, counting, rigidity, isomorphism
(HamelCharactersTVG_v18 Theorem 11.1, Corollary 11.2, Theorem 13.1, Corollary 13.2, Corollary 13.3)

All topologies are `β_f = betaT f ⊤`, `σ_f = sigmaT f ⊤` (the multiplier ranging over all real numbers).
Mathlib's `≤` is "finer than": the paper's `σ_g ⊆ σ_f` reads `sigmaT f ⊤ ≤ sigmaT g ⊤`.
-/

namespace LeanCheck

open Filter Topology Cardinal

/-! ### Rescaled function sets -/

lemma FsetScaled_top (g : ℝ →+ ℚ) (c : ℝ) (hc : c ≠ 0) : FsetScaled g c ⊤ = Fset g ⊤ := by
  ext m
  constructor
  · rintro ⟨a, -, rfl⟩; exact ⟨c * a, Submodule.mem_top, rfl⟩
  · rintro ⟨a, -, rfl⟩
    exact ⟨a / c, Submodule.mem_top, by congr 1; field_simp⟩

lemma fa_comp_scale (f g : ℝ →+ ℚ) (b : ℝ) (hb : ∀ x : ℝ, g x = f (b * x)) (a : ℝ) :
    fa g a = fa f (b * a) := by
  ext x
  simp only [fa_apply]
  rw [hb, mul_assoc]

lemma Fset_top_eq_iff (f g : ℝ →+ ℚ) (hg : g ≠ 0) :
    Fset g ⊤ = Fset f ⊤ ↔ ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f (b * x) := by
  constructor
  · intro h
    have hm : fa g 1 ∈ Fset g ⊤ := ⟨1, Submodule.mem_top, rfl⟩
    rw [h] at hm
    obtain ⟨b, -, hb⟩ := hm
    have hb' : ∀ x, g x = f (b * x) := fun x => by
      have := congrArg (fun m : ℝ →+ ℚ => m x) hb
      simpa [fa_apply] using this
    refine ⟨b, ?_, hb'⟩
    rintro rfl
    apply hg
    ext x
    rw [hb' x]; simp
  · rintro ⟨b, hb0, hb⟩
    ext m
    constructor
    · rintro ⟨a, -, rfl⟩
      exact ⟨b * a, Submodule.mem_top, fa_comp_scale f g b hb a⟩
    · rintro ⟨a, -, rfl⟩
      refine ⟨a / b, Submodule.mem_top, ?_⟩
      rw [fa_comp_scale f g b hb]
      congr 1; field_simp

/-! ### Theorem 11.1 -/

lemma cont_one_iff_le (t t' : TopologicalSpace ℝ) :
    Continuous[t, t'] (fun x : ℝ => (1 : ℝ) * x) ↔ t ≤ t' := by
  rw [← continuous_id_iff_le]
  have : (fun x : ℝ => (1 : ℝ) * x) = id := by funext x; simp
  rw [this]

/-- **Theorem 11.1 (exact comparison of the modular topologies).**  For nonzero `f, g`, the following are
equivalent: `σ_g ⊆ σ_f`; `σ_g = σ_f`; `g(x) = f(bx)` for some `b ≠ 0`; `β_g = β_f`; `β_g ⊆ β_f`. -/
theorem modular_comparison (f g : ℝ →+ ℚ) (hg : g ≠ 0) :
    List.TFAE
      [ sigmaT f ⊤ ≤ sigmaT g ⊤,
        sigmaT g ⊤ = sigmaT f ⊤,
        ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f (b * x),
        betaT g ⊤ = betaT f ⊤,
        betaT f ⊤ ≤ betaT g ⊤ ] := by
  have hsig : Fset g ⊤ = Fset f ⊤ → sigmaT g ⊤ = sigmaT f ⊤ := by
    intro h
    apply le_antisymm
    · have : Continuous[sigmaT g ⊤, sigmaT f ⊤] (fun x : ℝ => (1 : ℝ) * x) := by
        rw [scale_cont_sigma_iff g f ⊤ ⊤ 1, FsetScaled_top f 1 one_ne_zero, h]
      exact (cont_one_iff_le _ _).1 this
    · have : Continuous[sigmaT f ⊤, sigmaT g ⊤] (fun x : ℝ => (1 : ℝ) * x) := by
        rw [scale_cont_sigma_iff f g ⊤ ⊤ 1, FsetScaled_top g 1 one_ne_zero, h]
      exact (cont_one_iff_le _ _).1 this
  have hbet : Fset g ⊤ = Fset f ⊤ → betaT g ⊤ = betaT f ⊤ := by
    intro h
    apply le_antisymm
    · have : Continuous[betaT g ⊤, betaT f ⊤] (fun x : ℝ => (1 : ℝ) * x) := by
        rw [scale_cont_beta_iff g f ⊤ ⊤ 1, FsetScaled_top f 1 one_ne_zero, h]
      exact (cont_one_iff_le _ _).1 this
    · have : Continuous[betaT f ⊤, betaT g ⊤] (fun x : ℝ => (1 : ℝ) * x) := by
        rw [scale_cont_beta_iff f g ⊤ ⊤ 1, FsetScaled_top g 1 one_ne_zero, h]
      exact (cont_one_iff_le _ _).1 this
  tfae_have 1 → 3 := by
    intro h
    have hc : Continuous[sigmaT f ⊤, sigmaT g ⊤] (fun x : ℝ => (1 : ℝ) * x) := by
      exact (cont_one_iff_le _ _).2 h
    have hs := (scale_cont_sigma_iff f g ⊤ ⊤ 1).1 hc
    have hm : fa g (1 * 1) ∈ FsetScaled g 1 ⊤ := ⟨1, Submodule.mem_top, rfl⟩
    obtain ⟨b, -, hb⟩ := hs hm
    have hb' : ∀ x, g x = f (b * x) := fun x => by
      have := congrArg (fun m : ℝ →+ ℚ => m x) hb
      simpa [fa_apply] using this
    refine ⟨b, ?_, hb'⟩
    rintro rfl
    apply hg
    ext x
    rw [hb' x]; simp
  tfae_have 3 → 2 := fun h => hsig ((Fset_top_eq_iff f g hg).2 h)
  tfae_have 2 → 1 := fun h => h.symm.le
  tfae_have 3 → 4 := fun h => hbet ((Fset_top_eq_iff f g hg).2 h)
  tfae_have 4 → 5 := fun h => h.symm.le
  tfae_have 5 → 3 := by
    intro h
    have hc : Continuous[betaT f ⊤, betaT g ⊤] (fun x : ℝ => (1 : ℝ) * x) := by
      exact (cont_one_iff_le _ _).2 h
    have hs := (scale_cont_beta_iff f g ⊤ ⊤ 1).1 hc
    have hm : fa g (1 * 1) ∈ FsetScaled g 1 ⊤ := ⟨1, Submodule.mem_top, rfl⟩
    obtain ⟨b, -, hb⟩ := hs hm
    have hb' : ∀ x, g x = f (b * x) := fun x => by
      have := congrArg (fun m : ℝ →+ ℚ => m x) hb
      simpa [fa_apply] using this
    refine ⟨b, ?_, hb'⟩
    rintro rfl
    apply hg
    ext x
    rw [hb' x]; simp
  tfae_finish

/-- Distinct members of either modular family are incomparable. -/
theorem modular_incomparable (f g : ℝ →+ ℚ) (hf : f ≠ 0) (hg : g ≠ 0) :
    (sigmaT f ⊤ ≤ sigmaT g ⊤ → sigmaT g ⊤ = sigmaT f ⊤) ∧
    (betaT f ⊤ ≤ betaT g ⊤ → betaT g ⊤ = betaT f ⊤) := by
  have h := modular_comparison f g hg
  exact ⟨fun h1 => (h.out 1 2).1 h1, fun h1 => (h.out 5 4).1 h1⟩

/-! ### Corollary 11.2 : counting -/

theorem count_range {X Y : Type} (F : X → Y) (hX : #X = 2 ^ 𝔠)
    (hfib : ∀ x, #{y : X // F y = F x} ≤ 𝔠) : #(Set.range F) = 2 ^ 𝔠 := by
  classical
  have hsurj : Function.Surjective (Set.rangeFactorization F) :=
    fun ⟨y, x, hx⟩ => ⟨x, Subtype.ext hx⟩
  apply le_antisymm
  · rw [← hX]; exact mk_le_of_surjective hsurj
  · by_contra hlt
    rw [not_le] at hlt
    have hfib' : ∀ q : Set.range F, #{x : X // Set.rangeFactorization F x = q} ≤ 𝔠 := by
      intro q
      obtain ⟨x0, hx0⟩ := q.2
      refine le_trans (mk_le_of_injective (f := fun x : {x : X // Set.rangeFactorization F x = q} =>
        (⟨x.1, ?_⟩ : {y : X // F y = F x0})) ?_) (hfib x0)
      · have h1 := congrArg Subtype.val x.2
        simp only [Set.rangeFactorization_coe] at h1
        rw [h1, hx0]
      · intro x x' h
        exact Subtype.ext (congrArg (fun y : {y : X // F y = F x0} => y.1) h)
    have hsum : #X ≤ #(Set.range F) * 𝔠 := by
      rw [← mk_congr (Equiv.sigmaFiberEquiv (Set.rangeFactorization F)), mk_sigma,
        ← sum_const' (Set.range F) 𝔠]
      exact sum_le_sum _ _ hfib'
    have hlt2 : #(Set.range F) * 𝔠 < 2 ^ 𝔠 :=
      mul_lt_of_lt (aleph0_le_continuum.trans (cantor 𝔠).le) hlt (cantor 𝔠)
    rw [hX] at hsum
    exact absurd hsum (not_le.2 hlt2)

/-- The set of rescalings `{g | g = f_b, b ≠ 0}` has cardinality at most `𝔠`. -/
theorem rescale_class_le (f : ℝ →+ ℚ) (hf : f ≠ 0) :
    #{g : ℝ →+ ℚ // ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f (b * x)} ≤ 𝔠 := by
  classical
  have hex : ∀ g : {g : ℝ →+ ℚ // ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f (b * x)}, ∃ b : ℝ,
      g.1 = fa f b := fun g => by
    obtain ⟨b, -, hb⟩ := g.2
    exact ⟨b, by ext x; simp [fa_apply, hb x]⟩
  have inj : Function.Injective (fun g => Classical.choose (hex g)) := by
    intro g g' h
    apply Subtype.ext
    rw [Classical.choose_spec (hex g), Classical.choose_spec (hex g')]
    simp only at h
    rw [h]
  calc #{g : ℝ →+ ℚ // ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f (b * x)} ≤ #ℝ := mk_le_of_injective inj
    _ = 𝔠 := mk_real

/-- **Corollary 11.2.**  Each of the families `{σ_f}`, `{β_f}` (`f ≠ 0`) contains exactly `2^𝔠` distinct
topologies on the real line. -/
theorem modular_count :
    #(Set.range (fun f : {f : ℝ →+ ℚ // f ≠ 0} => sigmaT f.1 ⊤)) = 2 ^ 𝔠 ∧
    #(Set.range (fun f : {f : ℝ →+ ℚ // f ≠ 0} => betaT f.1 ⊤)) = 2 ^ 𝔠 := by
  constructor
  · refine count_range _ card_nonzero_addHom (fun f => ?_)
    refine le_trans (mk_le_of_injective
      (f := fun y : {y : {f : ℝ →+ ℚ // f ≠ 0} // sigmaT y.1 ⊤ = sigmaT f.1 ⊤} =>
        (⟨y.1.1, ((modular_comparison f.1 y.1.1 y.1.2).out 2 3).1 y.2⟩ :
          {g : ℝ →+ ℚ // ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f.1 (b * x)})) ?_) (rescale_class_le f.1 f.2)
    intro y y' h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  · refine count_range _ card_nonzero_addHom (fun f => ?_)
    refine le_trans (mk_le_of_injective
      (f := fun y : {y : {f : ℝ →+ ℚ // f ≠ 0} // betaT y.1 ⊤ = betaT f.1 ⊤} =>
        (⟨y.1.1, ((modular_comparison f.1 y.1.1 y.1.2).out 4 3).1 y.2⟩ :
          {g : ℝ →+ ℚ // ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f.1 (b * x)})) ?_) (rescale_class_le f.1 f.2)
    intro y y' h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)

/-! ### Theorem 13.1 : rigidity -/

/-- `η` is one of the two modular topologies built from `f` (real parameters). -/
def IsKind (f : ℝ →+ ℚ) (η : TopologicalSpace ℝ) : Prop := η = betaT f ⊤ ∨ η = sigmaT f ⊤

lemma kind_dual (f : ℝ →+ ℚ) (η : TopologicalSpace ℝ) (h : IsKind f η) (χ : Chars) :
    @Continuous ℝ Circ η circTop χ ↔ ∃ c a : ℝ, a ∈ (⊤ : Submodule ℚ ℝ) ∧ ∀ x : ℝ, χ x = chiH f c a x := by
  rcases h with rfl | rfl
  · exact dual_beta f ⊤ χ
  · exact dual_sigma f ⊤ χ

lemma kind_cmul (f : ℝ →+ ℚ) (η : TopologicalSpace ℝ) (h : IsKind f η) (r : ℝ) :
    @Continuous ℝ Circ η circTop (cmulHom r) := by
  rcases h with rfl | rfl
  · exact cmulHom_cont_beta f ⊤ r
  · exact continuous_le_dom (sigmaT_le_betaT f ⊤) (cmulHom_cont_beta f ⊤ r)

lemma kind_dilation (f : ℝ →+ ℚ) (hf : f ≠ 0) (η : TopologicalSpace ℝ) (h : IsKind f η) (r : ℝ) :
    Continuous[η, η] (fun x : ℝ => r * x) := by
  obtain ⟨u, hu⟩ := exists_unit f hf
  have hr : r ∈ scalarRing (⊤ : Submodule ℚ ℝ) := fun a _ => Submodule.mem_top
  rcases h with rfl | rfl
  · exact (scalar_beta f u hu ⊤ r).2 hr
  · exact (scalar_sigma f u hu ⊤ r).2 hr

/-- **Theorem 13.1 (rigidity of continuous homomorphisms).**  For any choice of kinds `η_f ∈ {β_f, σ_f}`,
`η_g ∈ {β_g, σ_g}`, every continuous additive map `(ℝ, η_f) → (ℝ, η_g)` is multiplication by a constant `c`,
and for `c ≠ 0` it is continuous exactly when `η_g ⊆ η_f`. -/
theorem tvg_rigidity (f g : ℝ →+ ℚ) (hf : f ≠ 0) (hg : g ≠ 0) (ηf ηg : TopologicalSpace ℝ)
    (hηf : IsKind f ηf) (hηg : IsKind g ηg) :
    (∀ L : ℝ →+ ℝ, Continuous[ηf, ηg] L → ∃ c : ℝ, ∀ x, L x = c * x) ∧
    (∀ c : ℝ, c ≠ 0 → (Continuous[ηf, ηg] (fun x : ℝ => c * x) ↔ ηf ≤ ηg)) := by
  refine ⟨fun L hL => ?_, fun c hc => ?_⟩
  · exact rigidity_abstract f g ⊤ ⊤ ηf ηg (kind_dual f ηf hηf) (kind_cmul g ηg hηg) L hL
  · constructor
    · intro h
      have h2 : Continuous[ηg, ηg] (fun x : ℝ => c⁻¹ * x) := kind_dilation g hg ηg hηg c⁻¹
      have : Continuous[ηf, ηg] (id : ℝ → ℝ) := by
        have e : (id : ℝ → ℝ) = (fun x : ℝ => c⁻¹ * x) ∘ (fun x : ℝ => c * x) := by
          funext x; simp [← mul_assoc, inv_mul_cancel₀ hc]
        rw [e]
        exact @Continuous.comp ℝ ℝ ℝ ηf ηg ηg _ _ h2 h
      exact continuous_id_iff_le.1 this
    · intro h
      have h1 : Continuous[ηf, ηf] (fun x : ℝ => c * x) := kind_dilation f hf ηf hηf c
      have h2 : Continuous[ηf, ηg] (id : ℝ → ℝ) := continuous_id_iff_le.2 h
      have := @Continuous.comp ℝ ℝ ℝ ηf ηf ηg (fun x : ℝ => c * x) (id : ℝ → ℝ) h2 h1
      exact this

/-! ### Corollary 13.2 : isomorphism classification -/

lemma isoTop_beta_iff (f g : ℝ →+ ℚ) (hg : g ≠ 0) :
    IsoTop (betaT f ⊤) (betaT g ⊤) ↔ ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f (b * x) := by
  rw [iso_iff_beta]
  constructor
  · rintro ⟨c, hc, h⟩
    rw [FsetScaled_top g c hc] at h
    exact (Fset_top_eq_iff f g hg).1 h
  · intro h
    exact ⟨1, one_ne_zero, by rw [FsetScaled_top g 1 one_ne_zero]; exact (Fset_top_eq_iff f g hg).2 h⟩

lemma isoTop_sigma_iff (f g : ℝ →+ ℚ) (hg : g ≠ 0) :
    IsoTop (sigmaT f ⊤) (sigmaT g ⊤) ↔ ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f (b * x) := by
  rw [iso_iff_sigma]
  constructor
  · rintro ⟨c, hc, h⟩
    rw [FsetScaled_top g c hc] at h
    exact (Fset_top_eq_iff f g hg).1 h
  · intro h
    exact ⟨1, one_ne_zero, by rw [FsetScaled_top g 1 one_ne_zero]; exact (Fset_top_eq_iff f g hg).2 h⟩

theorem iso_beta_iff_eq (f g : ℝ →+ ℚ) (hg : g ≠ 0) :
    IsoTop (betaT f ⊤) (betaT g ⊤) ↔ betaT g ⊤ = betaT f ⊤ :=
  (isoTop_beta_iff f g hg).trans ((modular_comparison f g hg).out 3 4)

theorem iso_sigma_iff_eq (f g : ℝ →+ ℚ) (hg : g ≠ 0) :
    IsoTop (sigmaT f ⊤) (sigmaT g ⊤) ↔ sigmaT g ⊤ = sigmaT f ⊤ :=
  (isoTop_sigma_iff f g hg).trans ((modular_comparison f g hg).out 3 2)

/-- Between distinct members of the same modular family the only continuous homomorphism is zero. -/
theorem distinct_hom_zero (f g : ℝ →+ ℚ) (hf : f ≠ 0) (hg : g ≠ 0) (ηf ηg : TopologicalSpace ℝ)
    (hηf : IsKind f ηf) (hηg : IsKind g ηg) (hinc : ηf ≤ ηg → ηg = ηf) (hne : ηg ≠ ηf)
    (L : ℝ →+ ℝ) (hL : Continuous[ηf, ηg] L) (x : ℝ) : L x = 0 := by
  obtain ⟨hrig, hcrit⟩ := tvg_rigidity f g hf hg ηf ηg hηf hηg
  obtain ⟨c, hc⟩ := hrig L hL
  by_cases hc0 : c = 0
  · rw [hc x, hc0, zero_mul]
  · exfalso
    have hfun : (L : ℝ → ℝ) = fun y : ℝ => c * y := funext hc
    rw [hfun] at hL
    exact hne (hinc ((hcrit c hc0).1 hL))

/-- **Corollary 13.2 (isomorphism classification).**  Within the `β`-family (resp. `σ`-family) two groups are
isomorphic iff their topologies are equal (iff `g = f_b`). -/
theorem tvg_isomorphism_classification (f g : ℝ →+ ℚ) (hf : f ≠ 0) (hg : g ≠ 0) :
    (IsoTop (betaT f ⊤) (betaT g ⊤) ↔ betaT g ⊤ = betaT f ⊤) ∧
    (IsoTop (sigmaT f ⊤) (sigmaT g ⊤) ↔ sigmaT g ⊤ = sigmaT f ⊤) ∧
    (betaT g ⊤ ≠ betaT f ⊤ → ∀ L : ℝ →+ ℝ, Continuous[betaT f ⊤, betaT g ⊤] L → ∀ x, L x = 0) ∧
    (sigmaT g ⊤ ≠ sigmaT f ⊤ → ∀ L : ℝ →+ ℝ, Continuous[sigmaT f ⊤, sigmaT g ⊤] L → ∀ x, L x = 0) :=
  ⟨iso_beta_iff_eq f g hg, iso_sigma_iff_eq f g hg,
    fun hne L hL x => distinct_hom_zero f g hf hg _ _ (Or.inl rfl) (Or.inl rfl)
      ((modular_incomparable f g hf hg).2) hne L hL x,
    fun hne L hL x => distinct_hom_zero f g hf hg _ _ (Or.inr rfl) (Or.inr rfl)
      ((modular_incomparable f g hf hg).1) hne L hL x⟩

/-- Every continuous endomorphism of a member of either modular family is a scalar multiplication. -/
theorem tvg_endomorphisms (f : ℝ →+ ℚ) (hf : f ≠ 0) :
    (∀ L : ℝ →+ ℝ, Continuous[betaT f ⊤, betaT f ⊤] L → ∃ c : ℝ, ∀ x, L x = c * x) ∧
    (∀ L : ℝ →+ ℝ, Continuous[sigmaT f ⊤, sigmaT f ⊤] L → ∃ c : ℝ, ∀ x, L x = c * x) :=
  ⟨(tvg_rigidity f f hf hf _ _ (Or.inl rfl) (Or.inl rfl)).1,
    (tvg_rigidity f f hf hf _ _ (Or.inr rfl) (Or.inr rfl)).1⟩

/-- Each family contains exactly `2^𝔠` pairwise nonisomorphic topological groups. -/
theorem tvg_isomorphism_count :
    #(Quotient (isoSetoid (fun f : {f : ℝ →+ ℚ // f ≠ 0} => betaT f.1 ⊤))) = 2 ^ 𝔠 ∧
    #(Quotient (isoSetoid (fun f : {f : ℝ →+ ℚ // f ≠ 0} => sigmaT f.1 ⊤))) = 2 ^ 𝔠 := by
  constructor
  · refine count_types _ card_nonzero_addHom (fun f => ?_)
    refine le_trans (mk_le_of_injective
      (f := fun y : {y : {f : ℝ →+ ℚ // f ≠ 0} // IsoTop (betaT f.1 ⊤) (betaT y.1 ⊤)} =>
        (⟨y.1.1, (isoTop_beta_iff f.1 y.1.1 y.1.2).1 y.2⟩ :
          {g : ℝ →+ ℚ // ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f.1 (b * x)})) ?_) (rescale_class_le f.1 f.2)
    intro y y' h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  · refine count_types _ card_nonzero_addHom (fun f => ?_)
    refine le_trans (mk_le_of_injective
      (f := fun y : {y : {f : ℝ →+ ℚ // f ≠ 0} // IsoTop (sigmaT f.1 ⊤) (sigmaT y.1 ⊤)} =>
        (⟨y.1.1, (isoTop_sigma_iff f.1 y.1.1 y.1.2).1 y.2⟩ :
          {g : ℝ →+ ℚ // ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f.1 (b * x)})) ?_) (rescale_class_le f.1 f.2)
    intro y y' h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)

/-! ### Corollary 13.3 : maps between the two families -/

/-- **Corollary 13.3.**  There is no nonzero continuous homomorphism `(ℝ, β_f) → (ℝ, σ_g)`.  A nonzero continuous
homomorphism `(ℝ, σ_f) → (ℝ, β_g)` exists exactly when `g = f_b` for some `b ≠ 0`, and in that case all scalar
multiplications are continuous. -/
theorem tvg_maps_between_families (f g : ℝ →+ ℚ) (hf : f ≠ 0) (hg : g ≠ 0) :
    (∀ L : ℝ →+ ℝ, Continuous[betaT f ⊤, sigmaT g ⊤] L → ∀ x, L x = 0) ∧
    ((∃ L : ℝ →+ ℝ, L ≠ 0 ∧ Continuous[sigmaT f ⊤, betaT g ⊤] L) ↔
      ∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f (b * x)) ∧
    ((∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f (b * x)) →
      ∀ c : ℝ, Continuous[sigmaT f ⊤, betaT g ⊤] (fun x : ℝ => c * x)) := by
  have key : ∀ c : ℝ, Continuous[sigmaT f ⊤, betaT g ⊤] (fun x : ℝ => c * x) ↔
      ∀ a ∈ (⊤ : Submodule ℚ ℝ), ∃ b ∈ (⊤ : Submodule ℚ ℝ), fa g (c * a) = fa f b := fun c => by
    obtain ⟨u, hu⟩ := exists_unit f hf
    exact scale_cont_target_beta f g ⊤ ⊤ (sigmaT f ⊤) (sigmaT_le_betaT f ⊤)
      (fun χ => dual_sigma f ⊤ χ) c
  have hD : (∃ b : ℝ, b ≠ 0 ∧ ∀ x : ℝ, g x = f (b * x)) →
      ∀ c : ℝ, Continuous[sigmaT f ⊤, betaT g ⊤] (fun x : ℝ => c * x) := by
    rintro ⟨b, hb0, hb⟩ c
    exact (key c).2 (fun a _ => ⟨b * (c * a), Submodule.mem_top, fa_comp_scale f g b hb _⟩)
  refine ⟨?_, ⟨?_, ?_⟩, hD⟩
  · intro L hL x
    obtain ⟨c, hc⟩ := rigidity_abstract f g ⊤ ⊤ (betaT f ⊤) (sigmaT g ⊤) (fun χ => dual_beta f ⊤ χ)
      (fun r => continuous_le_dom (sigmaT_le_betaT g ⊤) (cmulHom_cont_beta g ⊤ r)) L hL
    by_cases hc0 : c = 0
    · rw [hc x, hc0, zero_mul]
    · exfalso
      have hfun : (L : ℝ → ℝ) = fun y : ℝ => c * y := funext hc
      have hcont : Continuous[betaT f ⊤, uR] (fun y : ℝ => c * y) := by
        rw [← hfun]
        have hid : Continuous[sigmaT g ⊤, uR] (id : ℝ → ℝ) := continuous_id_iff_le.2 (sigmaT_le_usual g ⊤)
        have := @Continuous.comp ℝ ℝ ℝ (betaT f ⊤) (sigmaT g ⊤) uR (L : ℝ → ℝ) (id : ℝ → ℝ) hid hL
        exact this
      refine no_cont_surj_usual (betaT f ⊤) (beta_precompact f ⊤) (AddMonoidHom.mulLeft c) hcont ?_
      intro y; exact ⟨c⁻¹ * y, by simp [hc0]⟩
  · rintro ⟨L, hL0, hL⟩
    obtain ⟨c, hc⟩ := rigidity_abstract f g ⊤ ⊤ (sigmaT f ⊤) (betaT g ⊤) (fun χ => dual_sigma f ⊤ χ)
      (fun r => cmulHom_cont_beta g ⊤ r) L hL
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hL0
      ext x; rw [hc x]; simp
    have hfun : (L : ℝ → ℝ) = fun y : ℝ => c * y := funext hc
    rw [hfun] at hL
    have h1 := (key c).1 hL (1 / c) Submodule.mem_top
    obtain ⟨b, -, hb⟩ := h1
    have hb' : ∀ x, g x = f (b * x) := fun x => by
      have := congrArg (fun m : ℝ →+ ℚ => m x) hb
      have e : c * (1 / c) = 1 := mul_one_div_cancel hc0
      simp only [fa_apply, e, one_mul] at this
      exact this
    refine ⟨b, ?_, hb'⟩
    rintro rfl
    apply hg
    ext x
    rw [hb' x]; simp
  · intro hb
    refine ⟨AddMonoidHom.mulLeft 1, ?_, hD hb 1⟩
    intro h0
    have := congrArg (fun L : ℝ →+ ℝ => L 1) h0
    simp at this

end LeanCheck
