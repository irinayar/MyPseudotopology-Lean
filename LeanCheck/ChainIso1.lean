import LeanCheck.ChainPrecompact

/-!
# Isomorphism classification of the modular families (TVGQ-v7, Theorem `isomorphism-v3` and its corollary)

For nonzero `f, g : ℝ →+ ℚ` and `ℚ`-subspaces `S, T` of `ℝ` let `F(f,S) = { f_a : a ∈ S }` (`Fset`) and
`F(g, cT) = { g_{ca} : a ∈ T }` (`FsetScaled`).  For each of the two modular constructions `η ∈ {β, σ}`:

* **rigidity** (`rigidity_beta`, `rigidity_sigma`): every continuous additive map `L : (ℝ,η_{f,S}) → (ℝ,η_{g,T})` is `x ↦ c x`;
* for `c ≠ 0`, `m_c` is continuous iff `F(g,cT) ⊆ F(f,S)` (`scale_cont_beta_iff`, `scale_cont_sigma_iff`);
* an additive topological isomorphism exists iff `F(g,cT) = F(f,S)` for some `c ≠ 0`
  (`iso_iff_beta`, `iso_iff_sigma`), and then the continuous scalar rings agree.
-/

namespace LeanCheck

open Filter Topology

/-- `F(f,S) = { f_a : a ∈ S }`. -/
def Fset (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : Set (ℝ →+ ℚ) := {m | ∃ a ∈ S, m = fa f a}

/-- `F(g, cT) = { g_{ca} : a ∈ T }`. -/
def FsetScaled (g : ℝ →+ ℚ) (c : ℝ) (T : Submodule ℚ ℝ) : Set (ℝ →+ ℚ) := {m | ∃ a ∈ T, m = fa g (c * a)}

/-- The continuous scalar ring of a topology on `ℝ`. -/
def scalarCont (η : TopologicalSpace ℝ) : Set ℝ := {r | Continuous[η, η] (fun x : ℝ => r * x)}

/-- An additive isomorphism of `ℝ` that is a homeomorphism for the two topologies. -/
def IsoTop (η₁ η₂ : TopologicalSpace ℝ) : Prop :=
  ∃ L : ℝ ≃+ ℝ, Continuous[η₁, η₂] L ∧ Continuous[η₂, η₁] L.symm

/-! ### Elementary lemmas -/

lemma additive_int_zero (h : ℝ →+ ℝ) (hint : ∀ x, ∃ k : ℤ, h x = k) : ∀ x, h x = 0 := by
  intro x
  apply int_of_all_div
  intro n hn
  obtain ⟨k, hk⟩ := hint (x / n)
  refine ⟨k, ?_⟩
  have : h x = n * h (x / n) := by
    rw [← nsmul_eq_mul, ← map_nsmul]; congr 1
    rw [nsmul_eq_mul]; field_simp
  rw [this, hk]
  field_simp

lemma pform (f : ℝ →+ ℚ) (L : ℝ →+ ℝ) (d a : ℝ)
    (h : ∀ x, ((L x : ℝ) : Circ) = chiH f d a x) : ∀ x, L x = d * x + f (a * x) := by
  let H : ℝ →+ ℝ := L - AddMonoidHom.mulLeft d - faR f a
  have hH : ∀ x, ∃ k : ℤ, H x = k := by
    intro x
    have h0 : (((L x - (d * x + ((f (a * x) : ℚ) : ℝ))) : ℝ) : Circ) = 0 := by
      rw [AddCircle.coe_sub, h x, chiH, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h0
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one] at hk
    simp only [H, AddMonoidHom.sub_apply, AddMonoidHom.coe_mulLeft, faR_apply]
    linarith
  intro x
  have := additive_int_zero H hH x
  simp only [H, AddMonoidHom.sub_apply, AddMonoidHom.coe_mulLeft, faR_apply] at this
  linarith

/-- A real-multiple of the identity with rational values is zero. -/
lemma mul_rat_zero (d : ℝ) (h : ∀ x : ℝ, ∃ q : ℚ, d * x = q) : d = 0 := by
  by_contra hd
  apply Cardinal.not_countable_real
  have : (Set.univ : Set ℝ) ⊆ Set.range (fun q : ℚ => (q : ℝ) / d) := by
    intro t _
    obtain ⟨q, hq⟩ := h t
    refine ⟨q, ?_⟩
    show (q : ℝ) / d = t
    rw [← hq]; field_simp
  exact (Set.countable_range _).mono this

/-! ### Rigidity -/

lemma rigidity_abstract (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (ηs ηt : TopologicalSpace ℝ)
    (hdual : ∀ χ : Chars, @Continuous ℝ Circ ηs circTop χ ↔
      ∃ (c a : ℝ), a ∈ S ∧ ∀ x : ℝ, χ x = chiH f c a x)
    (hchar : ∀ r : ℝ, @Continuous ℝ Circ ηt circTop (cmulHom r))
    (L : ℝ →+ ℝ) (hL : Continuous[ηs, ηt] L) : ∃ c : ℝ, ∀ x, L x = c * x := by
  have hform : ∀ M : ℝ →+ ℝ, Continuous[ηs, ηt] M → ∀ r : ℝ, ∃ (e b : ℝ), ∀ x, r * M x = e * x + f (b * x) := by
    intro M hM r
    have hc : @Continuous ℝ Circ ηs circTop ((cmulHom r).comp M) :=
      @Continuous.comp ℝ ℝ Circ ηs ηt circTop (M : ℝ → ℝ) (cmulHom r) (hchar r) hM
    obtain ⟨e, b, -, hb⟩ := (hdual _).1 hc
    refine ⟨e, b, ?_⟩
    have := pform f ((AddMonoidHom.mulLeft r).comp M) e b (fun x => by
      have := hb x
      simpa [cmulHom_apply] using this)
    intro x
    simpa using this x
  obtain ⟨d, a, ha⟩ := hform L hL 1
  obtain ⟨e, b, hb⟩ := hform L hL (Real.sqrt 2)
  have ha' : ∀ x, L x = d * x + f (a * x) := fun x => by simpa using ha x
  have key : ∀ x, (Real.sqrt 2 * d - e) * x = (f (b * x) : ℝ) - Real.sqrt 2 * (f (a * x) : ℝ) := by
    intro x
    have h1 := hb x
    rw [ha' x] at h1
    linarith
  have hke : Real.sqrt 2 * d - e = 0 := by
    by_contra hne
    apply Cardinal.not_countable_real
    have : (Set.univ : Set ℝ) ⊆ Set.range (fun p : ℚ × ℚ => (p.1 : ℝ) - Real.sqrt 2 * p.2) := by
      intro t _
      refine ⟨(f (b * (t / (Real.sqrt 2 * d - e))), f (a * (t / (Real.sqrt 2 * d - e)))), ?_⟩
      have := key (t / (Real.sqrt 2 * d - e))
      simp only
      rw [← this]; field_simp
    exact (Set.countable_range _).mono this
  have hfa : ∀ x, f (a * x) = 0 := by
    intro x
    by_contra hne
    have h2 := key x
    rw [hke, zero_mul] at h2
    apply irrational_sqrt_two
    refine ⟨f (b * x) / f (a * x), ?_⟩
    have hne' : ((f (a * x) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hne
    have h3 : ((f (b * x) : ℚ) : ℝ) = Real.sqrt 2 * (f (a * x) : ℝ) := by linarith
    rw [Rat.cast_div, h3]
    field_simp
  refine ⟨d, fun x => ?_⟩
  rw [ha' x, hfa x]; simp

theorem rigidity_beta (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (L : ℝ →+ ℝ)
    (hL : Continuous[betaT f S, betaT g T] L) : ∃ c : ℝ, ∀ x, L x = c * x :=
  rigidity_abstract f g S T (betaT f S) (betaT g T) (fun χ => dual_beta f S χ)
    (fun r => cmulHom_cont_beta g T r) L hL

theorem rigidity_sigma (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (L : ℝ →+ ℝ)
    (hL : Continuous[sigmaT f S, sigmaT g T] L) : ∃ c : ℝ, ∀ x, L x = c * x :=
  rigidity_abstract f g S T (sigmaT f S) (sigmaT g T) (fun χ => dual_sigma f S χ)
    (fun r => continuous_le_dom (sigmaT_le_betaT g T) (cmulHom_cont_beta g T r)) L hL

/-! ### Continuity of scalar maps -/

lemma scale_cont_target_beta (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (ηs : TopologicalSpace ℝ)
    (hηs : ηs ≤ betaT f S)
    (hdual : ∀ χ : Chars, @Continuous ℝ Circ ηs circTop χ ↔
      ∃ (c a : ℝ), a ∈ S ∧ ∀ x : ℝ, χ x = chiH f c a x) (c : ℝ) :
    Continuous[ηs, betaT g T] (fun x : ℝ => c * x) ↔
      ∀ a ∈ T, ∃ b ∈ S, fa g (c * a) = fa f b := by
  constructor
  · intro h a ha
    have hχ : @Continuous ℝ Circ ηs circTop ((pfHom g a).comp (AddMonoidHom.mulLeft c)) :=
      @Continuous.comp ℝ ℝ Circ ηs (betaT g T) circTop (fun x : ℝ => c * x) (pfHom g a)
        (pfHom_cont_beta g T ⟨a, ha⟩) h
    obtain ⟨d, b, hb, hform⟩ := (hdual _).1 hχ
    have hp := pform f (faR g (c * a)) d b (fun x => by
      have := hform x
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
        pfHom_apply] at this
      rw [faR_apply, show c * a * x = a * (c * x) by ring]
      exact this)
    have hd : d = 0 := mul_rat_zero d (fun x => ⟨g (c * a * x) - f (b * x), by
      have := hp x
      rw [faR_apply] at this
      push_cast
      linarith⟩)
    refine ⟨b, hb, ?_⟩
    ext x
    have := hp x
    rw [hd, zero_mul, zero_add, faR_apply] at this
    simp only [fa_apply]
    exact_mod_cast this
  · intro h
    have hbeta : Continuous[betaT f S, betaT g T] (fun x : ℝ => c * x) := by
      have hB : Continuous[betaT f S, ⨅ b : ℝ, TopologicalSpace.induced
          (fun x : ℝ => ((b * x : ℝ) : Circ)) circTop] (fun x : ℝ => c * x) := by
        refine continuous_iInf_rng.2 (fun b => continuous_induced_rng.2 ?_)
        have : ((fun x : ℝ => ((b * x : ℝ) : Circ)) ∘ fun x : ℝ => c * x) = cmulHom (b * c) := by
          funext x; simp only [Function.comp, cmulHom_apply]; rw [mul_assoc]
        rw [this]
        exact cmulHom_cont_beta f S (b * c)
      have hA : Continuous[betaT f S, ⨅ a : T, TopologicalSpace.induced
          (fun x : ℝ => (((g ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop] (fun x : ℝ => c * x) := by
        refine continuous_iInf_rng.2 (fun a => continuous_induced_rng.2 ?_)
        obtain ⟨b, hb, hab⟩ := h (a : ℝ) a.2
        have : ((fun x : ℝ => (((g ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) ∘ fun x : ℝ => c * x) =
            pfHom f b := by
          funext x
          simp only [Function.comp, pfHom_apply]
          have := congrArg (fun m : ℝ →+ ℚ => m x) hab
          simp only [fa_apply] at this
          rw [show (a : ℝ) * (c * x) = c * a * x by ring, this]
        rw [this]
        exact pfHom_cont_beta f S ⟨b, hb⟩
      exact (continuous_inf_rng (t₁ := betaT f S)).2 ⟨hB, hA⟩
    exact continuous_le_dom hηs hbeta

theorem scale_cont_beta_iff (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (c : ℝ) :
    Continuous[betaT f S, betaT g T] (fun x : ℝ => c * x) ↔ FsetScaled g c T ⊆ Fset f S := by
  rw [scale_cont_target_beta f g S T (betaT f S) le_rfl (fun χ => dual_beta f S χ) c]
  constructor
  · rintro h m ⟨a, ha, rfl⟩
    obtain ⟨b, hb, e⟩ := h a ha
    exact ⟨b, hb, e⟩
  · intro h a ha
    obtain ⟨b, hb, e⟩ := h ⟨a, ha, rfl⟩
    exact ⟨b, hb, e⟩

theorem scale_cont_sigma_iff (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (c : ℝ) :
    Continuous[sigmaT f S, sigmaT g T] (fun x : ℝ => c * x) ↔ FsetScaled g c T ⊆ Fset f S := by
  have e : sigmaT g T = (inferInstance : TopologicalSpace ℝ) ⊓ betaT g T := sigmaT_eq g T
  constructor
  · intro h
    have h' : Continuous[sigmaT f S, betaT g T] (fun x : ℝ => c * x) := by
      rw [e] at h
      exact ((continuous_inf_rng (t₁ := sigmaT f S) (t₂ := (inferInstance : TopologicalSpace ℝ))
        (t₃ := betaT g T)).1 h).2
    rw [scale_cont_target_beta f g S T (sigmaT f S) (sigmaT_le_betaT f S)
      (fun χ => dual_sigma f S χ) c] at h'
    rintro m ⟨a, ha, rfl⟩
    obtain ⟨b, hb, e⟩ := h' a ha
    exact ⟨b, hb, e⟩
  · intro h
    have h' : Continuous[sigmaT f S, betaT g T] (fun x : ℝ => c * x) := by
      rw [scale_cont_target_beta f g S T (sigmaT f S) (sigmaT_le_betaT f S)
        (fun χ => dual_sigma f S χ) c]
      intro a ha
      obtain ⟨b, hb, e⟩ := h ⟨a, ha, rfl⟩
      exact ⟨b, hb, e⟩
    rw [e]
    exact (continuous_inf_rng (t₁ := sigmaT f S) (t₂ := (inferInstance : TopologicalSpace ℝ))
      (t₃ := betaT g T)).2 ⟨continuous_le_dom (sigmaT_le_usual f S) (continuous_const.mul continuous_id), h'⟩

/-! ### Isomorphism criterion -/

lemma fscaled_sub_inv (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (c : ℝ) (hc : c ≠ 0)
    (h : FsetScaled g c T = Fset f S) : FsetScaled f c⁻¹ S ⊆ Fset g T := by
  rintro m ⟨b, hb, rfl⟩
  have hm : fa f b ∈ Fset f S := ⟨b, hb, rfl⟩
  rw [← h] at hm
  obtain ⟨a, ha, e⟩ := hm
  refine ⟨a, ha, ?_⟩
  ext x
  have := congrArg (fun m : ℝ →+ ℚ => m (c⁻¹ * x)) e
  simp only [fa_apply] at this ⊢
  rw [show c⁻¹ * b * x = b * (c⁻¹ * x) by ring, this]
  congr 1
  field_simp

lemma fscaled_fwd (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (c : ℝ) (hc : c ≠ 0)
    (h : FsetScaled g c T ⊆ Fset f S) (h' : FsetScaled f c⁻¹ S ⊆ Fset g T) :
    FsetScaled g c T = Fset f S := by
  refine Set.Subset.antisymm h ?_
  rintro m ⟨b, hb, rfl⟩
  obtain ⟨a, ha, e⟩ := h' ⟨b, hb, rfl⟩
  refine ⟨a, ha, ?_⟩
  ext x
  have := congrArg (fun m : ℝ →+ ℚ => m (c * x)) e
  simp only [fa_apply] at this ⊢
  rw [show c * a * x = a * (c * x) by ring, ← this]
  congr 1
  field_simp

lemma iso_iff_of (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (ηs ηt : TopologicalSpace ℝ)
    (hrs : ∀ L : ℝ →+ ℝ, Continuous[ηs, ηt] L → ∃ c : ℝ, ∀ x, L x = c * x)
    (hrt : ∀ L : ℝ →+ ℝ, Continuous[ηt, ηs] L → ∃ c : ℝ, ∀ x, L x = c * x)
    (hs : ∀ c : ℝ, Continuous[ηs, ηt] (fun x : ℝ => c * x) ↔ FsetScaled g c T ⊆ Fset f S)
    (ht : ∀ c : ℝ, Continuous[ηt, ηs] (fun x : ℝ => c * x) ↔ FsetScaled f c S ⊆ Fset g T) :
    IsoTop ηs ηt ↔ ∃ c : ℝ, c ≠ 0 ∧ FsetScaled g c T = Fset f S := by
  constructor
  · rintro ⟨L, h1, h2⟩
    obtain ⟨c, hc⟩ := hrs (L : ℝ →+ ℝ) h1
    obtain ⟨c', hc'⟩ := hrt (L.symm : ℝ →+ ℝ) h2
    have hcc : c * c' = 1 := by
      have := L.apply_symm_apply (1 : ℝ)
      have e1 : L.symm 1 = c' * 1 := hc' 1
      have e2 : L (L.symm 1) = c * L.symm 1 := hc _
      rw [e2, e1] at this
      linarith
    have hc0 : c ≠ 0 := fun h0 => by rw [h0] at hcc; simp at hcc
    have hc'e : c' = c⁻¹ := by field_simp; linarith
    have h1' : Continuous[ηs, ηt] (fun x : ℝ => c * x) := by
      have : (fun x : ℝ => c * x) = ⇑L := funext fun x => (hc x).symm
      rw [this]; exact h1
    have h2' : Continuous[ηt, ηs] (fun x : ℝ => c⁻¹ * x) := by
      have : (fun x : ℝ => c⁻¹ * x) = ⇑L.symm := funext fun x => by rw [← hc'e]; exact (hc' x).symm
      rw [this]; exact h2
    exact ⟨c, hc0, fscaled_fwd f g S T c hc0 ((hs c).1 h1') ((ht c⁻¹).1 h2')⟩
  · rintro ⟨c, hc, h⟩
    refine ⟨{ toFun := fun x => c * x, invFun := fun x => c⁻¹ * x,
              left_inv := fun x => by field_simp, right_inv := fun x => by field_simp,
              map_add' := fun x y => by ring }, ?_, ?_⟩
    · exact (hs c).2 (h ▸ Set.Subset.refl _)
    · exact (ht c⁻¹).2 (fscaled_sub_inv f g S T c hc h)

theorem iso_iff_beta (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) :
    IsoTop (betaT f S) (betaT g T) ↔ ∃ c : ℝ, c ≠ 0 ∧ FsetScaled g c T = Fset f S :=
  iso_iff_of f g S T _ _ (rigidity_beta f g S T) (rigidity_beta g f T S)
    (scale_cont_beta_iff f g S T) (scale_cont_beta_iff g f T S)

theorem iso_iff_sigma (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) :
    IsoTop (sigmaT f S) (sigmaT g T) ↔ ∃ c : ℝ, c ≠ 0 ∧ FsetScaled g c T = Fset f S :=
  iso_iff_of f g S T _ _ (rigidity_sigma f g S T) (rigidity_sigma g f T S)
    (scale_cont_sigma_iff f g S T) (scale_cont_sigma_iff g f T S)

end LeanCheck
