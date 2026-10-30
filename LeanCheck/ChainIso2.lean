import LeanCheck.ChainIso1

/-!
# Isomorphism classification, part 2: consequences for the modular families

Consequences of the exact isomorphism criterion `iso_iff_beta` / `iso_iff_sigma`:

* every additive isomorphism of the families is a scalar map, so the continuous scalar ring is an invariant;
* distinct subalgebras used as parameter spaces give non-isomorphic groups;
* for fixed `f ≠ 0`: `(ℝ, η_{f,S}) ≅ (ℝ, η_{f,T})` iff `S = c T` for some `c ≠ 0`;
* for `S = T = ℚ`: the criterion is `g (c x) = r f x`, with `c ≠ 0`, `r ∈ ℚ \ {0}`;
* `β_{f,S}` and `σ_{g,T}` are never isomorphic (precompact versus not).
-/

namespace LeanCheck

open Filter Topology

/-! ### Elementary facts about `f ≠ 0` -/

lemma exists_unit (f : ℝ →+ ℚ) (hf : f ≠ 0) : ∃ u : ℝ, f u = 1 := by
  by_contra hno
  push_neg at hno
  apply hf
  ext x
  by_contra hx
  have hx' : f x ≠ 0 := hx
  apply hno (((f x)⁻¹ : ℚ) * x)
  rw [f_ratmul]
  exact inv_mul_cancel₀ hx'

lemma fa_inj (f : ℝ →+ ℚ) (hf : f ≠ 0) (a b : ℝ) (h : fa f a = fa f b) : a = b := by
  by_contra hab
  have hd : a - b ≠ 0 := sub_ne_zero.2 hab
  obtain ⟨u, hu⟩ := exists_unit f hf
  have := congrArg (fun m : ℝ →+ ℚ => m (u / (a - b))) h
  simp only [fa_apply] at this
  have h2 : f ((a - b) * (u / (a - b))) = 0 := by
    rw [sub_mul, map_sub, this, sub_self]
  rw [mul_div_cancel₀ _ hd, hu] at h2
  exact one_ne_zero h2

/-! ### Scalar-ring invariance -/

lemma scalarCont_subset_of_scale (ηs ηt : TopologicalSpace ℝ) (c : ℝ) (hc : c ≠ 0)
    (h1 : Continuous[ηs, ηt] (fun x : ℝ => c * x))
    (h2 : Continuous[ηt, ηs] (fun x : ℝ => c⁻¹ * x)) :
    scalarCont ηs ⊆ scalarCont ηt := by
  intro r hr
  have hin : Continuous[ηt, ηs] (fun x : ℝ => r * (c⁻¹ * x)) :=
    @Continuous.comp ℝ ℝ ℝ ηt ηs ηs (fun x : ℝ => c⁻¹ * x) (fun x : ℝ => r * x) hr h2
  have hout : Continuous[ηt, ηt] (fun x : ℝ => c * (r * (c⁻¹ * x))) :=
    @Continuous.comp ℝ ℝ ℝ ηt ηs ηt (fun x : ℝ => r * (c⁻¹ * x)) (fun x : ℝ => c * x) h1 hin
  have e : (fun x : ℝ => c * (r * (c⁻¹ * x))) = fun x : ℝ => r * x := by
    funext x; field_simp
  rw [e] at hout
  exact hout

lemma iso_scalar_form (ηs ηt : TopologicalSpace ℝ)
    (hrs : ∀ L : ℝ →+ ℝ, Continuous[ηs, ηt] L → ∃ c : ℝ, ∀ x, L x = c * x)
    (hrt : ∀ L : ℝ →+ ℝ, Continuous[ηt, ηs] L → ∃ c : ℝ, ∀ x, L x = c * x)
    (h : IsoTop ηs ηt) :
    ∃ c : ℝ, c ≠ 0 ∧ Continuous[ηs, ηt] (fun x : ℝ => c * x) ∧
      Continuous[ηt, ηs] (fun x : ℝ => c⁻¹ * x) := by
  obtain ⟨L, h1, h2⟩ := h
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
  refine ⟨c, hc0, ?_, ?_⟩
  · have : (fun x : ℝ => c * x) = ⇑L := funext fun x => (hc x).symm
    rw [this]; exact h1
  · have : (fun x : ℝ => c⁻¹ * x) = ⇑L.symm := funext fun x => by rw [← hc'e]; exact (hc' x).symm
    rw [this]; exact h2

lemma scalarCont_eq_of_iso (ηs ηt : TopologicalSpace ℝ)
    (hrs : ∀ L : ℝ →+ ℝ, Continuous[ηs, ηt] L → ∃ c : ℝ, ∀ x, L x = c * x)
    (hrt : ∀ L : ℝ →+ ℝ, Continuous[ηt, ηs] L → ∃ c : ℝ, ∀ x, L x = c * x)
    (h : IsoTop ηs ηt) : scalarCont ηs = scalarCont ηt := by
  obtain ⟨c, hc, h1, h2⟩ := iso_scalar_form ηs ηt hrs hrt h
  refine Set.Subset.antisymm (scalarCont_subset_of_scale ηs ηt c hc h1 h2) ?_
  have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
  have h2' : Continuous[ηs, ηt] (fun x : ℝ => (c⁻¹)⁻¹ * x) := by rw [inv_inv]; exact h1
  exact scalarCont_subset_of_scale ηt ηs c⁻¹ hc' h2 h2'

/-- The continuous scalar ring of a modular `β` topology is invariant under additive isomorphism. -/
theorem scalarCont_eq_of_iso_beta (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ)
    (h : IsoTop (betaT f S) (betaT g T)) : scalarCont (betaT f S) = scalarCont (betaT g T) :=
  scalarCont_eq_of_iso _ _ (rigidity_beta f g S T) (rigidity_beta g f T S) h

theorem scalarCont_eq_of_iso_sigma (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ)
    (h : IsoTop (sigmaT f S) (sigmaT g T)) : scalarCont (sigmaT f S) = scalarCont (sigmaT g T) :=
  scalarCont_eq_of_iso _ _ (rigidity_sigma f g S T) (rigidity_sigma g f T S) h

lemma scalarCont_beta_alg (f : ℝ →+ ℚ) (hf : f ≠ 0) (A : Subalgebra ℚ ℝ) :
    scalarCont (betaT f (Subalgebra.toSubmodule A)) = (A : Set ℝ) := by
  obtain ⟨u, hu⟩ := exists_unit f hf
  ext r
  show Continuous[betaT f (Subalgebra.toSubmodule A), betaT f (Subalgebra.toSubmodule A)]
      (fun x : ℝ => r * x) ↔ r ∈ (A : Set ℝ)
  rw [scalar_beta f u hu _ r, scalarRing_algebra]

lemma scalarCont_sigma_alg (f : ℝ →+ ℚ) (hf : f ≠ 0) (A : Subalgebra ℚ ℝ) :
    scalarCont (sigmaT f (Subalgebra.toSubmodule A)) = (A : Set ℝ) := by
  obtain ⟨u, hu⟩ := exists_unit f hf
  ext r
  show Continuous[sigmaT f (Subalgebra.toSubmodule A), sigmaT f (Subalgebra.toSubmodule A)]
      (fun x : ℝ => r * x) ↔ r ∈ (A : Set ℝ)
  rw [scalar_sigma f u hu _ r, scalarRing_algebra]

/-- Distinct subalgebras (in particular intermediate fields) as parameter spaces give
non-isomorphic groups, whatever the nonzero functionals. -/
theorem iso_algebra_beta (f g : ℝ →+ ℚ) (hf : f ≠ 0) (hg : g ≠ 0) (A A' : Subalgebra ℚ ℝ)
    (h : IsoTop (betaT f (Subalgebra.toSubmodule A)) (betaT g (Subalgebra.toSubmodule A'))) :
    A = A' := by
  have := scalarCont_eq_of_iso_beta f g _ _ h
  rw [scalarCont_beta_alg f hf, scalarCont_beta_alg g hg] at this
  exact SetLike.coe_injective this

theorem iso_algebra_sigma (f g : ℝ →+ ℚ) (hf : f ≠ 0) (hg : g ≠ 0) (A A' : Subalgebra ℚ ℝ)
    (h : IsoTop (sigmaT f (Subalgebra.toSubmodule A)) (sigmaT g (Subalgebra.toSubmodule A'))) :
    A = A' := by
  have := scalarCont_eq_of_iso_sigma f g _ _ h
  rw [scalarCont_sigma_alg f hf, scalarCont_sigma_alg g hg] at this
  exact SetLike.coe_injective this

/-! ### Fixed functional: `S = c T` -/

lemma fscaled_eq_iff (f : ℝ →+ ℚ) (hf : f ≠ 0) (S T : Submodule ℚ ℝ) (c : ℝ) :
    FsetScaled f c T = Fset f S ↔ ∀ y : ℝ, y ∈ S ↔ ∃ a ∈ T, y = c * a := by
  constructor
  · intro h y
    constructor
    · intro hy
      have hm : fa f y ∈ Fset f S := ⟨y, hy, rfl⟩
      rw [← h] at hm
      obtain ⟨a, ha, e⟩ := hm
      exact ⟨a, ha, fa_inj f hf _ _ e⟩
    · rintro ⟨a, ha, rfl⟩
      have hm : fa f (c * a) ∈ FsetScaled f c T := ⟨a, ha, rfl⟩
      rw [h] at hm
      obtain ⟨b, hb, e⟩ := hm
      rw [fa_inj f hf _ _ e]; exact hb
  · intro h
    ext m
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨c * a, (h _).2 ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, ha, rfl⟩ := (h b).1 hb
      exact ⟨a, ha, rfl⟩

theorem iso_fixed_beta (f : ℝ →+ ℚ) (hf : f ≠ 0) (S T : Submodule ℚ ℝ) :
    IsoTop (betaT f S) (betaT f T) ↔
      ∃ c : ℝ, c ≠ 0 ∧ ∀ y : ℝ, y ∈ S ↔ ∃ a ∈ T, y = c * a := by
  rw [iso_iff_beta]
  exact exists_congr fun c => and_congr_right fun _ => fscaled_eq_iff f hf S T c

theorem iso_fixed_sigma (f : ℝ →+ ℚ) (hf : f ≠ 0) (S T : Submodule ℚ ℝ) :
    IsoTop (sigmaT f S) (sigmaT f T) ↔
      ∃ c : ℝ, c ≠ 0 ∧ ∀ y : ℝ, y ∈ S ↔ ∃ a ∈ T, y = c * a := by
  rw [iso_iff_sigma]
  exact exists_congr fun c => and_congr_right fun _ => fscaled_eq_iff f hf S T c

/-! ### The rational parameter space -/

/-- The rational parameter space `ℚ ⊆ ℝ`. -/
noncomputable def ratSub : Submodule ℚ ℝ := Submodule.span ℚ {(1 : ℝ)}

lemma mem_ratSub (a : ℝ) : a ∈ ratSub ↔ ∃ q : ℚ, a = q := by
  unfold ratSub
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, by simp [Rat.smul_def]⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, by simp [Rat.smul_def]⟩

lemma fscaled_Q_iff (f g : ℝ →+ ℚ) (hf : f ≠ 0) (c : ℝ) :
    FsetScaled g c ratSub = Fset f ratSub ↔ ∃ r : ℚ, r ≠ 0 ∧ ∀ x : ℝ, g (c * x) = r * f x := by
  constructor
  · intro h
    have hm : fa f 1 ∈ Fset f ratSub := ⟨1, (mem_ratSub 1).2 ⟨1, by simp⟩, rfl⟩
    rw [← h] at hm
    obtain ⟨a, ha, e⟩ := hm
    obtain ⟨q, rfl⟩ := (mem_ratSub a).1 ha
    have hq : q ≠ 0 := by
      rintro rfl
      apply hf
      ext x
      have := congrArg (fun m : ℝ →+ ℚ => m x) e
      simp only [fa_apply] at this
      simpa using this
    refine ⟨q⁻¹, inv_ne_zero hq, fun x => ?_⟩
    have h1 := congrArg (fun m : ℝ →+ ℚ => m x) e
    simp only [fa_apply, one_mul] at h1
    have h2 : g (c * (q : ℝ) * x) = q * g (c * x) := by
      rw [show c * (q : ℝ) * x = (q : ℝ) * (c * x) by ring, f_ratmul]
    rw [h2] at h1
    rw [h1]
    field_simp
  · rintro ⟨r, hr, h⟩
    ext m
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨q, rfl⟩ := (mem_ratSub a).1 ha
      refine ⟨((q * r : ℚ) : ℝ), (mem_ratSub _).2 ⟨_, rfl⟩, ?_⟩
      ext x
      simp only [fa_apply]
      rw [show c * (q : ℝ) * x = (q : ℝ) * (c * x) by ring, f_ratmul g q (c * x), h,
        f_ratmul f (q * r) x]
      ring
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨q, rfl⟩ := (mem_ratSub b).1 hb
      refine ⟨((q / r : ℚ) : ℝ), (mem_ratSub _).2 ⟨_, rfl⟩, ?_⟩
      ext x
      simp only [fa_apply]
      rw [show c * ((q / r : ℚ) : ℝ) * x = ((q / r : ℚ) : ℝ) * (c * x) by ring,
        f_ratmul g (q / r) (c * x), h, f_ratmul f q x]
      field_simp

theorem iso_Q_beta (f g : ℝ →+ ℚ) (hf : f ≠ 0) :
    IsoTop (betaT f ratSub) (betaT g ratSub) ↔
      ∃ c : ℝ, c ≠ 0 ∧ ∃ r : ℚ, r ≠ 0 ∧ ∀ x : ℝ, g (c * x) = r * f x := by
  rw [iso_iff_beta]
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨r, hr, hh⟩ := (fscaled_Q_iff f g hf c).1 h
    exact ⟨c, hc, r, hr, hh⟩
  · rintro ⟨c, hc, r, hr, hh⟩
    exact ⟨c, hc, (fscaled_Q_iff f g hf c).2 ⟨r, hr, hh⟩⟩

theorem iso_Q_sigma (f g : ℝ →+ ℚ) (hf : f ≠ 0) :
    IsoTop (sigmaT f ratSub) (sigmaT g ratSub) ↔
      ∃ c : ℝ, c ≠ 0 ∧ ∃ r : ℚ, r ≠ 0 ∧ ∀ x : ℝ, g (c * x) = r * f x := by
  rw [iso_iff_sigma]
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨r, hr, hh⟩ := (fscaled_Q_iff f g hf c).1 h
    exact ⟨c, hc, r, hr, hh⟩
  · rintro ⟨c, hc, r, hr, hh⟩
    exact ⟨c, hc, (fscaled_Q_iff f g hf c).2 ⟨r, hr, hh⟩⟩

/-! ### `β` and `σ` are never isomorphic -/

lemma Ioo_nhds_uR : Set.Ioo (-1 : ℝ) 1 ∈ @nhds ℝ uR 0 := by
  unfold uR
  exact Ioo_mem_nhds (by norm_num) (by norm_num)

/-- A precompact group topology has no continuous additive surjection onto the usual real line. -/
lemma no_cont_surj_usual (η : TopologicalSpace ℝ) (hη : Precompact η) (L : ℝ →+ ℝ)
    (hL : Continuous[η, uR] L) (hs : Function.Surjective L) : False := by
  have hc : @ContinuousAt ℝ ℝ η uR L 0 := @Continuous.continuousAt ℝ ℝ η uR L 0 hL
  have hU : Set.Ioo (-1 : ℝ) 1 ∈ @nhds ℝ uR (L 0) := by rw [map_zero]; exact Ioo_nhds_uR
  have hpre : L ⁻¹' Set.Ioo (-1 : ℝ) 1 ∈ @nhds ℝ η 0 :=
    @ContinuousAt.preimage_mem_nhds ℝ ℝ η uR L 0 _ hc hU
  obtain ⟨F, hF⟩ := hη _ hpre
  obtain ⟨x, hx⟩ := hs (F.sum (fun t => |L t|) + 1)
  obtain ⟨t, htF, ht⟩ := hF x
  have h1 : |L (x - t)| < 1 := by
    have := ht
    simp only [Set.mem_preimage, Set.mem_Ioo] at this
    exact abs_lt.2 this
  rw [map_sub, hx] at h1
  have h2 : |L t| ≤ F.sum (fun t => |L t|) :=
    Finset.single_le_sum (f := fun t => |L t|) (fun _ _ => abs_nonneg _) htF
  have h4 : 0 ≤ F.sum (fun t => |L t|) := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h3 := abs_sub_abs_le_abs_sub (F.sum (fun t => |L t|) + 1) (L t)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ F.sum (fun t => |L t|) + 1)] at h3
  have h5 : |L t| < F.sum (fun t => |L t|) + 1 := by linarith [abs_lt.1 h1]
  linarith [le_abs_self (L t), neg_abs_le (L t), abs_lt.1 h1]

theorem beta_precompact (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : Precompact (betaT f S) := by
  rw [betaT_eq_theta]; exact theta_precompact _

theorem not_iso_beta_sigma (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) :
    ¬ IsoTop (betaT f S) (sigmaT g T) := by
  rintro ⟨L, h1, _⟩
  exact no_cont_surj_usual (betaT f S) (beta_precompact f S) (L : ℝ →+ ℝ)
    (continuous_le_rng (sigmaT_le_usual g T) h1) L.surjective

theorem not_iso_sigma_beta (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) :
    ¬ IsoTop (sigmaT f S) (betaT g T) := by
  rintro ⟨L, _, h2⟩
  exact no_cont_surj_usual (betaT g T) (beta_precompact g T) (L.symm : ℝ →+ ℝ)
    (continuous_le_rng (sigmaT_le_usual f S) h2) L.symm.surjective

end LeanCheck
