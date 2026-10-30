import LeanCheck.ChainIso2

/-!
# Isomorphism classification, part 3: continuous maps on `τ_{f,S}`
(TVGQ-v7, Section `tauiso`: Lemma `tauiso:maps`, Theorem `tauiso:hom`)

* real-valued continuous additive maps on `(ℝ, τ_{f,S})` are exactly `c x + ∑ d_j f(b_j x)`, `b_j ∈ S`;
* rational-valued ones are exactly `Fset f S`;
* an additive `L : (ℝ, τ_{f,S}) → (ℝ, τ_{g,T})` is continuous iff it has that form and, for `c ≠ 0`,
  `FsetScaled g c T ⊆ Fset f S` (the condition is automatic for `c = 0`).
-/

namespace LeanCheck

open Filter Topology

/-- The usual topology on `ℝ`, as a reducible name so that instances see through it. -/
abbrev uR' : TopologicalSpace ℝ := inferInstance

/-! ### Rational-valued continuous maps -/

theorem rat_dual_tau (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (h : ℝ →+ ℚ)
    (hcont : Continuous[tauT f S, uR'] (fun x : ℝ => ((h x : ℚ) : ℝ))) :
    ∃ a ∈ S, h = fa f a := by
  classical
  obtain ⟨c, κ, hκ, b, d, hbS, hli, hform⟩ :=
    dual_tau_real f S ((Rat.castHom ℝ).toAddMonoidHom.comp h) hcont
  have hform' : ∀ x : ℝ, ((h x : ℚ) : ℝ) = c * x + ∑ j, d j * ((f (b j * x) : ℚ) : ℝ) := hform
  have hc : c = 0 := by
    by_contra hc
    apply HkerG_not_countable (fun j => fa f (b j))
    refine (Set.countable_range (fun q : ℚ => (q : ℝ) / c)).mono ?_
    intro x hx
    refine ⟨h x, ?_⟩
    have hx' : ∀ j, f (b j * x) = 0 := fun j => by
      have := congrFun (AddMonoidHom.mem_ker.mp hx) j
      simpa [HmapG_apply, fa_apply] using this
    have := hform' x
    simp only [hx', Rat.cast_zero, mul_zero, Finset.sum_const_zero, add_zero] at this
    field_simp
    linarith
  subst hc
  choose xs hxs using fun j : κ => Hmap_surj f b hli (Pi.single j (1 : ℚ))
  have hd : ∀ i, d i = ((h (xs i) : ℚ) : ℝ) := by
    intro i
    have := hform' (xs i)
    have hb : ∀ j, f (b j * xs i) = (Pi.single i (1 : ℚ) : κ → ℚ) j := fun j => by
      have := congrFun (hxs i) j
      simpa [Hmap_apply] using this
    simp only [hb, zero_mul, zero_add] at this
    rw [this, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  set q : κ → ℚ := fun i => h (xs i) with hq
  have hfx : ∀ x : ℝ, h x = ∑ j, q j * f (b j * x) := by
    intro x
    have := hform' x
    simp only [zero_mul, zero_add, hd] at this
    exact_mod_cast this
  have hfa : ∀ x : ℝ, f ((∑ j, ((q j : ℚ) : ℝ) * b j) * x) = ∑ j, q j * f (b j * x) := by
    intro x
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_assoc, f_ratmul]
  have hmem : (∑ j, ((q j : ℚ) : ℝ) * b j) ∈ S := by
    refine S.sum_mem (fun j _ => ?_)
    have := S.smul_mem (q j) (hbS j)
    simpa [Rat.smul_def] using this
  refine ⟨_, hmem, ?_⟩
  ext x
  rw [fa_apply, hfa]
  exact hfx x

/-! ### Real-valued continuous maps -/

lemma tau_form_cont (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (c : ℝ) {κ : Type} [Fintype κ]
    (b d : κ → ℝ) (hb : ∀ j, b j ∈ S) :
    Continuous[tauT f S, uR'] (fun x : ℝ => c * x + ∑ j, d j * ((f (b j * x) : ℚ) : ℝ)) := by
  have h1 : Continuous[tauT f S, uR'] (fun x : ℝ => c * x) :=
    continuous_le_dom (TfS_le_usual f S usualQ) (continuous_const.mul continuous_id)
  have h2 : ∀ j, Continuous[tauT f S, uR'] (fun x : ℝ => d j * ((f (b j * x) : ℚ) : ℝ)) := fun j =>
    @Continuous.comp ℝ ℝ ℝ (tauT f S) uR' uR' (faR f (b j)) (fun y : ℝ => d j * y)
      (continuous_const.mul continuous_id) (faR_cont_tau f S (b j) (hb j))
  have h3 : Continuous[tauT f S, uR'] (fun x : ℝ => ∑ j, d j * ((f (b j * x) : ℚ) : ℝ)) :=
    @continuous_finsetSum κ ℝ ℝ (tauT f S) uR' _ _ (fun j x => d j * ((f (b j * x) : ℚ) : ℝ))
      Finset.univ (fun j _ => h2 j)
  exact @Continuous.add ℝ uR' _ _ ℝ (tauT f S) _ _ h1 h3

/-- **Real-valued duals of `τ_{f,S}`** (TVGQ-v7 Lemma `tauiso:maps`, first half). -/
theorem tau_real_iff (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (h : ℝ →+ ℝ) :
    Continuous[tauT f S, uR'] h ↔
      ∃ (c : ℝ) (κ : Type) (_ : Fintype κ) (b d : κ → ℝ), (∀ j, b j ∈ S) ∧
        ∀ x : ℝ, h x = c * x + ∑ j, d j * ((f (b j * x) : ℚ) : ℝ) := by
  constructor
  · intro hc
    obtain ⟨c, κ, hκ, b, d, hbS, -, hform⟩ := dual_tau_real f S h hc
    exact ⟨c, κ, hκ, b, d, hbS, hform⟩
  · rintro ⟨c, κ, hκ, b, d, hbS, hform⟩
    have : (h : ℝ → ℝ) = fun x => c * x + ∑ j, d j * ((f (b j * x) : ℚ) : ℝ) := funext hform
    rw [this]
    exact tau_form_cont f S c b d hbS

/-- **Rational-valued duals of `τ_{f,S}`** are exactly `{f_a : a ∈ S}`
(TVGQ-v7 Lemma `tauiso:maps`, second half). -/
theorem tau_rat_iff (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (h : ℝ →+ ℚ) :
    Continuous[tauT f S, uR'] (fun x : ℝ => ((h x : ℚ) : ℝ)) ↔ h ∈ Fset f S := by
  constructor
  · intro hc
    obtain ⟨a, ha, e⟩ := rat_dual_tau f S h hc
    exact ⟨a, ha, e⟩
  · rintro ⟨a, ha, rfl⟩
    exact faR_cont_tau f S a ha

/-! ### All continuous additive homomorphisms -/

lemma comp_form (f g : ℝ →+ ℚ) (a c : ℝ) {κ : Type} [Fintype κ] (b d : κ → ℝ) (x : ℝ) :
    g (a * (c * x + ∑ j, d j * ((f (b j * x) : ℚ) : ℝ))) =
      g (c * a * x) + ∑ j, g (a * d j) * f (b j * x) := by
  have : a * (c * x + ∑ j, d j * ((f (b j * x) : ℚ) : ℝ)) =
      c * a * x + ∑ j, ((f (b j * x) : ℚ) : ℝ) * (a * d j) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [this, map_add, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by rw [f_ratmul]; ring)

lemma fscaled_zero_sub (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) : FsetScaled g 0 T ⊆ Fset f S := by
  rintro m ⟨a, ha, rfl⟩
  refine ⟨0, S.zero_mem, ?_⟩
  ext x
  simp [fa_apply]

lemma sum_mem_param (S : Submodule ℚ ℝ) {κ : Type} [Fintype κ] (b : κ → ℝ) (hb : ∀ j, b j ∈ S)
    (q : κ → ℚ) : (∑ j, ((q j : ℚ) : ℝ) * b j) ∈ S := by
  refine S.sum_mem (fun j _ => ?_)
  have := S.smul_mem (q j) (hb j)
  simpa [Rat.smul_def] using this

theorem tau_hom_necessary (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (L : ℝ →+ ℝ) (c : ℝ)
    {κ : Type} [Fintype κ] (b d : κ → ℝ) (hb : ∀ j, b j ∈ S)
    (hL : ∀ x, L x = c * x + ∑ j, d j * ((f (b j * x) : ℚ) : ℝ))
    (hcont : Continuous[tauT f S, tauT g T] L) : FsetScaled g c T ⊆ Fset f S := by
  rintro m ⟨a, ha, rfl⟩
  let R : ℝ →+ ℚ := (fa g a).comp L
  have hR : Continuous[tauT f S, uR'] (fun x : ℝ => ((R x : ℚ) : ℝ)) :=
    @Continuous.comp ℝ ℝ ℝ (tauT f S) (tauT g T) uR' (fun x => L x) (faR g a)
      (faR_cont_tau g T a ha) hcont
  obtain ⟨e, he, hRe⟩ := rat_dual_tau f S R hR
  refine ⟨e - ∑ j, ((g (a * d j) : ℚ) : ℝ) * b j,
    S.sub_mem he (sum_mem_param S b hb _), ?_⟩
  ext x
  have h1 : g (a * L x) = f (e * x) := congrArg (fun m : ℝ →+ ℚ => m x) hRe
  rw [hL x, comp_form f g a c b d x] at h1
  have h2 : ∀ j, f (((g (a * d j) : ℚ) : ℝ) * b j * x) = g (a * d j) * f (b j * x) :=
    fun j => by rw [mul_assoc, f_ratmul]
  show g (c * a * x) = f ((e - ∑ j, ((g (a * d j) : ℚ) : ℝ) * b j) * x)
  rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
  simp only [h2]
  linarith

theorem tau_hom_sufficient (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (L : ℝ →+ ℝ) (c : ℝ)
    {κ : Type} [Fintype κ] (b d : κ → ℝ) (hb : ∀ j, b j ∈ S)
    (hL : ∀ x, L x = c * x + ∑ j, d j * ((f (b j * x) : ℚ) : ℝ))
    (hsub : FsetScaled g c T ⊆ Fset f S) : Continuous[tauT f S, tauT g T] L := by
  have hU : Continuous[tauT f S, uR'] L := (tau_real_iff f S L).2 ⟨c, κ, inferInstance, b, d, hb, hL⟩
  have hA : Continuous[tauT f S, ⨅ a : T, TopologicalSpace.induced (fa g (a : ℝ)) usualQ] L := by
    refine continuous_iInf_rng.2 (fun a => continuous_induced_rng.2 ?_)
    obtain ⟨e, he, hee⟩ := hsub ⟨(a : ℝ), a.2, rfl⟩
    have hmem := S.add_mem he (sum_mem_param S b hb (fun j => g ((a : ℝ) * d j)))
    have hfun : ((fa g (a : ℝ)) ∘ L : ℝ → ℚ) =
        ⇑(fa f (e + ∑ j, ((g ((a : ℝ) * d j) : ℚ) : ℝ) * b j)) := by
      funext x
      show g ((a : ℝ) * L x) = _
      rw [hL x, comp_form, fa_apply]
      have h1 : g (c * (a : ℝ) * x) = f (e * x) := congrArg (fun m : ℝ →+ ℚ => m x) hee
      rw [h1, add_mul, map_add, Finset.sum_mul, map_sum]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by rw [mul_assoc, f_ratmul])
    rw [hfun]
    exact faS_cont f S usualQ ⟨_, hmem⟩
  exact (continuous_inf_rng (t₁ := tauT f S)).2 ⟨hU, hA⟩

/-- **All continuous additive homomorphisms** `(ℝ, τ_{f,S}) → (ℝ, τ_{g,T})`
(TVGQ-v7 Theorem `tauiso:hom`). -/
theorem tau_hom_iff (f g : ℝ →+ ℚ) (S T : Submodule ℚ ℝ) (L : ℝ →+ ℝ) :
    Continuous[tauT f S, tauT g T] L ↔
      ∃ (c : ℝ) (κ : Type) (_ : Fintype κ) (b d : κ → ℝ), (∀ j, b j ∈ S) ∧
        (∀ x, L x = c * x + ∑ j, d j * ((f (b j * x) : ℚ) : ℝ)) ∧
        (c ≠ 0 → FsetScaled g c T ⊆ Fset f S) := by
  constructor
  · intro hcont
    have hU : Continuous[tauT f S, uR'] L := continuous_le_rng (TfS_le_usual g T usualQ) hcont
    obtain ⟨c, κ, hκ, b, d, hb, hL⟩ := (tau_real_iff f S L).1 hU
    exact ⟨c, κ, hκ, b, d, hb, hL, fun _ => tau_hom_necessary f g S T L c b d hb hL hcont⟩
  · rintro ⟨c, κ, hκ, b, d, hb, hL, hsub⟩
    refine tau_hom_sufficient f g S T L c b d hb hL ?_
    by_cases hc : c = 0
    · subst hc; exact fscaled_zero_sub f g S T
    · exact hsub hc

end LeanCheck
