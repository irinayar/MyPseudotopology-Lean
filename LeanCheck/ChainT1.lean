import LeanCheck.ChainX4

/-!
# The TVG paper (real parameters): lifts, total disconnectedness, and the lifts of characters
(HamelCharactersTVG_v18 Proposition 6.1, Lemma 6.2, Corollary 6.3, Corollary 10.4, Corollary 5.3)

All statements concern the topologies `β_f = betaT f ⊤`, `σ_f = sigmaT f ⊤`, `τ_f = tauT f ⊤` (the multiplier `a`
ranging over all of `ℝ`), for a nonzero rational-valued additive function `f`.
-/

namespace LeanCheck

open Filter Topology

/-! ### Lemma 6.2 : uniqueness of additive lifts -/

/-- **Lemma 6.2.**  If additive maps `g, h : ℝ → ℝ` have the same circle reductions, then `g = h`. -/
theorem lift_unique (g h : ℝ →+ ℝ) (hgh : ∀ x : ℝ, ((g x : ℝ) : Circ) = ((h x : ℝ) : Circ)) : g = h := by
  ext x
  let d : ℝ →+ ℝ := g - h
  have hd : ∀ y : ℝ, ∃ n : ℤ, d y = n := by
    intro y
    have h1 : (((d y : ℝ)) : Circ) = 0 := by
      show (((g y - h y : ℝ)) : Circ) = 0
      rw [AddCircle.coe_sub, hgh y, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h1
    exact ⟨n, by simpa using hn.symm⟩
  obtain ⟨n, hn⟩ := hd x
  have hn0 : n = 0 := by
    set m : ℕ := n.natAbs + 1 with hm
    have hmpos : (0 : ℝ) < m := by positivity
    obtain ⟨k, hk⟩ := hd (x / m)
    have hdx : d x = (m : ℝ) * d (x / m) := by
      have : d ((m : ℕ) • (x / m)) = (m : ℕ) • d (x / m) := map_nsmul d m (x / m)
      rw [nsmul_eq_mul, nsmul_eq_mul, mul_div_cancel₀ _ hmpos.ne'] at this
      exact this
    rw [hn, hk] at hdx
    have hz : (n : ℤ) = (m : ℤ) * k := by exact_mod_cast hdx
    have hdvd : (m : ℤ) ∣ n := ⟨k, hz⟩
    apply Int.eq_zero_of_abs_lt_dvd hdvd
    rw [Int.abs_eq_natAbs]
    simp [hm]
  rw [hn0] at hn
  simpa [d, sub_eq_zero] using hn

/-! ### a rational-valued function is not real-linear -/

lemma rat_linear_contra (g : ℝ →+ ℚ) (e : ℝ) (h : ∀ x : ℝ, ((g x : ℚ) : ℝ) = e * x) : g = 0 := by
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := by
    by_contra hall; push_neg at hall; exact hne (AddMonoidHom.ext hall)
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have h1 : e * y = (g y : ℝ) := (h y).symm
  have h2 : ((g (Real.sqrt 2 * y) : ℚ) : ℝ) = e * (Real.sqrt 2 * y) := h _
  have h3 : e * (Real.sqrt 2 * y) = Real.sqrt 2 * (g y : ℝ) := by rw [← h1]; ring
  have hq : (g y : ℝ) ≠ 0 := by exact_mod_cast hy
  have : Real.sqrt 2 = ((g (Real.sqrt 2 * y) / g y : ℚ) : ℝ) := by
    push_cast
    rw [h2, h3]; field_simp
  exact irrational_sqrt_two ⟨_, this.symm⟩

/-! ### Characters `p ∘ f_a` and total disconnectedness -/

lemma pfHom_sep (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (x : ℝ) (hx : x ≠ 0) :
    pfHom f (u / (2 * x)) x ≠ 0 := by
  rw [pfHom_apply]
  have : u / (2 * x) * x = (((1 / 2 : ℚ)) : ℝ) * u := by push_cast; field_simp
  rw [this, f_ratmul, hu]
  intro h
  have := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h
  obtain ⟨n, hn⟩ := this
  have h1 : ((n : ℝ)) = ((1 / 2 * 1 : ℚ) : ℝ) := by simpa using hn
  have : (n : ℝ) = 1 / 2 := by rw [h1]; norm_num
  have hn' : (2 * n : ℝ) = 1 := by linarith
  have : (2 * n : ℤ) = 1 := by exact_mod_cast hn'
  omega

/-- Abstract form: continuous countable-valued circle maps separating points make a space totally
disconnected. -/
theorem totallyDisconnected_of_maps {X : Type*} [TopologicalSpace X] {ι : Type*} (φ : ι → X → Circ)
    (hcont : ∀ i, Continuous (φ i)) (hcount : ∀ i, (Set.range (φ i)).Countable)
    (hsep : ∀ x y : X, x ≠ y → ∃ i, φ i x ≠ φ i y) : TotallyDisconnectedSpace X := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro x
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy
    by_contra hne
    obtain ⟨i, hi⟩ := hsep y x hne
    have htd : IsTotallyDisconnected (Set.range (φ i)) := (hcount i).isTotallyDisconnected
    have hpre : IsPreconnected ((φ i) '' connectedComponent x) :=
      isPreconnected_connectedComponent.image _ (hcont i).continuousOn
    have hsub : ((φ i) '' connectedComponent x) ⊆ Set.range (φ i) := by
      rintro _ ⟨z, -, rfl⟩; exact ⟨z, rfl⟩
    exact hi (htd _ hsub hpre ⟨y, hy, rfl⟩ ⟨x, mem_connectedComponent, rfl⟩)
  · rintro rfl; exact mem_connectedComponent

/-- A topology on `ℝ` for which all `p ∘ f_a` are continuous is totally disconnected. -/
theorem totallyDisconnected_of_pf (η : TopologicalSpace ℝ) (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1)
    (hc : ∀ a : ℝ, @Continuous ℝ Circ η circTop (pfHom f a)) : @TotallyDisconnectedSpace ℝ η := by
  have key : TotallyDisconnectedSpace (RT η) :=
    totallyDisconnected_of_maps (X := RT η) (fun a : ℝ => fun x : RT η => pfHom f a x.val)
      (fun a => hc a) (fun a => by
        refine (Set.countable_range (fun q : ℚ => ((q : ℝ) : Circ))).mono ?_
        rintro _ ⟨z, rfl⟩
        exact ⟨f (a * z.val), (pfHom_apply f a z.val).symm⟩)
      (fun x y hxy => by
        have hne : y.val - x.val ≠ 0 := sub_ne_zero.mpr (fun h => hxy (h.symm))
        refine ⟨u / (2 * (y.val - x.val)), fun h => ?_⟩
        apply pfHom_sep f u hu (y.val - x.val) hne
        rw [map_sub, ← h, sub_self])
  exact key

/-- **Proposition 6.1.**  The three topologies `β_f`, `σ_f`, `τ_f` are totally disconnected, and the continuous
characters `p ∘ f_a` separate points. -/
theorem tvg_totally_disconnected (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    @TotallyDisconnectedSpace ℝ (betaT f ⊤) ∧ @TotallyDisconnectedSpace ℝ (sigmaT f ⊤) ∧
      @TotallyDisconnectedSpace ℝ (tauT f ⊤) ∧
      (∀ x : ℝ, x ≠ 0 → ∃ a : ℝ, pfHom f a x ≠ 0) := by
  have hb : ∀ a : ℝ, @Continuous ℝ Circ (betaT f ⊤) circTop (pfHom f a) :=
    fun a => pfHom_cont_beta f ⊤ ⟨a, Submodule.mem_top⟩
  have hs : ∀ a : ℝ, @Continuous ℝ Circ (sigmaT f ⊤) circTop (pfHom f a) :=
    fun a => continuous_le_dom (sigmaT_le_betaT f ⊤) (hb a)
  have ht : ∀ a : ℝ, @Continuous ℝ Circ (tauT f ⊤) circTop (pfHom f a) :=
    fun a => continuous_le_dom (tauT_le_sigmaT f ⊤) (hs a)
  exact ⟨totallyDisconnected_of_pf _ f u hu hb, totallyDisconnected_of_pf _ f u hu hs,
    totallyDisconnected_of_pf _ f u hu ht, fun x hx => ⟨_, pfHom_sep f u hu x hx⟩⟩

/-! ### Corollary 6.3 and Corollary 10.4 : lifts of characters -/

/-- **Corollary 6.3.**  For `a ≠ 0` the `σ_f`-continuous character `p ∘ f_a` has the unique additive real lift
`f_a`; it is not continuous (for `σ_f` or for `β_f`) into the usual real line. -/
theorem lift_pf (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (a : ℝ) (ha : a ≠ 0) :
    @Continuous ℝ Circ (sigmaT f ⊤) circTop (pfHom f a) ∧
    (∀ g : ℝ →+ ℝ, (∀ x : ℝ, ((g x : ℝ) : Circ) = pfHom f a x) → g = faR f a) ∧
    ¬ Continuous[sigmaT f ⊤, (inferInstance : TopologicalSpace ℝ)] (faR f a) ∧
    ¬ Continuous[betaT f ⊤, (inferInstance : TopologicalSpace ℝ)] (faR f a) := by
  refine ⟨continuous_le_dom (sigmaT_le_betaT f ⊤) (pfHom_cont_beta f ⊤ ⟨a, Submodule.mem_top⟩), ?_, ?_, ?_⟩
  · intro g hg
    apply lift_unique
    intro x
    rw [hg x, pfHom_apply, faR_apply]
  · exact not_cont_sigma_rat f ⊤ (fa f a) (fa_ne_zero f u hu a ha)
  · exact no_rat_dual_beta f ⊤ (fa f a) (fa_ne_zero f u hu a ha)

/-- The additive real lift `h_{c,a}(x) = c x + f(a x)` of the character `χ_{c,a}`. -/
noncomputable def hlift (f : ℝ →+ ℚ) (c a : ℝ) : ℝ →+ ℝ :=
  (c • (AddMonoidHom.id ℝ).comp (AddMonoidHom.id ℝ) : ℝ →+ ℝ) + faR f a

lemma hlift_apply (f : ℝ →+ ℚ) (c a x : ℝ) : hlift f c a x = c * x + ((f (a * x) : ℚ) : ℝ) := by
  simp [hlift, faR_apply]

/-- **Corollary 10.4.**  Every `χ_{c,a}` has the unique additive real-valued lift `h_{c,a}`; for `σ_f` this lift is
continuous iff `a = 0`, for `β_f` iff `c = a = 0`. -/
theorem lift_chi (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (c a : ℝ) :
    (∀ x : ℝ, ((hlift f c a x : ℝ) : Circ) = chiH f c a x) ∧
    (∀ g : ℝ →+ ℝ, (∀ x : ℝ, ((g x : ℝ) : Circ) = chiH f c a x) → g = hlift f c a) ∧
    (Continuous[sigmaT f ⊤, (inferInstance : TopologicalSpace ℝ)] (hlift f c a) ↔ a = 0) ∧
    (Continuous[betaT f ⊤, (inferInstance : TopologicalSpace ℝ)] (hlift f c a) ↔ c = 0 ∧ a = 0) := by
  refine ⟨fun x => by rw [hlift_apply]; rfl, ?_, ?_, ?_⟩
  · intro g hg
    apply lift_unique
    intro x
    rw [hg x, hlift_apply]; rfl
  · rw [dual_sigma_real f u hu ⊤]
    constructor
    · rintro ⟨e, he⟩
      by_contra ha
      have h2 : ∀ x : ℝ, ((f (a * x) : ℚ) : ℝ) = (e - c) * x := fun x => by
        have := he x; rw [hlift_apply] at this; linarith
      have h0 : fa f a = 0 := rat_linear_contra (fa f a) (e - c) h2
      exact fa_ne_zero f u hu a ha h0
    · rintro rfl
      exact ⟨c, fun x => by rw [hlift_apply]; simp⟩
  · constructor
    · intro hcont
      have h0 := dual_beta_real f u hu ⊤ (hlift f c a) hcont
      have hz := mixed_zero f u hu c a (fun x => by
        have := h0 x
        rw [hlift_apply] at this
        unfold chiH
        rw [this]; simp)
      exact hz
    · rintro ⟨rfl, rfl⟩
      have : (hlift f 0 0 : ℝ → ℝ) = fun _ => 0 := by funext x; rw [hlift_apply]; simp
      rw [this]
      exact @continuous_const ℝ ℝ (betaT f ⊤) _ 0

end LeanCheck
