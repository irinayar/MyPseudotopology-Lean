import LeanCheck.ChainHamelTau

/-!
# Exact continuous scalar rings and the order of the parameter spaces
(TVGQ-v7 Theorems `scalar` and `order`, plus the real-valued dual of `σ_{f,S}`)

* `C_η = M(S) = { r : r S ⊆ S }` for `η = β_{f,S}, σ_{f,S}, τ_{f,S}`;
* `S ≤ T  ↔  β_{f,T} ≤ β_{f,S}  ↔  σ_{f,T} ≤ σ_{f,S}  ↔  τ_{f,T} ≤ τ_{f,S}` (i.e. `β_S ⊆ β_T ⇔ S ⊆ T`, …).
-/

namespace LeanCheck

open Filter Topology

/-- `M(S) = { r : r S ⊆ S }`. -/
def scalarRing (S : Submodule ℚ ℝ) : Set ℝ := {r | ∀ a ∈ S, a * r ∈ S}

/-! ### Membership of parameters -/

/-- If `f_a` is `τ_{f,T}`-continuous then `a ∈ T`. -/
theorem mem_of_tau_cont (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (T : Submodule ℚ ℝ) (a : ℝ)
    (h : Continuous[tauT f T, (inferInstance : TopologicalSpace ℝ)] (faR f a)) : a ∈ T := by
  classical
  obtain ⟨c, κ, hκ, b, d, hbS, hli, hform⟩ := dual_tau_real f T (faR f a) h
  have hform' : ∀ x : ℝ, ((f (a * x) : ℚ) : ℝ) = c * x + ∑ j, d j * ((f (b j * x) : ℚ) : ℝ) := hform
  -- `c = 0`
  have hc : c = 0 := by
    by_contra hc
    apply HkerG_not_countable (fun j => fa f (b j))
    refine (Set.countable_range (fun q : ℚ => (q : ℝ) / c)).mono ?_
    intro x hx
    refine ⟨f (a * x), ?_⟩
    have hx' : ∀ j, f (b j * x) = 0 := fun j => by
      have := congrFun (AddMonoidHom.mem_ker.mp hx) j
      simpa [HmapG_apply, fa_apply] using this
    have := hform' x
    simp only [hx', Rat.cast_zero, mul_zero, Finset.sum_const_zero, add_zero] at this
    field_simp
    linarith
  subst hc
  -- sections
  choose xs hxs using fun j : κ => Hmap_surj f b hli (Pi.single j (1 : ℚ))
  have hd : ∀ i, d i = ((f (a * xs i) : ℚ) : ℝ) := by
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
  -- `f_a = f_{∑ q_j b_j}`
  set q : κ → ℚ := fun i => f (a * xs i) with hq
  have hfx : ∀ x : ℝ, f (a * x) = ∑ j, q j * f (b j * x) := by
    intro x
    have := hform' x
    simp only [zero_mul, zero_add, hd] at this
    exact_mod_cast this
  have hfa : ∀ x : ℝ, f ((∑ j, ((q j : ℚ) : ℝ) * b j) * x) = ∑ j, q j * f (b j * x) := by
    intro x
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_assoc, f_ratmul]
  have hmem : (∑ j, ((q j : ℚ) : ℝ) * b j) ∈ T := by
    refine T.sum_mem (fun j _ => ?_)
    have := T.smul_mem (q j) (hbS j)
    simpa [Rat.smul_def] using this
  have hzero := mixed_zero f u hu 0 (a - ∑ j, ((q j : ℚ) : ℝ) * b j) (fun x => by
    unfold chiH
    rw [zero_mul, zero_add, sub_mul, map_sub, hfx, hfa, sub_self]
    simp)
  have : a = ∑ j, ((q j : ℚ) : ℝ) * b j := sub_eq_zero.mp hzero.2
  rw [this]; exact hmem

/-- If `p ∘ f_a` is `β_{f,T}`-continuous then `a ∈ T`. -/
theorem mem_of_pf_cont_beta (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (T : Submodule ℚ ℝ) (a : ℝ)
    (h : @Continuous ℝ Circ (betaT f T) circTop (pfHom f a)) : a ∈ T := by
  obtain ⟨c, a', ha', hc⟩ := (dual_beta f T (pfHom f a)).mp h
  have heq : ∀ x, chiH f 0 a x = chiH f c a' x := fun x => by
    rw [← hc x, pfHom_apply]; simp [chiH]
  have := chiH_unique f u hu 0 a c a' heq
  rw [this.2]; exact ha'

/-- If `p ∘ f_a` is `σ_{f,T}`-continuous then `a ∈ T`. -/
theorem mem_of_pf_cont_sigma (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (T : Submodule ℚ ℝ) (a : ℝ)
    (h : @Continuous ℝ Circ (sigmaT f T) circTop (pfHom f a)) : a ∈ T := by
  obtain ⟨c, a', ha', hc⟩ := (dual_sigma f T (pfHom f a)).mp h
  have heq : ∀ x, chiH f 0 a x = chiH f c a' x := fun x => by
    rw [← hc x, pfHom_apply]; simp [chiH]
  have := chiH_unique f u hu 0 a c a' heq
  rw [this.2]; exact ha'

/-! ### The exact scalar rings -/

lemma betaT_dilation (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (r : ℝ) (hr : r ∈ scalarRing S) :
    Continuous[betaT f S, betaT f S] (fun x : ℝ => r * x) := by
  have hB : Continuous[betaT f S, ⨅ b : ℝ, TopologicalSpace.induced (fun x : ℝ => ((b * x : ℝ) : Circ)) circTop]
      (fun x : ℝ => r * x) := by
    refine continuous_iInf_rng.2 (fun b => continuous_induced_rng.2 ?_)
    have : ((fun x : ℝ => ((b * x : ℝ) : Circ)) ∘ fun x : ℝ => r * x) = cmulHom (b * r) := by
      funext x; simp only [Function.comp, cmulHom_apply]; rw [mul_assoc]
    rw [this]
    exact cmulHom_cont_beta f S (b * r)
  have hA : Continuous[betaT f S, ⨅ a : S, TopologicalSpace.induced
      (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop] (fun x : ℝ => r * x) := by
    refine continuous_iInf_rng.2 (fun a => continuous_induced_rng.2 ?_)
    have : ((fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) ∘ fun x : ℝ => r * x) =
        pfHom f ((a : ℝ) * r) := by
      funext x; simp only [Function.comp, pfHom_apply]; rw [mul_assoc]
    rw [this]
    exact pfHom_cont_beta f S ⟨(a : ℝ) * r, hr a a.2⟩
  exact (continuous_inf_rng (t₁ := betaT f S)).2 ⟨hB, hA⟩

/-- **`C_{τ_{f,S}} = M(S)`.** -/
theorem scalar_tau (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) (r : ℝ) :
    Continuous[tauT f S, tauT f S] (fun x : ℝ => r * x) ↔ r ∈ scalarRing S := by
  constructor
  · intro hr a ha
    apply mem_of_tau_cont f u hu S (a * r)
    have h1 := faR_cont_tau f S a ha
    have : (faR f (a * r) : ℝ → ℝ) = (faR f a : ℝ → ℝ) ∘ fun x : ℝ => r * x := by
      funext x; simp only [Function.comp, faR_apply]; rw [mul_assoc]
    rw [this]
    exact @Continuous.comp ℝ ℝ ℝ (tauT f S) (tauT f S) _ (fun x : ℝ => r * x) (faR f a) h1 hr
  · intro hr
    exact TfS_dilation f S usualQ r hr

/-- **`C_{σ_{f,S}} = M(S)`.** -/
theorem scalar_sigma (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) (r : ℝ) :
    Continuous[sigmaT f S, sigmaT f S] (fun x : ℝ => r * x) ↔ r ∈ scalarRing S := by
  constructor
  · intro hr a ha
    apply mem_of_pf_cont_sigma f u hu S (a * r)
    have h1 : @Continuous ℝ Circ (sigmaT f S) circTop (pfHom f a) :=
      continuous_le_dom (sigmaT_le_betaT f S) (pfHom_cont_beta f S ⟨a, ha⟩)
    have : (pfHom f (a * r) : ℝ → Circ) = (pfHom f a : ℝ → Circ) ∘ fun x : ℝ => r * x := by
      funext x; simp only [Function.comp, pfHom_apply]; rw [mul_assoc]
    rw [this]
    exact @Continuous.comp ℝ ℝ Circ (sigmaT f S) (sigmaT f S) circTop (fun x : ℝ => r * x)
      (pfHom f a) h1 hr
  · intro hr
    exact TfS_dilation f S gamma0 r hr

/-- **`C_{β_{f,S}} = M(S)`.** -/
theorem scalar_beta (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) (r : ℝ) :
    Continuous[betaT f S, betaT f S] (fun x : ℝ => r * x) ↔ r ∈ scalarRing S := by
  constructor
  · intro hr a ha
    apply mem_of_pf_cont_beta f u hu S (a * r)
    have h1 := pfHom_cont_beta f S ⟨a, ha⟩
    have : (pfHom f (a * r) : ℝ → Circ) = (pfHom f a : ℝ → Circ) ∘ fun x : ℝ => r * x := by
      funext x; simp only [Function.comp, pfHom_apply]; rw [mul_assoc]
    rw [this]
    exact @Continuous.comp ℝ ℝ Circ (betaT f S) (betaT f S) circTop (fun x : ℝ => r * x)
      (pfHom f a) h1 hr
  · intro hr
    exact betaT_dilation f S r hr

/-! ### Order of the parameter spaces -/

lemma betaT_mono_S (f : ℝ →+ ℚ) {S T : Submodule ℚ ℝ} (h : S ≤ T) : betaT f T ≤ betaT f S := by
  unfold betaT
  exact inf_le_inf_left _ (le_iInf fun a : S => iInf_le (fun b : T =>
    TopologicalSpace.induced (fun x : ℝ => (((f ((b : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop) ⟨(a : ℝ), h a.2⟩)

lemma sigmaT_mono_S (f : ℝ →+ ℚ) {S T : Submodule ℚ ℝ} (h : S ≤ T) : sigmaT f T ≤ sigmaT f S :=
  TfS_mono_S f h gamma0

lemma tauT_mono_S (f : ℝ →+ ℚ) {S T : Submodule ℚ ℝ} (h : S ≤ T) : tauT f T ≤ tauT f S :=
  TfS_mono_S f h usualQ

/-- **Order of the parameter spaces.**  `S ⊆ T` iff `β_S ⊆ β_T` (iff `σ_S ⊆ σ_T`, iff `τ_S ⊆ τ_T`). -/
theorem order_beta (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S T : Submodule ℚ ℝ) :
    S ≤ T ↔ betaT f T ≤ betaT f S := by
  constructor
  · exact betaT_mono_S f
  · intro hle a ha
    exact mem_of_pf_cont_beta f u hu T a
      (continuous_le_dom hle (pfHom_cont_beta f S ⟨a, ha⟩))

theorem order_sigma (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S T : Submodule ℚ ℝ) :
    S ≤ T ↔ sigmaT f T ≤ sigmaT f S := by
  constructor
  · exact sigmaT_mono_S f
  · intro hle a ha
    exact mem_of_pf_cont_sigma f u hu T a
      (continuous_le_dom hle (continuous_le_dom (sigmaT_le_betaT f S) (pfHom_cont_beta f S ⟨a, ha⟩)))

theorem order_tau (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S T : Submodule ℚ ℝ) :
    S ≤ T ↔ tauT f T ≤ tauT f S := by
  constructor
  · exact tauT_mono_S f
  · intro hle a ha
    exact mem_of_tau_cont f u hu T a (continuous_le_dom hle (faR_cont_tau f S a ha))

/-- Different parameter spaces give different topologies. -/
theorem betaT_injective (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S T : Submodule ℚ ℝ)
    (h : betaT f S = betaT f T) : S = T :=
  le_antisymm ((order_beta f u hu S T).2 h.ge) ((order_beta f u hu T S).2 h.le)

theorem sigmaT_injective (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S T : Submodule ℚ ℝ)
    (h : sigmaT f S = sigmaT f T) : S = T :=
  le_antisymm ((order_sigma f u hu S T).2 h.ge) ((order_sigma f u hu T S).2 h.le)

theorem tauT_injective (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S T : Submodule ℚ ℝ)
    (h : tauT f S = tauT f T) : S = T :=
  le_antisymm ((order_tau f u hu S T).2 h.ge) ((order_tau f u hu T S).2 h.le)

/-! ### Real-valued continuous additive maps on `σ_{f,S}` -/

/-- `Hom_cont((ℝ, σ_{f,S}), ℝ_usual) = ℝ · id`. -/
theorem dual_sigma_real (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) (g : ℝ →+ ℝ) :
    Continuous[sigmaT f S, (inferInstance : TopologicalSpace ℝ)] g ↔ ∃ c : ℝ, ∀ x : ℝ, g x = c * x := by
  constructor
  · intro hg
    let χ : ℝ →+ Circ := (cmulHom 1).comp g
    have hχc : @Continuous ℝ Circ (sigmaT f S) circTop χ := by
      have := @Continuous.comp ℝ ℝ Circ (sigmaT f S) _ circTop g (cmulHom 1)
        (continuous_coe_circ.comp (continuous_const.mul continuous_id)) hg
      exact this
    obtain ⟨c, a, ha, h⟩ := (dual_sigma f S χ).mp hχc
    have hint : ∀ x : ℝ, g x - (c * x + ((f (a * x) : ℚ) : ℝ)) = 0 := by
      intro x
      apply int_of_all_div
      intro n hn
      have h0 := h (((1 / (n : ℚ) : ℚ) : ℝ) * x)
      have hχx : χ (((1 / (n : ℚ) : ℚ) : ℝ) * x) = ((g (((1 / (n : ℚ) : ℚ) : ℝ) * x) : ℝ) : Circ) := by
        simp [χ, cmulHom_apply]
      rw [hχx] at h0
      unfold chiH at h0
      have h2 : ((g (((1 / (n : ℚ) : ℚ) : ℝ) * x) -
          (c * (((1 / (n : ℚ) : ℚ) : ℝ) * x) + ((f (a * (((1 / (n : ℚ) : ℚ) : ℝ) * x)) : ℚ) : ℝ)) : ℝ) : Circ)
          = 0 := by
        rw [AddCircle.coe_sub, h0, sub_self]
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h2
      refine ⟨k, ?_⟩
      rw [zsmul_eq_mul, mul_one] at hk
      have hgq : g (((1 / (n : ℚ) : ℚ) : ℝ) * x) = (1 / (n : ℝ)) * g x := by
        have := map_ratCast_smul g ℝ ℝ (1 / (n : ℚ)) x
        simpa [smul_eq_mul] using this
      have h3 : f (a * (((1 / (n : ℚ) : ℚ) : ℝ) * x)) = (1 / (n : ℚ)) * f (a * x) := by
        rw [mul_left_comm, f_ratmul]
      rw [hgq, h3] at hk
      push_cast at hk
      have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [hk]
      field_simp
    -- `f_a` is then continuous and rational-valued, hence zero
    have hfa : fa f a = 0 := by
      by_contra hne
      apply not_cont_sigma_rat f S (fa f a) hne
      have : (fun x : ℝ => ((fa f a x : ℚ) : ℝ)) = fun x : ℝ => g x - c * x := by
        funext x
        have := hint x
        simp only [fa_apply]
        linarith
      rw [this]
      have hc' : Continuous[sigmaT f S, (inferInstance : TopologicalSpace ℝ)] (fun x : ℝ => c * x) :=
        continuous_le_dom (sigmaT_le_usual f S) (continuous_const.mul continuous_id)
      have hc2 : Continuous[sigmaT f S, (inferInstance : TopologicalSpace ℝ)] (fun x : ℝ => (-c) * x) :=
        continuous_le_dom (sigmaT_le_usual f S) (continuous_const.mul continuous_id)
      have := @Continuous.add ℝ _ _ _ ℝ (sigmaT f S) _ _ hg hc2
      convert this using 2
      simp [sub_eq_add_neg]
    refine ⟨c, fun x => ?_⟩
    have := hint x
    have h0 : f (a * x) = 0 := by
      have := congrArg (fun m : ℝ →+ ℚ => m x) hfa
      simpa [fa_apply] using this
    simp only [h0, Rat.cast_zero, add_zero] at this
    linarith
  · rintro ⟨c, hc⟩
    have : (g : ℝ → ℝ) = fun x => c * x := funext hc
    rw [this]
    exact continuous_le_dom (sigmaT_le_usual f S) (continuous_const.mul continuous_id)

end LeanCheck
