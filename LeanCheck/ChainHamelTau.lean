import LeanCheck.ChainHamelStrict

/-!
# The real-valued topology `τ_{f,S}`: duals, exact scalar rings, and order of parameter spaces
(TVGQ-v7 Theorems `realcompletion` (dual part), `scalar`, `order`)
-/

namespace LeanCheck

open Filter Topology

/-! ### Strictness `σ ⊊ τ` and rational duals -/

/-- `x ↦ f(a x)` as an additive map `ℝ → ℝ` (rational-valued). -/
noncomputable def faR (f : ℝ →+ ℚ) (a : ℝ) : ℝ →+ ℝ := (Rat.castHom ℝ).toAddMonoidHom.comp (fa f a)

lemma faR_apply (f : ℝ →+ ℚ) (a x : ℝ) : faR f a x = ((f (a * x) : ℚ) : ℝ) := rfl

lemma fa_ne_zero (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (a : ℝ) (ha : a ≠ 0) : fa f a ≠ 0 := by
  intro h
  have := congrArg (fun m : ℝ →+ ℚ => m (u / a)) h
  simp only [fa_apply, AddMonoidHom.zero_apply] at this
  rw [show a * (u / a) = u by field_simp, hu] at this
  exact one_ne_zero this

/-- `f_a` is `τ_{f,S}`-continuous (into `ℝ`) for `a ∈ S`. -/
theorem faR_cont_tau (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (a : ℝ) (ha : a ∈ S) :
    Continuous[tauT f S, (inferInstance : TopologicalSpace ℝ)] (faR f a) := by
  have h := faS_cont f S usualQ ⟨a, ha⟩
  have h2 : Continuous[usualQ, (inferInstance : TopologicalSpace ℝ)] (fun s : ℚ => (s : ℝ)) :=
    Rat.continuous_coe_real
  exact @Continuous.comp ℝ ℚ ℝ (tauT f S) usualQ _ (fa f a) (fun s : ℚ => (s : ℝ)) h2 h

/-- **`τ_{f,S} ⊊ σ_{f,S}`** (i.e. `σ ⊊ τ` as families of open sets). -/
theorem tauT_lt_sigmaT (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) (a : ℝ) (haS : a ∈ S)
    (ha : a ≠ 0) : tauT f S < sigmaT f S := by
  refine lt_of_le_of_ne (tauT_le_sigmaT f S) (fun heq => ?_)
  have h := faR_cont_tau f S a haS
  rw [heq] at h
  exact not_cont_sigma_rat f S (fa f a) (fa_ne_zero f u hu a ha) h

/-- The continuous rational-valued additive duals of `σ` and `β` are zero. -/
theorem no_rat_dual_beta (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (g : ℝ →+ ℚ) (hg : g ≠ 0) :
    ¬ Continuous[betaT f S, (inferInstance : TopologicalSpace ℝ)] (fun x : ℝ => ((g x : ℚ) : ℝ)) := by
  intro h
  exact not_cont_sigma_rat f S g hg (continuous_le_dom (sigmaT_le_betaT f S) h)

/-! ### The uncountable joint kernel -/

lemma HkerG_not_countable {ι : Type} [Fintype ι] (g : ι → ℝ →+ ℚ) :
    ¬ ((HmapG g).ker : Set ℝ).Countable := by
  intro hc
  classical
  let r : (ι → ℚ) → ℝ := fun v => if hv : ∃ x, HmapG g x = v then hv.choose else 0
  have hsub : (Set.univ : Set ℝ) ⊆ ⋃ v : ι → ℚ, (fun e : ℝ => e + r v) '' ((HmapG g).ker : Set ℝ) := by
    intro x _
    refine Set.mem_iUnion.2 ⟨HmapG g x, ⟨x - r (HmapG g x), ?_, by ring⟩⟩
    have hv : ∃ y, HmapG g y = HmapG g x := ⟨x, rfl⟩
    have : r (HmapG g x) = hv.choose := by simp only [r, dif_pos hv]
    rw [this]
    show HmapG g (x - hv.choose) = 0
    rw [map_sub, hv.choose_spec, sub_self]
  exact Cardinal.not_countable_real ((Set.countable_iUnion fun v => hc.image _).mono hsub)

/-! ### Real-valued continuous additive maps on `τ_{f,S}` -/

/-- **Dual of `τ_{f,S}` (real-valued)**: a continuous additive `g : ℝ → ℝ` is `c x + ∑ d_j f(b_j x)` with
`b_j ∈ S` (and `f_{b_j}` `ℚ`-independent). -/
theorem dual_tau_real (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (g : ℝ →+ ℝ)
    (hg : Continuous[tauT f S, (inferInstance : TopologicalSpace ℝ)] g) :
    ∃ (c : ℝ) (κ : Type) (_ : Fintype κ) (b : κ → ℝ) (d : κ → ℝ),
      (∀ j, b j ∈ S) ∧ LinearIndependent ℚ (fun j => Fa f (b j)) ∧
      ∀ x : ℝ, g x = c * x + ∑ j, d j * ((f (b j * x) : ℚ) : ℝ) := by
  classical
  have hT : g ⁻¹' Set.Ioo (-(1 / 4) : ℝ) (1 / 4) ∈ @nhds ℝ (tauT f S) 0 := by
    have h0 := (@Continuous.continuousAt ℝ ℝ (tauT f S) _ g 0 hg)
    have hI : Set.Ioo (-(1 / 4) : ℝ) (1 / 4) ∈ 𝓝 (g 0) := by
      rw [map_zero]
      exact Ioo_mem_nhds (by norm_num) (by norm_num)
    exact h0 hI
  obtain ⟨ε, hε, κ, hκ, b, W, hbS, hli, -, hW, hsm⟩ :=
    packagedS_set f S usualQ usualQ_group usualQ_scalar _ hT ∅ (by simp)
  -- linearize `p ∘ g` on the joint kernel
  let χ : ℝ →+ Circ := (cmulHom 1).comp g
  have hχ : ∀ x, χ x = ((g x : ℝ) : Circ) := by intro x; simp [χ, cmulHom_apply]
  have hsmall : ∀ x ∈ (Hmap f b).ker, |x| < ε → ‖χ x‖ < 1 / 4 := by
    intro x hx hxε
    have hmem : x ∈ {x : ℝ | |x| < ε ∧ ∀ j, f (b j * x) ∈ W j} := by
      refine ⟨hxε, fun j => ?_⟩
      have h0 : f (b j * x) = 0 := by
        have := congrFun (AddMonoidHom.mem_ker.mp hx) j
        simpa [Hmap_apply] using this
      rw [h0]; exact mem_of_mem_nhds (hW j)
    have hgx := hsm hmem
    simp only [Set.mem_preimage, Set.mem_Ioo] at hgx
    rw [hχ]
    have hn := norm_coe_le (g x) 0
    simp only [Int.cast_zero, sub_zero] at hn
    have habs : |g x| < 1 / 4 := abs_lt.mpr ⟨by linarith [hgx.1], hgx.2⟩
    exact lt_of_le_of_lt hn habs
  obtain ⟨c, hc⟩ := linearize χ (Hmap f b).ker ε hε (Hker_qmul f b) hsmall (Hker_dense f b)
  -- `g = c x` on the kernel
  have hgN : ∀ x ∈ (Hmap f b).ker, g x = c * x := by
    intro x hx
    have hdiv : (g x - c * x) = 0 := by
      apply int_of_all_div
      intro n hn
      have hq : (((1 / (n : ℚ) : ℚ) : ℝ)) * x ∈ (Hmap f b).ker := Hker_qmul f b x hx _
      have h1 := hc _ hq
      rw [hχ] at h1
      have h2 : ((g (((1 / (n : ℚ) : ℚ) : ℝ) * x) - c * (((1 / (n : ℚ) : ℚ) : ℝ) * x) : ℝ) : Circ) = 0 := by
        rw [AddCircle.coe_sub, h1, sub_self]
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h2
      refine ⟨k, ?_⟩
      rw [zsmul_eq_mul, mul_one] at hk
      have hgq : g (((1 / (n : ℚ) : ℚ) : ℝ) * x) = (1 / (n : ℝ)) * g x := by
        have := map_ratCast_smul g ℝ ℝ (1 / (n : ℚ)) x
        simpa [smul_eq_mul] using this
      rw [hgq] at hk
      push_cast at hk
      have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [hk]
      field_simp
    linarith
  -- sections
  have hli' := hli
  choose xs hxs using fun j : κ => Hmap_surj f b hli (Pi.single j (1 : ℚ))
  refine ⟨c, κ, hκ, b, fun j => g (xs j) - c * xs j, hbS, hli, fun x => ?_⟩
  have hz : x - ∑ j, ((f (b j * x) : ℚ) : ℝ) * xs j ∈ (Hmap f b).ker := by
    rw [AddMonoidHom.mem_ker]
    funext i
    rw [map_sub, map_sum]
    have hHx : ∀ (t : ℚ) (j i : κ), Hmap f b ((t : ℝ) * xs j) i =
        t * (Pi.single j (1 : ℚ) : κ → ℚ) i := by
      intro t j i
      rw [Hmap_apply, mul_left_comm, f_ratmul, ← Hmap_apply, hxs j]
    simp only [Pi.sub_apply, Finset.sum_apply, hHx, Pi.zero_apply]
    simp [Pi.single_apply, Hmap_apply]
  have h0 := hgN _ hz
  rw [map_sub, map_sum] at h0
  have hqs : ∀ j, g (((f (b j * x) : ℚ) : ℝ) * xs j) = ((f (b j * x) : ℚ) : ℝ) * g (xs j) := by
    intro j
    have := map_ratCast_smul g ℝ ℝ (f (b j * x)) (xs j)
    simpa [smul_eq_mul] using this
  simp only [hqs] at h0
  have e : c * (x - ∑ j, ((f (b j * x) : ℚ) : ℝ) * xs j) =
      c * x - ∑ j, ((f (b j * x) : ℚ) : ℝ) * (c * xs j) := by
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => by ring)
  have e2 : ∑ j, (g (xs j) - c * xs j) * ((f (b j * x) : ℚ) : ℝ) =
      ∑ j, ((f (b j * x) : ℚ) : ℝ) * g (xs j) - ∑ j, ((f (b j * x) : ℚ) : ℝ) * (c * xs j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have e3 : ∑ j, (g (xs j) - c * xs j) * ((f (b j * x) : ℚ) : ℝ) =
      ∑ j, (g (xs j) - c * xs j) * ((f (b j * x) : ℚ) : ℝ) := rfl
  have e4 : ∑ j, (g (xs j) - c * xs j) * ((f (b j * x) : ℚ) : ℝ) =
      ∑ j, (g (xs j) - c * xs j) * ((f (b j * x) : ℚ) : ℝ) := rfl
  rw [e] at h0
  have : g x = c * x + ∑ j, (g (xs j) - c * xs j) * ((f (b j * x) : ℚ) : ℝ) := by
    rw [e2]; linarith
  exact this

end LeanCheck
