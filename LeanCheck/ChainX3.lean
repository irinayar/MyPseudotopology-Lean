import LeanCheck.ChainX2

/-!
# A strictly finer compatible rational topology, and restrictions on a greatest topology
(TVGQ-v7 Proposition 13.2 `strict-compatible`, Corollary 13.6 `greatest-restrictions-v4`)

For the factorial chain `M_n = (n+1)!` (ratios `n+2 → ∞`, every integer divides a term) the topology `λ` of
`ℚ/ℤ` is compatible with `ℤι` (`dual_exact`), and its lift `δ = γ_λ` to `ℚ` lies in `𝒟_Γ`, is strictly finer
than `γ₀`, and is not precompact.

* `strict_compatible_refinement` : there is `δ ∈ 𝒟_Γ` with `δ ⊊ ...` i.e. `δ < γ₀`; consequently
  `S_f(δ) ∈ 𝒞^ℚ_{f,ℚ}` and `S_f(δ) < σ_{f,ℚ}`;
* `greatest_restrictions` : a greatest member of `𝒞^ℚ_{f,ℚ}` is non-Baire, nonprecompact, not locally compact and
  not completely metrizable;
* `greatest_rational_restrictions` : the same four properties for a greatest member of `𝒟_Γ`.
-/

namespace LeanCheck

open Filter Topology

/-! ### The factorial chain -/

def alpha2 : ℕ → ℕ := fun i => i + 2

lemma Mseq_alpha2 (n : ℕ) : Mseq alpha2 n = (n + 1).factorial := by
  induction n with
  | zero => simp [Mseq]
  | succ n ih =>
    simp only [Mseq, alpha2, ih]
    rw [Nat.factorial_succ (n + 1)]

lemma Mseq_alpha2_succ (n : ℕ) : Mseq alpha2 (n + 1) = (n + 2) * Mseq alpha2 n := by
  simp [Mseq, alpha2]

lemma Mseq_alpha2_pos (n : ℕ) : 0 < Mseq alpha2 n := Mseq_pos (fun i => by simp [alpha2]) n

lemma alpha2_dual (χ : TorsA →+ Circ) :
    @Continuous TorsA Circ (basisOf (Set.range (Mseq alpha2))).topology _ χ ↔
      ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ) := by
  refine dual_exact (α := alpha2) (fun i => by simp [alpha2]) ?_ ?_ (by simp [Mseq]) χ
  · intro A
    refine ⟨⌈A⌉₊, fun i hi => ?_⟩
    have : A ≤ (i : ℝ) := (Nat.le_ceil A).trans (by exact_mod_cast hi)
    simp only [alpha2]; push_cast; linarith
  · intro N hN
    refine ⟨N, fun n hn => ?_⟩
    rw [Mseq_alpha2]
    exact Nat.dvd_factorial hN (by omega)

/-- The topology `λ` of the factorial chain on `ℚ/ℤ`. -/
noncomputable def lamC : TopologicalSpace TorsA := (basisOf (Set.range (Mseq alpha2))).topology

lemma one_mem_range_Mseq : (1 : ℕ) ∈ Set.range (Mseq alpha2) := ⟨0, by simp [Mseq]⟩

lemma lamC_group : @IsTopologicalAddGroup TorsA lamC _ := (basisOf (Set.range (Mseq alpha2))).isTopologicalAddGroup

/-- The lifted topology `δ = γ_λ` on `ℚ`. -/
noncomputable def delta2 : TopologicalSpace ℚ := gam lamC

lemma delta2_mem : delta2 ∈ Ccls Gam := by
  refine ⟨⟨gam_group _ lamC_group, @gam_t2 _ (t2_basisOf one_mem_range_Mseq),
    lqc_gam _ (lqc_basisOf _), fun χ => dual_gam _ lamC_group alpha2_dual χ⟩, fun q => ?_⟩
  have e : (⇑(mq q : ℚ →+ ℚ)) = fun x : ℚ => q * x := by funext x; simp [mq_apply]
  rw [e]
  exact gam_scalar _ q

/-! ### The inclusion `λ ≤ circle topology` and `δ ≤ γ₀` -/

lemma gam_mono {t t' : TopologicalSpace TorsA} (h : t ≤ t') : gam t ≤ gam t' :=
  iInf_mono (fun r => induced_mono h)

lemma lamC_le_circT : lamC ≤ circT := by
  have hc : Continuous[lamC, circTop] ((AddCommGroup.torsion Circ).subtype) :=
    continuous_of_quarter (Set.range (Mseq alpha2)) _ ⟨1 / 8, by norm_num, fun x hx => by
      have := hx 1 one_mem_range_Mseq
      rw [one_nsmul] at this
      show ‖(x : Circ)‖ < 1 / 4
      linarith⟩
  exact continuous_iff_le_induced.mp hc

lemma delta2_le_gamma0 : delta2 ≤ gamma0 := by
  rw [gamma0_eq_gam]
  exact gam_mono lamC_le_circT

/-! ### The witnesses `e_k` -/

def mk' (k : ℕ) : ℕ := (k + 2) / 2

noncomputable def ek (k : ℕ) : ℚ := (mk' k : ℚ) / (Mseq alpha2 (k + 1) : ℚ)

lemma ek_real (k : ℕ) : ((ek k : ℚ) : ℝ) = (mk' k : ℝ) / (Mseq alpha2 (k + 1) : ℝ) := by
  unfold ek; push_cast; rfl

/-- `M_k e_k = m_k / (k+2)`. -/
lemma Mk_ek (k : ℕ) : (Mseq alpha2 k : ℝ) * ((ek k : ℚ) : ℝ) = (mk' k : ℝ) / ((k : ℝ) + 2) := by
  rw [ek_real, Mseq_alpha2_succ]
  have h1 : (Mseq alpha2 k : ℝ) ≠ 0 := by exact_mod_cast (Mseq_alpha2_pos k).ne'
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  push_cast
  field_simp

lemma mk'_bounds (k : ℕ) : 3 * mk' k ≥ k + 2 ∧ 2 * mk' k ≤ k + 2 := by
  unfold mk'; omega

lemma norm_Mk_ek (k : ℕ) :
    1 / 3 ≤ ‖(Mseq alpha2 k) • ((piHom (ek k) : TorsA) : Circ)‖ := by
  rw [piHom_coe, nsmul_coe_circ, Mk_ek]
  obtain ⟨h3, h2⟩ := mk'_bounds k
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hv : (mk' k : ℝ) / ((k : ℝ) + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hk (by norm_num)]
    have : (2 * mk' k : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast h2
    linarith
  have hv0 : 0 ≤ (mk' k : ℝ) / ((k : ℝ) + 2) := by positivity
  rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2
    (by rw [abs_of_nonneg hv0]; simpa using hv), abs_of_nonneg hv0]
  rw [le_div_iff₀ hk]
  have : ((k : ℝ) + 2) ≤ 3 * (mk' k : ℝ) := by exact_mod_cast h3
  linarith

lemma Mj_ek_zero {i j : ℕ} (h : i < j) : (Mseq alpha2 j) • ((piHom (ek i) : TorsA) : Circ) = 0 := by
  rw [piHom_coe, nsmul_coe_circ, AddCircle.coe_eq_zero_iff]
  obtain ⟨c, hc⟩ := Mseq_dvd alpha2 (show i + 1 ≤ j from h)
  refine ⟨(mk' i * c : ℕ), ?_⟩
  rw [ek_real, hc]
  have h1 : (Mseq alpha2 (i + 1) : ℝ) ≠ 0 := by exact_mod_cast (Mseq_alpha2_pos _).ne'
  simp only [zsmul_eq_mul, mul_one, Int.cast_natCast, Nat.cast_mul]
  field_simp
  push_cast
  ring

/-! ### `δ ≠ γ₀` -/

lemma ek_tendsto_gamma0 : Tendsto ek atTop (@nhds ℚ gamma0 0) := by
  unfold gamma0
  rw [nhds_iInf, tendsto_iInf]
  intro r
  rw [nhds_induced, tendsto_comap_iff]
  have hreal : Tendsto (fun k : ℕ => ((ek k : ℚ) : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => ?_) (fun k => ?_) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · rw [ek_real]; positivity
    · rw [ek_real, Mseq_alpha2_succ]
      have hM : (k : ℝ) + 1 ≤ (Mseq alpha2 k : ℝ) := by
        rw [Mseq_alpha2]
        exact_mod_cast Nat.self_le_factorial (k + 1)
      have hm : (mk' k : ℝ) * 2 ≤ (k : ℝ) + 2 := by
        have := (mk'_bounds k).2
        exact_mod_cast (by omega : mk' k * 2 ≤ k + 2)
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      push_cast
      have hMpos : (0 : ℝ) < (Mseq alpha2 k : ℝ) := by exact_mod_cast Mseq_alpha2_pos k
      rw [div_le_div_iff₀ (mul_pos hk2 hMpos) hk1]
      nlinarith [Nat.cast_nonneg (α := ℝ) (mk' k), Nat.cast_nonneg (α := ℝ) k]
  have hmul : Tendsto (fun k : ℕ => ((r : ℚ) : ℝ) * ((ek k : ℚ) : ℝ)) atTop (𝓝 0) := by
    simpa using hreal.const_mul ((r : ℚ) : ℝ)
  have h3 := (continuous_coe_circ.tendsto (0 : ℝ)).comp hmul
  have e : ((fun s : ℚ => (((r * s : ℚ) : ℝ) : Circ)) ∘ ek) =
      (fun y : ℝ => (y : Circ)) ∘ (fun k : ℕ => ((r : ℚ) : ℝ) * ((ek k : ℚ) : ℝ)) := by
    funext k; simp
  have e0 : ((((r * 0 : ℚ) : ℝ)) : Circ) = ((0 : ℝ) : Circ) := by simp
  rw [e, e0]
  exact h3

theorem delta2_ne_gamma0 : delta2 ≠ gamma0 := by
  intro heq
  have h1 : Tendsto ek atTop (@nhds ℚ delta2 0) := by rw [heq]; exact ek_tendsto_gamma0
  have h2 : Tendsto (fun k => hq 1 (ek k)) atTop (@nhds TorsA lamC 0) := by
    have hc := @Continuous.tendsto ℚ TorsA delta2 lamC (hq 1) (hq_continuous lamC 1) 0
    rw [map_zero] at hc
    exact hc.comp h1
  have hmem : obs (Set.range (Mseq alpha2)) (1 / 4) ∈ @nhds TorsA lamC 0 :=
    ((basisOf (Set.range (Mseq alpha2))).nhds_zero_hasBasis).mem_of_mem
      (mem_basisOf (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨k, hk⟩ := (h2.eventually hmem).exists
  have := hk (Mseq alpha2 k) ⟨k, rfl⟩
  have h3 := norm_Mk_ek k
  rw [hq_apply, one_mul] at this
  linarith

theorem delta2_lt_gamma0 : delta2 < gamma0 := lt_of_le_of_ne delta2_le_gamma0 delta2_ne_gamma0

/-- **Proposition 13.2 (`strict-compatible`).**  There is `δ ∈ 𝒟_Γ` strictly finer than `γ₀`; consequently
`S_f(δ)` is a member of `𝒞^ℚ_{f,ℚ}` strictly finer than `σ_{f,ℚ}`. -/
theorem strict_compatible_refinement (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    ∃ δ ∈ Ccls Gam, δ < gamma0 ∧ Tq f δ ∈ Ccls (Hq f) ∧ Tq f δ < sigmaQ f := by
  refine ⟨delta2, delta2_mem, delta2_lt_gamma0, Tq_mem_Ccls f u hu _ delta2_mem, ?_⟩
  rw [← Tq_gamma0]
  refine lt_of_le_of_ne ?_ ?_
  · exact Tq_mono f delta2_le_gamma0
  · intro h
    have h' : Tq f delta2 ≤ Tq f gamma0 := h.le
    have hg0 := delta2_mem.1.1
    have := (Tq_le_iff f u hu gamma0 delta2 (by rw [gamma0_eq_gam]; exact gam_group _ circT_group) hg0).1 h.symm.le
    exact delta2_ne_gamma0 (le_antisymm delta2_le_gamma0 this)

/-! ### Precompactness -/

/-- Precompactness of a group topology on an arbitrary additive group. -/
def PrecompactG {G : Type*} [AddCommGroup G] (τ : TopologicalSpace G) : Prop :=
  ∀ U ∈ @nhds G τ 0, ∃ F : Finset G, ∀ x : G, ∃ t ∈ F, x - t ∈ U

lemma precompactG_of_le {G : Type*} [AddCommGroup G] {τ τ' : TopologicalSpace G} (h : τ ≤ τ')
    (hτ : PrecompactG τ) : PrecompactG τ' := fun U hU => hτ U ((nhds_mono h) hU)

lemma precompactG_image {G H : Type*} [AddCommGroup G] [AddCommGroup H] {τ : TopologicalSpace G}
    {σ : TopologicalSpace H} (g : G →+ H) (hg : Continuous[τ, σ] g) (hs : Function.Surjective g)
    (hτ : PrecompactG τ) : PrecompactG σ := by
  classical
  intro U hU
  have hpre : g ⁻¹' U ∈ @nhds G τ 0 :=
    @ContinuousAt.preimage_mem_nhds G H τ σ g 0 U (@Continuous.continuousAt G H τ σ g 0 hg)
      (by rw [map_zero]; exact hU)
  obtain ⟨F, hF⟩ := hτ _ hpre
  refine ⟨F.image g, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hs y
  obtain ⟨t, ht, hxt⟩ := hF x
  exact ⟨g t, Finset.mem_image_of_mem g ht, by simpa [map_sub] using hxt⟩

/-- `λ` of the factorial chain is not precompact. -/
theorem lamC_not_precompact : ¬ PrecompactG lamC := by
  intro hP
  have hU : obs (Set.range (Mseq alpha2)) (1 / 8) ∈ @nhds TorsA lamC 0 :=
    ((basisOf (Set.range (Mseq alpha2))).nhds_zero_hasBasis).mem_of_mem
      (mem_basisOf (by norm_num : (0 : ℝ) < 1 / 8))
  obtain ⟨F, hF⟩ := hP _ hU
  choose t ht hxt using fun k : ℕ => hF (piHom (ek k))
  obtain ⟨i, j, hij, hsame⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (⟨t k, ht k⟩ : F))
  have hsame' : t i = t j := congrArg Subtype.val hsame
  -- wlog i < j
  have key : ∀ i j : ℕ, i < j → t i = t j → False := by
    intro i j hlt hs
    have h1 := hxt j (Mseq alpha2 j) ⟨j, rfl⟩
    have h2 := hxt i (Mseq alpha2 j) ⟨j, rfl⟩
    have h0 := Mj_ek_zero hlt
    have hsplit : (Mseq alpha2 j) • (((piHom (ek j) : TorsA) : Circ)) =
        (Mseq alpha2 j) • (((piHom (ek j) - t j : TorsA) : Circ)) -
          (Mseq alpha2 j) • (((piHom (ek i) - t i : TorsA) : Circ)) + (Mseq alpha2 j) • ((piHom (ek i) : TorsA) : Circ) := by
      rw [hs]
      simp only [AddSubgroup.coe_sub, smul_sub]
      abel
    rw [h0, add_zero] at hsplit
    have hn := norm_Mk_ek j
    rw [hsplit] at hn
    have := norm_sub_le ((Mseq alpha2 j) • (((piHom (ek j) - t j : TorsA) : Circ)))
      ((Mseq alpha2 j) • (((piHom (ek i) - t i : TorsA) : Circ)))
    linarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hsame'
  · exact key j i h hsame'.symm

theorem delta2_not_precompact : ¬ PrecompactG delta2 := by
  intro hP
  exact lamC_not_precompact (precompactG_image (hq 1) (hq_continuous lamC 1)
    (by intro y; obtain ⟨t, rfl⟩ := piHom_surjective y; exact ⟨t, by simp [hq_apply]⟩) hP)

/-! ### Restrictions on a greatest member -/

/-- The usual line is not precompact. -/
lemma uR_not_precompact : ¬ Precompact uR := by
  intro h
  have hmem : Set.Ioo (-1 : ℝ) 1 ∈ (𝓝 (0 : ℝ)) := Ioo_mem_nhds (by norm_num) (by norm_num)
  obtain ⟨F, hF⟩ := h (Set.Ioo (-1 : ℝ) 1) hmem
  obtain ⟨t, ht, hxt⟩ := hF (2 + ∑ s ∈ F, |s|)
  have h1 : |t| ≤ ∑ s ∈ F, |s| :=
    Finset.single_le_sum (f := fun s : ℝ => |s|) (fun s _ => abs_nonneg s) ht
  rw [Set.mem_Ioo] at hxt
  linarith [le_abs_self t, hxt.2]

/-- **Corollary 13.6 (`greatest-restrictions`), source part.**  A greatest member of `𝒞^ℚ_{f,ℚ}` is non-Baire,
nonprecompact, not locally compact, and not completely metrizable. -/
theorem greatest_restrictions {W : TopW} (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1)
    (hμ : W.t ∈ Ccls (Hq f)) (hgr : ∀ τ ∈ Ccls (Hq f), W.t ≤ τ) :
    ¬ BaireSpace (RT W.t) ∧ ¬ Precompact W.t ∧ ¬ LocallyCompactSpace (RT W.t) ∧
      ¬ TopologicalSpace.IsCompletelyMetrizableSpace (RT W.t) := by
  refine ⟨not_baire_Ccls hμ u hu, ?_, not_locallyCompact hμ.1 u hu, not_completelyMetrizable hμ.1 u hu⟩
  intro hP
  have h1 : W.t ≤ Tq f delta2 := hgr _ (Tq_mem_Ccls f u hu _ delta2_mem)
  exact uR_not_precompact (precompact_of_le (h1.trans (Tq_le_usual f delta2)) hP)

/-! ### The rational part -/

/-- A topology in `ℒ(Γ)` on `ℚ` is nondiscrete: the irrational character `q ↦ p(√2 q)` is not in `Γ`. -/
theorem rational_nondiscrete (ν : TopologicalSpace ℚ) (hν : ν ∈ Lcls Gam) : ¬ @DiscreteTopology ℚ ν := by
  intro hd
  let ψ : ℚ →+ Circ :=
    { toFun := fun q => (((Real.sqrt 2 * (q : ℝ) : ℝ)) : Circ)
      map_zero' := by simp
      map_add' := by intro a b; simp [mul_add, AddCircle.coe_add] }
  have hc : @Continuous ℚ Circ ν circTop ψ := by
    letI := ν
    haveI := hd
    exact continuous_of_discreteTopology
  obtain ⟨r, hr⟩ := (hν.2.2.2 ψ).1 hc
  have h1 : (((Real.sqrt 2 * ((1 : ℚ) : ℝ) : ℝ)) : Circ) = ((((r * 1 : ℚ) : ℝ)) : Circ) := hr 1
  have h2 : (((Real.sqrt 2 - (r : ℝ) : ℝ)) : Circ) = 0 := by
    have e : (((Real.sqrt 2 - (r : ℝ) : ℝ)) : Circ) =
        (((Real.sqrt 2 * ((1 : ℚ) : ℝ) : ℝ)) : Circ) - ((((r * 1 : ℚ) : ℝ)) : Circ) := by
      simp [AddCircle.coe_sub]
    rw [e, h1, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h2
  exact irrational_sqrt_two ⟨r + n, by push_cast; simp at hn; linarith⟩

/-- No topology in `ℒ(Γ)` has an isolated point. -/
theorem rational_no_isolated (ν : TopologicalSpace ℚ) (hν : ν ∈ Lcls Gam) (a : ℚ) :
    ¬ @IsOpen ℚ ν {a} := by
  intro ha
  letI : TopologicalSpace ℚ := ν
  haveI : IsTopologicalAddGroup ℚ := hν.1
  apply rational_nondiscrete ν hν
  have h0 : IsOpen ({0} : Set ℚ) := by
    have e : ({0} : Set ℚ) = (fun x : ℚ => x + a) ⁻¹' {a} := by ext x; simp
    rw [e]; exact ha.preimage (continuous_id.add continuous_const)
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  have e : ({x} : Set ℚ) = (fun y : ℚ => y - x) ⁻¹' {0} := by ext y; simp [sub_eq_zero]
  rw [e]; exact h0.preimage (continuous_id.sub continuous_const)

/-- A topology in `ℒ(Γ)` on `ℚ` is not a Baire space (countably many nowhere dense singletons). -/
theorem rational_not_baire (ν : TopologicalSpace ℚ) (hν : ν ∈ Lcls Gam) : ¬ @BaireSpace ℚ ν := by
  intro hB
  letI : TopologicalSpace ℚ := ν
  haveI : T2Space ℚ := hν.2.1
  obtain ⟨i, y, hy⟩ := nonempty_interior_of_iUnion_of_closed (f := fun q : ℚ => ({q} : Set ℚ))
    (fun q => isClosed_singleton) (by ext x; simp)
  have hyi : y = i := by simpa using interior_subset hy
  subst hyi
  apply rational_no_isolated ν hν y
  rw [← interior_eq_iff_isOpen]
  apply Set.Subset.antisymm interior_subset
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]; exact hy

/-- **Corollary 13.6, rational part.**  A greatest member of `𝒟_Γ` on `ℚ` is non-Baire, nonprecompact, not
locally compact, and not completely metrizable. -/
theorem greatest_rational_restrictions (ν : TopologicalSpace ℚ) (hν : ν ∈ Ccls Gam)
    (hgr : ∀ δ ∈ Ccls Gam, ν ≤ δ) :
    ¬ @BaireSpace ℚ ν ∧ ¬ PrecompactG ν ∧ ¬ @LocallyCompactSpace ℚ ν ∧
      ¬ @TopologicalSpace.IsCompletelyMetrizableSpace ℚ ν := by
  refine ⟨rational_not_baire ν hν.1, ?_, ?_, ?_⟩
  · intro hP
    exact delta2_not_precompact (precompactG_of_le (hgr _ delta2_mem) hP)
  · intro hlc
    letI : TopologicalSpace ℚ := ν
    haveI : T2Space ℚ := hν.1.2.1
    exact rational_not_baire ν hν.1 inferInstance
  · intro hcm
    letI : TopologicalSpace ℚ := ν
    exact rational_not_baire ν hν.1 inferInstance

end LeanCheck
