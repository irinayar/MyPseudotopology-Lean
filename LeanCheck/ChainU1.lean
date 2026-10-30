import LeanCheck.ChainV4

/-!
# Convergent sequences and compact sets of the modular pair (HamelCharactersTVG_v18, §14)

* `bohr_to_usual`            : a sequence that tends to `0` for the Bohr topology of `ℝ` tends to `0` usually
                                (an elementary dominated-convergence argument; no Glicksberg theorem is used);
* `beta_null_iff_sigma_null`, `conv_beta_iff`, `conv_sigma_iff`, `conv_tau_iff`  (Theorem 14.1, sequence part,
                                and Corollary 14.2): `β_f` and `σ_f` have the same convergent sequences with the same
                                limits, and the explicit tests;
* `pell_unscaled_top`         : (Corollary 14.5) the unscaled universal sequence `x_n = n!(3-2√2)^{n²}` gives a set
                                `{0, x_1, x_2, …}` that is compact for `β_f`, `σ_f` and not compact for `τ_f`;
* `finite_span_tau`, `finite_span_sigma`, `finite_span_beta`  (Theorem 14.6) and `one_dim_no_separation`,
  `two_dim_separation` (Corollary 14.7).
-/

namespace LeanCheck

open Filter Topology MeasureTheory intervalIntegral

section Sequences

lemma tendsto_beta_iff (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (u : ℕ → ℝ) :
    Tendsto u atTop (@nhds ℝ (betaT f S) 0) ↔
      (∀ b : ℝ, Tendsto (fun n => ((b * u n : ℝ) : Circ)) atTop (𝓝 0)) ∧
      ∀ a : S, Tendsto (fun n => (((f ((a : ℝ) * u n) : ℚ) : ℝ) : Circ)) atTop (𝓝 0) := by
  unfold betaT
  rw [@nhds_inf ℝ (⨅ b : ℝ, TopologicalSpace.induced (fun x : ℝ => ((b * x : ℝ) : Circ)) circTop)
    (⨅ a : S, TopologicalSpace.induced (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop) 0,
    tendsto_inf, nhds_iInf, tendsto_iInf, nhds_iInf, tendsto_iInf]
  refine and_congr (forall_congr' fun b => ?_) (forall_congr' fun a => ?_)
  · rw [nhds_induced, tendsto_comap_iff]
    simp [Function.comp_def]
    rfl
  · rw [nhds_induced, tendsto_comap_iff]
    simp [Function.comp_def]
    rfl

/-- `1 - cos(2π y)` is bounded by the square of the circle norm. -/
lemma one_sub_cos_le (y : ℝ) : 1 - Real.cos (2 * Real.pi * y) ≤ 2 * Real.pi ^ 2 * ‖(y : Circ)‖ ^ 2 := by
  rw [norm_coe_circ]
  set k : ℤ := round y with hk
  have h1 : Real.cos (2 * Real.pi * y) = Real.cos (2 * Real.pi * (y - k)) := by
    rw [show 2 * Real.pi * (y - k) = 2 * Real.pi * y - k * (2 * Real.pi) by ring,
      Real.cos_sub_int_mul_two_pi]
  rw [h1]
  have h2 := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (y - k))
  have h3 : |y - k| ^ 2 = (y - k) ^ 2 := sq_abs _
  rw [h3]
  nlinarith

/-- **A Bohr-null sequence of reals is usually null.** -/
theorem bohr_to_usual (x : ℕ → ℝ)
    (h : ∀ b : ℝ, Tendsto (fun n => ((b * x n : ℝ) : Circ)) atTop (𝓝 0)) : Tendsto x atTop (𝓝 0) := by
  by_contra hne
  rw [Metric.tendsto_nhds] at hne
  push_neg at hne
  obtain ⟨c, hc, hfreq⟩ := hne
  have hfreq' : ∃ᶠ n in atTop, c ≤ |x n| := by
    refine hfreq.mono (fun n hn => ?_)
    simpa [Real.dist_eq] using hn
  set T : ℝ := 1 / (Real.pi * c) with hT
  have hTpos : 0 < T := by positivity
  set F : ℕ → ℝ → ℝ := fun n b => 1 - Real.cos (2 * Real.pi * (b * x n)) with hF
  -- the integrals tend to `0`
  have hlim : Tendsto (fun n => ∫ b in (0 : ℝ)..T, F n b) atTop (𝓝 0) := by
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (a := 0) (b := T) (l := (atTop : Filter ℕ)) (F := F) (f := fun _ => (0 : ℝ)) (fun _ => (2 : ℝ))
      (Eventually.of_forall (fun n => by
        have : Continuous (F n) := by
          simp only [hF]; fun_prop
        exact this.aestronglyMeasurable))
      (Eventually.of_forall (fun n => Eventually.of_forall (fun b _ => by
        have h1 := Real.neg_one_le_cos (2 * Real.pi * (b * x n))
        have h2 := Real.cos_le_one (2 * Real.pi * (b * x n))
        simp only [hF, Real.norm_eq_abs]
        rw [abs_le]
        constructor <;> linarith)))
      intervalIntegrable_const
      (Eventually.of_forall (fun b _ => by
        have hb := h b
        have hnorm : Tendsto (fun n => ‖((b * x n : ℝ) : Circ)‖) atTop (𝓝 0) := by
          simpa using hb.norm
        have hsq : Tendsto (fun n => 2 * Real.pi ^ 2 * ‖((b * x n : ℝ) : Circ)‖ ^ 2) atTop (𝓝 0) := by
          have := (hnorm.pow 2).const_mul (2 * Real.pi ^ 2)
          simpa using this
        refine squeeze_zero (fun n => ?_) (fun n => one_sub_cos_le (b * x n)) hsq
        have := Real.cos_le_one (2 * Real.pi * (b * x n))
        simp only [hF]; linarith))
    simpa using this
  -- but each integral is large when `|x n| ≥ c`
  have hbig : ∀ y : ℝ, c ≤ |y| → T / 2 ≤ ∫ b in (0 : ℝ)..T, (1 - Real.cos (2 * Real.pi * (b * y))) := by
    intro y hy
    have hy0 : y ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hy; linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have hk : (2 * Real.pi * y) ≠ 0 := by positivity
    have hint : ∫ b in (0 : ℝ)..T, Real.cos (2 * Real.pi * (b * y)) =
        Real.sin (2 * Real.pi * (T * y)) / (2 * Real.pi * y) := by
      have e : ∀ b : ℝ, Real.cos (2 * Real.pi * (b * y)) = Real.cos ((2 * Real.pi * y) * b) := fun b => by
        ring_nf
      simp_rw [e]
      rw [intervalIntegral.integral_comp_mul_left (fun u => Real.cos u) hk, integral_cos]
      simp only [smul_eq_mul, mul_zero, Real.sin_zero, sub_zero]
      field_simp
    rw [intervalIntegral.integral_sub intervalIntegrable_const (by
      apply Continuous.intervalIntegrable; fun_prop), hint]
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul]
    have hs := Real.abs_sin_le_one (2 * Real.pi * (T * y))
    have hdiv : Real.sin (2 * Real.pi * (T * y)) / (2 * Real.pi * y) ≤ T / 2 := by
      have habs : |Real.sin (2 * Real.pi * (T * y)) / (2 * Real.pi * y)| ≤ 1 / (2 * Real.pi * c) := by
        rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hpi]
        have hyc : c ≤ |y| := hy
        have : 0 < 2 * Real.pi * |y| := by positivity
        calc |Real.sin (2 * Real.pi * (T * y))| / (2 * Real.pi * |y|) ≤ 1 / (2 * Real.pi * |y|) :=
              div_le_div_of_nonneg_right hs this.le
          _ ≤ 1 / (2 * Real.pi * c) := by
              apply one_div_le_one_div_of_le (by positivity)
              nlinarith
      have h2 : 1 / (2 * Real.pi * c) = T / 2 := by
        rw [hT]; field_simp
      exact (le_abs_self _).trans (habs.trans h2.le)
    linarith
  -- contradiction
  have hev : ∀ᶠ n in atTop, (∫ b in (0 : ℝ)..T, F n b) < T / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨n, hn1, hn2⟩ := (hfreq'.and_eventually hev).exists
  have := hbig (x n) hn1
  simp only [hF] at hn2
  linarith

end Sequences

section SeqConvergence

lemma tendsto_nhds_iff_sub {t : TopologicalSpace ℝ} (ht : @IsTopologicalAddGroup ℝ t _) (u : ℕ → ℝ) (x : ℝ) :
    Tendsto u atTop (@nhds ℝ t x) ↔ Tendsto (fun n => u n - x) atTop (@nhds ℝ t 0) := by
  letI := t
  haveI := ht
  exact tendsto_sub_nhds_zero_iff.symm

/-- Null sequences of `β_{f,S}` and `σ_{f,S}` coincide. -/
theorem beta_null_iff_sigma_null (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (u : ℕ → ℝ) :
    Tendsto u atTop (@nhds ℝ (betaT f S) 0) ↔ Tendsto u atTop (@nhds ℝ (sigmaT f S) 0) := by
  constructor
  · intro h
    rw [tendsto_beta_iff] at h
    rw [tendsto_sigma_iff]
    exact ⟨bohr_to_usual u h.1, h.2⟩
  · intro h
    exact h.mono_right (nhds_mono (sigmaT_le_betaT f S))

theorem sigmaT_group (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : @IsTopologicalAddGroup ℝ (sigmaT f S) _ :=
  TfS_group f S gamma0 gamma0_group

theorem tauT_group (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : @IsTopologicalAddGroup ℝ (tauT f S) _ :=
  TfS_group f S usualQ usualQ_group

/-- **Corollary 14.2 (first topology)**: convergence to `x` in `β_f` (equivalently in `σ_f`) is usual convergence
together with `‖f(a(x_n - x))‖ → 0` for all real `a`; these have the same limits. -/
theorem conv_beta_iff (f : ℝ →+ ℚ) (u : ℕ → ℝ) (x : ℝ) :
    Tendsto u atTop (@nhds ℝ (betaT f ⊤) x) ↔
      Tendsto u atTop (𝓝 x) ∧ ∀ a : ℝ, Tendsto (fun n => (((f (a * (u n - x)) : ℚ) : ℝ) : Circ)) atTop (𝓝 0) := by
  rw [tendsto_nhds_iff_sub (betaT_group f ⊤), beta_null_iff_sigma_null, tendsto_sigma_iff,
    tendsto_sub_nhds_zero_iff]
  refine and_congr Iff.rfl ⟨fun h a => h ⟨a, trivial⟩, fun h a => h a⟩

theorem conv_sigma_iff (f : ℝ →+ ℚ) (u : ℕ → ℝ) (x : ℝ) :
    Tendsto u atTop (@nhds ℝ (sigmaT f ⊤) x) ↔
      Tendsto u atTop (𝓝 x) ∧ ∀ a : ℝ, Tendsto (fun n => (((f (a * (u n - x)) : ℚ) : ℝ) : Circ)) atTop (𝓝 0) := by
  rw [tendsto_nhds_iff_sub (sigmaT_group f ⊤), tendsto_sigma_iff, tendsto_sub_nhds_zero_iff]
  refine and_congr Iff.rfl ⟨fun h a => h ⟨a, trivial⟩, fun h a => h a⟩

/-- **Corollary 14.2 (third topology)**: convergence in `τ_f` is usual convergence and `f(a(x_n - x)) → 0` in `ℚ`. -/
theorem conv_tau_iff (f : ℝ →+ ℚ) (u : ℕ → ℝ) (x : ℝ) :
    Tendsto u atTop (@nhds ℝ (tauT f ⊤) x) ↔
      Tendsto u atTop (𝓝 x) ∧ ∀ a : ℝ, Tendsto (fun n => ((f (a * (u n - x)) : ℚ) : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_nhds_iff_sub (tauT_group f ⊤), tendsto_tau_iff, tendsto_sub_nhds_zero_iff]
  refine and_congr Iff.rfl ⟨fun h a => h ⟨a, trivial⟩, fun h a => h a⟩

/-- **Theorem 14.1 (sequence part)**: `β_f` and `σ_f` have the same convergent sequences and limits. -/
theorem beta_sigma_same_sequences (f : ℝ →+ ℚ) (u : ℕ → ℝ) (x : ℝ) :
    Tendsto u atTop (@nhds ℝ (betaT f ⊤) x) ↔ Tendsto u atTop (@nhds ℝ (sigmaT f ⊤) x) := by
  rw [conv_beta_iff, conv_sigma_iff]

end SeqConvergence

section PellUnscaled

/-- **Corollary 14.5 for the unscaled universal sequence.**  For every nonzero `f`, the set
`{0, x_1, x_2, …}` with `x_n = n!(3 - 2√2)^{n²}` is compact for `σ_f` and `β_f` and not compact for `τ_f`. -/
theorem pell_unscaled_top (f : ℝ →+ ℚ) (hf : f ≠ 0) :
    Tendsto pz atTop (@nhds ℝ (sigmaT f ⊤) 0) ∧ Tendsto pz atTop (@nhds ℝ (betaT f ⊤) 0) ∧
      ¬ Tendsto pz atTop (@nhds ℝ (tauT f ⊤) 0) ∧
      @IsCompact ℝ (sigmaT f ⊤) (insert 0 (Set.range pz)) ∧
      @IsCompact ℝ (betaT f ⊤) (insert 0 (Set.range pz)) ∧
      ¬ @IsCompact ℝ (tauT f ⊤) (insert 0 (Set.range pz)) := by
  obtain ⟨hσ, hβ, hτ⟩ := pell_criterion f ⊤
  obtain ⟨u, hu⟩ : ∃ u : ℝ, f u = 1 := by
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf (AddMonoidHom.ext h)
    exact ⟨(((f x)⁻¹ : ℚ) : ℝ) * x, by rw [f_ratmul]; field_simp⟩
  have hnotτ : ¬ Tendsto pz atTop (@nhds ℝ (tauT f ⊤) 0) :=
    hτ.2 ⟨u, trivial, Or.inl (by rw [hu]; exact one_ne_zero)⟩
  have hdiv : Tendsto (fun n => |((f (u * pz n) : ℚ) : ℝ)|) atTop atTop :=
    abs_g_pz_tendsto f u (by rw [hu]; simpa using d_ne_zero 1 (f (u * Real.sqrt 2)) (Or.inl one_ne_zero))
  refine ⟨hσ, hβ, hnotτ, compact_of_tendsto' _ _ _ hσ, compact_of_tendsto' _ _ _ hβ, ?_⟩
  have hτle : tauT f ⊤ ≤ (inferInstance : TopologicalSpace ℝ) :=
    (tauT_le_sigmaT f ⊤).trans (sigmaT_le_usual f ⊤)
  have hcont := faR_cont_tau f ⊤ u trivial
  have hV : faR f u ⁻¹' Metric.ball (0 : ℝ) 1 ∈ @nhds ℝ (tauT f ⊤) 0 := by
    have := @Continuous.continuousAt ℝ ℝ (tauT f ⊤) _ (faR f u) 0 hcont
    exact this (by simpa using Metric.ball_mem_nhds (0 : ℝ) one_pos)
  refine not_compact_of_cluster (show TopologicalSpace ℝ from inferInstance) (tauT f ⊤)
    (show @T2Space ℝ (show TopologicalSpace ℝ from inferInstance) from inferInstance) hτle _ 0
    pz_tendsto_zero _ hV ?_
  filter_upwards [tendsto_atTop.1 hdiv 1] with n hn hmem
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, faR_apply, Real.norm_eq_abs] at hmem
  linarith

end PellUnscaled

end LeanCheck
