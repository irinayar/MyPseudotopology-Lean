import LeanCheck.ChainG1

/-!
# Infinite-dimensional convergence depends on the functional
(TVGadd-v2 Theorem `seq:dependence`)

For a transcendental `t ∈ (0,1)` there are nonzero rational-linear `f, g : ℝ → ℚ` such that the (rationally independent) sequence
`t^n` tends to zero in `τ_f` (hence in `σ_f`, `β_f`) but not in any of `τ_g`, `σ_g`, `β_g`.

The functional `f` is `ℓ ∘ Π`, where `K = ℚ(t)`, `Π : ℝ → K` is a `K`-linear projection with `Π 1 = 1`, and `ℓ : K → ℚ` is
a rational-linear functional with `ℓ 1 ≠ 0` that vanishes on the elements of positive `t`-adic order, i.e. on the elements
`t p(t) / r(t)` with `r(0) ≠ 0`.
-/

namespace LeanCheck

open Filter Topology Polynomial

section Decay

lemma aeval_ne_zero_of_eval {t : ℝ} (ht : Transcendental ℚ t) {r : ℚ[X]} (hr : r.eval 0 ≠ 0) : aeval t r ≠ 0 := by
  intro h
  have : r = 0 := by
    by_contra hne
    exact ht ⟨r, hne, h⟩
  rw [this] at hr
  simp at hr

/-- Elements of positive `t`-adic order, as a rational subspace of `K = ℚ(t)`. -/
noncomputable def posOrder (t : ℝ) (ht : Transcendental ℚ t) :
    Submodule ℚ (IntermediateField.adjoin ℚ ({t} : Set ℝ)) where
  carrier := {y | ∃ p r : ℚ[X], r.eval 0 ≠ 0 ∧ (y : ℝ) = t * aeval t p / aeval t r}
  zero_mem' := ⟨0, 1, by simp, by simp⟩
  add_mem' := by
    rintro y z ⟨p1, r1, hr1, hy⟩ ⟨p2, r2, hr2, hz⟩
    refine ⟨p1 * r2 + p2 * r1, r1 * r2, ?_, ?_⟩
    · simp [Polynomial.eval_mul, hr1, hr2]
    · have h1 := aeval_ne_zero_of_eval ht hr1
      have h2 := aeval_ne_zero_of_eval ht hr2
      simp only [IntermediateField.coe_add, hy, hz, map_add, map_mul]
      field_simp
  smul_mem' := by
    rintro c y ⟨p, r, hr, hy⟩
    refine ⟨Polynomial.C c * p, r, hr, ?_⟩
    have e : ((c • y : IntermediateField.adjoin ℚ ({t} : Set ℝ)) : ℝ) = (c : ℝ) * (y : ℝ) := by
      simp [Rat.smul_def]
    rw [e, hy]
    simp [map_mul, Polynomial.aeval_C]
    ring

lemma one_not_mem_posOrder {t : ℝ} (ht : Transcendental ℚ t) :
    (1 : IntermediateField.adjoin ℚ ({t} : Set ℝ)) ∉ posOrder t ht := by
  rintro ⟨p, r, hr, h⟩
  have hr' := aeval_ne_zero_of_eval ht hr
  have h2 : aeval t r = t * aeval t p := by
    simp only [IntermediateField.coe_one] at h
    field_simp at h
    linarith
  have h3 : r = X * p := by
    by_contra hne
    exact ht ⟨r - X * p, sub_ne_zero.2 hne, by simp [h2]⟩
  rw [h3] at hr
  simp at hr

lemma eventually_posOrder {t : ℝ} (ht : Transcendental ℚ t)
    (y : IntermediateField.adjoin ℚ ({t} : Set ℝ)) :
    ∃ N : ℕ, ∀ n ≥ N, (⟨t, IntermediateField.mem_adjoin_simple_self ℚ t⟩ :
      IntermediateField.adjoin ℚ ({t} : Set ℝ)) ^ n * y ∈ posOrder t ht := by
  obtain ⟨r, s, hy⟩ := (IntermediateField.mem_adjoin_simple_iff (F := ℚ) (α := t) (y : ℝ)).1 y.2
  by_cases hs : s = 0
  · refine ⟨0, fun n _ => ?_⟩
    have : (y : ℝ) = 0 := by rw [hy, hs]; simp
    have hy0 : y = 0 := Subtype.ext this
    rw [hy0, mul_zero]; exact (posOrder t ht).zero_mem
  · obtain ⟨q, hsq, hqd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd s hs 0
    set e := Polynomial.rootMultiplicity 0 s with he
    have hq0 : q.eval 0 ≠ 0 := by
      intro h0
      apply hqd
      simp only [map_zero, sub_zero]
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      exact h0
    refine ⟨e + 1, fun n hn => ?_⟩
    refine ⟨X ^ (n - e - 1) * r, q, hq0, ?_⟩
    have hq' := aeval_ne_zero_of_eval ht hq0
    have ht0 : t ≠ 0 := ht.ne_zero
    have hn' : n = e + 1 + (n - e - 1) := by omega
    simp only [IntermediateField.coe_mul, IntermediateField.coe_pow, hy, hsq, map_mul, map_pow, aeval_X]
    simp only [map_sub, aeval_X, map_zero, sub_zero] 
    have hte : t ^ e ≠ 0 := pow_ne_zero _ ht0
    have : t ^ n = t ^ e * t * t ^ (n - e - 1) := by
      conv_lhs => rw [hn', pow_add, pow_add]
      ring
    rw [this]
    field_simp

/-- A nonzero rational-linear `f : ℝ → ℚ` with `f (a t^n) = 0` eventually, for every real `a`. -/
lemma exists_decay_functional {t : ℝ} (ht : Transcendental ℚ t) :
    ∃ f : ℝ →+ ℚ, f ≠ 0 ∧ ∀ a : ℝ, ∀ᶠ n in atTop, f (a * t ^ n) = 0 := by
  set K := IntermediateField.adjoin ℚ ({t} : Set ℝ) with hK
  obtain ⟨ℓ, hℓ1, hℓm⟩ := Submodule.exists_le_ker_of_notMem (one_not_mem_posOrder ht)
  let ι : K →ₗ[K] ℝ := LinearMap.toSpanSingleton K ℝ 1
  have hι : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro c d h
    have h' : (c : ℝ) = (d : ℝ) := by
      have := h
      simpa [ι, LinearMap.toSpanSingleton_apply, Algebra.smul_def] using this
    exact Subtype.ext h'
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective ι hι
  have hP1 : P 1 = 1 := by
    have := congrArg (fun m : K →ₗ[K] K => m 1) hP
    simpa [ι] using this
  let f0 : ℝ →ₗ[ℚ] ℚ := ℓ.comp (P.restrictScalars ℚ)
  refine ⟨f0.toAddMonoidHom, ?_, fun a => ?_⟩
  · intro h0
    have := congrArg (fun m : ℝ →+ ℚ => m 1) h0
    simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.zero_apply, f0, LinearMap.comp_apply,
      LinearMap.coe_restrictScalars, hP1] at this
    exact hℓ1 this
  · obtain ⟨N, hN⟩ := eventually_posOrder ht (P a)
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have e1 : a * t ^ n = ((⟨t, IntermediateField.mem_adjoin_simple_self ℚ t⟩ : K) ^ n) • a := by
      rw [Algebra.smul_def]
      simp [mul_comm]
    have e2 : P (a * t ^ n) = (⟨t, IntermediateField.mem_adjoin_simple_self ℚ t⟩ : K) ^ n * P a := by
      rw [e1, map_smul, smul_eq_mul]
    show ℓ (P (a * t ^ n)) = 0
    rw [e2]
    exact hℓm (hN n hn)

end Decay

section Half

/-- A rational-linear functional with value `1/2` on every member of a linearly independent sequence. -/
lemma exists_half_functional (v : ℕ → ℝ) (hv : LinearIndependent ℚ v) :
    ∃ g : ℝ →+ ℚ, g ≠ 0 ∧ ∀ j, g (v j) = 1 / 2 := by
  let f0 : Submodule.span ℚ (Set.range v) →ₗ[ℚ] ℚ :=
    (Finsupp.linearCombination ℚ (fun _ : ℕ => (1 / 2 : ℚ))).comp hv.repr
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f0
  have hgv : ∀ j, g (v j) = 1 / 2 := by
    intro j
    have := congrArg (fun m => m ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    simp [f0, hv.repr_eq_single j ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩ rfl]
  refine ⟨g.toAddMonoidHom, ?_, hgv⟩
  intro h0
  have := congrArg (fun m : ℝ →+ ℚ => m (v 0)) h0
  simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.zero_apply, hgv 0] at this
  norm_num at this

end Half

section Dependence

lemma exists_transcendental_unit : ∃ t : ℝ, Transcendental ℚ t ∧ 0 < t ∧ t < 1 := by
  set x := liouvilleNumber 2 with hxdef
  have hx : Transcendental ℚ x := fun h =>
    transcendental_liouvilleNumber (le_refl 2) ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).2 h)
  have hx1 : 1 < x := by
    have h := LiouvilleNumber.partialSum_add_remainder (m := 2) (by norm_num) 1
    have hr := LiouvilleNumber.remainder_pos (m := 2) (by norm_num) 1
    have hp : LiouvilleNumber.partialSum 2 1 = 1 := by
      simp [LiouvilleNumber.partialSum, Finset.sum_range_succ]; norm_num
    rw [hp] at h
    linarith
  exact ⟨x⁻¹, fun h => hx (IsAlgebraic.inv_iff.1 h), by positivity, inv_lt_one_of_one_lt₀ hx1⟩

lemma linearIndependent_pow {t : ℝ} (ht : Transcendental ℚ t) : LinearIndependent ℚ (fun n : ℕ => t ^ n) := by
  have hinj : Function.Injective (Polynomial.aeval (R := ℚ) t) := transcendental_iff_injective.1 ht
  have h := (Polynomial.basisMonomials ℚ).linearIndependent.map' (Polynomial.aeval (R := ℚ) t).toLinearMap
    (LinearMap.ker_eq_bot.2 hinj)
  convert h using 1
  funext n
  simp [Polynomial.coe_basisMonomials, Polynomial.aeval_monomial]

/-- **TVGadd-v2 Theorem `seq:dependence`.**  There are nonzero rational-linear `f, g : ℝ → ℚ` and a rationally independent sequence `x`
that tends to zero in `τ_f` (hence in `σ_f` and `β_f`) but in none of `τ_g`, `σ_g`, `β_g`. -/
theorem seq_dependence :
    ∃ (f g : ℝ →+ ℚ) (x : ℕ → ℝ), f ≠ 0 ∧ g ≠ 0 ∧ LinearIndependent ℚ x ∧
      Tendsto x atTop (@nhds ℝ (tauT f ⊤) 0) ∧ Tendsto x atTop (@nhds ℝ (sigmaT f ⊤) 0) ∧
      Tendsto x atTop (@nhds ℝ (betaT f ⊤) 0) ∧
      ¬ Tendsto x atTop (@nhds ℝ (tauT g ⊤) 0) ∧ ¬ Tendsto x atTop (@nhds ℝ (sigmaT g ⊤) 0) ∧
      ¬ Tendsto x atTop (@nhds ℝ (betaT g ⊤) 0) := by
  obtain ⟨t, ht, ht0, ht1⟩ := exists_transcendental_unit
  obtain ⟨f, hf, hdec⟩ := exists_decay_functional ht
  obtain ⟨g, hg, hgv⟩ := exists_half_functional _ (linearIndependent_pow ht)
  have hτ : Tendsto (fun n : ℕ => t ^ n) atTop (@nhds ℝ (tauT f ⊤) 0) := by
    refine (conv_tau_iff f (fun n : ℕ => t ^ n) 0).2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one ht0.le ht1, fun a => ?_⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hdec a] with n hn
    simp [hn]
  have hσ : Tendsto (fun n : ℕ => t ^ n) atTop (@nhds ℝ (sigmaT f ⊤) 0) :=
    (@Continuous.tendsto ℝ ℝ (tauT f ⊤) (sigmaT f ⊤) id
      (@continuous_id_of_le ℝ (tauT f ⊤) (sigmaT f ⊤) (tauT_le_sigmaT f ⊤)) 0).comp hτ
  have hnτ : ¬ Tendsto (fun n : ℕ => t ^ n) atTop (@nhds ℝ (tauT g ⊤) 0) := by
    intro h
    have h1 := ((conv_tau_iff g (fun n : ℕ => t ^ n) 0).1 h).2 1
    have h2 : (fun n : ℕ => (((g (1 * (t ^ n - 0)) : ℚ) : ℝ))) = fun _ => (1 / 2 : ℝ) := by
      funext n
      have := hgv n
      simp only [one_mul, sub_zero]
      rw [this]; norm_num
    rw [h2] at h1
    have := tendsto_nhds_unique tendsto_const_nhds h1
    norm_num at this
  have hnσ : ¬ Tendsto (fun n : ℕ => t ^ n) atTop (@nhds ℝ (sigmaT g ⊤) 0) := by
    intro h
    have h1 := ((conv_sigma_iff g (fun n : ℕ => t ^ n) 0).1 h).2 1
    have h2 : (fun n : ℕ => (((g (1 * (t ^ n - 0)) : ℚ) : ℝ) : Circ)) = fun _ => (((1 / 2 : ℝ)) : Circ) := by
      funext n
      have := hgv n
      simp only [one_mul, sub_zero]
      rw [this]; norm_num
    rw [h2] at h1
    exact half_ne_zero_circ (tendsto_nhds_unique tendsto_const_nhds h1)
  exact ⟨f, g, fun n => t ^ n, hf, hg, linearIndependent_pow ht, hτ, hσ,
    (beta_null_iff_sigma_null f ⊤ _).2 hσ, hnτ, hnσ, fun h => hnσ ((beta_null_iff_sigma_null g ⊤ _).1 h)⟩

end Dependence

end LeanCheck
