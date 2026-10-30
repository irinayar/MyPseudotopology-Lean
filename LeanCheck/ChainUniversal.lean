import LeanCheck.ChainPell

/-!
# Universal separating sequences (TVGQ-v7: `no-universal`, `finite-universal`, necessity in `universal-complete`)

A sequence `x : ℕ → ℝ` *separates* `σ_{f,S}` from `τ_{f,S}` for `f` if `x → 0` in `σ_{f,S}` but not in `τ_{f,S}`.
A *universal* sequence separates for every nonzero `f : ℝ →+ ℚ`.

* `no_universal`      : if `0 < dim_ℚ S < 𝔠`, for every sequence there is a nonzero `f` with `f(a x_n) = 0` for all `a ∈ S`;
  hence a usually null sequence is `τ_{f,S}`-null and no universal sequence exists.
* `finite_universal`  : if a sequence is `σ_{f,S}`-null for every nonzero `f` then its rational span is finite-dimensional.
* `universal_necessary`: a universal sequence forces finitely many reals `b₁,…,b_m` with `b₁S + ⋯ + b_mS = ℝ`.
-/

namespace LeanCheck

open Filter Topology

/-- All observations of a sequence vanish ⇒ it is `τ_{f,S}`-null as soon as it is usually null. -/
lemma tau_null_of_zero (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0))
    (hz : ∀ a ∈ S, ∀ n, f (a * x n) = 0) : Tendsto x atTop (@nhds ℝ (tauT f S) 0) := by
  rw [tendsto_tau_iff]
  refine ⟨hx, fun a => ?_⟩
  have : ∀ n, ((f ((a : ℝ) * x n) : ℚ) : ℝ) = 0 := fun n => by rw [hz a a.2 n]; simp
  simp [this]

/-- Cardinality obstruction: `0 < dim S < 𝔠` ⇒ every sequence is killed by some nonzero `f`. -/
theorem no_universal (S : Submodule ℚ ℝ) (hS : Module.rank ℚ S < Cardinal.continuum) (x : ℕ → ℝ) :
    ∃ g : ℝ →+ ℚ, g ≠ 0 ∧ ∀ a ∈ S, ∀ n, g (a * x n) = 0 := by
  let L : (ℕ →₀ S) →ₗ[ℚ] ℝ :=
    Finsupp.lsum ℚ (fun n : ℕ => (LinearMap.mulRight ℚ (x n)).comp S.subtype)
  let W : Submodule ℚ ℝ := LinearMap.range L
  have hW : Module.rank ℚ W ≤ Module.rank ℚ (ℕ →₀ S) := rank_range_le L
  have hfin : Module.rank ℚ (ℕ →₀ S) = Cardinal.aleph0 * Module.rank ℚ S := by
    rw [rank_finsupp]; simp
  have hlt : Module.rank ℚ W < Cardinal.continuum := by
    refine lt_of_le_of_lt hW ?_
    rw [hfin]
    exact lt_of_le_of_lt (Cardinal.mul_le_max _ _)
      (max_lt (max_lt Cardinal.aleph0_lt_continuum hS) Cardinal.aleph0_lt_continuum)
  have hne : W ≠ ⊤ := by
    intro h
    rw [h, rank_top, Real.rank_rat_real] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)
  refine ⟨φ.toAddMonoidHom, ?_, fun a ha n => ?_⟩
  · intro h0; apply hφ0; ext y; exact congrArg (fun m : ℝ →+ ℚ => m y) h0
  · have hmem : a * x n ∈ W := ⟨Finsupp.single n ⟨a, ha⟩, by simp [L, mul_comm]⟩
    exact hφ hmem

/-- **Theorem `no-universal`**: if `dim_ℚ S < 𝔠`, no sequence separates `σ_{f,S}` from `τ_{f,S}` for every nonzero `f`. -/
theorem no_universal_sequence (S : Submodule ℚ ℝ) (hS : Module.rank ℚ S < Cardinal.continuum)
    (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0)) :
    ∃ g : ℝ →+ ℚ, g ≠ 0 ∧ Tendsto x atTop (@nhds ℝ (tauT g S) 0) ∧
      Tendsto x atTop (@nhds ℝ (sigmaT g S) 0) := by
  obtain ⟨g, hg0, hz⟩ := no_universal S hS x
  have hτ := tau_null_of_zero g S x hx hz
  exact ⟨g, hg0, hτ, hτ.mono_right (nhds_mono (tauT_le_sigmaT g S))⟩

theorem no_universal_separating (S : Submodule ℚ ℝ) (hS : Module.rank ℚ S < Cardinal.continuum) :
    ¬ ∃ x : ℕ → ℝ, ∀ g : ℝ →+ ℚ, g ≠ 0 →
      Tendsto x atTop (@nhds ℝ (sigmaT g S) 0) ∧ ¬ Tendsto x atTop (@nhds ℝ (tauT g S) 0) := by
  rintro ⟨x, hx⟩
  obtain ⟨f1, hf1⟩ := exists_coefficient
  have hf10 : f1 ≠ 0 := by
    intro h0; have := congrArg (fun m : ℝ →+ ℚ => m 1) h0; simp [hf1] at this
  have hxnull : Tendsto x atTop (𝓝 0) := ((tendsto_sigma_iff f1 S x).1 (hx f1 hf10).1).1
  obtain ⟨g, hg0, hτ, -⟩ := no_universal_sequence S hS x hxnull
  exact (hx g hg0).2 hτ

/-! ### Universal modular convergence forces a finite rational span -/

lemma exists_indep_subseq (x : ℕ → ℝ) (h : ¬ FiniteDimensional ℚ (Submodule.span ℚ (Set.range x))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ LinearIndependent ℚ (x ∘ φ) := by
  classical
  obtain ⟨κ, a, hainj, hsp, hli⟩ := exists_linearIndependent' ℚ x
  have hκ : Infinite κ := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    apply h
    rw [← hsp]
    exact FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hA : (Set.range a).Infinite := Set.infinite_range_of_injective hainj
  have hA' : (setOf fun n => n ∈ Set.range a).Infinite := hA
  let φ : ℕ → ℕ := Nat.nth (fun n => n ∈ Set.range a)
  have hφmono : StrictMono φ := Nat.nth_strictMono hA'
  have hφmem : ∀ n, φ n ∈ Set.range a := fun n => Nat.nth_mem_of_infinite hA' n
  choose e he using hφmem
  have heinj : Function.Injective e := by
    intro n m hnm
    apply hφmono.injective
    rw [← he n, ← he m, hnm]
  refine ⟨φ, hφmono, ?_⟩
  have : (x ∘ φ) = (x ∘ a) ∘ e := by
    funext n; simp [Function.comp, he n]
  rw [this]
  exact hli.comp e heinj

theorem finite_universal (S : Submodule ℚ ℝ) (hS : ∃ a ∈ S, a ≠ 0) (x : ℕ → ℝ)
    (hx : ∀ g : ℝ →+ ℚ, g ≠ 0 → Tendsto x atTop (@nhds ℝ (sigmaT g S) 0)) :
    FiniteDimensional ℚ (Submodule.span ℚ (Set.range x)) := by
  by_contra hfd
  obtain ⟨φ, hφ, hli⟩ := exists_indep_subseq x hfd
  obtain ⟨a₀, ha₀, ha₀ne⟩ := hS
  -- `v j = a₀ x_{φ j}` is linearly independent
  let v : ℕ → ℝ := fun j => a₀ * x (φ j)
  have hv : LinearIndependent ℚ v := by
    have hinj : LinearMap.ker (LinearMap.mulLeft ℚ a₀) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro y z h
      exact mul_left_cancel₀ ha₀ne h
    exact hli.map' (LinearMap.mulLeft ℚ a₀) hinj
  -- a functional taking the value `1/2` on every `v j`
  let f0 : Submodule.span ℚ (Set.range v) →ₗ[ℚ] ℚ :=
    (Finsupp.linearCombination ℚ (fun _ : ℕ => (1 / 2 : ℚ))).comp hv.repr
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f0
  have hgv : ∀ j, g (v j) = 1 / 2 := by
    intro j
    have := congrArg (fun m => m ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    simp [f0, hv.repr_eq_single j ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩ rfl]
  have hg0 : g.toAddMonoidHom ≠ 0 := by
    intro h0
    have := congrArg (fun m : ℝ →+ ℚ => m (v 0)) h0
    simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.zero_apply, hgv 0] at this
    norm_num at this
  have hconv := (tendsto_sigma_iff g.toAddMonoidHom S x).1 (hx _ hg0)
  have h1 := (hconv.2 ⟨a₀, ha₀⟩).comp hφ.tendsto_atTop
  have h2 : ∀ j, (((g.toAddMonoidHom (a₀ * x (φ j)) : ℚ) : ℝ) : Circ) = (((1 / 2 : ℚ) : ℝ) : Circ) := by
    intro j
    have := hgv j
    simp only [v] at this
    simp [this]
  simp only [Function.comp_def, h2] at h1
  have h3 : (((1 / 2 : ℚ) : ℝ) : Circ) = 0 := tendsto_nhds_unique tendsto_const_nhds h1
  rw [AddCircle.coe_eq_zero_iff] at h3
  obtain ⟨m, hm⟩ := h3
  rw [zsmul_eq_mul, mul_one] at hm
  push_cast at hm
  have : (2 : ℝ) * m = 1 := by linarith
  have h4 : (2 : ℤ) * m = 1 := by exact_mod_cast this
  omega

/-- **Necessity in `universal-complete`**: a universal separating sequence gives finitely many reals
`b_t` (`t ∈ T`) with `∑ b_t S = ℝ`. -/
theorem universal_necessary (S : Submodule ℚ ℝ) (hS : ∃ a ∈ S, a ≠ 0) (x : ℕ → ℝ)
    (hx : ∀ g : ℝ →+ ℚ, g ≠ 0 →
      Tendsto x atTop (@nhds ℝ (sigmaT g S) 0) ∧ ¬ Tendsto x atTop (@nhds ℝ (tauT g S) 0)) :
    ∃ T : Finset ℝ, (⨆ t : T, S.map (LinearMap.mulLeft ℚ (t : ℝ))) = ⊤ := by
  classical
  have hfd := finite_universal S hS x (fun g hg => (hx g hg).1)
  obtain ⟨T, hT⟩ := (Submodule.fg_iff_finiteDimensional _).2 hfd
  refine ⟨T, ?_⟩
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hg0 : φ.toAddMonoidHom ≠ 0 := by
    intro h0; apply hφ0; ext y; exact congrArg (fun m : ℝ →+ ℚ => m y) h0
  have hsp : ∀ a ∈ S, ∀ w ∈ Submodule.span ℚ (T : Set ℝ), φ (a * w) = 0 := by
    intro a ha w hw
    induction hw using Submodule.span_induction with
    | mem t ht =>
      have : a * t ∈ ⨆ t : T, S.map (LinearMap.mulLeft ℚ (t : ℝ)) :=
        Submodule.mem_iSup_of_mem ⟨t, ht⟩ ⟨a, ha, by simp [mul_comm]⟩
      exact hφ this
    | zero => simp
    | add u u' _ _ hu hu' => rw [mul_add, map_add, hu, hu', add_zero]
    | smul c u _ hu =>
      rw [mul_smul_comm, map_smul, hu, smul_zero]
  have hxsp : ∀ n, x n ∈ Submodule.span ℚ (T : Set ℝ) := fun n => by
    rw [hT]; exact Submodule.subset_span ⟨n, rfl⟩
  have hnull : Tendsto x atTop (𝓝 0) := by
    obtain ⟨f1, hf1⟩ := exists_coefficient
    have hf10 : f1 ≠ 0 := by
      intro h0; have := congrArg (fun m : ℝ →+ ℚ => m 1) h0; simp [hf1] at this
    exact ((tendsto_sigma_iff f1 S x).1 (hx f1 hf10).1).1
  exact (hx _ hg0).2 (tau_null_of_zero _ S x hnull (fun a ha n => hsp a ha (x n) (hxsp n)))

end LeanCheck
