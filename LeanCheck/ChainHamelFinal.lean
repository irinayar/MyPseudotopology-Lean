import LeanCheck.ChainHamelScalar

/-!
# Remaining Hamel-side facts: non-discreteness, `β_{f,S}` is unbounded (precompact behaviour), incomparability with
the usual topology, `Hom_cont(β, ℝ) = 0`, and the scalar-ring corollaries.
-/

namespace LeanCheck

open Filter Topology

/-! ### Non-discreteness -/

/-- `0` is not isolated in `TfS f S δ` when `δ`-neighbourhoods of `0` are arbitrary: every basic neighbourhood
contains a nonzero real number (the joint kernel of the `f_a` is dense). -/
theorem TfS_not_isolated (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ) :
    ({0} : Set ℝ) ∉ @nhds ℝ (TfS f S δ) 0 := by
  classical
  intro h
  obtain ⟨ε, hε, I, hIS, U, hU, hsub⟩ := tfS_nhds_sub f S δ _ h
  let fam : I → (ℝ →+ ℚ) := fun a => fa f (a : ℝ)
  obtain ⟨z, hzN, hz⟩ := (HkerG_dense fam).exists_mem_open
    (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) ε)) ⟨ε / 2, by constructor <;> linarith⟩
  have hz0 : ∀ a : I, f ((a : ℝ) * z) = 0 := fun a => by
    have := congrFun (AddMonoidHom.mem_ker.mp hzN) a
    simpa [HmapG_apply, fam, fa_apply] using this
  have hzmem : z ∈ ({0} : Set ℝ) := by
    apply hsub
    refine ⟨?_, fun a ha => ?_⟩
    · rw [abs_of_pos hz.1]; exact hz.2
    · rw [hz0 ⟨a, ha⟩]; exact mem_of_mem_nhds (hU a ha)
  exact absurd (Set.mem_singleton_iff.mp hzmem) hz.1.ne'

theorem sigmaT_not_isolated (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : ({0} : Set ℝ) ∉ @nhds ℝ (sigmaT f S) 0 :=
  TfS_not_isolated f S gamma0

theorem tauT_not_isolated (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : ({0} : Set ℝ) ∉ @nhds ℝ (tauT f S) 0 :=
  TfS_not_isolated f S usualQ

/-- `β_{f,S}` is non-discrete (it is coarser than `σ_{f,S}`). -/
theorem betaT_not_isolated (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : ({0} : Set ℝ) ∉ @nhds ℝ (betaT f S) 0 := by
  intro h
  exact sigmaT_not_isolated f S ((nhds_mono (sigmaT_le_betaT f S)) h)

/-! ### Neighbourhoods of `β_{f,S}` -/

lemma nhds_iInf_induced_circ {J : Type} (Ψ : J → ℝ → Circ) (hΨ : ∀ i, Ψ i 0 = 0) (V : Set ℝ)
    (hV : V ∈ @nhds ℝ (⨅ i, TopologicalSpace.induced (Ψ i) circTop) 0) :
    ∃ I : Finset J, ∃ W : J → Set Circ, (∀ i, W i ∈ 𝓝 (0 : Circ)) ∧
      {x : ℝ | ∀ i ∈ I, Ψ i x ∈ W i} ⊆ V := by
  classical
  rw [nhds_iInf] at hV
  obtain ⟨I, hI, T, hT, -, hs⟩ := Filter.mem_iInf'.mp hV
  have hex : ∀ i : J, ∃ W : Set Circ, W ∈ 𝓝 (0 : Circ) ∧ Ψ i ⁻¹' W ⊆ T i := by
    intro i
    have h := hT i
    rw [nhds_induced] at h
    obtain ⟨W, hW, hWT⟩ := Filter.mem_comap.mp h
    refine ⟨W, ?_, hWT⟩
    have e : Ψ i 0 = 0 := hΨ i
    rw [e] at hW
    exact hW
  choose W hW hWT using hex
  refine ⟨hI.toFinset, W, hW, fun x hx => ?_⟩
  rw [hs.1]
  refine Set.mem_iInter₂.mpr (fun i hi => ?_)
  exact hWT i (hx i (hI.mem_toFinset.mpr hi))

theorem beta_nhds_sub (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (V : Set ℝ) (hV : V ∈ @nhds ℝ (betaT f S) 0) :
    ∃ (I1 : Finset ℝ) (W1 : ℝ → Set Circ) (I2 : Finset S) (W2 : S → Set Circ),
      (∀ b, W1 b ∈ 𝓝 (0 : Circ)) ∧ (∀ a, W2 a ∈ 𝓝 (0 : Circ)) ∧
      {x : ℝ | (∀ b ∈ I1, ((b * x : ℝ) : Circ) ∈ W1 b) ∧
        ∀ a ∈ I2, (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ) ∈ W2 a} ⊆ V := by
  have hV2 : V ∈ @nhds ℝ ((⨅ b : ℝ, TopologicalSpace.induced (fun x : ℝ => ((b * x : ℝ) : Circ)) circTop) ⊓
      ⨅ a : S, TopologicalSpace.induced (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop) 0 := hV
  have hinf := @nhds_inf ℝ (⨅ b : ℝ, TopologicalSpace.induced (fun x : ℝ => ((b * x : ℝ) : Circ)) circTop)
    (⨅ a : S, TopologicalSpace.induced (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop) 0
  rw [hinf] at hV2
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_inf_iff_superset.mp hV2
  obtain ⟨I1, W1, hW1, hs1⟩ := nhds_iInf_induced_circ (fun (b : ℝ) (x : ℝ) => ((b * x : ℝ) : Circ))
    (fun b => by simp) t1 ht1
  obtain ⟨I2, W2, hW2, hs2⟩ := nhds_iInf_induced_circ
    (fun (a : S) (x : ℝ) => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) (fun a => by simp) t2 ht2
  exact ⟨I1, W1, I2, W2, hW1, hW2, fun x hx => hsub ⟨hs1 hx.1, hs2 hx.2⟩⟩

/-! ### `β_{f,S}` is "precompact": every neighbourhood of `0` is unbounded -/

/-- The joint character map `ℝ → (I1 → 𝕋) × (I2 → 𝕋)`. -/
noncomputable def PhiB (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (I1 : Finset ℝ) (I2 : Finset S) :
    ℝ →+ ((I1 → Circ) × (I2 → Circ)) where
  toFun x := (fun b => ((b.1 * x : ℝ) : Circ), fun a => (((f ((a.1 : ℝ) * x) : ℚ) : ℝ) : Circ))
  map_zero' := by
    ext <;> simp
  map_add' x y := by
    ext
    · simp [mul_add, AddCircle.coe_add]
    · simp [mul_add, AddCircle.coe_add]

/-- **Unboundedness of `β_{f,S}`-neighbourhoods**: every neighbourhood of `0` contains reals of arbitrarily large
absolute value (pigeonhole in the compact torus). -/
theorem beta_unbounded (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (V : Set ℝ) (hV : V ∈ @nhds ℝ (betaT f S) 0)
    (B : ℝ) : ∃ x ∈ V, B < |x| := by
  classical
  obtain ⟨I1, W1, I2, W2, hW1, hW2, hsub⟩ := beta_nhds_sub f S V hV
  set N : ℝ := max B 0 + 1 with hN
  have hNpos : 0 < N := by positivity
  let s : ℕ → (I1 → Circ) × (I2 → Circ) := fun n => PhiB f S I1 I2 ((n : ℝ) * N)
  obtain ⟨L, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (fun n => Set.mem_univ (s n))
  let U : Set ((I1 → Circ) × (I2 → Circ)) :=
    (Set.pi Set.univ (fun b : I1 => W1 b.1)) ×ˢ (Set.pi Set.univ (fun a : I2 => W2 a.1))
  have hU : U ∈ 𝓝 (0 : (I1 → Circ) × (I2 → Circ)) := by
    refine prod_mem_nhds ?_ ?_
    · exact set_pi_mem_nhds Set.finite_univ (fun b _ => hW1 b.1)
    · exact set_pi_mem_nhds Set.finite_univ (fun a _ => hW2 a.1)
  have hdiff : Tendsto (fun n => s (φ (n + 1)) - s (φ n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => s (φ (n + 1))) atTop (𝓝 L) :=
      (tendsto_add_atTop_iff_nat 1).2 hlim
    have := h1.sub hlim
    simpa using this
  obtain ⟨n, hn⟩ := (hdiff.eventually hU).exists
  have hlt : φ n < φ (n + 1) := hφ (Nat.lt_succ_self n)
  set m : ℕ := φ (n + 1) - φ n with hm
  have hm1 : 1 ≤ m := by omega
  have hcast : ((m : ℕ) : ℝ) = (φ (n + 1) : ℝ) - φ n := by
    rw [hm, Nat.cast_sub hlt.le]
  refine ⟨(m : ℝ) * N, hsub ⟨fun b hb => ?_, fun a ha => ?_⟩, ?_⟩
  · have := hn.1 ⟨b, hb⟩ (Set.mem_univ _)
    have e : (s (φ (n + 1)) - s (φ n)).1 ⟨b, hb⟩ = ((b * ((m : ℝ) * N) : ℝ) : Circ) := by
      simp only [s, PhiB, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_sub, Pi.sub_apply]
      rw [← AddCircle.coe_sub, hcast]; congr 1; ring
    rw [e] at this
    exact this
  · have := hn.2 ⟨a, ha⟩ (Set.mem_univ _)
    have e : (s (φ (n + 1)) - s (φ n)).2 ⟨a, ha⟩ =
        (((f ((a : ℝ) * ((m : ℝ) * N)) : ℚ) : ℝ) : Circ) := by
      simp only [s, PhiB, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.snd_sub, Pi.sub_apply]
      rw [← AddCircle.coe_sub, ← Rat.cast_sub, ← map_sub, ← mul_sub, hcast]
      congr 3; ring
    rw [e] at this
    exact this
  · rw [abs_of_nonneg (by positivity)]
    have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have : max B 0 + 1 ≤ (m : ℝ) * N := by nlinarith
    linarith [le_max_left B 0]

/-- `β_{f,S}` is incomparable with the usual topology (for `S ≠ 0`). -/
theorem beta_not_le_usual (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    ¬ betaT f S ≤ (inferInstance : TopologicalSpace ℝ) := by
  intro hle
  have hid : Continuous[betaT f S, (inferInstance : TopologicalSpace ℝ)] (id : ℝ → ℝ) :=
    continuous_iff_le_induced.mpr (by rw [induced_id]; exact hle)
  have hpre : (id : ℝ → ℝ) ⁻¹' Set.Ioo (-1 : ℝ) 1 ∈ @nhds ℝ (betaT f S) 0 :=
    (@Continuous.continuousAt ℝ ℝ (betaT f S) _ id 0 hid) (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨x, hxV, hxB⟩ := beta_unbounded f S _ hpre 1
  have h1 : |x| < 1 := abs_lt.mpr ⟨hxV.1, hxV.2⟩
  linarith

theorem usual_not_le_beta (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) (a : ℝ) (haS : a ∈ S)
    (ha : a ≠ 0) : ¬ (inferInstance : TopologicalSpace ℝ) ≤ betaT f S := by
  intro hle
  exact pfHom_not_usual f u hu a ha (continuous_le_dom hle (pfHom_cont_beta f S ⟨a, haS⟩))

/-- `Hom_cont((ℝ, β_{f,S}), ℝ_usual) = 0`. -/
theorem dual_beta_real (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) (g : ℝ →+ ℝ)
    (hg : Continuous[betaT f S, (inferInstance : TopologicalSpace ℝ)] g) : ∀ x : ℝ, g x = 0 := by
  have hgσ : Continuous[sigmaT f S, (inferInstance : TopologicalSpace ℝ)] g :=
    continuous_le_dom (sigmaT_le_betaT f S) hg
  obtain ⟨c, hc⟩ := (dual_sigma_real f u hu S g).mp hgσ
  have hc0 : c = 0 := by
    by_contra hne
    have hpre : g ⁻¹' Set.Ioo (-1 : ℝ) 1 ∈ @nhds ℝ (betaT f S) 0 :=
      (@Continuous.continuousAt ℝ ℝ (betaT f S) _ g 0 hg)
        (by rw [map_zero]; exact Ioo_mem_nhds (by norm_num) (by norm_num))
    obtain ⟨x, hxV, hxB⟩ := beta_unbounded f S _ hpre (2 / |c|)
    have h1 : |g x| < 1 := abs_lt.mpr ⟨hxV.1, hxV.2⟩
    rw [hc x, abs_mul] at h1
    have hcpos : 0 < |c| := abs_pos.mpr hne
    have : 2 < |c| * |x| := by
      rw [div_lt_iff₀ hcpos] at hxB; linarith
    linarith
  intro x
  rw [hc x, hc0, zero_mul]

/-! ### Scalar rings: algebras -/

/-- Every unital `ℚ`-subalgebra `A ⊆ ℝ` occurs as the exact scalar ring: `M(A) = A`. -/
theorem scalarRing_algebra (A : Subalgebra ℚ ℝ) : scalarRing (Subalgebra.toSubmodule A) = (A : Set ℝ) := by
  ext r
  constructor
  · intro hr
    have := hr 1 A.one_mem
    simpa using this
  · intro hr a ha
    exact A.mul_mem ha hr

/-! ### Proposition `basic`, collected -/

/-- **Proposition `basic`**: for a nonzero `ℚ`-subspace `S`, the three topologies are Hausdorff, non-discrete group
topologies with continuous rational dilations, and `τ ⊆ … ` i.e. `τ_{f,S} ≤ σ_{f,S} ≤ β_{f,S}` with
`σ_{f,S} = tu ∨ β_{f,S}`. -/
theorem hamel_prop_basic (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    -- group topologies
    @IsTopologicalAddGroup ℝ (betaT f S) _ ∧ @IsTopologicalAddGroup ℝ (sigmaT f S) _ ∧
    @IsTopologicalAddGroup ℝ (tauT f S) _ ∧
    -- Hausdorff
    @T2Space ℝ (betaT f S) ∧ @T2Space ℝ (sigmaT f S) ∧ @T2Space ℝ (tauT f S) ∧
    -- non-discrete
    ({0} : Set ℝ) ∉ @nhds ℝ (betaT f S) 0 ∧ ({0} : Set ℝ) ∉ @nhds ℝ (sigmaT f S) 0 ∧
    ({0} : Set ℝ) ∉ @nhds ℝ (tauT f S) 0 ∧
    -- rational dilations
    (∀ q : ℚ, Continuous[betaT f S, betaT f S] (fun x : ℝ => (q : ℝ) * x)) ∧
    (∀ q : ℚ, Continuous[sigmaT f S, sigmaT f S] (fun x : ℝ => (q : ℝ) * x)) ∧
    (∀ q : ℚ, Continuous[tauT f S, tauT f S] (fun x : ℝ => (q : ℝ) * x)) ∧
    -- inclusions and σ = tu ∨ β
    tauT f S ≤ sigmaT f S ∧ sigmaT f S ≤ betaT f S ∧
    sigmaT f S = (inferInstance : TopologicalSpace ℝ) ⊓ betaT f S := by
  have hq : ∀ q : ℚ, (q : ℝ) ∈ scalarRing S := fun q a ha => by
    have := S.smul_mem q ha
    simpa [Rat.smul_def, mul_comm] using this
  refine ⟨betaT_group f S, TfS_group f S gamma0 gamma0_group, TfS_group f S usualQ usualQ_group,
    betaT_t2 f S, TfS_t2 f S gamma0, TfS_t2 f S usualQ,
    betaT_not_isolated f S, sigmaT_not_isolated f S, tauT_not_isolated f S,
    fun q => betaT_dilation f S q (hq q), fun q => TfS_ratdil f S gamma0 q,
    fun q => TfS_ratdil f S usualQ q, tauT_le_sigmaT f S, sigmaT_le_betaT f S, sigmaT_eq f S⟩

end LeanCheck
