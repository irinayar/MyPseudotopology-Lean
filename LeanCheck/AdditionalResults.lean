import LeanCheck.ChainHamelFinal

/-!
Additional results for TVGadd. No nuclear-group predicate is defined here:
the external Glicksberg theorem is NOT assumed as an axiom. The compactness
hypothesis below is explicit, and its application to nuclear groups remains external.
-/
namespace LeanCheck
open Filter Topology

/-- A finer topology preserving compact sets of a Hausdorff compactly generated
coarser topology must coincide with it. This is the topological core of Proposition 5.1. -/
theorem topology_eq_of_compact_preservation {X : Type*}
    (w rho : TopologicalSpace X) (hfine : rho ≤ w)
    (hHaus : @T2Space X w) (hgen : @CompactlyGeneratedSpace X w)
    (hcompact : ∀ K : Set X, @IsCompact X w K → @IsCompact X rho K) : rho = w := by
  letI : TopologicalSpace X := w
  letI : T2Space X := hHaus
  letI : CompactlyGeneratedSpace X := hgen
  apply TopologicalSpace.ext_isClosed
  intro s
  constructor
  · intro hs
    apply CompactlyGeneratedSpace.isClosed
    intro K hK
    have hc : @IsCompact X rho (s ∩ K) :=
      by
        letI : TopologicalSpace X := rho
        have hkclosed : @IsClosed X rho K := @IsClosed.mono X rho w K (@IsCompact.isClosed X w hHaus K hK) hfine
        exact (hcompact K hK).of_isClosed_subset (hs.inter hkclosed) Set.inter_subset_right
    have hid : Continuous[rho, w] (id : X → X) :=
      continuous_iff_le_induced.mpr (by rw [induced_id]; exact hfine)
    have hw : @IsCompact X w (s ∩ K) := by simpa using @IsCompact.image X X rho w (s ∩ K) id hc hid
    exact hw.isClosed
  · intro hs
    exact hs.mono hfine

/-- Arbitrary rational values on a rationally independent family extend to a
rational-linear functional on the real line. -/
theorem prescribe_independent {I : Type*} (v : I → ℝ)
    (hv : LinearIndependent ℚ v) (c : I → ℚ) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, ∀ i, f (v i) = c i := by
  classical
  let l : Submodule.span ℚ (Set.range v) →ₗ[ℚ] ℚ :=
    (Finsupp.linearCombination ℚ c).comp hv.repr
  obtain ⟨f, hf⟩ := l.exists_extend
  refine ⟨f, fun i => ?_⟩
  have he := LinearMap.congr_fun hf ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  change f (v i) = (Finsupp.linearCombination ℚ c) (hv.repr ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩) at he
  rw [hv.repr_eq_single i _ rfl] at he
  simpa using he

/-- A rationally independent sequence can always be obstructed by a nonzero
coefficient functional. This proves the algebraic obstruction in Theorems 6.2 and 6.3. -/
theorem independent_sequence_bad_functional (v : ℕ → ℝ)
    (hv : LinearIndependent ℚ v) :
    ∃ f : ℝ →+ ℚ, f (v 0) = 1 / 2 ∧
      ¬ Tendsto v atTop (@nhds ℝ (tauT f ⊤) 0) := by
  obtain ⟨f, hf⟩ := prescribe_independent v hv (fun _ => 1 / 2)
  refine ⟨f.toAddMonoidHom, hf 0, ?_⟩
  intro h
  have hc := faR_cont_tau f.toAddMonoidHom ⊤ 1 (by simp)
  have ht := (@Continuous.tendsto ℝ ℝ (tauT f.toAddMonoidHom ⊤) _ (faR f.toAddMonoidHom 1) hc 0).comp h
  have he : (fun n => faR f.toAddMonoidHom 1 (v n)) = (fun _ : ℕ => (1 / 2 : ℝ)) := by
    funext n
    simp [faR_apply, hf]
  have ht' : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def, he, map_zero, circTop] using ht
  have : (1 / 2 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht'
  norm_num at this

/-- A sequence converging for every nonzero coefficient functional has finite
rational span, expressed without choosing coordinates. -/
theorem universal_tau_finite_span (x : ℕ → ℝ)
    (h : ∀ f : ℝ →+ ℚ, f ≠ 0 → Tendsto x atTop (@nhds ℝ (tauT f ⊤) 0)) :
    ∃ b : Set ℝ, b.Finite ∧ Submodule.span ℚ b = Submodule.span ℚ (Set.range x) := by
  classical
  obtain ⟨b, hb, hspan, hind⟩ := exists_linearIndependent ℚ (Set.range x)
  refine ⟨b, ?_, hspan⟩
  by_contra hinf
  haveI : Infinite b := Set.infinite_coe_iff.mpr hinf
  let e : ℕ ↪ b := Infinite.natEmbedding b
  have hex : ∀ n, ∃ k, x k = (e n : ℝ) := fun n => hb (e n).property
  choose k hk using hex
  have hk_inj : Function.Injective k := by
    intro n m he
    apply e.injective
    apply Subtype.ext
    rw [← hk n, ← hk m, he]
  have hv : LinearIndependent ℚ (fun n => (e n : ℝ)) := hind.comp e e.injective
  obtain ⟨f, hf, hbad⟩ := independent_sequence_bad_functional _ hv
  have hf0 : f ≠ 0 := by
    intro he
    simp [he] at hf
  have ht := (h f hf0).comp hk_inj.nat_tendsto_atTop
  apply hbad
  simpa only [Function.comp_def, hk] using ht

/-- The Laurent-series calculation underlying the positive half of Theorem 6.3.
It does not by itself construct the projection from the real line. -/
theorem laurent_negative_coeff_eventually_zero (a : LaurentSeries ℚ) :
    ∀ᶠ n : ℕ in atTop, a.coeff (-(n : ℤ)) = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-a.order)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply HahnSeries.coeff_eq_zero_of_lt_order
  have hnn : (N : ℤ) ≤ n := by exact_mod_cast hn
  omega

/-- Direct negation of compact preservation if the two topologies differ. -/
theorem not_compact_preservation_of_ne {X : Type*}
    (w rho : TopologicalSpace X) (hfine : rho ≤ w)
    (hHaus : @T2Space X w) (hgen : @CompactlyGeneratedSpace X w)
    (hne : rho ≠ w) :
    ∃ K : Set X, @IsCompact X w K ∧ ¬ @IsCompact X rho K := by
  by_contra h
  push_neg at h
  exact hne (topology_eq_of_compact_preservation w rho hfine hHaus hgen h)

/-- Exact initial-topology convergence criterion; no compactness theorem is used. -/
theorem tau_null_iff (f : ℝ →+ ℚ) (x : ℕ → ℝ) :
    Tendsto x atTop (@nhds ℝ (tauT f ⊤) 0) ↔
      Tendsto x atTop (nhds 0) ∧
      ∀ a : ℝ, Tendsto (fun n => f (a * x n)) atTop (@nhds ℚ usualQ 0) := by
  unfold tauT TfS
  rw [nhds_inf, tendsto_inf, nhds_iInf, tendsto_iInf]
  simp only [
    nhds_induced, tendsto_comap_iff, map_zero, Function.comp_def, fa_apply]
  constructor
  · rintro ⟨h, ha⟩
    exact ⟨h, fun a => ha ⟨a, by simp⟩⟩
  · rintro ⟨h, ha⟩
    exact ⟨h, fun a => ha a⟩

/-- Eventual vanishing of each observation suffices, with thresholds depending on a. -/
theorem tau_null_of_eventually_zero (f : ℝ →+ ℚ) (x : ℕ → ℝ)
    (hx : Tendsto x atTop (nhds 0))
    (hobs : ∀ a : ℝ, ∀ᶠ n in atTop, f (a * x n) = 0) :
    Tendsto x atTop (@nhds ℝ (tauT f ⊤) 0) := by
  apply (tau_null_iff f x).2
  refine ⟨hx, fun a => ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [hobs a] with n hn
  exact hn.symm

/-- The constant Laurent coefficient of X^n a vanishes eventually. -/
theorem laurent_shift_constant_eventually_zero (a : LaurentSeries ℚ) :
    ∀ᶠ n : ℕ in atTop,
      ((HahnSeries.single (n : ℤ) (1 : ℚ)) * a).coeff 0 = 0 := by
  simpa only [HahnSeries.coeff_single_mul, zero_sub, one_mul] using
    laurent_negative_coeff_eventually_zero a

/-- The modular version of the independent-sequence obstruction. -/
theorem independent_sequence_bad_beta (v : ℕ → ℝ)
    (hv : LinearIndependent ℚ v) :
    ∃ f : ℝ →+ ℚ, f (v 0) = 1 / 2 ∧
      ¬ Tendsto v atTop (@nhds ℝ (betaT f ⊤) 0) := by
  letI : TopologicalSpace Circ := circTop
  haveI : T2Space Circ := inferInstance
  obtain ⟨f, hf⟩ := prescribe_independent v hv (fun _ => 1 / 2)
  refine ⟨f.toAddMonoidHom, hf 0, ?_⟩
  intro h
  have hc := pfHom_cont_beta f.toAddMonoidHom ⊤ ⟨1, by simp⟩
  have ht := (@Continuous.tendsto ℝ Circ (betaT f.toAddMonoidHom ⊤) circTop
    (pfHom f.toAddMonoidHom 1) hc 0).comp h
  have he : (fun n => pfHom f.toAddMonoidHom 1 (v n)) =
      (fun _ : ℕ => (((1 / 2 : ℝ)) : Circ)) := by
    funext n
    simp [pfHom_apply, hf]
  have ht' : Tendsto (fun _ : ℕ => (((1 / 2 : ℝ)) : Circ)) atTop (nhds 0) := by
    simpa [Function.comp_def, he, map_zero, circTop] using ht
  have hz : (((1 / 2 : ℝ)) : Circ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht'
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  simp only [zsmul_eq_mul, mul_one] at hz
  have hp : (0 : ℝ) < z := by linarith
  have hq : (z : ℝ) < 1 := by linarith
  have hp' : (0 : ℤ) < z := by exact_mod_cast hp
  have hq' : z < (1 : ℤ) := by exact_mod_cast hq
  omega

/-- Finite rational span is necessary for convergence in beta for every functional. -/
theorem universal_beta_finite_span (x : ℕ → ℝ)
    (h : ∀ f : ℝ →+ ℚ, f ≠ 0 → Tendsto x atTop (@nhds ℝ (betaT f ⊤) 0)) :
    ∃ b : Set ℝ, b.Finite ∧ Submodule.span ℚ b = Submodule.span ℚ (Set.range x) := by
  classical
  obtain ⟨b, hb, hspan, hind⟩ := exists_linearIndependent ℚ (Set.range x)
  refine ⟨b, ?_, hspan⟩
  by_contra hinf
  haveI : Infinite b := Set.infinite_coe_iff.mpr hinf
  let e : ℕ ↪ b := Infinite.natEmbedding b
  have hex : ∀ n, ∃ k, x k = (e n : ℝ) := fun n => hb (e n).property
  choose k hk using hex
  have hk_inj : Function.Injective k := by
    intro n m he
    apply e.injective
    apply Subtype.ext
    rw [← hk n, ← hk m, he]
  have hv : LinearIndependent ℚ (fun n => (e n : ℝ)) := hind.comp e e.injective
  obtain ⟨f, hf, hbad⟩ := independent_sequence_bad_beta _ hv
  have hf0 : f ≠ 0 := by
    intro he
    simp [he] at hf
  have ht := (h f hf0).comp hk_inj.nat_tendsto_atTop
  apply hbad
  simpa only [Function.comp_def, hk] using ht

end LeanCheck






