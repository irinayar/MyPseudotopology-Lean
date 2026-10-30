import LeanCheck.ChainPW6
import LeanCheck.ChainComp7
import LeanCheck.ChainDuality

/-!
# F2 (Peter–Weyl) proved: Hausdorff precompact group topologies on `ℝ` are character topologies

`GeneratedFact`: for every Hausdorff precompact group topology `τ` on `ℝ`, `τ = θ(dual τ)`.  Proof: the
completion `K` of `(ℝ, τ)` is a compact Hausdorff abelian group; by the abelian Peter–Weyl theorem
(`PW.exists_char_ne`) its continuous characters separate points, hence (compactness) every neighbourhood of
`0` in `K` contains a finite intersection of character neighbourhoods; restricting to `ℝ` gives the claim.
-/

namespace LeanCheck

open Filter Topology UniformSpace

section Compact

variable {K : Type} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
  [CompactSpace K] [T2Space K]

/-- Circle-valued characters separate the points of a compact Hausdorff abelian group. -/
theorem exists_circ_char (x₀ : K) (hx₀ : x₀ ≠ 0) :
    ∃ χ : K →+ Circ, Continuous χ ∧ χ x₀ ≠ 0 := by
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  obtain ⟨c, hcont, hmul, hnorm, hcx⟩ := PW.exists_char_ne x₀ hx₀
  have hc0 : c 0 = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    have hne : c 0 ≠ 0 := by
      intro h0; have := hnorm 0; rw [h0] at this; simp at this
    exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)
  let cc : K → Circle := fun a => ⟨c a, mem_sphere_zero_iff_norm.2 (hnorm a)⟩
  have hcc : Continuous cc := Continuous.subtype_mk hcont _
  have hcc0 : cc 0 = 1 := Subtype.ext hc0
  have hccadd : ∀ a b, cc (a + b) = cc a * cc b := fun a b => Subtype.ext (hmul a b)
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  have he : ∀ y, e y = AddCircle.toCircle y := fun y => AddCircle.homeomorphCircle_apply one_ne_zero y
  have he0 : e 0 = 1 := by rw [he, AddCircle.toCircle_zero]
  refine ⟨{ toFun := fun a => e.symm (cc a)
            map_zero' := ?_
            map_add' := ?_ }, ?_, ?_⟩
  · show e.symm (cc 0) = 0
    rw [hcc0, e.symm_apply_eq, he0]
  · intro a b
    show e.symm (cc (a + b)) = e.symm (cc a) + e.symm (cc b)
    apply e.injective
    rw [Homeomorph.apply_symm_apply, hccadd, he, AddCircle.toCircle_add, ← he, ← he,
      Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  · exact e.symm.continuous.comp hcc
  · intro h
    apply hcx
    have h1 : e.symm (cc x₀) = 0 := h
    have h2 : cc x₀ = 1 := by rw [e.symm_apply_eq, he0] at h1; exact h1
    exact congrArg Subtype.val h2

/-- Every neighbourhood of `0` in a compact Hausdorff abelian group contains a finite intersection of
character balls. -/
theorem finite_chars_in_nhds {V : Set K} (hV : V ∈ 𝓝 (0 : K)) :
    ∃ (t : Finset K) (χ : K → K →+ Circ) (r : K → ℝ), (∀ p ∈ t, Continuous (χ p)) ∧
      (∀ p ∈ t, 0 < r p) ∧ {q : K | ∀ p ∈ t, ‖χ p q‖ ≤ r p} ⊆ V := by
  classical
  have hsep : ∀ p : K, p ≠ 0 → ∃ χ : K →+ Circ, Continuous χ ∧ χ p ≠ 0 := fun p hp =>
    exists_circ_char p hp
  choose! χ hχc hχp using hsep
  set O := interior V with hO
  have hO0 : (0 : K) ∈ O := mem_interior_iff_mem_nhds.2 hV
  have hOc : IsCompact Oᶜ := (isOpen_interior.isClosed_compl).isCompact
  have hne : ∀ p : (Oᶜ : Set K), p.1 ≠ 0 := fun p h => p.2 (h ▸ hO0)
  let rr : K → ℝ := fun p => ‖χ p p‖ / 2
  have hrr : ∀ p : (Oᶜ : Set K), 0 < rr p.1 := fun p => by
    have := norm_pos_iff.2 (hχp p.1 (hne p))
    simp only [rr]; positivity
  let U : (Oᶜ : Set K) → Set K := fun p => {q | rr p.1 < ‖χ p.1 q‖}
  have hUo : ∀ p, IsOpen (U p) := fun p =>
    isOpen_lt continuous_const (continuous_norm.comp (hχc p.1 (hne p)))
  have hsU : Oᶜ ⊆ ⋃ p, U p := by
    intro q hq
    refine Set.mem_iUnion.2 ⟨⟨q, hq⟩, ?_⟩
    have := hrr ⟨q, hq⟩
    have h2 : ‖χ q q‖ = 2 * rr q := by simp only [rr]; ring
    show rr q < ‖χ q q‖
    rw [h2]; linarith
  obtain ⟨t', ht'⟩ := hOc.elim_finite_subcover U hUo hsU
  refine ⟨t'.image Subtype.val, χ, rr, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨p', -, rfl⟩ := Finset.mem_image.1 hp
    exact hχc _ (hne p')
  · intro p hp
    obtain ⟨p', -, rfl⟩ := Finset.mem_image.1 hp
    exact hrr p'
  · intro q hq
    by_contra hqV
    have hqO : q ∈ Oᶜ := fun h => hqV (interior_subset h)
    obtain ⟨p', hp', hqU⟩ := Set.mem_iUnion₂.1 (ht' hqO)
    have := hq p'.1 (Finset.mem_image_of_mem _ hp')
    exact absurd hqU (not_lt.2 this)

end Compact

/-- The completion of a totally bounded uniform abelian group is compact. -/
theorem completion_compactSpace (α : Type) [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
    (hα : TotallyBounded (Set.univ : Set α)) : CompactSpace (Completion α) := by
  have h1 : TotallyBounded (Set.range ((↑) : α → Completion α)) := by
    rw [← Set.image_univ]
    exact hα.image (Completion.uniformContinuous_coe α)
  have h2 : TotallyBounded (Set.univ : Set (Completion α)) := by
    have := h1.closure
    rwa [(Completion.denseRange_coe (α := α)).closure_eq] at this
  exact ⟨(isCompact_iff_totallyBounded_isComplete.2 ⟨h2, isComplete_univ⟩)⟩

/-- **(F2) Peter–Weyl**: Hausdorff precompact group topologies on `ℝ` are generated by their characters. -/
theorem generatedFact : GeneratedFact := by
  intro τ hτ hT2 hP
  haveI : IsTopologicalAddGroup (RT τ) := hτ
  haveI : T2Space (RT τ) := hT2
  -- total boundedness
  have htb : TotallyBounded (Set.univ : Set (RT τ)) := by
    rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
    intro U hU
    obtain ⟨F, hF⟩ := hP U hU
    refine ⟨(F : Set ℝ), F.finite_toSet, fun x _ => ?_⟩
    let x' : ℝ := x
    obtain ⟨t, htF, htU⟩ := hF x'
    refine Set.mem_iUnion₂.2 ⟨t, htF, ?_⟩
    exact Set.mem_vadd_set.2 ⟨show RT τ from (x' - t), htU, by
      change t + (x' - t) = x'; ring⟩
  haveI : CompactSpace (Completion (RT τ)) := completion_compactSpace _ htb
  let J : RT τ →+ Completion (RT τ) := coeAddHom' (RT τ)
  have hJdense : DenseRange J := Completion.denseRange_coe
  have hJind : IsInducing J := (Completion.isDenseInducing_coe (α := RT τ)).toIsInducing
  have hH := fun χ => mem_dualGroup τ hτ χ
  -- every `τ`-neighbourhood of `0` is a `θ`-neighbourhood
  have hard : ∀ U ∈ @nhds ℝ τ 0, U ∈ @nhds ℝ (theta (dualGroup τ hτ : Set Chars)) 0 := by
    intro U hU
    have hU' : U ∈ 𝓝 (0 : RT τ) := hU
    rw [hJind.nhds_eq_comap, map_zero] at hU'
    obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.1 hU'
    obtain ⟨t, χ, r, hχc, hr, hsub⟩ := finite_chars_in_nhds hV
    let ψ : Completion (RT τ) → Chars := fun p => (χ p).comp J
    have hψmem : ∀ p ∈ t, ψ p ∈ dualGroup τ hτ := by
      intro p hp
      refine (hH _).2 ?_
      exact @Continuous.comp (RT τ) (Completion (RT τ)) Circ _ _ circTop' (⇑J) (⇑(χ p)) (hχc p hp)
        (Completion.continuous_coe (RT τ))
    have hS : {x : ℝ | ∀ p ∈ t, ‖ψ p x‖ ≤ r p} ∈
        @nhds ℝ (theta (dualGroup τ hτ : Set Chars)) 0 := by
      have : {x : ℝ | ∀ p ∈ t, ‖ψ p x‖ ≤ r p} = ⋂ p ∈ t, (ψ p : ℝ → Circ) ⁻¹' (Metric.closedBall 0 (r p)) := by
        ext x; simp
      rw [this]
      refine (Filter.biInter_finset_mem t).2 (fun p hp => ?_)
      have hc := theta_cont_of_mem (dualGroup τ hτ : Set Chars) (ψ p) (hψmem p hp)
      exact (@Continuous.continuousAt ℝ Circ (theta (dualGroup τ hτ : Set Chars)) circTop' (ψ p) 0 hc)
        (by rw [map_zero]; exact Metric.closedBall_mem_nhds 0 (hr p hp))
    refine Filter.mem_of_superset hS (fun x hx => hVU ?_)
    exact hsub (fun p hp => hx p hp)
  have h1 : τ ≤ theta (dualGroup τ hτ : Set Chars) := by
    refine le_iInf fun χ => ?_
    exact continuous_iff_le_induced.1 ((hH χ.1).1 χ.2)
  have hnhds : @nhds ℝ τ 0 = @nhds ℝ (theta (dualGroup τ hτ : Set Chars)) 0 :=
    Filter.ext fun U => ⟨fun hU => hard U hU, fun hU => nhds_mono h1 hU⟩
  exact IsTopologicalAddGroup.ext hτ (theta_group _) hnhds

/-- The complete duality package, now unconditional. -/
theorem precompactDuality : PrecompactDuality := PrecompactDuality.of_generated generatedFact

end LeanCheck
