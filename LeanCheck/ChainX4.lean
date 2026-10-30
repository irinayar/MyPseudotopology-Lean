import LeanCheck.ChainX3

/-!
# Conditions for a scalar field and for a real vector topology
(TVGQ-v7 Proposition 14.1 `field-regularity`, Proposition 14.2 `joint-v3`)

* `scalar_field_of_locallyCompact` : if the additive group of a TVGQ topology on `ℝ` is locally compact and
  sigma-compact (in particular if it is compact), every nonzero continuous scalar has a continuous inverse, so the
  continuous scalar ring is a field (`scalarCont_subfield`);
* `joint_continuity_of_orbit` : orbit continuity of the real line plus equicontinuity at zero of the rational
  dilations of modulus `≤ 1` give jointly continuous scalar multiplication.
-/

namespace LeanCheck

open Filter Topology

/-! ### Proposition 14.1 -/

/-- Every nonzero continuous scalar of a locally compact sigma-compact Hausdorff group topology on `ℝ`
has a continuous inverse. -/
theorem scalar_field_of_locallyCompact (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _)
    (hT2 : @T2Space ℝ τ) (hlc : @LocallyCompactSpace ℝ τ) (hsc : @SigmaCompactSpace ℝ τ)
    (a : ℝ) (ha : a ∈ scalarCont τ) (ha0 : a ≠ 0) : a⁻¹ ∈ scalarCont τ := by
  letI := τ
  haveI := hτ
  haveI := hT2
  haveI := hlc
  haveI := hsc
  let g : ℝ →+ ℝ := AddMonoidHom.mulLeft a
  have hcont : Continuous g := ha
  have hsurj : Function.Surjective g := fun y => ⟨a⁻¹ * y, by simp [g, mul_inv_cancel_left₀ ha0]⟩
  have hopen : IsOpenMap g := AddMonoidHom.isOpenMap_of_sigmaCompact g hsurj hcont
  let e : ℝ ≃ ℝ := Equiv.mulLeft₀ a ha0
  have hsymm : Continuous (e.toHomeomorphOfContinuousOpen hcont hopen).symm :=
    (e.toHomeomorphOfContinuousOpen hcont hopen).symm.continuous
  show Continuous[τ, τ] (fun x : ℝ => a⁻¹ * x)
  convert hsymm using 1
  funext x
  show a⁻¹ * x = e.symm x
  simp [e, Equiv.mulLeft₀]

/-- **Proposition 14.1.**  The continuous scalar ring of such a TVGQ is a subfield of `ℝ`. -/
theorem scalarCont_subfield (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _)
    (hq : ∀ q : ℚ, Continuous[τ, τ] (fun x : ℝ => (q : ℝ) * x))
    (hT2 : @T2Space ℝ τ) (hlc : @LocallyCompactSpace ℝ τ) (hsc : @SigmaCompactSpace ℝ τ) :
    ∃ K : Subfield ℝ, (K : Set ℝ) = scalarCont τ := by
  obtain ⟨R, hR, -⟩ := scalarCont_subring τ hτ hq
  refine ⟨{ R with
    inv_mem' := fun a ha => ?_ }, hR⟩
  by_cases h0 : a = 0
  · subst h0; simpa using R.zero_mem
  · have ha' : a ∈ scalarCont τ := by rw [← hR]; exact ha
    have := scalar_field_of_locallyCompact τ hτ hT2 hlc hsc a ha' h0
    rw [← hR] at this
    exact this

/-- Compact Hausdorff TVGQ spaces are included. -/
theorem scalarCont_subfield_compact (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _)
    (hq : ∀ q : ℚ, Continuous[τ, τ] (fun x : ℝ => (q : ℝ) * x))
    (hT2 : @T2Space ℝ τ) (hc : @CompactSpace ℝ τ) :
    ∃ K : Subfield ℝ, (K : Set ℝ) = scalarCont τ := by
  letI := τ
  haveI := hc
  exact scalarCont_subfield τ hτ hq hT2 inferInstance inferInstance

/-! ### Proposition 14.2 -/

section Joint

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]

/-- Equicontinuity at zero of all real dilations of modulus `≤ 1`. -/
lemma real_equicontinuous (horb : ∀ x : V, Continuous fun r : ℝ => r • x)
    (hequi : ∀ U ∈ 𝓝 (0 : V), ∃ W ∈ 𝓝 (0 : V), ∀ q : ℚ, |(q : ℝ)| ≤ 1 → ∀ w ∈ W, (q : ℝ) • w ∈ U)
    (U : Set V) (hU : U ∈ 𝓝 (0 : V)) :
    ∃ W ∈ 𝓝 (0 : V), ∀ r : ℝ, |r| ≤ 1 → ∀ w ∈ W, r • w ∈ U := by
  obtain ⟨U0, ⟨hU0, hU0c⟩, hU0U⟩ := (closed_nhds_basis (0 : V)).mem_iff.1 hU
  obtain ⟨W, hW, hWq⟩ := hequi U0 hU0
  refine ⟨W, hW, fun r hr w hw => hU0U ?_⟩
  have hA : IsClosed {s : ℝ | s • w ∈ U0} := hU0c.preimage (horb w)
  have hq : ∀ q : ℚ, |(q : ℝ)| ≤ 1 → (q : ℝ) ∈ {s : ℝ | s • w ∈ U0} :=
    fun q hq => hWq q hq w hw
  rcases eq_or_lt_of_le hr with h1 | h1
  · rcases abs_choice r with h | h
    · have : r = ((1 : ℚ) : ℝ) := by rw [h] at h1; push_cast; linarith
      rw [this]; exact hq 1 (by simp)
    · have : r = (((-1 : ℚ)) : ℝ) := by
        have : -r = 1 := by rw [h] at h1; linarith
        push_cast; linarith
      rw [this]; exact hq (-1) (by simp)
  · by_contra hrA
    have hopen : IsOpen ({s : ℝ | s • w ∈ U0}ᶜ ∩ Set.Ioo (-1 : ℝ) 1) :=
      hA.isOpen_compl.inter isOpen_Ioo
    have hne : ({s : ℝ | s • w ∈ U0}ᶜ ∩ Set.Ioo (-1 : ℝ) 1).Nonempty := ⟨r, hrA, abs_lt.mp h1⟩
    obtain ⟨q, hq1, hq2⟩ := Rat.denseRange_cast.exists_mem_open hopen hne
    exact hq1 (hq q (le_of_lt (abs_lt.mpr hq2)))

/-- Equicontinuity at zero of all real dilations of modulus `≤ N`. -/
lemma bounded_equicontinuous (horb : ∀ x : V, Continuous fun r : ℝ => r • x)
    (hequi : ∀ U ∈ 𝓝 (0 : V), ∃ W ∈ 𝓝 (0 : V), ∀ q : ℚ, |(q : ℝ)| ≤ 1 → ∀ w ∈ W, (q : ℝ) • w ∈ U)
    (N : ℕ) (U : Set V) (hU : U ∈ 𝓝 (0 : V)) :
    ∃ W' ∈ 𝓝 (0 : V), ∀ r : ℝ, |r| ≤ N → ∀ u ∈ W', r • u ∈ U := by
  obtain ⟨W, hW, hWr⟩ := real_equicontinuous horb hequi U hU
  refine ⟨(fun u : V => N • u) ⁻¹' W, ?_, fun r hr u hu => ?_⟩
  · exact (continuous_nsmul N).continuousAt.preimage_mem_nhds (by simpa using hW)
  · rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      have : r = 0 := by simpa using hr
      subst this
      simpa using mem_of_mem_nhds hU
    · have hNr : (N : ℝ) ≠ 0 := by positivity
      have h1 : |r / N| ≤ 1 := by
        rw [abs_div, Nat.abs_cast]
        exact div_le_one_of_le₀ hr (Nat.cast_nonneg N)
      have := hWr (r / N) h1 (N • u) hu
      rwa [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, div_mul_cancel₀ _ hNr] at this

/-- **Proposition 14.2.**  Orbit continuity plus equicontinuity at zero of the rational dilations of modulus
`≤ 1` give jointly continuous scalar multiplication by the real numbers. -/
theorem joint_continuity_of_orbit (horb : ∀ x : V, Continuous fun r : ℝ => r • x)
    (hequi : ∀ U ∈ 𝓝 (0 : V), ∃ W ∈ 𝓝 (0 : V), ∀ q : ℚ, |(q : ℝ)| ≤ 1 → ∀ w ∈ W, (q : ℝ) • w ∈ U) :
    ContinuousSMul ℝ V := by
  refine ⟨?_⟩
  rw [continuous_iff_continuousAt]
  rintro ⟨r0, x0⟩
  have e : (fun p : ℝ × V => p.1 • p.2) =
      fun p => r0 • x0 + (p.1 • (p.2 - x0) + (p.1 - r0) • x0) := by
    funext p
    simp only [smul_sub, sub_smul]
    abel
  rw [ContinuousAt, e]
  have h2 : Tendsto (fun p : ℝ × V => (p.1 - r0) • x0) (𝓝 (r0, x0)) (𝓝 0) := by
    have h := ((horb x0).continuousAt (x := r0)).tendsto.comp (continuous_fst.tendsto (r0, x0))
    have := h.sub_const (r0 • x0)
    simpa [sub_smul] using this
  have h1 : Tendsto (fun p : ℝ × V => p.1 • (p.2 - x0)) (𝓝 (r0, x0)) (𝓝 0) := by
    rw [tendsto_def]
    intro U hU
    obtain ⟨W', hW', hbound⟩ := bounded_equicontinuous horb hequi (⌈|r0|⌉₊ + 1) U hU
    have ht1 : ∀ᶠ p in 𝓝 (r0, x0), p.1 ∈ Metric.ball r0 1 :=
      (continuous_fst.tendsto (r0, x0)).eventually (Metric.ball_mem_nhds r0 one_pos)
    have ht2 : ∀ᶠ p in 𝓝 (r0, x0), p.2 - x0 ∈ W' := by
      have := (continuous_snd.tendsto (r0, x0)).sub_const x0
      rw [sub_self] at this
      exact this.eventually hW'
    filter_upwards [ht1, ht2] with p hp1 hp2
    apply hbound p.1 _ _ hp2
    rw [Metric.mem_ball, Real.dist_eq] at hp1
    have : |p.1| ≤ |r0| + 1 := by
      calc |p.1| = |r0 + (p.1 - r0)| := by ring_nf
        _ ≤ |r0| + |p.1 - r0| := abs_add_le _ _
        _ ≤ |r0| + 1 := by linarith
    have hc : |r0| ≤ (⌈|r0|⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  have := (tendsto_const_nhds (x := r0 • x0)).add (h1.add h2)
  simpa using this

end Joint

end LeanCheck
