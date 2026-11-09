import Mathlib
import LeanCheck.PVGBetaQChoose
import LeanCheck.PVGBetaFinal
import LeanCheck.PVGLacMain
import LeanCheck.PVGNoFU
import LeanCheck.PVGClosed

/-!
# PVG: a non-pretopological PVG `ξ_{β,I_S}` that is not coarser than `τ_B` (Lean check)

Scope. Addendum H of the research note (the variant of Theorem `thm:betaexists`, and the admissible pair `(β, I_S)`).

* `RecurTop β`: the recurrence property `(Q)` stated for the neighbourhoods of `0`: for every `W ∈ 𝓝_β(0)`, `c ∈ ℝ` and `N` there are
  `p > q ≥ N` with `c (s_p - s_q) ∈ W` (`s_n = 2^(n²)`);
* `recur_betaTop`: `(Q)` for the topology `betaTop` of the pseudonorm `ρ_μ` when the measure `μ` has the recurrence property `RecurProp`
  (`recur_rho` of `PVGBetaQCantor`);
* `zero_mem_closure_D_beta`: if `β` has `(Q)`, `c ≥ 1` and `c t ∈ A` for only finitely many `t ∈ T`, then `0 ∈ closure_β (Dset c A)`;
* `xiIS_main`: for a Hausdorff group topology `β` inside the Euclidean topology with continuous dilations and `(Q)`, the convergence
  `ξ_{β,I_S}` is a Hausdorff PVG, coarser than the Euclidean convergence, not pretopological, not Euclidean, and not Fréchet–Urysohn
  (Proposition `noFUxi`);
* `exists_beta_Q`: there is such a `β` with the properties (a), (b), (c) of Theorem `thm:betaexists` (Kronecker's theorem is proved in
  `PVGKronecker`, so there is no hypothesis);
* `not_le_bohr`: such a `β` is not coarser than `τ_B`: `¬ (bohrTop ≤ β)`; this uses the hypothesis `BohrMinimal` (the minimality of `τ_B`,
  cited, not formalized), while `ne_bohr` (`β ≠ bohrTop`) is proved without it, because the characters are `τ_B`-continuous and not
  `β`-continuous.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open MeasureTheory Filter Topology Set
open PVG.Q95 PVG.Lac

namespace PVG
namespace Beta

/-- The recurrence property `(Q)` for the neighbourhoods of `0` of a topology on `ℝ`. -/
def RecurTop (β : TopologicalSpace ℝ) : Prop :=
  ∀ W ∈ @nhds ℝ β 0, ∀ (c : ℝ) (N : ℕ), ∃ p q : ℕ, N ≤ q ∧ q < p ∧ c * (sS p - sS q) ∈ W

theorem recur_betaTop (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hsupp : μ (Set.Icc (1 : ℝ) 2)ᶜ = 0) (hrec : RecurProp μ) :
    RecurTop (betaTop (isPseudoNorm_rho μ hsupp)) := by
  intro W hW c N
  obtain ⟨F, δ, hδ, hFW⟩ := (mem_nhds_zero_iff (isPseudoNorm_rho μ hsupp)).1 hW
  classical
  obtain ⟨p, q, hq, hpq, h⟩ := recur_rho μ hrec (F.image (fun c' => c' * c)) δ hδ N
  refine ⟨p, q, hq, hpq, hFW fun c' hc' => ?_⟩
  have := h (c' * c) (Finset.mem_image.2 ⟨c', hc', rfl⟩)
  rw [mul_assoc] at this
  exact this

/-- `0` is in the `β`-closure of `D` when `β` has the recurrence property. -/
theorem zero_mem_closure_D_beta {β : TopologicalSpace ℝ} (hrec : RecurTop β) {A : Set ℝ} {c : ℝ}
    (hfin : {t | t ∈ Tset ∧ c * t ∈ A}.Finite) : (0 : ℝ) ∈ @closure ℝ β (Dset c A) := by
  rw [@mem_closure_iff_nhds ℝ β]
  intro W hW
  obtain ⟨Mb, hMb⟩ := (hfin.image (fun t : ℝ => |t|)).bddAbove
  obtain ⟨L, hL⟩ := sS_unbounded (2 * Mb)
  obtain ⟨n, l, hlN, hln, hVln⟩ := hrec W hW c (max L 1)
  have hL1 : 1 ≤ l := le_trans (le_max_right _ _) hlN
  have hLl : L ≤ l := le_trans (le_max_left _ _) hlN
  have hxA : c * (sS n - sS l) ∉ A := by
    intro hxA
    have hT : (sS n - sS l) ∈ Tset := ⟨n, l, hL1, hln, true, false, by simp [tval, sgn]; ring⟩
    have hmem : (sS n - sS l) ∈ {t | t ∈ Tset ∧ c * t ∈ A} := ⟨hT, hxA⟩
    have hle : |sS n - sS l| ≤ Mb := hMb ⟨_, hmem, rfl⟩
    have hb := (tval_bounds hln true false).1
    have e1 : tval n l true false = sS n - sS l := by simp [tval, sgn]; ring
    rw [e1] at hb
    have hmono : sS L ≤ sS n := sS_mono (by omega)
    linarith
  exact ⟨c * (sS n - sS l), hVln, n, l, hL1, hln, rfl, hxA⟩

/-- **The admissible pair `(β, I_S)`**: for a Hausdorff group topology `β` inside the Euclidean topology with continuous dilations and the
recurrence property, `ξ_{β,I_S}` is a Hausdorff PVG, coarser than the Euclidean convergence, not pretopological, not Euclidean and not
Fréchet–Urysohn. -/
theorem xiIS_main (β : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ β _) (ht2 : @T2Space ℝ β)
    (hsm : @ContinuousConstSMul ℝ ℝ β _) (heT : eT ≤ β) (hrec : RecurTop β) :
    IsPVG (@xiConv ℝ β IS) ∧ PHausdorff (@xiConv ℝ β IS) ∧
      (∀ (F : Filter ℝ) (x : ℝ), F ≤ @nhds ℝ eT x → @xiConv ℝ β IS F x) ∧
      ¬ IsPretop (@xiConv ℝ β IS) ∧
      (∃ F : Filter ℝ, @xiConv ℝ β IS F 0 ∧ ¬ F ≤ @nhds ℝ eT 0) ∧
      ¬ IsFU (@xiConv ℝ β IS) := by
  have hpvg : IsPVG (@xiConv ℝ β IS) := @xi_isPVG ℝ _ _ β hg hsm IS IS_isIdeal
  have hcoarse : ∀ (F : Filter ℝ) (x : ℝ), F ≤ @nhds ℝ eT x → @xiConv ℝ β IS F x := by
    intro F x h
    refine ⟨h.trans (nhds_mono heT), Metric.ball x 1, h (Metric.ball_mem_nhds x one_pos), ?_⟩
    refine bounded_mem_IS (M := |x| + 1) (fun a ha => ?_)
    rw [Metric.mem_ball, Real.dist_eq] at ha
    have h1 : |a| ≤ |a - x| + |x| := by
      have := abs_add_le (a - x) x
      simpa using this
    linarith
  have hD0 : (0 : ℝ) ∈ @closure ℝ β (Dset 1 ∅) :=
    zero_mem_closure_D_beta hrec (c := 1) (A := ∅) (by
      refine Set.Finite.subset (Set.finite_empty) ?_
      rintro t ⟨_, ht⟩
      exact absurd ht (Set.notMem_empty _))
  have hnotE : ∃ F : Filter ℝ, @xiConv ℝ β IS F 0 ∧ ¬ F ≤ @nhds ℝ eT 0 := by
    haveI hne : (@nhds ℝ β 0 ⊓ Filter.principal (Dset 1 ∅)).NeBot :=
      (@mem_closure_iff_nhdsWithin_neBot ℝ β 0 (Dset 1 ∅)).1 hD0
    refine ⟨@nhds ℝ β 0 ⊓ Filter.principal (Dset 1 ∅), ⟨inf_le_left, Dset 1 ∅,
      Filter.mem_inf_of_right (Filter.mem_principal_self _), Dset_mem_IS 1 ∅⟩, ?_⟩
    intro hle
    have hball : Metric.ball (0 : ℝ) 1 ∈ (@nhds ℝ β 0 ⊓ Filter.principal (Dset 1 ∅)) :=
      hle (Metric.ball_mem_nhds 0 one_pos)
    rw [Filter.mem_inf_principal] at hball
    rw [@mem_closure_iff_nhds ℝ β] at hD0
    obtain ⟨x, hx1, hx2⟩ := hD0 _ hball
    have h1 := Dset_abs_ge le_rfl hx2
    have h2 := hx1 hx2
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at h2
    linarith
  refine ⟨hpvg, @xi_hausdorff ℝ _ _ β hg hsm IS ht2, hcoarse, ?_, hnotE, ?_⟩
  · exact @xi_not_pretop ℝ _ _ β hg hsm IS IS_isIdeal (fun A hA => by
      obtain ⟨c, hc, hfin⟩ := exists_dilation hA
      exact ⟨Dset c A, Dset_mem_IS c A, Dset_disjoint c A, zero_mem_closure_D_beta hrec hfin⟩)
  · intro hFU
    obtain ⟨F, hF, hnF⟩ := hnotE
    exact hnF ((@noFU_xi β hg ht2 hsm IS IS_isIdeal hcoarse hFU F 0).1 hF)

/-- A `β`-nonpretopological example: with the recurrence property and the measure of the variant of the construction. -/
theorem exists_beta_Q :
    ∃ β : TopologicalSpace ℝ,
      @IsTopologicalAddGroup ℝ β _ ∧ @T2Space ℝ β ∧ eT ≤ β ∧ @ContinuousConstSMul ℝ ℝ β _ ∧
      (∀ V ∈ @nhds ℝ β 0, ∃ k : ℤ, ((k : ℝ) + 1 / 2) ∈ V) ∧
      (∀ b : ℝ, b ≠ 0 → ¬ @Continuous ℝ (AddCircle (1 : ℝ)) β cT (chi b)) ∧
      (∀ x : ℝ, x ∈ @closure ℝ β (Set.range (fun k : ℤ => (k : ℝ)))) ∧ RecurTop β := by
  obtain ⟨μ, hprob, hnull, hsupp, hst, hrec⟩ := exists_Q_measure kronecker_density
  haveI := hprob
  haveI := hnull
  have hps := isPseudoNorm_rho μ hsupp
  have hH := halfInt_of_stages μ hst
  exact ⟨betaTop hps, betaTop_isTopologicalAddGroup hps, betaTop_t2 hps, eT_le_betaTop hps,
    betaTop_constSMul hps, half_in_nhds hps hH, fun b hb => chi_not_continuous hps hH hb,
    int_dense hps hH, recur_betaTop μ hsupp hrec⟩

/-- The characters `t ↦ bt + ℤ` are continuous for the Bohr topology. -/
theorem chi_continuous_bohr (b : ℝ) : @Continuous ℝ (AddCircle (1 : ℝ)) bohrTop cT (chi b) := by
  have h : @Continuous ℝ K bohrTop _ e := continuous_induced_dom
  exact @Continuous.comp ℝ K (AddCircle (1 : ℝ)) bohrTop _ cT _ _ (continuous_eval b) h

/-- `β` is not the Bohr topology (no hypothesis). -/
theorem ne_bohr {β : TopologicalSpace ℝ}
    (hchi : ∀ b : ℝ, b ≠ 0 → ¬ @Continuous ℝ (AddCircle (1 : ℝ)) β cT (chi b)) : β ≠ bohrTop := by
  intro h
  exact hchi 1 one_ne_zero (h ▸ chi_continuous_bohr 1)

/-- `β` is not coarser than `τ_B`, by the minimality of `τ_B` (hypothesis `BohrMinimal`). -/
theorem not_le_bohr (hmin : BohrMinimal) {β : TopologicalSpace ℝ} (hg : @IsTopologicalAddGroup ℝ β _)
    (ht2 : @T2Space ℝ β) (hsm : @ContinuousConstSMul ℝ ℝ β _)
    (hchi : ∀ b : ℝ, b ≠ 0 → ¬ @Continuous ℝ (AddCircle (1 : ℝ)) β cT (chi b)) : ¬ bohrTop ≤ β :=
  fun hle => ne_bohr hchi (hmin β hg ht2 hsm hle)

end Beta
end PVG
