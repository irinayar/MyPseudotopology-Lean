import LeanCheck.PVGSeqFU
import LeanCheck.PVGSeqGen2

/-!
# PVG: admissible pairs below the Euclidean convergence (Lean check)

Scope. Proposition `prop:noFUxi` of PVG_v22. Let `β` be a Hausdorff group topology on `ℝ` with continuous dilations, `I` an ideal in the
sense of `IsIdeal`, and `ξ = ξ_{β,I}` (`@xiConv ℝ β I`). If `ξ` is coarser than the Euclidean convergence (every Euclidean convergent
filter `ξ`-converges) and `ξ` is Fréchet–Urysohn, then `ξ` is the Euclidean convergence. The Euclidean topology is written `eT`, because a
variable topology `β` on `ℝ` would otherwise capture the default instance.

* `euclid_le_of_coarse`: coarseness forces `β` to be inside the Euclidean topology (the article, Remark `scopeFU`);
* `seq_euclid_of_group_topology`: a `β`-convergent sequence converges in the Euclidean topology (Proposition `betaseq` (b), through
  `PVG.Gen.seq_conv_euclid` for `X = (ℝ, β)`, `ι = id`);
* `noFU_xi_of_seq`: the argument for an abstract `β` whose convergent sequences are Euclidean convergent;
* `noFU_xi`: the proposition.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Q95

/-- The Euclidean topology of `ℝ`, named so that it can be used next to a variable topology `β`. -/
abbrev eT : TopologicalSpace ℝ := inferInstance

/-- Coarseness of `ξ_{β,I}` than the Euclidean convergence forces `β` to be inside the Euclidean topology. -/
theorem euclid_le_of_coarse (β : TopologicalSpace ℝ) (I : Set (Set ℝ))
    (hcoarse : ∀ (F : Filter ℝ) (x : ℝ), F ≤ @nhds ℝ eT x → @xiConv ℝ β I F x) {s : Set ℝ}
    (hs : @IsOpen ℝ β s) : @IsOpen ℝ eT s := by
  rw [@isOpen_iff_mem_nhds ℝ eT]
  intro x hx
  have h := (hcoarse (@nhds ℝ eT x) x le_rfl).1
  exact h (@IsOpen.mem_nhds ℝ β x s hs hx)

/-- A `β`-convergent sequence converges in the Euclidean topology. -/
theorem seq_euclid_of_group_topology (β : TopologicalSpace ℝ) [hg : @IsTopologicalAddGroup ℝ β _]
    [ht2 : @T2Space ℝ β] [hsm : @ContinuousConstSMul ℝ ℝ β _]
    (hβE : ∀ s : Set ℝ, @IsOpen ℝ β s → @IsOpen ℝ eT s) (a : ℕ → ℝ) (x : ℝ)
    (h : Tendsto a atTop (@nhds ℝ β x)) : Tendsto a atTop (@nhds ℝ eT x) := by
  have hι : @Continuous ℝ ℝ eT β (LinearMap.id : ℝ →ₗ[ℝ] ℝ) :=
    (@continuous_def ℝ ℝ eT β _).2 (fun s hs => hβE s hs)
  exact @PVG.Gen.seq_conv_euclid ℝ _ _ β hg ht2 hsm (LinearMap.id) hι (fun u v h => h) a x h

/-- The argument for an abstract topology `β` on `ℝ` whose convergent sequences are Euclidean convergent. -/
theorem noFU_xi_of_seq (β : TopologicalSpace ℝ) {I : Set (Set ℝ)} (hI : IsIdeal I)
    (hFU : IsFU (@xiConv ℝ β I))
    (hseq : ∀ (a : ℕ → ℝ) (x : ℝ), Tendsto a atTop (@nhds ℝ β x) → Tendsto a atTop (@nhds ℝ eT x))
    {F : Filter ℝ} {x : ℝ} (hF : @xiConv ℝ β I F x) : F ≤ @nhds ℝ eT x := by
  by_contra hno
  rw [Filter.le_def] at hno
  push Not at hno
  obtain ⟨W, hW, hWF⟩ := hno
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
  have hballF : Metric.ball x ε ∉ F := fun h => hWF (Filter.mem_of_superset h hball)
  obtain ⟨A, hAF, hAI⟩ := hF.2
  set A' : Set ℝ := A \ Metric.ball x ε with hA'
  have hA'I : A' ∈ I := hI.mono hAI Set.sdiff_subset
  have hne : (@nhds ℝ β x ⊓ Filter.principal A').NeBot := by
    rw [Filter.inf_principal_neBot_iff]
    intro U hU
    have hUF : U ∈ F := hF.1 hU
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hballF
    refine Filter.mem_of_superset (Filter.inter_mem hUF hAF) (fun y hy => ?_)
    by_contra hyb
    have : y ∈ U ∩ A' := ⟨hy.1, hy.2, hyb⟩
    rw [hemp] at this
    exact this
  have hconv : @xiConv ℝ β I (@nhds ℝ β x ⊓ Filter.principal A') x :=
    ⟨inf_le_left, A', Filter.mem_inf_of_right (Filter.mem_principal_self _), hA'I⟩
  obtain ⟨u, hu, hconvu⟩ := hFU A' x ⟨_, hne, Filter.mem_inf_of_right (Filter.mem_principal_self _), hconv⟩
  have hlim := hseq u x hconvu.1
  have hev : ∀ᶠ n in atTop, u n ∈ Metric.ball x ε := hlim (Metric.ball_mem_nhds x hε)
  obtain ⟨n, hn⟩ := hev.exists
  exact (hu n).2 hn

/-- **Proposition `noFUxi`.** If `ξ_{β,I}` is coarser than the Euclidean convergence and Fréchet–Urysohn, it is the Euclidean
convergence. -/
theorem noFU_xi (β : TopologicalSpace ℝ) [hg : @IsTopologicalAddGroup ℝ β _]
    [ht2 : @T2Space ℝ β] [hsm : @ContinuousConstSMul ℝ ℝ β _] {I : Set (Set ℝ)} (hI : IsIdeal I)
    (hcoarse : ∀ (F : Filter ℝ) (x : ℝ), F ≤ @nhds ℝ eT x → @xiConv ℝ β I F x)
    (hFU : IsFU (@xiConv ℝ β I)) (F : Filter ℝ) (x : ℝ) : @xiConv ℝ β I F x ↔ F ≤ @nhds ℝ eT x := by
  refine ⟨fun h => noFU_xi_of_seq β hI hFU ?_ h, hcoarse F x⟩
  intro a y hy
  exact seq_euclid_of_group_topology β (fun s hs => euclid_le_of_coarse β I hcoarse hs) a y hy

end Q95
end PVG
