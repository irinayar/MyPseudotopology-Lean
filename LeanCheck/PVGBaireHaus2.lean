import Mathlib
import LeanCheck.PVGBaireHaus

/-!
# PVG: consequences of Theorem A (Lean check)

Scope. Corollary 8.59 of PVG_v26 (see `PVGBaireHaus.lean` for Theorem A, `theorem_A`).

* `seq_euclid_of_hausdorff`: let `conv` be a PVG on `ℝ` that is coarser than the Euclidean convergence and whose modification is Hausdorff
  (two different points have disjoint `conv`-open neighbourhoods). Then every `conv`-convergent sequence converges in the Euclidean
  topology. (A sequence that is not Euclidean convergent has either an unbounded translate, which Theorem A excludes, or a bounded
  subsequence with a Euclidean limit different from the `conv`-limit, which Hausdorffness excludes.)
* `noFU_xi_of_xiseq`: the argument of `noFU_xi_of_seq` with the hypothesis on `ξ`-convergent sequences instead of `β`-convergent ones;
* `noFU_of_hausdorff_topology`: Proposition `noFUxi` for `ξ_{γ,I}` where `γ` is an arbitrary Hausdorff topology on `ℝ` for which `ξ_{γ,I}`
  is a PVG; no group structure of `γ` and no admissibility of the pair is assumed. If `ξ_{γ,I}` is coarser than the Euclidean convergence
  and Fréchet–Urysohn, it is the Euclidean convergence.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Q95

/-- If the modification is Hausdorff, every `conv`-convergent sequence converges in the Euclidean topology. -/
theorem seq_euclid_of_hausdorff {conv : Filter ℝ → ℝ → Prop} (hP : IsPVG conv)
    (hcoarse : ∀ (F : Filter ℝ) (x : ℝ), F ≤ 𝓝 x → conv F x)
    (hHaus : ∀ x y : ℝ, x ≠ y → ∃ O O' : Set ℝ, ConvOpen conv O ∧ ConvOpen conv O' ∧ x ∈ O ∧ y ∈ O' ∧ Disjoint O O')
    (a : ℕ → ℝ) (x : ℝ) (ha : conv (Filter.map a atTop) x) : Tendsto a atTop (𝓝 x) := by
  by_contra hno
  rw [Metric.tendsto_nhds] at hno
  push Not at hno
  obtain ⟨ε, hε, hfreq⟩ := hno
  have hfreq' : ∃ᶠ n in atTop, ε ≤ dist (a n) x := by
    refine Filter.Frequently.mono hfreq ?_
    intro n hn
    exact hn
  by_cases hb : ∃ (R : ℝ) (N : ℕ), ∀ n ≥ N, dist (a n) x ≤ R
  · obtain ⟨R, N, hRN⟩ := hb
    set s : Set ℝ := Metric.closedBall x R \ Metric.ball x ε with hs
    have hsb : Bornology.IsBounded s := Metric.isBounded_closedBall.subset Set.sdiff_subset
    have hfs : ∃ᶠ n in atTop, a n ∈ s := by
      have := hfreq'.and_eventually (eventually_ge_atTop N)
      refine this.mono ?_
      rintro n ⟨h1, h2⟩
      refine ⟨Metric.mem_closedBall.2 (hRN n h2), ?_⟩
      rw [Metric.mem_ball, not_lt]
      exact h1
    obtain ⟨l, hl, φ, hφ, hlim⟩ := tendsto_subseq_of_frequently_bounded hsb hfs
    have hlx : l ≠ x := by
      intro h
      have hcl : closure s ⊆ {y | ε ≤ dist y x} := by
        refine closure_minimal (fun y hy => ?_) (isClosed_le continuous_const (continuous_id.dist continuous_const))
        have := hy.2
        rw [Metric.mem_ball, not_lt] at this
        exact this
      have h2 := hcl hl
      simp only [Set.mem_setOf_eq] at h2
      rw [h, dist_self] at h2
      linarith
    have hconvl : conv (Filter.map (a ∘ φ) atTop) l := hcoarse _ _ hlim
    have hconvx : conv (Filter.map (a ∘ φ) atTop) x := by
      refine hP.p2 ha ?_
      rw [← Filter.map_map]
      exact Filter.map_mono hφ.tendsto_atTop
    obtain ⟨O, O', hO, hO', hlO, hxO', hd⟩ := hHaus l x hlx
    have h1 : O ∈ Filter.map (a ∘ φ) atTop := hO l hlO _ hconvl
    have h2 : O' ∈ Filter.map (a ∘ φ) atTop := hO' x hxO' _ hconvx
    have h3 : (∅ : Set ℝ) ∈ Filter.map (a ∘ φ) atTop := by
      have := Filter.inter_mem h1 h2
      rwa [Set.disjoint_iff_inter_eq_empty.1 hd] at this
    have : (Filter.map (a ∘ φ) atTop).NeBot := Filter.map_neBot
    exact (Filter.NeBot.ne inferInstance) (Filter.empty_mem_iff_bot.1 h3)
  · push Not at hb
    have hu : conv (Filter.map (fun n => a n - x) atTop) 0 := by
      have h1 := hP.add ha (hP.p1 (-x))
      rw [Filter.map₂_pure_right, add_neg_cancel] at h1
      have e : Filter.map (fun b => b + -x) (Filter.map a atTop) = Filter.map (fun n => a n - x) atTop := by
        rw [Filter.map_map]
        rfl
      rw [e] at h1
      exact h1
    have hunb : ∀ R : ℝ, ∀ N : ℕ, ∃ n ≥ N, R < |a n - x| := by
      intro R N
      obtain ⟨n, hn, hR⟩ := hb R N
      exact ⟨n, hn, by rwa [Real.dist_eq] at hR⟩
    obtain ⟨O, O', hO, hO', h0, h1, hd⟩ := hHaus 0 1 zero_ne_one
    have := theorem_A hP hcoarse hu hunb 1 hO h0 hO' h1
    rw [Set.disjoint_iff_inter_eq_empty.1 hd] at this
    exact Set.not_nonempty_empty this

/-- The argument of `noFU_xi_of_seq`, with the hypothesis on `ξ`-convergent sequences. -/
theorem noFU_xi_of_xiseq (β : TopologicalSpace ℝ) {I : Set (Set ℝ)} (hI : IsIdeal I)
    (hFU : IsFU (@xiConv ℝ β I))
    (hseq : ∀ (a : ℕ → ℝ) (x : ℝ), @xiConv ℝ β I (Filter.map a atTop) x → Tendsto a atTop (@nhds ℝ eT x))
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
  have hlim := hseq u x hconvu
  have hev : ∀ᶠ n in atTop, u n ∈ Metric.ball x ε := hlim (Metric.ball_mem_nhds x hε)
  obtain ⟨n, hn⟩ := hev.exists
  exact (hu n).2 hn

/-- **Corollary 8.59.** `ξ_{γ,I}` for an arbitrary Hausdorff topology `γ` on `ℝ` such that `ξ_{γ,I}` is a PVG: if it is coarser than the
Euclidean convergence and Fréchet–Urysohn, it is the Euclidean convergence. -/
theorem noFU_of_hausdorff_topology (γ : TopologicalSpace ℝ) [ht2 : @T2Space ℝ γ] {I : Set (Set ℝ)} (hI : IsIdeal I)
    (hP : IsPVG (@xiConv ℝ γ I)) (hcoarse : ∀ (F : Filter ℝ) (x : ℝ), F ≤ @nhds ℝ eT x → @xiConv ℝ γ I F x)
    (hFU : IsFU (@xiConv ℝ γ I)) (F : Filter ℝ) (x : ℝ) : @xiConv ℝ γ I F x ↔ F ≤ @nhds ℝ eT x := by
  refine ⟨fun h => noFU_xi_of_xiseq γ hI hFU ?_ h, hcoarse F x⟩
  have hHaus : ∀ x y : ℝ, x ≠ y → ∃ O O' : Set ℝ, ConvOpen (@xiConv ℝ γ I) O ∧ ConvOpen (@xiConv ℝ γ I) O' ∧ x ∈ O ∧
      y ∈ O' ∧ Disjoint O O' := by
    intro x y hxy
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := @t2_separation ℝ γ ht2 x y hxy
    exact ⟨U, V, fun z hz G hG => hG.1 (@IsOpen.mem_nhds ℝ γ z U hU hz),
      fun z hz G hG => hG.1 (@IsOpen.mem_nhds ℝ γ z V hV hz), hxU, hyV, hUV⟩
  intro a y hy
  exact seq_euclid_of_hausdorff hP hcoarse hHaus a y hy

#print axioms seq_euclid_of_hausdorff
#print axioms noFU_of_hausdorff_topology

end Q95
end PVG
