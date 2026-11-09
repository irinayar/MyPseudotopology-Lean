import LeanCheck.PVGClosed
import LeanCheck.PVGInterpolation

/-!
# PVG: sequences and the Fréchet–Urysohn property (Lean check)

Scope. The first half of Section 8 of `PVG_v19` ("Sequences and the Fréchet–Urysohn property"), for the PVGs of Sections 3 to 7.
`IsFU` is the Fréchet–Urysohn property of `PVGNonzero`; a sequence `a` converges to `x` for `conv` if `conv (map a atTop) x`.

* `bohrseq` (Proposition `bohrseq`): a real sequence converges in the Bohr topology iff it converges in the Euclidean topology
  (from Proposition `bohrseq`8 for `G = 0`);
* `xiB`, `xiB_seq`, `xiB_euclid_of_FU`, `xiB_eq_euclid_of_FU` (Theorem `notFU` (a), (b), (c)): for an ideal `I` and `ξ = ξ_{τ_B, I}`;
* `lac_not_FU`, `lac_seq_iff` (Corollary `notFU` (a), (b)): the lacunary PVG of Theorem 7.4 is not Fréchet–Urysohn, and its convergent
  sequences are the Euclidean convergent ones;
* `beta_open_mod`, `relaxed_closed`, `relaxed_strict`, `finite_closed` (Propositions `finite` and `relaxed`): `τ_ξ` is finer than `β`; sets whose
  traces on the members of the ideal are `β`-closed are `τ_ξ`-closed;
* `countable_isFU`, `countable_modTop` (Proposition `ctblFU`): the countable PVG is Fréchet–Urysohn, with Euclidean topological modification.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology Pointwise Cardinal

namespace PVG
namespace Q95

/-! ### Proposition `bohrseq`: sequences in the Bohr topology -/

theorem bohrseq (a : ℕ → ℝ) (x : ℝ) : bohrConv (Filter.map a atTop) x ↔ Tendsto a atTop (𝓝 x) := by
  constructor
  · intro h
    by_cases hb : ∃ M, ∀ n, |a n| ≤ M
    · exact seqG_bounded bohrConv_isPVG bohrConv_hausdorff (fun F x h => h) a x hb h
    · push Not at hb
      exfalso
      have h1 := seqG_unbounded ⊥ a x hb ((etaConv_bot_iff _ _).2 h)
      rw [rank_bot] at h1
      exact absurd h1.symm ((Cardinal.zero_le (#ℝ)).trans_lt (Cardinal.cantor _)).ne'
  · intro h
    unfold bohrConv
    rw [Filter.tendsto_map'_iff]
    exact (continuous_e.tendsto x).comp h

/-! ### Theorem `notFU` -/

/-- `ξ_{τ_B, I}`. -/
abbrev xiB (I : Set (Set ℝ)) : Filter ℝ → ℝ → Prop := @xiConv ℝ bohrTop I

/-- Theorem `notFU` (a): sequences converging for `ξ` converge in the Euclidean topology. -/
theorem xiB_seq {I : Set (Set ℝ)} {a : ℕ → ℝ} {x : ℝ} (h : xiB I (Filter.map a atTop) x) :
    Tendsto a atTop (𝓝 x) :=
  (bohrseq a x).1 ((bohrConv_iff _ _).2 h.1)

/-- Bounded sets belong to an ideal containing `(-1,1)`. -/
lemma bounded_mem_of_ball {I : Set (Set ℝ)} (hI : IsIdeal I) (hball : Metric.ball (0 : ℝ) 1 ∈ I) {A : Set ℝ} {M : ℝ}
    (hA : ∀ a ∈ A, |a| ≤ M) : A ∈ I := by
  have hM : (0 : ℝ) < |M| + 1 := by positivity
  have hsm : ((|M| + 1) • Metric.ball (0 : ℝ) 1) ∈ I := hI.smul _ hball
  refine hI.mono hsm (fun a ha => ?_)
  refine ⟨a / (|M| + 1), ?_, by simp [smul_eq_mul]; field_simp⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_div, abs_of_pos hM, div_lt_one hM]
  have := hA a ha
  have := le_abs_self M
  linarith

/-- Theorem `notFU` (b): if `ξ_{τ_B,I}` is Fréchet–Urysohn then `ξ`-convergence implies Euclidean convergence. -/
theorem xiB_euclid_of_FU {I : Set (Set ℝ)} (hI : IsIdeal I) (hFU : IsFU (xiB I)) {F : Filter ℝ} {x : ℝ}
    (hF : xiB I F x) : F ≤ 𝓝 x := by
  by_contra hno
  rw [Filter.le_def] at hno
  push Not at hno
  obtain ⟨W, hW, hWF⟩ := hno
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
  have hballF : Metric.ball x ε ∉ F := fun h => hWF (Filter.mem_of_superset h hball)
  obtain ⟨A, hAF, hAI⟩ := hF.2
  set A' : Set ℝ := A \ Metric.ball x ε with hA'
  have hA'I : A' ∈ I := hI.mono hAI Set.diff_subset
  have hne : (@nhds ℝ bohrTop x ⊓ 𝓟 A').NeBot := by
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
  have hconv : xiB I (@nhds ℝ bohrTop x ⊓ 𝓟 A') x :=
    ⟨inf_le_left, A', Filter.mem_inf_of_right (Filter.mem_principal_self _), hA'I⟩
  obtain ⟨u, hu, hconvu⟩ := hFU A' x ⟨_, hne, Filter.mem_inf_of_right (Filter.mem_principal_self _), hconv⟩
  have hlim := xiB_seq hconvu
  have hev : ∀ᶠ n in atTop, u n ∈ Metric.ball x ε := hlim (Metric.ball_mem_nhds x hε)
  obtain ⟨n, hn⟩ := hev.exists
  exact (hu n).2 hn

/-- Theorem `notFU` (c): if `ξ_{τ_B,I}` is Fréchet–Urysohn and `(-1,1) ∈ I`, it is the Euclidean convergence. -/
theorem xiB_eq_euclid_of_FU {I : Set (Set ℝ)} (hI : IsIdeal I) (hball : Metric.ball (0 : ℝ) 1 ∈ I)
    (hFU : IsFU (xiB I)) (F : Filter ℝ) (x : ℝ) : xiB I F x ↔ F ≤ 𝓝 x := by
  refine ⟨fun h => xiB_euclid_of_FU hI hFU h, fun h => ?_⟩
  refine ⟨h.trans (bohr_coarser_euclid x), Metric.ball x 1, h (Metric.ball_mem_nhds x one_pos), ?_⟩
  refine bounded_mem_of_ball hI hball (M := |x| + 1) (fun a ha => ?_)
  rw [Metric.mem_ball, Real.dist_eq] at ha
  have h1 : |a| ≤ |a - x| + |x| := by
    have := abs_add_le (a - x) x
    simpa using this
  linarith

/-! ### Corollary `notFU` -/

/-- `lacConv = ξ_{τ_B, I_S}` is `xiB IS`. -/
lemma lacConv_eq_xiB : Lac.lacConv = xiB Lac.IS := rfl

/-- Corollary `notFU` (a): the PVG of Theorem 7.4 is not Fréchet–Urysohn. -/
theorem lac_not_FU : ¬ IsFU Lac.lacConv := by
  intro hFU
  obtain ⟨F, hF, hnot⟩ := Lac.lac_not_euclid
  have hball : Metric.ball (0 : ℝ) 1 ∈ Lac.IS :=
    Lac.bounded_mem_IS (M := 1) (fun a ha => by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ha; exact ha.le)
  exact hnot (((xiB_eq_euclid_of_FU Lac.IS_isIdeal hball hFU F 0).1 hF))

/-- Corollary `notFU` (b): a sequence converges for `lacConv` iff it converges in the Euclidean topology. -/
theorem lac_seq_iff (a : ℕ → ℝ) (x : ℝ) : Lac.lacConv (Filter.map a atTop) x ↔ Tendsto a atTop (𝓝 x) :=
  ⟨fun h => xiB_seq h, fun h => Lac.lac_coarser_euclid h⟩

/-! ### Propositions `finite` and `relaxed`: closed sets of the topological modification -/

section Relaxed

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousConstSMul ℝ X] {I : Set (Set X)}

/-- Every `β`-open set is open in the topological modification of `ξ_{β,I}`. -/
theorem beta_open_mod {U : Set X} (hU : IsOpen U) : @IsOpen X (modTop (xiConv I)) U := by
  intro x hx F hF
  exact hF.1 (hU.mem_nhds hx)

/-- Proposition `relaxed`: if every trace `J ∩ C` (`J ∈ I`) is `β`-closed then `C` is closed in the topological modification. -/
theorem relaxed_closed {C : Set X} (hC : ∀ J ∈ I, IsClosed (J ∩ C)) : @IsOpen X (modTop (xiConv I)) Cᶜ := by
  rw [mem_modTop_iff]
  intro J hJ
  have hdiff : J \ Cᶜ = J ∩ C := by ext z; simp
  rw [hdiff, (hC J hJ).closure_eq]
  rw [Set.eq_empty_iff_forall_notMem]
  rintro z ⟨⟨_, hz⟩, hzc⟩
  exact hzc hz

/-- If moreover `C` is not `β`-closed, the modification is strictly finer than `β`. -/
theorem relaxed_strict {C : Set X} (hC : ∀ J ∈ I, IsClosed (J ∩ C)) (hnot : ¬ IsClosed C) :
    ∃ U : Set X, @IsOpen X (modTop (xiConv I)) U ∧ ¬ IsOpen U := by
  refine ⟨Cᶜ, relaxed_closed hC, ?_⟩
  intro h
  exact hnot (isOpen_compl_iff.1 h)

/-- Proposition `finite`: if `C ∩ J` is finite for every `J ∈ I`, in a `T₁` space. -/
theorem finite_closed [T1Space X] {C : Set X} (hC : ∀ J ∈ I, (J ∩ C).Finite) :
    @IsOpen X (modTop (xiConv I)) Cᶜ :=
  relaxed_closed (fun J hJ => (hC J hJ).isClosed)

end Relaxed

/-! ### Proposition `ctblFU`: the countable PVG is Fréchet–Urysohn -/

theorem countable_isFU : IsFU countableConv := by
  rintro A x ⟨F, hne, hAF, hF⟩
  obtain ⟨hle, K, hK, hKc⟩ := hF
  have hAK : A ∩ K ∈ F := Filter.inter_mem hAF hK
  haveI := hne
  have hcl : x ∈ closure (A ∩ K) :=
    mem_closure_of_tendsto (f := id) hle (Filter.eventually_of_mem hAK (fun _ h => h))
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  refine ⟨u, fun n => (hu n).1, ?_⟩
  refine ⟨hlim, Set.range u, ?_, hKc.mono ?_⟩
  · exact Filter.mem_map.2 (Filter.mem_of_superset Filter.univ_mem (fun n _ => ⟨n, rfl⟩))
  · rintro _ ⟨n, rfl⟩; exact (hu n).2

#print axioms bohrseq
#print axioms xiB_seq
#print axioms xiB_euclid_of_FU
#print axioms xiB_eq_euclid_of_FU
#print axioms lac_not_FU
#print axioms lac_seq_iff
#print axioms relaxed_closed
#print axioms countable_isFU

end Q95
end PVG
