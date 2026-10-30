import LeanCheck.ChainU2

/-!
# Compact-set tests
(HamelCharactersTVG_v18 Proposition 14.3 `prop:compact-tests`)

A subset `C ⊆ ℝ` is compact for `σ_f` iff it is usual-compact and each `x ↦ p(f(a x))` is usual-continuous on `C`;
it is compact for `τ_f` iff it is usual-compact and each `x ↦ f(a x) ∈ ℚ_usual` is usual-continuous on `C`.
For `β_f` we prove: usual-compact + continuity ⇒ `β_f`-compact (the converse direction is Glicksberg's theorem and
is not formalized).
-/

namespace LeanCheck

open Filter Topology

section CompactTests

lemma isCompact_of_le' {X : Type*} {t u : TopologicalSpace X} (hle : t ≤ u) {C : Set X} (hC : @IsCompact X t C) :
    @IsCompact X u C := by
  have := @IsCompact.image X X t u C id hC (continuous_id_of_le hle)
  simpa using this

/-- A compact subset of a finer topology has the same neighbourhood filters within it, when the coarser topology is
Hausdorff. -/
lemma nhdsWithin_eq_of_compact {X : Type*} (t u : TopologicalSpace X) (hle : t ≤ u) (hT2 : @T2Space X u)
    (C : Set X) (hC : @IsCompact X t C) (x : X) (hx : x ∈ C) :
    @nhdsWithin X t x C = @nhdsWithin X u x C := by
  apply le_antisymm
  · exact inf_le_inf_right _ (nhds_mono hle)
  · rw [Filter.le_def]
    intro S hS
    obtain ⟨V, hVt, hxV, hVS⟩ : ∃ V, @IsOpen X t V ∧ x ∈ V ∧ V ∩ C ⊆ S := by
      rw [@mem_nhdsWithin X t] at hS
      obtain ⟨V, hVo, hxV, hVS⟩ := hS
      exact ⟨V, hVo, hxV, hVS⟩
    have hK : @IsCompact X t (C \ V) := @IsCompact.diff X t C V hC hVt
    have hKu : @IsCompact X u (C \ V) := isCompact_of_le' hle hK
    have hclosed : @IsClosed X u (C \ V) := @IsCompact.isClosed X u hT2 (C \ V) hKu
    rw [@mem_nhdsWithin X u]
    refine ⟨(C \ V)ᶜ, hclosed.isOpen_compl, ?_, ?_⟩
    · intro hx'
      exact hx'.2 hxV
    · rintro y ⟨hy1, hy2⟩
      apply hVS
      refine ⟨?_, hy2⟩
      by_contra hyV
      exact hy1 ⟨hy2, hyV⟩

/-- A map continuous for the finer topology is continuous on a finer-compact set for the coarser Hausdorff one. -/
lemma continuousOn_of_compact_finer {X Y : Type*} (t u : TopologicalSpace X) (hle : t ≤ u) (hT2 : @T2Space X u)
    (vY : TopologicalSpace Y) (g : X → Y) (hg : @Continuous X Y t vY g) (C : Set X)
    (hC : @IsCompact X t C) : @ContinuousOn X Y u vY g C := by
  intro x hx
  have h0 : @Tendsto X Y g (@nhds X t x) (@nhds Y vY (g x)) := @Continuous.tendsto X Y t vY g hg x
  have h1 : @Tendsto X Y g (@nhdsWithin X t x C) (@nhds Y vY (g x)) := h0.mono_left inf_le_left
  rw [nhdsWithin_eq_of_compact t u hle hT2 C hC x hx] at h1
  exact h1

/-- **Compact-set test for `σ_f`.** -/
theorem compact_sigma_iff (f : ℝ →+ ℚ) (C : Set ℝ) :
    @IsCompact ℝ (sigmaT f ⊤) C ↔
      IsCompact C ∧ ∀ a : ℝ, ContinuousOn (fun x : ℝ => (((f (a * x) : ℚ) : ℝ) : Circ)) C := by
  constructor
  · intro hC
    refine ⟨isCompact_of_le' (sigmaT_le_usual f ⊤) hC, fun a => ?_⟩
    have hcont : @Continuous ℝ Circ (sigmaT f ⊤) circTop (fun x : ℝ => (((f (a * x) : ℚ) : ℝ) : Circ)) := by
      rw [continuous_iff_le_induced, sigmaT_eq_A]
      exact inf_le_right.trans (iInf_le (fun a : (⊤ : Submodule ℚ ℝ) => TopologicalSpace.induced
        (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop) ⟨a, trivial⟩)
    exact continuousOn_of_compact_finer (sigmaT f ⊤) (inferInstance : TopologicalSpace ℝ) (sigmaT_le_usual f ⊤)
      (show @T2Space ℝ (inferInstance : TopologicalSpace ℝ) from inferInstance) circTop _ hcont C hC
  · rintro ⟨hC, hg⟩
    have hcont : Continuous[(inferInstance : TopologicalSpace C), sigmaT f ⊤] (fun x : C => (x : ℝ)) := by
      rw [sigmaT_eq_A]
      refine continuous_inf_rng.2 ⟨continuous_subtype_val, continuous_iInf_rng.2 (fun a => ?_)⟩
      exact continuous_induced_rng.2 ((hg (a : ℝ)).restrict)
    have hcomp : IsCompact (Set.univ : Set C) := (isCompact_iff_compactSpace.1 hC).isCompact_univ
    have := @IsCompact.image C ℝ _ (sigmaT f ⊤) Set.univ (fun x : C => (x : ℝ)) hcomp hcont
    simpa using this

/-- **Compact-set test for `τ_f`.** -/
theorem compact_tau_iff (f : ℝ →+ ℚ) (C : Set ℝ) :
    @IsCompact ℝ (tauT f ⊤) C ↔
      IsCompact C ∧ ∀ a : ℝ, ContinuousOn (fun x : ℝ => ((f (a * x) : ℚ) : ℝ)) C := by
  constructor
  · intro hC
    have hle : tauT f ⊤ ≤ (inferInstance : TopologicalSpace ℝ) := (tauT_le_sigmaT f ⊤).trans (sigmaT_le_usual f ⊤)
    refine ⟨isCompact_of_le' hle hC, fun a => ?_⟩
    exact continuousOn_of_compact_finer (tauT f ⊤) (inferInstance : TopologicalSpace ℝ) hle
      (show @T2Space ℝ (inferInstance : TopologicalSpace ℝ) from inferInstance) _ _ (faR_cont_tau f ⊤ a trivial) C hC
  · rintro ⟨hC, hg⟩
    have hcont : Continuous[(inferInstance : TopologicalSpace C), tauT f ⊤] (fun x : C => (x : ℝ)) := by
      unfold tauT TfS
      refine continuous_inf_rng.2 ⟨continuous_subtype_val, continuous_iInf_rng.2 (fun a => ?_)⟩
      refine continuous_induced_rng.2 ?_
      have : Continuous (fun x : C => ((fa f (a : ℝ) (x : ℝ) : ℚ) : ℝ)) := (hg (a : ℝ)).restrict
      exact (Rat.isEmbedding_coe_real.continuous_iff).2 this
    have hcomp : IsCompact (Set.univ : Set C) := (isCompact_iff_compactSpace.1 hC).isCompact_univ
    have := @IsCompact.image C ℝ _ (tauT f ⊤) Set.univ (fun x : C => (x : ℝ)) hcomp hcont
    simpa using this

/-- **Compact-set test for `β_f`** (the direction not requiring Glicksberg's theorem). -/
theorem compact_beta_of (f : ℝ →+ ℚ) (C : Set ℝ) (hC : IsCompact C)
    (hg : ∀ a : ℝ, ContinuousOn (fun x : ℝ => (((f (a * x) : ℚ) : ℝ) : Circ)) C) :
    @IsCompact ℝ (betaT f ⊤) C :=
  isCompact_of_le' (sigmaT_le_betaT f ⊤) ((compact_sigma_iff f C).2 ⟨hC, hg⟩)

end CompactTests

end LeanCheck
