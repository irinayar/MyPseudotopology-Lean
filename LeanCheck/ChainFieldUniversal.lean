import LeanCheck.ChainUniversal2
import LeanCheck.ChainArtinSchreier

/-!
# Corollary `field-universal` (TVGQ-v7): intermediate fields

For an intermediate field `F` of `ℝ/ℚ`, a universal separating sequence exists iff `[ℝ : F] < ∞`, iff `F = ℝ`.
The finite-covering criterion `universal_complete` becomes finite-dimensionality of `ℝ` over `F`, and the
Artin–Schreier theorem (`finite_index_subfield_real`) turns that into `F = ℝ`.
(The second assertion of the corollary, for subspaces of finite rational codimension, is
`finite_codim_universal`.)
-/

namespace LeanCheck

open Filter Topology

/-- The finite covering condition for a subfield is finite-dimensionality of `ℝ` over `F`. -/
theorem field_cover_iff (F : IntermediateField ℚ ℝ) :
    (∃ T : Finset ℝ, (⨆ t : T, (Subalgebra.toSubmodule F.toSubalgebra).map
        (LinearMap.mulLeft ℚ (t : ℝ))) = ⊤) ↔ FiniteDimensional F ℝ := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨⟨T, ?_⟩⟩
    rw [eq_top_iff]
    have hle : (⊤ : Submodule ℚ ℝ) ≤ (Submodule.span F (T : Set ℝ)).restrictScalars ℚ := by
      rw [← hT]
      refine iSup_le fun t => ?_
      rintro _ ⟨s, hs, rfl⟩
      have hs' : (s : ℝ) ∈ F := hs
      have : (⟨s, hs'⟩ : F) • (t : ℝ) ∈ Submodule.span F (T : Set ℝ) :=
        Submodule.smul_mem _ _ (Submodule.subset_span t.2)
      simpa [Algebra.smul_def, mul_comm] using this
    intro x _
    exact hle (Submodule.mem_top)
  · intro hfin
    obtain ⟨s, hs⟩ := (Module.finite_def.1 hfin)
    refine ⟨s, ?_⟩
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span F (s : Set ℝ) := by rw [hs]; exact Submodule.mem_top
    obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.1 hx
    refine Submodule.sum_mem _ (fun y hy => ?_)
    exact Submodule.mem_iSup_of_mem (⟨y, hy⟩ : {t // t ∈ s}) ⟨(f y : ℝ), (f y).2, by
      simp [Algebra.smul_def, mul_comm]⟩

/-- **Corollary `field-universal`.** For an intermediate field `F`, a universal separating sequence exists
iff `[ℝ : F] < ∞`, iff `F = ℝ`; in particular no proper intermediate field admits one. -/
theorem field_universal (F : IntermediateField ℚ ℝ) :
    (∃ x : ℕ → ℝ, ∀ g : ℝ →+ ℚ, g ≠ 0 →
      Tendsto x atTop (@nhds ℝ (sigmaT g (Subalgebra.toSubmodule F.toSubalgebra)) 0) ∧
      ¬ Tendsto x atTop (@nhds ℝ (tauT g (Subalgebra.toSubmodule F.toSubalgebra)) 0)) ↔ F = ⊤ := by
  have hS : ∃ a ∈ Subalgebra.toSubmodule F.toSubalgebra, a ≠ 0 := ⟨1, F.one_mem, one_ne_zero⟩
  rw [universal_complete _ hS, field_cover_iff]
  constructor
  · intro hfin
    exact finite_index_subfield_real F
  · intro h
    subst h
    refine ⟨⟨{1}, ?_⟩⟩
    rw [eq_top_iff]
    intro x _
    rw [Finset.coe_singleton, Submodule.mem_span_singleton]
    exact ⟨⟨x, trivial⟩, by simp [Algebra.smul_def]⟩

end LeanCheck
