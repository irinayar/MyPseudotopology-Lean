import LeanCheck.ChainComp2

/-!
# Completions of `σ_{f,S}` and `β_{f,S}`: density and the packaged theorem
(TVGQ-v7 Theorem `thm:completion`)

`Comp(ℝ, σ_{f,S}) ≅ ℝ_usual × K_S` and `Comp(ℝ, β_{f,S}) ≅ K_ℝ × K_S`, in the form: the embedding
`I_S` (resp. `J_S`) is a topological embedding with dense image into a locally compact Hausdorff, hence
complete, abelian group.
-/

namespace LeanCheck

open Filter Topology

/-- `I_S(ℝ)` is dense in `ℝ × K_S`. -/
theorem ISigma_denseRange (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) :
    DenseRange (ISigma f S) := by
  classical
  refine dense_iff_inter_open.2 (fun U hU ⟨p, hp⟩ => ?_)
  obtain ⟨w, v, hw, hv, hpw, hpv, hsub⟩ := isOpen_prod_iff.1 hU p.1 p.2 hp
  obtain ⟨F', t', ht', hvv⟩ := pd_basic_open p.2 v hv hpv
  obtain ⟨x1, -, hx1⟩ := approx_chars f u hu S ∅ F' 0 p.2 (fun _ => ∅) t' (by simp) ht'
  obtain ⟨n, hn, hnw⟩ := (Hker_dense f (fun a : {a // a ∈ F'} => ((a.1 : S) : ℝ))).exists_mem_open
    (hw.preimage (continuous_const.add continuous_id : Continuous fun y : ℝ => x1 + y))
    ⟨p.1 - x1, by show x1 + (p.1 - x1) ∈ w; rw [add_sub_cancel]; exact hpw⟩
  have hker : ∀ a : {a // a ∈ F'}, f (((a.1 : S) : ℝ) * n) = 0 := by
    intro a
    have := congrFun (AddMonoidHom.mem_ker.mp hn) a
    simpa [Hmap_apply] using this
  refine ⟨ISigma f S (x1 + n), hsub ⟨hnw, hvv _ (fun a ha => ?_)⟩, x1 + n, rfl⟩
  have : jHom f S (x1 + n) a = jHom f S x1 a := by
    rw [map_add, AddMonoidHom.add_apply]
    have h0 : jHom f S n a = 0 := by
      rw [jHom_apply, hker ⟨a, ha⟩]; simp
    rw [h0, add_zero]
  show (jHom f S (x1 + n)) a ∈ t' a
  rw [this]
  exact hx1 a ha

/-- `J_S(ℝ)` is dense in `K_ℝ × K_S`. -/
theorem JBeta_denseRange (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) :
    DenseRange (JBeta f S) := by
  classical
  refine dense_iff_inter_open.2 (fun U hU ⟨p, hp⟩ => ?_)
  obtain ⟨w, v, hw, hv, hpw, hpv, hsub⟩ := isOpen_prod_iff.1 hU p.1 p.2 hp
  obtain ⟨F, t, ht, hww⟩ := pd_basic_open p.1 w hw hpw
  obtain ⟨F', t', ht', hvv⟩ := pd_basic_open p.2 v hv hpv
  obtain ⟨x, hxF, hxF'⟩ := approx_chars f u hu S F F' p.1 p.2 t t' ht ht'
  exact ⟨JBeta f S x, hsub ⟨hww _ hxF, hvv _ hxF'⟩, x, rfl⟩

/-- **Completion of `σ_{f,S}`** (TVGQ-v7 Theorem `thm:completion`, first half):
`I_S : (ℝ, σ_{f,S}) → ℝ_usual × K_S` is a topological embedding with dense range into a locally compact
Hausdorff (hence complete) abelian group; so `Comp(ℝ, σ_{f,S}) ≅ ℝ × K_S`. -/
theorem completion_sigma (f : ℝ →+ ℚ) (hf : f ≠ 0) (S : Submodule ℚ ℝ) :
    @IsInducing ℝ (ℝ × PD S) (sigmaT f S) _ (ISigma f S) ∧ DenseRange (ISigma f S) ∧
      CompleteSpace (ℝ × PD S) ∧ LocallyCompactSpace (ℝ × PD S) ∧ T2Space (ℝ × PD S) := by
  obtain ⟨u, hu⟩ := exists_unit f hf
  exact ⟨ISigma_inducing f S, ISigma_denseRange f u hu S, inferInstance, inferInstance, inferInstance⟩

/-- **Completion of `β_{f,S}`** (TVGQ-v7 Theorem `thm:completion`, second half):
`J_S : (ℝ, β_{f,S}) → K_ℝ × K_S` is a topological embedding with dense range into a compact Hausdorff
abelian group; so `Comp(ℝ, β_{f,S}) ≅ K_ℝ × K_S`. -/
theorem completion_beta (f : ℝ →+ ℚ) (hf : f ≠ 0) (S : Submodule ℚ ℝ) :
    @IsInducing ℝ (PD ℝ × PD S) (betaT f S) _ (JBeta f S) ∧ DenseRange (JBeta f S) ∧
      CompactSpace (PD ℝ × PD S) ∧ CompleteSpace (PD ℝ × PD S) ∧ T2Space (PD ℝ × PD S) := by
  obtain ⟨u, hu⟩ := exists_unit f hf
  exact ⟨JBeta_inducing f S, JBeta_denseRange f u hu S, inferInstance, inferInstance, inferInstance⟩

end LeanCheck
