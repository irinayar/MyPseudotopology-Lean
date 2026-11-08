import LeanCheck.PVGExamples
import LeanCheck.PVGClassify

/-!
# PVG: the Bohr topology on `ℝ` (Lean check)

Scope. Formal counterpart of Section 5 of `PVG_v19`. The Bohr topology `bohrTop` is the topology on `ℝ` induced by `e : ℝ → K`,
`K = Hom(ℝ, 𝕋)`, i.e. the topology of pointwise convergence of the characters `t ↦ e^{iωt}` (the sets `x + W(ω₁,…,ω_r; η)` of
the article form a neighbourhood base of this topology; the identification of the two descriptions is by the product topology of
`K`).

* `bohr_isTopologicalAddGroup`, `bohr_t2`, `bohr_constSMul`, `bohr_coarser_euclid` (Proposition 5.1 (a), (b), (c)): `bohrTop` is a
  Hausdorff group topology on `ℝ`, dilations are continuous, and every Euclidean neighbourhood of `x` is a Bohr neighbourhood
  filter's superset (`𝓝 x ≤ 𝓝_B x`);
* `bohr_unbounded` (Proposition 5.1 (d)): every Bohr neighbourhood of `0` is unbounded (pigeonhole in the compact group `K`);
* `bohrConv_isPVG`, `bohr_not_euclid`, `bohr_not_jointCont` (Corollary 5.2): the Bohr convergence is a Hausdorff PVG, coarser than
  the Euclidean one, not the Euclidean one, and its scalar multiplication is not jointly continuous (Theorem 4.1).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology Pointwise

namespace PVG
namespace Q95

/-- `e` as an additive homomorphism. -/
def eHom : ℝ →+ K where
  toFun := e
  map_zero' := e_zero
  map_add' := e_add

/-- The Bohr topology on `ℝ`: induced by `e`. -/
def bohrTop : TopologicalSpace ℝ := TopologicalSpace.induced e inferInstance

lemma bohrTop_eq : bohrTop = TopologicalSpace.induced eHom inferInstance := rfl

lemma nhds_bohr (x : ℝ) : @nhds ℝ bohrTop x = Filter.comap e (𝓝 (e x)) := by
  unfold bohrTop; rw [nhds_induced]

lemma bohrConv_iff (F : Filter ℝ) (x : ℝ) : bohrConv F x ↔ F ≤ @nhds ℝ bohrTop x := by
  rw [nhds_bohr]; unfold bohrConv; exact Filter.tendsto_iff_comap

/-- Proposition 5.1 (a): a group topology. -/
theorem bohr_isTopologicalAddGroup : @IsTopologicalAddGroup ℝ bohrTop _ := by
  rw [bohrTop_eq]; exact topologicalAddGroup_induced eHom

/-- Proposition 5.1 (a): Hausdorff. -/
theorem bohr_t2 : @T2Space ℝ bohrTop := by
  letI : TopologicalSpace ℝ := bohrTop
  have : Topology.IsEmbedding e := ⟨⟨rfl⟩, e_injective'⟩
  exact this.t2Space

/-- Proposition 5.1 (b): the dilations are continuous. -/
theorem bohr_constSMul : @ContinuousConstSMul ℝ ℝ bohrTop _ := by
  letI : TopologicalSpace ℝ := bohrTop
  refine ⟨fun a => ?_⟩
  have hind : Topology.IsInducing e := ⟨rfl⟩
  rw [hind.continuous_iff]
  have : (e ∘ fun x : ℝ => a • x) = fun x => a • e x := by
    funext x; simp [Function.comp, smul_e]
  rw [this]
  exact (continuous_smul_const a).comp hind.continuous

/-- Proposition 5.1 (c): the Bohr topology is coarser than the Euclidean one. -/
theorem bohr_coarser_euclid (x : ℝ) : 𝓝 x ≤ @nhds ℝ bohrTop x := by
  rw [nhds_bohr]
  exact Filter.tendsto_iff_comap.1 (continuous_e.tendsto x)

/-- Proposition 5.1 (d): every Bohr neighbourhood of `0` is unbounded. -/
theorem bohr_unbounded {W : Set ℝ} (hW : W ∈ @nhds ℝ bohrTop 0) (b : ℝ) : ∃ t ∈ W, b < |t| := by
  rw [nhds_bohr, e_zero] at hW
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.1 hW
  set M : ℝ := |b| + 1 with hM
  have hM0 : 0 < M := by positivity
  set z : ℕ → K := fun j => e ((j : ℝ) * M) with hz
  obtain ⟨κ, hκ⟩ := exists_clusterPt_of_compactSpace (Filter.map z atTop)
  have hsub : ∃ V1 ∈ 𝓝 κ, ∀ a ∈ V1, ∀ c ∈ V1, a - c ∈ V := by
    have h1 : Tendsto (fun p : K × K => p.1 - p.2) (𝓝 (κ, κ)) (𝓝 (κ - κ)) :=
      (continuous_sub.tendsto (κ, κ))
    rw [sub_self] at h1
    have h2 := h1 hV
    rw [nhds_prod_eq, Filter.mem_map, mem_prod_self_iff] at h2
    obtain ⟨V1, hV1, hV1sub⟩ := h2
    exact ⟨V1, hV1, fun a ha c hc => hV1sub (Set.mk_mem_prod ha hc)⟩
  obtain ⟨V1, hV1, hV1V⟩ := hsub
  have hfreq : ∃ᶠ j in atTop, z j ∈ V1 := (mapClusterPt_iff_frequently.1 hκ) V1 hV1
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨j₀, -, hj₀⟩ := hfreq 0
  obtain ⟨l, hl, hlV⟩ := hfreq (j₀ + 1)
  refine ⟨((l : ℝ) - j₀) * M, ?_, ?_⟩
  · apply hVW
    show e (((l : ℝ) - j₀) * M) ∈ V
    have : ((l : ℝ) - j₀) * M = (l : ℝ) * M - (j₀ : ℝ) * M := by ring
    rw [this, e_sub]
    exact hV1V _ hlV _ hj₀
  · have h1 : (1 : ℝ) ≤ (l : ℝ) - j₀ := by
      have : ((j₀ + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
      push_cast at this; linarith
    rw [abs_mul, abs_of_pos hM0, abs_of_nonneg (by linarith)]
    have : M ≤ ((l : ℝ) - j₀) * M := by nlinarith
    have h2 : b ≤ |b| := le_abs_self b
    linarith

/-- The Bohr convergence is a PVG pseudotopology. -/
theorem bohrConv_isPVG : IsPVG bohrConv where
  p1 x := by
    unfold bohrConv
    exact tendsto_pure_nhds e x
  p2 := fun hF hGF => Filter.Tendsto.mono_left hF hGF
  p3 := by
    intro F _ x hU
    unfold bohrConv
    exact (Filter.tendsto_iff_ultrafilter _ _ _).2 (fun U hUF => hU U hUF)
  add := by
    intro F G x y hF hG
    unfold bohrConv at *
    rw [← Filter.map_prod_eq_map₂ (fun a b : ℝ => a + b), Filter.tendsto_map'_iff]
    have h1 : Tendsto (fun p : ℝ × ℝ => e p.1 + e p.2) (F ×ˢ G) (𝓝 (e x + e y)) :=
      (hF.comp Filter.tendsto_fst).add (hG.comp Filter.tendsto_snd)
    rw [← e_add] at h1
    exact h1.congr (fun p => (e_add p.1 p.2).symm)
  smul := by
    intro a F x hF
    unfold bohrConv at *
    rw [Filter.tendsto_map'_iff]
    have h1 : Tendsto (fun z : ℝ => a • e z) F (𝓝 (a • e x)) :=
      ((continuous_smul_const a).tendsto _).comp hF
    have hx : e (a • x) = a • e x := by rw [smul_eq_mul, smul_e]
    rw [hx]
    refine h1.congr (fun z => ?_)
    simp [Function.comp, smul_e]

theorem bohrConv_hausdorff : PHausdorff bohrConv := by
  intro F _ x y hx hy
  unfold bohrConv at hx hy
  exact e_injective' (tendsto_nhds_unique hx hy)

/-- Corollary 5.2: the Bohr convergence is not the Euclidean convergence. -/
theorem bohr_not_euclid : ¬ ∀ F x, bohrConv F x → F ≤ 𝓝 x := by
  intro h
  have h0 : bohrConv (@nhds ℝ bohrTop 0) 0 := (bohrConv_iff _ _).2 le_rfl
  have h1 := h _ _ h0
  have h2 : Metric.ball (0 : ℝ) 1 ∈ @nhds ℝ bohrTop 0 := h1 (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨t, ht, hbig⟩ := bohr_unbounded h2 1
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  linarith

/-- Corollary 5.2: scalar multiplication of the Bohr PVG is not jointly continuous. -/
theorem bohr_not_jointCont : ¬ JointCont bohrConv := by
  intro hj
  apply bohr_not_euclid
  intro F x hF
  exact ((joint_euclid bohrConv_isPVG bohrConv_hausdorff hj F x).1 hF)

#print axioms bohr_isTopologicalAddGroup
#print axioms bohr_t2
#print axioms bohr_constSMul
#print axioms bohr_coarser_euclid
#print axioms bohr_unbounded
#print axioms bohrConv_isPVG
#print axioms bohr_not_jointCont

end Q95
end PVG
