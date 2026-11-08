import LeanCheck.PVGLacMain
import LeanCheck.PVGNonzero

/-!
# PVG: pretopologies below the Bohr topology (Lean check)

Scope. Corollary 8.24 (`closedPVG`) of `PVG_v19`: `η_G` is pretopological exactly when `G` is closed in `K`, and the Bohr topology is
the only pretopological member of the family. The article uses the cited minimality of the Bohr topology among Hausdorff TVG
topologies on `ℝ` [Y1981]; that result is not formalized and appears here as the explicit hypothesis `BohrMinimal`.

* `BohrMinimal`: every Hausdorff group topology on `ℝ` with continuous dilations that is coarser than `bohrTop` equals `bohrTop`
  (the cited statement, a hypothesis);
* `etaConv_pretop_closed` (unconditional, with `DenseRange e`): if `η_G` is pretopological, `G = ⋂_{A ∈ V(0)} cl_K e(A)` is closed;
* `quotTop`, `etaConv_iff_quot`, `etaConv_topological_of_closed` (unconditional): if `G` is closed, `η_G` is the convergence of
  the topology on `ℝ` induced by `x ↦ e(x) + G ∈ K/G`;
* `quotTop_*`: the topology `quotTop G` is a group topology with continuous dilations coarser than `bohrTop`, Hausdorff for admissible `G`;
* `closed_eq_bot` (with `BohrMinimal` and `DenseRange e`): a closed admissible `G` is `0`;
* `closedPVG`, `closedPVG_bot`: `η_G` is pretopological iff `G` is closed iff `G = 0`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology Pointwise

namespace PVG
namespace Q95

/-- **Hypothesis (the cited result [Y1981], not formalized)**: minimality of the Bohr topology among Hausdorff group topologies
on `ℝ` with continuous dilations. -/
def BohrMinimal : Prop :=
  ∀ β : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ β _ → @T2Space ℝ β → @ContinuousConstSMul ℝ ℝ β _ →
    bohrTop ≤ β → β = bohrTop

/-! ### Pretopological implies closed -/

theorem etaConv_pretop_closed (hdense : DenseRange e) (G : Submodule ℝ K) (hp : IsPretop (etaConv G)) :
    IsClosed (G : Set K) := by
  set V : Filter ℝ := Vfil (etaConv G) 0 with hV
  have hV0 : etaConv G V 0 := hp 0
  have hset : (G : Set K) = ⋂ A ∈ {A : Set ℝ | A ∈ V}, closure (e '' A) := by
    ext κ
    simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro hκ A hA
      obtain ⟨U, rfl⟩ := exists_ultra_lr hdense κ
      have hU0 : etaConv G U 0 := (etaConv_ultra_zero G U).2 hκ
      have hUV : (U : Filter ℝ) ≤ V := le_sSup hU0
      have hAU : A ∈ (U : Filter ℝ) := hUV hA
      exact mem_closure_of_tendsto (tendsto_Lr U) (Filter.mem_map.2 (Filter.mem_of_superset hAU (fun a ha => ⟨a, ha, rfl⟩)))
    · intro hκ
      have hne : (V ⊓ Filter.comap e (𝓝 κ)).NeBot := by
        rw [Filter.inf_neBot_iff]
        intro A hA N' hN'
        obtain ⟨N, hN, hNN'⟩ := Filter.mem_comap.1 hN'
        obtain ⟨_, hy1, ⟨a, ha, rfl⟩⟩ := mem_closure_iff_nhds.1 (hκ A hA) N hN
        exact ⟨a, ha, hNN' hy1⟩
      set U : Ultrafilter ℝ := Ultrafilter.of (V ⊓ Filter.comap e (𝓝 κ)) with hU
      have hUV : (U : Filter ℝ) ≤ V := (Ultrafilter.of_le _).trans inf_le_left
      have hUc : (U : Filter ℝ) ≤ Filter.comap e (𝓝 κ) := (Ultrafilter.of_le _).trans inf_le_right
      have hLr : Lr U = κ := Lr_eq_of_tendsto (Filter.tendsto_iff_comap.2 hUc)
      have := (etaConv_ultra_zero G U).1 ((etaConv_pseudo G).p2 hV0 hUV)
      rwa [hLr] at this
  rw [hset]
  exact isClosed_biInter (fun A _ => isClosed_closure)

/-! ### Closed implies topological: the quotient topology -/

section Quot

variable (G : Submodule ℝ K)

/-- `x ↦ e(x) + G ∈ K/G` as an additive homomorphism. -/
def epsHom : ℝ →+ (K ⧸ G) := (G.mkQ : K →ₗ[ℝ] K ⧸ G).toAddMonoidHom.comp eHom

lemma epsHom_apply (x : ℝ) : epsHom G x = G.mkQ (e x) := rfl

/-- The topology on `ℝ` induced by `x ↦ e(x) + G`. -/
def quotTop : TopologicalSpace ℝ := TopologicalSpace.induced (epsHom G) inferInstance

lemma nhds_quot (x : ℝ) : @nhds ℝ (quotTop G) x = Filter.comap (epsHom G) (𝓝 (epsHom G x)) := by
  unfold quotTop; rw [nhds_induced]

lemma quotTop_isTopologicalAddGroup : @IsTopologicalAddGroup ℝ (quotTop G) _ := by
  unfold quotTop; exact topologicalAddGroup_induced (epsHom G)

lemma continuous_const_smul_quot (a : ℝ) : Continuous (fun q : K ⧸ G => a • q) := by
  rw [(Submodule.isQuotientMap_mkQ G).continuous_iff]
  have : ((fun q : K ⧸ G => a • q) ∘ G.mkQ) = fun κ => G.mkQ (a • κ) := by
    funext κ; simp [Function.comp]
  rw [this]
  exact (Submodule.continuous_mkQ G).comp (continuous_smul_const a)

lemma quotTop_constSMul : @ContinuousConstSMul ℝ ℝ (quotTop G) _ := by
  letI : TopologicalSpace ℝ := quotTop G
  refine ⟨fun a => ?_⟩
  have hind : Topology.IsInducing (epsHom G) := ⟨rfl⟩
  rw [hind.continuous_iff]
  have : (epsHom G ∘ fun x : ℝ => a • x) = fun x => a • epsHom G x := by
    funext x
    show G.mkQ (e (a • x)) = a • G.mkQ (e x)
    rw [smul_eq_mul, ← smul_e, LinearMap.map_smul]
  rw [this]
  exact (continuous_const_smul_quot G a).comp hind.continuous

lemma continuous_eps_bohr : @Continuous ℝ (K ⧸ G) bohrTop _ (epsHom G) := by
  letI : TopologicalSpace ℝ := bohrTop
  have hind : Topology.IsInducing e := ⟨rfl⟩
  exact (Submodule.continuous_mkQ G).comp hind.continuous

lemma bohrTop_le_quotTop : bohrTop ≤ quotTop G := by
  have hc : @Continuous ℝ ℝ bohrTop (quotTop G) id := by
    unfold quotTop
    exact continuous_induced_rng.2 (continuous_eps_bohr G)
  have h2 : bohrTop ≤ TopologicalSpace.induced (id : ℝ → ℝ) (quotTop G) := (@continuous_iff_le_induced ℝ ℝ id bohrTop (quotTop G)).1 hc
  exact h2.trans (@induced_id ℝ (quotTop G)).le

/-- For admissible `G` the topology `quotTop G` is Hausdorff (when `G` is closed). -/
lemma quotTop_t2 (hcl : IsClosed (G : Set K)) (hG : IsAdmissible G) : @T2Space ℝ (quotTop G) := by
  haveI : IsClosed (G : Set K) := hcl
  letI : TopologicalSpace ℝ := quotTop G
  have hinj : Function.Injective (epsHom G) := by
    intro x y hxy
    have h1 : G.mkQ (e x) = G.mkQ (e y) := hxy
    have h2 : e x - e y ∈ G := (Submodule.Quotient.eq G).1 h1
    have h3 : e (x - y) ∈ G := by rw [e_sub]; exact h2
    have h4 : e (x - y) = 0 := by
      refine Submodule.disjoint_def.1 hG _ h3 ?_
      exact Submodule.mem_span_singleton.2 ⟨x - y, by rw [e_eq_smul (x - y)]⟩
    have h5 : x - y = 0 := e_injective' (h4.trans e_zero.symm)
    linarith
  have hind : Topology.IsInducing (epsHom G) := ⟨rfl⟩
  exact (Topology.IsEmbedding.mk hind hinj).t2Space

/-- `η_G` is the convergence of the topology `quotTop G` when `G` is closed. -/
theorem etaConv_iff_quot (hcl : IsClosed (G : Set K)) (F : Filter ℝ) (x : ℝ) :
    etaConv G F x ↔ F ≤ @nhds ℝ (quotTop G) x := by
  haveI : IsClosed (G : Set K) := hcl
  rw [nhds_quot, ← Filter.tendsto_iff_comap]
  have hLr : ∀ U : Ultrafilter ℝ, Tendsto (epsHom G) U (𝓝 (G.mkQ (Lr U))) := fun U =>
    ((Submodule.continuous_mkQ G).tendsto _).comp (tendsto_Lr U)
  constructor
  · intro h
    rw [Filter.tendsto_iff_ultrafilter]
    intro U hU
    have h1 : Lr U - e x ∈ G := h U hU
    have h2 : G.mkQ (Lr U) = G.mkQ (e x) := (Submodule.Quotient.eq G).2 h1
    have := hLr U
    rwa [h2] at this
  · intro h U hU
    have h1 := ((Filter.tendsto_iff_ultrafilter _ _ _).1 h) U hU
    have h2 : G.mkQ (Lr U) = epsHom G x := tendsto_nhds_unique (hLr U) h1
    exact (Submodule.Quotient.eq G).1 h2

/-- **Corollary 8.24, converse part** (unconditional): if `G` is closed, `η_G` is topological. -/
theorem etaConv_topological_of_closed (hcl : IsClosed (G : Set K)) : IsTopological (etaConv G) :=
  ⟨quotTop G, fun F x => etaConv_iff_quot G hcl F x⟩

end Quot

/-! ### The Bohr topology as `η₀` -/

theorem etaConv_bot_iff (F : Filter ℝ) (x : ℝ) : etaConv ⊥ F x ↔ bohrConv F x := by
  unfold bohrConv
  constructor
  · intro h
    rw [Filter.tendsto_iff_ultrafilter]
    intro U hU
    have h1 : Lr U - e x ∈ (⊥ : Submodule ℝ K) := h U hU
    have h2 : Lr U = e x := sub_eq_zero.1 ((Submodule.mem_bot ℝ).1 h1)
    have := tendsto_Lr U
    rwa [h2] at this
  · intro h U hU
    have : Lr U = e x := Lr_eq_of_tendsto (h.mono_left hU)
    rw [this, sub_self]
    exact Submodule.zero_mem _

/-- Under the minimality of the Bohr topology, a closed admissible `G` is zero. -/
theorem closed_eq_bot (hmin : BohrMinimal) (hdense : DenseRange e) (G : Submodule ℝ K)
    (hG : IsAdmissible G) (hcl : IsClosed (G : Set K)) : G = ⊥ := by
  have hβ : quotTop G = bohrTop :=
    hmin (quotTop G) (quotTop_isTopologicalAddGroup G) (quotTop_t2 G hcl hG) (quotTop_constSMul G)
      (bohrTop_le_quotTop G)
  refine etaConv_inj hdense G ⊥ (fun F x => ?_)
  rw [etaConv_iff_quot G hcl, hβ, etaConv_bot_iff, bohrConv_iff]

/-- **Corollary 8.24.** For admissible `G`, `η_G` is pretopological iff `G` is closed iff `G = 0` (the Bohr topology), assuming the
cited minimality of the Bohr topology. -/
theorem closedPVG (hmin : BohrMinimal) (hdense : DenseRange e) (G : Submodule ℝ K) (hG : IsAdmissible G) :
    IsPretop (etaConv G) ↔ IsClosed (G : Set K) := by
  constructor
  · exact etaConv_pretop_closed hdense G
  · intro hcl
    exact topological_isPretop (etaConv_topological_of_closed G hcl)

theorem closedPVG_bot (hmin : BohrMinimal) (hdense : DenseRange e) (G : Submodule ℝ K) (hG : IsAdmissible G) :
    IsPretop (etaConv G) ↔ G = ⊥ := by
  rw [closedPVG hmin hdense G hG]
  constructor
  · exact closed_eq_bot hmin hdense G hG
  · rintro rfl
    simp only [Submodule.bot_coe]
    exact isClosed_singleton

#print axioms etaConv_pretop_closed
#print axioms etaConv_topological_of_closed
#print axioms closed_eq_bot
#print axioms closedPVG
#print axioms closedPVG_bot

/-! ### Corollary 8.29 and Corollary 8.27(c): the non-pretopological parts -/

/-- **Corollary 8.29** (not pretopological, hence not topological): `η_G` for admissible `G ≠ 0`, assuming the cited minimality. -/
theorem nonzeroG_not_pretop (hmin : BohrMinimal) (hdense : DenseRange e) (G : Submodule ℝ K)
    (hG : IsAdmissible G) (hne : G ≠ ⊥) : ¬ IsPretop (etaConv G) :=
  fun h => hne ((closedPVG_bot hmin hdense G hG).1 h)

theorem nonzeroG_not_topological (hmin : BohrMinimal) (hdense : DenseRange e) (G : Submodule ℝ K)
    (hG : IsAdmissible G) (hne : G ≠ ⊥) : ¬ IsTopological (etaConv G) :=
  fun h => nonzeroG_not_pretop hmin hdense G hG hne (topological_isPretop h)

/-- A complement of `e(ℝ)` in `K` is nonzero (`|K| = 2^𝔠 > 𝔠 = |e(ℝ)|`). -/
theorem complement_ne_bot (H : Submodule ℝ K) (hH : IsCompl (ℝ ∙ e 1) H) : H ≠ ⊥ := by
  rintro rfl
  have htop : (ℝ ∙ e 1) = ⊤ := by
    have := hH.sup_eq_top
    simpa using this
  have hsurj : Function.Surjective (fun a : ℝ => a • e 1) := by
    intro κ
    have : κ ∈ (ℝ ∙ e 1) := by rw [htop]; exact Submodule.mem_top
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    exact ⟨a, ha⟩
  have h1 : Cardinal.mk K ≤ Cardinal.mk ℝ := Cardinal.mk_le_of_surjective hsurj
  rw [card_K] at h1
  exact absurd (Cardinal.cantor (Cardinal.mk ℝ)) (not_lt.2 h1)

/-- **Corollary 8.27(c)** (last assertion): no minimal Hausdorff PVG below the Bohr topology is pretopological, hence none is a
topology (assuming the cited minimality). -/
theorem minimal_not_pretop (hmin : BohrMinimal) (hdense : DenseRange e) (H : Submodule ℝ K)
    (hH : IsCompl (ℝ ∙ e 1) H) : ¬ IsPretop (etaConv H) :=
  nonzeroG_not_pretop hmin hdense H hH.symm.disjoint (complement_ne_bot H hH)

theorem minimal_not_topological (hmin : BohrMinimal) (hdense : DenseRange e) (H : Submodule ℝ K)
    (hH : IsCompl (ℝ ∙ e 1) H) : ¬ IsTopological (etaConv H) :=
  fun h => minimal_not_pretop hmin hdense H hH (topological_isPretop h)

#print axioms nonzeroG_not_pretop
#print axioms complement_ne_bot
#print axioms minimal_not_pretop

end Q95
end PVG
