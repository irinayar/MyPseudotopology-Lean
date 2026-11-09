import LeanCheck.PVGModStrict
import LeanCheck.PVGClosed

/-!
# PVG: PVGs not of the form `ξ_{β,I}`, the structure of the topological modification (Lean check)

Scope. Further statements of Section 8 of `PVG_v19`:

* `AdmPair`, `notxiform` (Corollary `notxiform`): with the cited minimality of the Bohr topology (`BohrMinimal`, a hypothesis), the
  convergence `η_G` for an admissible `G ≠ 0` is a Hausdorff PVG, coarser than the Euclidean convergence, that is not `ξ_{β,I}` for
  any admissible pair;
* `tau_open_iff`, `tau_unbounded`, `tau_seq_iff` (Proposition `taustructure` (a), (b) and the sequence part of (c)): the open sets
  of the topological modification are those whose traces on the members of `I` are relatively `β`-open; nonempty open sets of the
  modification of the lacunary PVG are unbounded; its convergent sequences are the Euclidean convergent ones (the statement on
  compact sets uses Glicksberg's theorem, which is cited and not formalized);
* `cohTop`, `prod_le_coh`, `add_continuous_coh` (Remark `coherentproduct`): the coherent topology on `ℝ × ℝ` contains the product of
  the modification with itself, and addition is continuous from it into the modification.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Set Filter Topology Pointwise
open scoped Classical

namespace PVG
namespace Q95

/-! ### Corollary `notxiform` -/

/-- An admissible pair `(β, I)`: `β` is a Hausdorff group topology with continuous dilations, `I` satisfies (I1)–(I5). -/
structure AdmPair (β : TopologicalSpace ℝ) (I : Set (Set ℝ)) : Prop where
  grp : @IsTopologicalAddGroup ℝ β _
  t2 : @T2Space ℝ β
  smul : @ContinuousConstSMul ℝ ℝ β _
  ideal : IsIdeal I

/-- **Corollary `notxiform`** (with the cited minimality of the Bohr topology as a hypothesis). -/
theorem notxiform (hmin : BohrMinimal) (hdense : DenseRange e) :
    ∃ conv : Filter ℝ → ℝ → Prop, IsPVG conv ∧ PHausdorff conv ∧ (∀ F x, F ≤ 𝓝 x → conv F x) ∧
      ¬ ∃ (β : TopologicalSpace ℝ) (I : Set (Set ℝ)), AdmPair β I ∧ ∀ F x, conv F x ↔ @xiConv ℝ β I F x := by
  obtain ⟨G, hG, hne⟩ := exists_nonzero_admissible
  refine ⟨etaConv G, etaConv_isPVG G, etaConv_hausdorff hG, fun F x h => euclid_coarser G h, ?_⟩
  rintro ⟨β, I, hA, hiff⟩
  -- `β` is coarser than the Bohr topology
  have hnh : ∀ x, @nhds ℝ bohrTop x ≤ @nhds ℝ β x := by
    intro x
    have h1 : bohrConv (@nhds ℝ bohrTop x) x := (bohrConv_iff _ _).2 le_rfl
    exact ((hiff _ _).1 (bohr_coarser G h1)).1
  have hle : bohrTop ≤ β := by
    intro s hs
    refine isOpen_bohr_of_nhds s (fun x hx => ?_)
    exact hnh x (@IsOpen.mem_nhds ℝ β x s hs hx)
  have hβ : β = bohrTop := hmin β hA.grp hA.t2 hA.smul hle
  subst hβ
  obtain ⟨g0, hg0G, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨U, hU⟩ := exists_ultra_lr hdense g0
  have hU0 : etaConv G U 0 := (etaConv_ultra_zero G U).2 (by rw [hU]; exact hg0G)
  have hxi := ((hiff _ _).1 hU0).1
  have hb : bohrConv (U : Filter ℝ) 0 := (bohrConv_iff _ _).2 hxi
  have : Lr U = e 0 := Lr_eq_of_tendsto hb
  rw [e_zero, hU] at this
  exact hg0 this

/-! ### Proposition `taustructure` (a) -/

section Tau

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousConstSMul ℝ X] {I : Set (Set X)}

/-- (a): `U` is open in the modification iff its traces on the members of `I` are relatively open. -/
theorem tau_open_iff (hI : IsIdeal I) (U : Set X) :
    @IsOpen X (modTop (xiConv I)) U ↔ ∀ J ∈ I, ∀ x ∈ U ∩ J, ∃ W ∈ 𝓝 x, W ∩ J ⊆ U := by
  rw [mem_modTop_iff]
  constructor
  · intro hU J hJ x hx
    have hx' : x ∉ closure (J \ U) := fun hc => by
      have := hU J hJ
      rw [Set.eq_empty_iff_forall_notMem] at this
      exact this x ⟨hc, hx.1⟩
    rw [mem_closure_iff_nhds] at hx'
    push Not at hx'
    obtain ⟨W, hW, hWe⟩ := hx'
    refine ⟨W, hW, fun y hy => ?_⟩
    by_contra hyU
    have : y ∈ W ∩ (J \ U) := ⟨hy.1, hy.2, hyU⟩
    rw [hWe] at this
    exact this
  · intro H J hJ
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxc, hxU⟩
    have hJ' : insert x J ∈ I := by
      have := hI.union hJ (hI.single x)
      rwa [show J ∪ {x} = insert x J by ext; simp [or_comm]] at this
    obtain ⟨W, hW, hWU⟩ := H (insert x J) hJ' x ⟨hxU, Set.mem_insert _ _⟩
    rw [mem_closure_iff_nhds] at hxc
    obtain ⟨y, hyW, hyJ, hyU⟩ := hxc W hW
    exact hyU (hWU ⟨hyW, Set.mem_insert_of_mem _ hyJ⟩)

end Tau

end Q95

namespace Lac

open Q95

/-- (b): every nonempty open set of the topological modification of the lacunary PVG is Euclidean-unbounded. -/
theorem tau_unbounded {U : Set ℝ} (hU : @IsOpen ℝ (modTop lacConv) U) (hne : U.Nonempty) (r : ℝ) :
    ∃ u ∈ U, r < |u| := by
  by_contra hno
  push Not at hno
  obtain ⟨x, hx⟩ := hne
  set M : ℝ := 2 * |r| + 1 with hM
  set A : Set ℝ := Set.Icc (-M) M with hA
  have hAI : A ∈ IS := bounded_mem_IS (M := M) (fun a ha => abs_le.2 ha)
  obtain ⟨c, hc, hfin⟩ := exists_dilation hAI
  have hDI := Dset_mem_IS c A
  set J : Set ℝ := {x} + Dset c A with hJ
  have hJI : J ∈ IS := IS_isIdeal.add (IS_isIdeal.single x) hDI
  have hdisj : J \ U = J := by
    ext z
    constructor
    · exact fun h => h.1
    · intro hz
      refine ⟨hz, fun hzU => ?_⟩
      obtain ⟨a, ha, d, hd, rfl⟩ := hz
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨n, l, hl1, hln, hdx, hdA⟩ := hd
      have hdM : M < |d| := by
        by_contra hcon
        push Not at hcon
        exact hdA (abs_le.1 hcon)
      have h1 := hno _ hzU
      have h2 := hno _ hx
      have h3 : |d| ≤ |a + d| + |a| := by
        have := abs_sub (a + d) a; simpa using this
      linarith [abs_nonneg r, le_abs_self r]
  have hcl : x ∈ @closure ℝ bohrTop J := by
    letI : TopologicalSpace ℝ := bohrTop
    haveI := bohr_isTopologicalAddGroup
    have h0 := zero_mem_closure_D hc.1 hfin
    have := map_mem_closure (f := fun d : ℝ => x + d) (continuous_const_add x) h0
      (t := J) (fun d hd => ⟨x, rfl, d, hd, rfl⟩)
    simpa using this
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  have hmod := (mem_modTop_iff (I := IS) U).1 hU J hJI
  rw [hdisj] at hmod
  have : x ∈ closure J ∩ U := ⟨hcl, hx⟩
  rw [hmod] at this
  exact this

/-- (c), sequences: a sequence converges in the topological modification iff it converges in the Euclidean topology. -/
theorem tau_seq_iff (a : ℕ → ℝ) (x : ℝ) :
    Tendsto a atTop (@nhds ℝ (modTop lacConv) x) ↔ Tendsto a atTop (𝓝 x) := by
  constructor
  · intro h
    have hle : modTop lacConv ≤ bohrTop := fun s hs => bohr_le_lac_modTop hs
    have hb : Tendsto a atTop (@nhds ℝ bohrTop x) := h.mono_right (nhds_mono hle)
    exact (bohrseq a x).1 ((bohrConv_iff _ _).2 hb)
  · intro h
    have hE : (inferInstance : TopologicalSpace ℝ) ≤ modTop lacConv := fun s hs => lac_modTop_le_euclid hs
    exact h.mono_right (nhds_mono hE)

end Lac

/-! ### Remark `coherentproduct` -/

namespace Q95

/-- The coherent topology on `ℝ × ℝ`: `G` is open iff its traces on `J × J'` (`J, J' ∈ I`) are relatively open for the product of the
Bohr topologies. -/
def cohTop (I : Set (Set ℝ)) : TopologicalSpace (ℝ × ℝ) where
  IsOpen G := ∀ J ∈ I, ∀ J' ∈ I, ∀ p ∈ G, p.1 ∈ J → p.2 ∈ J' →
    ∃ W ∈ @nhds ℝ bohrTop p.1, ∃ W' ∈ @nhds ℝ bohrTop p.2, ∀ q ∈ W ×ˢ W', q.1 ∈ J → q.2 ∈ J' → q ∈ G
  isOpen_univ := fun J _ J' _ p _ _ _ => ⟨univ, Filter.univ_mem, univ, Filter.univ_mem, fun q _ _ _ => mem_univ q⟩
  isOpen_inter := by
    intro G₁ G₂ h₁ h₂ J hJ J' hJ' p hp hpJ hpJ'
    obtain ⟨W₁, hW₁, W₁', hW₁', hs₁⟩ := h₁ J hJ J' hJ' p hp.1 hpJ hpJ'
    obtain ⟨W₂, hW₂, W₂', hW₂', hs₂⟩ := h₂ J hJ J' hJ' p hp.2 hpJ hpJ'
    refine ⟨W₁ ∩ W₂, Filter.inter_mem hW₁ hW₂, W₁' ∩ W₂', Filter.inter_mem hW₁' hW₂', fun q hq hqJ hqJ' => ⟨?_, ?_⟩⟩
    · exact hs₁ q ⟨hq.1.1, hq.2.1⟩ hqJ hqJ'
    · exact hs₂ q ⟨hq.1.2, hq.2.2⟩ hqJ hqJ'
  isOpen_sUnion := by
    intro S hS J hJ J' hJ' p ⟨G, hGS, hpG⟩ hpJ hpJ'
    obtain ⟨W, hW, W', hW', hs⟩ := hS G hGS J hJ J' hJ' p hpG hpJ hpJ'
    exact ⟨W, hW, W', hW', fun q hq hqJ hqJ' => ⟨G, hGS, hs q hq hqJ hqJ'⟩⟩

end Q95

namespace Lac

open Q95

/-- `τ_ξ × τ_ξ` is contained in the coherent topology. -/
theorem prod_le_coh {G : Set (ℝ × ℝ)}
    (hG : @IsOpen (ℝ × ℝ) (@instTopologicalSpaceProd ℝ ℝ (modTop lacConv) (modTop lacConv)) G) :
    @IsOpen (ℝ × ℝ) (cohTop IS) G := by
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  intro J hJ J' hJ' p hp hpJ hpJ'
  obtain ⟨u, v, hu, hv, hpu, hpv, huv⟩ :=
    (@isOpen_prod_iff ℝ ℝ (modTop lacConv) (modTop lacConv) G).1 hG p.1 p.2 hp
  obtain ⟨W, hW, hWs⟩ := (tau_open_iff (I := IS) IS_isIdeal u).1 hu J hJ p.1 ⟨hpu, hpJ⟩
  obtain ⟨W', hW', hWs'⟩ := (tau_open_iff (I := IS) IS_isIdeal v).1 hv J' hJ' p.2 ⟨hpv, hpJ'⟩
  refine ⟨W, hW, W', hW', fun q hq hqJ hqJ' => huv ⟨hWs ⟨hq.1, hqJ⟩, hWs' ⟨hq.2, hqJ'⟩⟩⟩

/-- Addition is continuous from the coherent topology into the topological modification. -/
theorem add_continuous_coh {U : Set ℝ} (hU : @IsOpen ℝ (modTop lacConv) U) :
    @IsOpen (ℝ × ℝ) (cohTop IS) ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' U) := by
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  intro J hJ J' hJ' p hp hpJ hpJ'
  have hJJ : J + J' ∈ IS := IS_isIdeal.add hJ hJ'
  obtain ⟨W, hW, hWs⟩ := (tau_open_iff (I := IS) IS_isIdeal U).1 hU (J + J') hJJ (p.1 + p.2) ⟨hp, Set.add_mem_add hpJ hpJ'⟩
  have hcont : Tendsto (fun q : ℝ × ℝ => q.1 + q.2) (𝓝 p) (𝓝 (p.1 + p.2)) := continuous_add.tendsto p
  have hW' : (fun q : ℝ × ℝ => q.1 + q.2) ⁻¹' W ∈ 𝓝 p := hcont hW
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hW'
  obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ := hW'
  refine ⟨W₁, hW₁, W₂, hW₂, fun q hq hqJ hqJ' => ?_⟩
  exact hWs ⟨hsub hq, Set.add_mem_add hqJ hqJ'⟩

#print axioms notxiform
#print axioms tau_open_iff
#print axioms tau_unbounded
#print axioms tau_seq_iff
#print axioms prod_le_coh
#print axioms add_continuous_coh

end Lac
end PVG
