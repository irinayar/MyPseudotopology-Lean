import LeanCheck.PVGLacDilation

/-!
# PVG: a lacunary PVG that is not pretopological (Lean check)

Scope. Theorem 7.4 (`thm:main`) and Remark 7.6 of `PVG_v19`. `lacConv = xiConv_{τ_B, I_S}`: `F → x` iff `F` is finer than the Bohr
neighbourhood filter of `x` and has a member in `I_S`.

* `exists_pair`: for any real sequence `u` and neighbourhood `V` of `0` in `K`, and any `N`, there are `N ≤ l < n` with
  `e(u n) - e(u l) ∈ V` (a cluster point of `e ∘ u` in the compact group `K`);
* `exists_D`: for `A ∈ I_S` and `c ∈ [1,2]` with `c t ∈ A` for only finitely many `t ∈ T`, the set
  `D = {c (s_n - s_l)} \ A` lies in `I_S`, is disjoint from `A`, has `|x| ≥ 1` on its members and `0 ∈ closure_{τ_B} D`;
* `lacConv_isPVG`, `lacConv_hausdorff`, `lac_coarser_euclid`, `lac_finer_bohr`, `lac_not_pretop`, `lac_not_topological`,
  `lac_not_euclid` (Theorem 7.4): `lacConv` is a Hausdorff PVG on `ℝ`, coarser than the Euclidean convergence, finer than the
  Bohr one, not pretopological (hence not topological) and not the Euclidean convergence;
* `lac_modTop_le_euclid`, `bohr_le_lac_modTop`, `lac_ball_not_open` (Remark 7.6): `τ_B ⊆ τ_ξ ⊆ τ_E` and `(-1,1)` is not `τ_ξ`-open.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Set Pointwise Filter Topology
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-- A cluster-point argument in the compact group `K`. -/
theorem exists_pair (u : ℕ → ℝ) {V : Set K} (hV : V ∈ 𝓝 (0 : K)) (N : ℕ) :
    ∃ l n : ℕ, N ≤ l ∧ l < n ∧ e (u n) - e (u l) ∈ V := by
  obtain ⟨κ, hκ⟩ := exists_clusterPt_of_compactSpace (Filter.map (fun j => e (u j)) atTop)
  have hsub : ∃ V1 ∈ 𝓝 κ, ∀ a ∈ V1, ∀ c ∈ V1, a - c ∈ V := by
    have h1 : Tendsto (fun p : K × K => p.1 - p.2) (𝓝 (κ, κ)) (𝓝 (κ - κ)) :=
      (continuous_sub.tendsto (κ, κ))
    rw [sub_self] at h1
    have h2 := h1 hV
    rw [nhds_prod_eq, Filter.mem_map, mem_prod_self_iff] at h2
    obtain ⟨V1, hV1, hV1sub⟩ := h2
    exact ⟨V1, hV1, fun a ha c hc => hV1sub (Set.mk_mem_prod ha hc)⟩
  obtain ⟨V1, hV1, hV1V⟩ := hsub
  have hfreq : ∃ᶠ j in atTop, e (u j) ∈ V1 := (mapClusterPt_iff_frequently.1 hκ) V1 hV1
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨l, hl, hlV⟩ := hfreq N
  obtain ⟨n, hn, hnV⟩ := hfreq (l + 1)
  exact ⟨l, n, hl, hn, hV1V _ hnV _ hlV⟩

/-- The set `D` of the proof of Theorem 7.4. -/
def Dset (c : ℝ) (A : Set ℝ) : Set ℝ :=
  {x | ∃ n l : ℕ, 1 ≤ l ∧ l < n ∧ x = c * (sS n - sS l) ∧ x ∉ A}

lemma Dset_mem_IS (c : ℝ) (A : Set ℝ) : Dset c A ∈ IS := by
  rw [mem_IS_iff]
  refine ⟨0, [c, -c], fun z hz => ?_⟩
  obtain ⟨n, l, hl1, hln, rfl, -⟩ := hz
  refine ⟨0, c * (sS n - sS l), by simp, ?_, by ring⟩
  refine mem_sumSet_cons.2 ⟨sS n, Or.inr ⟨n, by omega, Or.inl rfl⟩, -c * sS l + 0, ?_, by ring⟩
  refine mem_sumSet_cons.2 ⟨sS l, Or.inr ⟨l, hl1, Or.inl rfl⟩, 0, rfl, by ring⟩

lemma Dset_disjoint (c : ℝ) (A : Set ℝ) : Disjoint (Dset c A) A := by
  rw [Set.disjoint_left]
  rintro x ⟨_, _, _, _, _, hx⟩
  exact hx

lemma Dset_abs_ge {c : ℝ} (hc : 1 ≤ c) {A : Set ℝ} {x : ℝ} (hx : x ∈ Dset c A) : 1 ≤ |x| := by
  obtain ⟨n, l, hl1, hln, rfl, -⟩ := hx
  have h1 := two_sS_le hln
  have h2 : 16 ≤ sS n := by
    have : sS 2 ≤ sS n := sS_mono (by omega)
    have h16 : sS 2 = 16 := by unfold sS; norm_num
    linarith
  have hl := sS_pos l
  have h3 : 8 ≤ sS n - sS l := by linarith
  rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ c), abs_of_nonneg (by linarith)]
  nlinarith

/-- `0 ∈ closure_{τ_B} D`. -/
theorem zero_mem_closure_D {A : Set ℝ} {c : ℝ} (hc : 1 ≤ c)
    (hfin : {t | t ∈ Tset ∧ c * t ∈ A}.Finite) : (0 : ℝ) ∈ @closure ℝ bohrTop (Dset c A) := by
  letI : TopologicalSpace ℝ := bohrTop
  rw [mem_closure_iff_nhds]
  intro W hW
  have hW' := hW
  rw [nhds_bohr, e_zero] at hW'
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.1 hW'
  -- a bound for the finitely many exceptional `t`
  obtain ⟨Mb, hMb⟩ := (hfin.image (fun t : ℝ => |t|)).bddAbove
  obtain ⟨L, hL⟩ := sS_unbounded (2 * Mb)
  obtain ⟨l, n, hlN, hln, hVln⟩ := exists_pair (fun n => c * sS n) hV (max L 1)
  have hL1 : 1 ≤ l := le_trans (le_max_right _ _) hlN
  have hLl : L ≤ l := le_trans (le_max_left _ _) hlN
  set x : ℝ := c * (sS n - sS l) with hx
  have hxW : x ∈ W := by
    apply hVW
    show e x ∈ V
    have : x = c * sS n - c * sS l := by rw [hx]; ring
    rw [this, e_sub]
    exact hVln
  have hxA : x ∉ A := by
    intro hxA
    have hT : (sS n - sS l) ∈ Tset := ⟨n, l, hL1, hln, true, false, by simp [tval, sgn]; ring⟩
    have hmem : (sS n - sS l) ∈ {t | t ∈ Tset ∧ c * t ∈ A} := ⟨hT, hxA⟩
    have hle : |sS n - sS l| ≤ Mb := hMb ⟨_, hmem, rfl⟩
    have hb := (tval_bounds hln true false).1
    have e1 : tval n l true false = sS n - sS l := by simp [tval, sgn]; ring
    rw [e1] at hb
    have hmono : sS L ≤ sS n := sS_mono (by omega)
    linarith
  exact ⟨x, hxW, n, l, hL1, hln, rfl, hxA⟩

/-! ### The PVG `lacConv` -/

/-- `F → x` iff `F` contains the Bohr neighbourhood filter of `x` and has a member in `I_S`. -/
abbrev lacConv : Filter ℝ → ℝ → Prop := @xiConv ℝ bohrTop IS

theorem lacConv_isPVG : IsPVG lacConv := by
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  exact xi_isPVG IS_isIdeal

theorem lacConv_hausdorff : PHausdorff lacConv := by
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_t2
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  exact xi_hausdorff

/-- Every filter converging in the Euclidean sense converges for `lacConv`. -/
theorem lac_coarser_euclid {F : Filter ℝ} {x : ℝ} (h : F ≤ 𝓝 x) : lacConv F x := by
  refine ⟨h.trans (bohr_coarser_euclid x), Metric.ball x 1, h (Metric.ball_mem_nhds x one_pos), ?_⟩
  refine bounded_mem_IS (M := |x| + 1) (fun a ha => ?_)
  rw [Metric.mem_ball, Real.dist_eq] at ha
  have h1 : |a| ≤ |a - x| + |x| := by
    have := abs_add_le (a - x) x
    simpa using this
  linarith

/-- Every filter converging for `lacConv` converges in the Bohr topology. -/
theorem lac_finer_bohr {F : Filter ℝ} {x : ℝ} (h : lacConv F x) : bohrConv F x :=
  (bohrConv_iff F x).2 h.1

/-- `0` is in the Bohr closure of a set `D` for `c = 1`, `A = ∅`. -/
theorem zero_mem_closure_D1 : (0 : ℝ) ∈ @closure ℝ bohrTop (Dset 1 ∅) :=
  zero_mem_closure_D le_rfl (by
    refine Set.Finite.subset (Set.finite_empty) ?_
    rintro t ⟨_, ht⟩
    exact absurd ht (Set.notMem_empty _))

/-- **Theorem 7.4**: `lacConv` is not pretopological. -/
theorem lac_not_pretop : ¬ IsPretop lacConv := by
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  refine xi_not_pretop IS_isIdeal (fun A hA => ?_)
  obtain ⟨c, hc, hfin⟩ := exists_dilation hA
  exact ⟨Dset c A, Dset_mem_IS c A, Dset_disjoint c A, zero_mem_closure_D hc.1 hfin⟩

theorem lac_not_topological : ¬ IsTopological lacConv := fun h => lac_not_pretop (topological_isPretop h)

/-- **Theorem 7.4**: `lacConv` is not the Euclidean convergence. -/
theorem lac_not_euclid : ∃ (F : Filter ℝ), lacConv F 0 ∧ ¬ F ≤ 𝓝 0 := by
  letI : TopologicalSpace ℝ := bohrTop
  have hcl := zero_mem_closure_D1
  haveI hne : (𝓝 (0 : ℝ) ⊓ 𝓟 (Dset 1 ∅)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  refine ⟨𝓝 (0 : ℝ) ⊓ 𝓟 (Dset 1 ∅), ⟨inf_le_left, Dset 1 ∅, Filter.mem_inf_of_right (Filter.mem_principal_self _),
    Dset_mem_IS 1 ∅⟩, ?_⟩
  intro hle
  have hball : Metric.ball (0 : ℝ) 1 ∈ (𝓝 (0 : ℝ) ⊓ 𝓟 (Dset 1 ∅)) := hle (Metric.ball_mem_nhds 0 one_pos)
  rw [Filter.mem_inf_principal] at hball
  rw [mem_closure_iff_nhds] at hcl
  obtain ⟨x, hx1, hx2⟩ := hcl _ hball
  have h1 := Dset_abs_ge le_rfl hx2
  have h2 := hx1 hx2
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at h2
  linarith

/-! ### Remark 7.6: the topological modification -/

theorem lac_modTop_le_euclid {U : Set ℝ} (hU : @IsOpen ℝ (modTop lacConv) U) : IsOpen U := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact hU x hx _ (lac_coarser_euclid le_rfl)

theorem bohr_le_lac_modTop {U : Set ℝ} (hU : @IsOpen ℝ bohrTop U) : @IsOpen ℝ (modTop lacConv) U := by
  intro x hx F hF
  have h1 : U ∈ @nhds ℝ bohrTop x := @IsOpen.mem_nhds ℝ bohrTop x U hU hx
  exact hF.1 h1

/-- `(-1,1)` is not open in the topological modification. -/
theorem lac_ball_not_open : ¬ @IsOpen ℝ (modTop lacConv) (Metric.ball (0 : ℝ) 1) := by
  intro hU
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  have h := (mem_modTop_iff (I := IS) (Metric.ball (0 : ℝ) 1)).1 hU (Dset 1 ∅) (Dset_mem_IS 1 ∅)
  have hcl := zero_mem_closure_D1
  have hdiff : Dset 1 ∅ \ Metric.ball (0 : ℝ) 1 = Dset 1 ∅ := by
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      have := Dset_abs_ge le_rfl hx
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      linarith
  rw [hdiff] at h
  have : (0 : ℝ) ∈ closure (Dset 1 ∅) ∩ Metric.ball (0 : ℝ) 1 := ⟨hcl, Metric.mem_ball_self one_pos⟩
  rw [h] at this
  exact this

#print axioms lacConv_isPVG
#print axioms lac_coarser_euclid
#print axioms lac_not_pretop
#print axioms lac_not_topological
#print axioms lac_not_euclid
#print axioms lac_ball_not_open

end Lac
end PVG
