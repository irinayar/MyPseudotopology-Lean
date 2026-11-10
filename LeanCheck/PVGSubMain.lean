import Mathlib
import LeanCheck.PVGSubGap
import LeanCheck.PVGSeqFU

/-!
# PVG: a Boolean algebra of lacunary PVGs (Lean check)

Scope. Addendum N2 of the research note, Theorem 8.61 of PVG_v27 (planned). For `A ⊆ ℕ` let `subConv A = ξ_{τ_B, I_A}` (`F → x` iff `F` is
finer than the Bohr neighbourhood filter of `x` and has a member in `I_A`, `PVGSubIdeal.IA`).

* `subConv_isPVG`, `subConv_hausdorff`, `subConv_coarser_euclid`, `subConv_finer_bohr`: `subConv A` is a Hausdorff PVG between the Bohr
  topology and the Euclidean convergence;
* `conv_sub_iff`: every `subConv A`-convergent filter is `subConv B`-convergent if and only if `A \ B` is finite;
* `subConv_eq_euclid_of_finite`: `subConv A` is the Euclidean convergence when `A` is finite;
* `subConv_not_pretop`, `subConv_not_topological`, `subConv_not_FU`: for infinite `A` the PVG is not pretopological (hence not topological)
  and not Fréchet–Urysohn.

Not formalized: the identity `I_A ∩ I_B = I_{A ∩ B}` and the statements on the topological modifications (hand proofs in Addendum N2).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter Topology
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-- `ξ_{τ_B, I_A}`. -/
abbrev subConv (A : Set ℕ) : Filter ℝ → ℝ → Prop := @xiConv ℝ bohrTop (IA A)

theorem subConv_isPVG (A : Set ℕ) : IsPVG (subConv A) := by
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  exact xi_isPVG (IA_isIdeal A)

theorem subConv_hausdorff (A : Set ℕ) : PHausdorff (subConv A) := by
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_t2
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  exact xi_hausdorff

theorem subConv_coarser_euclid (A : Set ℕ) {F : Filter ℝ} {x : ℝ} (h : F ≤ 𝓝 x) : subConv A F x := by
  refine ⟨h.trans (bohr_coarser_euclid x), Metric.ball x 1, h (Metric.ball_mem_nhds x one_pos), ?_⟩
  refine bounded_mem_IA A (M := |x| + 1) (fun a ha => ?_)
  rw [Metric.mem_ball, Real.dist_eq] at ha
  have h1 : |a| ≤ |a - x| + |x| := by
    have := abs_add_le (a - x) x
    simpa using this
  linarith

theorem subConv_finer_bohr (A : Set ℕ) {F : Filter ℝ} {x : ℝ} (h : subConv A F x) : bohrConv F x :=
  (bohrConv_iff F x).2 h.1

/-! ### The sets `D` -/

/-- `D = {c (s_n - s_l) : n, l ∈ A, 1 ≤ l < n} \ J`. -/
def DsetA (A : Set ℕ) (c : ℝ) (J : Set ℝ) : Set ℝ :=
  {x | ∃ n l : ℕ, n ∈ A ∧ l ∈ A ∧ 1 ≤ l ∧ l < n ∧ x = c * (sS n - sS l) ∧ x ∉ J}

lemma DsetA_mem_IA (A : Set ℕ) (c : ℝ) (J : Set ℝ) : DsetA A c J ∈ IA A := by
  rw [mem_IA_iff]
  refine ⟨0, [c, -c], fun z hz => ?_⟩
  obtain ⟨n, l, hn, hl, hl1, hln, rfl, -⟩ := hz
  refine ⟨0, c * (sS n - sS l), by simp, ?_, by ring⟩
  refine mem_sumSetA_cons.2 ⟨sS n, Or.inr ⟨n, hn, by omega, Or.inl rfl⟩, -c * sS l + 0, ?_, by ring⟩
  refine mem_sumSetA_cons.2 ⟨sS l, Or.inr ⟨l, hl, hl1, Or.inl rfl⟩, 0, rfl, by ring⟩

lemma DsetA_disjoint (A : Set ℕ) (c : ℝ) (J : Set ℝ) : Disjoint (DsetA A c J) J := by
  rw [Set.disjoint_left]
  rintro x ⟨_, _, _, _, _, _, _, hx⟩
  exact hx

lemma DsetA_pos {A : Set ℕ} {c : ℝ} (hc : 1 ≤ c) {J : Set ℝ} {x : ℝ} (hx : x ∈ DsetA A c J) : 0 < x := by
  obtain ⟨n, l, -, -, hl1, hln, rfl, -⟩ := hx
  have h1 := two_sS_le hln
  have h2 := sS_pos l
  have : 0 < sS n - sS l := by linarith
  nlinarith

/-- `0 ∈ closure_{τ_B} D` for infinite `A`. -/
theorem zero_mem_closure_DA {A : Set ℕ} (hA : A.Infinite) {c : ℝ} (hc : 1 ≤ c) {J : Set ℝ}
    (hfin : {t | t ∈ Tset ∧ c * t ∈ J}.Finite) : (0 : ℝ) ∈ @closure ℝ bohrTop (DsetA A c J) := by
  letI : TopologicalSpace ℝ := bohrTop
  have hA' : (setOf fun n => n ∈ A).Infinite := hA
  set g : ℕ → ℕ := Nat.nth (fun n => n ∈ A) with hg
  have hgm : StrictMono g := Nat.nth_strictMono hA'
  have hgA : ∀ k, g k ∈ A := fun k => Nat.nth_mem_of_infinite hA' k
  rw [mem_closure_iff_nhds]
  intro W hW
  have hW' := hW
  rw [nhds_bohr, e_zero] at hW'
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.1 hW'
  obtain ⟨Mb, hMb⟩ := (hfin.image (fun t : ℝ => |t|)).bddAbove
  obtain ⟨L, hL⟩ := sS_unbounded (2 * Mb)
  obtain ⟨l, n, hlN, hln, hVln⟩ := exists_pair (fun k => c * sS (g k)) hV (max L 1)
  have hL1 : 1 ≤ l := le_trans (le_max_right _ _) hlN
  have hLl : L ≤ l := le_trans (le_max_left _ _) hlN
  have hgl : l ≤ g l := hgm.id_le l
  have hgln : g l < g n := hgm hln
  have hL1' : 1 ≤ g l := le_trans hL1 hgl
  have hLgl : L ≤ g l := le_trans hLl hgl
  set x : ℝ := c * (sS (g n) - sS (g l)) with hx
  have hxW : x ∈ W := by
    apply hVW
    show e x ∈ V
    have : x = c * sS (g n) - c * sS (g l) := by rw [hx]; ring
    rw [this, e_sub]
    exact hVln
  have hxA : x ∉ J := by
    intro hxA
    have hT : (sS (g n) - sS (g l)) ∈ Tset := ⟨g n, g l, hL1', hgln, true, false, by simp [tval, sgn]; ring⟩
    have hmem : (sS (g n) - sS (g l)) ∈ {t | t ∈ Tset ∧ c * t ∈ J} := ⟨hT, hxA⟩
    have hle : |sS (g n) - sS (g l)| ≤ Mb := hMb ⟨_, hmem, rfl⟩
    have hb := (tval_bounds hgln true false).1
    have e1 : tval (g n) (g l) true false = sS (g n) - sS (g l) := by simp [tval, sgn]; ring
    rw [e1] at hb
    have hmono : sS L ≤ sS (g n) := sS_mono (by omega)
    linarith
  exact ⟨x, hxW, g n, g l, hgA n, hgA l, hL1', hgln, rfl, hxA⟩

/-! ### Comparison of `subConv A` and `subConv B` -/

/-- If `C` is disjoint from `B` and `J ∈ I_B`, then `J ∩ D` is finite for `D = {s_n - s_l : n, l ∈ C}`. -/
theorem DsetA_inter_finite {C B : Set ℕ} (hCB : ∀ n ∈ C, n ∉ B) {J : Set ℝ} (hJ : J ∈ IA B) :
    (J ∩ DsetA C 1 ∅).Finite := by
  obtain ⟨m, l, hJ'⟩ := mem_IA_iff.1 hJ
  obtain ⟨N1, hN1⟩ := top_index B l (m := max m 0) (γ1 := 1 / 2) (γ2 := 1) (le_max_right _ _) (by norm_num) one_pos
  refine Set.Finite.subset (((Finset.range N1 ×ˢ Finset.range N1).finite_toSet).image
    (fun p : ℕ × ℕ => sS p.1 - sS p.2)) ?_
  rintro x ⟨hxJ, n, l', hn, hl, hl1, hln, hx, -⟩
  by_contra hcon
  have hnN : N1 ≤ n := by
    by_contra h
    push Not at h
    refine hcon ⟨(n, l'), ?_, ?_⟩
    · simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
      exact ⟨h, lt_trans hln h⟩
    · simp only
      rw [hx]; ring
  obtain ⟨y, σ, hy, hσ, hxe⟩ := hJ' x hxJ
  have h1 := two_sS_le hln
  have h2 := sS_pos l'
  have hxpos : x = sS n - sS l' := by rw [hx]; ring
  have habs : |y + σ| = sS n - sS l' := by
    rw [← hxe, hxpos]
    exact abs_of_pos (by linarith)
  refine hN1 n hnN (hCB n hn) y σ (hy.trans (le_max_left _ _)) hσ ⟨?_, ?_⟩
  · rw [habs]; linarith
  · rw [habs]; linarith

/-- `A \ B` finite implies `subConv A ⊆ subConv B`. -/
theorem conv_sub_of_diff_finite {A B : Set ℕ} (h : (A \ B).Finite) {F : Filter ℝ} {x : ℝ}
    (hF : subConv A F x) : subConv B F x := by
  refine ⟨hF.1, ?_⟩
  obtain ⟨A', hA', hI⟩ := hF.2
  exact ⟨A', hA', IA_mono_of_diff_finite h hI⟩

/-- `subConv A ⊆ subConv B` implies that `A \ B` is finite. -/
theorem diff_finite_of_conv_sub {A B : Set ℕ} (h : ∀ (F : Filter ℝ) (x : ℝ), subConv A F x → subConv B F x) :
    (A \ B).Finite := by
  by_contra hinf
  set C : Set ℕ := A \ B with hC
  have hCB : ∀ n ∈ C, n ∉ B := fun n hn => hn.2
  have hCA : C ⊆ A := fun n hn => hn.1
  have hD := zero_mem_closure_DA hinf (c := 1) le_rfl (J := ∅) (by
    refine Set.Finite.subset Set.finite_empty ?_
    rintro t ⟨_, ht⟩
    exact absurd ht (Set.notMem_empty _))
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_t2
  haveI hne : (𝓝 (0 : ℝ) ⊓ 𝓟 (DsetA C 1 ∅)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hD
  have hconvA : subConv A (𝓝 (0 : ℝ) ⊓ 𝓟 (DsetA C 1 ∅)) 0 :=
    ⟨inf_le_left, DsetA C 1 ∅, Filter.mem_inf_of_right (Filter.mem_principal_self _),
      IA_mono hCA (DsetA_mem_IA C 1 ∅)⟩
  obtain ⟨-, J, hJF, hJI⟩ := h _ _ hconvA
  rw [Filter.mem_inf_principal] at hJF
  have hfin := DsetA_inter_finite hCB hJI
  have h0 : (0 : ℝ) ∉ J ∩ DsetA C 1 ∅ := fun h0 => absurd (DsetA_pos le_rfl h0.2) (lt_irrefl _)
  have hnb : (J ∩ DsetA C 1 ∅)ᶜ ∈ 𝓝 (0 : ℝ) := hfin.isClosed.isOpen_compl.mem_nhds h0
  rw [mem_closure_iff_nhds] at hD
  obtain ⟨x, hxW, hxD⟩ := hD _ (Filter.inter_mem hJF hnb)
  exact hxW.2 ⟨hxW.1 hxD, hxD⟩

/-- **Comparison.** Every `ξ_A`-convergent filter is `ξ_B`-convergent iff `A \ B` is finite. -/
theorem conv_sub_iff {A B : Set ℕ} :
    (∀ (F : Filter ℝ) (x : ℝ), subConv A F x → subConv B F x) ↔ (A \ B).Finite :=
  ⟨diff_finite_of_conv_sub, fun h _ _ hF => conv_sub_of_diff_finite h hF⟩

/-! ### Non-pretopological, non-Fréchet–Urysohn for infinite `A` -/

theorem subConv_not_pretop {A : Set ℕ} (hA : A.Infinite) : ¬ IsPretop (subConv A) := by
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  refine xi_not_pretop (IA_isIdeal A) (fun J hJ => ?_)
  obtain ⟨c, hc, hfin⟩ := exists_dilation (IA_sub_IS A hJ)
  exact ⟨DsetA A c J, DsetA_mem_IA A c J, DsetA_disjoint A c J, zero_mem_closure_DA hA hc.1 hfin⟩

theorem subConv_not_topological {A : Set ℕ} (hA : A.Infinite) : ¬ IsTopological (subConv A) :=
  fun h => subConv_not_pretop hA (topological_isPretop h)

theorem subConv_not_FU {A : Set ℕ} (hA : A.Infinite) : ¬ IsFU (subConv A) := by
  intro hFU
  have hball : Metric.ball (0 : ℝ) 1 ∈ IA A :=
    bounded_mem_IA A (M := 1) (fun a ha => by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ha; exact ha.le)
  have heq := xiB_eq_euclid_of_FU (IA_isIdeal A) hball hFU
  exact subConv_not_topological hA ⟨inferInstance, fun F x => heq F x⟩

/-! ### Finite `A`: the Euclidean convergence -/

lemma sumSetA_empty : ∀ (l : List ℝ) (x : ℝ), x ∈ sumSetA ∅ l → x = 0
  | [], x, hx => hx
  | a :: l, x, hx => by
    obtain ⟨c, hc, y, hy, rfl⟩ := mem_sumSetA_cons.1 hx
    have hc0 : c = 0 := by
      rcases hc with h | ⟨n, hn, -, -⟩
      · exact h
      · exact absurd hn (Set.notMem_empty _)
    rw [hc0, sumSetA_empty l y hy]; ring

/-- Every member of `I_A` is bounded when `A` is finite. -/
lemma IA_bounded_of_finite {A : Set ℕ} (hA : A.Finite) {J : Set ℝ} (hJ : J ∈ IA A) : ∃ M : ℝ, ∀ a ∈ J, |a| ≤ M := by
  have hJ' : J ∈ IA ∅ := IA_mono_of_diff_finite (by simpa using hA) hJ
  obtain ⟨m, l, h⟩ := mem_IA_iff.1 hJ'
  refine ⟨m, fun a ha => ?_⟩
  obtain ⟨y, σ, hy, hσ, rfl⟩ := h a ha
  rw [sumSetA_empty l σ hσ, add_zero]
  exact hy

#print axioms conv_sub_iff
#print axioms subConv_not_pretop
#print axioms subConv_not_FU

end Lac
end PVG
