import Mathlib
import LeanCheck.PVGNotGroup
import LeanCheck.PVGProdLimit

/-!
# PVG: the atoms of any assignment of Bohr neighbourhoods sum to an open interval (Lean check)

Scope. Lemma "atoms sum to an open interval" of `PVG_v47` (Section "A necessary condition for the group property"; assignment form of
condition (N)). For every real `a` let `J_a = {a (s_n - s_m) + t : n, m ≥ 1, |t| ≤ 1}` (this is `[-1,1] + aS - aS`, a member of `I_S`), and let `B : ℝ → Set ℝ`
assign to every `a` a Bohr neighbourhood `B a` of `0`. The *atoms* are `Atoms B = ⋃_a (J_a ∩ B a)`.

* `Jtil_mem_IS` : `J_a ∈ I_S`;
* `atoms_add_contains_interval` : `Atoms B + Atoms B` contains a nonempty Euclidean open set (an open interval).

Proof (as in the article): by `prodLimit_bohr` (iterated Bohr limit of `a s_n - a s_m`) every `a` lies in some `T_p = {a : a (s_n - s_m) ∈ int_{τ_B} (B a)}`,
`p = (n, m)`, `n < m`; there are countably many `p`; by Baire's theorem some `closure (T_p)` has nonempty interior. Bohr-open sets are Euclidean open,
so the atoms contain an open set `U ⊇ σ T_p` (`σ = s_n - s_m`) which is dense in `σ · interior (closure T_p)`; two dense open sets of an interval sum to an interval.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set Pointwise
open scoped Classical

namespace PVG
namespace Lac
open Q95

/-- `J_a = [-1,1] + a S - a S` (elements `a (s_n - s_m) + t`, `|t| ≤ 1`). -/
def Jtil (a : ℝ) : Set ℝ := {y | ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ ∃ t : ℝ, |t| ≤ 1 ∧ y = a * (sS n - sS m) + t}

lemma Jtil_mem_IS (a : ℝ) : Jtil a ∈ IS := by
  have h1 : (Icc (-1 : ℝ) 1) ∈ IS := bounded_mem_IS (M := 1) (fun x hx => abs_le.2 hx)
  have h2 : Icc (-1 : ℝ) 1 + Jc a ∈ IS := IS_isIdeal.add h1 (Jc_mem_IS a)
  refine IS_isIdeal.mono h2 ?_
  rintro y ⟨n, m, hn, hm, t, ht, rfl⟩
  refine ⟨t, abs_le.1 ht, a * (sS n - sS m), ⟨n, m, hn, hm, rfl⟩, by ring⟩

/-- The atoms of an assignment `a ↦ B a`. -/
def Atoms (B : ℝ → Set ℝ) : Set ℝ := {y | ∃ a : ℝ, y ∈ Jtil a ∧ y ∈ B a}

lemma sS_lt_sS {n m : ℕ} (h : n < m) : sS n < sS m := by
  unfold sS
  exact pow_lt_pow_right₀ (by norm_num) (by nlinarith)

lemma bohr_nhds_euclid {x : ℝ} {s : Set ℝ} (hs : s ∈ @nhds ℝ bohrTop x) : s ∈ 𝓝 x :=
  bohr_coarser_euclid x hs

/-- **Atoms sum to an open interval.** -/
theorem atoms_add_contains_interval (B : ℝ → Set ℝ) (hB : ∀ a, B a ∈ @nhds ℝ bohrTop 0) :
    ∃ L : Set ℝ, IsOpen L ∧ L.Nonempty ∧ L ⊆ Atoms B + Atoms B := by
  -- the Bohr interior of `B a`
  set O : ℝ → Set ℝ := fun a => @interior ℝ bohrTop (B a) with hO
  have hOopen : ∀ a, @IsOpen ℝ bohrTop (O a) := fun a => @isOpen_interior ℝ bohrTop (B a)
  have hO0 : ∀ a, (0 : ℝ) ∈ O a := fun a =>
    (@mem_interior_iff_mem_nhds ℝ bohrTop 0 (B a)).2 (hB a)
  have hOsub : ∀ a, O a ⊆ B a := fun a => @interior_subset ℝ bohrTop (B a)
  have hOeucl : ∀ a, ∀ y ∈ O a, O a ∈ 𝓝 y := fun a y hy =>
    bohr_nhds_euclid ((@IsOpen.mem_nhds ℝ bohrTop _ _ (hOopen a) hy))
  -- the sets `T_p`
  let T : ℕ × ℕ → Set ℝ := fun p => {a | 1 ≤ p.1 ∧ p.1 < p.2 ∧ a * (sS p.1 - sS p.2) ∈ O a}
  have hcov : ⋃ p : ℕ × ℕ, T p = univ := by
    refine eq_univ_of_forall fun a => ?_
    obtain ⟨W0, hW0⟩ : ∃ W0 : Ultrafilter ℕ, Free W0 := ⟨Ultrafilter.of Filter.cofinite, Ultrafilter.of_le _⟩
    have hV : O a ∈ @nhds ℝ bohrTop 0 := @IsOpen.mem_nhds ℝ bohrTop _ _ (hOopen a) (hO0 a)
    have h1 := prodLimit a W0 hW0 (O a) hV
    have h0 : ∀ᶠ n in (W0 : Filter ℕ), 0 < n := prodLimit_lt W0 hW0 0
    obtain ⟨n, hn, hn0⟩ := (h1.and h0).exists
    obtain ⟨m, hm⟩ := hn.exists
    refine mem_iUnion.2 ⟨(n, m), ?_⟩
    refine ⟨hn0, hm.1, ?_⟩
    have : a * (sS n - sS m) = a * sS n - a * sS m := by ring
    simpa [this] using hm.2
  -- Baire
  obtain ⟨p, hp⟩ : ∃ p : ℕ × ℕ, (interior (closure (T p))).Nonempty := by
    refine nonempty_interior_of_iUnion_of_closed (f := fun p => closure (T p)) (fun p => isClosed_closure) ?_
    refine eq_univ_of_forall fun a => ?_
    have : a ∈ ⋃ p : ℕ × ℕ, T p := by rw [hcov]; trivial
    obtain ⟨p, hp⟩ := mem_iUnion.1 this
    exact mem_iUnion.2 ⟨p, subset_closure hp⟩
  obtain ⟨g0, hg0⟩ := hp
  -- `T p` is nonempty, hence `1 ≤ p.1 < p.2`
  have hTne : (T p).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty, interior_empty] at hg0
    exact hg0
  obtain ⟨a1, ha1⟩ := hTne
  have hp1 : 1 ≤ p.1 := ha1.1
  have hp12 : p.1 < p.2 := ha1.2.1
  set σ : ℝ := sS p.1 - sS p.2 with hσ
  have hσne : σ ≠ 0 := by
    have := sS_lt_sS hp12
    intro h; linarith
  -- the open set `U ⊆ Atoms B`
  let U : Set ℝ := {y | ∃ a ∈ T p, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ Metric.ball (a * σ) δ ⊆ B a ∧ y ∈ Metric.ball (a * σ) δ}
  have hUopen : IsOpen U := by
    have : U = ⋃ a ∈ T p, ⋃ δ ∈ {δ : ℝ | 0 < δ ∧ δ ≤ 1 ∧ Metric.ball (a * σ) δ ⊆ B a}, Metric.ball (a * σ) δ := by
      ext y
      simp only [U, mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨a, ha, δ, h1, h2, h3, h4⟩
        exact ⟨a, ha, δ, ⟨h1, h2, h3⟩, h4⟩
      · rintro ⟨a, ha, δ, ⟨h1, h2, h3⟩, h4⟩
        exact ⟨a, ha, δ, h1, h2, h3, h4⟩
    rw [this]
    exact isOpen_biUnion fun a _ => isOpen_biUnion fun δ _ => Metric.isOpen_ball
  have hUatoms : U ⊆ Atoms B := by
    rintro y ⟨a, ha, δ, hδ0, hδ1, hball, hy⟩
    refine ⟨a, ?_, hball hy⟩
    refine ⟨p.1, p.2, hp1, by omega, y - a * σ, ?_, by simp [hσ]⟩
    have : dist y (a * σ) < δ := hy
    rw [Real.dist_eq] at this
    exact (abs_lt.1 this |>.2.le.trans hδ1 |> fun h => abs_le.2 ⟨by linarith [abs_lt.1 this |>.1], h⟩)
  have hσTU : ∀ a ∈ T p, a * σ ∈ U := by
    intro a ha
    have hmem : a * σ ∈ O a := ha.2.2
    have hnh : O a ∈ 𝓝 (a * σ) := hOeucl a _ hmem
    obtain ⟨ε, hε0, hεsub⟩ := Metric.mem_nhds_iff.1 hnh
    refine ⟨a, ha, min ε 1, lt_min hε0 one_pos, min_le_right _ _, ?_, Metric.mem_ball_self (lt_min hε0 one_pos)⟩
    exact (Metric.ball_subset_ball (min_le_left _ _)).trans (hεsub.trans (hOsub a))
  -- `H = σ · interior (closure (T p))` is open and contained in `closure U`
  set H : Set ℝ := (fun x => σ * x) '' interior (closure (T p)) with hH
  have hHopen : IsOpen H := by
    have := (Homeomorph.mulLeft₀ σ hσne).isOpenMap _ (isOpen_interior (s := closure (T p)))
    simpa [hH] using this
  have hHcl : H ⊆ closure U := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ closure (T p) := interior_subset hx
    have himg : (fun x => σ * x) '' closure (T p) ⊆ closure U := by
      have hcont : Continuous (fun x : ℝ => σ * x) := continuous_const.mul continuous_id
      refine (image_closure_subset_closure_image hcont).trans (closure_mono ?_)
      rintro _ ⟨a, ha, rfl⟩
      have := hσTU a ha
      simpa [mul_comm] using this
    exact himg ⟨x, hx', rfl⟩
  have hHne : H.Nonempty := ⟨σ * g0, g0, hg0, rfl⟩
  refine ⟨H + H, hHopen.add_left, hHne.add hHne, ?_⟩
  -- two dense open sets of an interval sum to an interval
  rintro y ⟨g1, hg1, g2, hg2, rfl⟩
  have hBopen : IsOpen {x : ℝ | g1 + g2 - x ∈ U} :=
    hUopen.preimage (continuous_const.sub continuous_id)
  set G : Set ℝ := H ∩ {x | g1 + g2 - x ∈ H} with hG
  have hGopen : IsOpen G := hHopen.inter (hHopen.preimage (continuous_const.sub continuous_id))
  have hg1G : g1 ∈ G := ⟨hg1, by simpa using hg2⟩
  -- `G ⊆ closure U`
  have hGA : G ⊆ closure U := fun x hx => hHcl hx.1
  -- `G ⊆ closure {x | y - x ∈ U}`
  have hGB : G ⊆ closure {x : ℝ | g1 + g2 - x ∈ U} := by
    intro x hx
    rw [mem_closure_iff]
    intro N hN hxN
    have hyx : g1 + g2 - x ∈ closure U := hHcl hx.2
    have hN' : IsOpen {z : ℝ | g1 + g2 - z ∈ N} := hN.preimage (continuous_const.sub continuous_id)
    have hmem : g1 + g2 - x ∈ {z : ℝ | g1 + g2 - z ∈ N} := by simpa using hxN
    obtain ⟨u, hu, huU⟩ := mem_closure_iff.1 hyx _ hN' hmem
    refine ⟨g1 + g2 - u, hu, ?_⟩
    simpa using huU
  -- find `x ∈ G` with `x ∈ U` and `y - x ∈ U`
  have h1 : (G ∩ U).Nonempty := by
    obtain ⟨z, hz⟩ := mem_closure_iff.1 (hGA hg1G) G hGopen hg1G
    exact ⟨z, hz⟩
  obtain ⟨x0, hx0G, hx0U⟩ := h1
  have h2 : ((G ∩ U) ∩ {x : ℝ | g1 + g2 - x ∈ U}).Nonempty := by
    exact mem_closure_iff.1 (hGB hx0G) (G ∩ U) (hGopen.inter hUopen) ⟨hx0G, hx0U⟩
  obtain ⟨x1, ⟨_, hx1U⟩, hx1B⟩ := h2
  refine ⟨x1, hUatoms hx1U, g1 + g2 - x1, hUatoms hx1B, by ring⟩

#print axioms atoms_add_contains_interval

end Lac
end PVG
