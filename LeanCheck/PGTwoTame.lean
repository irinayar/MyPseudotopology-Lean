import Mathlib
import LeanCheck.PGNullFilters
import LeanCheck.PGXi
import LeanCheck.PGTwoCoreflection

/-!
# PGtwo: tame admissible pairs have a discrete coreflection (Lean check)

Scope. Definition 5.x (tame admissible pairs) and the theorem of the second article (`PGtwo.tex`) that a tame admissible pair
`(β, I)` gives a PG `ξ_{β,I}` (`PGXi`) all of whose continuous homomorphisms from topological groups have open kernels,
abstract form.

* `Tame I` : for every `A ∈ I` there is `N` such that every infinite `S ⊆ A` contains elements `s₁, …, sₙ` (`1 ≤ n ≤ N`,
  repetitions allowed) with `s₁ + ⋯ + sₙ ∉ A`;
* `exists_nhds_sum` : in a topological group, for every neighbourhood `U` of `0` and every `N` there is a neighbourhood
  `W` of `0` such that every sum of at most `N` elements of `W` lies in `U`;
* `kernel_open_of_tame` : for a tame admissible ideal `I` in a Hausdorff topological group `G`, every continuous homomorphism
  from a topological group into `ξ_{β,I}` has an open kernel.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

section Tame

variable {G : Type*} [AddCommGroup G]

/-- Tame ideals: bounded-length sums escape every member from infinite subsets of it. -/
def Tame (I : Set (Set G)) : Prop :=
  ∀ A ∈ I, ∃ N : ℕ, ∀ S : Set G, S ⊆ A → S.Infinite →
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ ∃ s : Fin n → G, (∀ i, s i ∈ S) ∧ ∑ i, s i ∉ A

variable {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]

/-- Sums of at most `N` elements of a small neighbourhood stay in a given neighbourhood of `0`. -/
theorem exists_nhds_sum (N : ℕ) : ∀ U ∈ 𝓝 (0 : T), ∃ W ∈ 𝓝 (0 : T),
    ∀ n : ℕ, n ≤ N → ∀ w : Fin n → T, (∀ i, w i ∈ W) → ∑ i, w i ∈ U := by
  induction N with
  | zero =>
    intro U hU
    refine ⟨U, hU, fun n hn w _ => ?_⟩
    have : n = 0 := by omega
    subst this
    simpa using mem_of_mem_nhds hU
  | succ N ih =>
    intro U hU
    obtain ⟨U₁, hU₁, hU₁U⟩ := exists_nhds_zero_half hU
    obtain ⟨W₁, hW₁n, hW₁s⟩ := ih U₁ hU₁
    refine ⟨W₁ ∩ U₁, Filter.inter_mem hW₁n hU₁, fun n hn w hw => ?_⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simpa using mem_of_mem_nhds hU
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [Fin.sum_univ_castSucc]
      refine hU₁U _ ?_ _ ?_
      · exact hW₁s m (by omega) (fun i => w (Fin.castSucc i)) (fun i => (hw _).1)
      · exact (hw _).2

/-- A tame admissible ideal in a Hausdorff topological group: every continuous homomorphism from a topological group into
`ξ_{β,I}` has an open kernel. -/
theorem kernel_open_of_tame [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    {I : Set (Set G)} (hI : AdmIdeal I) (hT : Tame I) (f : T →+ G)
    (hf : XiCont {F : Filter G | xi I F 0} f) : ∃ U ∈ 𝓝 (0 : T), ∀ x ∈ U, f x = 0 := by
  have hC : NullFamily {F : Filter G | xi I F 0} := nullFamily_of_conv (isPGConv_xi hI)
  have hM : xi I (Filter.map f (𝓝 (0 : T))) 0 := (xiCont_iff hC f).1 hf
  obtain ⟨hMne, hM0, A, hA, hAM⟩ := hM
  obtain ⟨N, hN⟩ := hT A hA
  have hU : f ⁻¹' A ∈ 𝓝 (0 : T) := hAM
  obtain ⟨W, hW, hWsum⟩ := exists_nhds_sum (N + 1) (f ⁻¹' A) hU
  have hWA : ∀ w ∈ W, f w ∈ A := by
    intro w hw
    have := hWsum 1 (by omega) (fun _ => w) (fun _ => hw)
    simpa using this
  have hfin : (f '' W).Finite := by
    by_contra hinf
    obtain ⟨n, hn1, hnN, s, hs, hsum⟩ := hN (f '' W) (by rintro _ ⟨w, hw, rfl⟩; exact hWA w hw) hinf
    choose w hwW hws using hs
    apply hsum
    have e : ∑ i, s i = f (∑ i, w i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => (hws i).symm)
    rw [e]
    exact hWsum n (by omega) w hwW
  have hclosed : IsClosed (f '' W \ {0}) := (hfin.subset Set.sdiff_subset).isClosed
  have hB : (f '' W \ {0})ᶜ ∈ 𝓝 (0 : G) :=
    hclosed.isOpen_compl.mem_nhds (by simp)
  have hV : f ⁻¹' ((f '' W \ {0})ᶜ) ∈ 𝓝 (0 : T) := hM0 hB
  refine ⟨f ⁻¹' ((f '' W \ {0})ᶜ) ∩ W, Filter.inter_mem hV hW, fun x hx => ?_⟩
  by_contra hne
  exact hx.1 ⟨⟨x, hx.2, rfl⟩, hne⟩

end Tame

end PG
