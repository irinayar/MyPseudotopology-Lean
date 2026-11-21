import Mathlib
import LeanCheck.PGLimit

/-!
# PG: group topologies containing the convergence of `ξ` (Lean check, abstract part of Theorem T)

Scope. Parts (b) and (c) of Theorem T of `PG_v4`, in the abstract setting of `PGXi`/`PGLimit`: `G` is an abelian group with a
Hausdorff group topology `β` (the given instance), `I` an admissible ideal, `D : ℕ → Set G` closed sets with every member of `I`
contained in some `D k`, and `Op : Set G → Prop` the family of open sets of a second topology `τ'` (only the family is used,
so no second `TopologicalSpace` instance is needed) such that for every `W` with `Op W` and every `k` there is a `β`-open `O`
with `O ∩ D k = W ∩ D k` (the `β`-trace of `W` on `D k` is its `τ'`-trace). In the article `τ'` is the topology induced on `ℤ`
by the direct limit of the closures `E_k` of the digit sets in the Bohr compactification.

* `xi_converges_op` : if `F → x` for `ξ`, then `W ∈ F` for every `W` with `Op W` and `x ∈ W` (`F` converges to `x` in `τ'`);
* `isOpenXi_of_op` : every `W` with `Op W` is open in the topological modification of `ξ` (`τ' ≤ τ_ξ`).

Not formalized: that `τ'` is a group topology (the direct limit of compact sets is a `k_ω`-group; this uses the product theorem for
`k_ω`-spaces), and the construction of `τ'` from the compactification.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]

theorem xi_converges_op {I : Set (Set G)} (D : ℕ → Set G) (hD : ∀ A ∈ I, ∃ k, A ⊆ D k)
    (hclosed : ∀ k, IsClosed (D k)) (Op : Set G → Prop)
    (htrace : ∀ (k : ℕ) (W : Set G), Op W → ∃ O : Set G, IsOpen O ∧ O ∩ D k = W ∩ D k)
    {F : Filter G} {x : G} (hF : xi I F x) {W : Set G} (hW : Op W) (hxW : x ∈ W) : W ∈ F := by
  obtain ⟨hne, hle, A, hA, hAF⟩ := hF
  obtain ⟨k, hk⟩ := hD A hA
  have hDF : D k ∈ F := Filter.mem_of_superset hAF hk
  have hxD : x ∈ D k := by
    have hx : x ∈ closure (D k) := by
      rw [mem_closure_iff_clusterPt]
      exact hne.mono (le_inf hle (Filter.le_principal_iff.2 hDF))
    rwa [(hclosed k).closure_eq] at hx
  obtain ⟨O, hO, hOW⟩ := htrace k W hW
  have hxO : x ∈ O := by
    have : x ∈ O ∩ D k := by rw [hOW]; exact ⟨hxW, hxD⟩
    exact this.1
  have hOF : O ∈ F := hle (hO.mem_nhds hxO)
  have h1 : O ∩ D k ∈ F := Filter.inter_mem hOF hDF
  rw [hOW] at h1
  exact Filter.mem_of_superset h1 (fun y hy => hy.1)

theorem isOpenXi_of_op {I : Set (Set G)} (hI : AdmIdeal I) (D : ℕ → Set G)
    (hD : ∀ A ∈ I, ∃ k, A ⊆ D k) (hDI : ∀ k, D k ∈ I) (hclosed : ∀ k, IsClosed (D k))
    (Op : Set G → Prop)
    (htrace : ∀ (k : ℕ) (W : Set G), Op W → ∃ O : Set G, IsOpen O ∧ O ∩ D k = W ∩ D k)
    {W : Set G} (hW : Op W) : IsOpenXi I W := by
  rw [isOpenXi_iff_closed_traces hI D hD hDI hclosed]
  intro k
  obtain ⟨O, hO, hOW⟩ := htrace k W hW
  have : D k \ W = D k ∩ Oᶜ := by
    ext y
    constructor
    · rintro ⟨hyD, hyW⟩
      refine ⟨hyD, fun hyO => hyW ?_⟩
      have : y ∈ O ∩ D k := ⟨hyO, hyD⟩
      rw [hOW] at this
      exact this.1
    · rintro ⟨hyD, hyO⟩
      refine ⟨hyD, fun hyW => hyO ?_⟩
      have : y ∈ W ∩ D k := ⟨hyW, hyD⟩
      rw [← hOW] at this
      exact this.1
  rw [this]
  exact (hclosed k).inter hO.isClosed_compl

end PG
