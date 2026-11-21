import Mathlib

/-!
# PG: closures of the digit sets in a compactification (Lean check)

Scope. The facts about the sets `E_k = cl_K e(D_k)` used for Theorem T of `PG_v4` (the closures of the digit sets in the
Bohr compactification `K` of `ℤ`), in the abstract setting of a topological embedding `e : G → K`.

* `closure_image_inter_range` : if `e` is a topological embedding and `D ⊆ G` is closed, then
  `cl_K (e '' D) ∩ range e = e '' D` (so `E_k ∩ ℤ = D_k` when `D_k` is closed in the Bohr topology);
* `closure_add_subset` : `cl A + cl B ⊆ cl (A + B)` in a topological additive monoid, and
  `closure_neg_subset`: `-cl A ⊆ cl (-A)` in a topological additive group; hence `E_k + E_l ⊆ E_{k+l}` and `-E_k = E_k`
  follow from `D_k + D_l ⊆ D_{k+l}` and `-D_k = D_k`.

Not formalized: the Bohr compactification itself, the compactness of `E_k`, and the fact that the direct limit of the `E_k` is a
topological group (product theorem for `k_ω`-spaces).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Set Topology

namespace PG

variable {G K : Type*} [TopologicalSpace G] [TopologicalSpace K]

theorem closure_image_inter_range {e : G → K} (he : Topology.IsEmbedding e) {D : Set G}
    (hD : IsClosed D) : closure (e '' D) ∩ Set.range e = e '' D := by
  ext y
  constructor
  · rintro ⟨hy, ⟨x, rfl⟩⟩
    refine ⟨x, ?_, rfl⟩
    have hx : x ∈ closure D := by
      rw [he.closure_eq_preimage_closure_image]
      exact hy
    rwa [hD.closure_eq] at hx
  · rintro ⟨x, hx, rfl⟩
    exact ⟨subset_closure ⟨x, hx, rfl⟩, ⟨x, rfl⟩⟩

theorem closure_add_subset [Add K] [ContinuousAdd K] (A B : Set K) :
    Set.image2 (· + ·) (closure A) (closure B) ⊆ closure (Set.image2 (· + ·) A B) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  have hab : (a, b) ∈ closure (A ×ˢ B) := by
    rw [closure_prod_eq]
    exact ⟨ha, hb⟩
  exact map_mem_closure (f := fun p : K × K => p.1 + p.2) continuous_add hab
    (fun p hp => ⟨p.1, hp.1, p.2, hp.2, rfl⟩)

theorem closure_neg_subset [Neg K] [ContinuousNeg K] (A : Set K) :
    (fun x : K => -x) '' closure A ⊆ closure ((fun x : K => -x) '' A) := by
  rintro _ ⟨a, ha, rfl⟩
  exact map_mem_closure continuous_neg ha (fun x hx => ⟨x, hx, rfl⟩)

end PG
