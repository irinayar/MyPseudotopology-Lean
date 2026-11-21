import Mathlib
import LeanCheck.PGXi

/-!
# PG: the modification as an inductive-limit topology (Lean check)

Scope. Theorem 6.5, Lemma 6.3 and Proposition 6.6 of `PG_v3`, in the abstract setting of `PGXi`: `G` is an abelian group with a
Hausdorff group topology, `I` is an admissible ideal (`AdmIdeal`) and `D : ℕ → Set G` is a family of closed sets with
`D k ∈ I` and such that every member of `I` lies in some `D k` (for `ℤ`, the Bohr topology and the digit ideal `I_p`, with
`D k = D_{p,k}`; the closedness of `D_{p,k}` is Proposition 6.4 of the article and is NOT formalized here).

* `isOpenXi_iff_closed_traces` : `U` is open in the topological modification iff `D k \ U` is closed for every `k`
  (equivalently `U ∩ D k` is relatively open in `D k` for every `k`);
* `thin_set_closed` : if `C ∩ D k` is finite for every `k`, then every subset `B ⊆ C` is closed in the modification
  (Lemma 6.3);
* `isOpenXi_translate`, `isOpenXi_neg` : preimages of open sets of the modification under translations and under
  negation are open (Proposition 6.6; `IsOpenXi` is invariant under the homeomorphisms of `G` that map members of `I` to
  members of `I`, `isOpenXi_preimage_homeo`).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]

/-- Theorem 6.5. -/
theorem isOpenXi_iff_closed_traces {I : Set (Set G)} (hI : AdmIdeal I) (D : ℕ → Set G)
    (hD : ∀ A ∈ I, ∃ k, A ⊆ D k) (hDI : ∀ k, D k ∈ I) (hclosed : ∀ k, IsClosed (D k)) (U : Set G) :
    IsOpenXi I U ↔ ∀ k, IsClosed (D k \ U) := by
  rw [isOpenXi_iff hI]
  constructor
  · intro H k
    have h1 := H (D k) (hDI k)
    have h2 : closure (D k \ U) ⊆ D k \ U := by
      intro x hx
      refine ⟨?_, fun hxU => ?_⟩
      · exact (hclosed k).closure_subset (closure_mono Set.sdiff_subset hx)
      · have : x ∈ closure (D k \ U) ∩ U := ⟨hx, hxU⟩
        rw [h1] at this
        exact this
    exact closure_subset_iff_isClosed.1 h2
  · intro H B hB
    obtain ⟨k, hk⟩ := hD B hB
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hxU⟩
    have : x ∈ closure (D k \ U) := closure_mono (Set.diff_subset_diff_left hk) hx1
    rw [(H k).closure_eq] at this
    exact this.2 hxU

/-- Lemma 6.3: subsets of thin sets are closed in the modification. -/
theorem thin_set_closed {I : Set (Set G)} (hI : AdmIdeal I) (D : ℕ → Set G)
    (hD : ∀ A ∈ I, ∃ k, A ⊆ D k) (hDI : ∀ k, D k ∈ I) (hclosed : ∀ k, IsClosed (D k))
    (C : Set G) (hC : ∀ k, (C ∩ D k).Finite) (B : Set G) (hB : B ⊆ C) : IsOpenXi I Bᶜ := by
  rw [isOpenXi_iff_closed_traces hI D hD hDI hclosed]
  intro k
  have : D k \ Bᶜ = D k ∩ B := by
    ext x; simp
  rw [this]
  refine Set.Finite.isClosed ((hC k).subset ?_)
  rintro x ⟨hxD, hxB⟩
  exact ⟨hB hxB, hxD⟩

/-- Invariance under homeomorphisms preserving `I` (Proposition 6.6). -/
theorem isOpenXi_preimage_homeo {I : Set (Set G)} (hI : AdmIdeal I) (h : G ≃ₜ G)
    (hh : ∀ B ∈ I, h '' B ∈ I) {U : Set G} (hU : IsOpenXi I U) : IsOpenXi I (h ⁻¹' U) := by
  rw [isOpenXi_iff hI] at hU ⊢
  intro B hB
  have h1 : B \ (h ⁻¹' U) = h ⁻¹' ((h '' B) \ U) := by
    ext y
    simp only [Set.mem_diff, Set.mem_preimage, h.injective.mem_set_image]
  rw [h1, ← h.preimage_closure, ← Set.preimage_inter, hU (h '' B) (hh B hB), Set.preimage_empty]

theorem isOpenXi_translate {I : Set (Set G)} (hI : AdmIdeal I) (a : G) {U : Set G}
    (hU : IsOpenXi I U) : IsOpenXi I ((fun y => a + y) ⁻¹' U) := by
  refine isOpenXi_preimage_homeo hI (Homeomorph.addLeft a) ?_ hU
  intro B hB
  have := hI.add {a} (hI.single a) B hB
  rwa [Set.image2_singleton_left] at this

theorem isOpenXi_neg {I : Set (Set G)} (hI : AdmIdeal I) {U : Set G}
    (hU : IsOpenXi I U) : IsOpenXi I ((fun y => -y) ⁻¹' U) :=
  isOpenXi_preimage_homeo hI (Homeomorph.neg G) (fun B hB => hI.neg B hB) hU

end PG
