import Mathlib
import LeanCheck.PGIdem

/-!
# PG: closures of sumsets of a set with compact closure (Lean check)

Scope. Lemma 7.4 of `PG_v7`. In a Hausdorff topological additive group `K`, if `A ⊆ K` has compact closure, then the closure of
the `m`-fold sumset `Pw A m = A + ... + A` is the `m`-fold sumset of the closure: `closure (Pw A m) = Pw (closure A) m`
(`closure_Pw`), and these sets are compact (`isCompact_Pw`). For `K` the Bohr compactification of `ℤ` and `A = D_{p,1}` this gives
`cl(D_{p,m}) = G + ... + G` with `G` the compact closure of `{0, ±p^n}`.

`Pw` is defined in `PGIdem`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Set Topology

namespace PG

variable {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K] [T2Space K]

theorem isCompact_Pw {C : Set K} (hC : IsCompact C) : ∀ m : ℕ, IsCompact (Pw C m)
  | 0 => by simpa [Pw] using isCompact_singleton
  | m + 1 => by
    have h := (hC.prod (isCompact_Pw hC m)).image (continuous_add : Continuous fun p : K × K => p.1 + p.2)
    have e : (fun p : K × K => p.1 + p.2) '' (C ×ˢ Pw C m) = Set.image2 (· + ·) C (Pw C m) :=
      Set.image_prod (fun a b : K => a + b)
    rw [e] at h
    exact h

theorem Pw_mono_set {A B : Set K} (h : A ⊆ B) : ∀ m : ℕ, Pw A m ⊆ Pw B m
  | 0 => fun x hx => hx
  | m + 1 => by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, h ha, b, Pw_mono_set h m hb, rfl⟩

theorem closure_Pw {A : Set K} (hA : IsCompact (closure A)) :
    ∀ m : ℕ, closure (Pw A m) = Pw (closure A) m
  | 0 => by
    simp [Pw]
  | m + 1 => by
    have ih := closure_Pw hA m
    have hcomp : IsCompact (Pw (closure A) (m + 1)) := isCompact_Pw hA (m + 1)
    apply Set.Subset.antisymm
    · apply closure_minimal _ hcomp.isClosed
      rintro _ ⟨a, ha, b, hb, rfl⟩
      refine ⟨a, subset_closure ha, b, ?_, rfl⟩
      rw [← ih]
      exact subset_closure hb
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      rw [← ih] at hy
      have hxy : (x, y) ∈ closure (A ×ˢ Pw A m) := by
        rw [closure_prod_eq]
        exact ⟨hx, hy⟩
      exact map_mem_closure (f := fun p : K × K => p.1 + p.2) continuous_add hxy
        (fun p hp => ⟨p.1, hp.1, p.2, hp.2, rfl⟩)

end PG
