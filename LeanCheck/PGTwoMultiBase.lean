import Mathlib
import LeanCheck.PGDigit
import LeanCheck.PGTwoTame
import LeanCheck.PGTwoCosets

/-!
# PGtwo: finitely many integer bases, granting a bound on arithmetic progressions (Lean check)

Scope. The extension to a finite family of bases in the remark on arithmetic progressions of the second article
(`PGtwo.tex`). `D p k` is the set of sums of at most `k` signed powers of `p` (`PGDigit`).

* `Dmulti p k` : the sums `d 0 + ⋯ + d (r-1)` with `d i ∈ D (p i) k`; `Imulti p` : the sets contained in some `Dmulti p k`;
* `APBounded p` : for every `k` the lengths of the arithmetic progressions with nonzero difference inside `Dmulti p k` are
  bounded. **This is a hypothesis.** In the article it comes from the quoted theorem of Hajdu in the formulation of
  Conant, which is NOT formalized here or anywhere in this repository;
* `admIdeal_Imulti` : with at least one base, the family is an admissible ideal (properness from `APBounded`);
* `tame_Imulti` : it is tame;
* `kernel_open_Imulti` : for every Hausdorff group topology `β` on `ℤ` (the article takes the Bohr topology), every
  continuous homomorphism from a topological group into the PG of `β` and `Imulti p` has an open kernel.

No condition on the bases is used. A Lean proof verifies its formal statement under its hypotheses; the correspondence
with the article requires mathematical review.
-/

open Filter Set Topology

namespace PG

section MultiBase

variable {r : ℕ} (p : Fin r → ℕ)

/-- Sums of one element of `D (p i) k` for every base. -/
def Dmulti (k : ℕ) : Set ℤ := {n | ∃ d : Fin r → ℤ, (∀ i, d i ∈ D (p i) k) ∧ ∑ i, d i = n}

/-- The sets contained in some `Dmulti p k`. -/
def Imulti : Set (Set ℤ) := {A | ∃ k, A ⊆ Dmulti p k}

/-- Bounded arithmetic progressions in every layer. -/
def APBounded : Prop :=
  ∀ k : ℕ, ∃ R : ℕ, ∀ a d : ℤ, d ≠ 0 → ¬ ∀ j : ℕ, j ≤ R → a + (j : ℤ) * d ∈ Dmulti p k

theorem Dmulti_mono {k l : ℕ} (h : k ≤ l) : Dmulti p k ⊆ Dmulti p l := by
  rintro n ⟨d, hd, rfl⟩
  exact ⟨d, fun i => D_mono h (hd i), rfl⟩

theorem Dmulti_add {k l : ℕ} {n m : ℤ} (hn : n ∈ Dmulti p k) (hm : m ∈ Dmulti p l) : n + m ∈ Dmulti p (k + l) := by
  obtain ⟨d, hd, rfl⟩ := hn
  obtain ⟨e, he, rfl⟩ := hm
  exact ⟨fun i => d i + e i, fun i => D_add (hd i) (he i), Finset.sum_add_distrib⟩

theorem Dmulti_neg {k : ℕ} {n : ℤ} (hn : n ∈ Dmulti p k) : -n ∈ Dmulti p k := by
  obtain ⟨d, hd, rfl⟩ := hn
  exact ⟨fun i => -d i, fun i => D_neg (hd i), Finset.sum_neg_distrib _⟩

theorem mem_Dmulti_abs (hr : 0 < r) (n : ℤ) : n ∈ Dmulti p n.natAbs := by
  refine ⟨fun i => if i = ⟨0, hr⟩ then n else 0, fun i => ?_, ?_⟩
  · by_cases h : i = ⟨0, hr⟩
    · subst h
      simpa using mem_D_abs (p ⟨0, hr⟩) n
    · simpa [h] using zero_mem_D (p i) n.natAbs
  · simp

theorem admIdeal_Imulti (hr : 0 < r) (hAP : APBounded p) : AdmIdeal (Imulti p) where
  sub := by
    rintro A ⟨k, hk⟩ B hB
    exact ⟨k, hB.trans hk⟩
  union := by
    rintro A ⟨k, hk⟩ B ⟨l, hl⟩
    exact ⟨max k l, Set.union_subset (hk.trans (Dmulti_mono p (le_max_left _ _)))
      (hl.trans (Dmulti_mono p (le_max_right _ _)))⟩
  single := by
    intro n
    exact ⟨n.natAbs, by simpa using mem_Dmulti_abs p hr n⟩
  proper := by
    rintro ⟨k, hk⟩
    obtain ⟨R, hR⟩ := hAP k
    exact hR 0 1 one_ne_zero (fun j _ => hk (Set.mem_univ _))
  add := by
    rintro A ⟨k, hk⟩ B ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Dmulti_add p (hk ha) (hl hb)
  neg := by
    rintro A ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact Dmulti_neg p (hk ha)

theorem tame_Imulti (hAP : APBounded p) : Tame (Imulti p) := by
  refine tame_of_ap_bounded _ (fun A hA => ?_)
  obtain ⟨k, hk⟩ := hA
  obtain ⟨R, hR⟩ := hAP k
  exact ⟨R, fun a d hd h => hR a d hd (fun j hj => hk (h j hj))⟩

/-- For every Hausdorff group topology `β` on `ℤ`, every continuous homomorphism from a topological group into the PG of
`β` and the ideal has an open kernel. -/
theorem kernel_open_Imulti (hr : 0 < r) (hAP : APBounded p) (β : TopologicalSpace ℤ)
    (hβ : @IsTopologicalAddGroup ℤ β _) (h2 : @T2Space ℤ β)
    {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] (f : T →+ ℤ)
    (hf : XiCont (idealNull β (Imulti p)) f) : ∃ U ∈ 𝓝 (0 : T), ∀ x ∈ U, f x = 0 :=
  @kernel_open_of_tame ℤ _ T _ _ _ β hβ h2 (Imulti p) (admIdeal_Imulti p hr hAP) (tame_Imulti p hAP) f hf

end MultiBase

end PG
