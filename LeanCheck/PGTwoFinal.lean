import Mathlib
import LeanCheck.PGNullFilters
import LeanCheck.PGGenerated
import LeanCheck.PGTwoGeneration
import LeanCheck.PGTwoLattice
import LeanCheck.PGTwoReflection

/-!
# PGtwo: initial and final structures, quotients of topological groups (Lean check)

Scope. Section 6 of the second article (`PGtwo.tex`), Proposition 6.3, Theorem 6.4 and Proposition 6.6, abstract form.
A PG is given by a null family (`PGNullFilters`).

* `exists_ultra_map_eq` : an ultrafilter finer than the image `f F` of a proper filter is the image of an ultrafilter finer
  than `F`;
* `initFam f C`, `initFam_nullFamily`, `initFam_univ` : the initial structure for a family of homomorphisms
  `f i : H →+ G i` (products, subgroups): the proper filters whose images are null for every `i` form a null family, and a
  homomorphism into `H` is continuous iff every composite is (Proposition 6.3);
* `finalGen f C`, `map_mem_finalGen`, `finalGen_univ` : the final structure for a family `f i : G i →+ H`, the PG generated
  (`PGTwoGeneration`) by the images of the null filters; a homomorphism out of `H` is continuous iff every composite is
  (Theorem 6.4);
* `nullTop`, `nullTop_nullFamily` : the filters finer than `𝓝 0` in a topological group form a null family;
* `final_of_open_map`, `final_quotient` : the final structure for a continuous open homomorphism of topological groups, in
  particular the quotient map, is the topological group of the target (Proposition 6.6).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

/-- An ultrafilter finer than the image of a proper filter is the image of an ultrafilter finer than the filter. -/
theorem exists_ultra_map_eq {H G : Type*} (f : H → G) (F : Filter H) [F.NeBot] (V : Ultrafilter G)
    (hV : (V : Filter G) ≤ Filter.map f F) :
    ∃ W : Ultrafilter H, (W : Filter H) ≤ F ∧ W.map f = V := by
  have hne : (F ⊓ Filter.comap f (V : Filter G)).NeBot := by
    rw [Filter.inf_neBot_iff]
    intro s hs t ht
    obtain ⟨C, hC, hCt⟩ := Filter.mem_comap.1 ht
    have h1 : f '' s ∈ (V : Filter G) := hV (Filter.image_mem_map hs)
    obtain ⟨y, ⟨a, ha, rfl⟩, hyC⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 hC)
    exact ⟨a, ha, hCt hyC⟩
  let W : Ultrafilter H := Ultrafilter.of (F ⊓ Filter.comap f (V : Filter G))
  have hW : (W : Filter H) ≤ F ⊓ Filter.comap f (V : Filter G) := Ultrafilter.of_le _
  refine ⟨W, hW.trans inf_le_left, ?_⟩
  have h1 : ((W.map f : Ultrafilter G) : Filter G) ≤ (V : Filter G) := by
    rw [Ultrafilter.coe_map]
    exact Filter.map_le_iff_le_comap.2 (hW.trans inf_le_right)
  exact Ultrafilter.coe_le_coe.1 h1

section Initial

variable {H : Type*} [AddCommGroup H] {ι : Type*} {Gi : ι → Type*} [∀ i, AddCommGroup (Gi i)]

/-- The initial structure for the homomorphisms `f i : H →+ Gi i`. -/
def initFam (f : ∀ i, H →+ Gi i) (C : ∀ i, Set (Filter (Gi i))) : Set (Filter H) :=
  {F | F.NeBot ∧ ∀ i, Filter.map (f i) F ∈ C i}

theorem initFam_nullFamily (f : ∀ i, H →+ Gi i) {C : ∀ i, Set (Filter (Gi i))}
    (hC : ∀ i, NullFamily (C i)) : NullFamily (initFam f C) where
  ne := fun F hF => hF.1
  pure_zero := ⟨inferInstance, fun i => by
    rw [Filter.map_pure, map_zero]; exact (hC i).pure_zero⟩
  finer := by
    rintro F ⟨hne, hF⟩ H' hle hH'
    exact ⟨hH', fun i => (hC i).finer _ (hF i) _ (Filter.map_mono hle) (hH'.map _)⟩
  add := by
    rintro F ⟨hFn, hF⟩ H' ⟨hHn, hH⟩
    refine ⟨hFn.map₂ hHn, fun i => ?_⟩
    have e : Filter.map (f i) (Filter.map₂ (· + ·) F H')
        = Filter.map₂ (· + ·) (Filter.map (f i) F) (Filter.map (f i) H') := by
      apply Filter.map_map₂_distrib
      intro a b
      exact map_add _ _ _
    rw [e]
    exact (hC i).add _ (hF i) _ (hH i)
  neg := by
    rintro F ⟨hne, hF⟩
    refine ⟨hne.map _, fun i => ?_⟩
    have e : Filter.map (f i) (Filter.map (fun x : H => -x) F)
        = Filter.map (fun x : Gi i => -x) (Filter.map (f i) F) := by
      rw [Filter.map_map, Filter.map_map]
      congr 1
      funext x
      simp [map_neg]
    rw [e]
    exact (hC i).neg _ (hF i)
  ultra := by
    rintro F hne hU
    refine ⟨hne, fun i => (hC i).ultra _ (hne.map _) (fun V hV => ?_)⟩
    haveI := hne
    obtain ⟨W, hWF, hWV⟩ := exists_ultra_map_eq (f i) F V hV
    have h := (hU W hWF).2 i
    have : Filter.map (f i) (W : Filter H) = (V : Filter (Gi i)) := by
      rw [← Ultrafilter.coe_map, hWV]
    rwa [this] at h

/-- Universal property of the initial structure (Proposition 6.3). -/
theorem initFam_univ (f : ∀ i, H →+ Gi i) {C : ∀ i, Set (Filter (Gi i))} {L : Type*} [AddCommGroup L]
    (CL : Set (Filter L)) (hCL : NullFamily CL) (h : L →+ H) :
    (∀ F ∈ CL, Filter.map h F ∈ initFam f C) ↔
      ∀ i, ∀ F ∈ CL, Filter.map ((f i).comp h) F ∈ C i := by
  constructor
  · intro hh i F hF
    have := (hh F hF).2 i
    rwa [Filter.map_map] at this
  · intro hh F hF
    refine ⟨(hCL.ne F hF).map _, fun i => ?_⟩
    rw [Filter.map_map]
    exact hh i F hF

end Initial

section Final

variable {H : Type*} [AddCommGroup H] {ι : Type*} {Gi : ι → Type*} [∀ i, AddCommGroup (Gi i)]

/-- The final structure for the homomorphisms `f i : Gi i →+ H`: the PG generated by the images of the null filters. -/
def finalGen (f : ∀ i, Gi i →+ H) (C : ∀ i, Set (Filter (Gi i))) : Set (Filter H) :=
  genFam {F | ∃ i, ∃ F0 ∈ C i, F = Filter.map (f i) F0}

theorem finalGen_nullFamily (f : ∀ i, Gi i →+ H) (C : ∀ i, Set (Filter (Gi i))) :
    NullFamily (finalGen f C) := genFam_nullFamily _

theorem map_mem_finalGen (f : ∀ i, Gi i →+ H) {C : ∀ i, Set (Filter (Gi i))}
    (hC : ∀ i, NullFamily (C i)) (i : ι) {F : Filter (Gi i)} (hF : F ∈ C i) :
    Filter.map (f i) F ∈ finalGen f C := by
  refine subset_genFam ?_ ⟨i, F, hF, rfl⟩
  rintro _ ⟨j, F0, hF0, rfl⟩
  exact (hC j).ne F0 hF0 |>.map _

/-- Universal property of the final structure (Theorem 6.4). -/
theorem finalGen_univ (f : ∀ i, Gi i →+ H) {C : ∀ i, Set (Filter (Gi i))} (hC : ∀ i, NullFamily (C i))
    {K : Type*} [AddCommGroup K] {CK : Set (Filter K)} (hCK : NullFamily CK) (g : H →+ K) :
    (∀ i, ∀ F ∈ C i, Filter.map (g ∘ f i) F ∈ CK) ↔
      ∀ F ∈ finalGen f C, Filter.map g F ∈ CK := by
  constructor
  · intro h
    have hnf : NullFamily (initFam (fun _ : Unit => g) (fun _ => CK)) :=
      initFam_nullFamily _ (fun _ => hCK)
    have hsub : {F | ∃ i, ∃ F0 ∈ C i, F = Filter.map (f i) F0} ⊆ initFam (fun _ : Unit => g) (fun _ => CK) := by
      rintro _ ⟨i, F0, hF0, rfl⟩
      refine ⟨(hC i).ne F0 hF0 |>.map _, fun _ => ?_⟩
      rw [Filter.map_map]
      exact h i F0 hF0
    intro F hF
    exact (genFam_le hnf hsub hF).2 ()
  · intro h i F hF
    have := h _ (map_mem_finalGen f hC i hF)
    rwa [Filter.map_map] at this

end Final

section Topological

variable {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]

/-- The filters converging to `0` in a topological group. -/
def nullTop (T : Type*) [TopologicalSpace T] [Zero T] : Set (Filter T) :=
  {F | F.NeBot ∧ F ≤ 𝓝 0}

theorem nullTop_nullFamily : NullFamily (nullTop T) where
  ne := fun F hF => hF.1
  pure_zero := ⟨inferInstance, pure_le_nhds 0⟩
  finer := fun F hF H' hle hH' => ⟨hH', hle.trans hF.2⟩
  add := by
    rintro F ⟨hFn, hF⟩ H' ⟨hHn, hH⟩
    refine ⟨hFn.map₂ hHn, ?_⟩
    rw [← Filter.map_prod_eq_map₂ (· + ·)]
    have h1 : Tendsto Prod.fst (F ×ˢ H') (𝓝 (0 : T)) := Filter.tendsto_fst.mono_right hF
    have h2 : Tendsto Prod.snd (F ×ˢ H') (𝓝 (0 : T)) := Filter.tendsto_snd.mono_right hH
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  neg := by
    rintro F ⟨hF, hle⟩
    refine ⟨hF.map _, ?_⟩
    have h1 : Tendsto (fun x : T => -x) (𝓝 0) (𝓝 0) := by
      have := (continuous_neg (G := T)).tendsto (0 : T)
      rwa [neg_zero] at this
    exact (Filter.map_mono hle).trans h1
  ultra := by
    rintro F hne hU
    refine ⟨hne, ?_⟩
    rw [Filter.le_iff_ultrafilter]
    intro U hUF
    exact (hU U hUF).2

variable {Q : Type*} [AddCommGroup Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q]

/-- Proposition 6.6: the final structure for a continuous open homomorphism of topological groups is the topological
group of the target. -/
theorem final_of_open_map (π : T →+ Q) (hc : Continuous π) (ho : IsOpenMap π) :
    genFam {F | ∃ F0 ∈ nullTop T, F = Filter.map π F0} = nullTop Q := by
  ext F
  constructor
  · intro hF
    refine genFam_le nullTop_nullFamily ?_ hF
    rintro _ ⟨F0, ⟨hn, hle⟩, rfl⟩
    refine ⟨hn.map _, ?_⟩
    have h1 : Tendsto π (𝓝 (0 : T)) (𝓝 0) := by
      have := hc.tendsto (0 : T)
      rwa [map_zero] at this
    exact (Filter.map_mono hle).trans h1
  · rintro ⟨hne, hle⟩
    refine ⟨hne, fun U hU => ⟨Filter.map π (𝓝 0), SumClosure.gen ⟨𝓝 0, ⟨inferInstance, le_rfl⟩, rfl⟩, ?_⟩⟩
    have h1 : 𝓝 (0 : Q) ≤ Filter.map π (𝓝 (0 : T)) := by
      have := ho.nhds_le (0 : T)
      rwa [map_zero] at this
    exact hU.trans (hle.trans h1)

/-- Proposition 6.6 for a quotient group. -/
theorem final_quotient (N : AddSubgroup T) :
    genFam {F | ∃ F0 ∈ nullTop T, F = Filter.map (QuotientAddGroup.mk' N) F0} = nullTop (T ⧸ N) :=
  final_of_open_map (QuotientAddGroup.mk' N) continuous_quot_mk QuotientAddGroup.isOpenMap_coe

end Topological

end PG
