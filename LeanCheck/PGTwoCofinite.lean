import Mathlib
import LeanCheck.PGNullFilters
import LeanCheck.PGTwoLattice
import LeanCheck.PGTwoReflection
import LeanCheck.PGTwoQuotient

/-!
# PGtwo: the cofinite filter at zero as a vicinity filter (Lean check)

Scope. Proposition 6.12 of the second article (`PGtwo.tex`), abstract form. `C` is a null family on an infinite abelian
group `G` whose vicinity filter `vic C` consists of the sets that contain `0` and have a finite complement (hypothesis
`CofinAtZero C`). Nothing is claimed about the existence of such a `C`.

* `hausdorff_of_cofin` (a): the only `g` with `pure g ∈ C` is `0`; `unique_limit_of_cofin`: limits are unique;
* `isOpenMod_iff_of_cofin` (b): a set is open for the topological modification iff it is empty or has a finite complement;
* `nbhd_eq_top_of_cofin` (b): a neighbourhood filter of `0` of a group topology that is coarser than the vicinity filter
  is the trivial filter `⊤`; `halveFilter_eq_top_of_cofin`: in particular the filter of the finest group topology;
* `exists_free_ultra_of_cofin` (c): every infinite set belongs to a nonprincipal ultrafilter in `C`;
* `not_reflect_of_cofin` (d): two ultrafilters in `C` are never images of each other under `x ↦ g - x` with `g ≠ 0`;
* `no_pseudointersection_of_cofin` (e): no member of `C` has an infinite pseudointersection;
  `countablyGenerated_eq_pure_of_cofin`: a countably generated member of `C` is `pure 0`;
  `eventually_eq_of_cofin`: a convergent sequence is eventually equal to its limit.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

variable {G : Type*} [AddCommGroup G]

/-- The vicinity filter of `C` is the cofinite filter at `0`. -/
def CofinAtZero (C : Set (Filter G)) : Prop := ∀ s : Set G, s ∈ vic C ↔ (0 : G) ∈ s ∧ sᶜ.Finite

section Cofin

variable {C : Set (Filter G)} (hC : NullFamily C) (hV : CofinAtZero C)
include hC hV
set_option linter.unusedSectionVars false

/-- (a) The only principal filter in `C` is `pure 0`. -/
theorem hausdorff_of_cofin : ∀ g : G, (pure g : Filter G) ∈ C → g = 0 := by
  intro g hg
  by_contra hne
  have hs : ({g}ᶜ : Set G) ∈ vic C := by
    refine (hV _).2 ⟨?_, ?_⟩
    · intro h
      exact hne (Set.mem_singleton_iff.1 h).symm
    · rw [compl_compl]
      exact Set.finite_singleton g
  have : g ∈ ({g}ᶜ : Set G) := mem_vic.1 hs _ hg
  exact this rfl

/-- (a) Limits are unique. -/
theorem unique_limit_of_cofin : ∀ (F : Filter G) (x y : G), conv C F x → conv C F y → x = y :=
  hausdorff_iff.2 ((hausdorff_iff_principal hC).2 (hausdorff_of_cofin hC hV))

/-- (b) The topological modification is the cofinite topology. -/
theorem isOpenMod_iff_of_cofin (O : Set G) : IsOpenMod C O ↔ O = ∅ ∨ Oᶜ.Finite := by
  constructor
  · intro h
    rcases O.eq_empty_or_nonempty with he | ⟨x, hx⟩
    · exact Or.inl he
    right
    have hs : ((fun y : G => y + x) ⁻¹' O) ∈ vic C := by
      rw [mem_vic]
      intro F0 hF0
      have e : Filter.map (fun y => y - x) (Filter.map (fun y => y + x) F0) = F0 := by
        rw [Filter.map_map]
        have : ((fun y : G => y - x) ∘ fun y => y + x) = id := by funext y; simp
        rw [this, Filter.map_id]
      have hconv : conv C (Filter.map (fun y => y + x) F0) x := by
        unfold conv
        rw [e]; exact hF0
      have hne : F0.NeBot := hC.ne F0 hF0
      exact h x hx _ (hne.map _) hconv
    have hfin := ((hV _).1 hs).2
    refine (hfin.image (fun y => y + x)).subset (fun z hz => ?_)
    refine ⟨z - x, ?_, by simp⟩
    intro hmem
    apply hz
    simpa using hmem
  · rintro (rfl | hfin)
    · intro x hx
      exact absurd hx (Set.notMem_empty x)
    intro x hx F _ hconv
    have hs : ((fun y : G => y + x) ⁻¹' O) ∈ vic C := by
      refine (hV _).2 ⟨by simpa using hx, ?_⟩
      refine (hfin.image (fun z => z - x)).subset (fun y hy => ?_)
      exact ⟨y + x, hy, by simp⟩
    have h1 : ((fun y : G => y + x) ⁻¹' O) ∈ Filter.map (fun y => y - x) F := mem_vic.1 hs _ hconv
    have h2 : (fun y => y - x) ⁻¹' ((fun y : G => y + x) ⁻¹' O) ∈ F := h1
    have e : (fun y => y - x) ⁻¹' ((fun y : G => y + x) ⁻¹' O) = O := by
      ext z; simp
    rwa [e] at h2

/-- (b) A neighbourhood filter of `0` of a group topology below the vicinity filter (as families of sets) is `⊤`. -/
theorem nbhd_eq_top_of_cofin [Infinite G] {N : Filter G} (hN : IsNbhdFilter N) (hle : vic C ≤ N) : N = ⊤ := by
  have huniv : ∀ A ∈ N, A = Set.univ := by
    intro A hA
    obtain ⟨B, hB, hBA⟩ := hN.halve A hA
    have hBfin : Bᶜ.Finite := ((hV B).1 (hle hB)).2
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨w, hw⟩ := (hBfin.union (hBfin.image (fun y => z - y))).exists_notMem
    have hwB : w ∈ B := by
      by_contra h
      exact hw (Or.inl h)
    have hzw : z - w ∈ B := by
      by_contra h
      exact hw (Or.inr ⟨z - w, h, by simp⟩)
    have := hBA w hwB (z - w) hzw
    simpa using this
  refine top_unique (fun A hA => ?_)
  rw [huniv A hA]
  exact Filter.mem_top.2 rfl

/-- (b) The neighbourhood filter of `0` of the finest group topology is `⊤`: that topology is indiscrete. -/
theorem halveFilter_eq_top_of_cofin [Infinite G] : halveFilter (vic C) = ⊤ :=
  nbhd_eq_top_of_cofin hC hV
    (isNbhdFilter_halveFilter (fun _ hA => vic_zero_mem hC hA) (fun _ hA => vic_neg hC hA))
    (le_halveFilter _)

/-- (c) Every infinite set belongs to a nonprincipal ultrafilter in `C`. -/
theorem exists_free_ultra_of_cofin {A : Set G} (hA : A.Infinite) :
    ∃ U : Ultrafilter G, (U : Filter G) ∈ C ∧ A ∈ U ∧ ∀ a : G, U ≠ pure a := by
  have hA' : (A \ {0}).Infinite := hA.sdiff (Set.finite_singleton 0)
  have hs : (A \ {0})ᶜ ∉ vic C := by
    intro h
    have := ((hV _).1 h).2
    rw [compl_compl] at this
    exact hA' this
  rw [mem_vic] at hs
  push Not at hs
  obtain ⟨F, hF, hsF⟩ := hs
  have : F.NeBot := hC.ne F hF
  obtain ⟨U, hUF, hU⟩ := exists_ultra_compl_mem F hsF
  rw [compl_compl] at hU
  have hUC : (U : Filter G) ∈ C := hC.finer F hF _ hUF U.neBot
  refine ⟨U, hUC, Filter.mem_of_superset hU Set.sdiff_subset, ?_⟩
  intro a ha
  subst ha
  have ha0 : a = 0 := hausdorff_of_cofin hC hV a hUC
  have hmem : a ∈ A \ {0} := hU
  exact hmem.2 ha0

/-- (d) An ultrafilter in `C` is never the image of another one under `x ↦ g - x` with `g ≠ 0`. -/
theorem not_reflect_of_cofin {U W : Ultrafilter G} (hU : (U : Filter G) ∈ C) (hW : (W : Filter G) ∈ C)
    {g : G} (hg : g ≠ 0) : W ≠ U.map (fun x => g - x) := by
  intro h
  have hle : (pure g : Filter G) ≤ Filter.map₂ (· + ·) (U : Filter G) (W : Filter G) := by
    intro s hs
    obtain ⟨a, ha, b, hb, hab⟩ := Filter.mem_map₂_iff.1 hs
    have hb' : (fun x => g - x) ⁻¹' b ∈ (U : Filter G) := by
      rw [h] at hb
      exact hb
    obtain ⟨x, hxa, hxb⟩ := Filter.nonempty_of_mem (Filter.inter_mem (f := (U : Filter G)) ha hb')
    exact hab ⟨x, hxa, g - x, hxb, by simp⟩
  have hsum := hC.add _ hU _ hW
  exact hg (hausdorff_of_cofin hC hV g (hC.finer _ hsum _ hle inferInstance))

/-- (e) A member of `C` has no infinite pseudointersection. -/
theorem no_pseudointersection_of_cofin [Infinite G] {F : Filter G} (hF : F ∈ C) {B : Set G} (hB : B.Infinite)
    (hps : ∀ A ∈ F, (B \ A).Finite) : False := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ≠ 0 := by
    obtain ⟨g, hg⟩ := (Set.finite_singleton (0 : G)).exists_notMem
    exact ⟨g, hg⟩
  have hinj : Function.Injective (fun x : G => g - x) := fun a b h => sub_right_injective h
  have hgB : ((fun x : G => g - x) '' B).Infinite := hB.image hinj.injOn
  obtain ⟨U, hUC, hUmem, hfree⟩ := exists_free_ultra_of_cofin hC hV hgB
  have hT : ∀ A ∈ F, (fun x : G => g - x) ⁻¹' A ∈ U := by
    intro A hA
    by_contra h
    have hc : ((fun x : G => g - x) ⁻¹' A)ᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.2 h
    have hfin : (((fun x : G => g - x) '' B) ∩ ((fun x : G => g - x) ⁻¹' A)ᶜ).Finite := by
      refine ((hps A hA).image (fun x : G => g - x)).subset ?_
      rintro y ⟨⟨b, hb, rfl⟩, hy⟩
      refine ⟨b, ⟨hb, fun hbA => hy ?_⟩, rfl⟩
      show g - (g - b) ∈ A
      simpa using hbA
    obtain ⟨a, _, ha⟩ := Ultrafilter.eq_pure_of_finite_mem hfin (Filter.inter_mem (f := (U : Filter G)) hUmem hc)
    exact hfree a ha
  have hle : (pure g : Filter G) ≤ Filter.map₂ (· + ·) F (U : Filter G) := by
    intro s hs
    obtain ⟨a, ha, c, hc, hac⟩ := Filter.mem_map₂_iff.1 hs
    obtain ⟨x, hxc, hxa⟩ := Filter.nonempty_of_mem (Filter.inter_mem (f := (U : Filter G)) hc (hT a ha))
    exact hac ⟨g - x, hxa, x, hxc, by simp⟩
  have hsum := hC.add _ hF _ hUC
  exact hg (hausdorff_of_cofin hC hV g (hC.finer _ hsum _ hle inferInstance))

/-- (e) A countably generated member of `C` is `pure 0`. -/
theorem countablyGenerated_eq_pure_of_cofin [Infinite G] {F : Filter G} (hF : F ∈ C) [F.IsCountablyGenerated] :
    F = pure 0 := by
  classical
  have hne : F.NeBot := hC.ne F hF
  by_cases hfin : ∃ S ∈ F, S.Finite
  · obtain ⟨S, hS, hSfin⟩ := hfin
    have hle : F ≤ pure 0 := by
      rw [Filter.le_iff_ultrafilter]
      intro U hU
      obtain ⟨a, _, ha⟩ := Ultrafilter.eq_pure_of_finite_mem hSfin (hU hS)
      have hUC : (U : Filter G) ∈ C := hC.finer F hF _ hU U.neBot
      rw [ha] at hUC ⊢
      have ha0 : a = 0 := hausdorff_of_cofin hC hV a hUC
      rw [ha0]
      exact le_rfl
    exact (Filter.NeBot.le_pure_iff hne).1 hle
  · exfalso
    push Not at hfin
    obtain ⟨s, hs⟩ := F.exists_antitone_basis
    have hinf : ∀ n, (s n).Infinite := fun n => hfin (s n) (hs.1.mem_of_mem trivial)
    have hch : ∀ (n : ℕ) (t : Finset G), ∃ y, y ∈ s n ∧ y ∉ t := fun n t => (hinf n).exists_notMem_finset t
    choose pick hpick using hch
    let used : ℕ → Finset G := fun n => Nat.rec ∅ (fun k t => insert (pick k t) t) n
    let b : ℕ → G := fun n => pick n (used n)
    have hused_succ : ∀ n, used (n + 1) = insert (b n) (used n) := fun n => rfl
    have hmono : ∀ m n, m < n → b m ∈ used n := by
      intro m n hmn
      induction n with
      | zero => omega
      | succ n ih =>
        rw [hused_succ]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hmn with h | h
        · exact Finset.mem_insert_of_mem (ih h)
        · subst h
          exact Finset.mem_insert_self _ _
    have hbinj : Function.Injective b := by
      intro m n h
      rcases lt_trichotomy m n with hlt | heq | hlt
      · have hmem : b n ∈ used n := by rw [← h]; exact hmono m n hlt
        exact absurd hmem (hpick n (used n)).2
      · exact heq
      · have hmem : b m ∈ used m := by rw [h]; exact hmono n m hlt
        exact absurd hmem (hpick m (used m)).2
    refine no_pseudointersection_of_cofin hC hV hF (Set.infinite_range_of_injective hbinj) (fun A hA => ?_)
    obtain ⟨n, _, hn⟩ := hs.1.mem_iff.1 hA
    refine ((Set.finite_Iio n).image b).subset ?_
    rintro _ ⟨⟨m, rfl⟩, hmA⟩
    refine ⟨m, ?_, rfl⟩
    by_contra hmn
    have hnm : n ≤ m := not_lt.1 hmn
    exact hmA (hn (hs.2 hnm (hpick m (used m)).1))

/-- (e) A sequence converging in the PG is eventually equal to its limit. -/
theorem eventually_eq_of_cofin [Infinite G] (x : ℕ → G) (a : G) (h : conv C (Filter.map x atTop) a) :
    ∀ᶠ n in atTop, x n = a := by
  have hmem : Filter.map (fun n => x n - a) atTop ∈ C := by
    unfold conv at h
    rwa [Filter.map_map] at h
  have := countablyGenerated_eq_pure_of_cofin hC hV hmem
  have h0 : ({0} : Set G) ∈ Filter.map (fun n => x n - a) atTop := by
    rw [this]; exact rfl
  have h1 : ∀ᶠ n in atTop, x n - a ∈ ({0} : Set G) := h0
  exact h1.mono (fun n hn => sub_eq_zero.1 hn)

end Cofin

end PG
