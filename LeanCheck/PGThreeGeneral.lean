import Mathlib
import LeanCheck.PGThreeNull
import LeanCheck.PGThreeExact
import LeanCheck.PGThreePPoint

/-!
# PGthree: Section 6 on every countably infinite abelian group, and Hausdorffness of the group topology (Lean check)

Scope. Sections 6 and 8 of the third article (`PGthree.tex`). `G` is **any** countably infinite abelian group, `S` a
set of pairwise non-isomorphic selective ultrafilters, and `C = genFam (ultraGen S)`. The only extra hypothesis is
that `C` is Hausdorff, in the equivalent form: every image `m • u` (`u ∈ S`, `m ≠ 0`) is nonprincipal or `pure 0`
(`Sel.genFam_hausdorff_iff`).

* `Img x` : the image `c • u` of the letter `x = (u, c)`; a word is good when its letters are in `S` and no image is
  `pure 0`;
* `null_free_iff_general` : the nonprincipal ultrafilters in `C` are exactly the `pw w` for nonempty good words;
* `pw_injective_general` : `pw w = pw w'` for good words forces the lists of images `c • u` to be equal;
* `only_trivial_general`, `kernel_open_general` : the only neighbourhood filter of a group topology in `C` is `pure 0`,
  continuous homomorphisms from topological groups have open kernels, and the vicinity filter is not in `C` when `S`
  is nonempty;
* `exists_discrete_coreflection_general` : under (S), on every countably infinite abelian group satisfying the
  condition of Theorem 4.4 for `H = G`, a Hausdorff PG with the cofinite vicinity filter at `0`, indiscrete finest
  group topology and no nontrivial null group filter;
* `ppoint_hausdorff` : for countably many P-points whose PG is Hausdorff, the group topology of the modification
  separates points.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

namespace Null

open Sel

attribute [local instance] Ultrafilter.add Ultrafilter.addSemigroup

variable {G : Type} [AddCommGroup G]

/-- The image `c • u` of the letter `(u, c)`. -/
def Img (x : Ultrafilter G × ℤ) : Ultrafilter G := x.1.map (fun z : G => x.2 • z)

/-- A word with letters in `S` none of whose images is `pure 0`. -/
def Good0 (S : Set (Ultrafilter G)) (w : List (Ultrafilter G × ℤ)) : Prop := ∀ x ∈ w, x.1 ∈ S ∧ Img x ≠ pure 0

theorem pw_cons (x : Ultrafilter G × ℤ) (w : List (Ultrafilter G × ℤ)) : pw (x :: w) = Img x + pw w := rfl

/-- Letters with image `pure 0` may be omitted. -/
theorem exists_pw_filter (w : List (Ultrafilter G × ℤ)) :
    ∃ w' : List (Ultrafilter G × ℤ), (∀ x ∈ w', x ∈ w ∧ Img x ≠ pure 0) ∧ pw w' = pw w := by
  induction w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons x w ih =>
    obtain ⟨w', hw', hpw⟩ := ih
    by_cases h : Img x = pure 0
    · refine ⟨w', fun y hy => ⟨List.mem_cons_of_mem _ (hw' y hy).1, (hw' y hy).2⟩, ?_⟩
      rw [pw_cons, h, pure_zero_add, hpw]
    · refine ⟨x :: w', fun y hy => ?_, by rw [pw_cons, pw_cons, hpw]⟩
      rcases List.mem_cons.1 hy with h' | h'
      · rw [h']; exact ⟨List.mem_cons_self .., h⟩
      · exact ⟨List.mem_cons_of_mem _ (hw' y h').1, (hw' y h').2⟩

variable [Countable G] [Infinite G] (S : Set (Ultrafilter G)) (hsel : ∀ u ∈ S, IsSel u)
  (hiso : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ Iso u v)
  (hH : ∀ u ∈ S, ∀ m : ℤ, m ≠ 0 → (∀ a, u.map (fun x : G => m • x) ≠ pure a) ∨ u.map (fun x : G => m • x) = pure 0)

include hH in
theorem img_free (x : Ultrafilter G × ℤ) (hx : x.1 ∈ S) (h0 : Img x ≠ pure 0) : ∀ a, Img x ≠ pure a := by
  by_cases hc : x.2 = 0
  · exact absurd (by unfold Img; rw [hc, map_zero_smul]) h0
  · rcases hH x.1 hx x.2 hc with h | h
    · exact h
    · exact absurd h h0

include hH in
theorem pw_free_general (w : List (Ultrafilter G × ℤ)) (hw : Good0 S w) (hne : w ≠ []) : ∀ a, pw w ≠ pure a := by
  induction w with
  | nil => exact absurd rfl hne
  | cons x w ih =>
    intro a ha
    have hx := hw x (List.mem_cons_self ..)
    have hmem : ({a} : Set G) ∈ pw (x :: w) := by rw [ha]; exact rfl
    rw [mem_pw_cons] at hmem
    rcases eq_or_ne w [] with hw0 | hw0
    · subst hw0
      have h1 : ({a} : Set G) ∈ Img x := by
        show {b : G | x.2 • b ∈ ({a} : Set G)} ∈ x.1
        refine Filter.mem_of_superset hmem (fun b hb => ?_)
        have h2 : (0 : G) ∈ {z : G | x.2 • b + z ∈ ({a} : Set G)} := hb
        simpa using h2
      obtain ⟨y, hy, h2⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h1
      exact img_free S hH x hx.1 hx.2 y h2
    · obtain ⟨b, hb⟩ := Ultrafilter.nonempty_of_mem hmem
      have h1 : {z : G | x.2 • b + z ∈ ({a} : Set G)} ∈ pw w := hb
      refine ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) hw0 (a - x.2 • b) ?_
      have h2 : ({a - x.2 • b} : Set G) ∈ pw w := by
        refine Filter.mem_of_superset h1 (fun z hz => ?_)
        have h3 : x.2 • b + z = a := hz
        rw [mem_singleton_iff, ← h3]; abel
      obtain ⟨y, hy, h4⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h2
      rw [h4, mem_singleton_iff.1 hy]

include hsel hiso hH in
/-- Theorem 6.1, existence, on every countably infinite abelian group. -/
theorem null_free_iff_general (W : Ultrafilter G) :
    ((W : Filter G) ∈ genFam (ultraGen S) ∧ ∀ a, W ≠ pure a) ↔ ∃ w, Good0 S w ∧ w ≠ [] ∧ pw w = W := by
  constructor
  · rintro ⟨hW, hfree⟩
    obtain ⟨w, hw, _, hpw⟩ := exists_word hsel hiso W hW hfree
    obtain ⟨w', hw', hpw'⟩ := exists_pw_filter w
    refine ⟨w', fun x hx => ⟨(hw x (hw' x hx).1).1, (hw' x hx).2⟩, fun h => ?_, hpw'.trans hpw⟩
    rw [h] at hpw'
    exact hfree 0 (by rw [← hpw, ← hpw']; rfl)
  · rintro ⟨w, hw, hne, rfl⟩
    exact ⟨pw_mem S w (fun x hx => (hw x hx).1), pw_free_general S hH w hw hne⟩

include hsel hiso hH in
/-- Theorem 6.1, uniqueness: the images `c • u` of the letters are determined by the ultrafilter. -/
theorem pw_injective_general (w w' : List (Ultrafilter G × ℤ)) (hw : Good0 S w) (hw' : Good0 S w')
    (h : pw w = pw w') : w.map Img = w'.map Img := by
  classical
  obtain ⟨e⟩ : Nonempty (ℕ ≃ G) := by
    have := Encodable.ofCountable G
    have := Denumerable.ofEncodableOfInfinite G
    exact ⟨(Denumerable.eqv G).symm⟩
  set U : Finset (Ultrafilter G) := ((w ++ w').map Prod.fst).toFinset with hU
  have hUS : ∀ u ∈ U, u ∈ S := by
    intro u hu
    rw [hU, List.mem_toFinset, List.mem_map] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    rcases List.mem_append.1 hx with h' | h'
    · exact (hw x h').1
    · exact (hw' x h').1
  have hwU : ∀ x ∈ w, x.1 ∈ U := fun x hx => by
    rw [hU, List.mem_toFinset]
    exact List.mem_map.2 ⟨x, List.mem_append_left _ hx, rfl⟩
  have hw'U : ∀ x ∈ w', x.1 ∈ U := fun x hx => by
    rw [hU, List.mem_toFinset]
    exact List.mem_map.2 ⟨x, List.mem_append_right _ hx, rfl⟩
  let uu : Fin U.card → Ultrafilter G := fun k => (U.equivFin.symm k).1
  have huuS : ∀ k, uu k ∈ S := fun k => hUS _ (U.equivFin.symm k).2
  have huuinj : Function.Injective uu := fun a b hab => U.equivFin.symm.injective (Subtype.ext hab)
  let om : Fin U.card → Ultrafilter ℕ := fun k => (uu k).map e.symm
  have homsel : ∀ k, IsSel (om k) := fun k =>
    isSel_map_of_injective (hsel _ (huuS k)) e.symm e.symm.injective
  have homiso : ∀ k k', k ≠ k' → ¬ Iso (om k) (om k') := by
    rintro k k' hkk' ⟨π, hπ⟩
    refine hiso _ (huuS k) _ (huuS k') (fun h => hkk' (huuinj h)) ⟨(e.symm.trans π).trans e, ?_⟩
    have h2 := congrArg (Ultrafilter.map e) hπ
    simp only [om, Ultrafilter.map_map] at h2
    have h3 : (e : ℕ → G) ∘ (e.symm : G → ℕ) = id := by funext x; simp
    rw [h3, Ultrafilter.map_id] at h2
    exact h2
  set n : ℕ := ((w ++ w').map (fun x => x.2.natAbs)).sum with hn
  have hbound : ∀ x ∈ w ++ w', x.2.natAbs ≤ n := fun x hx =>
    List.le_sum_of_mem (List.mem_map.2 ⟨x, hx, rfl⟩)
  set L : ℕ := w.length + w'.length with hL
  set D : Finset ℤ := Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ)) with hD
  -- members avoiding all short relations whose coefficients do not annihilate their ultrafilters
  have hrel : ∀ m : ℕ, ∀ σ : Fin (m + 1) → Fin U.card, ∀ d : Fin (m + 1) → ℤ,
      (∀ l, Img (uu (σ l), d l) ≠ pure 0) → ∃ B : Fin U.card → Set ℕ, (∀ k, B k ∈ om k) ∧
        ∀ y : Fin (m + 1) → ℕ, StrictMono y → (∀ i, y i ∈ B (σ i)) → ∑ l, d l • e (y l) ≠ 0 := by
    intro m σ d hd
    have hnl : ¬ Large (m + 1) (fun i => om (σ i)) {y : Fin (m + 1) → ℕ | ∑ l, d l • e (y l) = 0} := by
      rw [large_snoc]
      have hempty : {p : Fin m → ℕ | {z : ℕ | (Fin.snoc p z : Fin (m + 1) → ℕ) ∈
          {y : Fin (m + 1) → ℕ | ∑ l, d l • e (y l) = 0}} ∈ om (σ (Fin.last m))} = ∅ := by
        refine eq_empty_of_forall_notMem (fun p hp => ?_)
        have h1 : {z : ℕ | (Fin.snoc p z : Fin (m + 1) → ℕ) ∈
            {y : Fin (m + 1) → ℕ | ∑ l, d l • e (y l) = 0}} ∈ om (σ (Fin.last m)) := hp
        have h2 : ({-∑ l : Fin m, d l.castSucc • e (p l)} : Set G) ∈ Img (uu (σ (Fin.last m)), d (Fin.last m)) := by
          show {x : G | d (Fin.last m) • x ∈ ({-∑ l : Fin m, d l.castSucc • e (p l)} : Set G)} ∈ uu (σ (Fin.last m))
          have h3 : e.symm ⁻¹' {z : ℕ | (Fin.snoc p z : Fin (m + 1) → ℕ) ∈
              {y : Fin (m + 1) → ℕ | ∑ l, d l • e (y l) = 0}} ∈ uu (σ (Fin.last m)) := h1
          refine Filter.mem_of_superset h3 (fun x hx => ?_)
          have h4 : ∑ l, d l • e ((Fin.snoc p (e.symm x) : Fin (m + 1) → ℕ) l) = 0 := hx
          rw [Fin.sum_univ_castSucc] at h4
          simp only [Fin.snoc_castSucc, Fin.snoc_last, Equiv.apply_symm_apply] at h4
          show d (Fin.last m) • x = -∑ l : Fin m, d l.castSucc • e (p l)
          exact eq_neg_of_add_eq_zero_right h4
        obtain ⟨a, _, h5⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h2
        exact img_free S hH _ (huuS _) (hd (Fin.last m)) a h5
      rw [hempty]
      exact not_large_empty m _
    exact tuples om homsel homiso (m + 1) σ _ hnl
  have hrel' : ∀ k : Fin U.card, ∃ C ∈ om k, ∀ m < L, ∀ σ : Fin (m + 1) → Fin U.card, ∀ d : Fin (m + 1) → ℤ,
      (∀ l, d l ∈ D) → ∀ hd : (∀ l, Img (uu (σ l), d l) ≠ pure 0), C ⊆ Classical.choose (hrel m σ d hd) k := by
    intro k
    have h1 : ∀ m : ℕ, (⋂ σ ∈ (Finset.univ : Finset (Fin (m + 1) → Fin U.card)),
        ⋂ d ∈ Fintype.piFinset (fun _ : Fin (m + 1) => D),
          (if hd : (∀ l, Img (uu (σ l), d l) ≠ pure 0) then Classical.choose (hrel m σ d hd) k else univ))
        ∈ (om k : Filter ℕ) := by
      intro m
      refine (Filter.biInter_finset_mem _).2 (fun σ _ => (Filter.biInter_finset_mem _).2 (fun d _ => ?_))
      split_ifs with hd
      · exact (Classical.choose_spec (hrel m σ d hd)).1 k
      · exact Filter.univ_mem
    refine ⟨_, (Filter.biInter_finset_mem (Finset.range L)).2 (fun m _ => h1 m), ?_⟩
    intro m hm σ d hdD hd x hx
    have h2 := mem_iInter₂.1 hx m (Finset.mem_range.2 hm)
    have h3 := mem_iInter₂.1 (mem_iInter₂.1 h2 σ (Finset.mem_univ σ)) d (Fintype.mem_piFinset.2 hdD)
    rw [dif_pos hd] at h3
    exact h3
  choose C1 hC1mem hC1 using hrel'
  have hdisj : ∃ C2 : Fin U.card → Set ℕ, (∀ k, C2 k ∈ om k) ∧ ∀ k k', ∀ x ∈ C2 k, x ∈ C2 k' → k = k' := by
    have h1 : ∀ k k' : Fin U.card, ∃ A : Set ℕ, A ∈ om k ∧ (k ≠ k' → Aᶜ ∈ om k') := by
      intro k k'
      by_cases hkk : k = k'
      · exact ⟨univ, Filter.univ_mem, fun h => absurd hkk h⟩
      have hne : om k ≠ om k' := fun h => homiso k k' hkk (h ▸ ⟨Equiv.refl ℕ, by
        rw [show ((Equiv.refl ℕ : Equiv.Perm ℕ) : ℕ → ℕ) = id from rfl, Ultrafilter.map_id]⟩)
      have : ∃ A, A ∈ om k ∧ A ∉ om k' := by
        by_contra h
        refine hne (Ultrafilter.coe_le_coe.1 (fun A hA => ?_)).symm
        by_contra hn'
        exact h ⟨A, hA, hn'⟩
      obtain ⟨A, hA, hA'⟩ := this
      exact ⟨A, hA, fun _ => Ultrafilter.compl_mem_iff_notMem.2 hA'⟩
    choose A hA hAc using h1
    refine ⟨fun k => ⋂ k' ∈ (Finset.univ : Finset (Fin U.card)), (A k k' ∩ if k = k' then univ else (A k' k)ᶜ),
      fun k => ?_, fun k k' x hx hx' => ?_⟩
    · refine (Filter.biInter_finset_mem _).2 (fun k' _ => Filter.inter_mem (hA k k') ?_)
      split_ifs with h
      · exact Filter.univ_mem
      · exact hAc k' k (Ne.symm h)
    · by_contra hne
      have h2 := (mem_iInter₂.1 hx k' (Finset.mem_univ _)).2
      rw [if_neg hne] at h2
      exact h2 (mem_iInter₂.1 hx' k (Finset.mem_univ _)).1
  obtain ⟨C2, hC2mem, hC2⟩ := hdisj
  -- coefficients that annihilate an ultrafilter annihilate a member of it
  let Z : Fin U.card → Set ℕ := fun k => {y | ∀ d ∈ D, Img (uu k, d) = pure 0 → d • e y = 0}
  have hZmem : ∀ k, Z k ∈ om k := by
    intro k
    have h1 : (⋂ d ∈ D, {y : ℕ | Img (uu k, d) = pure 0 → d • e y = 0}) ∈ (om k : Filter ℕ) := by
      refine (Filter.biInter_finset_mem D).2 (fun d _ => ?_)
      by_cases hd : Img (uu k, d) = pure 0
      · have h2 : ({0} : Set G) ∈ Img (uu k, d) := by rw [hd]; exact rfl
        have h3 : {x : G | d • x ∈ ({0} : Set G)} ∈ uu k := h2
        show e.symm ⁻¹' {y : ℕ | Img (uu k, d) = pure 0 → d • e y = 0} ∈ uu k
        refine Filter.mem_of_superset h3 (fun x hx => ?_)
        intro _
        show d • e (e.symm x) = 0
        rw [Equiv.apply_symm_apply]; exact hx
      · exact Filter.mem_of_superset Filter.univ_mem (fun y _ h => absurd h hd)
    exact Filter.mem_of_superset h1 (fun y hy d hd => mem_iInter₂.1 hy d hd)
  let C : Fin U.card → Set ℕ := fun k => C1 k ∩ C2 k ∩ Z k
  have hCmem : ∀ k, C k ∈ om k := fun k => Filter.inter_mem (Filter.inter_mem (hC1mem k) (hC2mem k)) (hZmem k)
  let ix : (x : Ultrafilter G) → x ∈ U → Fin U.card := fun x hx => U.equivFin ⟨x, hx⟩
  have huix : ∀ x (hx : x ∈ U), uu (ix x hx) = x := by
    intro x hx
    show (U.equivFin.symm (U.equivFin ⟨x, hx⟩)).1 = x
    rw [Equiv.symm_apply_apply]
  let κ : Fin w.length → Fin U.card := fun i => ix (w.get i).1 (hwU _ (List.get_mem _ _))
  let κ' : Fin w'.length → Fin U.card := fun i => ix (w'.get i).1 (hw'U _ (List.get_mem _ _))
  have huκ : ∀ i, uu (κ i) = (w.get i).1 := fun i => huix _ _
  have huκ' : ∀ i, uu (κ' i) = (w'.get i).1 := fun i => huix _ _
  let cf : Fin w.length → ℤ := fun i => (w.get i).2
  let cf' : Fin w'.length → ℤ := fun i => (w'.get i).2
  let E : Set G := {x | ∃ z : Fin w.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (κ i)) ∧ ∑ i, cf i • e (z i) = x}
  let E' : Set G := {x | ∃ z : Fin w'.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (κ' i)) ∧ ∑ i, cf' i • e (z i) = x}
  have hmemE : ∀ (v : List (Ultrafilter G × ℤ)) (kk : Fin v.length → Fin U.card),
      (∀ i, uu (kk i) = (v.get i).1) →
      {x : G | ∃ z : Fin v.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (kk i)) ∧ ∑ i, (v.get i).2 • e (z i) = x}
        ∈ pw v := by
    intro v kk hkk
    have h1 : List.ofFn (fun i => ((v.get i).1, (v.get i).2)) = v := by
      exact List.ofFn_get v
    have h2 := mem_pw_ofFn e v.length (fun i => (v.get i).1) (fun i => (v.get i).2)
      {x : G | ∃ z : Fin v.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (kk i)) ∧ ∑ i, (v.get i).2 • e (z i) = x}
    rw [h1] at h2
    rw [h2]
    have h3 : (fun i => ((v.get i).1).map e.symm) = fun i => om (kk i) := by
      funext i
      show ((v.get i).1).map e.symm = (uu (kk i)).map e.symm
      rw [hkk i]
    rw [h3]
    refine large_mono _ _ (fun y hy => ?_)
      (large_inc v.length (fun i => om (kk i)) (fun i => (homsel (kk i)).1) (fun i => C (kk i))
        (fun i => hCmem (kk i)) 0)
    exact ⟨y, hy.1, hy.2.1, rfl⟩
  have hE : E ∈ pw w := hmemE w κ huκ
  have hE' : E' ∈ pw w' := hmemE w' κ' huκ'
  rw [← h] at hE'
  obtain ⟨x, hxE, hxE'⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (pw w : Filter G)) hE hE')
  obtain ⟨z, hzm, hzC, hzx⟩ := hxE
  obtain ⟨z', hzm', hzC', hzx'⟩ := hxE'
  set Y : Finset ℕ := Finset.univ.image z ∪ Finset.univ.image z' with hY
  let d : ℕ → ℤ := fun y => (∑ i ∈ Finset.univ.filter (fun i => z i = y), cf i)
    - ∑ i ∈ Finset.univ.filter (fun i => z' i = y), cf' i
  have hsingle : ∀ i, Finset.univ.filter (fun j => z j = z i) = {i} := by
    intro i
    ext j
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => hzm.injective h.2, fun h => ⟨Finset.mem_univ _, by rw [h]⟩⟩
  have hsingle' : ∀ i, Finset.univ.filter (fun j => z' j = z' i) = {i} := by
    intro i
    ext j
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => hzm'.injective h.2, fun h => ⟨Finset.mem_univ _, by rw [h]⟩⟩
  have hsum : ∑ y ∈ Y, d y • e y = 0 := by
    have key : ∀ (m : ℕ) (zz : Fin m → ℕ) (cc : Fin m → ℤ), (∀ i, zz i ∈ Y) →
        ∑ y ∈ Y, (∑ i ∈ Finset.univ.filter (fun i => zz i = y), cc i) • e y = ∑ i, cc i • e (zz i) := by
      intro m zz cc hmem
      rw [← Finset.sum_fiberwise_of_maps_to (fun i (_ : i ∈ Finset.univ) => hmem i) (fun i => cc i • e (zz i))]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [(Finset.mem_filter.1 hi).2]
    have h1 := key _ z cf (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem z (Finset.mem_univ i)))
    have h2 := key _ z' cf' (fun i => Finset.mem_union_right _ (Finset.mem_image_of_mem z' (Finset.mem_univ i)))
    simp only [d, sub_smul]
    rw [Finset.sum_sub_distrib, h1, h2, hzx, hzx', sub_self]
  have hdsmall : ∀ y, d y ∈ D := by
    intro y
    have one : ∀ (v : List (Ultrafilter G × ℤ)), (∀ x ∈ v, x ∈ w ++ w') → ∀ (zz : Fin v.length → ℕ),
        Function.Injective zz → |∑ i ∈ Finset.univ.filter (fun i => zz i = y), (v.get i).2| ≤ (n : ℤ) := by
      intro v hv zz hzz
      by_cases hne : (Finset.univ.filter (fun i => zz i = y)).Nonempty
      · obtain ⟨i, hi⟩ := hne
        have h1 : Finset.univ.filter (fun i => zz i = y) = {i} := by
          ext j
          rw [Finset.mem_filter, Finset.mem_singleton]
          refine ⟨fun h => hzz (h.2.trans (Finset.mem_filter.1 hi).2.symm), fun h => ?_⟩
          rw [h]; exact Finset.mem_filter.1 hi
        rw [h1, Finset.sum_singleton]
        have h2 := hbound _ (hv _ (List.get_mem v i))
        rw [Int.abs_eq_natAbs]
        exact_mod_cast h2
      · rw [Finset.not_nonempty_iff_eq_empty.1 hne]
        simp
    have h4 : |∑ i ∈ Finset.univ.filter (fun i => z i = y), cf i| ≤ (n : ℤ) :=
      one w (fun x hx => List.mem_append_left _ hx) z hzm.injective
    have h5 : |∑ i ∈ Finset.univ.filter (fun i => z' i = y), cf' i| ≤ (n : ℤ) :=
      one w' (fun x hx => List.mem_append_right _ hx) z' hzm'.injective
    have h6 := abs_le.1 h4
    have h7 := abs_le.1 h5
    refine Finset.mem_Icc.2 ?_
    show -(2 * (n : ℤ)) ≤ (∑ i ∈ Finset.univ.filter (fun i => z i = y), cf i)
        - (∑ i ∈ Finset.univ.filter (fun i => z' i = y), cf' i) ∧
      (∑ i ∈ Finset.univ.filter (fun i => z i = y), cf i)
        - (∑ i ∈ Finset.univ.filter (fun i => z' i = y), cf' i) ≤ 2 * (n : ℤ)
    omega
  have hty : ∀ y ∈ Y, ∃ k, y ∈ C k := by
    intro y hy
    rcases Finset.mem_union.1 hy with h2 | h2
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h2
      exact ⟨κ i, hi ▸ hzC i⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h2
      exact ⟨κ' i, hi ▸ hzC' i⟩
  -- every collected coefficient annihilates the ultrafilter of its point
  have hdzero : ∀ y ∈ Y, ∀ k, y ∈ C k → Img (uu k, d y) = pure 0 := by
    by_contra hcon
    set T : Finset ℕ := Y.filter (fun y => ∃ k, y ∈ C k ∧ Img (uu k, d y) ≠ pure 0) with hT
    have hTne : T.Nonempty := by
      by_contra he
      refine hcon (fun y hy k hk => ?_)
      by_contra h'
      exact he ⟨y, Finset.mem_filter.2 ⟨hy, k, hk, h'⟩⟩
    obtain ⟨m, hm⟩ : ∃ m, T.card = m + 1 := ⟨T.card - 1, by have := hTne.card_pos; omega⟩
    have hmL : m < L := by
      have h1 : T.card ≤ Y.card := Finset.card_filter_le _ _
      have h2 : Y.card ≤ L := by
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
        · exact Finset.card_image_le.trans (by simp)
        · exact Finset.card_image_le.trans (by simp)
      omega
    let t : Fin (m + 1) → ℕ := fun l => T.orderEmbOfFin hm l
    have htmem : ∀ l, t l ∈ T := fun l => Finset.orderEmbOfFin_mem _ _ _
    have htm : StrictMono t := (T.orderEmbOfFin hm).strictMono
    have hσ : ∀ l, ∃ k, t l ∈ C k ∧ Img (uu k, d (t l)) ≠ pure 0 := fun l => (Finset.mem_filter.1 (htmem l)).2
    choose σ hσC hσne using hσ
    let dd : Fin (m + 1) → ℤ := fun l => d (t l)
    have hddD : ∀ l, dd l ∈ D := fun l => hdsmall _
    have hdd : ∀ l, Img (uu (σ l), dd l) ≠ pure 0 := hσne
    have hsub : ∀ l, t l ∈ Classical.choose (hrel m σ dd hdd) (σ l) := fun l =>
      hC1 (σ l) m hmL σ dd hddD hdd (hσC l).1.1
    refine (Classical.choose_spec (hrel m σ dd hdd)).2 t htm hsub ?_
    have himg : Finset.univ.image t = T := T.image_orderEmbOfFin_univ hm
    have h1 : ∑ l, dd l • e (t l) = ∑ y ∈ T, d y • e y := by
      rw [← himg, Finset.sum_image (fun a _ b _ hab => htm.injective hab)]
    rw [h1]
    have h2 : ∑ y ∈ T, d y • e y = ∑ y ∈ Y, d y • e y := by
      refine Finset.sum_filter_of_ne (fun y hy hne => ?_)
      obtain ⟨k, hk⟩ := hty y hy
      refine ⟨k, hk, fun h0 => hne ?_⟩
      exact hk.2 (d y) (hdsmall y) h0
    rw [h2, hsum]
  have hcf : ∀ i, Img (uu (κ i), cf i) ≠ pure 0 := by
    intro i
    rw [huκ i]
    exact (hw _ (List.get_mem w i)).2
  have hcf' : ∀ i, Img (uu (κ' i), cf' i) ≠ pure 0 := by
    intro i
    rw [huκ' i]
    exact (hw' _ (List.get_mem w' i)).2
  -- coefficients that differ by an annihilating one give the same image
  have hsame : ∀ (v : Ultrafilter G) (a b : ℤ), Img (v, a - b) = pure 0 → Img (v, a) = Img (v, b) := by
    intro v a b hab
    have h1 : ({0} : Set G) ∈ Img (v, a - b) := by rw [hab]; exact rfl
    have h2 : {x : G | (a - b) • x ∈ ({0} : Set G)} ∈ v := h1
    have h3 : (fun x : G => a • x) =ᶠ[(v : Filter G)] fun x => b • x := by
      refine Filter.mem_of_superset h2 (fun x hx => ?_)
      have h4 : (a - b) • x = 0 := hx
      rw [sub_smul, sub_eq_zero] at h4
      exact h4
    refine Ultrafilter.coe_injective ?_
    show Filter.map (fun x : G => a • x) (v : Filter G) = Filter.map (fun x : G => b • x) (v : Filter G)
    exact Filter.map_congr h3
  have hmatch : ∀ i, ∃ j, z' j = z i ∧ Img (w.get i) = Img (w'.get j) := by
    intro i
    have h1 := hdzero (z i) (Finset.mem_union_left _ (Finset.mem_image_of_mem z (Finset.mem_univ i)))
      (κ i) (hzC i)
    have h3 : d (z i) = cf i - ∑ j ∈ Finset.univ.filter (fun j => z' j = z i), cf' j := by
      show (∑ j ∈ Finset.univ.filter (fun j => z j = z i), cf j) - _ = _
      rw [hsingle, Finset.sum_singleton]
    by_cases hex : ∃ j, z' j = z i
    · obtain ⟨j, hj⟩ := hex
      have h4 : d (z i) = cf i - cf' j := by rw [h3, ← hj, hsingle', Finset.sum_singleton]
      have hκ : κ' j = κ i := by
        have h5 := (hzC' j).1.2
        rw [hj] at h5
        exact hC2 _ _ _ h5 (hzC i).1.2
      refine ⟨j, hj, ?_⟩
      have h6 : (w'.get j).1 = (w.get i).1 := by rw [← huκ' j, hκ, huκ i]
      rw [h4, huκ i] at h1
      have h7 := hsame _ _ _ h1
      show Img ((w.get i).1, cf i) = Img ((w'.get j).1, cf' j)
      rw [h6]; exact h7
    · have h4 : Finset.univ.filter (fun j => z' j = z i) = ∅ :=
        Finset.filter_eq_empty_iff.2 (fun j _ h => hex ⟨j, h⟩)
      rw [h3, h4, Finset.sum_empty, sub_zero] at h1
      exact absurd h1 (hcf i)
  have hmatch' : ∀ j, ∃ i, z i = z' j := by
    intro j
    have h1 := hdzero (z' j) (Finset.mem_union_right _ (Finset.mem_image_of_mem z' (Finset.mem_univ j)))
      (κ' j) (hzC' j)
    by_contra hex
    have h4 : Finset.univ.filter (fun i => z i = z' j) = ∅ :=
      Finset.filter_eq_empty_iff.2 (fun i _ h => hex ⟨i, h⟩)
    have h3 : d (z' j) = -cf' j := by
      show (∑ i ∈ Finset.univ.filter (fun i => z i = z' j), cf i)
        - (∑ i ∈ Finset.univ.filter (fun i => z' i = z' j), cf' i) = _
      rw [h4, hsingle', Finset.sum_empty, Finset.sum_singleton, zero_sub]
    rw [h3] at h1
    have h5 := hsame (uu (κ' j)) 0 (cf' j) (by rwa [zero_sub])
    have h6 : Img (uu (κ' j), (0 : ℤ)) = pure 0 := map_zero_smul _
    exact hcf' j (h5.symm.trans h6)
  have himg : Finset.univ.image z = Finset.univ.image z' := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨j, hj, _⟩ := hmatch i
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
    · intro hy
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨i, hi⟩ := hmatch' j
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hlen : w.length = w'.length := by
    have h1 := congrArg Finset.card himg
    rw [Finset.card_image_of_injective _ hzm.injective, Finset.card_image_of_injective _ hzm'.injective] at h1
    simpa using h1
  have hzz : ∀ i : Fin w.length, z i = z' (Fin.cast hlen i) := by
    have h1 : z = fun i => z' (Fin.cast hlen i) := by
      have hc : (Finset.univ.image z).card = w.length := by
        rw [Finset.card_image_of_injective _ hzm.injective]; simp
      have h2 := Finset.orderEmbOfFin_unique hc (f := z)
        (fun i => Finset.mem_image_of_mem z (Finset.mem_univ i)) hzm
      have h3 := Finset.orderEmbOfFin_unique hc (f := fun i => z' (Fin.cast hlen i))
        (fun i => by rw [himg]; exact Finset.mem_image_of_mem z' (Finset.mem_univ _))
        (fun a b hab => hzm' (by simpa using hab))
      rw [h2, h3]
    exact fun i => congrFun h1 i
  refine List.ext_get (by simp [hlen]) (fun i h1 h2 => ?_)
  have h1' : i < w.length := by simpa using h1
  have h2' : i < w'.length := by simpa using h2
  have hzi := hzz ⟨i, h1'⟩
  obtain ⟨j, hj, hImg⟩ := hmatch ⟨i, h1'⟩
  have hj' : j = ⟨i, h2'⟩ := hzm'.injective (hj.trans hzi)
  rw [hj'] at hImg
  simpa using hImg

include hsel hiso hH in
/-- Theorem 6.2 on every countably infinite abelian group. -/
theorem only_trivial_general :
    (∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen S) → N = pure 0) ∧
      (S.Nonempty → vic (genFam (ultraGen S)) ∉ genFam (ultraGen S)) := by
  classical
  set C := genFam (ultraGen S) with hCdef
  have hC : NullFamily C := genFam_nullFamily _
  have hhaus := genFam_hausdorff_general S hsel hiso hH
  have main : ∀ N : Filter G, IsNbhdFilter N → N ∈ C → N = pure 0 := by
    intro N hN hNC
    by_contra hne0
    have h0N : pure 0 ≤ N := fun s hs => Filter.mem_pure.2 (hN.zero_mem s hs)
    set X : Set (Ultrafilter G) := {U | (U : Filter G) ≤ N ∧ ∀ a, U ≠ pure a} with hX
    have hXne : X.Nonempty := by
      by_contra h
      refine hne0 (le_antisymm ?_ h0N)
      refine Filter.le_iff_ultrafilter.2 (fun U hU => ?_)
      have : ∃ a, U = pure a := by
        by_contra h'
        exact h ⟨U, hU, fun a ha => h' ⟨a, ha⟩⟩
      obtain ⟨a, ha⟩ := this
      have h1 : (pure a : Filter G) ∈ C := by
        have h2 : (U : Filter G) ∈ C := hC.finer _ hNC _ hU U.neBot
        rwa [ha, Ultrafilter.coe_pure] at h2
      have h3 := hhaus a h1
      rw [ha, h3, Ultrafilter.coe_pure]
    have hXclosed : IsClosed X := by
      have h1 : X = (⋂ s ∈ N, {U : Ultrafilter G | s ∈ U}) ∩ ⋂ a : G, {U : Ultrafilter G | ({a}ᶜ : Set G) ∈ U} := by
        ext U
        rw [mem_inter_iff, mem_iInter₂, mem_iInter]
        refine and_congr Iff.rfl (forall_congr' (fun a => ?_))
        show U ≠ pure a ↔ ({a}ᶜ : Set G) ∈ U
        rw [Ultrafilter.compl_mem_iff_notMem]
        refine not_congr ⟨fun h => by rw [h]; exact rfl, fun h => ?_⟩
        obtain ⟨b, hb, hU⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton a) h
        rw [hU, mem_singleton_iff.1 hb]
      rw [h1]
      exact (isClosed_biInter (fun s _ => ultrafilter_isClosed_basic s)).inter
        (isClosed_iInter (fun a => ultrafilter_isClosed_basic _))
    have hword : ∀ U ∈ X, ∃ w, Good0 S w ∧ w ≠ [] ∧ pw w = U := fun U hU =>
      (null_free_iff_general S hsel hiso hH U).1 ⟨hC.finer _ hNC _ hU.1 U.neBot, hU.2⟩
    have hgood : ∀ w w' : List (Ultrafilter G × ℤ), Good0 S w → Good0 S w' → Good0 S (w ++ w') := by
      intro w w' h h' x hx
      rcases List.mem_append.1 hx with h1 | h1
      · exact h x h1
      · exact h' x h1
    have hXadd : ∀ V ∈ X, ∀ V' ∈ X, V + V' ∈ X := by
      intro V hV V' hV'
      refine ⟨fun s hs => ?_, ?_⟩
      · obtain ⟨B, hB, hBs⟩ := hN.halve s hs
        show s ∈ V + V'
        rw [mem_add]
        refine Filter.mem_of_superset (hV.1 hB) (fun m hm => ?_)
        exact Filter.mem_of_superset (hV'.1 hB) (fun z hz => hBs m hm z hz)
      · obtain ⟨w, hw, hwne, hpw⟩ := hword V hV
        obtain ⟨w', hw', _, hpw'⟩ := hword V' hV'
        have h1 : pw (w ++ w') = V + V' := by rw [pw_append, hpw, hpw']
        rw [← h1]
        exact pw_free_general S hH _ (hgood w w' hw hw') (fun h => hwne (List.append_eq_nil_iff.1 h).1)
    obtain ⟨p, hpX, hpp⟩ := exists_idempotent_in_compact_add_subsemigroup
      (M := Ultrafilter G) Ultrafilter.continuous_add_left X hXne hXclosed.isCompact hXadd
    obtain ⟨w, hw, hwne, hpw⟩ := hword p hpX
    have h1 : pw (w ++ w) = pw w := by rw [pw_append, hpw, hpp]
    have h2 := congrArg List.length (pw_injective_general S hsel hiso hH _ _ (hgood w w hw hw) hw h1)
    rw [List.length_map, List.length_map, List.length_append] at h2
    have h3 := List.length_pos_iff.2 hwne
    omega
  refine ⟨main, fun hne hvic => ?_⟩
  obtain ⟨u, hu⟩ := hne
  have hV : IsNbhdFilter (vic C) := by
    refine ⟨fun A hA => vic_zero_mem hC hA, fun A hA => vic_neg hC hA, fun A hA => ?_⟩
    have h1 : Filter.map₂ (· + ·) (vic C) (vic C) ≤ vic C := le_vic (hC.add _ hvic _ hvic)
    obtain ⟨B1, hB1, B2, hB2, h2⟩ := Filter.mem_map₂_iff.1 (h1 hA)
    exact ⟨B1 ∩ B2, Filter.inter_mem hB1 hB2, fun x hx y hy => h2 (mem_image2_of_mem hx.1 hy.2)⟩
  have h0 := main _ hV hvic
  have huC : (u : Filter G) ∈ C := subset_genFam (gen_ne S) ⟨u, hu, rfl⟩
  have h1 : (u : Filter G) ≤ pure 0 := h0 ▸ le_vic huC
  have h2 : ({0} : Set G) ∈ u := h1 (Filter.mem_pure.2 rfl)
  exact notMem_of_finite (hsel u hu).1 (finite_singleton 0) h2

include hsel hiso hH in
/-- Theorem 6.2: continuous homomorphisms from topological groups have open kernels. -/
theorem kernel_open_general {T : Type} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] (f : T →+ G)
    (hf : XiCont (genFam (ultraGen S)) f) : ∃ U ∈ 𝓝 (0 : T), ∀ x ∈ U, f x = 0 :=
  kernel_open_of_trivial (genFam_nullFamily _) (only_trivial_general S hsel hiso hH).1 f hf

/-- Corollary 6.3 on every countably infinite abelian group whose equations `m • x = 0` have finitely many solutions
or hold everywhere. -/
theorem exists_discrete_coreflection_general
    (hE : ∀ m : ℕ, 0 < m → {x : G | m • x = 0}.Finite ∨ ∀ x : G, m • x = 0) (hS : Supply) :
    ∃ C : Set (Filter G), NullFamily C ∧ (∀ g : G, (pure g : Filter G) ∈ C → g = 0) ∧
      (∀ s : Set G, s ∈ vic C ↔ (0 : G) ∈ s ∧ sᶜ.Finite) ∧ halveFilter (vic C) = ⊤ ∧
        ∀ N : Filter G, IsNbhdFilter N → N ∈ C → N = pure 0 := by
  classical
  obtain ⟨e⟩ : Nonempty (ℕ ≃ G) := by
    have := Encodable.ofCountable G
    have := Denumerable.ofEncodableOfInfinite G
    exact ⟨(Denumerable.eqv G).symm⟩
  obtain ⟨S0, hsel0, hiso0, _, hdense0⟩ := (dense_iff_supply univ infinite_univ).2 hS
  set S : Set (Ultrafilter G) := (fun u : Ultrafilter ℕ => u.map e) '' S0 with hSdef
  have hback : ∀ u : Ultrafilter ℕ, (u.map e).map e.symm = u := by
    intro u
    rw [Ultrafilter.map_map]
    have : (e.symm : G → ℕ) ∘ (e : ℕ → G) = id := by funext x; simp
    rw [this, Ultrafilter.map_id]
  have hselS : ∀ v ∈ S, IsSel v := by
    rintro _ ⟨u, hu, rfl⟩
    exact isSel_map_of_injective (hsel0 u hu) e e.injective
  have hisoS : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬ Iso v w := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne ⟨π, hπ⟩
    have hab : a ≠ b := fun h => hne (by rw [h])
    refine hiso0 a ha b hb hab ⟨(e.trans π).trans e.symm, ?_⟩
    have h1 : ((a.map e).map π).map e.symm = b := by
      have hπ' : (a.map e).map π = b.map e := hπ
      rw [hπ', hback]
    rw [Ultrafilter.map_map, Ultrafilter.map_map] at h1
    exact h1
  have hHS : ∀ v ∈ S, ∀ m : ℤ, m ≠ 0 →
      (∀ a, v.map (fun x : G => m • x) ≠ pure a) ∨ v.map (fun x : G => m • x) = pure 0 := by
    intro v hv m hm
    have habs : ∀ x : G, m • x = 0 ↔ m.natAbs • x = 0 := by
      intro x
      rcases Int.natAbs_eq m with h | h
      · conv_lhs => rw [h, natCast_zsmul]
      · conv_lhs => rw [h, neg_smul, neg_eq_zero, natCast_zsmul]
    rcases hE m.natAbs (Int.natAbs_pos.2 hm) with hfin | hzero
    · left
      intro a ha
      have h1 : {x : G | m • x = a} ∈ v := by
        have h2 : ({a} : Set G) ∈ v.map (fun x : G => m • x) := by rw [ha]; exact rfl
        exact h2
      obtain ⟨x0, hx0⟩ := Ultrafilter.nonempty_of_mem h1
      have hf : {x : G | m • x = a}.Finite := by
        refine (hfin.image (fun k => x0 + k)).subset (fun x hx => ?_)
        refine ⟨x - x0, ?_, by abel⟩
        refine (habs _).1 ?_
        have h3 : m • x = a := hx
        have h4 : m • x0 = a := hx0
        rw [smul_sub, h3, h4, sub_self]
      exact notMem_of_finite (hselS v hv).1 hf h1
    · right
      have : (fun x : G => m • x) = fun _ => (0 : G) := by
        funext x; exact (habs x).2 (hzero x)
      rw [this]
      refine Ultrafilter.coe_injective ?_
      rw [Ultrafilter.coe_map, Ultrafilter.coe_pure]
      exact Filter.map_const
  have hhaus := genFam_hausdorff_general S hselS hisoS hHS
  have hC : NullFamily (genFam (ultraGen S)) := genFam_nullFamily _
  have hvic : ∀ s : Set G, s ∈ vic (genFam (ultraGen S)) ↔ (0 : G) ∈ s ∧ sᶜ.Finite := by
    intro s
    have h1 := mem_vic_iff_of_dense S (⊤ : AddSubgroup G) (fun u hu => (hselS u hu).1)
      (fun u _ => by rw [AddSubgroup.coe_top]; exact Filter.univ_mem)
      (fun A _ hAinf => by
        obtain ⟨u, hu, hAu⟩ := hdense0 (e ⁻¹' A) (subset_univ _)
          (hAinf.preimage (by rw [e.range_eq_univ]; exact subset_univ _))
        exact ⟨_, ⟨u, hu, rfl⟩, hAu⟩) hhaus s
    rw [h1, AddSubgroup.coe_top, ← compl_eq_univ_diff]
  refine ⟨_, hC, hhaus, hvic, ?_, (only_trivial_general S hselS hisoS hHS).1⟩
  have hN : IsNbhdFilter (halveFilter (vic (genFam (ultraGen S)))) :=
    isNbhdFilter_halveFilter (fun A hA => vic_zero_mem hC hA) (fun A hA => vic_neg hC hA)
  rw [eq_top_iff]
  intro A hA
  rw [Filter.mem_top]
  obtain ⟨B, hB, hBA⟩ := hN.halve A hA
  have hBV : B ∈ vic (genFam (ultraGen S)) := le_halveFilter _ hB
  have hBfin := ((hvic B).1 hBV).2
  rw [eq_univ_iff_forall]
  intro x
  have h1 : (Bᶜ ∪ (fun y => x - y) ⁻¹' Bᶜ).Finite :=
    hBfin.union (hBfin.preimage (fun a _ b _ h => sub_right_injective h))
  obtain ⟨y, hy⟩ := h1.infinite_compl.nonempty
  rw [mem_compl_iff, mem_union, not_or] at hy
  have hyB : y ∈ B := not_not.1 hy.1
  have hxyB : x - y ∈ B := not_not.1 hy.2
  have := hBA y hyB (x - y) hxyB
  rwa [add_sub_cancel] at this

end Null

namespace PPoint

variable {G : Type*} [AddCommGroup G]

/-- In a PG with unique limits every point is closed for the topological modification. -/
theorem isOpenMod_compl_singleton {C : Set (Filter G)} (hC : NullFamily C)
    (hhaus : ∀ g : G, (pure g : Filter G) ∈ C → g = 0) (g : G) : IsOpenMod C ({g}ᶜ) := by
  intro x hx F hne hconv
  by_contra h
  have hle : pure g ≤ F := by
    intro A hA
    refine Filter.mem_pure.2 ?_
    by_contra hg
    exact h (Filter.mem_of_superset hA (fun a ha hag => hg (mem_singleton_iff.1 hag ▸ ha)))
  have h1 : (pure (g - x) : Filter G) ∈ C := by
    have h2 : Filter.map (fun y => y - x) (pure g) ≤ Filter.map (fun y => y - x) F := Filter.map_mono hle
    rw [Filter.map_pure] at h2
    exact hC.finer _ hconv _ h2 inferInstance
  have h3 := hhaus _ h1
  exact hx (mem_singleton_iff.2 (sub_eq_zero.1 h3).symm)

/-- For countably many P-points whose PG has unique limits, the group topology of the modification separates points. -/
theorem ppoint_hausdorff {J : Type*} [Countable J] (e : ℕ ≃ G) (u : J → Ultrafilter G) (hu : ∀ j, IsPPoint (u j))
    (hhaus : ∀ g : G, (pure g : Filter G) ∈ genFam (Sel.ultraGen (range u)) → g = 0) :
    ∃ t : TopologicalSpace G, @IsTopologicalAddGroup G t _ ∧
      (∀ O : Set G, IsOpen[t] O ↔ IsOpenMod (genFam (Sel.ultraGen (range u))) O) ∧
      IsFinest (genFam (Sel.ultraGen (range u))) t ∧ ∀ g : G, g ≠ 0 → ∃ A ∈ @nhds G t 0, g ∉ A := by
  obtain ⟨t, ht, hopen, _, hfin⟩ := ppoint_modification e u hu
  refine ⟨t, ht, hopen, hfin, fun g hg => ⟨{g}ᶜ, ?_, fun h => h rfl⟩⟩
  letI := t
  refine ((hopen _).2 (isOpenMod_compl_singleton (genFam_nullFamily _) hhaus g)).mem_nhds ?_
  exact fun h => hg (mem_singleton_iff.1 h).symm

end PPoint

end PG
