import Mathlib
import LeanCheck.PGThreeNonHaus

/-!
# PGthree: the normal form of the null ultrafilters of a selective family (Lean check)

Scope. Section 6 of the third article (`PGthree.tex`).

* `normal_unique` : two representations `h + p_w` of the same ultrafilter, in which the coefficients of equal letters
  that differ by a principal image are equal, coincide;
* `replace_letter` : changing a coefficient by one with a principal image changes the letter by a translation;
* `selective_not_pretopological` : for a nonempty family of nonprincipal pairwise non-isomorphic selective ultrafilters
  the vicinity filter is not null.

The proof of `normal_unique` follows that of `length_le` in `PGThreeNonHaus`. No set-theoretic hypothesis is used. A
Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology Cardinal

namespace PG

namespace Null

open Sel

attribute [local instance] Ultrafilter.add Ultrafilter.addSemigroup

variable {G : Type} [AddCommGroup G] [Countable G] [Infinite G]

theorem normal_unique (S : Set (Ultrafilter G)) (hsel : ∀ u ∈ S, IsSel u) (hiso : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ Iso u v)
    (w w' : List (Ultrafilter G × ℤ)) (hw : Free1 S w) (hw' : Free1 S w') (h1 h2 : G)
    (hnorm : ∀ x ∈ w, ∀ y ∈ w', x.1 = y.1 → (∃ a, Img (x.1, x.2 - y.2) = pure a) → x.2 = y.2)
    (h : (pure h1 : Ultrafilter G) + pw w = pure h2 + pw w') : h1 = h2 ∧ w = w' := by
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
  -- the principal values
  let val : Fin U.card × ℤ → G := fun p =>
    if hp : ∃ a, Img (uu p.1, p.2) = pure a then Classical.choose hp else 0
  set V : Finset G := insert 0 ((Finset.univ ×ˢ D).image val) with hV
  set K : Finset G := (Fintype.piFinset (fun _ : Fin L => V)).image (fun v => h2 - h1 - ∑ i, v i) with hK
  have hrel : ∀ m : ℕ, ∀ σ : Fin (m + 1) → Fin U.card, ∀ d : Fin (m + 1) → ℤ, ∀ κ0 : G,
      (∀ l a, Img (uu (σ l), d l) ≠ pure a) → ∃ B : Fin U.card → Set ℕ, (∀ k, B k ∈ om k) ∧
        ∀ y : Fin (m + 1) → ℕ, StrictMono y → (∀ i, y i ∈ B (σ i)) → ∑ l, d l • e (y l) ≠ κ0 := by
    intro m σ d κ0 hd
    have hnl : ¬ Large (m + 1) (fun i => om (σ i)) {y : Fin (m + 1) → ℕ | ∑ l, d l • e (y l) = κ0} := by
      rw [large_snoc]
      have hempty : {p : Fin m → ℕ | {z : ℕ | (Fin.snoc p z : Fin (m + 1) → ℕ) ∈
          {y : Fin (m + 1) → ℕ | ∑ l, d l • e (y l) = κ0}} ∈ om (σ (Fin.last m))} = ∅ := by
        refine eq_empty_of_forall_notMem (fun p hp => ?_)
        have h3 : {z : ℕ | (Fin.snoc p z : Fin (m + 1) → ℕ) ∈
            {y : Fin (m + 1) → ℕ | ∑ l, d l • e (y l) = κ0}} ∈ om (σ (Fin.last m)) := hp
        have h4 : ({κ0 - ∑ l : Fin m, d l.castSucc • e (p l)} : Set G)
            ∈ Img (uu (σ (Fin.last m)), d (Fin.last m)) := by
          show {x : G | d (Fin.last m) • x ∈ ({κ0 - ∑ l : Fin m, d l.castSucc • e (p l)} : Set G)}
            ∈ uu (σ (Fin.last m))
          have h5 : e.symm ⁻¹' {z : ℕ | (Fin.snoc p z : Fin (m + 1) → ℕ) ∈
              {y : Fin (m + 1) → ℕ | ∑ l, d l • e (y l) = κ0}} ∈ uu (σ (Fin.last m)) := h3
          refine Filter.mem_of_superset h5 (fun x hx => ?_)
          have h6 : ∑ l, d l • e ((Fin.snoc p (e.symm x) : Fin (m + 1) → ℕ) l) = κ0 := hx
          rw [Fin.sum_univ_castSucc] at h6
          simp only [Fin.snoc_castSucc, Fin.snoc_last, Equiv.apply_symm_apply] at h6
          show d (Fin.last m) • x = κ0 - ∑ l : Fin m, d l.castSucc • e (p l)
          rw [← h6, add_sub_cancel_left]
        obtain ⟨a, _, h7⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h4
        exact hd (Fin.last m) a h7
      rw [hempty]
      exact not_large_empty m _
    exact tuples om homsel homiso (m + 1) σ _ hnl
  have hrel' : ∀ k : Fin U.card, ∃ C ∈ om k, ∀ m < L, ∀ σ : Fin (m + 1) → Fin U.card, ∀ d : Fin (m + 1) → ℤ,
      (∀ l, d l ∈ D) → ∀ κ0 ∈ K, ∀ hd : (∀ l a, Img (uu (σ l), d l) ≠ pure a),
        C ⊆ Classical.choose (hrel m σ d κ0 hd) k := by
    intro k
    have h3 : ∀ m : ℕ, (⋂ σ ∈ (Finset.univ : Finset (Fin (m + 1) → Fin U.card)),
        ⋂ d ∈ Fintype.piFinset (fun _ : Fin (m + 1) => D), ⋂ κ0 ∈ K,
          (if hd : (∀ l a, Img (uu (σ l), d l) ≠ pure a) then Classical.choose (hrel m σ d κ0 hd) k else univ))
        ∈ (om k : Filter ℕ) := by
      intro m
      refine (Filter.biInter_finset_mem _).2 (fun σ _ => (Filter.biInter_finset_mem _).2 (fun d _ =>
        (Filter.biInter_finset_mem _).2 (fun κ0 _ => ?_)))
      split_ifs with hd
      · exact (Classical.choose_spec (hrel m σ d κ0 hd)).1 k
      · exact Filter.univ_mem
    refine ⟨_, (Filter.biInter_finset_mem (Finset.range L)).2 (fun m _ => h3 m), ?_⟩
    intro m hm σ d hdD κ0 hκ hd x hx
    have h4 := mem_iInter₂.1 hx m (Finset.mem_range.2 hm)
    have h5 := mem_iInter₂.1 (mem_iInter₂.1 (mem_iInter₂.1 h4 σ (Finset.mem_univ σ)) d
      (Fintype.mem_piFinset.2 hdD)) κ0 hκ
    rw [dif_pos hd] at h5
    exact h5
  choose C1 hC1mem hC1 using hrel'
  have hdisj : ∃ C2 : Fin U.card → Set ℕ, (∀ k, C2 k ∈ om k) ∧ ∀ k k', ∀ x ∈ C2 k, x ∈ C2 k' → k = k' := by
    have h3 : ∀ k k' : Fin U.card, ∃ A : Set ℕ, A ∈ om k ∧ (k ≠ k' → Aᶜ ∈ om k') := by
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
    choose A hA hAc using h3
    refine ⟨fun k => ⋂ k' ∈ (Finset.univ : Finset (Fin U.card)), (A k k' ∩ if k = k' then univ else (A k' k)ᶜ),
      fun k => ?_, fun k k' x hx hx' => ?_⟩
    · refine (Filter.biInter_finset_mem _).2 (fun k' _ => Filter.inter_mem (hA k k') ?_)
      split_ifs with h
      · exact Filter.univ_mem
      · exact hAc k' k (Ne.symm h)
    · by_contra hne
      have h4 := (mem_iInter₂.1 hx k' (Finset.mem_univ _)).2
      rw [if_neg hne] at h4
      exact h4 (mem_iInter₂.1 hx' k (Finset.mem_univ _)).1
  obtain ⟨C2, hC2mem, hC2⟩ := hdisj
  let Z : Fin U.card → Set ℕ := fun k => {y | ∀ d ∈ D, (∃ a, Img (uu k, d) = pure a) → d • e y = val (k, d)}
  have hZmem : ∀ k, Z k ∈ om k := by
    intro k
    have h3 : (⋂ d ∈ D, {y : ℕ | (∃ a, Img (uu k, d) = pure a) → d • e y = val (k, d)}) ∈ (om k : Filter ℕ) := by
      refine (Filter.biInter_finset_mem D).2 (fun d _ => ?_)
      by_cases hd : ∃ a, Img (uu k, d) = pure a
      · have hval : val (k, d) = Classical.choose hd := dif_pos hd
        have h4 : ({val (k, d)} : Set G) ∈ Img (uu k, d) := by
          have h5 := Classical.choose_spec hd
          rw [hval]
          have h6 : ∀ p : Ultrafilter G, p = pure (Classical.choose hd) → ({Classical.choose hd} : Set G) ∈ p :=
            fun p hp => by rw [hp]; exact Set.mem_singleton (Classical.choose hd)
          exact h6 _ h5
        have h6 : {x : G | d • x ∈ ({val (k, d)} : Set G)} ∈ uu k := h4
        show e.symm ⁻¹' {y : ℕ | (∃ a, Img (uu k, d) = pure a) → d • e y = val (k, d)} ∈ uu k
        refine Filter.mem_of_superset h6 (fun x hx => ?_)
        intro _
        show d • e (e.symm x) = val (k, d)
        rw [Equiv.apply_symm_apply]; exact hx
      · exact Filter.mem_of_superset Filter.univ_mem (fun y _ h => absurd h hd)
    exact Filter.mem_of_superset h3 (fun y hy d hd => mem_iInter₂.1 hy d hd)
  let C : Fin U.card → Set ℕ := fun k => C1 k ∩ C2 k ∩ Z k
  have hCmem : ∀ k, C k ∈ om k := fun k => Filter.inter_mem (Filter.inter_mem (hC1mem k) (hC2mem k)) (hZmem k)
  let ix : (x : Ultrafilter G) → x ∈ U → Fin U.card := fun x hx => U.equivFin ⟨x, hx⟩
  have huix : ∀ x (hx : x ∈ U), uu (ix x hx) = x := by
    intro x hx
    show (U.equivFin.symm (U.equivFin ⟨x, hx⟩)).1 = x
    rw [Equiv.symm_apply_apply]
  let κ : Fin w.length → Fin U.card := fun i => ix (w.get i).1 (hwU _ (List.get_mem _ _))
  let κ' : Fin w'.length → Fin U.card := fun i => ix (w'.get i).1 (hw'U _ (List.get_mem _ _))
  have huκ' : ∀ i, uu (κ' i) = (w'.get i).1 := fun i => huix _ _
  let cf : Fin w.length → ℤ := fun i => (w.get i).2
  let cf' : Fin w'.length → ℤ := fun i => (w'.get i).2
  have hmemE : ∀ (v : List (Ultrafilter G × ℤ)) (kk : Fin v.length → Fin U.card),
      (∀ i, uu (kk i) = (v.get i).1) →
      {x : G | ∃ z : Fin v.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (kk i)) ∧ ∑ i, (v.get i).2 • e (z i) = x}
        ∈ pw v := by
    intro v kk hkk
    have h3 : List.ofFn (fun i => ((v.get i).1, (v.get i).2)) = v := by
      exact List.ofFn_get v
    have h4 := mem_pw_ofFn e v.length (fun i => (v.get i).1) (fun i => (v.get i).2)
      {x : G | ∃ z : Fin v.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (kk i)) ∧ ∑ i, (v.get i).2 • e (z i) = x}
    rw [h3] at h4
    rw [h4]
    have h5 : (fun i => ((v.get i).1).map e.symm) = fun i => om (kk i) := by
      funext i
      show ((v.get i).1).map e.symm = (uu (kk i)).map e.symm
      rw [hkk i]
    rw [h5]
    refine large_mono _ _ (fun y hy => ?_)
      (large_inc v.length (fun i => om (kk i)) (fun i => (homsel (kk i)).1) (fun i => C (kk i))
        (fun i => hCmem (kk i)) 0)
    exact ⟨y, hy.1, hy.2.1, rfl⟩
  have hE := hmemE w κ (fun i => huix _ _)
  have hE' := hmemE w' κ' huκ'
  have hT : {a : G | -h1 + a ∈ {x : G | ∃ z : Fin w.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (κ i))
      ∧ ∑ i, cf i • e (z i) = x}} ∈ (pure h1 + pw w : Ultrafilter G) := by
    rw [mem_pure_add]
    refine Filter.mem_of_superset hE (fun x hx => ?_)
    simp only [mem_setOf_eq, neg_add_cancel_left]
    exact hx
  have hT' : {a : G | -h2 + a ∈ {x : G | ∃ z : Fin w'.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (κ' i))
      ∧ ∑ i, cf' i • e (z i) = x}} ∈ (pure h2 + pw w' : Ultrafilter G) := by
    rw [mem_pure_add]
    refine Filter.mem_of_superset hE' (fun x hx => ?_)
    simp only [mem_setOf_eq, neg_add_cancel_left]
    exact hx
  rw [← h] at hT'
  obtain ⟨a, haT, haT'⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem (f := ((pure h1 + pw w : Ultrafilter G) : Filter G)) hT hT')
  obtain ⟨z, hzm, hzC, hzx⟩ := haT
  obtain ⟨z', hzm', hzC', hzx'⟩ := haT'
  set Y : Finset ℕ := Finset.univ.image z ∪ Finset.univ.image z' with hY
  let d : ℕ → ℤ := fun y => (∑ i ∈ Finset.univ.filter (fun i => z i = y), cf i)
    - ∑ i ∈ Finset.univ.filter (fun i => z' i = y), cf' i
  have hsum : ∑ y ∈ Y, d y • e y = h2 - h1 := by
    have key : ∀ (m : ℕ) (zz : Fin m → ℕ) (cc : Fin m → ℤ), (∀ i, zz i ∈ Y) →
        ∑ y ∈ Y, (∑ i ∈ Finset.univ.filter (fun i => zz i = y), cc i) • e y = ∑ i, cc i • e (zz i) := by
      intro m zz cc hmem
      rw [← Finset.sum_fiberwise_of_maps_to (fun i (_ : i ∈ Finset.univ) => hmem i) (fun i => cc i • e (zz i))]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [(Finset.mem_filter.1 hi).2]
    have h3 := key _ z cf (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem z (Finset.mem_univ i)))
    have h4 := key _ z' cf' (fun i => Finset.mem_union_right _ (Finset.mem_image_of_mem z' (Finset.mem_univ i)))
    simp only [d, sub_smul]
    rw [Finset.sum_sub_distrib, h3, h4, hzx, hzx']
    abel
  have hdsmall : ∀ y, d y ∈ D := by
    intro y
    have one : ∀ (v : List (Ultrafilter G × ℤ)), (∀ x ∈ v, x ∈ w ++ w') → ∀ (zz : Fin v.length → ℕ),
        Function.Injective zz → |∑ i ∈ Finset.univ.filter (fun i => zz i = y), (v.get i).2| ≤ (n : ℤ) := by
      intro v hv zz hzz
      by_cases hne : (Finset.univ.filter (fun i => zz i = y)).Nonempty
      · obtain ⟨i, hi⟩ := hne
        have h3 : Finset.univ.filter (fun i => zz i = y) = {i} := by
          ext j
          rw [Finset.mem_filter, Finset.mem_singleton]
          refine ⟨fun h => hzz (h.2.trans (Finset.mem_filter.1 hi).2.symm), fun h => ?_⟩
          rw [h]; exact Finset.mem_filter.1 hi
        rw [h3, Finset.sum_singleton]
        have h4 := hbound _ (hv _ (List.get_mem v i))
        rw [Int.abs_eq_natAbs]
        exact_mod_cast h4
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
    rcases Finset.mem_union.1 hy with h3 | h3
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h3
      exact ⟨κ i, hi ▸ hzC i⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h3
      exact ⟨κ' i, hi ▸ hzC' i⟩
  have hty' : ∀ y, ∃ k : Option (Fin U.card), y ∈ Y → ∃ k0, k = some k0 ∧ y ∈ C k0 := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨k, hk⟩ := hty y hy
      exact ⟨some k, fun _ => ⟨k, rfl, hk⟩⟩
    · exact ⟨none, fun h => absurd h hy⟩
  have huniq : ∀ y k k', y ∈ C k → y ∈ C k' → k = k' := fun y k k' h3 h4 => hC2 k k' y h3.1.2 h4.1.2
  -- the points whose collected coefficient has a nonprincipal image
  set T : Finset ℕ := Y.filter (fun y => ∃ k, y ∈ C k ∧ ∀ a, Img (uu k, d y) ≠ pure a) with hTdef
  have huκ : ∀ i, uu (κ i) = (w.get i).1 := fun i => huix _ _
  -- a letter with a nonprincipal image has no principal image after a change of sign
  have hneg : ∀ (u : Ultrafilter G) (c : ℤ) (a0 : G), Img (u, -c) = pure a0 → ∃ b, Img (u, c) = pure b := by
    intro u c a0 ha0
    have h6 : ({-a0} : Set G) ∈ Img (u, c) := by
      have h7 : ({a0} : Set G) ∈ Img (u, -c) := by rw [ha0]; exact rfl
      have h8 : {x : G | (-c) • x ∈ ({a0} : Set G)} ∈ u := h7
      show {x : G | c • x ∈ ({-a0} : Set G)} ∈ u
      refine Filter.mem_of_superset h8 (fun x hx => ?_)
      have h9 : (-c) • x = a0 := hx
      show c • x = -a0
      rw [← h9, neg_smul, neg_neg]
    obtain ⟨b, _, h10⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h6
    exact ⟨b, h10⟩
  -- the collected coefficients at points of one word only, or of both
  have hfil0 : ∀ (m : ℕ) (zz : Fin m → ℕ) (y : ℕ), y ∉ Finset.univ.image zz →
      Finset.univ.filter (fun i => zz i = y) = ∅ := by
    intro m zz y hy
    exact Finset.filter_eq_empty_iff.2 (fun i _ h => hy (Finset.mem_image.2 ⟨i, Finset.mem_univ _, h⟩))
  have hfil1 : ∀ (m : ℕ) (zz : Fin m → ℕ), Function.Injective zz → ∀ i,
      Finset.univ.filter (fun j => zz j = zz i) = {i} := by
    intro m zz hzz i
    ext j
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => hzz h.2, fun h => ⟨Finset.mem_univ _, by rw [h]⟩⟩
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · have hP : ∀ y ∈ Y, ∀ k, y ∈ C k → ∃ a0, Img (uu k, d y) = pure a0 := by
      intro y hy k hk
      by_contra h3
      have h4 : y ∈ T := Finset.mem_filter.2 ⟨hy, k, hk, fun a0 ha0 => h3 ⟨a0, ha0⟩⟩
      rw [hT0] at h4
      exact absurd h4 (Finset.notMem_empty _)
    have himz : Finset.univ.image z = Finset.univ.image z' := by
      refine Finset.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
      · by_contra h3
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hy
        have h5 : d (z i) = cf i := by
          show (∑ j ∈ Finset.univ.filter (fun j => z j = z i), cf j)
            - (∑ j ∈ Finset.univ.filter (fun j => z' j = z i), cf' j) = _
          rw [hfil1 _ z hzm.injective i, hfil0 _ z' _ h3, Finset.sum_empty, Finset.sum_singleton, sub_zero]
        obtain ⟨a0, ha0⟩ := hP (z i) (Finset.mem_union_left _ hy) (κ i) (hzC i)
        rw [h5, huκ i] at ha0
        exact (hw _ (List.get_mem w i)).2 a0 ha0
      · by_contra h3
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hy
        have h5 : d (z' j) = -cf' j := by
          show (∑ i ∈ Finset.univ.filter (fun i => z i = z' j), cf i)
            - (∑ i ∈ Finset.univ.filter (fun i => z' i = z' j), cf' i) = _
          rw [hfil0 _ z _ h3, hfil1 _ z' hzm'.injective j, Finset.sum_empty, Finset.sum_singleton, zero_sub]
        obtain ⟨a0, ha0⟩ := hP (z' j) (Finset.mem_union_right _ hy) (κ' j) (hzC' j)
        rw [h5] at ha0
        obtain ⟨b, hb⟩ := hneg _ _ _ ha0
        rw [huκ' j] at hb
        exact (hw' _ (List.get_mem w' j)).2 b hb
    have hlen : w.length = w'.length := by
      have h3 := congrArg Finset.card himz
      rw [Finset.card_image_of_injective _ hzm.injective, Finset.card_image_of_injective _ hzm'.injective] at h3
      simpa using h3
    have hcard : (Finset.univ.image z).card = w.length := by
      rw [Finset.card_image_of_injective _ hzm.injective]; simp
    have hzz : ∀ i : Fin w.length, z i = z' (Fin.cast hlen i) := by
      have h3 : z = (Finset.univ.image z).orderEmbOfFin hcard :=
        Finset.orderEmbOfFin_unique hcard (fun i => Finset.mem_image_of_mem z (Finset.mem_univ i)) hzm
      have h4 : (fun i => z' (Fin.cast hlen i)) = (Finset.univ.image z).orderEmbOfFin hcard :=
        Finset.orderEmbOfFin_unique hcard
          (fun i => by rw [himz]; exact Finset.mem_image_of_mem z' (Finset.mem_univ _))
          (fun a b hab => hzm' (show Fin.cast hlen a < Fin.cast hlen b from hab))
      intro i
      exact (congrFun h3 i).trans (congrFun h4 i).symm
    have hlet : ∀ i : Fin w.length, w.get i = w'.get (Fin.cast hlen i) := by
      intro i
      have hk : κ i = κ' (Fin.cast hlen i) :=
        huniq (z i) _ _ (hzC i) (by rw [hzz i]; exact hzC' _)
      have h1u : (w.get i).1 = (w'.get (Fin.cast hlen i)).1 := by
        rw [← huκ i, ← huκ' (Fin.cast hlen i), hk]
      have h5 : d (z i) = cf i - cf' (Fin.cast hlen i) := by
        show (∑ j ∈ Finset.univ.filter (fun j => z j = z i), cf j)
          - (∑ j ∈ Finset.univ.filter (fun j => z' j = z i), cf' j) = _
        rw [hfil1 _ z hzm.injective i, Finset.sum_singleton, hzz i, hfil1 _ z' hzm'.injective, Finset.sum_singleton]
      obtain ⟨a0, ha0⟩ := hP (z i) (Finset.mem_union_left _ (Finset.mem_image_of_mem z (Finset.mem_univ i)))
        (κ i) (hzC i)
      rw [h5, huκ i] at ha0
      exact Prod.ext h1u (hnorm _ (List.get_mem w i) _ (List.get_mem w' _) h1u ⟨a0, ha0⟩)
    have hww : w = w' := List.ext_get hlen (fun i hi _ => hlet ⟨i, hi⟩)
    refine ⟨?_, hww⟩
    have h3 : ∑ i, cf i • e (z i) = ∑ j, cf' j • e (z' j) := by
      refine Fintype.sum_equiv (finCongr hlen) _ _ (fun i => ?_)
      show (w.get i).2 • e (z i) = (w'.get (Fin.cast hlen i)).2 • e (z' (Fin.cast hlen i))
      rw [hlet i, hzz i]
    have h4 : -h1 + a = -h2 + a := by rw [← hzx, ← hzx']; exact h3
    exact neg_injective (add_right_cancel h4)
  exfalso
  obtain ⟨m, hm⟩ : ∃ m, T.card = m + 1 := ⟨T.card - 1, by have := hTne.card_pos; omega⟩
  have hYL : Y.card ≤ L := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · exact Finset.card_image_le.trans (by simp)
    · exact Finset.card_image_le.trans (by simp)
  have hmL : m < L := by
    have h3 : T.card ≤ Y.card := Finset.card_filter_le _ _
    omega
  let t : Fin (m + 1) → ℕ := fun l => T.orderEmbOfFin hm l
  have htmem : ∀ l, t l ∈ T := fun l => Finset.orderEmbOfFin_mem _ _ _
  have htm : StrictMono t := (T.orderEmbOfFin hm).strictMono
  have hσ : ∀ l, ∃ k, t l ∈ C k ∧ ∀ a, Img (uu k, d (t l)) ≠ pure a := fun l => (Finset.mem_filter.1 (htmem l)).2
  choose σ hσC hσne using hσ
  -- the other points contribute a constant from `K`
  set R : Finset ℕ := Y \ T with hR
  have hRval : ∀ y ∈ R, d y • e y ∈ V := by
    intro y hy
    obtain ⟨hyY, hyT⟩ := Finset.mem_sdiff.1 hy
    obtain ⟨k, hk⟩ := hty y hyY
    have h3 : ∃ a, Img (uu k, d y) = pure a := by
      by_contra h4
      exact hyT (Finset.mem_filter.2 ⟨hyY, k, hk, fun a ha => h4 ⟨a, ha⟩⟩)
    rw [hk.2 (d y) (hdsmall y) h3]
    exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(k, d y),
      Finset.mem_product.2 ⟨Finset.mem_univ _, hdsmall y⟩, rfl⟩)
  have hκK : h2 - h1 - ∑ y ∈ R, d y • e y ∈ K := by
    have hRL : R.card ≤ L := (Finset.card_le_card Finset.sdiff_subset).trans hYL
    have hpad : ∃ v : Fin L → G, (∀ i, v i ∈ V) ∧ ∑ i, v i = ∑ y ∈ R, d y • e y := by
      let f : ℕ → G := fun i => if hi : i < R.card then
        d (R.equivFin.symm ⟨i, hi⟩).1 • e (R.equivFin.symm ⟨i, hi⟩).1 else 0
      refine ⟨fun i => f i, fun i => ?_, ?_⟩
      · show f i ∈ V
        by_cases hi : (i : ℕ) < R.card
        · simp only [f, dif_pos hi]
          exact hRval _ (R.equivFin.symm ⟨i, hi⟩).2
        · simp only [f, dif_neg hi]
          exact Finset.mem_insert_self _ _
      · rw [Fin.sum_univ_eq_sum_range f L]
        have h3 : ∑ i ∈ Finset.range L, f i = ∑ i ∈ Finset.range R.card, f i := by
          refine (Finset.sum_subset (Finset.range_mono hRL) (fun i _ hi => ?_)).symm
          rw [Finset.mem_range] at hi
          simp only [f, dif_neg hi]
        rw [h3, ← Fin.sum_univ_eq_sum_range f R.card]
        have h4 : ∀ i : Fin R.card, f i = d (R.equivFin.symm i).1 • e (R.equivFin.symm i).1 := by
          intro i
          simp only [f, dif_pos i.2, Fin.eta]
        simp only [h4]
        rw [Equiv.sum_comp R.equivFin.symm (fun y : R => d y.1 • e y.1)]
        exact Finset.sum_coe_sort R (fun y => d y • e y)
    obtain ⟨v, hv, hvs⟩ := hpad
    exact Finset.mem_image.2 ⟨v, Fintype.mem_piFinset.2 hv, by rw [hvs]⟩
  let dd : Fin (m + 1) → ℤ := fun l => d (t l)
  have hddD : ∀ l, dd l ∈ D := fun l => hdsmall _
  have hsub : ∀ l, t l ∈ Classical.choose (hrel m σ dd _ hσne) (σ l) := fun l =>
    hC1 (σ l) m hmL σ dd hddD _ hκK hσne (hσC l).1.1
  refine (Classical.choose_spec (hrel m σ dd _ hσne)).2 t htm hsub ?_
  have himg : Finset.univ.image t = T := T.image_orderEmbOfFin_univ hm
  have h3 : ∑ l, dd l • e (t l) = ∑ y ∈ T, d y • e y := by
    rw [← himg, Finset.sum_image (fun a _ b _ hab => htm.injective hab)]
  have h4 : ∑ y ∈ R, d y • e y + ∑ y ∈ T, d y • e y = ∑ y ∈ Y, d y • e y :=
    Finset.sum_sdiff (Finset.filter_subset _ _)
  rw [h3, ← hsum, ← h4, add_sub_cancel_left]

/-- Changing a coefficient by one with a principal image changes the letter by a translation. -/
theorem replace_letter (u : Ultrafilter G) (c r : ℤ) (a : G) (h : Img (u, c - r) = pure a) :
    Img (u, c) = (pure a : Ultrafilter G) + Img (u, r) := by
  refine Ultrafilter.coe_le_coe.1 (fun A hA => ?_)
  have h1 : A ∈ (pure a : Ultrafilter G) + Img (u, r) := hA
  rw [mem_pure_add] at h1
  have h2 : {x : G | a + r • x ∈ A} ∈ u := h1
  have h3 : ({a} : Set G) ∈ Img (u, c - r) := by rw [h]; exact rfl
  have h4 : {x : G | (c - r) • x ∈ ({a} : Set G)} ∈ u := h3
  show {x : G | c • x ∈ A} ∈ u
  refine Filter.mem_of_superset (Filter.inter_mem (f := (u : Filter G)) h2 h4) (fun x hx => ?_)
  have h5 : (c - r) • x = a := hx.2
  have h6 : a + r • x ∈ A := hx.1
  show c • x ∈ A
  rw [← h5, ← add_smul, sub_add_cancel] at h6
  exact h6

/-- A selective family generates no pretopology. -/
theorem selective_not_pretopological (S : Set (Ultrafilter G)) (hsel : ∀ u ∈ S, IsSel u)
    (hiso : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ Iso u v) (hfree : ∀ u ∈ S, ∀ a, u ≠ pure a) (hS : S.Nonempty) :
    vic (genFam (ultraGen S)) ∉ genFam (ultraGen S) := by
  classical
  intro hvic
  have hC : NullFamily (genFam (ultraGen S)) := genFam_nullFamily _
  obtain ⟨u, hu⟩ := hS
  have huC : (u : Filter G) ∈ genFam (ultraGen S) :=
    ⟨u.neBot, fun U hU => ⟨u, SumClosure.gen ⟨u, hu, rfl⟩, hU⟩⟩
  have hV : IsNbhdFilter (vic (genFam (ultraGen S))) := by
    refine ⟨fun A hA => vic_zero_mem hC hA, fun A hA => vic_neg hC hA, fun A hA => ?_⟩
    have h1 : Filter.map₂ (· + ·) (vic (genFam (ultraGen S))) (vic (genFam (ultraGen S)))
        ≤ vic (genFam (ultraGen S)) := le_vic (hC.add _ hvic _ hvic)
    obtain ⟨B1, hB1, B2, hB2, h2⟩ := Filter.mem_map₂_iff.1 (h1 hA)
    exact ⟨B1 ∩ B2, Filter.inter_mem hB1 hB2, fun x hx y hy => h2 (mem_image2_of_mem hx.1 hy.2)⟩
  obtain ⟨F, hFfin, _, hF⟩ := (nbhd_iff S hsel hiso _).1 ⟨hV, hvic⟩
  have h1 : (u : Filter G) ≤ 𝓟 (F : Set G) := hF ▸ le_vic huC
  have h2 : (F : Set G) ∈ u := h1 (mem_principal_self _)
  obtain ⟨b, _, h3⟩ := Ultrafilter.eq_pure_of_finite_mem hFfin h2
  exact hfree u hu b h3

end Null

end PG
