import Mathlib
import LeanCheck.PGThreeNonHaus
import LeanCheck.PGThreeWords
import LeanCheck.PGTwoQuotient

/-!
# PGthree, Section 6: any family of selective ultrafilters (Lean check)

Letters are pairs `(i, φ)` of an index and a function `φ : ℕ → G`, standing for the image of the selective ultrafilter
`v i` under `φ`; the `v i` are pairwise non-isomorphic.

* `fun_normal_unique` : uniqueness of translated words whose letters have free images, when two letters with the same
  index and with principal image of the difference are equal;
* `exists_fword`, `exists_normal`, `normal_form_unique` : for the family of the images `(v (cls j)).map (f j)`, every
  null ultrafilter is a translated normalized word, in exactly one way;
* `exists_presentation` : every family of selective ultrafilters on a countably infinite group is of this kind;
* `family_no_idempotent`, `family_nbhd`, `family_coarsest_iff`, `family_not_pretopological`,
  `family_finite_generators`, `family_finite_coarsest`, `family_torsion_coarsest`, `family_torsionfree_trivial` :
  the statements on any family of selective ultrafilters;
* `translates_all_null`, `allTranslates_coarsest_iff`, `all_coarsest_iff_finite_torsion` : translates of one selective
  ultrafilter;
* `closure_example`, `closure_example_supply` : the group of null points need not be the closure of `0` in the
  topological modification.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology Cardinal

namespace PG

namespace AnySel

open Sel PG.Null PG.Words PG.Idem

attribute [local instance] Ultrafilter.add Ultrafilter.addSemigroup

variable {G : Type} [AddCommGroup G] {I : Type} (v : I → Ultrafilter ℕ)

/-! ### Words with function-valued letters -/

/-- The sum in the semigroup of ultrafilters of the images `(v i).map φ`. -/
def pwf : List (I × (ℕ → G)) → Ultrafilter G
  | [] => pure 0
  | x :: w => (v x.1).map x.2 + pwf w

theorem pwf_cons (x : I × (ℕ → G)) (w : List (I × (ℕ → G))) : pwf v (x :: w) = (v x.1).map x.2 + pwf v w := rfl

theorem pure_zero_add' (V : Ultrafilter G) : (pure 0 : Ultrafilter G) + V = V := PG.Null.pure_zero_add V

theorem add_comm_pure (h : G) (p : Ultrafilter G) : (pure h : Ultrafilter G) + p = p + pure h := by
  refine Ultrafilter.coe_injective (Filter.ext (fun A => ?_))
  show A ∈ (pure h : Ultrafilter G) + p ↔ A ∈ p + pure h
  rw [PG.Null.mem_add, PG.Null.mem_add]
  have e1 : {m : G | {z : G | m + z ∈ A} ∈ (pure h : Ultrafilter G)} = {z : G | h + z ∈ A} := by
    ext m
    show m + h ∈ A ↔ h + m ∈ A
    rw [add_comm]
  rw [e1]
  exact Iff.rfl

theorem add_pure_pure (a b : G) : (pure a : Ultrafilter G) + pure b = pure (a + b) := by
  refine Ultrafilter.coe_injective (Filter.ext (fun A => ?_))
  show A ∈ (pure a : Ultrafilter G) + pure b ↔ A ∈ (pure (a + b) : Ultrafilter G)
  rw [PG.Null.mem_add]
  exact Iff.rfl

theorem mem_add_pure_left (h : G) (p : Ultrafilter G) (A : Set G) :
    A ∈ (pure h : Ultrafilter G) + p ↔ {z : G | h + z ∈ A} ∈ p := by
  rw [PG.Null.mem_add]
  exact Iff.rfl

theorem coe_add_le' (U V : Ultrafilter G) :
    ((U + V : Ultrafilter G) : Filter G) ≤ Filter.map₂ (· + ·) (U : Filter G) (V : Filter G) := by
  intro s hs
  obtain ⟨a, ha, b, hb, hab⟩ := Filter.mem_map₂_iff.1 hs
  show s ∈ U + V
  rw [PG.Null.mem_add]
  refine Filter.mem_of_superset ha (fun m hm => ?_)
  exact Filter.mem_of_superset hb (fun z hz => hab (mem_image2_of_mem hm hz))

theorem pwf_append (w w' : List (I × (ℕ → G))) : pwf v (w ++ w') = pwf v w + pwf v w' := by
  induction w with
  | nil => exact (pure_zero_add' _).symm
  | cons x w ih =>
    show (v x.1).map x.2 + pwf v (w ++ w') = ((v x.1).map x.2 + pwf v w) + pwf v w'
    rw [ih, add_assoc]

theorem mem_pwf_cons (x : I × (ℕ → G)) (w : List (I × (ℕ → G))) (A : Set G) :
    A ∈ pwf v (x :: w) ↔ {n : ℕ | {z | x.2 n + z ∈ A} ∈ pwf v w} ∈ v x.1 := by
  show A ∈ (v x.1).map x.2 + pwf v w ↔ _
  rw [PG.Null.mem_add]
  exact Iff.rfl

theorem mem_pwf_ofFn : ∀ (r : ℕ) (i : Fin r → I) (φ : Fin r → ℕ → G) (A : Set G),
    A ∈ pwf v (List.ofFn (fun l => (i l, φ l))) ↔ Large r (fun l => v (i l)) {y | ∑ l, φ l (y l) ∈ A} := by
  intro r
  induction r with
  | zero =>
    intro i φ A
    rw [List.ofFn_zero, large_zero]
    show A ∈ (pure 0 : Ultrafilter G) ↔ ∑ l : Fin 0, φ l (Fin.elim0 l) ∈ A
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact Iff.rfl
  | succ r ih =>
    intro i φ A
    rw [List.ofFn_succ, mem_pwf_cons, large_succ]
    have h : {n : ℕ | {z : G | φ 0 n + z ∈ A} ∈ pwf v (List.ofFn (fun l : Fin r => (i l.succ, φ l.succ)))}
        = {x : ℕ | Large r (fun l => v (i l.succ))
            {t : Fin r → ℕ | Fin.cons x t ∈ {y : Fin (r + 1) → ℕ | ∑ l, φ l (y l) ∈ A}}} := by
      ext a
      rw [mem_setOf_eq, mem_setOf_eq, ih (fun l => i l.succ) (fun l => φ l.succ)]
      have hs : {y : Fin r → ℕ | ∑ l, φ l.succ (y l) ∈ {z : G | φ 0 a + z ∈ A}}
          = {t : Fin r → ℕ | Fin.cons a t ∈ {y : Fin (r + 1) → ℕ | ∑ l, φ l (y l) ∈ A}} := by
        ext t
        rw [mem_setOf_eq, mem_setOf_eq, mem_setOf_eq, mem_setOf_eq, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hs]
    rw [h]

/-- All letters have nonprincipal images. -/
def FreeW (w : List (I × (ℕ → G))) : Prop := ∀ x ∈ w, ∀ a, (v x.1).map x.2 ≠ pure a

theorem pwf_free (w : List (I × (ℕ → G))) (hw : FreeW v w) (hne : w ≠ []) : ∀ a, pwf v w ≠ pure a := by
  induction w with
  | nil => exact absurd rfl hne
  | cons x w ih =>
    intro a ha
    have hmem : ({a} : Set G) ∈ pwf v (x :: w) := by rw [ha]; exact rfl
    rw [mem_pwf_cons] at hmem
    rcases eq_or_ne w [] with hw0 | hw0
    · subst hw0
      have h1 : ({a} : Set G) ∈ (v x.1).map x.2 := by
        show {n : ℕ | x.2 n ∈ ({a} : Set G)} ∈ v x.1
        refine Filter.mem_of_superset hmem (fun b hb => ?_)
        have h2 : (0 : G) ∈ {z : G | x.2 b + z ∈ ({a} : Set G)} := hb
        simpa using h2
      obtain ⟨y, _, h2⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h1
      exact hw x (List.mem_cons_self ..) y h2
    · obtain ⟨b, hb⟩ := Ultrafilter.nonempty_of_mem hmem
      have h1 : {z : G | x.2 b + z ∈ ({a} : Set G)} ∈ pwf v w := hb
      refine ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) hw0 (a - x.2 b) ?_
      have h2 : ({a - x.2 b} : Set G) ∈ pwf v w := by
        refine Filter.mem_of_superset h1 (fun z hz => ?_)
        have h3 : x.2 b + z = a := hz
        rw [mem_singleton_iff, ← h3]; abel
      obtain ⟨y, hy, h4⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h2
      rw [h4, mem_singleton_iff.1 hy]

/-- Finitely many pairwise distinct ultrafilters have disjoint members. -/
theorem disjoint_members {m : ℕ} (om : Fin m → Ultrafilter ℕ) (hinj : Function.Injective om) :
    ∃ C : Fin m → Set ℕ, (∀ k, C k ∈ om k) ∧ ∀ k k', ∀ x ∈ C k, x ∈ C k' → k = k' := by
  classical
  have h3 : ∀ k k' : Fin m, ∃ A : Set ℕ, A ∈ om k ∧ (k ≠ k' → Aᶜ ∈ om k') := by
    intro k k'
    by_cases hkk : k = k'
    · exact ⟨univ, Filter.univ_mem, fun h => absurd hkk h⟩
    have hne : om k ≠ om k' := fun h => hkk (hinj h)
    have : ∃ A, A ∈ om k ∧ A ∉ om k' := by
      by_contra h
      refine hne (Ultrafilter.coe_le_coe.1 (fun A hA => ?_)).symm
      by_contra hn'
      exact h ⟨A, hA, hn'⟩
    obtain ⟨A, hA, hA'⟩ := this
    exact ⟨A, hA, fun _ => Ultrafilter.compl_mem_iff_notMem.2 hA'⟩
  choose A hA hAc using h3
  refine ⟨fun k => ⋂ k' ∈ (Finset.univ : Finset (Fin m)), (A k k' ∩ if k = k' then univ else (A k' k)ᶜ),
    fun k => ?_, fun k k' x hx hx' => ?_⟩
  · refine (Filter.biInter_finset_mem _).2 (fun k' _ => Filter.inter_mem (hA k k') ?_)
    split_ifs with h
    · exact Filter.univ_mem
    · exact hAc k' k (Ne.symm h)
  · by_contra hne
    have h4 := (mem_iInter₂.1 hx k' (Finset.mem_univ _)).2
    rw [if_neg hne] at h4
    exact h4 (mem_iInter₂.1 hx' k (Finset.mem_univ _)).1

theorem ne_of_not_iso {u w : Ultrafilter ℕ} (h : ¬ Iso u w) : u ≠ w := by
  intro he
  refine h ⟨Equiv.refl ℕ, ?_⟩
  rw [show ((Equiv.refl ℕ : Equiv.Perm ℕ) : ℕ → ℕ) = id from rfl, Ultrafilter.map_id, he]

/-- Uniqueness of translated words. -/
theorem fun_normal_unique (hsel : ∀ i, IsSel (v i)) (hiso : ∀ i j, i ≠ j → ¬ Iso (v i) (v j))
    (w w' : List (I × (ℕ → G))) (hw : FreeW v w) (hw' : FreeW v w') (h1 h2 : G)
    (hnorm : ∀ x ∈ w, ∀ y ∈ w', x.1 = y.1 → (∃ a, (v x.1).map (x.2 - y.2) = pure a) → x.2 = y.2)
    (h : (pure h1 : Ultrafilter G) + pwf v w = pure h2 + pwf v w') : h1 = h2 ∧ w = w' := by
  classical
  set U : Finset I := ((w ++ w').map Prod.fst).toFinset with hU
  have hwU : ∀ x ∈ w, x.1 ∈ U := fun x hx => by
    rw [hU, List.mem_toFinset]
    exact List.mem_map.2 ⟨x, List.mem_append_left _ hx, rfl⟩
  have hw'U : ∀ x ∈ w', x.1 ∈ U := fun x hx => by
    rw [hU, List.mem_toFinset]
    exact List.mem_map.2 ⟨x, List.mem_append_right _ hx, rfl⟩
  let uu : Fin U.card → I := fun k => (U.equivFin.symm k).1
  have huuinj : Function.Injective uu := fun a b hab => U.equivFin.symm.injective (Subtype.ext hab)
  let om : Fin U.card → Ultrafilter ℕ := fun k => v (uu k)
  have homsel : ∀ k, IsSel (om k) := fun k => hsel _
  have homiso : ∀ k k', k ≠ k' → ¬ Iso (om k) (om k') := fun k k' hkk' =>
    hiso _ _ (fun h => hkk' (huuinj h))
  set L : ℕ := w.length + w'.length with hL
  set Φ : Finset (ℕ → G) := insert 0 (w.map Prod.snd).toFinset with hΦ
  set Ψ : Finset (ℕ → G) := insert 0 (w'.map Prod.snd).toFinset with hΨ
  set D : Finset (ℕ → G) := (Φ ×ˢ Ψ).image (fun p => p.1 - p.2) with hD
  let val : Fin U.card × (ℕ → G) → G := fun p =>
    if hp : ∃ a, (om p.1).map p.2 = pure a then Classical.choose hp else 0
  set V : Finset G := insert 0 ((Finset.univ ×ˢ D).image val) with hV
  set K : Finset G := (Fintype.piFinset (fun _ : Fin L => V)).image (fun f => h2 - h1 - ∑ i, f i) with hK
  have hrel : ∀ m : ℕ, ∀ σ : Fin (m + 1) → Fin U.card, ∀ d : Fin (m + 1) → (ℕ → G), ∀ κ0 : G,
      (∀ l a, (om (σ l)).map (d l) ≠ pure a) → ∃ B : Fin U.card → Set ℕ, (∀ k, B k ∈ om k) ∧
        ∀ y : Fin (m + 1) → ℕ, StrictMono y → (∀ i, y i ∈ B (σ i)) → ∑ l, d l (y l) ≠ κ0 := by
    intro m σ d κ0 hd
    have hnl : ¬ Large (m + 1) (fun i => om (σ i)) {y : Fin (m + 1) → ℕ | ∑ l, d l (y l) = κ0} := by
      rw [large_snoc]
      have hempty : {p : Fin m → ℕ | {z : ℕ | (Fin.snoc p z : Fin (m + 1) → ℕ) ∈
          {y : Fin (m + 1) → ℕ | ∑ l, d l (y l) = κ0}} ∈ om (σ (Fin.last m))} = ∅ := by
        refine eq_empty_of_forall_notMem (fun p hp => ?_)
        have h3 : {z : ℕ | (Fin.snoc p z : Fin (m + 1) → ℕ) ∈
            {y : Fin (m + 1) → ℕ | ∑ l, d l (y l) = κ0}} ∈ om (σ (Fin.last m)) := hp
        have h4 : ({κ0 - ∑ l : Fin m, d l.castSucc (p l)} : Set G)
            ∈ (om (σ (Fin.last m))).map (d (Fin.last m)) := by
          show {x : ℕ | d (Fin.last m) x ∈ ({κ0 - ∑ l : Fin m, d l.castSucc (p l)} : Set G)}
            ∈ om (σ (Fin.last m))
          refine Filter.mem_of_superset h3 (fun x hx => ?_)
          have h6 : ∑ l, d l ((Fin.snoc p x : Fin (m + 1) → ℕ) l) = κ0 := hx
          rw [Fin.sum_univ_castSucc] at h6
          simp only [Fin.snoc_castSucc, Fin.snoc_last] at h6
          show d (Fin.last m) x = κ0 - ∑ l : Fin m, d l.castSucc (p l)
          rw [← h6, add_sub_cancel_left]
        obtain ⟨a, _, h7⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h4
        exact hd (Fin.last m) a h7
      rw [hempty]
      exact not_large_empty m _
    exact tuples om homsel homiso (m + 1) σ _ hnl
  have hrel' : ∀ k : Fin U.card, ∃ C ∈ om k, ∀ m < L, ∀ σ : Fin (m + 1) → Fin U.card, ∀ d : Fin (m + 1) → (ℕ → G),
      (∀ l, d l ∈ D) → ∀ κ0 ∈ K, ∀ hd : (∀ l a, (om (σ l)).map (d l) ≠ pure a),
        C ⊆ Classical.choose (hrel m σ d κ0 hd) k := by
    intro k
    have h3 : ∀ m : ℕ, (⋂ σ ∈ (Finset.univ : Finset (Fin (m + 1) → Fin U.card)),
        ⋂ d ∈ Fintype.piFinset (fun _ : Fin (m + 1) => D), ⋂ κ0 ∈ K,
          (if hd : (∀ l a, (om (σ l)).map (d l) ≠ pure a) then Classical.choose (hrel m σ d κ0 hd) k else univ))
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
  obtain ⟨C2, hC2mem, hC2⟩ := disjoint_members om (fun a b hab => by
    by_contra hne
    exact ne_of_not_iso (homiso a b hne) hab)
  let Z : Fin U.card → Set ℕ := fun k => {y | ∀ d ∈ D, (∃ a, (om k).map d = pure a) → d y = val (k, d)}
  have hZmem : ∀ k, Z k ∈ om k := by
    intro k
    have h3 : (⋂ d ∈ D, {y : ℕ | (∃ a, (om k).map d = pure a) → d y = val (k, d)}) ∈ (om k : Filter ℕ) := by
      refine (Filter.biInter_finset_mem D).2 (fun d _ => ?_)
      by_cases hd : ∃ a, (om k).map d = pure a
      · have hval : val (k, d) = Classical.choose hd := dif_pos hd
        have h4 : ({val (k, d)} : Set G) ∈ (om k).map d := by
          have h5 := Classical.choose_spec hd
          rw [hval]
          have h6 : ∀ p : Ultrafilter G, p = pure (Classical.choose hd) → ({Classical.choose hd} : Set G) ∈ p :=
            fun p hp => by rw [hp]; exact Set.mem_singleton (Classical.choose hd)
          exact h6 _ h5
        have h6 : {y : ℕ | d y ∈ ({val (k, d)} : Set G)} ∈ om k := h4
        exact Filter.mem_of_superset h6 (fun y hy _ => hy)
      · exact Filter.mem_of_superset Filter.univ_mem (fun y _ h => absurd h hd)
    exact Filter.mem_of_superset h3 (fun y hy d hd => mem_iInter₂.1 hy d hd)
  let C : Fin U.card → Set ℕ := fun k => C1 k ∩ C2 k ∩ Z k
  have hCmem : ∀ k, C k ∈ om k := fun k => Filter.inter_mem (Filter.inter_mem (hC1mem k) (hC2mem k)) (hZmem k)
  let ix : (x : I) → x ∈ U → Fin U.card := fun x hx => U.equivFin ⟨x, hx⟩
  have huix : ∀ x (hx : x ∈ U), uu (ix x hx) = x := by
    intro x hx
    show (U.equivFin.symm (U.equivFin ⟨x, hx⟩)).1 = x
    rw [Equiv.symm_apply_apply]
  let κ : Fin w.length → Fin U.card := fun i => ix (w.get i).1 (hwU _ (List.get_mem _ _))
  let κ' : Fin w'.length → Fin U.card := fun i => ix (w'.get i).1 (hw'U _ (List.get_mem _ _))
  have huκ : ∀ i, uu (κ i) = (w.get i).1 := fun i => huix _ _
  have huκ' : ∀ i, uu (κ' i) = (w'.get i).1 := fun i => huix _ _
  let cf : Fin w.length → (ℕ → G) := fun i => (w.get i).2
  let cf' : Fin w'.length → (ℕ → G) := fun i => (w'.get i).2
  have hmemE : ∀ (u : List (I × (ℕ → G))) (kk : Fin u.length → Fin U.card),
      (∀ i, uu (kk i) = (u.get i).1) →
      {x : G | ∃ z : Fin u.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (kk i)) ∧ ∑ i, (u.get i).2 (z i) = x}
        ∈ pwf v u := by
    intro u kk hkk
    have h3 : List.ofFn (fun i => ((u.get i).1, (u.get i).2)) = u := by
      exact List.ofFn_get u
    have h4 := mem_pwf_ofFn v u.length (fun i => (u.get i).1) (fun i => (u.get i).2)
      {x : G | ∃ z : Fin u.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (kk i)) ∧ ∑ i, (u.get i).2 (z i) = x}
    rw [h3] at h4
    rw [h4]
    have h5 : (fun i => v (u.get i).1) = fun i => om (kk i) := by
      funext i
      show v (u.get i).1 = v (uu (kk i))
      rw [hkk i]
    rw [h5]
    refine large_mono _ _ (fun y hy => ?_)
      (large_inc u.length (fun i => om (kk i)) (fun i => (homsel (kk i)).1) (fun i => C (kk i))
        (fun i => hCmem (kk i)) 0)
    exact ⟨y, hy.1, hy.2.1, rfl⟩
  have hE := hmemE w κ huκ
  have hE' := hmemE w' κ' huκ'
  have hT : {a : G | -h1 + a ∈ {x : G | ∃ z : Fin w.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (κ i))
      ∧ ∑ i, cf i (z i) = x}} ∈ (pure h1 + pwf v w : Ultrafilter G) := by
    rw [mem_add_pure_left]
    refine Filter.mem_of_superset hE (fun x hx => ?_)
    simp only [mem_setOf_eq, neg_add_cancel_left]
    exact hx
  have hT' : {a : G | -h2 + a ∈ {x : G | ∃ z : Fin w'.length → ℕ, StrictMono z ∧ (∀ i, z i ∈ C (κ' i))
      ∧ ∑ i, cf' i (z i) = x}} ∈ (pure h2 + pwf v w' : Ultrafilter G) := by
    rw [mem_add_pure_left]
    refine Filter.mem_of_superset hE' (fun x hx => ?_)
    simp only [mem_setOf_eq, neg_add_cancel_left]
    exact hx
  rw [← h] at hT'
  obtain ⟨a, haT, haT'⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem (f := ((pure h1 + pwf v w : Ultrafilter G) : Filter G)) hT hT')
  obtain ⟨z, hzm, hzC, hzx⟩ := haT
  obtain ⟨z', hzm', hzC', hzx'⟩ := haT'
  set Y : Finset ℕ := Finset.univ.image z ∪ Finset.univ.image z' with hY
  let d : ℕ → (ℕ → G) := fun y => (∑ i ∈ Finset.univ.filter (fun i => z i = y), cf i)
    - ∑ i ∈ Finset.univ.filter (fun i => z' i = y), cf' i
  have hsum : ∑ y ∈ Y, d y y = h2 - h1 := by
    have key : ∀ (m : ℕ) (zz : Fin m → ℕ) (cc : Fin m → (ℕ → G)), (∀ i, zz i ∈ Y) →
        ∑ y ∈ Y, (∑ i ∈ Finset.univ.filter (fun i => zz i = y), cc i) y = ∑ i, cc i (zz i) := by
      intro m zz cc hmem
      rw [← Finset.sum_fiberwise_of_maps_to (fun i (_ : i ∈ Finset.univ) => hmem i) (fun i => cc i (zz i))]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [(Finset.mem_filter.1 hi).2]
    have h3 := key _ z cf (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem z (Finset.mem_univ i)))
    have h4 := key _ z' cf' (fun i => Finset.mem_union_right _ (Finset.mem_image_of_mem z' (Finset.mem_univ i)))
    simp only [d, Pi.sub_apply]
    rw [Finset.sum_sub_distrib, h3, h4, hzx, hzx']
    abel
  have hdsmall : ∀ y, d y ∈ D := by
    intro y
    have one : ∀ (u : List (I × (ℕ → G))) (zz : Fin u.length → ℕ), Function.Injective zz →
        (∑ i ∈ Finset.univ.filter (fun i => zz i = y), (u.get i).2) ∈ insert 0 (u.map Prod.snd).toFinset := by
      intro u zz hzz
      by_cases hne : (Finset.univ.filter (fun i => zz i = y)).Nonempty
      · obtain ⟨i, hi⟩ := hne
        have h3 : Finset.univ.filter (fun i => zz i = y) = {i} := by
          ext j
          rw [Finset.mem_filter, Finset.mem_singleton]
          refine ⟨fun h => hzz (h.2.trans (Finset.mem_filter.1 hi).2.symm), fun h => ?_⟩
          rw [h]; exact Finset.mem_filter.1 hi
        rw [h3, Finset.sum_singleton]
        exact Finset.mem_insert_of_mem (List.mem_toFinset.2 (List.mem_map.2 ⟨_, List.get_mem u i, rfl⟩))
      · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
        exact Finset.mem_insert_self _ _
    exact Finset.mem_image.2 ⟨(_, _), Finset.mem_product.2 ⟨one w z hzm.injective, one w' z' hzm'.injective⟩, rfl⟩
  have hty : ∀ y ∈ Y, ∃ k, y ∈ C k := by
    intro y hy
    rcases Finset.mem_union.1 hy with h3 | h3
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h3
      exact ⟨κ i, hi ▸ hzC i⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h3
      exact ⟨κ' i, hi ▸ hzC' i⟩
  have huniq : ∀ y k k', y ∈ C k → y ∈ C k' → k = k' := fun y k k' h3 h4 => hC2 k k' y h3.1.2 h4.1.2
  set T : Finset ℕ := Y.filter (fun y => ∃ k, y ∈ C k ∧ ∀ a, (om k).map (d y) ≠ pure a) with hTdef
  have hneg : ∀ (u : Ultrafilter ℕ) (c : ℕ → G) (a0 : G), u.map (-c) = pure a0 → ∃ b, u.map c = pure b := by
    intro u c a0 ha0
    have h6 : ({-a0} : Set G) ∈ u.map c := by
      have h7 : ({a0} : Set G) ∈ u.map (-c) := by rw [ha0]; exact rfl
      have h8 : {x : ℕ | (-c) x ∈ ({a0} : Set G)} ∈ u := h7
      show {x : ℕ | c x ∈ ({-a0} : Set G)} ∈ u
      refine Filter.mem_of_superset h8 (fun x hx => ?_)
      have h9 : -(c x) = a0 := hx
      show c x = -a0
      rw [← h9, neg_neg]
    obtain ⟨b, _, h10⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h6
    exact ⟨b, h10⟩
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
  · have hP : ∀ y ∈ Y, ∀ k, y ∈ C k → ∃ a0, (om k).map (d y) = pure a0 := by
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
        rw [h5] at ha0
        change (v (uu (κ i))).map (w.get i).2 = pure a0 at ha0
        rw [huκ i] at ha0
        exact hw _ (List.get_mem w i) a0 ha0
      · by_contra h3
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hy
        have h5 : d (z' j) = -cf' j := by
          show (∑ i ∈ Finset.univ.filter (fun i => z i = z' j), cf i)
            - (∑ i ∈ Finset.univ.filter (fun i => z' i = z' j), cf' i) = _
          rw [hfil0 _ z _ h3, hfil1 _ z' hzm'.injective j, Finset.sum_empty, Finset.sum_singleton, zero_sub]
        obtain ⟨a0, ha0⟩ := hP (z' j) (Finset.mem_union_right _ hy) (κ' j) (hzC' j)
        rw [h5] at ha0
        obtain ⟨b, hb⟩ := hneg _ _ _ ha0
        change (v (uu (κ' j))).map (w'.get j).2 = pure b at hb
        rw [huκ' j] at hb
        exact hw' _ (List.get_mem w' j) b hb
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
      rw [h5] at ha0
      change (v (uu (κ i))).map ((w.get i).2 - (w'.get (Fin.cast hlen i)).2) = pure a0 at ha0
      rw [huκ i] at ha0
      exact Prod.ext h1u (hnorm _ (List.get_mem w i) _ (List.get_mem w' _) h1u ⟨a0, ha0⟩)
    have hww : w = w' := List.ext_get hlen (fun i hi _ => hlet ⟨i, hi⟩)
    refine ⟨?_, hww⟩
    have h3 : ∑ i, cf i (z i) = ∑ j, cf' j (z' j) := by
      refine Fintype.sum_equiv (finCongr hlen) _ _ (fun i => ?_)
      show (w.get i).2 (z i) = (w'.get (Fin.cast hlen i)).2 (z' (Fin.cast hlen i))
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
  have hσ : ∀ l, ∃ k, t l ∈ C k ∧ ∀ a, (om k).map (d (t l)) ≠ pure a := fun l => (Finset.mem_filter.1 (htmem l)).2
  choose σ hσC hσne using hσ
  set R : Finset ℕ := Y \ T with hR
  have hRval : ∀ y ∈ R, d y y ∈ V := by
    intro y hy
    obtain ⟨hyY, hyT⟩ := Finset.mem_sdiff.1 hy
    obtain ⟨k, hk⟩ := hty y hyY
    have h3 : ∃ a, (om k).map (d y) = pure a := by
      by_contra h4
      exact hyT (Finset.mem_filter.2 ⟨hyY, k, hk, fun a ha => h4 ⟨a, ha⟩⟩)
    rw [hk.2 (d y) (hdsmall y) h3]
    exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(k, d y),
      Finset.mem_product.2 ⟨Finset.mem_univ _, hdsmall y⟩, rfl⟩)
  have hκK : h2 - h1 - ∑ y ∈ R, d y y ∈ K := by
    have hRL : R.card ≤ L := (Finset.card_le_card Finset.sdiff_subset).trans hYL
    have hpad : ∃ f : Fin L → G, (∀ i, f i ∈ V) ∧ ∑ i, f i = ∑ y ∈ R, d y y := by
      let f : ℕ → G := fun i => if hi : i < R.card then
        d (R.equivFin.symm ⟨i, hi⟩).1 (R.equivFin.symm ⟨i, hi⟩).1 else 0
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
        have h4 : ∀ i : Fin R.card, f i = d (R.equivFin.symm i).1 (R.equivFin.symm i).1 := by
          intro i
          simp only [f, dif_pos i.2, Fin.eta]
        simp only [h4]
        rw [Equiv.sum_comp R.equivFin.symm (fun y : R => d y.1 y.1)]
        exact Finset.sum_coe_sort R (fun y => d y y)
    obtain ⟨f, hf, hfs⟩ := hpad
    exact Finset.mem_image.2 ⟨f, Fintype.mem_piFinset.2 hf, by rw [hfs]⟩
  let dd : Fin (m + 1) → (ℕ → G) := fun l => d (t l)
  have hddD : ∀ l, dd l ∈ D := fun l => hdsmall _
  have hsub : ∀ l, t l ∈ Classical.choose (hrel m σ dd _ hσne) (σ l) := fun l =>
    hC1 (σ l) m hmL σ dd hddD _ hκK hσne (hσC l).1.1
  refine (Classical.choose_spec (hrel m σ dd _ hσne)).2 t htm hsub ?_
  have himg : Finset.univ.image t = T := T.image_orderEmbOfFin_univ hm
  have h3 : ∑ l, dd l (t l) = ∑ y ∈ T, d y y := by
    rw [← himg, Finset.sum_image (fun a _ b _ hab => htm.injective hab)]
  have h4 : ∑ y ∈ R, d y y + ∑ y ∈ T, d y y = ∑ y ∈ Y, d y y :=
    Finset.sum_sdiff (Finset.filter_subset _ _)
  rw [h3, ← hsum, ← h4, add_sub_cancel_left]

/-! ### The PG generated by images of the ultrafilters -/

variable {J : Type} (cls : J → I) (f : J → ℕ → G)

/-- The family of the images `(v (cls j)).map (f j)`. -/
def fam : Set (Ultrafilter G) := Set.range (fun j => (v (cls j)).map (f j))

/-- The group of functions generated by the `f j` of the class `i`. -/
def Lf (i : I) : AddSubgroup (ℕ → G) := AddSubgroup.closure {φ | ∃ j, cls j = i ∧ φ = f j}

/-- The group generated by the principal values. -/
def Hf : AddSubgroup G := AddSubgroup.closure {g | ∃ i, ∃ φ ∈ Lf cls f i, (v i).map φ = pure g}

theorem map_mem (i : I) (φ : ℕ → G) (hφ : φ ∈ Lf cls f i) :
    (((v i).map φ : Ultrafilter G) : Filter G) ∈ genFam (ultraGen (fam v cls f)) := by
  have hC : NullFamily (genFam (ultraGen (fam v cls f))) := genFam_nullFamily _
  induction hφ using AddSubgroup.closure_induction with
  | mem φ h =>
    obtain ⟨j, hj, rfl⟩ := h
    exact ultra_mem_genFam _ _ ⟨j, by simp only [hj]⟩
  | zero =>
    have h1 : (v i).map (0 : ℕ → G) = pure 0 := by
      refine Ultrafilter.coe_injective ?_
      rw [Ultrafilter.coe_map, Ultrafilter.coe_pure]
      exact Filter.map_const
    rw [h1, Ultrafilter.coe_pure]
    exact hC.pure_zero
  | add φ ψ _ _ ihφ ihψ =>
    refine hC.finer _ (hC.add _ ihφ _ ihψ) _ (fun s hs => ?_) (Ultrafilter.neBot _)
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := Filter.mem_map₂_iff.1 hs
    have hP' : φ ⁻¹' P ∈ v i := hP
    have hQ' : ψ ⁻¹' Q ∈ v i := hQ
    show (φ + ψ) ⁻¹' s ∈ v i
    exact Filter.mem_of_superset (Filter.inter_mem (f := (v i : Filter ℕ)) hP' hQ')
      (fun n hn => hPQ (mem_image2_of_mem hn.1 hn.2))
  | neg φ _ ih =>
    have h1 : (((v i).map (-φ) : Ultrafilter G) : Filter G)
        = Filter.map (fun x : G => -x) (((v i).map φ : Ultrafilter G) : Filter G) := by
      rw [Ultrafilter.coe_map, Ultrafilter.coe_map, Filter.map_map]
      rfl
    rw [h1]
    exact hC.neg _ ih

theorem Hf_le_null (g : G) (hg : g ∈ Hf v cls f) : (pure g : Filter G) ∈ genFam (ultraGen (fam v cls f)) := by
  have hC : NullFamily (genFam (ultraGen (fam v cls f))) := genFam_nullFamily _
  have hle : Hf v cls f ≤ nullPts _ hC := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨i, φ, hφ, hx⟩
    have h1 := map_mem v cls f i φ hφ
    rw [hx, Ultrafilter.coe_pure] at h1
    exact h1
  exact hle hg

theorem pwf_mem (w : List (I × (ℕ → G))) (hw : ∀ x ∈ w, x.2 ∈ Lf cls f x.1) :
    (pwf v w : Filter G) ∈ genFam (ultraGen (fam v cls f)) := by
  have hC : NullFamily (genFam (ultraGen (fam v cls f))) := genFam_nullFamily _
  induction w with
  | nil =>
    show ((pure 0 : Ultrafilter G) : Filter G) ∈ _
    rw [Ultrafilter.coe_pure]; exact hC.pure_zero
  | cons x w ih =>
    have h1 := map_mem v cls f x.1 x.2 (hw x (List.mem_cons_self ..))
    have h2 := hC.add _ h1 _ (ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)))
    exact hC.finer _ h2 _ (coe_add_le' _ _) (Ultrafilter.neBot _)

theorem translated_mem (h : G) (hh : h ∈ Hf v cls f) (w : List (I × (ℕ → G)))
    (hw : ∀ x ∈ w, x.2 ∈ Lf cls f x.1) :
    ((pure h + pwf v w : Ultrafilter G) : Filter G) ∈ genFam (ultraGen (fam v cls f)) := by
  have hC : NullFamily (genFam (ultraGen (fam v cls f))) := genFam_nullFamily _
  have h1 : ((pure h : Ultrafilter G) : Filter G) ∈ genFam (ultraGen (fam v cls f)) := by
    rw [Ultrafilter.coe_pure]; exact Hf_le_null v cls f h hh
  have h2 := hC.add _ h1 _ (pwf_mem v cls f w hw)
  exact hC.finer _ h2 _ (coe_add_le' _ _) (Ultrafilter.neBot _)

/-- Every null ultrafilter is the ultrafilter of a word. -/
theorem exists_fword (hsel : ∀ i, IsSel (v i)) (hiso : ∀ i j, i ≠ j → ¬ Iso (v i) (v j))
    (W : Ultrafilter G) (hW : (W : Filter G) ∈ genFam (ultraGen (fam v cls f))) :
    ∃ w : List (I × (ℕ → G)), (∀ x ∈ w, x.2 ∈ Lf cls f x.1) ∧ pwf v w = W := by
  classical
  obtain ⟨σ, hσ, hWσ⟩ := hW.2 W le_rfl
  obtain ⟨ι, _, u, ε, hu, hε, hrep⟩ := rep_of_sumClosure _ hσ
  choose jj hjj using hu
  have hjj' : ∀ k, (v (cls (jj k))).map (f (jj k)) = u k := hjj
  let sm : (ι → ℕ) → G := fun y => ∑ k, ε k • f (jj k) (y k)
  set F : Filter (ι → ℕ) := Filter.pi (fun k => (v (cls (jj k)) : Filter ℕ)) ⊓ Filter.comap sm (W : Filter G) with hF
  have hFne : F.NeBot := by
    rw [hF, Filter.inf_neBot_iff]
    intro s hs t ht
    obtain ⟨Is, _, A, hA, hAs⟩ := Filter.mem_pi.1 hs
    obtain ⟨B, hB, hBt⟩ := Filter.mem_comap.1 ht
    let A' : ι → Set ℕ := fun k => if k ∈ Is then A k else univ
    have hA' : ∀ k, A' k ∈ v (cls (jj k)) := by
      intro k
      show (if k ∈ Is then A k else univ) ∈ v (cls (jj k))
      split_ifs
      · exact hA k
      · exact Filter.univ_mem
    have himg : ∀ k, f (jj k) '' A' k ∈ u k := by
      intro k
      rw [← hjj' k]
      show f (jj k) ⁻¹' (f (jj k) '' A' k) ∈ v (cls (jj k))
      exact Filter.mem_of_superset (hA' k) (subset_preimage_image _ _)
    have hT := hWσ (hrep (fun k => f (jj k) '' A' k) himg)
    obtain ⟨z, hz1, hz2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (W : Filter G)) hT hB)
    obtain ⟨a, ha, hsum⟩ := hz1
    choose y hy hya using ha
    refine ⟨y, hAs (fun k hk => ?_), hBt ?_⟩
    · have := hy k
      simpa [A', hk] using this
    · show ∑ k, ε k • f (jj k) (y k) ∈ B
      have : ∑ k, ε k • f (jj k) (y k) = ∑ k, ε k • a k :=
        Finset.sum_congr rfl (fun k _ => by rw [hya k])
      rw [this, hsum]; exact hz2
  have := hFne
  set Z : Ultrafilter (ι → ℕ) := Ultrafilter.of F with hZ
  have hZF : (Z : Filter (ι → ℕ)) ≤ F := Ultrafilter.of_le F
  have hmarg : ∀ k, Z.map (fun y => y k) = v (cls (jj k)) := by
    intro k
    refine Ultrafilter.coe_le_coe.1 ?_
    rw [Ultrafilter.coe_map]
    exact (Filter.map_mono (hZF.trans (inf_le_left))).trans (Filter.tendsto_eval_pi _ k)
  have hsumZ : Z.map sm = W := by
    refine Ultrafilter.coe_le_coe.1 ?_
    rw [Ultrafilter.coe_map]
    exact (Filter.map_mono (hZF.trans inf_le_right)).trans Filter.map_comap_le
  rcases isEmpty_or_nonempty ι with h | hι
  · have h1 : Z.map sm = pure 0 := by
      have : sm = fun _ => (0 : G) := by
        funext y
        show ∑ k, ε k • f (jj k) (y k) = 0
        rw [Finset.univ_eq_empty, Finset.sum_empty]
      rw [this]
      refine Ultrafilter.coe_injective ?_
      rw [Ultrafilter.coe_map, Ultrafilter.coe_pure]
      exact Filter.map_const
    exact ⟨[], fun x hx => absurd hx List.not_mem_nil, by rw [← hsumZ, h1]; rfl⟩
  -- disjoint members of the different `v i`
  set UI : Finset I := Finset.univ.image (fun k => cls (jj k)) with hUI
  let uu : Fin UI.card → I := fun m => (UI.equivFin.symm m).1
  have huuinj : Function.Injective uu := fun a b hab => UI.equivFin.symm.injective (Subtype.ext hab)
  have hmemUI : ∀ k, cls (jj k) ∈ UI := fun k => Finset.mem_image_of_mem _ (Finset.mem_univ k)
  let ix : ι → Fin UI.card := fun k => UI.equivFin ⟨cls (jj k), hmemUI k⟩
  have huix : ∀ k, uu (ix k) = cls (jj k) := by
    intro k
    show (UI.equivFin.symm (UI.equivFin ⟨cls (jj k), hmemUI k⟩)).1 = cls (jj k)
    rw [Equiv.symm_apply_apply]
  obtain ⟨Dj, hDmem, hDdisj⟩ := disjoint_members (fun m => v (uu m)) (fun a b hab => by
    by_contra hne
    exact ne_of_not_iso (hiso _ _ (fun h => hne (huuinj h))) hab)
  have hDZ : (⋂ k ∈ (Finset.univ : Finset ι), {y : ι → ℕ | y k ∈ Dj (ix k)}) ∈ (Z : Filter _) := by
    refine (Filter.biInter_finset_mem _).2 (fun k _ => ?_)
    have h1 : Dj (ix k) ∈ v (cls (jj k)) := by rw [← huix k]; exact hDmem (ix k)
    rw [← hmarg k] at h1
    exact h1
  -- the pattern of equalities and order
  let rk : (ι → ℕ) → ι → Fin (Fintype.card ι) := fun a i =>
    ⟨((Finset.univ.image (fun j => a j)).filter (fun z => z < a i)).card, by
      have h1 : ((Finset.univ.image (fun j => a j)).filter (fun z => z < a i)) ⊂ Finset.univ.image (fun j => a j) :=
        Finset.filter_ssubset.2 ⟨a i, Finset.mem_image_of_mem _ (Finset.mem_univ i), lt_irrefl _⟩
      exact lt_of_lt_of_le (Finset.card_lt_card h1) (Finset.card_image_le.trans Finset.card_univ.le)⟩
  have hrk_mono : ∀ a i j, a i < a j → rk a i < rk a j := by
    intro a i j h
    show (Finset.filter _ _).card < (Finset.filter _ _).card
    refine Finset.card_lt_card ⟨fun z hz => ?_, fun hsub => ?_⟩
    · rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hz.2.trans h⟩
    · have h1 : a i ∈ (Finset.univ.image (fun j => a j)).filter (fun z => z < a j) :=
        Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), h⟩
      exact lt_irrefl _ (Finset.mem_filter.1 (hsub h1)).2
  have hrk_eq : ∀ a i j, rk a i = rk a j ↔ a i = a j := by
    intro a i j
    constructor
    · intro h
      rcases lt_trichotomy (a i) (a j) with h' | h' | h'
      · exact absurd h (hrk_mono a i j h').ne
      · exact h'
      · exact absurd h (hrk_mono a j i h').ne'
    · intro h
      apply Fin.ext
      show (Finset.filter _ _).card = (Finset.filter _ _).card
      rw [h]
  have hrk_lt : ∀ a i j, rk a i < rk a j ↔ a i < a j := by
    intro a i j
    refine ⟨fun h => ?_, hrk_mono a i j⟩
    rcases lt_trichotomy (a i) (a j) with h' | h' | h'
    · exact h'
    · exact absurd ((hrk_eq a i j).2 h') h.ne
    · exact absurd (hrk_mono a j i h') h.asymm
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ι → Fin (Fintype.card ι), {a | rk a = ρ} ∈ Z := by
    by_contra h
    have h1 : (⋂ ρ ∈ (Finset.univ : Finset (ι → Fin (Fintype.card ι))), {a : ι → ℕ | rk a = ρ}ᶜ) ∈ (Z : Filter _) := by
      refine (Filter.biInter_finset_mem _).2 (fun ρ _ => ?_)
      rcases Z.mem_or_compl_mem {a | rk a = ρ} with h' | h'
      · exact absurd ⟨ρ, h'⟩ h
      · exact h'
    obtain ⟨a, ha⟩ := Ultrafilter.nonempty_of_mem h1
    exact mem_iInter₂.1 ha (rk a) (Finset.mem_univ _) rfl
  obtain ⟨a0, ha0, ha0D⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hρ hDZ)
  have ha0' : rk a0 = ρ := ha0
  have hcls : ∀ k m, ρ k = ρ m → cls (jj k) = cls (jj m) := by
    intro k m hkm
    have h1 : a0 k = a0 m := (hrk_eq a0 k m).1 (by rw [ha0']; exact hkm)
    have h2 : a0 k ∈ Dj (ix k) := mem_iInter₂.1 ha0D k (Finset.mem_univ k)
    have h3 : a0 m ∈ Dj (ix m) := mem_iInter₂.1 ha0D m (Finset.mem_univ m)
    rw [← h1] at h3
    rw [← huix k, ← huix m, hDdisj _ _ _ h2 h3]
  set Jr : Finset (Fin (Fintype.card ι)) := Finset.univ.image ρ with hJ
  set r : ℕ := Jr.card with hr
  let ord : Fin r ≃o Jr := Jr.orderIsoOfFin rfl
  have hsec : ∀ l : Fin r, ∃ i, ρ i = (ord l).1 := by
    intro l
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 (ord l).2
    exact ⟨i, hi⟩
  choose s hs using hsec
  have hpos : ∀ i, ρ i ∈ Jr := fun i => Finset.mem_image_of_mem ρ (Finset.mem_univ i)
  let pos : ι → Fin r := fun i => ord.symm ⟨ρ i, hpos i⟩
  have hordpos : ∀ i, (ord (pos i)).1 = ρ i := by
    intro i
    show (ord (ord.symm ⟨ρ i, hpos i⟩)).1 = ρ i
    rw [OrderIso.apply_symm_apply]
  let z : (ι → ℕ) → Fin r → ℕ := fun a l => a (s l)
  have hz : ∀ a, rk a = ρ → ∀ i, a i = z a (pos i) := by
    intro a ha i
    refine (hrk_eq a i (s (pos i))).1 ?_
    rw [ha, hs, hordpos]
  have hzmono : ∀ a, rk a = ρ → StrictMono (z a) := by
    intro a ha l m hlm
    refine (hrk_lt a (s l) (s m)).1 ?_
    rw [ha, hs, hs]
    exact ord.strictMono hlm
  let idx : Fin r → I := fun l => cls (jj (s l))
  have hfub : ∀ R : Set (Fin r → ℕ), Large r (fun l => v (idx l)) R → {a | z a ∈ R} ∈ Z := by
    intro R hR
    rcases Z.mem_or_compl_mem {a | z a ∈ R} with h | h
    · exact h
    exfalso
    let w : Fin UI.card → Ultrafilter ℕ := fun m => v (uu m)
    let τ : Fin r → Fin UI.card := fun l => ix (s l)
    have hwτ : ∀ l, w (τ l) = v (idx l) := fun l => by
      show v (uu (ix (s l))) = v (idx l)
      rw [huix]
    have hwsel : ∀ m, IsSel (w m) := fun m => hsel _
    have hwiso : ∀ m m', m ≠ m' → ¬ Iso (w m) (w m') := fun m m' h => hiso _ _ (fun he => h (huuinj he))
    have hnl : ¬ Large r (fun l => w (τ l)) Rᶜ := by
      have : (fun l => w (τ l)) = fun l => v (idx l) := funext hwτ
      rw [this, large_compl]
      exact not_not.2 hR
    obtain ⟨B, hB, hav⟩ := tuples w hwsel hwiso r τ Rᶜ hnl
    have hmargB : ∀ l, {a : ι → ℕ | z a l ∈ B (τ l)} ∈ Z := by
      intro l
      have h1 : B (τ l) ∈ v (cls (jj (s l))) := by
        have h2 := hB (τ l)
        rw [hwτ l] at h2
        exact h2
      rw [← hmarg (s l)] at h1
      exact h1
    have hall : (⋂ l ∈ (Finset.univ : Finset (Fin r)), {a : ι → ℕ | z a l ∈ B (τ l)}) ∈ (Z : Filter _) :=
      (Filter.biInter_finset_mem _).2 (fun l _ => hmargB l)
    have h12 : {a | rk a = ρ} ∩ {a | z a ∈ R}ᶜ ∈ (Z : Filter _) := Filter.inter_mem hρ h
    obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h12 hall)
    exact hav (z a) (hzmono a ha1) (fun l => mem_iInter₂.1 ha3 l (Finset.mem_univ l)) ha2
  let φ : Fin r → (ℕ → G) := fun l => ∑ i ∈ Finset.univ.filter (fun i => pos i = l), ε i • f (jj i)
  have hφ : ∀ l, φ l ∈ Lf cls f (idx l) := by
    intro l
    refine AddSubgroup.sum_mem _ (fun i hi => AddSubgroup.zsmul_mem _
      (AddSubgroup.subset_closure (show f (jj i) ∈ {ψ | ∃ j, cls j = idx l ∧ ψ = f j} from ⟨jj i, ?_, rfl⟩)) _)
    have h1 : pos i = l := (Finset.mem_filter.1 hi).2
    refine hcls i (s l) ?_
    rw [hs l, ← h1, hordpos i]
  have hcollect : ∀ a, rk a = ρ → sm a = ∑ l, φ l (z a l) := by
    intro a ha
    show ∑ i, ε i • f (jj i) (a i)
      = ∑ l, (∑ i ∈ Finset.univ.filter (fun i => pos i = l), ε i • f (jj i)) (z a l)
    rw [← Finset.sum_fiberwise Finset.univ pos (fun i => ε i • f (jj i) (a i))]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have h1 : pos i = l := (Finset.mem_filter.1 hi).2
    have h2 := hz a ha i
    rw [h1] at h2
    rw [Pi.smul_apply, ← h2]
  refine ⟨List.ofFn (fun l => (idx l, φ l)), fun x hx => ?_, ?_⟩
  · rw [List.mem_ofFn] at hx
    obtain ⟨l, hl⟩ := hx
    rw [← hl]
    exact hφ l
  · refine (Ultrafilter.coe_le_coe.1 (fun A hA => ?_)).symm
    have h1 := (mem_pwf_ofFn v r idx φ A).1 hA
    have h2 := hfub _ h1
    have h3 : sm ⁻¹' A ∈ Z := by
      refine Filter.mem_of_superset (Filter.inter_mem hρ h2) (fun a ha => ?_)
      show sm a ∈ A
      rw [hcollect a ha.1]
      exact ha.2
    show A ∈ W
    rw [← hsumZ]
    exact h3

/-! ### Normalized words -/

/-- Two functions of the class `i` are equivalent when their difference has a principal image. -/
def sameCoset (i : I) : Setoid (Lf cls f i) where
  r a b := ∃ g, (v i).map ((a : ℕ → G) - (b : ℕ → G)) = pure g
  iseqv := by
    have key : ∀ (φ : ℕ → G) (g : G), (v i).map φ = pure g ↔ {n | φ n = g} ∈ v i := by
      intro φ g
      constructor
      · intro h
        have h1 : ({g} : Set G) ∈ (v i).map φ := by rw [h]; exact rfl
        exact h1
      · intro h
        have h1 : ({g} : Set G) ∈ (v i).map φ := h
        obtain ⟨b, hb, h2⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h1
        rw [h2, mem_singleton_iff.1 hb]
    refine ⟨fun a => ⟨0, (key _ _).2 ?_⟩, fun {a b} h => ?_, fun {a b c} h1 h2 => ?_⟩
    · exact Filter.mem_of_superset Filter.univ_mem (fun n _ => by simp)
    · obtain ⟨g, hg⟩ := h
      refine ⟨-g, (key _ _).2 (Filter.mem_of_superset ((key _ _).1 hg) (fun n hn => ?_))⟩
      have h3 : (a : ℕ → G) n - (b : ℕ → G) n = g := hn
      show (b : ℕ → G) n - (a : ℕ → G) n = -g
      rw [← h3, neg_sub]
    · obtain ⟨g, hg⟩ := h1
      obtain ⟨g', hg'⟩ := h2
      refine ⟨g + g', (key _ _).2 (Filter.mem_of_superset
        (Filter.inter_mem (f := (v i : Filter ℕ)) ((key _ _).1 hg) ((key _ _).1 hg')) (fun n hn => ?_))⟩
      have h3 : (a : ℕ → G) n - (b : ℕ → G) n = g := hn.1
      have h4 : (b : ℕ → G) n - (c : ℕ → G) n = g' := hn.2
      show (a : ℕ → G) n - (c : ℕ → G) n = g + g'
      rw [← h3, ← h4, sub_add_sub_cancel]

/-- A normalized letter: a chosen element of its coset, with nonprincipal image. -/
def NLetter (x : I × (ℕ → G)) : Prop :=
  (∃ h : x.2 ∈ Lf cls f x.1, (Quotient.mk (sameCoset v cls f x.1) ⟨x.2, h⟩).out = ⟨x.2, h⟩) ∧
    ∀ a, (v x.1).map x.2 ≠ pure a

def Normal (w : List (I × (ℕ → G))) : Prop := ∀ x ∈ w, NLetter v cls f x

theorem normal_mem (w : List (I × (ℕ → G))) (hw : Normal v cls f w) : ∀ x ∈ w, x.2 ∈ Lf cls f x.1 :=
  fun x hx => (hw x hx).1.1

theorem normal_free (w : List (I × (ℕ → G))) (hw : Normal v cls f w) : FreeW v w := fun x hx => (hw x hx).2

theorem map_eq_pure_add (i : I) (φ ψ : ℕ → G) (a : G) (h : (v i).map (φ - ψ) = pure a) :
    (v i).map φ = (pure a : Ultrafilter G) + (v i).map ψ := by
  refine Ultrafilter.coe_le_coe.1 (fun A hA => ?_)
  have h1 : A ∈ (pure a : Ultrafilter G) + (v i).map ψ := hA
  rw [mem_add_pure_left] at h1
  have h2 : {n : ℕ | a + ψ n ∈ A} ∈ v i := h1
  have h3 : ({a} : Set G) ∈ (v i).map (φ - ψ) := by rw [h]; exact rfl
  have h4 : {n : ℕ | (φ - ψ) n ∈ ({a} : Set G)} ∈ v i := h3
  show {n : ℕ | φ n ∈ A} ∈ v i
  refine Filter.mem_of_superset (Filter.inter_mem (f := (v i : Filter ℕ)) h2 h4) (fun n hn => ?_)
  have h5 : φ n - ψ n = a := hn.2
  have h6 : a + ψ n ∈ A := hn.1
  show φ n ∈ A
  rwa [← h5, sub_add_cancel] at h6

theorem normalize (w : List (I × (ℕ → G))) (hw : ∀ x ∈ w, x.2 ∈ Lf cls f x.1) :
    ∃ h ∈ Hf v cls f, ∃ w', Normal v cls f w' ∧ pwf v w = pure h + pwf v w' := by
  induction w with
  | nil => exact ⟨0, zero_mem _, [], fun x hx => absurd hx List.not_mem_nil, (pure_zero_add' _).symm⟩
  | cons x w ih =>
    obtain ⟨h, hh, w', hw', hpw⟩ := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    have hx := hw x (List.mem_cons_self ..)
    by_cases hp : ∃ a, (v x.1).map x.2 = pure a
    · obtain ⟨a, ha⟩ := hp
      have haH : a ∈ Hf v cls f := AddSubgroup.subset_closure ⟨x.1, x.2, hx, ha⟩
      refine ⟨a + h, add_mem haH hh, w', hw', ?_⟩
      rw [pwf_cons, ha, hpw, ← add_assoc, add_pure_pure]
    · set s := sameCoset v cls f x.1 with hs
      set ψ : Lf cls f x.1 := (Quotient.mk s ⟨x.2, hx⟩).out with hψ
      have hrel : s.r ψ ⟨x.2, hx⟩ := Quotient.mk_out (s := s) ⟨x.2, hx⟩
      obtain ⟨a, ha⟩ : s.r ⟨x.2, hx⟩ ψ := s.symm hrel
      have haH : a ∈ Hf v cls f :=
        AddSubgroup.subset_closure ⟨x.1, x.2 - (ψ : ℕ → G), sub_mem hx ψ.2, ha⟩
      have heq := map_eq_pure_add v x.1 x.2 (ψ : ℕ → G) a ha
      have hfree : ∀ b, (v x.1).map (ψ : ℕ → G) ≠ pure b := by
        intro b hb
        apply hp
        exact ⟨a + b, by rw [heq, hb, add_pure_pure]⟩
      have hnl : NLetter v cls f (x.1, (ψ : ℕ → G)) := by
        refine ⟨⟨ψ.2, ?_⟩, hfree⟩
        have h1 : Quotient.mk s ψ = Quotient.mk s ⟨x.2, hx⟩ := Quotient.out_eq _
        show (Quotient.mk s ψ).out = ψ
        rw [h1]
      refine ⟨a + h, add_mem haH hh, (x.1, (ψ : ℕ → G)) :: w', fun y hy => ?_, ?_⟩
      · rcases List.mem_cons.1 hy with h' | h'
        · rw [h']; exact hnl
        · exact hw' y h'
      · rw [pwf_cons, pwf_cons, heq, hpw]
        show (pure a + (v x.1).map (ψ : ℕ → G)) + (pure h + pwf v w')
          = pure (a + h) + ((v x.1).map (ψ : ℕ → G) + pwf v w')
        rw [← add_pure_pure, add_assoc, add_assoc, ← add_assoc ((v x.1).map (ψ : ℕ → G)), ← add_comm_pure,
          add_assoc]

/-- Every null ultrafilter is a translated normalized word. -/
theorem exists_normal (hsel : ∀ i, IsSel (v i)) (hiso : ∀ i j, i ≠ j → ¬ Iso (v i) (v j))
    (W : Ultrafilter G) (hW : (W : Filter G) ∈ genFam (ultraGen (fam v cls f))) :
    ∃ h ∈ Hf v cls f, ∃ w, Normal v cls f w ∧ W = pure h + pwf v w := by
  obtain ⟨w, hw, hpw⟩ := exists_fword v cls f hsel hiso W hW
  obtain ⟨h, hh, w', hw', h1⟩ := normalize v cls f w hw
  exact ⟨h, hh, w', hw', by rw [← hpw, h1]⟩

/-- The translation and the normalized word are determined by the ultrafilter. -/
theorem normal_form_unique (hsel : ∀ i, IsSel (v i)) (hiso : ∀ i j, i ≠ j → ¬ Iso (v i) (v j))
    (w w' : List (I × (ℕ → G))) (hw : Normal v cls f w) (hw' : Normal v cls f w') (h1 h2 : G)
    (h : (pure h1 : Ultrafilter G) + pwf v w = pure h2 + pwf v w') : h1 = h2 ∧ w = w' := by
  refine fun_normal_unique v hsel hiso w w' (normal_free v cls f w hw) (normal_free v cls f w' hw') h1 h2 ?_ h
  intro x hx y hy hxy hdiff
  obtain ⟨i, φ⟩ := x
  obtain ⟨i', ψ⟩ := y
  change i = i' at hxy
  subst hxy
  obtain ⟨⟨hφ, hoφ⟩, _⟩ := hw _ hx
  obtain ⟨⟨hψ, hoψ⟩, _⟩ := hw' _ hy
  have h3 : Quotient.mk (sameCoset v cls f i) ⟨φ, hφ⟩ = Quotient.mk (sameCoset v cls f i) ⟨ψ, hψ⟩ :=
    Quotient.sound hdiff
  change (Quotient.mk (sameCoset v cls f i) ⟨φ, hφ⟩).out = ⟨φ, hφ⟩ at hoφ
  change (Quotient.mk (sameCoset v cls f i) ⟨ψ, hψ⟩).out = ⟨ψ, hψ⟩ at hoψ
  rw [h3, hoψ] at hoφ
  exact (congrArg Subtype.val hoφ).symm

theorem null_points_iff (hsel : ∀ i, IsSel (v i)) (hiso : ∀ i j, i ≠ j → ¬ Iso (v i) (v j)) (g : G) :
    (pure g : Filter G) ∈ genFam (ultraGen (fam v cls f)) ↔ g ∈ Hf v cls f := by
  refine ⟨fun hg => ?_, Hf_le_null v cls f g⟩
  obtain ⟨h, hh, w, hw, hW⟩ := exists_normal v cls f hsel hiso (pure g) (by rwa [Ultrafilter.coe_pure])
  have hw0 : w = [] := by
    by_contra hne
    have h1 := pwf_free v w (normal_free v cls f w hw) hne
    have h2 : ({g} : Set G) ∈ (pure h : Ultrafilter G) + pwf v w := by rw [← hW]; exact rfl
    rw [mem_add_pure_left] at h2
    have h3 : ({g - h} : Set G) ∈ pwf v w := by
      refine Filter.mem_of_superset h2 (fun z hz => ?_)
      have h4 : h + z = g := hz
      rw [mem_singleton_iff, ← h4]; abel
    obtain ⟨b, _, h5⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h3
    exact h1 b h5
  subst hw0
  have h1 : (pure g : Ultrafilter G) = pure h := by
    rw [hW]
    show (pure h : Ultrafilter G) + pure 0 = pure h
    rw [add_pure_pure, add_zero]
  rw [Ultrafilter.pure_injective h1]
  exact hh

theorem no_idempotent (hsel : ∀ i, IsSel (v i)) (hiso : ∀ i j, i ≠ j → ¬ Iso (v i) (v j))
    (p : Ultrafilter G) (hp : (p : Filter G) ∈ genFam (ultraGen (fam v cls f))) (hfree : ∀ a, p ≠ pure a) :
    p + p ≠ p := by
  intro hpp
  obtain ⟨h, hh, w, hw, hW⟩ := exists_normal v cls f hsel hiso p hp
  have hne : w ≠ [] := by
    intro hw0
    subst hw0
    refine hfree h ?_
    rw [hW]
    show (pure h : Ultrafilter G) + pure 0 = pure h
    rw [add_pure_pure, add_zero]
  have h2 : p + p = pure (h + h) + pwf v (w ++ w) := by
    rw [hW, pwf_append, ← add_pure_pure, add_assoc, add_assoc, ← add_assoc (pwf v w), ← add_comm_pure,
      add_assoc]
  have h3 : (pure (h + h) : Ultrafilter G) + pwf v (w ++ w) = pure h + pwf v w := by
    rw [← h2, hpp, hW]
  have hww : Normal v cls f (w ++ w) := fun x hx => by
    rcases List.mem_append.1 hx with h' | h'
    · exact hw x h'
    · exact hw x h'
  have h4 := (normal_form_unique v cls f hsel hiso (w ++ w) w hww hw (h + h) h h3).2
  have h5 := congrArg List.length h4
  rw [List.length_append] at h5
  exact hne (List.length_eq_zero_iff.1 (by omega))

/-! ### Any family of selective ultrafilters on a countably infinite group -/

section Family

variable [Countable G] [Infinite G]

theorem exists_presentation (S : Set (Ultrafilter G)) (hS : ∀ u ∈ S, IsSel u) :
    ∃ (I : Type) (v : I → Ultrafilter ℕ) (cls : S → I) (f : S → ℕ → G),
      (∀ i, IsSel (v i)) ∧ (∀ i j, i ≠ j → ¬ Iso (v i) (v j)) ∧ fam v cls f = S ∧
        (∀ u : S, (v (cls u)).map (f u) = u.1) ∧ ∀ u, Function.Bijective (f u) := by
  classical
  obtain ⟨e⟩ : Nonempty (ℕ ≃ G) := by
    have := Encodable.ofCountable G
    have := Denumerable.ofEncodableOfInfinite G
    exact ⟨(Denumerable.eqv G).symm⟩
  let om : S → Ultrafilter ℕ := fun u => u.1.map e.symm
  have homsel : ∀ u, IsSel (om u) := fun u => isSel_map_of_injective (hS _ u.2) e.symm e.symm.injective
  let st : Setoid S := ⟨fun a b => Iso (om a) (om b),
    ⟨fun a => ⟨Equiv.refl ℕ, by
        rw [show ((Equiv.refl ℕ : Equiv.Perm ℕ) : ℕ → ℕ) = id from rfl, Ultrafilter.map_id]⟩,
      fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
  let v : Quotient st → Ultrafilter ℕ := fun i => om i.out
  let cls : S → Quotient st := fun u => Quotient.mk st u
  have hπ : ∀ u : S, ∃ π : Equiv.Perm ℕ, (v (cls u)).map π = om u := fun u => Quotient.mk_out (s := st) u
  choose π hπ using hπ
  let f : S → ℕ → G := fun u => e ∘ π u
  have hmap : ∀ u : S, (v (cls u)).map (f u) = u.1 := by
    intro u
    show (v (cls u)).map (e ∘ π u) = u.1
    rw [← Ultrafilter.map_map, hπ u]
    show (u.1.map e.symm).map e = u.1
    rw [Ultrafilter.map_map]
    have h3 : (e : ℕ → G) ∘ (e.symm : G → ℕ) = id := by funext x; simp
    rw [h3, Ultrafilter.map_id]
  refine ⟨Quotient st, v, cls, f, fun i => homsel _, fun i j hij hiso => hij ?_, ?_, hmap, fun u => ?_⟩
  · have h1 : Quotient.mk st i.out = Quotient.mk st j.out := Quotient.sound hiso
    rwa [Quotient.out_eq, Quotient.out_eq] at h1
  · ext w
    constructor
    · rintro ⟨u, rfl⟩
      show (v (cls u)).map (f u) ∈ S
      rw [hmap u]; exact u.2
    · intro hw
      exact ⟨⟨w, hw⟩, hmap ⟨w, hw⟩⟩
  · exact e.bijective.comp (π u).bijective

theorem family_no_idempotent (S : Set (Ultrafilter G)) (hS : ∀ u ∈ S, IsSel u) :
    ∀ p : Ultrafilter G, (p : Filter G) ∈ genFam (ultraGen S) → (∀ a, p ≠ pure a) → p + p ≠ p := by
  obtain ⟨I, v, cls, f, hsel, hiso, hfam, _, _⟩ := exists_presentation S hS
  intro p hp hfree
  rw [← hfam] at hp
  exact no_idempotent v cls f hsel hiso p hp hfree

theorem family_nbhd (S : Set (Ultrafilter G)) (hS : ∀ u ∈ S, IsSel u) (N : Filter G) :
    (IsNbhdFilter N ∧ N ∈ genFam (ultraGen S)) ↔
      ∃ F : AddSubgroup G, (F : Set G).Finite ∧ (∀ g ∈ F, (pure g : Filter G) ∈ genFam (ultraGen S)) ∧
        N = 𝓟 (F : Set G) :=
  nbhd_iff_of_no_idempotent (genFam_nullFamily _) (family_no_idempotent S hS) N

theorem family_coarsest_iff (S : Set (Ultrafilter G)) (hS : ∀ u ∈ S, IsSel u) :
    (∃ N0 : Filter G, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen S)) ∧
        ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen S) → N ≤ N0) ↔
      {g : G | (pure g : Filter G) ∈ genFam (ultraGen S) ∧ IsOfFinAddOrder g}.Finite :=
  coarsest_iff (genFam_nullFamily _) (family_nbhd S hS)

theorem family_not_pretopological (S : Set (Ultrafilter G)) (hS : ∀ u ∈ S, IsSel u) (hne : S.Nonempty) :
    vic (genFam (ultraGen S)) ∉ genFam (ultraGen S) := by
  intro hvic
  have hC : NullFamily (genFam (ultraGen S)) := genFam_nullFamily _
  obtain ⟨u, hu⟩ := hne
  have hV : IsNbhdFilter (vic (genFam (ultraGen S))) := by
    refine ⟨fun A hA => vic_zero_mem hC hA, fun A hA => vic_neg hC hA, fun A hA => ?_⟩
    have h1 : Filter.map₂ (· + ·) (vic (genFam (ultraGen S))) (vic (genFam (ultraGen S)))
        ≤ vic (genFam (ultraGen S)) := le_vic (hC.add _ hvic _ hvic)
    obtain ⟨B1, hB1, B2, hB2, h2⟩ := Filter.mem_map₂_iff.1 (h1 hA)
    exact ⟨B1 ∩ B2, Filter.inter_mem hB1 hB2, fun x hx y hy => h2 (mem_image2_of_mem hx.1 hy.2)⟩
  obtain ⟨F, hFfin, _, hF⟩ := (family_nbhd S hS _).1 ⟨hV, hvic⟩
  have h1 : (u : Filter G) ≤ 𝓟 (F : Set G) := hF ▸ le_vic (ultra_mem_genFam S u hu)
  have h2 : (F : Set G) ∈ u := h1 (mem_principal_self _)
  obtain ⟨b, _, h3⟩ := Ultrafilter.eq_pure_of_finite_mem hFfin h2
  exact (hS u hu).1 b h3

/-- For a finite family the group of null points is generated by at most as many elements. -/
theorem family_finite_generators (S : Set (Ultrafilter G)) (hS : ∀ u ∈ S, IsSel u) (hfin : S.Finite) :
    ∃ T : Finset G, T.card ≤ S.ncard ∧
      ∀ g : G, (pure g : Filter G) ∈ genFam (ultraGen S) ↔ g ∈ AddSubgroup.closure (T : Set G) := by
  classical
  obtain ⟨I, v, cls, f, hsel, hiso, hfam, _, _⟩ := exists_presentation S hS
  have : Finite S := hfin.to_subtype
  have : Fintype S := Fintype.ofFinite S
  set Is : Finset I := Finset.univ.image cls with hIs
  -- generators for one class
  have hclass : ∀ i : I, ∃ T : Finset G, T.card ≤ (Finset.univ.filter (fun u : S => cls u = i)).card ∧
      (∀ t ∈ T, ∃ φ ∈ Lf cls f i, (v i).map φ = pure t) ∧
      ∀ g, (∃ φ ∈ Lf cls f i, (v i).map φ = pure g) → g ∈ AddSubgroup.closure (T : Set G) := by
    intro i
    set Ci : Finset S := Finset.univ.filter (fun u : S => cls u = i) with hCi
    set n : ℕ := Ci.card with hn
    let gen : Fin n → (ℕ → G) := fun k => f (Ci.equivFin.symm k).1
    let lin : (Fin n → ℤ) →ₗ[ℤ] (ℕ → G) := Fintype.linearCombination ℤ gen
    have hlin : ∀ c : Fin n → ℤ, lin c = ∑ k, c k • gen k := fun c => Fintype.linearCombination_apply ℤ gen c
    have hLr : ∀ φ ∈ Lf cls f i, ∃ c : Fin n → ℤ, lin c = φ := by
      intro φ hφ
      have hle : Lf cls f i ≤ (LinearMap.range lin).toAddSubgroup := by
        refine (AddSubgroup.closure_le _).2 ?_
        rintro ψ ⟨u, hu, rfl⟩
        have huC : u ∈ Ci := Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩
        refine ⟨Pi.single (Ci.equivFin ⟨u, huC⟩) 1, ?_⟩
        show lin (Pi.single (Ci.equivFin ⟨u, huC⟩) 1) = f u
        rw [hlin, Finset.sum_eq_single (Ci.equivFin ⟨u, huC⟩)]
        · rw [Pi.single_eq_same, one_smul]
          show f (Ci.equivFin.symm (Ci.equivFin ⟨u, huC⟩)).1 = f u
          rw [Equiv.symm_apply_apply]
        · intro k _ hk
          rw [Pi.single_eq_of_ne hk, zero_smul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      exact hle hφ
    have hlinL : ∀ c : Fin n → ℤ, lin c ∈ Lf cls f i := by
      intro c
      rw [hlin]
      refine AddSubgroup.sum_mem _ (fun k _ => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) _)
      exact ⟨(Ci.equivFin.symm k).1, (Finset.mem_filter.1 (Ci.equivFin.symm k).2).2, rfl⟩
    let M : Submodule ℤ (Fin n → ℤ) :=
      { carrier := {c | ∃ g, (v i).map (lin c) = pure g}
        zero_mem' := by
          refine ⟨0, ?_⟩
          rw [map_zero]
          refine Ultrafilter.coe_injective ?_
          rw [Ultrafilter.coe_map, Ultrafilter.coe_pure]
          exact Filter.map_const
        add_mem' := fun {a b} ha hb => by
          obtain ⟨x, hx⟩ := ha
          obtain ⟨y, hy⟩ := hb
          refine ⟨x + y, ?_⟩
          have h1 : (v i).map (lin (a + b) - lin b) = pure x := by
            have : lin (a + b) - lin b = lin a := by rw [map_add, add_sub_cancel_right]
            rw [this, hx]
          rw [map_eq_pure_add v i (lin (a + b)) (lin b) x h1, hy, add_pure_pure]
        smul_mem' := fun k a ha => by
          obtain ⟨x, hx⟩ := ha
          refine ⟨k • x, ?_⟩
          have h1 : ({x} : Set G) ∈ (v i).map (lin a) := by rw [hx]; exact rfl
          have h2 : ({k • x} : Set G) ∈ (v i).map (lin (k • a)) := by
            have h3 : {m : ℕ | lin a m ∈ ({x} : Set G)} ∈ v i := h1
            show {m : ℕ | lin (k • a) m ∈ ({k • x} : Set G)} ∈ v i
            refine Filter.mem_of_superset h3 (fun m hm => ?_)
            have h4 : lin a m = x := hm
            show lin (k • a) m = k • x
            rw [map_smul, Pi.smul_apply, h4]
          obtain ⟨b, hb, h5⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h2
          rw [h5, mem_singleton_iff.1 hb] }
    have hM : ∀ c : M, ∃ g, (v i).map (lin c.1) = pure g := fun c => c.2
    choose val hval using hM
    have hvaladd : ∀ a b : M, val (a + b) = val a + val b := by
      intro a b
      have h1 : (v i).map (lin (a + b : M).1 - lin b.1) = pure (val a) := by
        have : lin (a + b : M).1 - lin b.1 = lin a.1 := by
          rw [Submodule.coe_add, map_add, add_sub_cancel_right]
        rw [this, hval a]
      have h2 := map_eq_pure_add v i (lin (a + b : M).1) (lin b.1) (val a) h1
      rw [hval (a + b), hval b, add_pure_pure] at h2
      exact Ultrafilter.pure_injective h2
    let lam : M →+ G := AddMonoidHom.mk' val hvaladd
    have hrank : Module.finrank ℤ M ≤ n := by
      have h1 := Submodule.finrank_le M
      rwa [Module.finrank_fin_fun] at h1
    let bs := Module.finBasis ℤ M
    refine ⟨Finset.univ.image (fun k => lam (bs k)), ?_, ?_, ?_⟩
    · exact Finset.card_image_le.trans (by simpa using hrank)
    · intro t ht
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 ht
      exact ⟨lin (bs k).1, hlinL _, hval (bs k)⟩
    · rintro g ⟨φ, hφ, hg⟩
      obtain ⟨c, hc⟩ := hLr φ hφ
      have hcM : c ∈ M := ⟨g, by rw [hc, hg]⟩
      have h1 : val ⟨c, hcM⟩ = g := by
        have h2 := hval ⟨c, hcM⟩
        change (v i).map (lin c) = pure (val ⟨c, hcM⟩) at h2
        rw [hc, hg] at h2
        exact (Ultrafilter.pure_injective h2).symm
      rw [← h1]
      show lam ⟨c, hcM⟩ ∈ _
      rw [← bs.sum_repr ⟨c, hcM⟩, map_sum]
      refine AddSubgroup.sum_mem _ (fun k _ => ?_)
      rw [map_zsmul]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Finset.mem_coe.2
        (Finset.mem_image_of_mem (fun k => lam (bs k)) (Finset.mem_univ k)))) _
  choose T hTcard hTmem hTgen using hclass
  refine ⟨Is.biUnion T, ?_, fun g => ?_⟩
  · refine Finset.card_biUnion_le.trans ?_
    have h1 : ∑ i ∈ Is, (T i).card ≤ ∑ i ∈ Is, (Finset.univ.filter (fun u : S => cls u = i)).card :=
      Finset.sum_le_sum (fun i _ => hTcard i)
    have h2 : ∑ i ∈ Is, (Finset.univ.filter (fun u : S => cls u = i)).card = Fintype.card S := by
      rw [← Finset.card_univ]
      exact (Finset.card_eq_sum_card_fiberwise (fun u _ => Finset.mem_image_of_mem cls (Finset.mem_univ u))).symm
    have h3 : Fintype.card S = S.ncard := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    omega
  · rw [← hfam, null_points_iff v cls f hsel hiso g]
    constructor
    · intro hg
      have hle : Hf v cls f ≤ AddSubgroup.closure ((Is.biUnion T : Finset G) : Set G) := by
        refine (AddSubgroup.closure_le _).2 ?_
        rintro x ⟨i, φ, hφ, hx⟩
        by_cases hi : i ∈ Is
        · have h1 := hTgen i x ⟨φ, hφ, hx⟩
          exact AddSubgroup.closure_mono (Finset.coe_subset.2 (Finset.subset_biUnion_of_mem T hi)) h1
        · have h1 : Lf cls f i = ⊥ := by
            refine (AddSubgroup.closure_eq_bot_iff).2 ?_
            rintro ψ ⟨u, hu, _⟩
            exact absurd (hu ▸ Finset.mem_image_of_mem cls (Finset.mem_univ u)) hi
          rw [h1, AddSubgroup.mem_bot] at hφ
          have h2 : (v i).map φ = pure 0 := by
            rw [hφ]
            refine Ultrafilter.coe_injective ?_
            rw [Ultrafilter.coe_map, Ultrafilter.coe_pure]
            exact Filter.map_const
          have h3 : x = 0 := Ultrafilter.pure_injective (hx.symm.trans h2)
          rw [h3]
          exact zero_mem _
      exact hle hg
    · intro hg
      have hle : AddSubgroup.closure ((Is.biUnion T : Finset G) : Set G) ≤ Hf v cls f := by
        refine (AddSubgroup.closure_le _).2 (fun t ht => ?_)
        obtain ⟨i, _, hti⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 ht)
        obtain ⟨φ, hφ, h1⟩ := hTmem i t hti
        exact AddSubgroup.subset_closure ⟨i, φ, hφ, h1⟩
      exact hle hg

theorem family_finite_coarsest (S : Set (Ultrafilter G)) (hS : ∀ u ∈ S, IsSel u) (hfin : S.Finite) :
    ∃ N0 : Filter G, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen S)) ∧
      ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen S) → N ≤ N0 := by
  obtain ⟨T, _, hT⟩ := family_finite_generators S hS hfin
  rw [family_coarsest_iff S hS]
  exact (finite_torsion_closure (T : Set G) T.finite_toSet).subset (fun g hg => ⟨(hT g).1 hg.1, hg.2⟩)

theorem family_torsion_coarsest (S : Set (Ultrafilter G)) (hS : ∀ u ∈ S, IsSel u)
    (htor : {g : G | IsOfFinAddOrder g}.Finite) :
    ∃ N0 : Filter G, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen S)) ∧
      ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen S) → N ≤ N0 := by
  rw [family_coarsest_iff S hS]
  exact htor.subset (fun g hg => hg.2)

theorem family_torsionfree_trivial (S : Set (Ultrafilter G)) (hS : ∀ u ∈ S, IsSel u)
    (htf : ∀ g : G, IsOfFinAddOrder g → g = 0) (N : Filter G) (hN : IsNbhdFilter N)
    (hNC : N ∈ genFam (ultraGen S)) : N = pure 0 := by
  obtain ⟨F, hF, _, rfl⟩ := (family_nbhd S hS N).1 ⟨hN, hNC⟩
  have h1 : F = ⊥ := by
    rw [AddSubgroup.eq_bot_iff_forall]
    intro g hg
    refine htf g ?_
    have h2 : (AddSubgroup.zmultiples g : Set G).Finite := hF.subset (AddSubgroup.zmultiples_le_of_mem hg)
    exact finite_zmultiples.1 h2
  rw [h1, AddSubgroup.coe_bot, principal_singleton]

/-! ### Translates of one selective ultrafilter -/

/-- The translates of `u`. -/
def allTranslates (u : Ultrafilter G) : Set (Ultrafilter G) := Set.range (fun g : G => u.map (fun x => g + x))

theorem allTranslates_sel (u : Ultrafilter G) (hu : IsSel u) : ∀ w ∈ allTranslates u, IsSel w := by
  rintro w ⟨g, rfl⟩
  exact isSel_map_of_injective hu _ (add_right_injective g)

theorem translates_all_null (u : Ultrafilter G) (g : G) :
    (pure g : Filter G) ∈ genFam (ultraGen (allTranslates u)) := by
  have hC : NullFamily (genFam (ultraGen (allTranslates u))) := genFam_nullFamily _
  refine pure_mem_of_translate hC u g (ultra_mem_genFam _ _ ⟨g, rfl⟩) (ultra_mem_genFam _ _ ⟨0, ?_⟩)
  have : (fun x : G => (0 : G) + x) = id := by funext x; simp
  show u.map (fun x => (0 : G) + x) = u
  rw [this, Ultrafilter.map_id]

theorem allTranslates_coarsest_iff (u : Ultrafilter G) (hu : IsSel u) :
    (∃ N0 : Filter G, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen (allTranslates u))) ∧
        ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen (allTranslates u)) → N ≤ N0) ↔
      {g : G | IsOfFinAddOrder g}.Finite := by
  rw [family_coarsest_iff _ (allTranslates_sel u hu)]
  have : {g : G | (pure g : Filter G) ∈ genFam (ultraGen (allTranslates u)) ∧ IsOfFinAddOrder g}
      = {g : G | IsOfFinAddOrder g} := by
    ext g
    simp only [mem_setOf_eq, translates_all_null u g, true_and]
  rw [this]

/-- If there is a selective ultrafilter, all selective families on `G` have a coarsest group topology of this kind
exactly when `G` has only finitely many elements of finite order. -/
theorem all_coarsest_iff_finite_torsion (hex : ∃ u : Ultrafilter ℕ, IsSel u) :
    (∀ S : Set (Ultrafilter G), (∀ u ∈ S, IsSel u) →
        ∃ N0 : Filter G, (IsNbhdFilter N0 ∧ N0 ∈ genFam (ultraGen S)) ∧
          ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen S) → N ≤ N0) ↔
      {g : G | IsOfFinAddOrder g}.Finite := by
  refine ⟨fun h => ?_, fun h S hS => family_torsion_coarsest S hS h⟩
  obtain ⟨u0, hu0⟩ := hex
  obtain ⟨e⟩ : Nonempty (ℕ ≃ G) := by
    have := Encodable.ofCountable G
    have := Denumerable.ofEncodableOfInfinite G
    exact ⟨(Denumerable.eqv G).symm⟩
  have hu : IsSel (u0.map e) := isSel_map_of_injective hu0 e e.injective
  exact (allTranslates_coarsest_iff _ hu).1 (h _ (allTranslates_sel _ hu))

end Family

/-! ### The group of null points and the closure of `0` -/

/-- With pairwise non-isomorphic selective ultrafilters indexed by `Option ℕ`: a family on `ℤ × ⊕ ℤ/2` whose null
points are the even integers, whose only symmetric halvable null filter with `0` is that of `0`, and whose topological
modification is indiscrete. -/
theorem closure_example (w : Option ℕ → Ultrafilter ℕ) (hsel : ∀ i, IsSel (w i))
    (hiso : ∀ i j, i ≠ j → ¬ Iso (w i) (w j)) :
    ∃ S : Set (Ultrafilter (ℤ × (ℕ →₀ ZMod 2))), (∀ u ∈ S, IsSel u) ∧
      (∀ g : ℤ × (ℕ →₀ ZMod 2), (pure g : Filter (ℤ × (ℕ →₀ ZMod 2))) ∈ genFam (ultraGen S) ↔
        g ∈ AddSubgroup.zmultiples ((2, 0) : ℤ × (ℕ →₀ ZMod 2))) ∧
      (∀ N : Filter (ℤ × (ℕ →₀ ZMod 2)), IsNbhdFilter N → N ∈ genFam (ultraGen S) → N = pure 0) ∧
      ∀ O : Set (ℤ × (ℕ →₀ ZMod 2)), IsOpenMod (genFam (ultraGen S)) O → O.Nonempty → O = Set.univ := by
  classical
  set f : Option ℕ → ℕ → ℤ × (ℕ →₀ ZMod 2) := fun i n =>
    match i with
    | none => (1, Finsupp.single n 1)
    | some k => (2 * (n : ℤ), Finsupp.single k 1) with hf
  have hfinj : ∀ i, Function.Injective (f i) := by
    intro i a b hab
    cases i with
    | none =>
      have h1 : Finsupp.single a (1 : ZMod 2) = Finsupp.single b 1 := congrArg Prod.snd hab
      exact Finsupp.single_left_injective one_ne_zero h1
    | some k =>
      have h1 : (2 : ℤ) * a = 2 * b := congrArg Prod.fst hab
      omega
  set S : Set (Ultrafilter (ℤ × (ℕ →₀ ZMod 2))) := fam w id f with hSdef
  have hSsel : ∀ u ∈ S, IsSel u := by
    rintro u ⟨i, rfl⟩
    exact isSel_map_of_injective (hsel _) _ (hfinj i)
  have h2 : ∀ x : ℕ →₀ ZMod 2, (2 : ℤ) • x = 0 := by
    intro x
    refine Finsupp.ext (fun n => ?_)
    rw [Finsupp.smul_apply, Finsupp.zero_apply]
    have : ∀ a : ZMod 2, (2 : ℤ) • a = 0 := by decide
    exact this _
  have hLf : ∀ i, ∀ φ ∈ Lf id f i, ∃ c : ℤ, c • f i = φ := by
    intro i φ hφ
    have h1 : {ψ : ℕ → ℤ × (ℕ →₀ ZMod 2) | ∃ j, id j = i ∧ ψ = f j} = {f i} := by
      ext ψ
      constructor
      · rintro ⟨j, hj, rfl⟩
        rw [show j = i from hj]
        rfl
      · intro h
        exact ⟨i, rfl, h⟩
    unfold Lf at hφ
    rw [h1] at hφ
    exact AddSubgroup.mem_closure_singleton.1 hφ
  have hval : ∀ i (c : ℤ) (g : ℤ × (ℕ →₀ ZMod 2)), (w i).map (c • f i) = pure g →
      g ∈ AddSubgroup.zmultiples ((2, 0) : ℤ × (ℕ →₀ ZMod 2)) := by
    intro i c g hg
    have h1 : ({g} : Set (ℤ × (ℕ →₀ ZMod 2))) ∈ (w i).map (c • f i) := by rw [hg]; exact rfl
    have h3 : {n : ℕ | c • f i n = g} ∈ w i := h1
    have h4 : {n : ℕ | c • f i n = g}.Infinite := infinite_of_mem (hsel i).1 h3
    obtain ⟨a, ha⟩ := h4.nonempty
    obtain ⟨b, hb, hba⟩ := h4.exists_gt a
    have hab : c • f i a = c • f i b := ha.trans hb.symm
    cases i with
    | none =>
      have h5 : c • Finsupp.single a (1 : ZMod 2) = c • Finsupp.single b 1 := congrArg Prod.snd hab
      have h6 : (c : ZMod 2) = 0 := by
        have h7 := DFunLike.congr_fun h5 a
        rw [Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne (Nat.ne_of_lt hba), smul_zero, zsmul_one] at h7
        exact h7
      obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd c 2).1 h6
      refine AddSubgroup.mem_zmultiples_iff.2 ⟨m, ?_⟩
      rw [← ha]
      refine Prod.ext ?_ ?_
      · show m • (2 : ℤ) = c • (1 : ℤ)
        rw [smul_eq_mul, smul_eq_mul, hm]
        push_cast
        ring
      · show m • (0 : ℕ →₀ ZMod 2) = c • Finsupp.single a (1 : ZMod 2)
        have h8 : c = m * 2 := by rw [hm]; push_cast; ring
        rw [smul_zero, h8, mul_smul, h2, smul_zero]
    | some k =>
      have h5 : c • ((2 : ℤ) * a) = c • ((2 : ℤ) * b) := congrArg Prod.fst hab
      have h6 : c = 0 := by
        rw [smul_eq_mul, smul_eq_mul] at h5
        by_contra hc
        have h7 : (2 : ℤ) * a = 2 * b := mul_left_cancel₀ hc h5
        omega
      have h8 : g = 0 := by rw [← ha, h6, zero_smul]
      rw [h8]
      exact zero_mem _
  have h20 : ((2, 0) : ℤ × (ℕ →₀ ZMod 2)) ∈ Hf w id f := by
    refine AddSubgroup.subset_closure ⟨none, (2 : ℤ) • f none,
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure
        (show f none ∈ {ψ | ∃ j, id j = (none : Option ℕ) ∧ ψ = f j} from ⟨none, rfl, rfl⟩)) _, ?_⟩
    have : (2 : ℤ) • f none = fun _ => ((2, 0) : ℤ × (ℕ →₀ ZMod 2)) := by
      funext n
      refine Prod.ext ?_ ?_
      · show (2 : ℤ) • (1 : ℤ) = 2
        simp
      · exact h2 _
    rw [this]
    refine Ultrafilter.coe_injective ?_
    rw [Ultrafilter.coe_map, Ultrafilter.coe_pure]
    exact Filter.map_const
  have hHf : Hf w id f = AddSubgroup.zmultiples ((2, 0) : ℤ × (ℕ →₀ ZMod 2)) := by
    refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) (AddSubgroup.zmultiples_le_of_mem h20)
    rintro g ⟨i, φ, hφ, hg⟩
    obtain ⟨c, hc⟩ := hLf i φ hφ
    rw [← hc] at hg
    exact hval i c g hg
  have hpts : ∀ g : ℤ × (ℕ →₀ ZMod 2), (pure g : Filter (ℤ × (ℕ →₀ ZMod 2))) ∈ genFam (ultraGen S) ↔
      g ∈ AddSubgroup.zmultiples ((2, 0) : ℤ × (ℕ →₀ ZMod 2)) := by
    intro g
    rw [← hHf]
    exact null_points_iff w id f hsel hiso g
  have hC : NullFamily (genFam (ultraGen S)) := genFam_nullFamily _
  refine ⟨S, hSsel, hpts, fun N hN hNC => ?_, fun O hO hne => ?_⟩
  · have : Infinite (ℤ × (ℕ →₀ ZMod 2)) := inferInstance
    obtain ⟨F, hF, hFH, rfl⟩ := (family_nbhd S hSsel N).1 ⟨hN, hNC⟩
    have h1 : F = ⊥ := by
      rw [AddSubgroup.eq_bot_iff_forall]
      intro g hg
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 ((hpts g).1 (hFH g hg))
      have h3 : (AddSubgroup.zmultiples g : Set (ℤ × (ℕ →₀ ZMod 2))).Finite :=
        hF.subset (AddSubgroup.zmultiples_le_of_mem hg)
      have h4 : IsOfFinAddOrder g := finite_zmultiples.1 h3
      obtain ⟨n, hn, hng⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 h4
      have h5 : (n : ℤ) * (m * 2) = 0 := by
        have h6 := congrArg Prod.fst hng
        rw [← hm] at h6
        simpa [Prod.smul_fst, smul_eq_mul] using h6
      have h7 : m = 0 := by
        have h8 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
        rcases mul_eq_zero.1 h5 with h | h
        · exact absurd h h8
        · omega
      rw [← hm, h7, zero_smul]
    rw [h1, AddSubgroup.coe_bot, principal_singleton]
  · have hS' : ∀ i, (w i).map (f i) ∈ S := fun i => ⟨i, rfl⟩
    have hstep : ∀ y ∈ O, ∀ i, ∃ n, y + f i n ∈ O := by
      intro y hy i
      set F : Filter (ℤ × (ℕ →₀ ZMod 2)) :=
        Filter.map (fun z => y + z) ((w i).map (f i) : Filter (ℤ × (ℕ →₀ ZMod 2))) with hF
      have hFne : F.NeBot := Filter.map_neBot
      have hconv : conv (genFam (ultraGen S)) F y := by
        have h1 : Filter.map (fun z => z - y) F = ((w i).map (f i) : Filter (ℤ × (ℕ →₀ ZMod 2))) := by
          rw [hF, Filter.map_map]
          have : ((fun z => z - y) ∘ fun z : ℤ × (ℕ →₀ ZMod 2) => y + z) = id := by
            funext z; simp
          rw [this, Filter.map_id]
        show Filter.map (fun z => z - y) F ∈ genFam (ultraGen S)
        rw [h1]
        exact ultra_mem_genFam _ _ (hS' i)
      have h3 : O ∈ F := hO y hy F hFne hconv
      have h4 : {n : ℕ | y + f i n ∈ O} ∈ w i := h3
      exact Ultrafilter.nonempty_of_mem h4
    have hH : ∀ y ∈ O, ∀ h ∈ AddSubgroup.zmultiples ((2, 0) : ℤ × (ℕ →₀ ZMod 2)), y + h ∈ O := by
      intro y hy h hh
      have hconv : conv (genFam (ultraGen S)) (pure (y + h)) y := by
        show Filter.map (fun z => z - y) (pure (y + h)) ∈ genFam (ultraGen S)
        rw [Filter.map_pure, add_sub_cancel_left]
        exact (hpts h).2 hh
      exact hO y hy _ pure_neBot hconv
    have he : ∀ y ∈ O, ∀ k, y + (0, Finsupp.single k 1) ∈ O := by
      intro y hy k
      obtain ⟨n, hn⟩ := hstep y hy (some k)
      have h1 := hH _ hn (-(n : ℤ) • ((2, 0) : ℤ × (ℕ →₀ ZMod 2)))
        (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _)
      have h3 : y + f (some k) n + -(n : ℤ) • ((2, 0) : ℤ × (ℕ →₀ ZMod 2)) = y + (0, Finsupp.single k 1) := by
        have h4 : f (some k) n + -(n : ℤ) • ((2, 0) : ℤ × (ℕ →₀ ZMod 2)) = (0, Finsupp.single k 1) := by
          refine Prod.ext ?_ ?_
          · show 2 * (n : ℤ) + -(n : ℤ) • (2 : ℤ) = 0
            rw [smul_eq_mul]; ring
          · show Finsupp.single k (1 : ZMod 2) + -(n : ℤ) • (0 : ℕ →₀ ZMod 2) = Finsupp.single k 1
            rw [smul_zero, add_zero]
        rw [add_assoc, h4]
      rwa [h3] at h1
    have ha : ∀ y ∈ O, y + (1, 0) ∈ O := by
      intro y hy
      obtain ⟨n, hn⟩ := hstep y hy none
      have h1 := he _ hn n
      have h3 : y + f none n + (0, Finsupp.single n 1) = y + (1, 0) := by
        have h4 : f none n + (0, Finsupp.single n 1) = ((1, 0) : ℤ × (ℕ →₀ ZMod 2)) := by
          refine Prod.ext ?_ ?_
          · show (1 : ℤ) + 0 = 1
            simp
          · show Finsupp.single n (1 : ZMod 2) + Finsupp.single n 1 = 0
            rw [← Finsupp.single_add]
            have : (1 : ZMod 2) + 1 = 0 := by decide
            rw [this, Finsupp.single_zero]
        rw [add_assoc, h4]
      rwa [h3] at h1
    have hneg : ∀ y ∈ O, y + (-1, 0) ∈ O := by
      intro y hy
      have h1 := ha _ (hH y hy (-1 • ((2, 0) : ℤ × (ℕ →₀ ZMod 2)))
        (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _))
      have h3 : y + -1 • ((2, 0) : ℤ × (ℕ →₀ ZMod 2)) + (1, 0) = y + (-1, 0) := by
        have h4 : -1 • ((2, 0) : ℤ × (ℕ →₀ ZMod 2)) + (1, 0) = ((-1, 0) : ℤ × (ℕ →₀ ZMod 2)) := by
          refine Prod.ext ?_ ?_
          · show (-1 : ℤ) • (2 : ℤ) + 1 = -1
            simp
          · show (-1 : ℤ) • (0 : ℕ →₀ ZMod 2) + 0 = 0
            simp
        rw [add_assoc, h4]
      rwa [h3] at h1
    let P : AddSubgroup (ℤ × (ℕ →₀ ZMod 2)) :=
      { carrier := {g | (∀ y ∈ O, y + g ∈ O) ∧ ∀ y ∈ O, y + -g ∈ O}
        zero_mem' := ⟨fun y hy => by rwa [add_zero], fun y hy => by rwa [neg_zero, add_zero]⟩
        add_mem' := fun {a b} h1 h3 =>
          ⟨fun y hy => by rw [← add_assoc]; exact h3.1 _ (h1.1 y hy),
            fun y hy => by rw [neg_add, ← add_assoc]; exact h3.2 _ (h1.2 y hy)⟩
        neg_mem' := fun {a} h1 => ⟨h1.2, fun y hy => by rw [neg_neg]; exact h1.1 y hy⟩ }
    have hPa : ((1, 0) : ℤ × (ℕ →₀ ZMod 2)) ∈ P := by
      refine ⟨ha, fun y hy => ?_⟩
      have : -((1, 0) : ℤ × (ℕ →₀ ZMod 2)) = (-1, 0) := by
        refine Prod.ext rfl ?_
        show -(0 : ℕ →₀ ZMod 2) = 0
        exact neg_zero
      rw [this]; exact hneg y hy
    have hPe : ∀ k, ((0, Finsupp.single k 1) : ℤ × (ℕ →₀ ZMod 2)) ∈ P := by
      intro k
      refine ⟨fun y hy => he y hy k, fun y hy => ?_⟩
      have : -((0, Finsupp.single k 1) : ℤ × (ℕ →₀ ZMod 2)) = (0, Finsupp.single k 1) := by
        refine Prod.ext neg_zero ?_
        show -Finsupp.single k (1 : ZMod 2) = Finsupp.single k 1
        rw [← Finsupp.single_neg]
        have : -(1 : ZMod 2) = 1 := by decide
        rw [this]
      rw [this]; exact he y hy k
    have hPall : ∀ g : ℤ × (ℕ →₀ ZMod 2), g ∈ P := by
      intro g
      have h1 : ∀ x : ℕ →₀ ZMod 2, ((0, x) : ℤ × (ℕ →₀ ZMod 2)) ∈ P := by
        intro x
        induction x using Finsupp.induction_linear with
        | zero => exact zero_mem P
        | add a b ha hb =>
          have h3 := add_mem ha hb
          rwa [Prod.mk_add_mk, add_zero] at h3
        | single n a =>
          have h3 : a = 0 ∨ a = 1 := by
            revert a
            decide
          rcases h3 with h | h
          · rw [h, Finsupp.single_zero]; exact zero_mem P
          · rw [h]; exact hPe n
      have h3 : g = g.1 • ((1, 0) : ℤ × (ℕ →₀ ZMod 2)) + (0, g.2) := by
        refine Prod.ext ?_ ?_
        · show g.1 = g.1 • (1 : ℤ) + 0
          simp
        · show g.2 = g.1 • (0 : ℕ →₀ ZMod 2) + g.2
          rw [smul_zero, zero_add]
      rw [h3]
      exact add_mem (zsmul_mem hPa _) (h1 _)
    obtain ⟨y0, hy0⟩ := hne
    refine eq_univ_of_forall (fun g => ?_)
    have h1 := (hPall (g - y0)).1 y0 hy0
    rwa [add_sub_cancel] at h1

/-- Under (S) such a family exists. -/
theorem closure_example_supply (hS : Supply) :
    ∃ S : Set (Ultrafilter (ℤ × (ℕ →₀ ZMod 2))), (∀ u ∈ S, IsSel u) ∧
      (∀ g : ℤ × (ℕ →₀ ZMod 2), (pure g : Filter (ℤ × (ℕ →₀ ZMod 2))) ∈ genFam (ultraGen S) ↔
        g ∈ AddSubgroup.zmultiples ((2, 0) : ℤ × (ℕ →₀ ZMod 2))) ∧
      (∀ N : Filter (ℤ × (ℕ →₀ ZMod 2)), IsNbhdFilter N → N ∈ genFam (ultraGen S) → N = pure 0) ∧
      ∀ O : Set (ℤ × (ℕ →₀ ZMod 2)), IsOpenMod (genFam (ultraGen S)) O → O.Nonempty → O = Set.univ := by
  obtain ⟨T, hsel, hiso, hcard⟩ := hS
  have hinf : T.Infinite := by
    intro hfin
    have h1 : #T < ℵ₀ := lt_aleph0_iff_set_finite.2 hfin
    exact absurd (h1.trans aleph0_lt_continuum) (not_lt.2 hcard)
  have := hinf.to_subtype
  set φ : ℕ ↪ T := Infinite.natEmbedding T with hφ
  set w : Option ℕ → Ultrafilter ℕ := fun i => (φ (Option.elim i 0 (fun k => k + 1))).1 with hw
  have hwinj : ∀ i j : Option ℕ, w i = w j → i = j := by
    intro i j h
    have h1 := φ.injective (Subtype.ext h)
    cases i <;> cases j <;> simp_all
  exact closure_example w (fun i => hsel _ (φ _).2)
    (fun i j hij => hiso _ (φ _).2 _ (φ _).2 (fun h => hij (hwinj i j h)))

end AnySel

end PG
