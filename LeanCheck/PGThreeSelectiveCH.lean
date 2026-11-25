import Mathlib
import LeanCheck.PGThreeSelective
import LeanCheck.PGTwoQuotient
import LeanCheck.PGTwoCofinite

/-!
# PGthree: the cofinite filter at zero is a vicinity filter, under the continuum hypothesis (Lean check)

Scope. Section 3 of the third article (`PGthree.tex`), the parts that use the continuum hypothesis, stated as
`𝔠 = ℵ₁`.

* `exists_selective_avoiding` : every infinite set belongs to a selective ultrafilter different from any given family
  of `ℵ₁` ultrafilters; `exists_dense_selective` : Lemma 3.6;
* `exists_hausdorff_vicinity` : Theorem 3.7;
* `exists_hausdorff_cofin_int` : Theorem 3.7 for `ℤ` together with Corollary 3.8.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Cardinal Ordinal

namespace PG

namespace Sel

/-- A countable family of infinite subsets of `A`, nested modulo finite sets, has an infinite pseudointersection. -/
theorem exists_pseudointersection {J : Type*} [Countable J] (A : Set ℕ) (hA : A.Infinite) (T : J → Set ℕ)
    (hTinf : ∀ j, (T j).Infinite) (hTA : ∀ j, T j ⊆ A)
    (hchain : ∀ j k, (T j \ T k).Finite ∨ (T k \ T j).Finite) :
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ ∀ j, (B \ T j).Finite := by
  classical
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨A, subset_rfl, hA, fun j => (hJ.false j).elim⟩
  obtain ⟨e, he⟩ := exists_surjective_nat J
  have htrans : ∀ X Y Z : Set ℕ, (X \ Y).Finite → (Y \ Z).Finite → (X \ Z).Finite := by
    intro X Y Z h1 h2
    refine (h1.union h2).subset (fun x hx => ?_)
    by_cases h : x ∈ Y
    · exact Or.inr ⟨h, hx.2⟩
    · exact Or.inl ⟨hx.1, h⟩
  have hmin : ∀ n, ∃ m0, ∀ m ≤ n, (T (e m0) \ T (e m)).Finite := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, fun m hm => ?_⟩
      have : m = 0 := by omega
      subst this
      simp
    | succ n ih =>
      obtain ⟨m0, hm0⟩ := ih
      rcases hchain (e m0) (e (n + 1)) with h | h
      · refine ⟨m0, fun m hm => ?_⟩
        rcases Nat.lt_or_ge m (n + 1) with h' | h'
        · exact hm0 m (by omega)
        · have : m = n + 1 := by omega
          rw [this]; exact h
      · refine ⟨n + 1, fun m hm => ?_⟩
        rcases Nat.lt_or_ge m (n + 1) with h' | h'
        · exact htrans _ _ _ h (hm0 m (by omega))
        · have : m = n + 1 := by omega
          rw [this]; simp
  set D : ℕ → Set ℕ := fun n => {x | x ∈ A ∧ ∀ m ≤ n, x ∈ T (e m)} with hD
  have hDinf : ∀ n, (D n).Infinite := by
    intro n
    obtain ⟨m0, hm0⟩ := hmin n
    have hfin : (⋃ m ∈ Iic n, (T (e m0) \ T (e m))).Finite :=
      (finite_Iic n).biUnion (fun m hm => hm0 m hm)
    refine ((hTinf (e m0)).sdiff hfin).mono (fun x hx => ⟨hTA _ hx.1, fun m hm => ?_⟩)
    by_contra h
    exact hx.2 (mem_iUnion₂.2 ⟨m, hm, hx.1, h⟩)
  have hpick : ∀ n (b : ℕ), ∃ x, x ∈ D n ∧ b < x := fun n b => by
    obtain ⟨x, hx, hbx⟩ := (hDinf n).exists_gt b
    exact ⟨x, hx, hbx⟩
  choose pick hpickD hpickgt using hpick
  let x : ℕ → ℕ := fun n => Nat.rec (pick 0 0) (fun k y => pick (k + 1) y) n
  have hxsucc : ∀ n, x (n + 1) = pick (n + 1) (x n) := fun n => rfl
  have hxD : ∀ n, x n ∈ D n := by
    intro n
    cases n with
    | zero => exact hpickD 0 0
    | succ n => rw [hxsucc]; exact hpickD _ _
  have hxmono : StrictMono x := strictMono_nat_of_lt_succ (fun n => by rw [hxsucc]; exact hpickgt _ _)
  refine ⟨range x, ?_, infinite_range_of_injective hxmono.injective, fun j => ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact (hxD n).1
  obtain ⟨m, rfl⟩ := he j
  refine ((finite_Iio m).image x).subset ?_
  rintro _ ⟨⟨n, rfl⟩, hn⟩
  refine ⟨n, ?_, rfl⟩
  by_contra h
  exact hn ((hxD n).2 m (not_lt.1 h))

/-- Shrink an infinite set so that `f` is constant or injective on it and it leaves the ultrafilter `z`. -/
theorem exists_shrink (B : Set ℕ) (hB : B.Infinite) (f : ℕ → ℕ) (z : Ultrafilter ℕ) :
    ∃ C : Set ℕ, C ⊆ B ∧ C.Infinite ∧ ((∃ c, ∀ x ∈ C, f x = c) ∨ InjOn f C) ∧ C ∉ z := by
  obtain ⟨C1, h1B, h1inf, h1f⟩ :
      ∃ C1 : Set ℕ, C1 ⊆ B ∧ C1.Infinite ∧ ((∃ c, ∀ x ∈ C1, f x = c) ∨ InjOn f C1) := by
    by_cases h : ∃ c, {x | x ∈ B ∧ f x = c}.Infinite
    · obtain ⟨c, hc⟩ := h
      exact ⟨_, fun x hx => hx.1, hc, Or.inl ⟨c, fun x hx => hx.2⟩⟩
    · push Not at h
      obtain ⟨C, hCB, hbij⟩ := Set.exists_subset_bijOn B f
      refine ⟨C, hCB, ?_, Or.inr hbij.injOn⟩
      have himg : (f '' B).Infinite := by
        intro hfin
        apply hB
        refine (hfin.biUnion (fun c _ => h c)).subset (fun x hx => ?_)
        exact mem_iUnion₂.2 ⟨f x, ⟨x, hx, rfl⟩, hx, rfl⟩
      intro hfin
      apply himg
      rw [← hbij.image_eq]
      exact hfin.image f
  obtain ⟨C2, C3, h2, h3, hdis, hun⟩ := exists_halves h1inf
  have s2 : C2 ⊆ C1 := hun ▸ subset_union_left
  have s3 : C3 ⊆ C1 := hun ▸ subset_union_right
  have hsub : ∀ C ⊆ C1, ((∃ c, ∀ x ∈ C, f x = c) ∨ InjOn f C) := by
    intro C hC
    rcases h1f with ⟨c, hc⟩ | hinj
    · exact Or.inl ⟨c, fun x hx => hc x (hC hx)⟩
    · exact Or.inr (hinj.mono hC)
  by_cases hz : C2 ∈ z
  · refine ⟨C3, s3.trans h1B, h3, hsub C3 s3, fun hz3 => ?_⟩
    obtain ⟨x, hx2, hx3⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (z : Filter ℕ)) hz hz3)
    exact disjoint_left.1 hdis hx2 hx3
  · exact ⟨C2, s2.trans h1B, h2, hsub C2 s2, hz⟩

/-- The index set of order type `ω₁`. -/
abbrev W1 : Type := (ℵ₁ : Cardinal.{0}).ord.ToType

theorem mk_W1 : #W1 = ℵ₁ := Cardinal.mk_ord_toType _

theorem countable_Iio_W1 (i : W1) : (Iio i).Countable := by
  have h : #(Iio i) < ℵ₁ := by
    have := Cardinal.mk_Iio_toType_ord_lt (c := ℵ₁) i
    exact this
  exact Cardinal.le_aleph0_iff_set_countable.1 (Cardinal.lt_aleph_one_iff.1 h)

instance : Nonempty W1 := by
  have : #W1 ≠ 0 := by
    rw [mk_W1]
    exact (Cardinal.aleph_pos 1).ne'
  exact Cardinal.mk_ne_zero_iff.1 this

/-- Under `𝔠 = ℵ₁`: a selective ultrafilter containing `A` and different from `ℵ₁` given ultrafilters. -/
theorem exists_selective_avoiding (CH : (𝔠 : Cardinal.{0}) = ℵ_ 1) (A : Set ℕ) (hA : A.Infinite) (z : W1 → Ultrafilter ℕ) :
    ∃ u : Ultrafilter ℕ, IsSel u ∧ A ∈ u ∧ ∀ i, u ≠ z i := by
  classical
  have hfun : #W1 = #(ℕ → ℕ) := by
    rw [mk_W1, ← CH]
    simp
  obtain ⟨fe⟩ := Cardinal.eq.1 hfun
  let P : (i : W1) → ((j : W1) → j < i → Set ℕ) → Set ℕ → Prop := fun i prev C =>
    C ⊆ A ∧ C.Infinite ∧ (∀ j (hj : j < i), (C \ prev j hj).Finite) ∧
      ((∃ c, ∀ x ∈ C, fe i x = c) ∨ InjOn (fe i) C) ∧ C ∉ z i
  let step : (i : W1) → ((j : W1) → j < i → Set ℕ) → Set ℕ := fun i prev =>
    if h : ∃ C, P i prev C then h.choose else ∅
  let T : W1 → Set ℕ := wellFounded_lt.fix step
  have hT : ∀ i, T i = step i (fun j _ => T j) := fun i => wellFounded_lt.fix_eq step i
  have hP : ∀ i, P i (fun j _ => T j) (T i) := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have hex : ∃ C, P i (fun j _ => T j) C := by
        have : Countable (Iio i) := (countable_Iio_W1 i).to_subtype
        obtain ⟨B, hBA, hBinf, hBsub⟩ := exists_pseudointersection (J := Iio i) A hA (fun j => T j.1)
          (fun j => (ih j.1 j.2).2.1) (fun j => (ih j.1 j.2).1) (fun j k => by
            rcases lt_trichotomy j.1 k.1 with h | h | h
            · exact Or.inr ((ih k.1 k.2).2.2.1 j.1 h)
            · rw [h]; simp
            · exact Or.inl ((ih j.1 j.2).2.2.1 k.1 h))
        obtain ⟨C, hCB, hCinf, hCf, hCz⟩ := exists_shrink B hBinf (fe i) (z i)
        refine ⟨C, hCB.trans hBA, hCinf, fun j hj => ?_, hCf, hCz⟩
        exact (hBsub ⟨j, hj⟩).subset (sdiff_subset_sdiff_left hCB)
      have e : T i = hex.choose := by
        rw [hT i]
        exact dif_pos hex
      rw [e]
      exact hex.choose_spec
  have hdir : ∀ i k, ∃ m, (T m \ T i).Finite ∧ (T m \ T k).Finite := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · exact ⟨k, (hP k).2.2.1 i h, by simp⟩
    · exact ⟨k, by rw [h]; simp, by simp⟩
    · exact ⟨i, by simp, (hP i).2.2.1 k h⟩
  have htrans : ∀ X Y Z : Set ℕ, (X \ Y).Finite → (Y \ Z).Finite → (X \ Z).Finite := by
    intro X Y Z h1 h2
    refine (h1.union h2).subset (fun x hx => ?_)
    by_cases h : x ∈ Y
    · exact Or.inr ⟨h, hx.2⟩
    · exact Or.inl ⟨hx.1, h⟩
  let F : Filter ℕ :=
    { sets := {s | ∃ i, (T i \ s).Finite}
      univ_sets := ⟨Classical.arbitrary W1, by simp⟩
      sets_of_superset := by
        rintro s t ⟨i, hi⟩ hst
        exact ⟨i, hi.subset (sdiff_subset_sdiff_right hst)⟩
      inter_sets := by
        rintro s t ⟨i, hi⟩ ⟨k, hk⟩
        obtain ⟨m, hmi, hmk⟩ := hdir i k
        refine ⟨m, ?_⟩
        rw [sdiff_inter]
        exact (htrans _ _ _ hmi hi).union (htrans _ _ _ hmk hk) }
  have hFmem : ∀ s, s ∈ F ↔ ∃ i, (T i \ s).Finite := fun s => Iff.rfl
  have : F.NeBot := by
    refine ⟨fun h => ?_⟩
    have h0 : (∅ : Set ℕ) ∈ F := by rw [h]; exact Filter.mem_bot
    obtain ⟨i, hi⟩ := (hFmem _).1 h0
    rw [sdiff_empty] at hi
    exact (hP i).2.1 hi
  set u := Ultrafilter.of F with hu
  have hle : ∀ s, s ∈ F → s ∈ u := fun s hs => Ultrafilter.of_le F hs
  have hTu : ∀ i, T i ∈ u := fun i => hle _ ((hFmem _).2 ⟨i, by simp⟩)
  refine ⟨u, ⟨fun a ha => ?_, fun f => ?_⟩, ?_, fun i h => ?_⟩
  · have h1 : ({a}ᶜ : Set ℕ) ∈ u := by
      refine hle _ ((hFmem _).2 ⟨Classical.arbitrary W1, (finite_singleton a).subset (fun x hx => ?_)⟩)
      exact not_not.1 hx.2
    rw [ha] at h1
    exact h1 rfl
  · obtain ⟨i, rfl⟩ := fe.surjective f
    rcases (hP i).2.2.2.1 with ⟨c, hc⟩ | hinj
    · exact Or.inl ⟨c, Filter.mem_of_superset (hTu i) hc⟩
    · exact Or.inr ⟨T i, hTu i, hinj⟩
  · exact Filter.mem_of_superset (hTu (Classical.arbitrary W1)) (hP _).1
  · exact (hP i).2.2.2.2 (h ▸ hTu i)

/-- Lemma 3.6: pairwise non-isomorphic selective ultrafilters on `H0`, dense in `H0`. -/
theorem exists_dense_selective (CH : (𝔠 : Cardinal.{0}) = ℵ_ 1) (H0 : Set ℕ) (hH : H0.Infinite) :
    ∃ u : W1 → Ultrafilter ℕ, (∀ i, IsSel (u i)) ∧ (∀ i, H0 ∈ u i) ∧ (∀ j i, j < i → ¬ Iso (u j) (u i)) ∧
      ∀ A ⊆ H0, A.Infinite → ∃ i, A ∈ u i := by
  classical
  have hsets : #W1 = #(Set ℕ) := by rw [mk_W1, ← CH, Cardinal.mk_set_nat]
  obtain ⟨ge⟩ := Cardinal.eq.1 hsets
  set Aw : W1 → Set ℕ := fun i => if (ge i ∩ H0).Infinite then ge i ∩ H0 else H0 with hAw
  have hAinf : ∀ i, (Aw i).Infinite := by
    intro i
    rw [hAw]
    dsimp only
    split_ifs with h
    · exact h
    · exact hH
  have hAsub : ∀ i, Aw i ⊆ H0 := by
    intro i
    rw [hAw]
    dsimp only
    split_ifs
    · exact inter_subset_right
    · exact subset_rfl
  have hperm : #(Equiv.Perm ℕ) = 𝔠 := by
    rw [Cardinal.mk_perm_eq_two_power, Cardinal.mk_nat, Cardinal.two_power_aleph0]
  have hz : ∀ (i : W1) (prev : (j : W1) → j < i → Ultrafilter ℕ),
      ∃ z : W1 → Ultrafilter ℕ, ∀ j (hj : j < i) (π : Equiv.Perm ℕ), ∃ k, z k = (prev j hj).map π := by
    intro i prev
    set Fb : Set (Ultrafilter ℕ) :=
      insert (pure 0) (range (fun p : (Iio i) × Equiv.Perm ℕ => (prev p.1.1 p.1.2).map p.2)) with hFb
    have : Countable (Iio i) := (countable_Iio_W1 i).to_subtype
    have hcard : #Fb ≤ #W1 := by
      rw [mk_W1]
      have h1 : #(range (fun p : (Iio i) × Equiv.Perm ℕ => (prev p.1.1 p.1.2).map p.2)) ≤ ℵ₁ := by
        refine Cardinal.mk_range_le.trans ?_
        rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, hperm, CH]
        have h2 : #(Iio i) ≤ ℵ₁ := (Cardinal.mk_le_aleph0.trans (Cardinal.aleph0_lt_aleph_one.le))
        exact (mul_le_mul' h2 le_rfl).trans (Cardinal.mul_eq_self (Cardinal.aleph0_lt_aleph_one.le)).le
      refine Cardinal.mk_insert_le.trans ?_
      exact (add_le_add h1 (Cardinal.one_le_aleph0.trans Cardinal.aleph0_lt_aleph_one.le)).trans
        (Cardinal.add_eq_self (Cardinal.aleph0_lt_aleph_one.le)).le
    obtain ⟨emb⟩ := (Cardinal.le_def _ _).1 hcard
    have : Nonempty Fb := ⟨⟨pure 0, mem_insert _ _⟩⟩
    refine ⟨fun k => (Function.invFun emb k).1, fun j hj π => ?_⟩
    have hmem : (prev j hj).map π ∈ Fb := mem_insert_of_mem _ ⟨(⟨j, hj⟩, π), rfl⟩
    refine ⟨emb ⟨_, hmem⟩, ?_⟩
    show (Function.invFun emb (emb ⟨_, hmem⟩)).1 = _
    rw [Function.leftInverse_invFun emb.injective]
  let step : (i : W1) → ((j : W1) → j < i → Ultrafilter ℕ) → Ultrafilter ℕ := fun i prev =>
    (exists_selective_avoiding CH (Aw i) (hAinf i) (hz i prev).choose).choose
  let u : W1 → Ultrafilter ℕ := wellFounded_lt.fix step
  have hu : ∀ i, u i = step i (fun j _ => u j) := fun i => wellFounded_lt.fix_eq step i
  have hspec : ∀ i, IsSel (u i) ∧ Aw i ∈ u i ∧
      ∀ k, u i ≠ (hz i (fun j _ => u j)).choose k := by
    intro i
    rw [hu i]
    exact (exists_selective_avoiding CH (Aw i) (hAinf i) (hz i (fun j _ => u j)).choose).choose_spec
  refine ⟨u, fun i => (hspec i).1, fun i => Filter.mem_of_superset (hspec i).2.1 (hAsub i), ?_, ?_⟩
  · rintro j i hji ⟨π, hπ⟩
    obtain ⟨k, hk⟩ := (hz i (fun j _ => u j)).choose_spec j hji π
    exact (hspec i).2.2 k (by rw [hk, hπ])
  · intro A hAH hAi
    refine ⟨ge.symm A, ?_⟩
    have h1 : Aw (ge.symm A) = A := by
      have h2 : ge (ge.symm A) ∩ H0 = A := by
        rw [ge.apply_symm_apply, inter_eq_left.2 hAH]
      rw [hAw]
      dsimp only
      rw [h2, if_pos hAi]
    have h3 := (hspec (ge.symm A)).2.1
    rwa [h1] at h3

section Main

variable {G : Type*} [AddCommGroup G] [Countable G] [Infinite G]

/-- Theorem 3.7. -/
theorem exists_hausdorff_vicinity (CH : (𝔠 : Cardinal.{0}) = ℵ_ 1) (htor : ∀ m : ℕ, 0 < m → {x : G | m • x = 0}.Finite)
    (H : AddSubgroup G) (hH : (H : Set G).Infinite) :
    ∃ C : Set (Filter G), NullFamily C ∧ (∀ (F : Filter G) (x y : G), conv C F x → conv C F y → x = y) ∧
      ∀ s : Set G, s ∈ vic C ↔ (0 : G) ∈ s ∧ ((H : Set G) \ s).Finite := by
  classical
  obtain ⟨e⟩ : Nonempty (ℕ ≃ G) := by
    have := Encodable.ofCountable G
    have := Denumerable.ofEncodableOfInfinite G
    exact ⟨(Denumerable.eqv G).symm⟩
  have hH0 : (e ⁻¹' (H : Set G)).Infinite := hH.preimage (by rw [e.range_eq_univ]; exact subset_univ _)
  obtain ⟨u, hsel, hmemH, hiso, hdense⟩ := exists_dense_selective CH _ hH0
  set S : Set (Ultrafilter G) := range (fun i => (u i).map e) with hS
  have hmap : ∀ i (s : Set G), s ∈ (u i).map e ↔ e ⁻¹' s ∈ u i := fun i s => Iff.rfl
  have hselS : ∀ v ∈ S, IsSel v := by
    rintro _ ⟨i, rfl⟩
    constructor
    · intro a ha
      apply (hsel i).1 (e.symm a)
      have h1 : ((u i).map e).map e.symm = (pure a : Ultrafilter G).map e.symm := by rw [← ha]
      rw [Ultrafilter.map_map, Ultrafilter.map_pure] at h1
      have h2 : (e.symm : G → ℕ) ∘ (e : ℕ → G) = id := by funext x; simp
      rwa [h2, Ultrafilter.map_id] at h1
    · intro f
      rcases (hsel i).2 (fun n => f (e n)) with ⟨c, hc⟩ | ⟨C, hC, hinj⟩
      · exact Or.inl ⟨c, hc⟩
      · refine Or.inr ⟨e '' C, ?_, ?_⟩
        · rw [hmap, preimage_image_eq _ e.injective]
          exact hC
        · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
          rw [hinj ha hb hab]
  have hisoS : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬ Iso v w := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne ⟨π, hπ⟩
    have hij : i ≠ j := fun h => hne (by rw [h])
    have hback : ∀ k, ((u k).map e).map e.symm = u k := by
      intro k
      rw [Ultrafilter.map_map]
      have : (e.symm : G → ℕ) ∘ (e : ℕ → G) = id := by funext x; simp
      rw [this, Ultrafilter.map_id]
    have hN : Iso (u i) (u j) := by
      refine ⟨(e.trans π).trans e.symm, ?_⟩
      have h1 : (((u i).map e).map π).map e.symm = u j := by
        have hπ' : ((u i).map e).map π = (u j).map e := hπ
        rw [hπ', hback]
      rw [Ultrafilter.map_map, Ultrafilter.map_map] at h1
      exact h1
    rcases lt_or_gt_of_ne hij with h | h
    · exact hiso i j h hN
    · exact hiso j i h hN.symm
  have hfreeS : ∀ v ∈ S, ∀ a, v ≠ pure a := fun v hv => (hselS v hv).1
  have hHS : ∀ v ∈ S, (H : Set G) ∈ v := by
    rintro _ ⟨i, rfl⟩
    exact hmemH i
  have hdenseS : ∀ A ⊆ (H : Set G), A.Infinite → ∃ v ∈ S, A ∈ v := by
    intro A hA hAinf
    obtain ⟨i, hi⟩ := hdense (e ⁻¹' A) (preimage_mono hA)
      (hAinf.preimage (by rw [e.range_eq_univ]; exact subset_univ _))
    exact ⟨_, ⟨i, rfl⟩, hi⟩
  have hhaus := genFam_hausdorff htor S hselS hisoS
  have hC : NullFamily (genFam (ultraGen S)) := genFam_nullFamily _
  exact ⟨_, hC, hausdorff_iff.2 ((hausdorff_iff_principal hC).2 hhaus),
    mem_vic_iff_of_dense S H hfreeS hHS hdenseS hhaus⟩

end Main

/-- Theorem 3.7 for `ℤ` and Corollary 3.8: under `𝔠 = ℵ₁` there is a Hausdorff PG on `ℤ` whose vicinity filter is the
cofinite filter at `0`; it is not discrete, its topological modification is the cofinite topology, the neighbourhood
filter of its finest group topology is `⊤`, and its vicinity filter does not converge to `0`. -/
theorem exists_hausdorff_cofin_int (CH : (𝔠 : Cardinal.{0}) = ℵ_ 1) :
    ∃ C : Set (Filter ℤ), NullFamily C ∧ (∀ (F : Filter ℤ) (x y : ℤ), conv C F x → conv C F y → x = y) ∧
      CofinAtZero C ∧ (∃ U : Ultrafilter ℤ, (U : Filter ℤ) ∈ C ∧ ∀ a, U ≠ pure a) ∧
      (∀ O : Set ℤ, IsOpenMod C O ↔ O = ∅ ∨ Oᶜ.Finite) ∧ halveFilter (vic C) = ⊤ ∧ vic C ∉ C := by
  have htor : ∀ m : ℕ, 0 < m → {x : ℤ | m • x = 0}.Finite := by
    intro m hm
    refine (finite_singleton (0 : ℤ)).subset (fun x hx => ?_)
    have h : m • x = 0 := hx
    rcases smul_eq_zero.1 h with h1 | h1
    · exact absurd h1 hm.ne'
    · exact h1
  obtain ⟨C, hC, hH, hv⟩ := exists_hausdorff_vicinity CH htor (⊤ : AddSubgroup ℤ)
    (by simpa using infinite_univ)
  have hV : CofinAtZero C := by
    intro s
    rw [hv s, AddSubgroup.coe_top, ← compl_eq_univ_sdiff]
  obtain ⟨U, hUC, _, hfree⟩ := exists_free_ultra_of_cofin hC hV (A := (univ : Set ℤ)) infinite_univ
  refine ⟨C, hC, hH, hV, ⟨U, hUC, hfree⟩, isOpenMod_iff_of_cofin hC hV, halveFilter_eq_top_of_cofin hC hV, ?_⟩
  intro hpre
  have hsum := hC.add _ hpre _ hpre
  have h1 : ({1}ᶜ : Set ℤ) ∈ vic C := by
    refine (hV _).2 ⟨by simp, ?_⟩
    rw [compl_compl]
    exact finite_singleton 1
  have h2 : ({1}ᶜ : Set ℤ) ∈ Filter.map₂ (· + ·) (vic C) (vic C) := mem_vic.1 h1 _ hsum
  obtain ⟨a, ha, b, hb, hab⟩ := Filter.mem_map₂_iff.1 h2
  have hafin := ((hV _).1 ha).2
  have hbfin := ((hV _).1 hb).2
  obtain ⟨w, hw⟩ := (hafin.union (hbfin.image (fun y => 1 - y))).exists_notMem
  have hwa : w ∈ a := by
    by_contra h
    exact hw (Or.inl h)
  have hwb : 1 - w ∈ b := by
    by_contra h
    exact hw (Or.inr ⟨1 - w, h, by simp⟩)
  have h3 : (1 : ℤ) ∈ ({1}ᶜ : Set ℤ) := hab ⟨w, hwa, 1 - w, hwb, add_sub_cancel w 1⟩
  exact h3 rfl

end Sel

end PG
