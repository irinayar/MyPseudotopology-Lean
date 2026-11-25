import Mathlib
import LeanCheck.PGThreeSelective
import LeanCheck.PGThreeSelectiveCH
import LeanCheck.PGTwoQuotient
import LeanCheck.PGTwoCofinite

/-!
# PGthree: weaker set theory and the exact condition on the group (Lean check)

Scope. Section 4 of the third article (`PGthree.tex`).

* `Supply` : the statement (S), that there are at least `𝔠` pairwise non-isomorphic selective ultrafilters on `ℕ`;
* `dense_iff_supply` : Lemma 4.1;
* `TowerProp` : every family of fewer than `𝔠` infinite sets, nested modulo finite sets, has an infinite
  pseudointersection (true if `𝔭 = 𝔠`); `towerProp_of_CH`, `supply_of_towerProp` : Remark 4.2. The case
  `cov(M) = 𝔠`, quoted from the literature in the article, is NOT formalized;
* `genFam_hausdorff_iff` : Proposition 4.3;
* `finite_or_zero_of_vicinity` : Theorem 4.4(a); `exists_vicinity_of_condition` : Theorem 4.4(b);
* `not_vicinity_boolean_times_int` : Corollary 4.5; `exists_vicinity_boolean` : the first sentence of Remark 4.6.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Cardinal Ordinal

namespace PG

namespace Sel

/-- The statement (S): at least `𝔠` pairwise non-isomorphic selective ultrafilters on `ℕ`. -/
def Supply : Prop :=
  ∃ T : Set (Ultrafilter ℕ), (∀ u ∈ T, IsSel u) ∧ (∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬ Iso u v) ∧ (𝔠 : Cardinal.{0}) ≤ #T

/-- A set of selective ultrafilters as in Lemma 3.6, on `H0 ⊆ ℕ`. -/
def DenseFamily (H0 : Set ℕ) : Prop :=
  ∃ S : Set (Ultrafilter ℕ), (∀ u ∈ S, IsSel u) ∧ (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ Iso u v) ∧ (∀ u ∈ S, H0 ∈ u) ∧
    ∀ A ⊆ H0, A.Infinite → ∃ u ∈ S, A ∈ u

theorem isSel_map_of_injective {α β : Type*} {u : Ultrafilter α} (hu : IsSel u) (f : α → β)
    (hf : Function.Injective f) : IsSel (u.map f) := by
  constructor
  · intro b hb
    have h1 : f ⁻¹' {b} ∈ u := by
      have h2 : ({b} : Set β) ∈ u.map f := by rw [hb]; exact rfl
      exact h2
    exact notMem_of_finite hu.1 ((finite_singleton b).preimage hf.injOn) h1
  · intro g
    rcases hu.2 (fun x => g (f x)) with ⟨c, hc⟩ | ⟨C, hC, hinj⟩
    · exact Or.inl ⟨c, hc⟩
    · refine Or.inr ⟨f '' C, ?_, ?_⟩
      · show f ⁻¹' (f '' C) ∈ u
        rw [preimage_image_eq _ hf]
        exact hC
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
        rw [hinj ha hb hab]

/-- Lemma 4.1. -/
theorem dense_iff_supply (H0 : Set ℕ) (hH : H0.Infinite) : DenseFamily H0 ↔ Supply := by
  classical
  constructor
  · rintro ⟨S, hsel, hiso, _, hdense⟩
    refine ⟨S, hsel, hiso, ?_⟩
    obtain ⟨φ, hφ, hφH⟩ : ∃ φ : ℕ → ℕ, Function.Injective φ ∧ ∀ n, φ n ∈ H0 := by
      have := hH.to_subtype
      have : Denumerable H0 := Nat.Subtype.denumerable _
      exact ⟨fun n => ((Denumerable.eqv H0).symm n).1,
        fun a b h => (Denumerable.eqv H0).symm.injective (Subtype.ext h), fun n => ((Denumerable.eqv H0).symm n).2⟩
    let code : (ℕ → Bool) → ℕ → ℕ := fun b n => φ (Encodable.encode (List.ofFn (fun i : Fin n => b i)))
    have hcode : ∀ b b' n n', code b n = code b' n' → n = n' ∧ ∀ i < n, b i = b' i := by
      intro b b' n n' h
      have h1 := Encodable.encode_injective (hφ h)
      have h2 : n = n' := by
        have := congrArg List.length h1
        simpa using this
      subst h2
      refine ⟨rfl, fun i hi => ?_⟩
      have h3 := List.ofFn_injective h1
      exact congrFun h3 ⟨i, hi⟩
    have hinf : ∀ b, (range (code b)).Infinite := fun b =>
      infinite_range_of_injective (fun a c h => (hcode b b a c h).1)
    have hsub : ∀ b, range (code b) ⊆ H0 := by
      rintro b _ ⟨n, rfl⟩
      exact hφH _
    have hAD : ∀ b b', b ≠ b' → (range (code b) ∩ range (code b')).Finite := by
      intro b b' hne
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
      refine ((finite_Iic k).image (code b)).subset ?_
      rintro _ ⟨⟨n, rfl⟩, ⟨n', hn'⟩⟩
      obtain ⟨_, h2⟩ := hcode b' b n' n hn'
      refine ⟨n, ?_, rfl⟩
      have h3 : n' = n := (hcode b' b n' n hn').1
      by_contra hlt
      have hkn : k < n := not_le.1 hlt
      exact hk (h2 k (h3 ▸ hkn)).symm
    have hch : ∀ b, ∃ u ∈ S, range (code b) ∈ u := fun b => hdense _ (hsub b) (hinf b)
    choose u hu hmem using hch
    have huinj : Function.Injective (fun b => (⟨u b, hu b⟩ : S)) := by
      intro b b' h
      by_contra hne
      have h1 : u b = u b' := congrArg Subtype.val h
      have h2 : range (code b') ∈ u b := h1 ▸ hmem b'
      exact notMem_of_finite (hsel _ (hu b)).1 (hAD b b' hne) (Filter.inter_mem (f := (u b : Filter ℕ)) (hmem b) h2)
    have h3 : #(ℕ → Bool) ≤ #S := Cardinal.mk_le_of_injective huinj
    have h4 : #(ℕ → Bool) = (𝔠 : Cardinal.{0}) := by simp
    rwa [h4] at h3
  · rintro ⟨T, hsel, hiso, hcard⟩
    let I := {A : Set ℕ // A ⊆ H0 ∧ A.Infinite}
    have hI : #I ≤ #T := by
      refine (Cardinal.mk_subtype_le _).trans ?_
      rw [Cardinal.mk_set_nat]
      exact hcard
    obtain ⟨g⟩ := (Cardinal.le_def _ _).1 hI
    have hf : ∀ A : I, ∃ f : ℕ → ℕ, Function.Injective f ∧ range f = A.1 := by
      intro A
      have := A.2.2.to_subtype
      have : Denumerable A.1 := Nat.Subtype.denumerable _
      refine ⟨fun n => ((Denumerable.eqv A.1).symm n).1,
        fun a b h => (Denumerable.eqv A.1).symm.injective (Subtype.ext h), ?_⟩
      ext x
      constructor
      · rintro ⟨n, rfl⟩
        exact ((Denumerable.eqv A.1).symm n).2
      · intro hx
        exact ⟨Denumerable.eqv A.1 ⟨x, hx⟩, by simp⟩
    choose f hfinj hfrange using hf
    let u : I → Ultrafilter ℕ := fun A => (g A).1.map (f A)
    have hsu : ∀ A, IsSel (u A) := fun A => isSel_map_of_injective (hsel _ (g A).2) _ (hfinj A)
    have hAu : ∀ A : I, A.1 ∈ u A := by
      intro A
      show f A ⁻¹' A.1 ∈ (g A).1
      refine Filter.univ_mem' (fun n => ?_)
      show f A n ∈ A.1
      rw [← hfrange A]
      exact mem_range_self n
    have hiu : ∀ A, Iso (g A).1 (u A) := fun A =>
      iso_of_injOn (hsel _ (g A).2).1 (f A) (C := univ) Filter.univ_mem (hfinj A).injOn
    refine ⟨range u, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨A, rfl⟩
      exact hsu A
    · rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩ hne hAB
      have h1 : Iso (g A).1 (g B).1 := (hiu A).trans (hAB.trans (hiu B).symm)
      by_cases h : (g A).1 = (g B).1
      · have : A = B := g.injective (Subtype.ext h)
        exact hne (by rw [this])
      · exact hiso _ (g A).2 _ (g B).2 h h1
    · rintro _ ⟨A, rfl⟩
      exact Filter.mem_of_superset (hAu A) A.2.1
    · intro A hA hAinf
      exact ⟨u ⟨A, hA, hAinf⟩, ⟨_, rfl⟩, hAu ⟨A, hA, hAinf⟩⟩

/-- Fewer than `𝔠` infinite sets, nested modulo finite sets, have an infinite pseudointersection. -/
def TowerProp : Prop :=
  ∀ (J : Type) (A : Set ℕ) (T : J → Set ℕ), (#J : Cardinal.{0}) < 𝔠 → A.Infinite → (∀ j, (T j).Infinite) →
    (∀ j, T j ⊆ A) → (∀ j k, (T j \ T k).Finite ∨ (T k \ T j).Finite) →
    ∃ B : Set ℕ, B ⊆ A ∧ B.Infinite ∧ ∀ j, (B \ T j).Finite

theorem towerProp_of_CH (CH : (𝔠 : Cardinal.{0}) = ℵ_ 1) : TowerProp := by
  intro J A T hJ hA hTinf hTA hchain
  rw [CH] at hJ
  have : Countable J := Cardinal.mk_le_aleph0_iff.1 (Cardinal.lt_aleph_one_iff.1 hJ)
  exact exists_pseudointersection A hA T hTinf hTA hchain

/-- The index set of order type `𝔠`. -/
abbrev Wc : Type := (𝔠 : Cardinal.{0}).ord.ToType

theorem mk_Wc : #Wc = (𝔠 : Cardinal.{0}) := Cardinal.mk_ord_toType _

theorem mk_Iio_Wc (i : Wc) : (#(Iio i) : Cardinal.{0}) < 𝔠 := Cardinal.mk_Iio_toType_ord_lt (c := 𝔠) i

instance : Nonempty Wc := by
  have : #Wc ≠ 0 := by
    rw [mk_Wc]
    exact Cardinal.continuum_ne_zero
  exact Cardinal.mk_ne_zero_iff.1 this

/-- A selective ultrafilter containing `A` and different from `𝔠` given ultrafilters. -/
theorem exists_selective_avoiding_of_tower (hP : TowerProp) (A : Set ℕ) (hA : A.Infinite) (z : Wc → Ultrafilter ℕ) :
    ∃ u : Ultrafilter ℕ, IsSel u ∧ A ∈ u ∧ ∀ i, u ≠ z i := by
  classical
  have hfun : #Wc = #(ℕ → ℕ) := by
    rw [mk_Wc]
    simp
  obtain ⟨fe⟩ := Cardinal.eq.1 hfun
  let P : (i : Wc) → ((j : Wc) → j < i → Set ℕ) → Set ℕ → Prop := fun i prev C =>
    C ⊆ A ∧ C.Infinite ∧ (∀ j (hj : j < i), (C \ prev j hj).Finite) ∧
      ((∃ c, ∀ x ∈ C, fe i x = c) ∨ InjOn (fe i) C) ∧ C ∉ z i
  let step : (i : Wc) → ((j : Wc) → j < i → Set ℕ) → Set ℕ := fun i prev =>
    if h : ∃ C, P i prev C then h.choose else ∅
  let T : Wc → Set ℕ := wellFounded_lt.fix step
  have hT : ∀ i, T i = step i (fun j _ => T j) := fun i => wellFounded_lt.fix_eq step i
  have hQ : ∀ i, P i (fun j _ => T j) (T i) := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have hex : ∃ C, P i (fun j _ => T j) C := by
        obtain ⟨B, hBA, hBinf, hBsub⟩ := hP (Iio i) A (fun j => T j.1) (mk_Iio_Wc i) hA
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
    · exact ⟨k, (hQ k).2.2.1 i h, by simp⟩
    · exact ⟨k, by rw [h]; simp, by simp⟩
    · exact ⟨i, by simp, (hQ i).2.2.1 k h⟩
  have htrans : ∀ X Y Z : Set ℕ, (X \ Y).Finite → (Y \ Z).Finite → (X \ Z).Finite := by
    intro X Y Z h1 h2
    refine (h1.union h2).subset (fun x hx => ?_)
    by_cases h : x ∈ Y
    · exact Or.inr ⟨h, hx.2⟩
    · exact Or.inl ⟨hx.1, h⟩
  let F : Filter ℕ :=
    { sets := {s | ∃ i, (T i \ s).Finite}
      univ_sets := ⟨Classical.arbitrary Wc, by simp⟩
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
    exact (hQ i).2.1 hi
  set u := Ultrafilter.of F with hu
  have hle : ∀ s, s ∈ F → s ∈ u := fun s hs => Ultrafilter.of_le F hs
  have hTu : ∀ i, T i ∈ u := fun i => hle _ ((hFmem _).2 ⟨i, by simp⟩)
  refine ⟨u, ⟨fun a ha => ?_, fun f => ?_⟩, ?_, fun i h => ?_⟩
  · have h1 : ({a}ᶜ : Set ℕ) ∈ u := by
      refine hle _ ((hFmem _).2 ⟨Classical.arbitrary Wc, (finite_singleton a).subset (fun x hx => ?_)⟩)
      exact not_not.1 hx.2
    rw [ha] at h1
    exact h1 rfl
  · obtain ⟨i, rfl⟩ := fe.surjective f
    rcases (hQ i).2.2.2.1 with ⟨c, hc⟩ | hinj
    · exact Or.inl ⟨c, Filter.mem_of_superset (hTu i) hc⟩
    · exact Or.inr ⟨T i, hTu i, hinj⟩
  · exact Filter.mem_of_superset (hTu (Classical.arbitrary Wc)) (hQ _).1
  · exact (hQ i).2.2.2.2 (h ▸ hTu i)

/-- Remark 4.2: the tower property gives (S). -/
theorem supply_of_towerProp (hP : TowerProp) : Supply := by
  classical
  have hperm : #(Equiv.Perm ℕ) = (𝔠 : Cardinal.{0}) := by
    rw [Cardinal.mk_perm_eq_two_power, Cardinal.mk_nat, Cardinal.two_power_aleph0]
  have hz : ∀ (i : Wc) (prev : (j : Wc) → j < i → Ultrafilter ℕ),
      ∃ z : Wc → Ultrafilter ℕ, ∀ j (hj : j < i) (π : Equiv.Perm ℕ), ∃ k, z k = (prev j hj).map π := by
    intro i prev
    set Fb : Set (Ultrafilter ℕ) :=
      insert (pure 0) (range (fun p : (Iio i) × Equiv.Perm ℕ => (prev p.1.1 p.1.2).map p.2)) with hFb
    have hcard : #Fb ≤ #Wc := by
      rw [mk_Wc]
      have h1 : #(range (fun p : (Iio i) × Equiv.Perm ℕ => (prev p.1.1 p.1.2).map p.2)) ≤ (𝔠 : Cardinal.{0}) := by
        refine Cardinal.mk_range_le.trans ?_
        rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, hperm]
        exact (mul_le_mul' (mk_Iio_Wc i).le le_rfl).trans (Cardinal.continuum_mul_self).le
      refine Cardinal.mk_insert_le.trans ?_
      exact (add_le_add h1 (Cardinal.one_le_aleph0.trans Cardinal.aleph0_le_continuum)).trans
        (Cardinal.continuum_add_self).le
    obtain ⟨emb⟩ := (Cardinal.le_def _ _).1 hcard
    have : Nonempty Fb := ⟨⟨pure 0, mem_insert _ _⟩⟩
    refine ⟨fun k => (Function.invFun emb k).1, fun j hj π => ?_⟩
    have hmem : (prev j hj).map π ∈ Fb := mem_insert_of_mem _ ⟨(⟨j, hj⟩, π), rfl⟩
    refine ⟨emb ⟨_, hmem⟩, ?_⟩
    show (Function.invFun emb (emb ⟨_, hmem⟩)).1 = _
    rw [Function.leftInverse_invFun emb.injective]
  let step : (i : Wc) → ((j : Wc) → j < i → Ultrafilter ℕ) → Ultrafilter ℕ := fun i prev =>
    (exists_selective_avoiding_of_tower hP univ infinite_univ (hz i prev).choose).choose
  let u : Wc → Ultrafilter ℕ := wellFounded_lt.fix step
  have hu : ∀ i, u i = step i (fun j _ => u j) := fun i => wellFounded_lt.fix_eq step i
  have hspec : ∀ i, IsSel (u i) ∧ ∀ k, u i ≠ (hz i (fun j _ => u j)).choose k := by
    intro i
    rw [hu i]
    have h := (exists_selective_avoiding_of_tower hP univ infinite_univ (hz i (fun j _ => u j)).choose).choose_spec
    exact ⟨h.1, h.2.2⟩
  have hiso : ∀ j i, j < i → ¬ Iso (u j) (u i) := by
    rintro j i hji ⟨π, hπ⟩
    obtain ⟨k, hk⟩ := (hz i (fun j _ => u j)).choose_spec j hji π
    exact (hspec i).2 k (by rw [hk, hπ])
  have huinj : Function.Injective u := by
    intro i j h
    rcases lt_trichotomy i j with hlt | heq | hlt
    · exact absurd (h ▸ ⟨Equiv.refl ℕ, by simp [Ultrafilter.map_id]⟩ : Iso (u i) (u j)) (hiso i j hlt)
    · exact heq
    · exact absurd (h ▸ ⟨Equiv.refl ℕ, by simp [Ultrafilter.map_id]⟩ : Iso (u j) (u i)) (hiso j i hlt)
  refine ⟨range u, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact (hspec i).1
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne h
    rcases lt_trichotomy i j with hlt | heq | hlt
    · exact hiso i j hlt h
    · exact hne (by rw [heq])
    · exact hiso j i hlt h.symm
  · rw [Cardinal.mk_range_eq u huinj, mk_Wc]

theorem supply_of_CH (CH : (𝔠 : Cardinal.{0}) = ℵ_ 1) : Supply := supply_of_towerProp (towerProp_of_CH CH)

section Group

variable {G : Type*} [AddCommGroup G]

/-- Proposition 4.3. -/
theorem genFam_hausdorff_iff [Countable G] [Infinite G] (S : Set (Ultrafilter G)) (hsel : ∀ u ∈ S, IsSel u)
    (hiso : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ Iso u v) :
    (∀ g : G, (pure g : Filter G) ∈ genFam (ultraGen S) → g = 0) ↔
      ∀ u ∈ S, ∀ m : ℤ, m ≠ 0 → (∀ a, u.map (fun x : G => m • x) ≠ pure a) ∨ u.map (fun x : G => m • x) = pure 0 := by
  constructor
  · intro h u hu m _
    by_cases hfree : ∀ a, u.map (fun x : G => m • x) ≠ pure a
    · exact Or.inl hfree
    right
    push Not at hfree
    obtain ⟨a, ha⟩ := hfree
    have hne : ∀ F ∈ ultraGen S, F.NeBot := by
      rintro F ⟨v, _, rfl⟩
      exact v.neBot
    have huC : (u : Filter G) ∈ genFam (ultraGen S) := subset_genFam hne ⟨u, hu, rfl⟩
    have h1 : Filter.map (fun x : G => m • x) (u : Filter G) ∈ genFam (ultraGen S) := by
      refine genFam_le (genFam_nullFamily _) (fun F hF => ?_) (map_zsmul_mem (u : Filter G) m)
      rw [mem_singleton_iff] at hF
      rw [hF]
      exact huC
    have h2 : Filter.map (fun x : G => m • x) (u : Filter G) = pure a := by
      rw [← Ultrafilter.coe_map, ha, Ultrafilter.coe_pure]
    rw [h2] at h1
    rw [ha, h a h1]
  · exact genFam_hausdorff_general S hsel hiso

/-- Theorem 4.4(a): no set-theoretic hypothesis and no countability. -/
theorem finite_or_zero_of_vicinity {C : Set (Filter G)} (hC : NullFamily C) (H : AddSubgroup G)
    (hV : ∀ s : Set G, s ∈ vic C ↔ (0 : G) ∈ s ∧ ((H : Set G) \ s).Finite) (m : ℕ) (_hm : 0 < m) :
    {x : G | x ∈ H ∧ m • x = 0}.Finite ∨ ∀ x ∈ H, m • x = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hinf, h0, h0H, h0ne⟩ := hcon
  have hhaus : ∀ g : G, (pure g : Filter G) ∈ C → g = 0 := by
    intro g hg
    by_contra hne
    have hs : ({g}ᶜ : Set G) ∈ vic C := by
      refine (hV _).2 ⟨fun h => hne (mem_singleton_iff.1 h).symm, (finite_singleton g).subset (fun x hx => ?_)⟩
      exact not_not.1 hx.2
    exact (mem_vic.1 hs _ hg) rfl
  set X : Set G := {x | x ∈ H ∧ m • x = m • h0} with hX
  have hXinf : X.Infinite := by
    refine (hinf.image (f := fun k => h0 + k) (fun a _ b _ h => add_left_cancel h)).mono ?_
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨H.add_mem h0H hk.1, by rw [smul_add, hk.2, add_zero]⟩
  have hs : (Xᶜ : Set G) ∉ vic C := by
    intro h
    have h1 := ((hV _).1 h).2
    refine hXinf (h1.subset (fun x hx => ⟨hx.1, fun hc => hc hx⟩))
  rw [mem_vic] at hs
  push Not at hs
  obtain ⟨F, hF, hsF⟩ := hs
  have : F.NeBot := hC.ne F hF
  obtain ⟨U, hUF, hUX⟩ := exists_ultra_compl_mem F hsF
  rw [compl_compl] at hUX
  have hUC : (U : Filter G) ∈ C := hC.finer F hF _ hUF U.neBot
  have h1 : Filter.map (fun x : G => m • x) (U : Filter G) ∈ C := by
    refine genFam_le hC (fun K hK => ?_) (map_nsmul_mem (U : Filter G) m)
    rw [mem_singleton_iff] at hK
    rw [hK]
    exact hUC
  have h2 : Filter.map (fun x : G => m • x) (U : Filter G) = pure (m • h0) := by
    have h3 : ({m • h0} : Set G) ∈ U.map (fun x : G => m • x) := by
      refine Filter.mem_of_superset (f := (U : Filter G)) hUX (fun x hx => ?_)
      exact hx.2
    obtain ⟨a, ha, hUa⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton (m • h0)) h3
    rw [← Ultrafilter.coe_map, hUa, Ultrafilter.coe_pure, mem_singleton_iff.1 ha]
  rw [h2] at h1
  exact h0ne (hhaus _ h1)

/-- Theorem 4.4(b). -/
theorem exists_vicinity_of_condition [Countable G] [Infinite G] (hS : Supply) (H : AddSubgroup G)
    (hH : (H : Set G).Infinite)
    (hE : ∀ m : ℕ, 0 < m → {x : G | x ∈ H ∧ m • x = 0}.Finite ∨ ∀ x ∈ H, m • x = 0) :
    ∃ C : Set (Filter G), NullFamily C ∧ (∀ (F : Filter G) (x y : G), conv C F x → conv C F y → x = y) ∧
      ∀ s : Set G, s ∈ vic C ↔ (0 : G) ∈ s ∧ ((H : Set G) \ s).Finite := by
  classical
  obtain ⟨e⟩ : Nonempty (ℕ ≃ G) := by
    have := Encodable.ofCountable G
    have := Denumerable.ofEncodableOfInfinite G
    exact ⟨(Denumerable.eqv G).symm⟩
  have hH0 : (e ⁻¹' (H : Set G)).Infinite := hH.preimage (by rw [e.range_eq_univ]; exact subset_univ _)
  obtain ⟨S0, hsel, hiso, hmemH, hdense⟩ := (dense_iff_supply _ hH0).2 hS
  set S : Set (Ultrafilter G) := (fun u : Ultrafilter ℕ => u.map e) '' S0 with hSdef
  have hback : ∀ u : Ultrafilter ℕ, (u.map e).map e.symm = u := by
    intro u
    rw [Ultrafilter.map_map]
    have : (e.symm : G → ℕ) ∘ (e : ℕ → G) = id := by funext x; simp
    rw [this, Ultrafilter.map_id]
  have hselS : ∀ v ∈ S, IsSel v := by
    rintro _ ⟨u, hu, rfl⟩
    exact isSel_map_of_injective (hsel u hu) e e.injective
  have hisoS : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬ Iso v w := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne ⟨π, hπ⟩
    have hab : a ≠ b := fun h => hne (by rw [h])
    refine hiso a ha b hb hab ⟨(e.trans π).trans e.symm, ?_⟩
    have h1 : ((a.map e).map π).map e.symm = b := by
      have hπ' : (a.map e).map π = b.map e := hπ
      rw [hπ', hback]
    rw [Ultrafilter.map_map, Ultrafilter.map_map] at h1
    exact h1
  have hfreeS : ∀ v ∈ S, ∀ a, v ≠ pure a := fun v hv => (hselS v hv).1
  have hHS : ∀ v ∈ S, (H : Set G) ∈ v := by
    rintro _ ⟨u, hu, rfl⟩
    exact hmemH u hu
  have hdenseS : ∀ A ⊆ (H : Set G), A.Infinite → ∃ v ∈ S, A ∈ v := by
    intro A hA hAinf
    obtain ⟨u, hu, hAu⟩ := hdense (e ⁻¹' A) (preimage_mono hA)
      (hAinf.preimage (by rw [e.range_eq_univ]; exact subset_univ _))
    exact ⟨_, ⟨u, hu, rfl⟩, hAu⟩
  have hmul : ∀ v ∈ S, ∀ m : ℤ, m ≠ 0 →
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
      have h3 := Filter.inter_mem (f := (v : Filter G)) (hHS v hv) h1
      obtain ⟨x₀, hx₀H, hx₀⟩ := Ultrafilter.nonempty_of_mem h3
      refine notMem_of_finite (hfreeS v hv) ((hfin.image (fun z => z + x₀)).subset (fun x hx => ?_)) h3
      refine ⟨x - x₀, ⟨H.sub_mem hx.1 hx₀H, (habs _).1 ?_⟩, by simp⟩
      have e1 : m • x = a := hx.2
      have e2 : m • x₀ = a := hx₀
      rw [smul_sub, e1, e2]
      exact sub_self a
    · right
      have h1 : ({0} : Set G) ∈ v.map (fun x : G => m • x) := by
        show (fun x : G => m • x) ⁻¹' {0} ∈ v
        refine Filter.mem_of_superset (f := (v : Filter G)) (hHS v hv) (fun x hx => ?_)
        exact (habs x).2 (hzero x hx)
      obtain ⟨a, ha, hva⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton (0 : G)) h1
      rw [hva, mem_singleton_iff.1 ha]
  have hhaus := genFam_hausdorff_general S hselS hisoS hmul
  have hC : NullFamily (genFam (ultraGen S)) := genFam_nullFamily _
  exact ⟨_, hC, hausdorff_iff.2 ((hausdorff_iff_principal hC).2 hhaus),
    mem_vic_iff_of_dense S H hfreeS hHS hdenseS hhaus⟩

end Group

/-- Corollary 4.5: on `(⊕ ℤ/2ℤ) × ℤ` the cofinite filter at `0` is not the vicinity filter of any PG. -/
theorem not_vicinity_boolean_times_int :
    ¬ ∃ C : Set (Filter ((ℕ →₀ ZMod 2) × ℤ)), NullFamily C ∧ CofinAtZero C := by
  rintro ⟨C, hC, hV⟩
  have hV' : ∀ s : Set ((ℕ →₀ ZMod 2) × ℤ), s ∈ vic C ↔
      (0 : (ℕ →₀ ZMod 2) × ℤ) ∈ s ∧ (((⊤ : AddSubgroup ((ℕ →₀ ZMod 2) × ℤ)) : Set _) \ s).Finite := by
    intro s
    rw [hV s, AddSubgroup.coe_top, ← compl_eq_univ_sdiff]
  rcases finite_or_zero_of_vicinity hC ⊤ hV' 2 (by norm_num) with hfin | hzero
  · have hinj : Function.Injective (fun n : ℕ => ((Finsupp.single n (1 : ZMod 2), (0 : ℤ)) : (ℕ →₀ ZMod 2) × ℤ)) := by
      intro a b h
      have h1 : Finsupp.single a (1 : ZMod 2) = Finsupp.single b 1 := congrArg Prod.fst h
      rcases (Finsupp.single_eq_single_iff _ _ _ _).1 h1 with h2 | h2
      · exact h2.1
      · exact absurd h2.1 one_ne_zero
    refine (infinite_range_of_injective hinj) (hfin.subset ?_)
    rintro _ ⟨n, rfl⟩
    refine ⟨AddSubgroup.mem_top _, Prod.ext ?_ (by simp)⟩
    show 2 • Finsupp.single n (1 : ZMod 2) = 0
    rw [two_nsmul, ← Finsupp.single_add, show (1 : ZMod 2) + 1 = 0 from by decide, Finsupp.single_zero]
  · have h := hzero ((0, 1) : (ℕ →₀ ZMod 2) × ℤ) (AddSubgroup.mem_top _)
    have h2 := congrArg Prod.snd h
    simp at h2

/-- Remark 4.6: under (S) the cofinite filter at `0` on `⊕ ℤ/2ℤ` is a vicinity filter. -/
theorem exists_vicinity_boolean (hS : Supply) :
    ∃ C : Set (Filter (ℕ →₀ ZMod 2)), NullFamily C ∧ CofinAtZero C := by
  have hE : ∀ m : ℕ, 0 < m → {x : ℕ →₀ ZMod 2 | x ∈ (⊤ : AddSubgroup (ℕ →₀ ZMod 2)) ∧ m • x = 0}.Finite ∨
      ∀ x ∈ (⊤ : AddSubgroup (ℕ →₀ ZMod 2)), m • x = 0 := by
    intro m _
    have h2 : ∀ x : ℕ →₀ ZMod 2, (2 : ℕ) • x = 0 := by
      intro x
      ext i
      have : ∀ a : ZMod 2, (2 : ℕ) • a = 0 := by decide
      simpa using this (x i)
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · right
      intro x _
      have e : m = k * 2 := by omega
      rw [e, mul_nsmul', h2, nsmul_zero]
    · left
      refine (finite_singleton (0 : ℕ →₀ ZMod 2)).subset (fun x hx => ?_)
      have h1 : m • x = x := by
        rw [hk, add_nsmul, one_nsmul, mul_comm, mul_nsmul', h2, nsmul_zero, zero_add]
      rw [mem_singleton_iff, ← h1]
      exact hx.2
  have hinf : ((⊤ : AddSubgroup (ℕ →₀ ZMod 2)) : Set (ℕ →₀ ZMod 2)).Infinite := by
    rw [AddSubgroup.coe_top]
    exact infinite_univ
  obtain ⟨C, hC, _, hv⟩ := exists_vicinity_of_condition hS ⊤ hinf hE
  refine ⟨C, hC, fun s => ?_⟩
  rw [hv s, AddSubgroup.coe_top, ← compl_eq_univ_sdiff]

end Sel

end PG
