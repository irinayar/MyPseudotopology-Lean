import Mathlib
import LeanCheck.PGThreeFamilies
import LeanCheck.PGThreeExact
import LeanCheck.PGThreeUncountable

/-!
# PGthree, Section 8: selective ultrafilters in the dominating construction

Completes `PGThreeFamilies`.

* `not_iso_of_map` : images under an injection into the integers of non-isomorphic
  ultrafilters on `ℕ` are non-isomorphic;
* `exists_selective_family` : from pairwise non-isomorphic selective ultrafilters indexed by
  `J` and a family of functions indexed by `J` that dominates every function, one obtains
  pairwise non-isomorphic selective ultrafilters on `ℤ`, indexed by `J`, such that openness
  for the topological modification of the PG they generate is openness for no group topology;
* `dominating_of_base` : a selective ultrafilter with a base indexed by `J` gives such a
  family of functions;
* `exists_selective_family_of_base` : the two combined;
* `exists_selective_family_of_card` : case (a) of the same corollary, with selectivity and
  non-isomorphism of the images.

No set-theoretic axiom is used. A Lean proof verifies its formal statement under its
hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Set Topology

namespace PG

namespace FamiliesSel

open Sel

/-- Images under an injection into `ℤ` of non-isomorphic ultrafilters are non-isomorphic. -/
theorem not_iso_of_map (y : ℕ → ℤ) (hy : Function.Injective y) {a b : Ultrafilter ℕ}
    (ha : ∀ x, a ≠ pure x) (hb : ∀ x, b ≠ pure x) (hab : ¬ Iso a b) :
    ¬ Iso (a.map y) (b.map y) := by
  rintro ⟨π, hπ⟩
  obtain ⟨E⟩ : Nonempty (ℤ ≃ ℕ) := ⟨Equiv.intEquivNat⟩
  have hinj : Function.Injective (fun n => E (y n)) := E.injective.comp hy
  have h1 : Iso a (a.map (fun n => E (y n))) :=
    iso_of_injOn ha _ (C := univ) Filter.univ_mem hinj.injOn
  have h2 : Iso b (b.map (fun n => E (y n))) :=
    iso_of_injOn hb _ (C := univ) Filter.univ_mem hinj.injOn
  have h3 : Iso (a.map (fun n => E (y n))) (b.map (fun n => E (y n))) := by
    refine ⟨(E.symm.trans π).trans E, ?_⟩
    have h4 := congrArg (Ultrafilter.map E) hπ
    rw [Ultrafilter.map_map, Ultrafilter.map_map] at h4
    rw [Ultrafilter.map_map]
    have e1 : (((E.symm.trans π).trans E : Equiv.Perm ℕ) : ℕ → ℕ) ∘ (fun n => E (y n))
        = (E ∘ (π : ℤ → ℤ)) ∘ y := by
      funext n
      simp
    have e2 : (fun n => E (y n)) = E ∘ y := rfl
    rw [e1, e2]
    exact h4
  exact hab ((h1.trans h3).trans h2.symm)

/-- Pairwise non-isomorphic selective ultrafilters on `ℤ` whose modification is not a group
topology, from selective ultrafilters on `ℕ` and a dominating family of functions. -/
theorem exists_selective_family {J : Type*} [Nonempty J] (y : ℕ → ℤ) (hy : Function.Injective y)
    (hpos : ∀ i, 0 < y i)
    (hgrow : ∀ B : ℕ, ∃ L : ℕ, ∀ l, L < l → 2 * (B : ℤ) * ∑ i ∈ Finset.range l, y i < y l)
    (v : J → Ultrafilter ℕ) (hv : ∀ j, IsSel (v j)) (hiso : ∀ i j, i ≠ j → ¬ Iso (v i) (v j))
    (g : J → ℕ → ℕ) (hdom : ∀ h : ℕ → ℕ, ∃ j, ∀ᶠ n in atTop, h n < g j n) :
    ∃ u : J → Ultrafilter ℤ, (∀ j, IsSel (u j)) ∧ (∀ i j, i ≠ j → ¬ Iso (u i) (u j)) ∧
      Function.Injective u ∧
      ¬ ∃ t : TopologicalSpace ℤ, @IsTopologicalAddGroup ℤ t _ ∧
        ∀ O : Set ℤ, IsOpen[t] O ↔ IsOpenMod (genFam (Sel.ultraGen (range u))) O := by
  classical
  set w : J → Ultrafilter ℕ := fun j => (v j).map (fun n => Nat.pair n (g j n)) with hw
  have hinj : ∀ j, Function.Injective (fun n => Nat.pair n (g j n)) := fun j a b hab =>
    (Nat.pair_eq_pair.1 hab).1
  have hwsel : ∀ j, IsSel (w j) := fun j => isSel_map_of_injective (hv j) _ (hinj j)
  have hvw : ∀ j, Iso (v j) (w j) := fun j =>
    iso_of_injOn (hv j).1 _ (C := univ) Filter.univ_mem (hinj j).injOn
  have hwiso : ∀ i j, i ≠ j → ¬ Iso (w i) (w j) := fun i j hij h =>
    hiso i j hij (((hvw i).trans h).trans (hvw j).symm)
  set u : J → Ultrafilter ℤ := fun j => (w j).map y with hu
  have husel : ∀ j, IsSel (u j) := fun j => isSel_map_of_injective (hwsel j) y hy
  have huiso : ∀ i j, i ≠ j → ¬ Iso (u i) (u j) := fun i j hij =>
    not_iso_of_map y hy (hwsel i).1 (hwsel j).1 (hwiso i j hij)
  have huinj : Function.Injective u := by
    intro i j hij
    by_contra hne
    refine huiso i j hne ⟨Equiv.refl ℤ, ?_⟩
    rw [show ((Equiv.refl ℤ : Equiv.Perm ℤ) : ℤ → ℤ) = id from rfl, Ultrafilter.map_id]
    exact hij
  refine ⟨u, husel, huiso, huinj, ?_⟩
  rintro ⟨t, ht, hopen⟩
  obtain ⟨O, h0, hO, hno⟩ :=
    Families.exists_open_not_nhds_of_dominating y v (fun j => (hv j).1) g hdom hpos hgrow
  have hCnull : NullFamily (genFam (Sel.ultraGen (range u))) := genFam_nullFamily _
  have huC : ∀ j, (u j : Filter ℤ) ∈ genFam (Sel.ultraGen (range u)) := fun j =>
    ⟨(u j).neBot, fun U hU => ⟨_, SumClosure.gen ⟨u j, mem_range_self j, rfl⟩, hU⟩⟩
  have hOt : IsOpen[t] O := (hopen O).2 hO
  refine hno t ht (fun j => ?_) (@IsOpen.mem_nhds ℤ t 0 O hOt h0)
  intro A hA
  obtain ⟨B, hBA, hBo, hB0⟩ := (@mem_nhds_iff ℤ t 0 A).1 hA
  refine mem_of_superset ?_ hBA
  exact (hopen B).1 hBo 0 hB0 _ (u j).neBot ((conv_zero _ _).2 (huC j))

/-- A selective ultrafilter with a base indexed by `J` gives a family of functions indexed
by `J` that dominates every function. -/
theorem dominating_of_base {J : Type*} {w : Ultrafilter ℕ} (hw : IsSel w) (b : J → Set ℕ)
    (hb : ∀ j, b j ∈ w) (hbase : ∀ A ∈ w, ∃ j, b j ⊆ A) :
    ∃ g : J → ℕ → ℕ, ∀ h : ℕ → ℕ, ∃ j, ∀ᶠ n in atTop, h n < g j n := by
  classical
  refine ⟨fun j n => Nat.nth (fun x => x ∈ b j) n + 1, fun h => ?_⟩
  let t : ℕ → ℕ := fun n => Nat.rec 0 (fun m s => s + 1 + h (m + 1)) n
  have ht0 : t 0 = 0 := rfl
  have htsucc : ∀ m, t (m + 1) = t m + 1 + h (m + 1) := fun m => rfl
  have htmono : StrictMono t := strictMono_nat_of_lt_succ (fun m => by
    rw [htsucc]; omega)
  have hth : ∀ m, 1 ≤ m → h m ≤ t m := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [htsucc]; omega
  have hex : ∀ x : ℕ, ∃ m : ℕ, x < t (m + 1) := fun x =>
    ⟨x, Nat.lt_of_lt_of_le (Nat.lt_succ_self x) (htmono.id_le (x + 1))⟩
  let p : ℕ → ℕ := fun x => Nat.find (hex x)
  have hplt : ∀ x, x < t (p x + 1) := fun x => Nat.find_spec (hex x)
  have hp : ∀ x, t (p x) ≤ x := by
    intro x
    rcases Nat.eq_zero_or_pos (p x) with h0 | h0
    · rw [h0, ht0]
      exact Nat.zero_le x
    · have h1 : ¬ x < t (p x - 1 + 1) := Nat.find_min (hex x) (Nat.sub_lt h0 Nat.one_pos)
      rw [show p x - 1 + 1 = p x by omega] at h1
      exact not_lt.1 h1
  have hpge : ∀ x m, t m ≤ x → m ≤ p x := fun x m hm => by
    have h1 : t m < t (p x + 1) := lt_of_le_of_lt hm (hplt x)
    exact Nat.lt_succ_iff.1 (htmono.lt_iff_lt.1 h1)
  have hpmono : Monotone p := fun a c hac => hpge c (p a) ((hp a).trans hac)
  have hpfib : ∀ c, {x | p x = c}.Finite := by
    intro c
    refine (finite_Iio (t (c + 1))).subset (fun x hx => ?_)
    show x < t (c + 1)
    by_contra hc
    have h1 := hpge x (c + 1) (not_lt.1 hc)
    have h2 : p x = c := hx
    omega
  obtain ⟨C, hC, hinj⟩ := hw.injOn_of_finite_fibres p hpfib
  obtain ⟨j, hj⟩ := hbase C hC
  refine ⟨j, eventually_atTop.2 ⟨1, fun n hn => ?_⟩⟩
  have hbinf : (setOf (fun x => x ∈ b j)).Infinite := infinite_of_mem hw.1 (hb j)
  have hmem : ∀ k, Nat.nth (fun x => x ∈ b j) k ∈ b j := fun k =>
    Nat.nth_mem_of_infinite hbinf k
  have hstrict : StrictMono (fun k => p (Nat.nth (fun x => x ∈ b j) k)) := by
    intro k l hkl
    have h1 : Nat.nth (fun x => x ∈ b j) k < Nat.nth (fun x => x ∈ b j) l :=
      Nat.nth_strictMono hbinf hkl
    refine lt_of_le_of_ne (hpmono h1.le) (fun heq => ?_)
    exact h1.ne (hinj (hj (hmem k)) (hj (hmem l)) heq)
  have h2 : n ≤ p (Nat.nth (fun x => x ∈ b j) n) := hstrict.id_le n
  have h3 : t n ≤ Nat.nth (fun x => x ∈ b j) n :=
    (htmono.monotone h2).trans (hp _)
  have h4 := hth n hn
  show h n < Nat.nth (fun x => x ∈ b j) n + 1
  omega

/-- Case (b) of the corollary on uncountably many selective ultrafilters, obtained through
the dominating construction. -/
theorem exists_selective_family_of_base {J : Type*} [Nonempty J] (y : ℕ → ℤ)
    (hy : Function.Injective y) (hpos : ∀ i, 0 < y i)
    (hgrow : ∀ B : ℕ, ∃ L : ℕ, ∀ l, L < l → 2 * (B : ℤ) * ∑ i ∈ Finset.range l, y i < y l)
    (v : J → Ultrafilter ℕ) (hv : ∀ j, IsSel (v j)) (hiso : ∀ i j, i ≠ j → ¬ Iso (v i) (v j))
    (w : Ultrafilter ℕ) (hw : IsSel w) (b : J → Set ℕ) (hb : ∀ j, b j ∈ w)
    (hbase : ∀ A ∈ w, ∃ j, b j ⊆ A) :
    ∃ u : J → Ultrafilter ℤ, (∀ j, IsSel (u j)) ∧ (∀ i j, i ≠ j → ¬ Iso (u i) (u j)) ∧
      Function.Injective u ∧
      ¬ ∃ t : TopologicalSpace ℤ, @IsTopologicalAddGroup ℤ t _ ∧
        ∀ O : Set ℤ, IsOpen[t] O ↔ IsOpenMod (genFam (Sel.ultraGen (range u))) O := by
  obtain ⟨g, hg⟩ := dominating_of_base hw b hb hbase
  exact exists_selective_family y hy hpos hgrow v hv hiso g hg

/-- Case (a) of the corollary on uncountably many selective ultrafilters, including that the
images are selective and pairwise non-isomorphic. -/
theorem exists_selective_family_of_card {J : Type} (y : ℕ → ℤ)
    (hy : Function.Injective y) (hpos : ∀ i, 0 < y i)
    (hgrow : ∀ B : ℕ, ∃ L : ℕ, ∀ l, L < l → 2 * (B : ℤ) * ∑ i ∈ Finset.range l, y i < y l)
    (v : J → Ultrafilter ℕ) (hv : ∀ j, IsSel (v j)) (hiso : ∀ i j, i ≠ j → ¬ Iso (v i) (v j))
    (hcard : Cardinal.mk (Set ℕ) < Cardinal.mk (J → Bool)) :
    ∃ u : J → Ultrafilter ℤ, (∀ j, IsSel (u j)) ∧ (∀ i j, i ≠ j → ¬ Iso (u i) (u j)) ∧
      Function.Injective u ∧
      ¬ ∃ t : TopologicalSpace ℤ, @IsTopologicalAddGroup ℤ t _ ∧
        ∀ O : Set ℤ, IsOpen[t] O ↔ IsOpenMod (genFam (Sel.ultraGen (range u))) O := by
  classical
  obtain ⟨ε, hε⟩ := Uncountable.exists_unseparated_of_card v hcard
  have hvinj : Function.Injective v := by
    intro i j hij
    by_contra hne
    refine hiso i j hne ⟨Equiv.refl ℕ, ?_⟩
    rw [show ((Equiv.refl ℕ : Equiv.Perm ℕ) : ℕ → ℕ) = id from rfl, Ultrafilter.map_id]
    exact hij
  have hvcof : ∀ j, (v j : Filter ℕ) ≤ cofinite := fun j => by
    rcases Ultrafilter.le_cofinite_or_eq_pure (v j) with h | ⟨a, ha⟩
    · exact h
    · exact absurd ha ((hv j).1 a)
  have hidx : ∀ j, Function.Injective (fun n => y (Uncountable.idx (ε j) n)) := by
    intro j a b hab
    have h1 := hy hab
    unfold Uncountable.idx at h1
    omega
  set u : J → Ultrafilter ℤ := Uncountable.gen y ε v with hu
  have husel : ∀ j, IsSel (u j) := fun j => isSel_map_of_injective (hv j) _ (hidx j)
  have huiso : ∀ i j, i ≠ j → ¬ Iso (u i) (u j) := by
    intro i j hij h
    have h1 : ∀ k, Iso (v k) ((v k).map (fun n => Uncountable.idx (ε k) n)) := fun k => by
      refine iso_of_injOn (hv k).1 _ (C := univ) Filter.univ_mem (Function.Injective.injOn ?_)
      intro a b hab
      simp only [Uncountable.idx] at hab
      omega
    have h2 : ∀ k, u k = ((v k).map (fun n => Uncountable.idx (ε k) n)).map y := fun k => by
      rw [Ultrafilter.map_map]
      rfl
    have h3 : ∀ k, ∀ a, (v k).map (fun n => Uncountable.idx (ε k) n) ≠ pure a := fun k =>
      (isSel_map_of_injective (hv k) _ (fun a b hab => by
        simp only [Uncountable.idx] at hab
        omega)).1
    rw [h2 i, h2 j] at h
    refine not_iso_of_map y hy (h3 i) (h3 j) (fun h4 => ?_) h
    exact hiso i j hij (((h1 i).trans h4).trans (h1 j).symm)
  have huinj : Function.Injective u := by
    intro i j hij
    by_contra hne
    refine huiso i j hne ⟨Equiv.refl ℤ, ?_⟩
    rw [show ((Equiv.refl ℤ : Equiv.Perm ℤ) : ℤ → ℤ) = id from rfl, Ultrafilter.map_id]
    exact hij
  exact ⟨u, husel, huiso, huinj, Uncountable.not_isGroupTopology y ε v hpos hgrow hvinj hvcof hε⟩

end FamiliesSel

end PG
