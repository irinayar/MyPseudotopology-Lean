import Mathlib
import LeanCheck.PGThreeFamilies

/-!
# PGfour: groupwise density and families of P-points

A family `F` of subsets of `ℕ` is *groupwise dense* if its members are infinite, it contains
every infinite almost-subset of a member, and for every partition of `ℕ` into finite
intervals some union of infinitely many of the intervals belongs to it. The groupwise
density number is the least number of groupwise dense families with no common member; the
hypothesis "`J` has fewer elements than that number" is stated as `Meets J`.

* `above_dense` : for a nonprincipal ultrafilter `v` and a function `h`, the sets whose
  next-element function exceeds `h` on a member of `v` form a groupwise dense family;
* `above_cofinal` : consequently, no family indexed by `J` is cofinal in the ultrapower;
* `common_pfilter_of_groupwise` : the common members of P-points indexed by `J` form a
  P-filter;
* `no_injection_of_groupwise` : there is no injection of the Cantor set into `J`;
* `pfilter_modification_of_groupwise` : openness for the modification of the PG generated
  by all ultrafilters containing every common member is openness for a group topology, the
  finest group topology of the PG of the P-points;
* `exists_open_not_nhds_of_copies` : if the functions `g j` are cofinal in the ultrapower
  by `v`, the images under a rapidly growing sequence of the copies of `v` placed on their
  graphs generate a PG whose modification is not given by a group topology.

No set-theoretic axiom is used. A Lean proof verifies its formal statement under its
hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Set Topology

open scoped Cardinal

namespace PG

namespace Groupwise

open PPoint

/-- Groupwise dense family of subsets of `ℕ`. -/
def GroupwiseDense (F : Set (Set ℕ)) : Prop :=
  (∀ X ∈ F, X.Infinite) ∧
  (∀ X ∈ F, ∀ Y : Set ℕ, Y.Infinite → (Y \ X).Finite → Y ∈ F) ∧
  (∀ a : ℕ → ℕ, StrictMono a → a 0 = 0 → ∃ K : Set ℕ, K.Infinite ∧ (⋃ k ∈ K, Ico (a k) (a (k + 1))) ∈ F)

/-- `J` is smaller than the groupwise density number. -/
def Meets (J : Type*) : Prop :=
  ∀ F : J → Set (Set ℕ), (∀ j, GroupwiseDense (F j)) → ∃ X : Set ℕ, ∀ j, X ∈ F j

/-- The least element of `X` above `n`. -/
noncomputable def nxt (X : Set ℕ) (n : ℕ) : ℕ := sInf {x | x ∈ X ∧ n < x}

theorem nxt_spec {X : Set ℕ} (hX : X.Infinite) (n : ℕ) : nxt X n ∈ X ∧ n < nxt X n := by
  obtain ⟨x, hx, hnx⟩ := hX.exists_gt n
  exact Nat.sInf_mem (s := {x | x ∈ X ∧ n < x}) ⟨x, hx, hnx⟩

theorem nxt_mono {X : Set ℕ} (hX : X.Infinite) : Monotone (nxt X) := fun a b hab =>
  Nat.sInf_le ⟨(nxt_spec hX b).1, lt_of_le_of_lt hab (nxt_spec hX b).2⟩

/-- The sets whose next-element function exceeds `h` on a member of `v`. -/
def Above (v : Ultrafilter ℕ) (h : ℕ → ℕ) : Set (Set ℕ) :=
  {X | X.Infinite ∧ {n | h n < nxt X n} ∈ v}

theorem above_dense (v : Ultrafilter ℕ) (hv : ∀ a, v ≠ pure a) (h : ℕ → ℕ) :
    GroupwiseDense (Above v h) := by
  classical
  refine ⟨fun X hX => hX.1, fun X hX Y hY hfin => ⟨hY, ?_⟩, fun a ha ha0 => ?_⟩
  · obtain ⟨M, hM⟩ := hfin.bddAbove
    have hbig : {n : ℕ | M < n} ∈ v := by
      rcases v.mem_or_compl_mem {n : ℕ | M < n} with h' | h'
      · exact h'
      · refine absurd h' (Sel.notMem_of_finite hv ((finite_Iic M).subset (fun n hn => ?_)))
        have : ¬ M < n := hn
        exact mem_Iic.2 (by omega)
    refine Filter.mem_of_superset (Filter.inter_mem (f := (v : Filter ℕ)) hX.2 hbig) (fun n hn => ?_)
    have h1 := nxt_spec hY n
    have h2 : nxt Y n ∈ X := by
      by_contra hc
      have h3 : nxt Y n ≤ M := hM ⟨h1.1, hc⟩
      have h4 : M < n := hn.2
      omega
    have h5 : nxt X n ≤ nxt Y n := Nat.sInf_le ⟨h2, h1.2⟩
    exact lt_of_lt_of_le hn.1 h5
  · let H : ℕ → ℕ := fun m => (Finset.range (m + 1)).sup h
    have hH : ∀ n m, n ≤ m → h n ≤ H m := fun n m hnm =>
      Finset.le_sup (f := h) (Finset.mem_range.2 (Nat.lt_succ_of_le hnm))
    let k : ℕ → ℕ := fun i => Nat.rec 0 (fun _ p => max (p + 1) (H (a (p + 1)) + 1)) i
    have hks : ∀ i, k (i + 1) = max (k i + 1) (H (a (k i + 1)) + 1) := fun i => rfl
    have hkmono : StrictMono k := strictMono_nat_of_lt_succ (fun i => by
      rw [hks]; exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))
    have hkbig : ∀ i, H (a (k i + 1)) < a (k (i + 1)) := fun i => by
      refine lt_of_lt_of_le ?_ (ha.id_le _)
      show H (a (k i + 1)) < k (i + 1)
      rw [hks]
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    let X : ℕ → Set ℕ := fun b => ⋃ m ∈ range (fun i => k (2 * i + b)), Ico (a m) (a (m + 1))
    have hmemX : ∀ b x, x ∈ X b ↔ ∃ i, a (k (2 * i + b)) ≤ x ∧ x < a (k (2 * i + b) + 1) := by
      intro b x
      show x ∈ (⋃ m ∈ range (fun i => k (2 * i + b)), Ico (a m) (a (m + 1))) ↔ _
      rw [mem_iUnion₂]
      constructor
      · rintro ⟨m, ⟨i, rfl⟩, hx⟩
        exact ⟨i, hx.1, hx.2⟩
      · rintro ⟨i, h1, h2⟩
        exact ⟨_, ⟨i, rfl⟩, h1, h2⟩
    have hinj : ∀ b, Function.Injective (fun i => k (2 * i + b)) := fun b i j hij => by
      have := hkmono.injective hij
      omega
    have hXinf : ∀ b, (X b).Infinite := fun b => by
      refine Set.infinite_of_injective_forall_mem (f := fun i => a (k (2 * i + b)))
        (ha.injective.comp (hinj b)) (fun i => ?_)
      exact (hmemX b _).2 ⟨i, le_rfl, ha (Nat.lt_succ_self _)⟩
    have key : ∀ n, h n < nxt (X 0) n ∨ h n < nxt (X 1) n := by
      intro n
      have h0 := nxt_spec (hXinf 0) n
      have h1 := nxt_spec (hXinf 1) n
      obtain ⟨i, hi1, hi2⟩ := (hmemX 0 _).1 h0.1
      obtain ⟨j, hj1, hj2⟩ := (hmemX 1 _).1 h1.1
      have far : ∀ p q x z : ℕ, p < q → x < a (k p + 1) → a (k q) ≤ z → n < x → h n < z := by
        intro p q x z hpq hx hz hnx
        have h2 : H (a (k p + 1)) < a (k (p + 1)) := hkbig p
        have h3 : a (k (p + 1)) ≤ a (k q) := ha.monotone (hkmono.monotone (Nat.succ_le_of_lt hpq))
        have h4 : h n ≤ H (a (k p + 1)) := hH n _ (le_of_lt (lt_trans hnx hx))
        omega
      rcases Nat.lt_or_ge (2 * i + 0) (2 * j + 1) with hlt | hge
      · exact Or.inr (far _ _ _ _ hlt hi2 hj1 h0.2)
      · have hlt' : 2 * j + 1 < 2 * i + 0 := by omega
        exact Or.inl (far _ _ _ _ hlt' hj2 hi1 h1.2)
    have hun : {n | h n < nxt (X 0) n} ∪ {n | h n < nxt (X 1) n} ∈ v := by
      refine Filter.mem_of_superset (Filter.univ_mem (f := (v : Filter ℕ))) (fun n _ => ?_)
      exact key n
    have hKinf : ∀ b, (range (fun i => k (2 * i + b))).Infinite := fun b =>
      infinite_range_of_injective (hinj b)
    rcases Ultrafilter.union_mem_iff.1 hun with h' | h'
    · exact ⟨_, hKinf 0, hXinf 0, h'⟩
    · exact ⟨_, hKinf 1, hXinf 1, h'⟩

section Consequences

variable {J : Type*} [Nonempty J]

/-- No family of fewer functions than the groupwise density number is cofinal in an
ultrapower: some function exceeds each of them on a member of `v`. -/
theorem above_cofinal (hg : Meets J) (v : Ultrafilter ℕ) (hv : ∀ a, v ≠ pure a) (g : J → ℕ → ℕ) :
    ∃ h : ℕ → ℕ, ∀ j, {n | g j n < h n} ∈ v := by
  obtain ⟨X, hX⟩ := hg (fun j => Above v (g j)) (fun j => above_dense v hv (g j))
  exact ⟨nxt X, fun j => (hX j).2⟩

/-- There is no injection of the Cantor set into `J`. -/
theorem no_injection_of_groupwise (hg : Meets J) : ¬ ∃ J0 : (ℕ → Bool) → J, Function.Injective J0 := by
  classical
  rintro ⟨J0, hJ0⟩
  have hcard : #(ℕ → ℕ) = #(ℕ → Bool) := by
    simp [Cardinal.mk_arrow, Cardinal.power_self_eq]
  obtain ⟨E⟩ := Cardinal.eq.1 hcard
  haveI : Nonempty (ℕ → Bool) := ⟨fun _ => false⟩
  have hv : ∀ a, hyperfilter ℕ ≠ pure a := fun a h => by
    have h1 : ({a} : Set ℕ) ∈ hyperfilter ℕ := by
      rw [h]; exact Ultrafilter.mem_pure.2 rfl
    exact notMem_hyperfilter_of_finite (finite_singleton a) h1
  obtain ⟨h, hh⟩ := above_cofinal hg (hyperfilter ℕ) hv (fun j => E.symm (Function.invFun J0 j))
  have h1 := hh (J0 (E h))
  rw [Function.leftInverse_invFun hJ0 _, E.symm_apply_apply] at h1
  obtain ⟨n, hn⟩ := Ultrafilter.nonempty_of_mem h1
  exact lt_irrefl _ (show h n < h n from hn)

variable {G : Type*} [AddCommGroup G]

omit [AddCommGroup G] in
/-- The common members of P-points indexed by `J` form a P-filter. -/
theorem common_pfilter_of_groupwise (hg : Meets J) (e : ℕ ≃ G) (u : J → Ultrafilter G)
    (hu : ∀ j, IsPPoint (u j)) (B : ℕ → Set G) (hB : ∀ m j, B m ∈ u j) :
    ∃ A : Set G, (∀ j, A ∈ u j) ∧ ∀ m, (A \ B m).Finite := by
  classical
  let B' : ℕ → Set G := fun m => ⋂ k ∈ Finset.range (m + 1), B k
  have hB' : ∀ m j, B' m ∈ u j := fun m j =>
    (Filter.biInter_finset_mem _).2 (fun k _ => hB k j)
  have hmono : ∀ a b, a ≤ b → B' b ⊆ B' a := fun a b hab x hx => by
    refine mem_iInter₂.2 (fun k hk => mem_iInter₂.1 hx k (Finset.mem_range.2 ?_))
    have := Finset.mem_range.1 hk
    omega
  have hC : ∀ j, ∃ C ∈ u j, ∀ m, (C \ B' m).Finite := fun j =>
    (hu j).pseudoInter B' (fun m => hB' m j)
  choose C hCmem hCfin using hC
  have hfin : ∀ j m, (e ⁻¹' (C j \ B' m)).Finite := fun j m =>
    (hCfin j m).preimage e.injective.injOn
  let h : J → ℕ → ℕ := fun j m => (hfin j m).toFinset.sup id
  let D : Set G := ⋂ m, B' m
  let φ : G → ℕ := fun x => sInf {n | x ∉ B' n}
  have hφ : ∀ x, x ∉ D → x ∉ B' (φ x) := by
    intro x hx
    have h1 : {n | x ∉ B' n}.Nonempty := by
      by_contra hne
      exact hx (mem_iInter.2 (fun n => not_not.1 (fun hn => hne ⟨n, hn⟩)))
    exact Nat.sInf_mem h1
  have hhyp : ∀ a, hyperfilter ℕ ≠ pure a := fun a h => by
    have h1 : ({a} : Set ℕ) ∈ hyperfilter ℕ := by
      rw [h]; exact Ultrafilter.mem_pure.2 rfl
    exact notMem_hyperfilter_of_finite (finite_singleton a) h1
  let w : J → Ultrafilter ℕ := fun j => if D ∈ u j then hyperfilter ℕ else (u j).map φ
  have hw : ∀ j a, w j ≠ pure a := by
    intro j a heq
    by_cases hD : D ∈ u j
    · have h1 : w j = hyperfilter ℕ := if_pos hD
      exact hhyp a (h1.symm.trans heq)
    · have h1 : w j = (u j).map φ := if_neg hD
      have h2 : ({a} : Set ℕ) ∈ (u j).map φ := by
        rw [← h1, heq]; exact Ultrafilter.mem_pure.2 rfl
      rw [Ultrafilter.mem_map] at h2
      have h3 : Dᶜ ∈ u j := by
        rcases (u j).mem_or_compl_mem D with h' | h'
        · exact absurd h' hD
        · exact h'
      obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := Ultrafilter.nonempty_of_mem
        (Filter.inter_mem (Filter.inter_mem (f := (u j : Filter G)) h2 h3) (hB' a j))
      have h4 : φ x = a := hx1
      exact (h4 ▸ hφ x hx2) hx3
  obtain ⟨X, hX⟩ := hg (fun j => Above (w j) (h j)) (fun j => above_dense (w j) (hw j) (h j))
  have hXinf : X.Infinite := by
    obtain ⟨j⟩ := ‹Nonempty J›
    exact (hX j).1
  let f : ℕ → ℕ := nxt X
  have hfmono : Monotone f := nxt_mono hXinf
  let A : Set G := {x | ∀ n, x ∉ B' n → e.symm x < f n}
  refine ⟨A, fun j => ?_, fun m => ?_⟩
  · by_cases hD : D ∈ u j
    · exact Filter.mem_of_superset hD (fun x hx n hn => absurd (mem_iInter.1 hx n) hn)
    · have h1 : w j = (u j).map φ := if_neg hD
      have h2 : {n | h j n < f n} ∈ (u j).map φ := h1 ▸ (hX j).2
      rw [Ultrafilter.mem_map] at h2
      have h3 : Dᶜ ∈ u j := by
        rcases (u j).mem_or_compl_mem D with h' | h'
        · exact absurd h' hD
        · exact h'
      refine Filter.mem_of_superset
        (Filter.inter_mem (Filter.inter_mem (f := (u j : Filter G)) h2 h3) (hCmem j)) (fun x hx n hn => ?_)
      have hxD : x ∉ D := hx.1.2
      have hlt : h j (φ x) < f (φ x) := hx.1.1
      have hle : φ x ≤ n := Nat.sInf_le (s := {n | x ∉ B' n}) hn
      have h4 : e.symm x ∈ (hfin j (φ x)).toFinset := by
        refine (hfin j (φ x)).mem_toFinset.2 ?_
        show e (e.symm x) ∈ C j \ B' (φ x)
        rw [e.apply_symm_apply]
        exact ⟨hx.2, hφ x hxD⟩
      have h5 : e.symm x ≤ h j (φ x) := Finset.le_sup (f := id) h4
      exact lt_of_le_of_lt h5 (lt_of_lt_of_le hlt (hfmono hle))
  · have h1 : {x : G | e.symm x < f m}.Finite :=
      ((finite_Iio (f m)).image e).subset (fun x hx => ⟨e.symm x, hx, e.apply_symm_apply x⟩)
    refine h1.subset (fun x hx => ?_)
    have h2 : x ∉ B' m := fun hc => hx.2 (mem_iInter₂.1 hc m (Finset.mem_range.2 (Nat.lt_succ_self m)))
    exact hx.1 m h2

end Consequences

section Modification

variable {G : Type*} [AddCommGroup G] {J : Type*} [Nonempty J]

/-- Openness for the modification of the PG generated by all ultrafilters containing every
common member is openness for a group topology, the finest group topology of the PG of the
P-points. -/
theorem pfilter_modification_of_groupwise (e : ℕ ≃ G) (u : J → Ultrafilter G)
    (hu : ∀ j, IsPPoint (u j))
    (hg : Meets J) :
    ∃ t : TopologicalSpace G, @IsTopologicalAddGroup G t _ ∧
      (∀ O : Set G, IsOpen[t] O ↔
        IsOpenMod (genFam (Sel.ultraGen {v : Ultrafilter G | (v : Filter G) ≤ ⨆ j, (u j : Filter G)})) O) ∧
      (∀ S : Set G, S ∈ @nhds G t 0 ↔ ∃ A : ℕ → Set G, (∀ i j, A i ∈ u j) ∧ Uset A ⊆ S) ∧
      IsFinest (genFam (Sel.ultraGen (range u))) t := by
  classical
  set Φ : Filter G := ⨆ j, (u j : Filter G) with hΦ
  have hmemΦ : ∀ S : Set G, S ∈ Φ ↔ ∀ j, S ∈ u j := fun S => Filter.mem_iSup
  set K : Set (Ultrafilter G) := {v : Ultrafilter G | (v : Filter G) ≤ Φ} with hK
  have huK : ∀ j, u j ∈ K := fun j => le_iSup (fun j => (u j : Filter G)) j
  set C : Set (Filter G) := genFam (Sel.ultraGen K) with hC
  have hCnull : NullFamily C := genFam_nullFamily _
  set N : Filter G :=
    { sets := {S | ∃ A : ℕ → Set G, (∀ i j, A i ∈ u j) ∧ Uset A ⊆ S}
      univ_sets := ⟨fun _ => univ, fun _ _ => Filter.univ_mem, subset_univ _⟩
      sets_of_superset := by
        rintro S T ⟨A, hA, h⟩ hST
        exact ⟨A, hA, h.trans hST⟩
      inter_sets := by
        rintro S T ⟨A, hA, h⟩ ⟨B, hB, h'⟩
        exact ⟨fun i => A i ∩ B i, fun i j => Filter.inter_mem (hA i j) (hB i j),
          subset_inter ((Uset_mono (fun _ => inter_subset_left)).trans h)
            ((Uset_mono (fun _ => inter_subset_right)).trans h')⟩ } with hNdef
  have hmemN : ∀ S, S ∈ N ↔ ∃ A : ℕ → Set G, (∀ i j, A i ∈ u j) ∧ Uset A ⊆ S := fun S => Iff.rfl
  have hN : IsNbhdFilter N := by
    refine ⟨fun S hS => ?_, fun S hS => ?_, fun S hS => ?_⟩
    · obtain ⟨A, _, h⟩ := (hmemN S).1 hS
      exact h (zero_mem_Uset _)
    · obtain ⟨A, hA, h⟩ := (hmemN S).1 hS
      exact (hmemN _).2 ⟨A, hA, fun x hx => h (neg_mem_Uset _ hx)⟩
    · obtain ⟨A, hA, h⟩ := (hmemN S).1 hS
      refine ⟨Uset (fun i => A (2 * i) ∩ A (2 * i + 1)),
        (hmemN _).2 ⟨_, fun i j => Filter.inter_mem (hA _ j) (hA _ j), subset_rfl⟩,
        fun x hx y hy => h (Uset_halve A hx hy)⟩
  obtain ⟨t, ht, hnhds⟩ := exists_topology hN
  have hΦN : Φ ≤ N := by
    intro S hS
    obtain ⟨A, hA, h⟩ := (hmemN S).1 hS
    have h1 : A 0 ∈ Φ := (hmemΦ _).2 (hA 0)
    refine Filter.mem_of_superset h1 (fun x hx => h ?_)
    refine ⟨1, fun _ => x, fun i hi => ?_, by simp⟩
    rw [Nat.lt_one_iff.1 hi]
    exact Or.inr (Or.inl hx)
  have hgenne : ∀ S : Set (Ultrafilter G), ∀ F ∈ Sel.ultraGen S, F.NeBot := by
    rintro S F ⟨v, _, rfl⟩
    exact v.neBot
  have hgen : ∀ v ∈ K, (v : Filter G) ∈ C := fun v hv =>
    subset_genFam (hgenne K) ⟨v, hv, rfl⟩
  have hΦne : Φ.NeBot := by
    obtain ⟨j⟩ := ‹Nonempty J›
    exact Filter.NeBot.mono (u j).neBot (huK j)
  have hΦC : Φ ∈ C :=
    hCnull.ultra Φ hΦne (fun U hU => hgen U hU)
  have hcoarse : ∀ (D : Set (Filter G)) (t' : TopologicalSpace G), @IsTopologicalAddGroup G t' _ →
      (∀ F ∈ D, F ≤ @nhds G t' 0) → ∀ O : Set G, IsOpen[t'] O → IsOpenMod D O := by
    intro D t' ht' hF' O hO x hx F hne hconv
    letI := t'
    haveI := ht'
    have h1 : F ≤ 𝓝 x := (le_nhds_iff_map_sub F x).2 (hF' _ hconv)
    exact h1 (hO.mem_nhds hx)
  have htC : ∀ F ∈ C, F ≤ @nhds G t 0 := by
    have h1 : Sel.ultraGen K ⊆ @nullTop G t _ := by
      rintro F ⟨v, hv, rfl⟩
      refine ⟨v.neBot, ?_⟩
      rw [hnhds]; exact le_trans hv hΦN
    have h2 : C ⊆ @nullTop G t _ := by
      letI := t
      haveI := ht
      exact genFam_le nullTop_nullFamily h1
    exact fun F hF => (h2 hF).2
  have hopT : ∀ O : Set G, IsOpenMod C O → ∀ x ∈ O, ∀ k : ℕ, ∃ S : Set G, (∀ j, S ∈ u j) ∧
      ∀ T : Finset ℕ, T.card ≤ k → ∀ a : ℕ → G, (∀ i ∈ T, a i ∈ S ∨ -a i ∈ S) → x + ∑ i ∈ T, a i ∈ O := by
    intro O hO x hx k
    set F : Filter G := pure 0 ⊔ (Φ ⊔ Filter.map (fun z : G => -z) Φ) with hF
    have hFne : F.NeBot := Filter.NeBot.mono (inferInstance : (pure (0 : G) : Filter G).NeBot) le_sup_left
    have hFC : F ∈ C := by
      refine hCnull.ultra F hFne (fun U hU => ?_)
      rcases (Ultrafilter.le_sup_iff).1 hU with h | h
      · exact hCnull.finer _ hCnull.pure_zero _ h inferInstance
      · rcases (Ultrafilter.le_sup_iff).1 h with h4 | h4
        · exact hCnull.finer _ hΦC _ h4 inferInstance
        · exact hCnull.finer _ (hCnull.neg _ hΦC) _ h4 inferInstance
    let Fk : ℕ → Filter G := fun n => Nat.rec (pure 0) (fun _ H => Filter.map₂ (· + ·) H F) n
    have hFkC : ∀ n, Fk n ∈ C := by
      intro n
      induction n with
      | zero => exact hCnull.pure_zero
      | succ n ih => exact hCnull.add _ ih _ hFC
    have hkey : ∀ n, ∀ s ∈ Fk n, ∃ S ∈ F, ∀ T : Finset ℕ, T.card ≤ n → ∀ a : ℕ → G, (∀ i ∈ T, a i ∈ S) →
        ∑ i ∈ T, a i ∈ s := by
      intro n
      induction n with
      | zero =>
        intro s hs
        have h0s : (0 : G) ∈ s := Filter.mem_pure.1 hs
        refine ⟨univ, Filter.univ_mem, fun T hT a _ => ?_⟩
        rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hT), Finset.sum_empty]
        exact h0s
      | succ n ih =>
        intro s hs
        obtain ⟨s1, hs1, s2, hs2, hsub⟩ := Filter.mem_map₂_iff.1 hs
        obtain ⟨S1, hS1, h1⟩ := ih s1 hs1
        refine ⟨S1 ∩ s2, Filter.inter_mem hS1 hs2, fun T hT a ha => ?_⟩
        have h0s2 : (0 : G) ∈ s2 := Filter.mem_pure.1 ((le_sup_left : pure (0 : G) ≤ F) hs2)
        rcases T.eq_empty_or_nonempty with hTe | ⟨i0, hi0⟩
        · rw [hTe, Finset.sum_empty]
          have h0s1 : (0 : G) ∈ s1 := by
            have := h1 ∅ (Nat.zero_le _) a (fun i hi => by simp at hi)
            simpa using this
          have := hsub (mem_image2_of_mem h0s1 h0s2)
          simpa using this
        · rw [← Finset.sum_erase_add T a hi0]
          refine hsub (mem_image2_of_mem (h1 _ ?_ a (fun i hi => (ha i (Finset.mem_of_mem_erase hi)).1))
            (ha i0 hi0).2)
          rw [Finset.card_erase_of_mem hi0]
          omega
    have hconv : conv C (Filter.map (fun z : G => x + z) (Fk k)) x := by
      unfold conv
      rw [Filter.map_map]
      have : ((fun y : G => y - x) ∘ fun z : G => x + z) = id := by funext z; simp
      rw [this, Filter.map_id]
      exact hFkC k
    have hFkne : (Fk k).NeBot := hCnull.ne _ (hFkC k)
    have hmem := hO x hx _ (Filter.NeBot.map hFkne _) hconv
    obtain ⟨S, hS, h⟩ := hkey k _ (Filter.mem_map.1 hmem)
    refine ⟨S ∩ (fun z : G => -z) ⁻¹' S, fun j => ?_, fun T hT a ha => h T hT a (fun i hi => ?_)⟩
    · have h1 : S ∈ Φ ⊔ Filter.map (fun z : G => -z) Φ :=
        (le_sup_right : Φ ⊔ Filter.map (fun z : G => -z) Φ ≤ F) hS
      exact Filter.inter_mem ((hmemΦ _).1 h1.1 j) ((hmemΦ _).1 h1.2 j)
    · rcases ha i hi with h' | h'
      · exact h'.1
      · have h2 : - -a i ∈ S := h'.2
        rwa [neg_neg] at h2
  have hP : ∀ B : ℕ → Set G, (∀ m j, B m ∈ u j) → ∃ A : Set G, (∀ j, A ∈ u j) ∧ ∀ m, (A \ B m).Finite :=
    common_pfilter_of_groupwise hg e u hu
  have hopen : ∀ O : Set G, IsOpen[t] O ↔ IsOpenMod C O := by
    intro O
    refine ⟨hcoarse C t ht htC O, fun hO => ?_⟩
    letI := t
    haveI := ht
    rw [isOpen_iff_mem_nhds]
    intro x hx
    set O' : Set G := (fun a => x + a) ⁻¹' O with hO'
    have h0 : (0 : G) ∈ O' := by
      show x + 0 ∈ O
      rwa [add_zero]
    have hop' : ∀ z ∈ O', ∀ k : ℕ, ∃ S : Set G, (∀ j, S ∈ u j) ∧
        ∀ T : Finset ℕ, T.card ≤ k → ∀ a : ℕ → G, (∀ i ∈ T, a i ∈ S ∨ -a i ∈ S) → z + ∑ i ∈ T, a i ∈ O' := by
      intro z hz k
      obtain ⟨S, hS, h⟩ := hopT O hO (x + z) hz k
      refine ⟨S, hS, fun T hT a ha => ?_⟩
      show x + (z + ∑ i ∈ T, a i) ∈ O
      rw [← add_assoc]
      exact h T hT a ha
    obtain ⟨A, hA, hAO⟩ := Families.exists_Uset_subset_common e u (fun j => (hu j).1) hP
      (no_injection_of_groupwise hg) O' h0 hop'
    have h1 : O' ∈ 𝓝 (0 : G) := by
      rw [hnhds]; exact (hmemN O').2 ⟨A, hA, hAO⟩
    have h2 := (Homeomorph.addLeft x).map_nhds_eq (0 : G)
    have h3 : Filter.map (fun a => x + a) (𝓝 (0 : G)) = 𝓝 x := by simpa using h2
    rw [← h3]
    exact h1
  have htu : ∀ F ∈ genFam (Sel.ultraGen (range u)), F ≤ @nhds G t 0 := by
    have h1 : Sel.ultraGen (range u) ⊆ @nullTop G t _ := by
      rintro F ⟨v, ⟨j, rfl⟩, rfl⟩
      refine ⟨(u j).neBot, ?_⟩
      rw [hnhds]; exact le_trans (huK j) hΦN
    have h2 : genFam (Sel.ultraGen (range u)) ⊆ @nullTop G t _ := by
      letI := t
      haveI := ht
      exact genFam_le nullTop_nullFamily h1
    exact fun F hF => (h2 hF).2
  refine ⟨t, ht, hopen, fun S => ?_, ⟨⟨ht, htu⟩, fun t' ht' => ?_⟩⟩
  · rw [hnhds]; exact hmemN S
  · obtain ⟨ht'g, ht'F⟩ := ht'
    refine @Continuous.mk G G t t' id (fun O hO => ?_)
    refine (hopen O).2 (hcoarse C t' ht'g (fun F hF => ?_) O hO)
    have hΦ' : Φ ≤ @nhds G t' 0 := by
      refine iSup_le (fun j => ?_)
      exact ht'F _ (subset_genFam (hgenne (range u)) ⟨u j, mem_range_self j, rfl⟩)
    have h1 : Sel.ultraGen K ⊆ @nullTop G t' _ := by
      rintro F' ⟨v, hv, rfl⟩
      exact ⟨v.neBot, le_trans hv hΦ'⟩
    have h2 : C ⊆ @nullTop G t' _ := by
      letI := t'
      haveI := ht'g
      exact genFam_le nullTop_nullFamily h1
    exact (h2 hF).2

end Modification

section Copies

variable {J : Type*} [Nonempty J] (y : ℕ → ℤ)

/-- Copies of one ultrafilter placed on the graphs of functions cofinal in its ultrapower. -/
theorem exists_open_not_nhds_of_copies (v : Ultrafilter ℕ) (hv : ∀ a, v ≠ pure a) (g : J → ℕ → ℕ)
    (hcof : ∀ h : ℕ → ℕ, ∃ j, {n | h n < g j n} ∈ v) (hpos : ∀ i, 0 < y i)
    (hgrow : ∀ B : ℕ, ∃ L : ℕ, ∀ l, L < l → 2 * (B : ℤ) * ∑ i ∈ Finset.range l, y i < y l) :
    ∃ O : Set ℤ, (0 : ℤ) ∈ O ∧
      IsOpenMod (genFam (Sel.ultraGen
        (range fun j => ((v.map (fun n => Nat.pair n (g j n))).map y)))) O ∧
      ∀ t : TopologicalSpace ℤ, @IsTopologicalAddGroup ℤ t _ →
        (∀ j, (((v.map (fun n => Nat.pair n (g j n))).map y) : Filter ℤ) ≤ @nhds ℤ t 0) →
          O ∉ @nhds ℤ t 0 := by
  classical
  have hinj : ∀ j, Function.Injective (fun n => Nat.pair n (g j n)) := fun j a b hab =>
    (Nat.pair_eq_pair.1 hab).1
  refine Families.exists_open_not_nhds y (fun j => v.map (fun n => Nat.pair n (g j n))) ?_
    (fun x => (Nat.unpair x).1) ?_ ?_ hpos hgrow
  · intro j a h
    have h1 : ({a} : Set ℕ) ∈ v.map (fun n => Nat.pair n (g j n)) := by
      rw [h]; exact Ultrafilter.mem_pure.2 rfl
    rw [Ultrafilter.mem_map] at h1
    exact Sel.notMem_of_finite hv ((finite_singleton a).preimage (hinj j).injOn) h1
  · intro j m h
    rw [Ultrafilter.mem_map] at h
    refine Sel.notMem_of_finite hv ((finite_singleton m).subset (fun n hn => ?_)) h
    have h2 : (Nat.unpair (Nat.pair n (g j n))).1 = m := hn
    rw [Nat.unpair_pair] at h2
    exact mem_singleton_iff.2 h2
  · intro C hC
    by_contra hno
    have hfin : ∀ m, {x : ℕ | x ∈ C ∧ (Nat.unpair x).1 = m}.Finite := fun m => by
      by_contra h
      exact hno ⟨m, h⟩
    let h : ℕ → ℕ := fun m => (hfin m).toFinset.sup (fun x => (Nat.unpair x).2)
    obtain ⟨j, hj⟩ := hcof h
    have h1 := hC j
    rw [Ultrafilter.mem_map] at h1
    obtain ⟨n, hn1, hn2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (v : Filter ℕ)) hj h1)
    have h2 : h n < g j n := hn1
    have h3 : Nat.pair n (g j n) ∈ (hfin n).toFinset := by
      refine (hfin n).mem_toFinset.2 ⟨hn2, ?_⟩
      rw [Nat.unpair_pair]
    have h4 : (Nat.unpair (Nat.pair n (g j n))).2 ≤ h n :=
      Finset.le_sup (f := fun x => (Nat.unpair x).2) h3
    rw [Nat.unpair_pair] at h4
    have h5 : g j n ≤ h n := h4
    omega

end Copies

end Groupwise

end PG
