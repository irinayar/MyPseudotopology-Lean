import Mathlib
import LeanCheck.PGThreeSelective
import LeanCheck.PGThreeSparse
import LeanCheck.PGTwoReflection

/-!
# PGthree: coreflections and idempotent ultrafilters (Lean check)

Scope. Section 9 of the third article (`PGthree.tex`).

* `nbhd_iff_of_no_idempotent` : in any PG on an abelian group in which no nonprincipal ultrafilter converging to `0`
  is idempotent, the neighbourhood filters of group topologies among the null filters are exactly the principal filters
  of the finite subgroups all of whose points converge to `0`;
* `trivial_of_no_idempotent` : with unique limits the only one is `pure 0`, and if some nonprincipal ultrafilter
  converges to `0`, the vicinity filter is not null;
* `independent_no_idempotent` : if all ultrafilters of `S` are nonprincipal and contain an independent set `E`, the PG
  they generate has unique limits and no nonprincipal null idempotent;
* `sparse_no_idempotent` : the same when `E` is the set of terms of a rapidly growing sequence of positive integers.

No set-theoretic hypothesis is used. A Lean proof verifies its formal statement under its hypotheses; the
correspondence with the article requires mathematical review.
-/

open Filter Set Topology

namespace PG

namespace Idem

open Sel

attribute [local instance] Ultrafilter.add Ultrafilter.addSemigroup

variable {G : Type*} [AddCommGroup G]

theorem mem_add (U V : Ultrafilter G) (A : Set G) : A ∈ U + V ↔ {m | {z | m + z ∈ A} ∈ V} ∈ U :=
  Ultrafilter.eventually_add U V (fun m => m ∈ A)

/-- The sum with a nonprincipal ultrafilter on the right is nonprincipal. -/
theorem free_add (p q : Ultrafilter G) (hq : ∀ a, q ≠ pure a) : ∀ a, p + q ≠ pure a := by
  intro a ha
  have h1 : ({a} : Set G) ∈ p + q := by rw [ha]; exact rfl
  rw [mem_add] at h1
  obtain ⟨m, hm⟩ := Ultrafilter.nonempty_of_mem h1
  have h2 : ({a - m} : Set G) ∈ q := by
    have h3 : {z : G | m + z ∈ ({a} : Set G)} ∈ q := hm
    refine Filter.mem_of_superset h3 (fun z hz => ?_)
    have h4 : m + z = a := hz
    rw [mem_singleton_iff, ← h4]; abel
  obtain ⟨b, _, h5⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h2
  exact hq b h5

/-- The criterion. -/
theorem nbhd_iff_of_no_idempotent {G : Type} [AddCommGroup G] {C : Set (Filter G)} (hC : NullFamily C)
    (hidem : ∀ p : Ultrafilter G, (p : Filter G) ∈ C → (∀ a, p ≠ pure a) → p + p ≠ p) (N : Filter G) :
    (IsNbhdFilter N ∧ N ∈ C) ↔
      ∃ F : AddSubgroup G, (F : Set G).Finite ∧ (∀ g ∈ F, (pure g : Filter G) ∈ C) ∧ N = 𝓟 (F : Set G) := by
  classical
  constructor
  · rintro ⟨hN, hNC⟩
    set X : Set (Ultrafilter G) := {U | (U : Filter G) ≤ N ∧ ∀ a, U ≠ pure a} with hX
    have hXe : X = ∅ := by
      by_contra hne
      have hXne : X.Nonempty := Set.nonempty_iff_ne_empty.2 hne
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
      have hXadd : ∀ V ∈ X, ∀ V' ∈ X, V + V' ∈ X := by
        intro V hV V' hV'
        refine ⟨fun s hs => ?_, free_add V V' hV'.2⟩
        obtain ⟨B, hB, hBs⟩ := hN.halve s hs
        show s ∈ V + V'
        rw [mem_add]
        refine Filter.mem_of_superset (hV.1 hB) (fun m hm => ?_)
        exact Filter.mem_of_superset (hV'.1 hB) (fun z hz => hBs m hm z hz)
      obtain ⟨p, hpX, hpp⟩ := exists_idempotent_in_compact_add_subsemigroup
        (M := Ultrafilter G) Ultrafilter.continuous_add_left X hXne hXclosed.isCompact hXadd
      exact hidem p (hC.finer _ hNC _ hpX.1 p.neBot) hpX.2 hpp
    have hprin : ∀ U : Ultrafilter G, (U : Filter G) ≤ N → ∃ a, U = pure a := by
      intro U hU
      by_contra h
      have h1 : U ∈ X := ⟨hU, fun a ha => h ⟨a, ha⟩⟩
      rw [hXe] at h1
      exact h1
    set F0 : Set G := {g | ∀ s ∈ N, g ∈ s} with hF0
    have hfin : F0.Finite := by
      by_contra hinf
      have hne : (𝓟 F0 ⊓ Filter.cofinite).NeBot := by
        have : Set.Infinite F0 := hinf
        rw [inf_comm]
        exact this.cofinite_inf_principal_neBot
      have hV := Ultrafilter.of_le (𝓟 F0 ⊓ Filter.cofinite)
      set V : Ultrafilter G := Ultrafilter.of (𝓟 F0 ⊓ Filter.cofinite) with hVdef
      have hVN : (V : Filter G) ≤ N := by
        intro s hs
        have h1 : F0 ∈ V := hV.trans inf_le_left (mem_principal_self _)
        exact Filter.mem_of_superset h1 (fun g hg => hg s hs)
      obtain ⟨a, ha⟩ := hprin V hVN
      have h2 : ({a}ᶜ : Set G) ∈ V := hV.trans inf_le_right (finite_singleton a).compl_mem_cofinite
      rw [ha] at h2
      exact h2 rfl
    let F : AddSubgroup G :=
      { carrier := F0
        zero_mem' := fun s hs => hN.zero_mem s hs
        add_mem' := fun {a b} ha hb s hs => by
          obtain ⟨B, hB, hBs⟩ := hN.halve s hs
          exact hBs a (ha B hB) b (hb B hB)
        neg_mem' := fun {a} ha s hs => ha _ (hN.neg_mem s hs) }
    have hpure : ∀ g ∈ F0, (pure g : Filter G) ≤ N := fun g hg s hs => hg s hs
    refine ⟨F, hfin, fun g hg => hC.finer _ hNC _ (hpure g hg) inferInstance, ?_⟩
    refine le_antisymm (Filter.le_iff_ultrafilter.2 (fun U hU => ?_)) (fun s hs => ?_)
    · obtain ⟨a, ha⟩ := hprin U hU
      rw [ha, Ultrafilter.coe_pure, Filter.pure_le_principal]
      intro s hs
      have h1 : s ∈ (U : Filter G) := hU hs
      rw [ha] at h1
      exact h1
    · exact Filter.mem_principal.2 (fun g hg => hg s hs)
  · rintro ⟨F, hFfin, hFC, rfl⟩
    refine ⟨⟨fun A hA => hA F.zero_mem, fun A hA => ?_, fun A hA => ?_⟩, ?_⟩
    · exact Filter.mem_principal.2 (fun x hx => hA (F.neg_mem hx))
    · exact ⟨F, mem_principal_self _, fun x hx y hy => hA (F.add_mem hx hy)⟩
    · have hne : (𝓟 (F : Set G)).NeBot := principal_neBot_iff.2 ⟨0, F.zero_mem⟩
      refine hC.ultra _ hne (fun U hU => ?_)
      have h1 : (F : Set G) ∈ U := hU (mem_principal_self _)
      obtain ⟨a, ha, hUa⟩ := Ultrafilter.eq_pure_of_finite_mem hFfin h1
      rw [hUa, Ultrafilter.coe_pure]
      exact hFC a ha

/-- With unique limits: only `pure 0`, and no pretopology when a nonprincipal ultrafilter converges to `0`. -/
theorem trivial_of_no_idempotent {G : Type} [AddCommGroup G] {C : Set (Filter G)} (hC : NullFamily C)
    (hhaus : ∀ g : G, (pure g : Filter G) ∈ C → g = 0)
    (hidem : ∀ p : Ultrafilter G, (p : Filter G) ∈ C → (∀ a, p ≠ pure a) → p + p ≠ p) :
    (∀ N : Filter G, IsNbhdFilter N → N ∈ C → N = pure 0) ∧
      ((∃ p : Ultrafilter G, (p : Filter G) ∈ C ∧ ∀ a, p ≠ pure a) → vic C ∉ C) := by
  have main : ∀ N : Filter G, IsNbhdFilter N → N ∈ C → N = pure 0 := by
    intro N hN hNC
    obtain ⟨F, _, hFC, rfl⟩ := (nbhd_iff_of_no_idempotent hC hidem N).1 ⟨hN, hNC⟩
    have h1 : (F : Set G) = {0} := by
      refine Set.Subset.antisymm (fun g hg => hhaus g (hFC g hg)) ?_
      exact singleton_subset_iff.2 F.zero_mem
    rw [h1, principal_singleton]
  refine ⟨main, ?_⟩
  rintro ⟨p, hpC, hpfree⟩ hvic
  have hV : IsNbhdFilter (vic C) := by
    refine ⟨fun A hA => vic_zero_mem hC hA, fun A hA => vic_neg hC hA, fun A hA => ?_⟩
    have h1 : Filter.map₂ (· + ·) (vic C) (vic C) ≤ vic C := le_vic (hC.add _ hvic _ hvic)
    obtain ⟨B1, hB1, B2, hB2, h2⟩ := Filter.mem_map₂_iff.1 (h1 hA)
    exact ⟨B1 ∩ B2, Filter.inter_mem hB1 hB2, fun x hx y hy => h2 (mem_image2_of_mem hx.1 hy.2)⟩
  have h0 := main _ hV hvic
  have h1 : (p : Filter G) ≤ pure 0 := h0 ▸ le_vic hpC
  have h2 : ({0} : Set G) ∈ p := h1 (Filter.mem_pure.2 rfl)
  obtain ⟨b, _, h3⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h2
  exact hpfree b h3

/-! ### Independent sets -/

/-- The sum with integer coefficients over `E`. -/
noncomputable def ev (E : Set G) (c : E →₀ ℤ) : G := c.sum (fun x a => a • (x : G))

theorem ev_add (E : Set G) (c d : E →₀ ℤ) : ev E (c + d) = ev E c + ev E d := by
  unfold ev
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

theorem ev_single (E : Set G) (x : E) (a : ℤ) : ev E (Finsupp.single x a) = a • (x : G) := by
  unfold ev
  exact Finsupp.sum_single_index (zero_smul _ _)

theorem ev_zero (E : Set G) : ev E 0 = 0 := by simp [ev]

theorem ev_finset_sum (E : Set G) {ι : Type*} (s : Finset ι) (c : ι → E →₀ ℤ) :
    ev E (∑ i ∈ s, c i) = ∑ i ∈ s, ev E (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ev_add, ih]

theorem ev_sub (E : Set G) (c d : E →₀ ℤ) : ev E (c - d) = ev E c - ev E d := by
  have h := ev_add E (c - d) d
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

/-- `E` is independent: a vanishing combination vanishes term by term. -/
def Indep (E : Set G) : Prop := ∀ c : E →₀ ℤ, ev E c = 0 → ∀ x : E, c x • (x : G) = 0

/-- A representation of a signed sum of elements of `E` with small coefficients. -/
theorem sum_rep (E : Set G) {ι : Type} [Fintype ι] (ε : ι → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (a : ι → G)
    (ha : ∀ i, a i ∈ E) :
    ∃ c : E →₀ ℤ, ev E c = ∑ i, ε i • a i ∧ (∑ x ∈ c.support, |c x|) ≤ (Fintype.card ι : ℤ) ∧
      ∀ x ∈ c.support, ∃ i, (x : G) = a i := by
  classical
  set c : E →₀ ℤ := ∑ i, Finsupp.single (⟨a i, ha i⟩ : E) (ε i) with hc
  have hsupp : ∀ x ∈ c.support, ∃ i, (x : G) = a i := by
    intro x hx
    by_contra h
    apply Finsupp.mem_support_iff.1 hx
    rw [hc, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    exact Finsupp.single_eq_of_ne (fun hxi => h ⟨i, by rw [hxi]⟩)
  refine ⟨c, ?_, ?_, hsupp⟩
  · rw [hc, ev_finset_sum]
    exact Finset.sum_congr rfl (fun i _ => ev_single E _ _)
  · have h1 : ∀ x ∈ c.support, |c x| ≤ ∑ i, |Finsupp.single (⟨a i, ha i⟩ : E) (ε i) x| := by
      intro x _
      rw [hc, Finsupp.finsetSum_apply]
      exact Finset.abs_sum_le_sum_abs _ _
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_comm]
    have h2 : ∀ i ∈ Finset.univ, ∑ x ∈ c.support, |Finsupp.single (⟨a i, ha i⟩ : E) (ε i) x| ≤ 1 := by
      intro i _
      have h3 : ∀ x, |Finsupp.single (⟨a i, ha i⟩ : E) (ε i) x| = if (⟨a i, ha i⟩ : E) = x then 1 else 0 := by
        intro x
        rw [Finsupp.single_apply]
        split_ifs
        · rcases hε i with h | h <;> rw [h] <;> simp
        · simp
      simp only [h3]
      rw [Finset.sum_ite_eq]
      split_ifs <;> simp
    refine (Finset.sum_le_sum h2).trans ?_
    simp

theorem independent_no_idempotent {G : Type} [AddCommGroup G] (E : Set G) (hE : Indep E)
    (S : Set (Ultrafilter G)) (hfree : ∀ u ∈ S, ∀ a, u ≠ pure a) (hES : ∀ u ∈ S, E ∈ u) :
    (∀ g : G, (pure g : Filter G) ∈ genFam (ultraGen S) → g = 0) ∧
      ∀ p : Ultrafilter G, (p : Filter G) ∈ genFam (ultraGen S) → (∀ a, p ≠ pure a) → p + p ≠ p := by
  classical
  -- every null ultrafilter is finer than a signed sum, hence contains the small sums
  have hrep : ∀ p : Ultrafilter G, (p : Filter G) ∈ genFam (ultraGen S) →
      ∃ (ι : Type) (_ : Fintype ι) (ε : ι → ℤ), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ A : Set G, (∀ u ∈ S, A ∈ u) → {z | ∃ a : ι → G, (∀ i, a i ∈ A) ∧ ∑ i, ε i • a i = z} ∈ p := by
    intro p hp
    obtain ⟨σ, hσ, hpσ⟩ := hp.2 p le_rfl
    obtain ⟨ι, hι, u, ε, hu, hε, h⟩ := rep_of_sumClosure S hσ
    exact ⟨ι, hι, ε, hε, fun A hA => hpσ (h (fun _ => A) (fun i => hA _ (hu i)))⟩
  have hdiff : ∀ F : Finset G, ∀ u ∈ S, E \ (F : Set G) ∈ u := by
    intro F u hu
    have h1 : (F : Set G)ᶜ ∈ u := by
      rcases u.mem_or_compl_mem (F : Set G) with h | h
      · exact absurd h (notMem_of_finite (hfree u hu) F.finite_toSet)
      · exact h
    exact Filter.inter_mem (hES u hu) h1
  refine ⟨fun g hg => ?_, fun p hp hpfree hpp => ?_⟩
  · obtain ⟨ι, _, ε, hε, h⟩ := hrep (pure g) (by rwa [Ultrafilter.coe_pure])
    have h1 : g ∈ {z | ∃ a : ι → G, (∀ i, a i ∈ E) ∧ ∑ i, ε i • a i = z} := h E hES
    obtain ⟨a, ha, hsum⟩ := h1
    obtain ⟨c, hc, _, _⟩ := sum_rep E ε hε a ha
    set F : Finset G := c.support.image (fun x : E => (x : G)) with hF
    have h2 : g ∈ {z | ∃ a : ι → G, (∀ i, a i ∈ E \ (F : Set G)) ∧ ∑ i, ε i • a i = z} := h _ (hdiff F)
    obtain ⟨b, hb, hsum'⟩ := h2
    obtain ⟨d, hd, _, hdsupp⟩ := sum_rep E ε hε b (fun i => (hb i).1)
    have h3 : ev E (c - d) = 0 := by rw [ev_sub, hc, hd, hsum, hsum', sub_self]
    have h4 : ∀ x ∈ c.support, c x • (x : G) = 0 := by
      intro x hx
      have h5 := hE _ h3 x
      have h6 : d x = 0 := by
        by_contra h7
        obtain ⟨i, hi⟩ := hdsupp x (Finsupp.mem_support_iff.2 h7)
        exact (hb i).2 (by rw [← hi]; exact Finset.mem_image_of_mem _ hx)
      rwa [Finsupp.sub_apply, h6, sub_zero] at h5
    rw [← hsum, ← hc]
    exact Finset.sum_eq_zero h4
  · obtain ⟨ι, _, ε, hε, h⟩ := hrep p hp
    set n : ℕ := Fintype.card ι with hn
    set B : Set G := {z | ∃ c : E →₀ ℤ, ev E c = z ∧ (∑ x ∈ c.support, |c x|) ≤ (n : ℤ)} with hB
    have hBp : B ∈ p := by
      refine Filter.mem_of_superset (h E hES) (fun z hz => ?_)
      obtain ⟨a, ha, hsum⟩ := hz
      obtain ⟨c, hc, hcn, _⟩ := sum_rep E ε hε a ha
      exact ⟨c, by rw [hc, hsum], hcn⟩
    have hr : ∀ z : G, ∃ c : E →₀ ℤ, z ∈ B → ev E c = z ∧ (∑ x ∈ c.support, |c x|) ≤ (n : ℤ) := by
      intro z
      by_cases hz : z ∈ B
      · obtain ⟨c, hc⟩ := hz
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => absurd h hz⟩
    choose r hr using hr
    have hbound : ∀ z ∈ B, ∀ x : E, |r z x| ≤ (n : ℤ) := by
      intro z hz x
      by_cases hx : x ∈ (r z).support
      · exact (Finset.single_le_sum (f := fun x => |r z x|) (fun _ _ => abs_nonneg _) hx).trans (hr z hz).2
      · rw [Finsupp.notMem_support_iff.1 hx]; simp
    -- components are well defined and additive
    have hcomp : ∀ (c d : E →₀ ℤ), ev E c = ev E d → ∀ x : E, c x • (x : G) = d x • (x : G) := by
      intro c d hcd x
      have h1 := hE (c - d) (by rw [ev_sub, hcd, sub_self]) x
      rwa [Finsupp.sub_apply, sub_smul, sub_eq_zero] at h1
    -- the sum of two small sums
    have hadd : ∀ x ∈ B, ∀ z ∈ B, x + z ∈ B → ∀ e : E,
        r (x + z) e • (e : G) = r x e • (e : G) + r z e • (e : G) := by
      intro x hx z hz hxz e
      have h1 := hcomp (r (x + z)) (r x + r z) (by
        rw [ev_add, (hr x hx).1, (hr z hz).1, (hr _ hxz).1]) e
      rwa [Finsupp.add_apply, add_smul] at h1
    -- membership in `p` implies membership in `p + p`
    have htwice : ∀ A ∈ p, ∀ᶠ x in (p : Filter G), ∀ᶠ z in (p : Filter G), x + z ∈ A := by
      intro A hA
      have h1 : A ∈ p + p := by rw [hpp]; exact hA
      rw [mem_add] at h1
      exact h1
    -- every component is `0` almost everywhere
    have hzero : ∀ e : E, {z | z ∈ B ∧ r z e • (e : G) = 0} ∈ p := by
      intro e
      have h1 : ∃ k ∈ Finset.Icc (-(n : ℤ)) n, {z | z ∈ B ∧ r z e • (e : G) = k • (e : G)} ∈ p := by
        by_contra hc
        have h2 : (⋂ k ∈ Finset.Icc (-(n : ℤ)) n, {z | z ∈ B ∧ r z e • (e : G) = k • (e : G)}ᶜ) ∈ (p : Filter G) := by
          refine (Filter.biInter_finset_mem _).2 (fun k hk => ?_)
          rcases p.mem_or_compl_mem {z | z ∈ B ∧ r z e • (e : G) = k • (e : G)} with h3 | h3
          · exact absurd ⟨k, hk, h3⟩ hc
          · exact h3
        obtain ⟨z, hz1, hz2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (p : Filter G)) h2 hBp)
        exact mem_iInter₂.1 hz1 (r z e) (Finset.mem_Icc.2 (abs_le.1 (hbound z hz2 e))) ⟨hz2, rfl⟩
      obtain ⟨k, _, hk⟩ := h1
      have h2 := htwice _ hk
      obtain ⟨x, hx1, hx2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (p : Filter G)) h2 hk)
      obtain ⟨z, ⟨hz1, hz2⟩⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (p : Filter G)) hx1 hk)
      have hz1' : x + z ∈ B ∧ r (x + z) e • (e : G) = k • (e : G) := hz1
      have h3 := hadd x hx2.1 z hz2.1 hz1'.1 e
      rw [hz1'.2, hx2.2, hz2.2] at h3
      have h4 : k • (e : G) = 0 := by
        have h5 : k • (e : G) + 0 = k • (e : G) + k • (e : G) := by rw [add_zero]; exact h3
        exact (add_left_cancel h5).symm
      rw [h4] at hk
      exact hk
    -- the number of nonzero components
    let supp : G → Finset E := fun z => (r z).support.filter (fun e => r z e • (e : G) ≠ 0)
    have hsupp : ∀ z (e : E), e ∈ supp z ↔ r z e • (e : G) ≠ 0 := by
      intro z e
      show e ∈ (r z).support.filter (fun e => r z e • (e : G) ≠ 0) ↔ _
      rw [Finset.mem_filter]
      refine ⟨fun h => h.2, fun h => ⟨Finsupp.mem_support_iff.2 (fun h0 => h ?_), h⟩⟩
      rw [h0, zero_smul]
    have hcard : ∀ z ∈ B, (supp z).card ≤ n := by
      intro z hz
      have h1 : ((supp z).card : ℤ) ≤ ∑ x ∈ (r z).support, |r z x| := by
        have h2 : ((supp z).card : ℤ) = ∑ _x ∈ supp z, (1 : ℤ) := by simp
        rw [h2]
        refine (Finset.sum_le_sum (fun x hx => ?_)).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _))
        exact Int.one_le_abs (Finsupp.mem_support_iff.1 (Finset.mem_filter.1 hx).1)
      exact_mod_cast h1.trans (hr z hz).2
    have hk : ∃ k ≤ n, {z | z ∈ B ∧ (supp z).card = k} ∈ p := by
      by_contra hc
      have h2 : (⋂ k ∈ Finset.range (n + 1), {z | z ∈ B ∧ (supp z).card = k}ᶜ) ∈ (p : Filter G) := by
        refine (Filter.biInter_finset_mem _).2 (fun k hk => ?_)
        rcases p.mem_or_compl_mem {z | z ∈ B ∧ (supp z).card = k} with h3 | h3
        · exact absurd ⟨k, Nat.le_of_lt_succ (Finset.mem_range.1 hk), h3⟩ hc
        · exact h3
      obtain ⟨z, hz1, hz2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (p : Filter G)) h2 hBp)
      exact mem_iInter₂.1 hz1 _ (Finset.mem_range.2 (Nat.lt_succ_of_le (hcard z hz2))) ⟨hz2, rfl⟩
    obtain ⟨k, _, hkp⟩ := hk
    have h2 := htwice _ hkp
    obtain ⟨x, hx1, hx2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (p : Filter G)) h2 hkp)
    have hfresh : (⋂ e ∈ supp x, {z | z ∈ B ∧ r z e • (e : G) = 0}) ∈ (p : Filter G) :=
      (Filter.biInter_finset_mem _).2 (fun e _ => hzero e)
    obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := Ultrafilter.nonempty_of_mem
      (Filter.inter_mem (f := (p : Filter G)) (Filter.inter_mem (f := (p : Filter G)) hx1 hkp) hfresh)
    have hz1' : x + z ∈ B ∧ (supp (x + z)).card = k := hz1
    have hzx : ∀ e ∈ supp x, r z e • (e : G) = 0 := fun e he => (mem_iInter₂.1 hz3 e he).2
    have hdisj : Disjoint (supp x) (supp z) := by
      rw [Finset.disjoint_left]
      intro e hex hez
      exact (hsupp z e).1 hez (hzx e hex)
    have hunion : supp (x + z) = supp x ∪ supp z := by
      ext e
      rw [Finset.mem_union, hsupp, hsupp, hsupp, hadd x hx2.1 z hz2.1 hz1'.1 e]
      by_cases hex : r x e • (e : G) = 0
      · rw [hex, zero_add]
        exact ⟨Or.inr, fun h => h.resolve_left (fun h' => h' rfl)⟩
      · rw [hzx e ((hsupp x e).2 hex), add_zero]
        exact ⟨Or.inl, fun _ => hex⟩
    have h3 : k = k + k := by
      have h4 := congrArg Finset.card hunion
      rw [Finset.card_union_of_disjoint hdisj, hz1'.2, hx2.2, hz2.2] at h4
      exact h4
    have hk0 : k = 0 := by omega
    -- so `p` is the principal ultrafilter at `0`
    have h5 : ({0} : Set G) ∈ p := by
      refine Filter.mem_of_superset hkp (fun w hw => ?_)
      obtain ⟨hwB, hwk⟩ := hw
      rw [hk0, Finset.card_eq_zero] at hwk
      show w = 0
      rw [← (hr w hwB).1]
      refine Finset.sum_eq_zero (fun e _ => ?_)
      by_contra h6
      have h7 : e ∈ supp w := (hsupp w e).2 h6
      rw [hwk] at h7
      simp at h7
    obtain ⟨b, _, h6⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h5
    exact hpfree b h6

/-! ### Rapidly growing sequences -/

section Sparse

variable (y : ℕ → ℤ) (hpos : ∀ i, 0 < y i)
  (hgrow : ∀ B : ℕ, ∃ L : ℕ, ∀ l, L < l → 2 * (B : ℤ) * ∑ i ∈ Finset.range l, y i < y l)

include hpos hgrow in
/-- A nonzero combination with bounded coefficients supported far out has a large value. -/
theorem far_zero (n : ℕ) (g : ℤ) : ∃ L : ℕ, ∀ e : ℕ →₀ ℤ, (∀ i, |e i| ≤ (n : ℤ)) → (∀ i ∈ e.support, L < i) →
    Sparse.val y e = g → e = 0 := by
  classical
  obtain ⟨L0, hL0⟩ := hgrow (n + 1)
  refine ⟨max L0 (g.natAbs + 1), fun e he hsupp hval => ?_⟩
  by_contra hne
  have hs : e.support.Nonempty := Finsupp.support_nonempty_iff.2 hne
  set l := e.support.max' hs with hl
  have hlmem : l ∈ e.support := e.support.max'_mem hs
  have hLl := hsupp l hlmem
  have h1 := hL0 l (lt_of_le_of_lt (le_max_left _ _) hLl)
  have hsum : Sparse.val y e = e l * y l + ∑ i ∈ Finset.range l, e i * y i := by
    have h2 : Sparse.val y e = ∑ i ∈ Finset.range (l + 1), e i * y i := by
      unfold Sparse.val Finsupp.sum
      refine Finset.sum_subset (fun i hi => Finset.mem_range.2 (Nat.lt_succ_of_le (e.support.le_max' i hi)))
        (fun i _ hi => ?_)
      rw [Finsupp.notMem_support_iff.1 hi]
      exact zero_mul _
    rw [h2, Finset.sum_range_succ, add_comm]
  set T : ℤ := ∑ i ∈ Finset.range l, y i with hT
  have h3 : |∑ i ∈ Finset.range l, e i * y i| ≤ (n : ℤ) * T := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [abs_mul, abs_of_pos (hpos i)]
    exact mul_le_mul_of_nonneg_right (he i) (hpos i).le
  have h4 : y l ≤ |e l * y l| := by
    rw [abs_mul, abs_of_pos (hpos l)]
    have : 1 ≤ |e l| := Int.one_le_abs (Finsupp.mem_support_iff.1 hlmem)
    calc y l = 1 * y l := (one_mul _).symm
      _ ≤ |e l| * y l := mul_le_mul_of_nonneg_right this (hpos l).le
  have h5 : |e l * y l| ≤ |g| + |∑ i ∈ Finset.range l, e i * y i| := by
    have h6 : e l * y l = g - ∑ i ∈ Finset.range l, e i * y i := by rw [← hval, hsum]; ring
    rw [h6]
    exact abs_sub _ _
  have hlT : (l : ℤ) ≤ T := by
    have h7 : ∑ _i ∈ Finset.range l, (1 : ℤ) ≤ T := Finset.sum_le_sum (fun i _ => hpos i)
    simpa using h7
  have hT0 : 0 ≤ T := le_trans (Int.natCast_nonneg l) hlT
  have h8 : 2 * ((n : ℤ) + 1) * T < y l := by exact_mod_cast h1
  have h9 : (g.natAbs : ℤ) + 1 < (l : ℤ) := by
    have : g.natAbs + 1 < l := lt_of_le_of_lt (le_max_right _ _) hLl
    exact_mod_cast this
  have h10 : |g| = (g.natAbs : ℤ) := (Int.natCast_natAbs g).symm
  have h11 : 0 ≤ (n : ℤ) * T := mul_nonneg (Int.natCast_nonneg n) hT0
  have h12 : 2 * ((n : ℤ) + 1) * T = (n : ℤ) * T + (n : ℤ) * T + (T + T) := by ring
  omega

include hpos hgrow in
theorem sparse_no_idempotent (T : Set (Ultrafilter ℕ)) (hfree : ∀ w ∈ T, ∀ a, w ≠ pure a) :
    (∀ g : ℤ, (pure g : Filter ℤ) ∈ genFam (ultraGen ((fun w => w.map y) '' T)) → g = 0) ∧
      ∀ p : Ultrafilter ℤ, (p : Filter ℤ) ∈ genFam (ultraGen ((fun w => w.map y) '' T)) →
        (∀ a, p ≠ pure a) → p + p ≠ p := by
  classical
  set S : Set (Ultrafilter ℤ) := (fun w => w.map y) '' T with hS
  have hrep : ∀ p : Ultrafilter ℤ, (p : Filter ℤ) ∈ genFam (ultraGen S) → ∃ n : ℕ, ∀ M : ℕ,
      {z | ∃ d : ℕ →₀ ℤ, Sparse.val y d = z ∧ (∑ i ∈ d.support, |d i|) ≤ (n : ℤ) ∧ ∀ i ∈ d.support, M < i} ∈ p := by
    intro p hp
    obtain ⟨σ, hσ, hpσ⟩ := hp.2 p le_rfl
    obtain ⟨ι, _, u, ε, hu, hε, h⟩ := rep_of_sumClosure S hσ
    refine ⟨Fintype.card ι, fun M => ?_⟩
    have hA : ∀ i, y '' Ioi M ∈ u i := by
      intro i
      obtain ⟨w, hw, hwu⟩ := hu i
      rw [← hwu]
      show y ⁻¹' (y '' Ioi M) ∈ w
      refine Filter.mem_of_superset ?_ (subset_preimage_image y (Ioi M))
      rcases w.mem_or_compl_mem (Ioi M) with h' | h'
      · exact h'
      · refine absurd h' (notMem_of_finite (hfree w hw) ((finite_Iic M).subset (fun x hx => ?_)))
        have : ¬ M < x := hx
        exact mem_Iic.2 (not_lt.1 this)
    refine hpσ (Filter.mem_of_superset (h (fun _ => y '' Ioi M) hA) (fun z hz => ?_))
    obtain ⟨a, ha, hsum⟩ := hz
    choose m hm hma using ha
    have hE : ∀ i, m i ∈ (univ : Set ℕ) := fun _ => mem_univ _
    set d : ℕ →₀ ℤ := ∑ i, Finsupp.single (m i) (ε i) with hd
    have hsupp : ∀ l ∈ d.support, M < l := by
      intro l hl
      by_contra hlM
      apply Finsupp.mem_support_iff.1 hl
      rw [hd, Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      exact Finsupp.single_eq_of_ne (fun hli => hlM (hli ▸ hm i))
    refine ⟨d, ?_, ?_, hsupp⟩
    · rw [hd, Sparse.val_finset_sum, ← hsum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      unfold Sparse.val
      rw [Finsupp.sum_single_index (zero_mul _), ← hma i, smul_eq_mul]
    · have h1 : ∀ l ∈ d.support, |d l| ≤ ∑ i, |Finsupp.single (m i) (ε i) l| := by
        intro l _
        rw [hd, Finsupp.finsetSum_apply]
        exact Finset.abs_sum_le_sum_abs _ _
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_comm]
      have h2 : ∀ i ∈ Finset.univ, ∑ l ∈ d.support, |Finsupp.single (m i) (ε i) l| ≤ 1 := by
        intro i _
        have h3 : ∀ l, |Finsupp.single (m i) (ε i) l| = if m i = l then 1 else 0 := by
          intro l
          rw [Finsupp.single_apply]
          split_ifs
          · rcases hε i with h | h <;> rw [h] <;> simp
          · simp
        simp only [h3]
        rw [Finset.sum_ite_eq]
        split_ifs <;> simp
      refine (Finset.sum_le_sum h2).trans ?_
      simp
  have hcoef : ∀ (n : ℕ) (d : ℕ →₀ ℤ), (∑ i ∈ d.support, |d i|) ≤ (n : ℤ) → ∀ i, |d i| ≤ (n : ℤ) := by
    intro n d hd i
    by_cases hi : i ∈ d.support
    · exact (Finset.single_le_sum (f := fun i => |d i|) (fun _ _ => abs_nonneg _) hi).trans hd
    · rw [Finsupp.notMem_support_iff.1 hi]; simp
  refine ⟨fun g hg => ?_, fun p hp hpfree hpp => ?_⟩
  · obtain ⟨n, h⟩ := hrep (pure g) (by rwa [Ultrafilter.coe_pure])
    obtain ⟨L, hL⟩ := far_zero y hpos hgrow n g
    have h1 : g ∈ {z | ∃ d : ℕ →₀ ℤ, Sparse.val y d = z ∧ (∑ i ∈ d.support, |d i|) ≤ (n : ℤ)
        ∧ ∀ i ∈ d.support, L < i} := h L
    obtain ⟨d, hd, hdn, hdL⟩ := h1
    have h2 := hL d (hcoef n d hdn) hdL hd
    rw [← hd, h2, Sparse.val_zero]
  · obtain ⟨n, h⟩ := hrep p hp
    set B : Set ℤ := {z | ∃ d : ℕ →₀ ℤ, Sparse.val y d = z ∧ (∑ i ∈ d.support, |d i|) ≤ (n : ℤ)} with hB
    have hBp : B ∈ p := Filter.mem_of_superset (h 0) (fun z hz => by
      obtain ⟨d, hd, hdn, _⟩ := hz
      exact ⟨d, hd, hdn⟩)
    have hr : ∀ z : ℤ, ∃ c : ℕ →₀ ℤ, z ∈ B → Sparse.val y c = z ∧ (∑ i ∈ c.support, |c i|) ≤ (n : ℤ) := by
      intro z
      by_cases hz : z ∈ B
      · obtain ⟨c, hc⟩ := hz
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => absurd h hz⟩
    choose r hr using hr
    -- every coefficient is almost everywhere constant
    have hconst : ∀ i : ℕ, ∃ k : ℤ, {z | z ∈ B ∧ r z i = k} ∈ p := by
      intro i
      by_contra hc
      have h2 : (⋂ k ∈ Finset.Icc (-(n : ℤ)) n, {z | z ∈ B ∧ r z i = k}ᶜ) ∈ (p : Filter ℤ) := by
        refine (Filter.biInter_finset_mem _).2 (fun k _ => ?_)
        rcases p.mem_or_compl_mem {z | z ∈ B ∧ r z i = k} with h3 | h3
        · exact absurd ⟨k, h3⟩ hc
        · exact h3
      obtain ⟨z, hz1, hz2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (p : Filter ℤ)) h2 hBp)
      exact mem_iInter₂.1 hz1 (r z i) (Finset.mem_Icc.2 (abs_le.1 (hcoef n _ (hr z hz2).2 i))) ⟨hz2, rfl⟩
    choose hh hhp using hconst
    -- only finitely many of the constants are nonzero
    have hfin : {i | hh i ≠ 0}.Finite := by
      by_contra hinf
      obtain ⟨I, hI, hIc⟩ := Set.Infinite.exists_subset_card_eq hinf (n + 1)
      have h1 : (⋂ i ∈ I, {z | z ∈ B ∧ r z i = hh i}) ∈ (p : Filter ℤ) :=
        (Filter.biInter_finset_mem _).2 (fun i _ => hhp i)
      obtain ⟨z, hz1, hz2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (p : Filter ℤ)) h1 hBp)
      have h2 : I ⊆ (r z).support := by
        intro i hi
        refine Finsupp.mem_support_iff.2 ?_
        rw [(mem_iInter₂.1 hz1 i hi).2]
        exact hI hi
      have h3 : ((I.card : ℕ) : ℤ) ≤ ∑ i ∈ (r z).support, |r z i| := by
        have h4 : ((I.card : ℕ) : ℤ) = ∑ _i ∈ I, (1 : ℤ) := by simp
        rw [h4]
        refine (Finset.sum_le_sum (fun i hi => ?_)).trans
          (Finset.sum_le_sum_of_subset_of_nonneg h2 (fun _ _ _ => abs_nonneg _))
        exact Int.one_le_abs (Finsupp.mem_support_iff.1 (h2 hi))
      have h5 := h3.trans (hr z hz2).2
      rw [hIc] at h5
      push_cast at h5
      omega
    obtain ⟨M, hM⟩ := hfin.bddAbove
    -- the low part and the tail
    let low : ℤ → ℕ →₀ ℤ := fun z => (r z).filter (fun i => i ≤ M)
    let tl : ℤ → ℕ →₀ ℤ := fun z => (r z).filter (fun i => ¬ i ≤ M)
    have hsplit : ∀ z ∈ B, z = Sparse.val y (low z) + Sparse.val y (tl z) := by
      intro z hz
      rw [← Sparse.val_add, Finsupp.filter_add_filter_not, (hr z hz).1]
    have hlow : ∃ a0 : ℤ, {z | z ∈ B ∧ Sparse.val y (low z) = a0} ∈ p := by
      set V : Finset ℤ := (Fintype.piFinset (fun _ : Fin (M + 1) => Finset.Icc (-(n : ℤ)) n)).image
        (fun c => ∑ i : Fin (M + 1), c i * y i) with hV
      have hmemV : ∀ z ∈ B, Sparse.val y (low z) ∈ V := by
        intro z hz
        refine Finset.mem_image.2 ⟨fun i : Fin (M + 1) => r z i, ?_, ?_⟩
        · rw [Fintype.mem_piFinset]
          intro i
          exact Finset.mem_Icc.2 (abs_le.1 (hcoef n _ (hr z hz).2 _))
        · rw [Fin.sum_univ_eq_sum_range (fun i => r z i * y i) (M + 1)]
          symm
          unfold Sparse.val Finsupp.sum
          have h1 : (low z).support ⊆ Finset.range (M + 1) := by
            intro i hi
            have h2 : i ∈ (r z).support.filter (fun i => i ≤ M) := by
              rwa [← Finsupp.support_filter]
            exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_filter.1 h2).2)
          have h3 : ∑ i ∈ (low z).support, low z i * y i = ∑ i ∈ Finset.range (M + 1), low z i * y i :=
            Finset.sum_subset h1 (fun i _ hi => by rw [Finsupp.notMem_support_iff.1 hi, zero_mul])
          rw [h3]
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have h4 : i ≤ M := Nat.le_of_lt_succ (Finset.mem_range.1 hi)
          show (r z).filter (fun i => i ≤ M) i * y i = r z i * y i
          rw [Finsupp.filter_apply_pos (fun i => i ≤ M) (r z) h4]
      by_contra hc
      have h2 : (⋂ a ∈ V, {z | z ∈ B ∧ Sparse.val y (low z) = a}ᶜ) ∈ (p : Filter ℤ) := by
        refine (Filter.biInter_finset_mem _).2 (fun a _ => ?_)
        rcases p.mem_or_compl_mem {z | z ∈ B ∧ Sparse.val y (low z) = a} with h3 | h3
        · exact absurd ⟨a, h3⟩ hc
        · exact h3
      obtain ⟨z, hz1, hz2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (p : Filter ℤ)) h2 hBp)
      exact mem_iInter₂.1 hz1 _ (hmemV z hz2) ⟨hz2, rfl⟩
    obtain ⟨a0, ha0⟩ := hlow
    -- the number of terms of the tail
    let sz : (ℕ →₀ ℤ) → ℤ := fun c => ∑ i ∈ c.support, |c i|
    have hsz : ∀ z ∈ B, 0 ≤ sz (tl z) ∧ sz (tl z) ≤ (n : ℤ) := by
      intro z hz
      refine ⟨Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
      have h1 : sz (tl z) = ∑ i ∈ (r z).support.filter (fun i => ¬ i ≤ M), |r z i| := by
        show ∑ i ∈ (tl z).support, |tl z i| = _
        rw [show (tl z).support = (r z).support.filter (fun i => ¬ i ≤ M) from Finsupp.support_filter _ _]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        show |(r z).filter (fun i => ¬ i ≤ M) i| = |r z i|
        rw [Finsupp.filter_apply_pos (fun i => ¬ i ≤ M) (r z) (Finset.mem_filter.1 hi).2]
      rw [h1]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => abs_nonneg _)).trans (hr z hz).2
    have hk : ∃ k : ℤ, {z | z ∈ B ∧ sz (tl z) = k} ∈ p := by
      by_contra hc
      have h2 : (⋂ k ∈ Finset.Icc (0 : ℤ) n, {z | z ∈ B ∧ sz (tl z) = k}ᶜ) ∈ (p : Filter ℤ) := by
        refine (Filter.biInter_finset_mem _).2 (fun k _ => ?_)
        rcases p.mem_or_compl_mem {z | z ∈ B ∧ sz (tl z) = k} with h3 | h3
        · exact absurd ⟨k, h3⟩ hc
        · exact h3
      obtain ⟨z, hz1, hz2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (p : Filter ℤ)) h2 hBp)
      exact mem_iInter₂.1 hz1 _ (Finset.mem_Icc.2 (hsz z hz2)) ⟨hz2, rfl⟩
    obtain ⟨k, hkp⟩ := hk
    -- the tail lies far out
    have hfar : ∀ L : ℕ, {z | z ∈ B ∧ ∀ i ∈ (tl z).support, L < i} ∈ p := by
      intro L
      have h1 : (⋂ i ∈ (Finset.range (L + 1)).filter (fun i => M < i), {z | z ∈ B ∧ r z i = hh i})
          ∈ (p : Filter ℤ) := (Filter.biInter_finset_mem _).2 (fun i _ => hhp i)
      refine Filter.mem_of_superset (Filter.inter_mem h1 hBp) (fun z hz => ⟨hz.2, fun i hi => ?_⟩)
      have h2 : i ∈ (r z).support.filter (fun i => ¬ i ≤ M) := by
        rwa [← Finsupp.support_filter]
      obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h2
      by_contra hiL
      have h5 : i ∈ (Finset.range (L + 1)).filter (fun i => M < i) :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by omega⟩
      have h6 := (mem_iInter₂.1 hz.1 i h5).2
      have h7 : hh i = 0 := by
        by_contra h8
        exact h4 (hM h8)
      exact Finsupp.mem_support_iff.1 h3 (h6.trans h7)
    have hk0 : k ≠ 0 := by
      intro hk0
      have h1 : ({a0} : Set ℤ) ∈ p := by
        refine Filter.mem_of_superset (Filter.inter_mem ha0 hkp) (fun z hz => ?_)
        obtain ⟨⟨hzB, hza⟩, ⟨_, hzk⟩⟩ := hz
        have h2 : tl z = 0 := by
          by_contra h3
          obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 h3
          have h4 : |tl z i| ≤ sz (tl z) :=
            Finset.single_le_sum (f := fun i => |tl z i|) (fun _ _ => abs_nonneg _) hi
          rw [hzk, hk0] at h4
          have h5 := Int.one_le_abs (Finsupp.mem_support_iff.1 hi)
          omega
        rw [mem_singleton_iff, hsplit z hzB, h2, Sparse.val_zero, add_zero, hza]
      obtain ⟨b, _, h2⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h1
      exact hpfree b h2
    obtain ⟨L, hL⟩ := far_zero y hpos hgrow (3 * n) (-a0)
    -- compare `p` with `p + p`
    set Zs : Set ℤ := {z | z ∈ B ∧ Sparse.val y (low z) = a0 ∧ sz (tl z) = k ∧ ∀ i ∈ (tl z).support, L < i}
      with hZs
    have hZp : Zs ∈ p := by
      refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem ha0 hkp) (hfar L)) (fun z hz => ?_)
      exact ⟨hz.1.1.1, hz.1.1.2, hz.1.2.2, hz.2.2⟩
    have htwice : ∀ᶠ x in (p : Filter ℤ), ∀ᶠ z in (p : Filter ℤ), x + z ∈ Zs := by
      have h1 : Zs ∈ p + p := by rw [hpp]; exact hZp
      rw [mem_add] at h1
      exact h1
    obtain ⟨x, hx1, hx2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (p : Filter ℤ)) htwice hZp)
    set Lx : ℕ := (tl x).support.sup id with hLx
    obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := Ultrafilter.nonempty_of_mem
      (Filter.inter_mem (f := (p : Filter ℤ)) (Filter.inter_mem (f := (p : Filter ℤ)) hx1 hZp) (hfar Lx))
    have hw : x + z ∈ Zs := hz1
    have hdisj : Disjoint (tl x).support (tl z).support := by
      rw [Finset.disjoint_left]
      intro i hix hiz
      have h1 : i ≤ Lx := Finset.le_sup (f := id) hix
      have h2 := hz3.2 i hiz
      omega
    set e : ℕ →₀ ℤ := tl (x + z) - (tl x + tl z) with he
    have hval : Sparse.val y e = a0 := by
      have h1 := hsplit x hx2.1
      have h2 := hsplit z hz2.1
      have h3 := hsplit (x + z) hw.1
      rw [hx2.2.1] at h1
      rw [hz2.2.1] at h2
      rw [hw.2.1] at h3
      have h4 : Sparse.val y e = Sparse.val y (tl (x + z)) - (Sparse.val y (tl x) + Sparse.val y (tl z)) := by
        rw [he, sub_eq_add_neg, Sparse.val_add, Sparse.val_neg, Sparse.val_add]
        ring
      rw [h4]
      omega
    have hecoef : ∀ i, |e i| ≤ ((3 * n : ℕ) : ℤ) := by
      intro i
      have htl : ∀ w ∈ B, |tl w i| ≤ (n : ℤ) := by
        intro w hwB
        by_cases hi : i ∈ (tl w).support
        · exact (Finset.single_le_sum (f := fun i => |tl w i|) (fun _ _ => abs_nonneg _) hi).trans (hsz w hwB).2
        · rw [Finsupp.notMem_support_iff.1 hi]; simp
      have h1 := htl x hx2.1
      have h2 := htl z hz2.1
      have h3 := htl (x + z) hw.1
      have h4 : e i = tl (x + z) i - (tl x i + tl z i) := by
        rw [he, Finsupp.sub_apply, Finsupp.add_apply]
      rw [h4, abs_le]
      rw [abs_le] at h1 h2 h3
      push_cast
      omega
    have hesupp : ∀ i ∈ e.support, L < i := by
      intro i hi
      have h1 : i ∈ (tl (x + z)).support ∨ i ∈ (tl x).support ∨ i ∈ (tl z).support := by
        by_contra h2
        rw [not_or, not_or] at h2
        apply Finsupp.mem_support_iff.1 hi
        rw [he, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.notMem_support_iff.1 h2.1,
          Finsupp.notMem_support_iff.1 h2.2.1, Finsupp.notMem_support_iff.1 h2.2.2]
        simp
      rcases h1 with h | h | h
      · exact hw.2.2.2 i h
      · exact hx2.2.2.2 i h
      · exact hz2.2.2.2 i h
    have hval0 : Sparse.val y (-e) = -a0 := by rw [Sparse.val_neg, hval]
    have he0 : -e = 0 := hL (-e) (fun i => by rw [Finsupp.neg_apply, abs_neg]; exact hecoef i)
      (fun i hi => hesupp i (by rwa [Finsupp.support_neg] at hi)) hval0
    have htl : tl (x + z) = tl x + tl z := by
      have h1 : e = 0 := neg_eq_zero.1 he0
      rw [he, sub_eq_zero] at h1
      exact h1
    have h2k : k = k + k := by
      have h1 : sz (tl x + tl z) = sz (tl x) + sz (tl z) := by
        show ∑ i ∈ (tl x + tl z).support, |(tl x + tl z) i| = _
        rw [Finsupp.support_add_eq hdisj, Finset.sum_union hdisj]
        congr 1
        · refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [Finsupp.add_apply, Finsupp.notMem_support_iff.1 (Finset.disjoint_left.1 hdisj hi), add_zero]
        · refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [Finsupp.add_apply, Finsupp.notMem_support_iff.1 (Finset.disjoint_right.1 hdisj hi), zero_add]
      rw [← htl, hw.2.2.1, hx2.2.2.1, hz2.2.2.1] at h1
      exact h1
    omega

end Sparse

end Idem

end PG
