import Mathlib
import LeanCheck.PGThreeSelective
import LeanCheck.PGThreeSparse
import LeanCheck.PGTwoReflection

/-!
# PGthree: ultrafilters with bounded digits (Lean check)

Scope. Section 9 of the third article (`PGthree.tex`).

* `nsmul_map_le` : if an ultrafilter is finer than a symmetric halvable neighbourhood filter, so are all its integer
  multiples;
* `bounded_nbhd` : for ultrafilters each containing a member of a bounded filtration with property (G), the
  neighbourhood filters of group topologies among the null filters of the generated PG are exactly the principal filters
  of the finite subgroups all of whose points converge to `0`;
* `bounded_discrete` : if the only finite subgroup is trivial, the only one is `pure 0`, and for a nonempty family the
  vicinity filter is not null;
* `freeAbelian_discrete` : vectors with bounded coordinates in a free abelian group;
* `digits_discrete` : integers with bounded digits with respect to a rapidly growing sequence.

No set-theoretic hypothesis is used. A Lean proof verifies its formal statement under its hypotheses; the
correspondence with the article requires mathematical review.
-/

open Filter Set Topology

namespace PG

namespace Height

open Sel

variable {G : Type} [AddCommGroup G]

theorem exists_nsmul_mem {N : Filter G} (hN : IsNbhdFilter N) (m : ℕ) :
    ∀ A ∈ N, ∃ B ∈ N, ∀ x ∈ B, m • x ∈ A := by
  induction m with
  | zero =>
    intro A hA
    refine ⟨univ, univ_mem, fun x _ => ?_⟩
    rw [zero_smul]
    exact hN.zero_mem A hA
  | succ m ih =>
    intro A hA
    obtain ⟨B1, hB1, h1⟩ := hN.halve A hA
    obtain ⟨B2, hB2, h2⟩ := ih B1 hB1
    refine ⟨B1 ∩ B2, Filter.inter_mem hB1 hB2, fun x hx => ?_⟩
    rw [succ_nsmul]
    exact h1 _ (h2 x hx.2) x hx.1

/-- Integer multiples of a filter finer than `N` are finer than `N`. -/
theorem nsmul_map_le {N : Filter G} (hN : IsNbhdFilter N) (e : Filter G) (he : e ≤ N) (m : ℕ) :
    e.map (fun x => m • x) ≤ N := by
  intro A hA
  obtain ⟨B, hB, h⟩ := exists_nsmul_mem hN m A hA
  exact Filter.mem_map.2 (Filter.mem_of_superset (he hB) h)

/-- A bounded filtration. -/
structure Bounded (B : ℕ → Set G) : Prop where
  zero : (0 : G) ∈ B 0
  neg : ∀ k, ∀ x ∈ B k, -x ∈ B k
  add : ∀ j k, ∀ x ∈ B j, ∀ y ∈ B k, x + y ∈ B (j + k)

theorem Bounded.signed_sum {B : ℕ → Set G} (hB : Bounded B) {ι : Type*} (s : Finset ι) (a : ι → G) (b : ι → ℕ)
    (ε : ι → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (ha : ∀ i, a i ∈ B (b i)) :
    ∑ i ∈ s, ε i • a i ∈ B (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine hB.add _ _ _ ?_ _ ih
    rcases hε i with h | h
    · rw [h, one_smul]; exact ha i
    · rw [h, neg_one_zsmul]; exact hB.neg _ _ (ha i)

/-- Every null ultrafilter of the generated PG contains a member of the filtration. -/
theorem null_contains {B : ℕ → Set G} (hB : Bounded B) (S : Set (Ultrafilter G)) (hSB : ∀ u ∈ S, ∃ b, B b ∈ u)
    (p : Ultrafilter G) (hp : (p : Filter G) ∈ genFam (ultraGen S)) : ∃ k, B k ∈ p := by
  classical
  obtain ⟨σ, hσ, hpσ⟩ := hp.2 p le_rfl
  obtain ⟨ι, _, u, ε, hu, hε, h⟩ := rep_of_sumClosure S hσ
  choose b hb using fun i => hSB (u i) (hu i)
  refine ⟨∑ i, b i, hpσ (Filter.mem_of_superset (h (fun i => B (b i)) hb) (fun z hz => ?_))⟩
  obtain ⟨a, ha, hsum⟩ := hz
  rw [← hsum]
  exact hB.signed_sum Finset.univ a b ε hε ha

/-- The criterion for ultrafilters on members of a bounded filtration. -/
theorem bounded_nbhd (B : ℕ → Set G) (hB : Bounded B) (W : Set ℕ) (hW : W.Infinite)
    (hG : ∀ j k : ℕ, ∀ᶠ m in atTop, m ∈ W → {x : G | x ∈ B j ∧ m • x ∈ B k}.Finite)
    (S : Set (Ultrafilter G)) (hSB : ∀ u ∈ S, ∃ b, B b ∈ u) (N : Filter G) :
    (IsNbhdFilter N ∧ N ∈ genFam (ultraGen S)) ↔
      ∃ F : AddSubgroup G, (F : Set G).Finite ∧ (∀ g ∈ F, (pure g : Filter G) ∈ genFam (ultraGen S)) ∧
        N = 𝓟 (F : Set G) := by
  classical
  have hC : NullFamily (genFam (ultraGen S)) := genFam_nullFamily _
  constructor
  · rintro ⟨hN, hNC⟩
    have hprin : ∀ e : Ultrafilter G, (e : Filter G) ≤ N → ∃ a, e = pure a := by
      intro e heN
      by_contra hfreee
      have heC : (e : Filter G) ∈ genFam (ultraGen S) := hC.finer _ hNC _ heN e.neBot
      obtain ⟨j, hj⟩ := null_contains hB S hSB e heC
      have hWne : (atTop ⊓ 𝓟 W : Filter ℕ).NeBot := by
        rw [← Nat.cofinite_eq_atTop]
        exact hW.cofinite_inf_principal_neBot
      set v : Ultrafilter ℕ := Ultrafilter.of (atTop ⊓ 𝓟 W) with hv
      have hvle : (v : Filter ℕ) ≤ atTop ⊓ 𝓟 W := Ultrafilter.of_le _
      set L : Filter G := Filter.bind (v : Filter ℕ) (fun m => (e : Filter G).map (fun x => m • x)) with hL
      have hmemL : ∀ A : Set G, (∀ᶠ m in (v : Filter ℕ), A ∈ (e : Filter G).map (fun x => m • x)) → A ∈ L :=
        fun A hA => Filter.mem_bind'.2 hA
      have hLN : L ≤ N := fun A hA =>
        hmemL A (Filter.Eventually.of_forall (fun m => nsmul_map_le hN _ heN m hA))
      have hLne : L.NeBot := by
        rw [Filter.neBot_iff]
        intro hbot
        have h1 : (∅ : Set G) ∈ L := by rw [hbot]; exact Filter.mem_bot
        have h2 : ∀ᶠ m in (v : Filter ℕ), (∅ : Set G) ∈ (e : Filter G).map (fun x => m • x) :=
          Filter.mem_bind'.1 h1
        obtain ⟨m, hm⟩ := h2.exists
        have h3 : (∅ : Set G) ∈ (e : Filter G) := Filter.mem_map.1 hm
        exact Filter.empty_notMem (e : Filter G) h3
      set r : Ultrafilter G := Ultrafilter.of L with hr
      have hrL : (r : Filter G) ≤ L := Ultrafilter.of_le _
      have hrC : (r : Filter G) ∈ genFam (ultraGen S) := hC.finer _ hNC _ (hrL.trans hLN) r.neBot
      obtain ⟨k, hk⟩ := null_contains hB S hSB r hrC
      have h1 : ∀ᶠ m in (v : Filter ℕ), (fun x : G => m • x) ⁻¹' B k ∈ e := by
        rcases v.mem_or_compl_mem {m : ℕ | (fun x : G => m • x) ⁻¹' B k ∈ e} with h | h
        · exact h
        · have h2 : (B k)ᶜ ∈ L := by
            refine hmemL _ (Filter.mem_of_superset h (fun m hm => ?_))
            exact Filter.mem_map.2 (Ultrafilter.compl_mem_iff_notMem.2 hm)
          exact absurd hk (Ultrafilter.compl_mem_iff_notMem.1 (hrL h2))
      have h2 : ∀ᶠ m in (v : Filter ℕ), m ∈ W := hvle.trans inf_le_right (mem_principal_self W)
      have h3 : ∀ᶠ m in (v : Filter ℕ), m ∈ W → {x : G | x ∈ B j ∧ m • x ∈ B k}.Finite :=
        (hvle.trans inf_le_left) (hG j k)
      obtain ⟨m, hm1, hm2, hm3⟩ := (h1.and (h2.and h3)).exists
      have h4 : {x : G | x ∈ B j ∧ m • x ∈ B k} ∈ e := Filter.inter_mem (f := (e : Filter G)) hj hm1
      obtain ⟨a, _, ha⟩ := Ultrafilter.eq_pure_of_finite_mem (hm3 hm2) h4
      exact hfreee ⟨a, ha⟩
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
          obtain ⟨D, hD, hDs⟩ := hN.halve s hs
          exact hDs a (ha D hD) b (hb D hD)
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

/-- With no nontrivial finite subgroup: only `pure 0`, and no pretopology for a nonempty family. -/
theorem bounded_discrete (B : ℕ → Set G) (hB : Bounded B) (W : Set ℕ) (hW : W.Infinite)
    (hG : ∀ j k : ℕ, ∀ᶠ m in atTop, m ∈ W → {x : G | x ∈ B j ∧ m • x ∈ B k}.Finite)
    (S : Set (Ultrafilter G)) (hfree : ∀ u ∈ S, ∀ a, u ≠ pure a) (hSB : ∀ u ∈ S, ∃ b, B b ∈ u)
    (htf : ∀ F : AddSubgroup G, (F : Set G).Finite → F = ⊥) :
    (∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen S) → N = pure 0) ∧
      (S.Nonempty → vic (genFam (ultraGen S)) ∉ genFam (ultraGen S)) := by
  classical
  have hC : NullFamily (genFam (ultraGen S)) := genFam_nullFamily _
  have main : ∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen S) → N = pure 0 := by
    intro N hN hNC
    obtain ⟨F, hFfin, _, rfl⟩ := (bounded_nbhd B hB W hW hG S hSB N).1 ⟨hN, hNC⟩
    rw [htf F hFfin, AddSubgroup.coe_bot, principal_singleton]
  refine ⟨main, ?_⟩
  rintro ⟨u, hu⟩ hvic
  have huC : (u : Filter G) ∈ genFam (ultraGen S) :=
    ⟨u.neBot, fun U hU => ⟨u, SumClosure.gen ⟨u, hu, rfl⟩, hU⟩⟩
  have hV : IsNbhdFilter (vic (genFam (ultraGen S))) := by
    refine ⟨fun A hA => vic_zero_mem hC hA, fun A hA => vic_neg hC hA, fun A hA => ?_⟩
    have h1 : Filter.map₂ (· + ·) (vic (genFam (ultraGen S))) (vic (genFam (ultraGen S)))
        ≤ vic (genFam (ultraGen S)) := le_vic (hC.add _ hvic _ hvic)
    obtain ⟨B1, hB1, B2, hB2, h2⟩ := Filter.mem_map₂_iff.1 (h1 hA)
    exact ⟨B1 ∩ B2, Filter.inter_mem hB1 hB2, fun x hx y hy => h2 (mem_image2_of_mem hx.1 hy.2)⟩
  have h0 := main _ hV hvic
  have h1 : (u : Filter G) ≤ pure 0 := h0 ▸ le_vic huC
  have h2 : ({0} : Set G) ∈ u := h1 (Filter.mem_pure.2 rfl)
  obtain ⟨b, _, h3⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h2
  exact hfree u hu b h3

/-! ### Free abelian groups -/

section FreeAbelian

variable (ι : Type)

/-- The vectors with all coordinates of absolute value at most `k`. -/
def box (k : ℕ) : Set (ι →₀ ℤ) := {x | ∀ i, |x i| ≤ (k : ℤ)}

theorem box_bounded : Bounded (box ι) := by
  refine ⟨fun i => by simp, fun k x hx i => ?_, fun j k x hx y hy i => ?_⟩
  · rw [Finsupp.neg_apply, abs_neg]; exact hx i
  · rw [Finsupp.add_apply]
    push_cast
    exact (abs_add_le _ _).trans (add_le_add (hx i) (hy i))

theorem box_G (j k : ℕ) : ∀ᶠ m in atTop, m ∈ (univ : Set ℕ) → {x : ι →₀ ℤ | x ∈ box ι j ∧ m • x ∈ box ι k}.Finite := by
  filter_upwards [eventually_gt_atTop k] with m hm _
  refine (finite_singleton (0 : ι →₀ ℤ)).subset (fun x hx => ?_)
  rw [mem_singleton_iff]
  ext i
  by_contra h
  have h1 := hx.2 i
  rw [Finsupp.smul_apply, nsmul_eq_mul, abs_mul, Nat.abs_cast] at h1
  have h2 : 1 ≤ |x i| := Int.one_le_abs (by simpa using h)
  have h3 : (m : ℤ) ≤ (m : ℤ) * |x i| := le_mul_of_one_le_right (Int.natCast_nonneg m) h2
  have h4 : (k : ℤ) < (m : ℤ) := by exact_mod_cast hm
  omega

theorem finsupp_finite_subgroup (F : AddSubgroup (ι →₀ ℤ)) (hF : (F : Set (ι →₀ ℤ)).Finite) : F = ⊥ := by
  rw [AddSubgroup.eq_bot_iff_forall]
  intro g hg
  have : Finite F := hF.to_subtype
  obtain ⟨n, hn, h⟩ := (isOfFinAddOrder_of_finite (⟨g, hg⟩ : F)).exists_nsmul_eq_zero
  have h1 : n • g = 0 := by simpa using congrArg Subtype.val h
  ext i
  have h2 := DFunLike.congr_fun h1 i
  rw [Finsupp.smul_apply, nsmul_eq_mul, Finsupp.zero_apply] at h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (Int.natCast_eq_zero.1 h3) hn.ne'
  · simpa using h3

theorem freeAbelian_discrete (S : Set (Ultrafilter (ι →₀ ℤ))) (hfree : ∀ u ∈ S, ∀ a, u ≠ pure a)
    (hSB : ∀ u ∈ S, ∃ b, box ι b ∈ u) :
    (∀ N : Filter (ι →₀ ℤ), IsNbhdFilter N → N ∈ genFam (ultraGen S) → N = pure 0) ∧
      (S.Nonempty → vic (genFam (ultraGen S)) ∉ genFam (ultraGen S)) :=
  bounded_discrete (box ι) (box_bounded ι) univ infinite_univ (box_G ι) S hfree hSB (finsupp_finite_subgroup ι)

end FreeAbelian

/-! ### Bounded digits with respect to a rapidly growing sequence -/

section Digits

variable (y : ℕ → ℤ)

/-- The integers with a representation with digits of absolute value at most `k`. -/
def digits (k : ℕ) : Set ℤ := {z | ∃ c : ℕ →₀ ℤ, Sparse.val y c = z ∧ ∀ i, |c i| ≤ (k : ℤ)}

theorem digits_bounded : Bounded (digits y) := by
  refine ⟨⟨0, Sparse.val_zero y, fun i => by simp⟩, ?_, ?_⟩
  · rintro k x ⟨c, hc, hck⟩
    refine ⟨-c, by rw [Sparse.val_neg, hc], fun i => ?_⟩
    rw [Finsupp.neg_apply, abs_neg]; exact hck i
  · rintro j k x ⟨c, hc, hcj⟩ z ⟨d, hd, hdk⟩
    refine ⟨c + d, by rw [Sparse.val_add, hc, hd], fun i => ?_⟩
    rw [Finsupp.add_apply]
    push_cast
    exact (abs_add_le _ _).trans (add_le_add (hcj i) (hdk i))

variable (hpos : ∀ i, 0 < y i)
  (hgrow : ∀ B : ℕ, ∃ L : ℕ, ∀ l, L < l → 2 * (B : ℤ) * ∑ i ∈ Finset.range l, y i < y l)

include hpos hgrow in
/-- A combination with bounded coefficients and value `0` has no terms far out. -/
theorem zero_far (n : ℕ) : ∃ L : ℕ, ∀ e : ℕ →₀ ℤ, (∀ i, |e i| ≤ (n : ℤ)) → Sparse.val y e = 0 →
    ∀ i, L < i → e i = 0 := by
  classical
  obtain ⟨L, hL⟩ := hgrow (n + 1)
  refine ⟨L, fun e he hval i hi => ?_⟩
  by_contra hne
  have hs : e.support.Nonempty := ⟨i, Finsupp.mem_support_iff.2 hne⟩
  set l := e.support.max' hs with hl
  have hlmem : l ∈ e.support := e.support.max'_mem hs
  have hLl : L < l := lt_of_lt_of_le hi (e.support.le_max' i (Finsupp.mem_support_iff.2 hne))
  have h1 := hL l hLl
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
  have h5 : |e l * y l| = |∑ i ∈ Finset.range l, e i * y i| := by
    have h6 : e l * y l = -∑ i ∈ Finset.range l, e i * y i := by
      rw [hval] at hsum
      omega
    rw [h6, abs_neg]
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ => (hpos i).le)
  have h8 : 2 * ((n : ℤ) + 1) * T < y l := by exact_mod_cast h1
  have h11 : 0 ≤ (n : ℤ) * T := mul_nonneg (Int.natCast_nonneg n) hT0
  have h12 : 2 * ((n : ℤ) + 1) * T = (n : ℤ) * T + (n : ℤ) * T + (T + T) := by ring
  omega

include hpos hgrow in
theorem digits_G (j k : ℕ) :
    ∀ᶠ m in atTop, m ∈ (univ : Set ℕ) → {x : ℤ | x ∈ digits y j ∧ m • x ∈ digits y k}.Finite := by
  classical
  filter_upwards [eventually_gt_atTop k] with m hm _
  obtain ⟨L, hL⟩ := zero_far y hpos hgrow (m * j + k)
  set V : Finset ℤ := (Fintype.piFinset (fun _ : Fin (L + 1) => Finset.Icc (-(j : ℤ)) j)).image
    (fun c => ∑ i : Fin (L + 1), c i * y i) with hV
  refine V.finite_toSet.subset (fun x hx => ?_)
  obtain ⟨⟨c, hc, hcj⟩, ⟨d, hd, hdk⟩⟩ := hx
  set e : ℕ →₀ ℤ := (m : ℤ) • c + -d with he
  have heval : Sparse.val y e = 0 := by
    rw [he, Sparse.val_add, Sparse.val_neg, Sparse.val_smul, hc, hd, nsmul_eq_mul, add_neg_cancel]
  have heapp : ∀ i, e i = (m : ℤ) * c i + -d i := by
    intro i
    rw [he, Finsupp.add_apply, Finsupp.neg_apply, Finsupp.smul_apply, smul_eq_mul]
  have hecoef : ∀ i, |e i| ≤ ((m * j + k : ℕ) : ℤ) := by
    intro i
    rw [heapp]
    push_cast
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hcj i) (Int.natCast_nonneg m)
    · rw [abs_neg]; exact hdk i
  have hc0 : ∀ i, L < i → c i = 0 := by
    intro i hi
    have h1 := hL e hecoef heval i hi
    rw [heapp] at h1
    by_contra h2
    have h3 : 1 ≤ |c i| := Int.one_le_abs h2
    have h4 : |d i| = (m : ℤ) * |c i| := by
      have h5 : d i = (m : ℤ) * c i := by omega
      rw [h5, abs_mul, Nat.abs_cast]
    have h6 : (m : ℤ) ≤ (m : ℤ) * |c i| := le_mul_of_one_le_right (Int.natCast_nonneg m) h3
    have h7 : (k : ℤ) < (m : ℤ) := by exact_mod_cast hm
    have h8 := hdk i
    omega
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨fun i : Fin (L + 1) => c i, ?_, ?_⟩)
  · rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.2 (abs_le.1 (hcj _))
  · rw [← hc, Fin.sum_univ_eq_sum_range (fun i => c i * y i) (L + 1)]
    symm
    unfold Sparse.val Finsupp.sum
    refine Finset.sum_subset (fun i hi => ?_) (fun i _ hi => ?_)
    swap
    · show c i * y i = 0
      rw [Finsupp.notMem_support_iff.1 hi, zero_mul]
    refine Finset.mem_range.2 (Nat.lt_succ_of_le (not_lt.1 (fun h => ?_)))
    exact Finsupp.mem_support_iff.1 hi (hc0 i h)

theorem int_finite_subgroup (F : AddSubgroup ℤ) (hF : (F : Set ℤ).Finite) : F = ⊥ := by
  rw [AddSubgroup.eq_bot_iff_forall]
  intro g hg
  have : Finite F := hF.to_subtype
  obtain ⟨n, hn, h⟩ := (isOfFinAddOrder_of_finite (⟨g, hg⟩ : F)).exists_nsmul_eq_zero
  have h1 : n • g = 0 := by simpa using congrArg Subtype.val h
  rw [nsmul_eq_mul] at h1
  rcases mul_eq_zero.1 h1 with h3 | h3
  · exact absurd (Int.natCast_eq_zero.1 h3) hn.ne'
  · exact h3

include hpos hgrow in
theorem digits_discrete (S : Set (Ultrafilter ℤ)) (hfree : ∀ u ∈ S, ∀ a, u ≠ pure a)
    (hSB : ∀ u ∈ S, ∃ b, digits y b ∈ u) :
    (∀ N : Filter ℤ, IsNbhdFilter N → N ∈ genFam (ultraGen S) → N = pure 0) ∧
      (S.Nonempty → vic (genFam (ultraGen S)) ∉ genFam (ultraGen S)) :=
  bounded_discrete (digits y) (digits_bounded y) univ infinite_univ (digits_G y hpos hgrow) S hfree hSB
    int_finite_subgroup

end Digits

end Height

end PG
