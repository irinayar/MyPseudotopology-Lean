import Mathlib
import LeanCheck.PGThreeSelective
import LeanCheck.PGThreeExact
import LeanCheck.PGTwoReflection
import LeanCheck.PGTwoCoreflection

/-!
# PGthree: the ultrafilters converging to zero for a selective family (Lean check)

Scope. Section 6 of the third article (`PGthree.tex`). `G` is a countably infinite abelian group in which only finitely
many `x` satisfy `m • x = 0` for every `m ≥ 1`, `S` is a set of pairwise non-isomorphic selective ultrafilters on `G`,
and `C = genFam (ultraGen S)`.

* `pw w` : the sum, in the semigroup of ultrafilters, of the images `c • u` for the letters `(u, c)` of the word `w`;
* `null_free_iff` : the nonprincipal ultrafilters in `C` are exactly the `pw w`, `w` a nonempty word with letters in
  `S` and nonzero coefficients (Theorem 6.1, existence);
* `pw_injective` : different such words give different ultrafilters (Theorem 6.1, uniqueness);
* `only_trivial`, `kernel_open` : for every such `S`, whatever its size, the only neighbourhood filter of a group
  topology that lies in `C` is `pure 0`, every continuous homomorphism from a topological group into the PG has an
  open kernel, and the vicinity filter is not in `C` when `S` is nonempty (Theorem 6.2);
* `exists_discrete_coreflection` : under the statement (S), a Hausdorff PG with the cofinite vicinity filter at `0`,
  indiscrete finest group topology and no nontrivial null group filter (Corollary 6.3).

No set-theoretic hypothesis is used except where (S) is assumed. A Lean proof verifies its formal statement under its
hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Set Topology

namespace PG

namespace Null

open Sel

attribute [local instance] Ultrafilter.add Ultrafilter.addSemigroup

/-! ### Large sets -/

theorem large_mono : ∀ (r : ℕ) (v : Fin r → Ultrafilter ℕ) {R R' : Set (Fin r → ℕ)}, R ⊆ R' →
    Large r v R → Large r v R' := by
  intro r
  induction r with
  | zero => intro v R R' h hR; exact h hR
  | succ r ih =>
    intro v R R' h hR
    rw [large_succ] at hR ⊢
    exact Filter.mem_of_superset hR (fun x hx => ih _ (fun t ht => h ht) hx)

theorem large_compl : ∀ (r : ℕ) (v : Fin r → Ultrafilter ℕ) (R : Set (Fin r → ℕ)),
    Large r v Rᶜ ↔ ¬ Large r v R := by
  intro r
  induction r with
  | zero => intro v R; exact Iff.rfl
  | succ r ih =>
    intro v R
    rw [large_succ, large_succ, ← Ultrafilter.compl_mem_iff_notMem]
    have h : {x : ℕ | Large r (fun i => v i.succ) {t : Fin r → ℕ | Fin.cons x t ∈ Rᶜ}}
        = {x : ℕ | Large r (fun i => v i.succ) {t : Fin r → ℕ | Fin.cons x t ∈ R}}ᶜ := by
      ext x
      rw [mem_compl_iff, mem_setOf_eq, mem_setOf_eq, ← ih]
      exact Iff.rfl
    rw [h]

/-- Increasing tuples from given members form a large set. -/
theorem large_inc : ∀ (r : ℕ) (v : Fin r → Ultrafilter ℕ), (∀ i a, v i ≠ pure a) →
    ∀ (B : Fin r → Set ℕ), (∀ i, B i ∈ v i) → ∀ N : ℕ,
      Large r v {y | StrictMono y ∧ (∀ i, y i ∈ B i) ∧ ∀ i, N < y i} := by
  intro r
  induction r with
  | zero =>
    intro v _ B _ N
    exact ⟨fun a => a.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ r ih =>
    intro v hv B hB N
    rw [large_succ]
    have hN : {x : ℕ | N < x} ∈ v 0 := by
      rcases (v 0).mem_or_compl_mem {x : ℕ | N < x} with h | h
      · exact h
      · refine absurd h (notMem_of_finite (hv 0) ((finite_Iic N).subset (fun x hx => ?_)))
        have : ¬ N < x := hx
        exact mem_Iic.2 (by omega)
    refine Filter.mem_of_superset (Filter.inter_mem (hB 0) hN) (fun x hx => ?_)
    obtain ⟨hxB, hxN⟩ := hx
    have hxN' : N < x := hxN
    refine large_mono r _ (fun t ht => ?_) (ih (fun i => v i.succ) (fun i => hv i.succ) (fun i => B i.succ)
      (fun i => hB i.succ) x)
    obtain ⟨hm, hmem, hlt⟩ := ht
    show StrictMono (Fin.cons x t : Fin (r + 1) → ℕ) ∧ (∀ i, (Fin.cons x t : Fin (r + 1) → ℕ) i ∈ B i)
      ∧ ∀ i, N < (Fin.cons x t : Fin (r + 1) → ℕ) i
    refine ⟨?_, fun i => ?_, fun i => ?_⟩
    · intro a b hab
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero => exact absurd hab (lt_irrefl _)
        | succ b =>
          rw [Fin.cons_zero, Fin.cons_succ]
          exact hlt b
      | succ a =>
        cases b using Fin.cases with
        | zero => exact absurd hab (not_lt.2 (Fin.zero_le _))
        | succ b =>
          rw [Fin.cons_succ, Fin.cons_succ]
          exact hm (Fin.succ_lt_succ_iff.1 hab)
    · cases i using Fin.cases with
      | zero => simpa using hxB
      | succ i => simpa using hmem i
    · cases i using Fin.cases with
      | zero => simpa using hxN'
      | succ i =>
        rw [Fin.cons_succ]
        exact hxN'.trans (hlt i)

/-! ### Words -/

variable {G : Type} [AddCommGroup G]

/-- The sum in the semigroup of ultrafilters of the images `c • u`. -/
def pw : List (Ultrafilter G × ℤ) → Ultrafilter G
  | [] => pure 0
  | x :: w => x.1.map (fun z : G => x.2 • z) + pw w

theorem mem_add (U V : Ultrafilter G) (A : Set G) : A ∈ U + V ↔ {m | {z | m + z ∈ A} ∈ V} ∈ U :=
  Ultrafilter.eventually_add U V (fun m => m ∈ A)

theorem mem_pw_cons (x : Ultrafilter G × ℤ) (w : List (Ultrafilter G × ℤ)) (A : Set G) :
    A ∈ pw (x :: w) ↔ {a | {z | x.2 • a + z ∈ A} ∈ pw w} ∈ x.1 := by
  show A ∈ x.1.map (fun z : G => x.2 • z) + pw w ↔ _
  rw [mem_add]
  exact Iff.rfl

theorem pure_zero_add (V : Ultrafilter G) : (pure 0 : Ultrafilter G) + V = V := by
  refine Ultrafilter.coe_injective (Filter.ext (fun A => ?_))
  show A ∈ (pure 0 : Ultrafilter G) + V ↔ A ∈ V
  rw [mem_add]
  show (0 : G) ∈ {m | {z | m + z ∈ A} ∈ V} ↔ A ∈ V
  rw [mem_setOf_eq]
  have : {z : G | 0 + z ∈ A} = A := by ext z; simp
  rw [this]

theorem pw_append (w w' : List (Ultrafilter G × ℤ)) : pw (w ++ w') = pw w + pw w' := by
  induction w with
  | nil => exact (pure_zero_add _).symm
  | cons x w ih =>
    show x.1.map (fun z : G => x.2 • z) + pw (w ++ w') = (x.1.map (fun z : G => x.2 • z) + pw w) + pw w'
    rw [ih, add_assoc]

theorem map_zero_smul (u : Ultrafilter G) : u.map (fun z : G => (0 : ℤ) • z) = pure 0 := by
  have : (fun z : G => (0 : ℤ) • z) = fun _ => (0 : G) := by funext z; simp
  rw [this]
  refine Ultrafilter.coe_injective ?_
  rw [Ultrafilter.coe_map, Ultrafilter.coe_pure]
  exact Filter.map_const

/-- Letters with coefficient `0` may be omitted. -/
theorem pw_filter (w : List (Ultrafilter G × ℤ)) : pw (w.filter (fun x => decide (x.2 ≠ 0))) = pw w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    by_cases h : x.2 = 0
    · rw [List.filter_cons_of_neg (by simp [h]), ih]
      show pw w = x.1.map (fun z : G => x.2 • z) + pw w
      rw [h, map_zero_smul, pure_zero_add]
    · rw [List.filter_cons_of_pos (by simp [h])]
      show x.1.map (fun z : G => x.2 • z) + pw (w.filter _) = x.1.map (fun z : G => x.2 • z) + pw w
      rw [ih]

/-- Membership in the ultrafilter of a word is largeness of the corresponding set of tuples. -/
theorem mem_pw_ofFn (e : ℕ ≃ G) : ∀ (r : ℕ) (v : Fin r → Ultrafilter G) (c : Fin r → ℤ) (A : Set G),
    A ∈ pw (List.ofFn (fun l => (v l, c l))) ↔
      Large r (fun l => (v l).map e.symm) {y | ∑ l, c l • e (y l) ∈ A} := by
  intro r
  induction r with
  | zero =>
    intro v c A
    rw [List.ofFn_zero, large_zero]
    show A ∈ (pure 0 : Ultrafilter G) ↔ ∑ l : Fin 0, c l • e (Fin.elim0 l) ∈ A
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact Iff.rfl
  | succ r ih =>
    intro v c A
    rw [List.ofFn_succ, mem_pw_cons, large_succ]
    have h : {a : G | {z : G | c 0 • a + z ∈ A} ∈ pw (List.ofFn (fun l : Fin r => (v l.succ, c l.succ)))}
        = e.symm ⁻¹' {x : ℕ | Large r (fun i => (v i.succ).map e.symm)
            {t : Fin r → ℕ | Fin.cons x t ∈ {y : Fin (r + 1) → ℕ | ∑ l, c l • e (y l) ∈ A}}} := by
      ext a
      rw [mem_preimage, mem_setOf_eq, mem_setOf_eq, ih (fun l => v l.succ) (fun l => c l.succ)]
      have hs : {y : Fin r → ℕ | ∑ l, c l.succ • e (y l) ∈ {z : G | c 0 • a + z ∈ A}}
          = {t : Fin r → ℕ | Fin.cons (e.symm a) t ∈ {y : Fin (r + 1) → ℕ | ∑ l, c l • e (y l) ∈ A}} := by
        ext t
        rw [mem_setOf_eq, mem_setOf_eq, mem_setOf_eq, mem_setOf_eq, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, Equiv.apply_symm_apply]
      rw [hs]
    rw [h]
    exact Iff.rfl

/-! ### The null family of a selective family -/

variable [Countable G] [Infinite G] (htor : ∀ m : ℕ, 0 < m → {x : G | m • x = 0}.Finite)
  (S : Set (Ultrafilter G)) (hsel : ∀ u ∈ S, IsSel u) (hiso : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ Iso u v)

/-- A word with letters in `S` and nonzero coefficients. -/
def Good (S : Set (Ultrafilter G)) (w : List (Ultrafilter G × ℤ)) : Prop := ∀ x ∈ w, x.1 ∈ S ∧ x.2 ≠ 0

include htor in
theorem finite_fibre (c : ℤ) (hc : c ≠ 0) (h : G) : {z : G | c • z = h}.Finite := by
  by_cases hne : {z : G | c • z = h}.Nonempty
  · obtain ⟨a0, ha0⟩ := hne
    have hker := htor c.natAbs (Int.natAbs_pos.2 hc)
    refine (hker.image (fun k => a0 + k)).subset (fun a ha => ?_)
    refine ⟨a - a0, ?_, by abel⟩
    have h1 : c • (a - a0) = 0 := by
      have h2 : c • a = h := ha
      have h3 : c • a0 = h := ha0
      rw [smul_sub, h2, h3, sub_self]
    show c.natAbs • (a - a0) = 0
    rcases Int.natAbs_eq c with h' | h'
    · rw [h', natCast_zsmul] at h1; exact h1
    · rw [h', neg_smul, neg_eq_zero, natCast_zsmul] at h1; exact h1
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact finite_empty

theorem gen_ne (S : Set (Ultrafilter G)) : ∀ F ∈ ultraGen S, F.NeBot := by
  rintro F ⟨v, _, rfl⟩
  exact v.neBot

theorem coe_add_le (U V : Ultrafilter G) :
    ((U + V : Ultrafilter G) : Filter G) ≤ Filter.map₂ (· + ·) (U : Filter G) (V : Filter G) := by
  intro s hs
  obtain ⟨a, ha, b, hb, hab⟩ := Filter.mem_map₂_iff.1 hs
  show s ∈ U + V
  rw [mem_add]
  refine Filter.mem_of_superset ha (fun m hm => ?_)
  exact Filter.mem_of_superset hb (fun z hz => hab (mem_image2_of_mem hm hz))

theorem pw_mem (w : List (Ultrafilter G × ℤ)) (hw : ∀ x ∈ w, x.1 ∈ S) :
    (pw w : Filter G) ∈ genFam (ultraGen S) := by
  have hC : NullFamily (genFam (ultraGen S)) := genFam_nullFamily _
  induction w with
  | nil =>
    show ((pure 0 : Ultrafilter G) : Filter G) ∈ _
    rw [Ultrafilter.coe_pure]; exact hC.pure_zero
  | cons x w ih =>
    have h1 : (x.1.map (fun z : G => x.2 • z) : Filter G) ∈ genFam (ultraGen S) := by
      rw [Ultrafilter.coe_map]
      refine genFam_le hC ?_ (map_zsmul_mem (x.1 : Filter G) x.2)
      intro F hF
      rw [mem_singleton_iff.1 hF]
      exact subset_genFam (gen_ne S) ⟨x.1, hw x (List.mem_cons_self ..), rfl⟩
    have h2 := hC.add _ h1 _ (ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)))
    exact hC.finer _ h2 _ (coe_add_le _ _) (Ultrafilter.neBot _)

include htor hsel in
theorem pw_free (w : List (Ultrafilter G × ℤ)) (hw : Good S w) (hne : w ≠ []) : ∀ a, pw w ≠ pure a := by
  induction w with
  | nil => exact absurd rfl hne
  | cons x w ih =>
    intro a ha
    have hx := hw x (List.mem_cons_self ..)
    have hmem : ({a} : Set G) ∈ pw (x :: w) := by rw [ha]; exact rfl
    rw [mem_pw_cons] at hmem
    rcases eq_or_ne w [] with hw0 | hw0
    · subst hw0
      refine notMem_of_finite (hsel _ hx.1).1 ((finite_fibre htor x.2 hx.2 a).subset (fun b hb => ?_)) hmem
      have h1 : (0 : G) ∈ {z : G | x.2 • b + z ∈ ({a} : Set G)} := hb
      simpa using h1
    · obtain ⟨b, hb⟩ := Ultrafilter.nonempty_of_mem hmem
      have h1 : {z : G | x.2 • b + z ∈ ({a} : Set G)} ∈ pw w := hb
      refine ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) hw0 (a - x.2 • b) ?_
      have h2 : ({a - x.2 • b} : Set G) ∈ pw w := by
        refine Filter.mem_of_superset h1 (fun z hz => ?_)
        have h3 : x.2 • b + z = a := hz
        rw [mem_singleton_iff, ← h3]; abel
      obtain ⟨y, hy, h4⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_singleton _) h2
      rw [h4, mem_singleton_iff.1 hy]

/-- Every nonprincipal ultrafilter of the PG is the ultrafilter of a word. -/
theorem exists_word {S : Set (Ultrafilter G)} (hsel : ∀ u ∈ S, IsSel u) (hiso : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ Iso u v)
    (W : Ultrafilter G) (hW : (W : Filter G) ∈ genFam (ultraGen S)) (hfree : ∀ a, W ≠ pure a) :
    ∃ w, Good S w ∧ w ≠ [] ∧ pw w = W := by
  classical
  obtain ⟨e⟩ : Nonempty (ℕ ≃ G) := by
    have := Encodable.ofCountable G
    have := Denumerable.ofEncodableOfInfinite G
    exact ⟨(Denumerable.eqv G).symm⟩
  obtain ⟨σ, hσ, hWσ⟩ := hW.2 W le_rfl
  obtain ⟨ι, _, u, ε, hu, hε, hrep⟩ := rep_of_sumClosure S hσ
  -- an ultrafilter on tuples with the given marginals and sum
  let sm : (ι → G) → G := fun a => ∑ i, ε i • a i
  set F : Filter (ι → G) := Filter.pi (fun i => (u i : Filter G)) ⊓ Filter.comap sm (W : Filter G) with hF
  have hFne : F.NeBot := by
    rw [hF, Filter.inf_neBot_iff]
    intro s hs t ht
    obtain ⟨I, _, A, hA, hAs⟩ := Filter.mem_pi.1 hs
    obtain ⟨B, hB, hBt⟩ := Filter.mem_comap.1 ht
    let A' : ι → Set G := fun i => if i ∈ I then A i else univ
    have hA' : ∀ i, A' i ∈ u i := by
      intro i
      show (if i ∈ I then A i else univ) ∈ u i
      split_ifs
      · exact hA i
      · exact Filter.univ_mem
    have hT := hWσ (hrep A' hA')
    obtain ⟨z, hz1, hz2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (W : Filter G)) hT hB)
    obtain ⟨a, ha, hsum⟩ := hz1
    refine ⟨a, hAs (fun i hi => ?_), hBt ?_⟩
    · have := ha i
      simpa [A', hi] using this
    · show ∑ i, ε i • a i ∈ B
      rw [hsum]; exact hz2
  have := hFne
  set Z : Ultrafilter (ι → G) := Ultrafilter.of F with hZ
  have hZF : (Z : Filter (ι → G)) ≤ F := Ultrafilter.of_le F
  have hmarg : ∀ i, Z.map (fun a => a i) = u i := by
    intro i
    refine Ultrafilter.coe_le_coe.1 ?_
    rw [Ultrafilter.coe_map]
    exact (Filter.map_mono (hZF.trans (inf_le_left))).trans (Filter.tendsto_eval_pi _ i)
  have hsumZ : Z.map sm = W := by
    refine Ultrafilter.coe_le_coe.1 ?_
    rw [Ultrafilter.coe_map]
    exact (Filter.map_mono (hZF.trans inf_le_right)).trans Filter.map_comap_le
  have hι : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : Z.map sm = pure 0 := by
      have : sm = fun _ => (0 : G) := by
        funext a
        show ∑ i, ε i • a i = 0
        rw [Finset.univ_eq_empty, Finset.sum_empty]
      rw [this]
      refine Ultrafilter.coe_injective ?_
      rw [Ultrafilter.coe_map, Ultrafilter.coe_pure]
      exact Filter.map_const
    exact hfree 0 (hsumZ ▸ h1)
  -- the pattern of equalities and order
  let rk : (ι → G) → ι → Fin (Fintype.card ι) := fun a i =>
    ⟨((Finset.univ.image (fun j => e.symm (a j))).filter (fun z => z < e.symm (a i))).card, by
      have h1 : ((Finset.univ.image (fun j => e.symm (a j))).filter (fun z => z < e.symm (a i)))
          ⊂ Finset.univ.image (fun j => e.symm (a j)) :=
        Finset.filter_ssubset.2 ⟨e.symm (a i), Finset.mem_image_of_mem _ (Finset.mem_univ i), lt_irrefl _⟩
      exact lt_of_lt_of_le (Finset.card_lt_card h1) (Finset.card_image_le.trans Finset.card_univ.le)⟩
  have hrk_mono : ∀ a i j, e.symm (a i) < e.symm (a j) → rk a i < rk a j := by
    intro a i j h
    show (Finset.filter _ _).card < (Finset.filter _ _).card
    refine Finset.card_lt_card ⟨fun z hz => ?_, fun hsub => ?_⟩
    · rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hz.2.trans h⟩
    · have h1 : e.symm (a i) ∈ (Finset.univ.image (fun j => e.symm (a j))).filter (fun z => z < e.symm (a j)) :=
        Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), h⟩
      exact lt_irrefl _ (Finset.mem_filter.1 (hsub h1)).2
  have hrk_eq : ∀ a i j, rk a i = rk a j ↔ e.symm (a i) = e.symm (a j) := by
    intro a i j
    constructor
    · intro h
      rcases lt_trichotomy (e.symm (a i)) (e.symm (a j)) with h' | h' | h'
      · exact absurd h (hrk_mono a i j h').ne
      · exact h'
      · exact absurd h (hrk_mono a j i h').ne'
    · intro h
      apply Fin.ext
      show (Finset.filter _ _).card = (Finset.filter _ _).card
      rw [h]
  have hrk_lt : ∀ a i j, rk a i < rk a j ↔ e.symm (a i) < e.symm (a j) := by
    intro a i j
    refine ⟨fun h => ?_, hrk_mono a i j⟩
    rcases lt_trichotomy (e.symm (a i)) (e.symm (a j)) with h' | h' | h'
    · exact h'
    · exact absurd ((hrk_eq a i j).2 h') h.ne
    · exact absurd (hrk_mono a j i h') h.asymm
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ι → Fin (Fintype.card ι), {a | rk a = ρ} ∈ Z := by
    by_contra h
    have h1 : (⋂ ρ ∈ (Finset.univ : Finset (ι → Fin (Fintype.card ι))), {a : ι → G | rk a = ρ}ᶜ) ∈ (Z : Filter _) := by
      refine (Filter.biInter_finset_mem _).2 (fun ρ _ => ?_)
      rcases Z.mem_or_compl_mem {a | rk a = ρ} with h' | h'
      · exact absurd ⟨ρ, h'⟩ h
      · exact h'
    obtain ⟨a, ha⟩ := Ultrafilter.nonempty_of_mem h1
    exact mem_iInter₂.1 ha (rk a) (Finset.mem_univ _) rfl
  obtain ⟨a0, ha0⟩ := Ultrafilter.nonempty_of_mem hρ
  have ha0' : rk a0 = ρ := ha0
  -- the ranks that occur are the first `r` numbers
  set J : Finset (Fin (Fintype.card ι)) := Finset.univ.image ρ with hJ
  set r : ℕ := J.card with hr
  let ord : Fin r ≃o J := J.orderIsoOfFin rfl
  have hsec : ∀ l : Fin r, ∃ i, ρ i = (ord l).1 := by
    intro l
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 (ord l).2
    exact ⟨i, hi⟩
  choose s hs using hsec
  have hpos : ∀ i, ρ i ∈ J := fun i => Finset.mem_image_of_mem ρ (Finset.mem_univ i)
  let pos : ι → Fin r := fun i => ord.symm ⟨ρ i, hpos i⟩
  have hordpos : ∀ i, (ord (pos i)).1 = ρ i := by
    intro i
    show (ord (ord.symm ⟨ρ i, hpos i⟩)).1 = ρ i
    rw [OrderIso.apply_symm_apply]
  let z : (ι → G) → Fin r → ℕ := fun a l => e.symm (a (s l))
  have hz : ∀ a, rk a = ρ → ∀ i, e.symm (a i) = z a (pos i) := by
    intro a ha i
    refine (hrk_eq a i (s (pos i))).1 ?_
    rw [ha, hs, hordpos]
  have hzmono : ∀ a, rk a = ρ → StrictMono (z a) := by
    intro a ha l m hlm
    refine (hrk_lt a (s l) (s m)).1 ?_
    rw [ha, hs, hs]
    exact ord.strictMono hlm
  have hselmap : ∀ i, IsSel ((u i).map e.symm) := fun i =>
    isSel_map_of_injective (hsel _ (hu i)) e.symm e.symm.injective
  let v : Fin r → Ultrafilter ℕ := fun l => (u (s l)).map e.symm
  -- the image on increasing tuples is the ultrafilter of the large sets
  have hfub : ∀ R : Set (Fin r → ℕ), Large r v R → {a | z a ∈ R} ∈ Z := by
    intro R hR
    rcases Z.mem_or_compl_mem {a | z a ∈ R} with h | h
    · exact h
    exfalso
    set U : Finset (Ultrafilter ℕ) := Finset.univ.image v with hU
    let w : Fin U.card → Ultrafilter ℕ := fun k => (U.equivFin.symm k).1
    have hvU : ∀ l, v l ∈ U := fun l => Finset.mem_image_of_mem v (Finset.mem_univ l)
    let τ : Fin r → Fin U.card := fun l => U.equivFin ⟨v l, hvU l⟩
    have hwτ : ∀ l, w (τ l) = v l := by
      intro l
      show (U.equivFin.symm (U.equivFin ⟨v l, hvU l⟩)).1 = v l
      rw [Equiv.symm_apply_apply]
    have hwv : ∀ k, ∃ l, w k = v l := by
      intro k
      obtain ⟨l, _, hl⟩ := Finset.mem_image.1 (U.equivFin.symm k).2
      exact ⟨l, hl.symm⟩
    have hwsel : ∀ k, IsSel (w k) := by
      intro k
      obtain ⟨l, hl⟩ := hwv k
      rw [hl]; exact hselmap _
    have hwiso : ∀ k k', k ≠ k' → ¬ Iso (w k) (w k') := by
      rintro k k' hkk' ⟨π, hπ⟩
      obtain ⟨l, hl⟩ := hwv k
      obtain ⟨l', hl'⟩ := hwv k'
      have hne : w k ≠ w k' := fun h => hkk' (U.equivFin.symm.injective (Subtype.ext h))
      have huu : u (s l) ≠ u (s l') := by
        intro h
        refine hne ?_
        rw [hl, hl']
        show (u (s l)).map e.symm = (u (s l')).map e.symm
        rw [h]
      refine hiso _ (hu (s l)) _ (hu (s l')) huu ⟨(e.symm.trans π).trans e, ?_⟩
      have h1 : (v l).map π = v l' := by rw [← hl, ← hl']; exact hπ
      have h2 := congrArg (Ultrafilter.map e) h1
      simp only [v, Ultrafilter.map_map] at h2
      have h3 : (e : ℕ → G) ∘ (e.symm : G → ℕ) = id := by funext x; simp
      rw [h3, Ultrafilter.map_id] at h2
      exact h2
    have hnl : ¬ Large r (fun l => w (τ l)) Rᶜ := by
      have : (fun l => w (τ l)) = v := funext hwτ
      rw [this, large_compl]
      exact not_not.2 hR
    obtain ⟨B, hB, hav⟩ := tuples w hwsel hwiso r τ Rᶜ hnl
    have hmargB : ∀ l, {a : ι → G | z a l ∈ B (τ l)} ∈ Z := by
      intro l
      have h1 : B (τ l) ∈ v l := by rw [← hwτ l]; exact hB (τ l)
      have h2 : e.symm ⁻¹' B (τ l) ∈ u (s l) := h1
      rw [← hmarg (s l)] at h2
      exact h2
    have hall : (⋂ l ∈ (Finset.univ : Finset (Fin r)), {a : ι → G | z a l ∈ B (τ l)}) ∈ (Z : Filter _) :=
      (Filter.biInter_finset_mem _).2 (fun l _ => hmargB l)
    have h12 : {a | rk a = ρ} ∩ {a | z a ∈ R}ᶜ ∈ (Z : Filter _) := Filter.inter_mem hρ h
    obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h12 hall)
    exact hav (z a) (hzmono a ha1) (fun l => mem_iInter₂.1 ha3 l (Finset.mem_univ l)) ha2
  -- the sum collected over equal coordinates
  let c : Fin r → ℤ := fun l => ∑ i ∈ Finset.univ.filter (fun i => pos i = l), ε i
  have hcollect : ∀ a, rk a = ρ → sm a = ∑ l, c l • e (z a l) := by
    intro a ha
    show ∑ i, ε i • a i = ∑ l, (∑ i ∈ Finset.univ.filter (fun i => pos i = l), ε i) • e (z a l)
    rw [← Finset.sum_fiberwise Finset.univ pos (fun i => ε i • a i)]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have h1 : pos i = l := (Finset.mem_filter.1 hi).2
    have h2 := hz a ha i
    rw [h1] at h2
    rw [← h2, Equiv.apply_symm_apply]
  set word : List (Ultrafilter G × ℤ) := List.ofFn (fun l => (u (s l), c l)) with hword
  have hpw : pw word = W := by
    refine (Ultrafilter.coe_le_coe.1 (fun A hA => ?_)).symm
    have h1 := (mem_pw_ofFn e r (fun l => u (s l)) c A).1 hA
    have h2 := hfub _ h1
    have h3 : sm ⁻¹' A ∈ Z := by
      refine Filter.mem_of_superset (Filter.inter_mem hρ h2) (fun a ha => ?_)
      show sm a ∈ A
      rw [hcollect a ha.1]
      exact ha.2
    show A ∈ W
    rw [← hsumZ]
    exact h3
  refine ⟨word.filter (fun x => decide (x.2 ≠ 0)), fun x hx => ?_, fun h0 => ?_, ?_⟩
  · obtain ⟨hx1, hx2⟩ := List.mem_filter.1 hx
    refine ⟨?_, by simpa using hx2⟩
    rw [hword, List.mem_ofFn] at hx1
    obtain ⟨l, hl⟩ := hx1
    rw [← hl]
    exact hu _
  · have h1 := pw_filter word
    rw [h0, hpw] at h1
    exact hfree 0 h1.symm
  · rw [pw_filter, hpw]

include htor hsel in
/-- Theorem 6.1, existence: the nonprincipal ultrafilters of the PG are exactly the ultrafilters of nonempty words. -/
theorem null_free_iff (hiso : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ Iso u v) (W : Ultrafilter G) :
    ((W : Filter G) ∈ genFam (ultraGen S) ∧ ∀ a, W ≠ pure a) ↔ ∃ w, Good S w ∧ w ≠ [] ∧ pw w = W := by
  constructor
  · rintro ⟨hW, hfree⟩
    exact exists_word hsel hiso W hW hfree
  · rintro ⟨w, hw, hne, rfl⟩
    exact ⟨pw_mem S w (fun x hx => (hw x hx).1), pw_free htor S hsel w hw hne⟩

include htor hsel hiso in
/-- Theorem 6.1, uniqueness: different words give different ultrafilters. -/
theorem pw_injective (w w' : List (Ultrafilter G × ℤ)) (hw : Good S w) (hw' : Good S w') (h : pw w = pw w') :
    w = w' := by
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
  -- a bound for the coefficients and the lengths
  set n : ℕ := ((w ++ w').map (fun x => x.2.natAbs)).sum with hn
  have hbound : ∀ x ∈ w ++ w', x.2.natAbs ≤ n := fun x hx =>
    List.le_sum_of_mem (List.mem_map.2 ⟨x, hx, rfl⟩)
  set L : ℕ := w.length + w'.length with hL
  set D : Finset ℤ := (Finset.Icc (-(2 * (n : ℤ))) (2 * (n : ℤ))).filter (fun d => d ≠ 0) with hD
  -- members avoiding all short relations
  have hrel : ∀ m : ℕ, ∀ σ : Fin (m + 1) → Fin U.card, ∀ d : Fin (m + 1) → ℤ, (∀ l, d l ≠ 0) →
      ∃ B : Fin U.card → Set ℕ, (∀ k, B k ∈ om k) ∧
        ∀ y : Fin (m + 1) → ℕ, StrictMono y → (∀ i, y i ∈ B (σ i)) → ∑ l, d l • e (y l) ≠ 0 := by
    intro m σ d hd
    have hfin : FinLast {y : Fin (m + 1) → ℕ | ∑ l, d l • e (y l) = 0} := by
      intro p
      have h1 : {x : G | d (Fin.last m) • x = -∑ l : Fin m, d l.castSucc • e (p l)}.Finite :=
        finite_fibre htor _ (hd _) _
      refine (h1.preimage e.injective.injOn).subset (fun x hx => ?_)
      have h2 : ∑ l, d l • e ((Fin.snoc p x : Fin (m + 1) → ℕ) l) = 0 := hx
      rw [Fin.sum_univ_castSucc] at h2
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at h2
      show d (Fin.last m) • e x = -∑ l : Fin m, d l.castSucc • e (p l)
      exact eq_neg_of_add_eq_zero_right h2
    have hnl := not_large_of_finLast m (fun i => om (σ i)) (fun i => (homsel (σ i)).1) _ hfin
    obtain ⟨B, hB, hav⟩ := tuples om homsel homiso (m + 1) σ _ hnl
    exact ⟨B, hB, hav⟩
  have hrel' : ∀ k : Fin U.card, ∃ C ∈ om k, ∀ m < L, ∀ σ : Fin (m + 1) → Fin U.card, ∀ d : Fin (m + 1) → ℤ,
      (∀ l, d l ∈ D) → ∀ B : Fin U.card → Set ℕ,
        (∀ hd : ∀ l, d l ≠ 0, B = Classical.choose (hrel m σ d hd)) → (∀ l, d l ≠ 0) → C ⊆ B k := by
    intro k
    have h1 : ∀ m : ℕ, (⋂ σ ∈ (Finset.univ : Finset (Fin (m + 1) → Fin U.card)),
        ⋂ d ∈ Fintype.piFinset (fun _ : Fin (m + 1) => D),
          (if hd : ∀ l, d l ≠ 0 then Classical.choose (hrel m σ d hd) k else univ)) ∈ (om k : Filter ℕ) := by
      intro m
      refine (Filter.biInter_finset_mem _).2 (fun σ _ => (Filter.biInter_finset_mem _).2 (fun d _ => ?_))
      split_ifs with hd
      · exact (Classical.choose_spec (hrel m σ d hd)).1 k
      · exact Filter.univ_mem
    refine ⟨_, (Filter.biInter_finset_mem (Finset.range L)).2 (fun m _ => h1 m), ?_⟩
    intro m hm σ d hdD B hB hd x hx
    have h2 := mem_iInter₂.1 hx m (Finset.mem_range.2 hm)
    have h3 := mem_iInter₂.1 (mem_iInter₂.1 h2 σ (Finset.mem_univ σ)) d (Fintype.mem_piFinset.2 hdD)
    rw [dif_pos hd] at h3
    rw [hB hd]
    exact h3
  choose C1 hC1mem hC1 using hrel'
  -- pairwise disjoint members
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
  let C : Fin U.card → Set ℕ := fun k => C1 k ∩ C2 k
  have hCmem : ∀ k, C k ∈ om k := fun k => Filter.inter_mem (hC1mem k) (hC2mem k)
  -- indices of the letters
  let ix : (x : Ultrafilter G) → x ∈ U → Fin U.card := fun x hx => U.equivFin ⟨x, hx⟩
  have huix : ∀ x (hx : x ∈ U), uu (ix x hx) = x := by
    intro x hx
    show (U.equivFin.symm (U.equivFin ⟨x, hx⟩)).1 = x
    rw [Equiv.symm_apply_apply]
  let κ : Fin w.length → Fin U.card := fun i => ix (w.get i).1 (hwU _ (List.get_mem _ _))
  let κ' : Fin w'.length → Fin U.card := fun i => ix (w'.get i).1 (hw'U _ (List.get_mem _ _))
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
  have hE : E ∈ pw w := hmemE w κ (fun i => huix _ _)
  have hE' : E' ∈ pw w' := hmemE w' κ' (fun i => huix _ _)
  rw [← h] at hE'
  obtain ⟨x, hxE, hxE'⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (f := (pw w : Filter G)) hE hE')
  obtain ⟨z, hzm, hzC, hzx⟩ := hxE
  obtain ⟨z', hzm', hzC', hzx'⟩ := hxE'
  -- collect equal points
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
  have hdsmall : ∀ y, |d y| ≤ 2 * (n : ℤ) := by
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
    have h1 := one w (fun x hx => List.mem_append_left _ hx) z hzm.injective
    have h2 := one w' (fun x hx => List.mem_append_right _ hx) z' hzm'.injective
    have h3 := abs_sub (∑ i ∈ Finset.univ.filter (fun i => z i = y), cf i)
      (∑ i ∈ Finset.univ.filter (fun i => z' i = y), cf' i)
    show |(∑ i ∈ Finset.univ.filter (fun i => z i = y), cf i)
      - ∑ i ∈ Finset.univ.filter (fun i => z' i = y), cf' i| ≤ 2 * (n : ℤ)
    have h4 : |∑ i ∈ Finset.univ.filter (fun i => z i = y), cf i| ≤ (n : ℤ) := h1
    have h5 : |∑ i ∈ Finset.univ.filter (fun i => z' i = y), cf' i| ≤ (n : ℤ) := h2
    omega
  have hdzero : ∀ y ∈ Y, d y = 0 := by
    by_contra hcon
    set T : Finset ℕ := Y.filter (fun y => d y ≠ 0) with hT
    have hTne : T.Nonempty := by
      by_contra he
      refine hcon (fun y hy => ?_)
      by_contra h'
      exact he ⟨y, Finset.mem_filter.2 ⟨hy, h'⟩⟩
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
    have hty : ∀ l, ∃ k, t l ∈ C k := by
      intro l
      have h1 := (Finset.mem_filter.1 (htmem l)).1
      rcases Finset.mem_union.1 h1 with h2 | h2
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h2
        exact ⟨κ i, hi ▸ hzC i⟩
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h2
        exact ⟨κ' i, hi ▸ hzC' i⟩
    choose σ hσ using hty
    let dd : Fin (m + 1) → ℤ := fun l => d (t l)
    have hdd : ∀ l, dd l ≠ 0 := fun l => (Finset.mem_filter.1 (htmem l)).2
    have hddD : ∀ l, dd l ∈ D := fun l =>
      Finset.mem_filter.2 ⟨Finset.mem_Icc.2 (abs_le.1 (hdsmall _)), hdd l⟩
    set B := Classical.choose (hrel m σ dd hdd) with hB
    have hsub : ∀ l, t l ∈ B (σ l) := by
      intro l
      exact hC1 (σ l) m hmL σ dd hddD B (fun _ => rfl) hdd (hσ l).1
    have hav := (Classical.choose_spec (hrel m σ dd hdd)).2 t htm hsub
    refine hav ?_
    have himg : Finset.univ.image t = T := T.image_orderEmbOfFin_univ hm
    have h1 : ∑ l, dd l • e (t l) = ∑ y ∈ T, d y • e y := by
      rw [← himg, Finset.sum_image (fun a _ b _ hab => htm.injective hab)]
    rw [h1]
    have h2 : ∑ y ∈ T, d y • e y = ∑ y ∈ Y, d y • e y := by
      refine Finset.sum_filter_of_ne (fun y _ hne h0 => hne ?_)
      rw [h0, zero_smul]
    rw [h2, hsum]
  -- the two representations coincide
  have hcf : ∀ i, cf i ≠ 0 := fun i => (hw _ (List.get_mem w i)).2
  have hcf' : ∀ i, cf' i ≠ 0 := fun i => (hw' _ (List.get_mem w' i)).2
  have hmatch : ∀ i, ∃ j, z' j = z i ∧ cf' j = cf i := by
    intro i
    have h1 := hdzero (z i) (Finset.mem_union_left _ (Finset.mem_image_of_mem z (Finset.mem_univ i)))
    have h2 : cf i - ∑ j ∈ Finset.univ.filter (fun j => z' j = z i), cf' j = 0 := by
      have h3 : (∑ j ∈ Finset.univ.filter (fun j => z j = z i), cf j)
          - ∑ j ∈ Finset.univ.filter (fun j => z' j = z i), cf' j = 0 := h1
      rwa [hsingle, Finset.sum_singleton] at h3
    by_cases hex : ∃ j, z' j = z i
    · obtain ⟨j, hj⟩ := hex
      rw [← hj, hsingle', Finset.sum_singleton] at h2
      exact ⟨j, hj, by omega⟩
    · have h4 : Finset.univ.filter (fun j => z' j = z i) = ∅ :=
        Finset.filter_eq_empty_iff.2 (fun j _ h => hex ⟨j, h⟩)
      rw [h4, Finset.sum_empty, sub_zero] at h2
      exact absurd h2 (hcf i)
  have hmatch' : ∀ j, ∃ i, z i = z' j := by
    intro j
    have h1 := hdzero (z' j) (Finset.mem_union_right _ (Finset.mem_image_of_mem z' (Finset.mem_univ j)))
    by_contra hex
    have h4 : Finset.univ.filter (fun i => z i = z' j) = ∅ :=
      Finset.filter_eq_empty_iff.2 (fun i _ h => hex ⟨i, h⟩)
    have h3 : (∑ i ∈ Finset.univ.filter (fun i => z i = z' j), cf i)
        - ∑ i ∈ Finset.univ.filter (fun i => z' i = z' j), cf' i = 0 := h1
    rw [h4, hsingle', Finset.sum_empty, Finset.sum_singleton, zero_sub, neg_eq_zero] at h3
    exact hcf' j h3
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
  refine List.ext_get hlen (fun i h1 h2 => ?_)
  have hi : Fin.cast hlen ⟨i, h1⟩ = ⟨i, h2⟩ := rfl
  have hzi := hzz ⟨i, h1⟩
  rw [hi] at hzi
  have hcoef : cf ⟨i, h1⟩ = cf' ⟨i, h2⟩ := by
    obtain ⟨j, hj, hc⟩ := hmatch ⟨i, h1⟩
    have : j = ⟨i, h2⟩ := hzm'.injective (hj.trans hzi)
    rw [this] at hc
    exact hc.symm
  have hult : (w.get ⟨i, h1⟩).1 = (w'.get ⟨i, h2⟩).1 := by
    have h3 := (hzC ⟨i, h1⟩).2
    have h4 := (hzC' ⟨i, h2⟩).2
    rw [← hzi] at h4
    have h5 := hC2 _ _ _ h3 h4
    have h6 := congrArg uu h5
    rwa [show uu (κ ⟨i, h1⟩) = (w.get ⟨i, h1⟩).1 from huix _ _,
      show uu (κ' ⟨i, h2⟩) = (w'.get ⟨i, h2⟩).1 from huix _ _] at h6
  exact Prod.ext hult hcoef

/-! ### The coreflection -/

include htor hsel hiso in
/-- Theorem 6.2, for every family, whatever its size: the only neighbourhood filter of a group topology among the null
filters is `pure 0`; and the vicinity filter is not null when the family is nonempty. -/
theorem only_trivial :
    (∀ N : Filter G, IsNbhdFilter N → N ∈ genFam (ultraGen S) → N = pure 0) ∧
      (S.Nonempty → vic (genFam (ultraGen S)) ∉ genFam (ultraGen S)) := by
  classical
  set C := genFam (ultraGen S) with hCdef
  have hC : NullFamily C := genFam_nullFamily _
  have main : ∀ N : Filter G, IsNbhdFilter N → N ∈ C → N = pure 0 := by
    intro N hN hNC
    by_contra hne0
    have h0N : pure 0 ≤ N := fun s hs => Filter.mem_pure.2 (hN.zero_mem s hs)
    -- the nonprincipal ultrafilters finer than `N` form a compact semigroup
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
      have h3 := genFam_hausdorff htor S hsel hiso a h1
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
    have hword : ∀ U ∈ X, ∃ w, Good S w ∧ w ≠ [] ∧ pw w = U := fun U hU =>
      exists_word hsel hiso U (hC.finer _ hNC _ hU.1 U.neBot) hU.2
    have hgood : ∀ w w' : List (Ultrafilter G × ℤ), Good S w → Good S w' → Good S (w ++ w') := by
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
        exact pw_free htor S hsel _ (hgood w w' hw hw') (fun h => hwne (List.append_eq_nil_iff.1 h).1)
    obtain ⟨p, hpX, hpp⟩ := exists_idempotent_in_compact_add_subsemigroup
      (M := Ultrafilter G) Ultrafilter.continuous_add_left X hXne hXclosed.isCompact hXadd
    obtain ⟨w, hw, hwne, hpw⟩ := hword p hpX
    have h1 : pw (w ++ w) = pw w := by rw [pw_append, hpw, hpp]
    have h2 := congrArg List.length (pw_injective htor S hsel hiso _ _ (hgood w w hw hw) hw h1)
    rw [List.length_append] at h2
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

include htor hsel hiso in
/-- Theorem 6.2: every continuous homomorphism from a topological group into the PG has an open kernel. -/
theorem kernel_open {T : Type} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] (f : T →+ G)
    (hf : XiCont (genFam (ultraGen S)) f) : ∃ U ∈ 𝓝 (0 : T), ∀ x ∈ U, f x = 0 :=
  kernel_open_of_trivial (genFam_nullFamily _) (only_trivial htor S hsel hiso).1 f hf

/-- Corollary 6.3: under (S) there is a Hausdorff PG whose vicinity filter is the cofinite filter at `0`, whose finest
group topology is indiscrete, and whose only neighbourhood filter of a group topology among the null filters is
`pure 0`. -/
theorem exists_discrete_coreflection (htor : ∀ m : ℕ, 0 < m → {x : G | m • x = 0}.Finite) (hS : Supply) :
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
  have hhaus := genFam_hausdorff htor S hselS hisoS
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
  refine ⟨_, hC, hhaus, hvic, ?_, (only_trivial htor S hselS hisoS).1⟩
  -- the finest group topology is indiscrete
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

end PG
