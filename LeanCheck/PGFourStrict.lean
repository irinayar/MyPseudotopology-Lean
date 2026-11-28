import Mathlib
import LeanCheck.PGThreeBohr
import LeanCheck.PGTwoQuotient

/-!
# PGfour: when the neighbourhoods of the modification are not the whole vicinity filter

`s 0, s 1, …` are ultrafilters on a countably infinite abelian group `G`, `PG` the pseudotopological group they
generate. `Null q` says that the ultrafilter `q` converges to `0`, and `Vic A` that `A` belongs to every such `q`.
It is assumed that the sets of `Vic` separate points: for `x ≠ 0` some `A` with `Vic A` is disjoint from `x + A`.

* `null_iff_genFam` : `Null` is convergence to `0` in the generated PG;
* `strict_of_escape` : if some `p` in the closure of the null ultrafilters has, for every filter sum, a member of the
  sum of which no translate meets `p` in the sense below, then some `A` with `Vic A` has `A - x` not vicinity for every
  `x ≠ 0`, and contains no set which contains `0` and is open for the topological modification;
* `strict_of_ppoints` : this applies when every `s i` is a P-point or principal and the PG is not pretopological;
* `strict_of_length` : and when each `s i` has a member of bounded length and no ball is a vicinity set.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology Pointwise

namespace PG

namespace Strict

variable {G : Type} [AddCommGroup G]

/-! ### The filter sums as words -/

/-- The letter `(b, i)` stands for `s i` if `b` and for `-s i` if not. -/
def letter (s : ℕ → Ultrafilter G) (c : Bool × ℕ) : Filter G :=
  if c.1 then (s c.2 : Filter G) else Filter.map (fun x : G => -x) (s c.2 : Filter G)

/-- The filter sum of a word. -/
def sig (s : ℕ → Ultrafilter G) : List (Bool × ℕ) → Filter G
  | [] => pure 0
  | c :: w => Filter.map₂ (· + ·) (letter s c) (sig s w)

/-- The set of the sums along a word, the letters taken in the sets `E i`. -/
def Sg (E : ℕ → Set G) : List (Bool × ℕ) → Set G
  | [] => {0}
  | c :: w => Set.image2 (· + ·) (if c.1 then E c.2 else (fun x : G => -x) ⁻¹' E c.2) (Sg E w)

theorem Sg_mono {E F : ℕ → Set G} (h : ∀ i, E i ⊆ F i) : ∀ w, Sg E w ⊆ Sg F w
  | [] => subset_rfl
  | c :: w => by
    refine image2_subset ?_ (Sg_mono h w)
    split_ifs
    · exact h _
    · exact preimage_mono (h _)

theorem map_neg_eq_comap (F : Filter G) :
    Filter.map (fun x : G => -x) F = Filter.comap (fun x : G => -x) F := by
  refine Filter.map_eq_comap_of_inverse ?_ ?_ <;>
  · funext x
    simp

theorem mem_letter (s : ℕ → Ultrafilter G) (c : Bool × ℕ) (A : Set G) :
    A ∈ letter s c ↔ ∃ E ∈ s c.2, (if c.1 then E else (fun x : G => -x) ⁻¹' E) ⊆ A := by
  unfold letter
  by_cases h : c.1
  · simp only [h, if_true]
    exact ⟨fun hA => ⟨A, hA, subset_rfl⟩, fun ⟨E, hE, hsub⟩ => Filter.mem_of_superset hE hsub⟩
  · simp only [h, Bool.false_eq_true, if_false]
    rw [map_neg_eq_comap]
    constructor
    · rintro ⟨E, hE, hsub⟩
      exact ⟨E, hE, hsub⟩
    · rintro ⟨E, hE, hsub⟩
      exact ⟨E, hE, hsub⟩

/-- The sets `Sg E w` form a base of the filter sum. -/
theorem mem_sig (s : ℕ → Ultrafilter G) : ∀ (w : List (Bool × ℕ)) (A : Set G),
    A ∈ sig s w ↔ ∃ E : ℕ → Set G, (∀ i, E i ∈ s i) ∧ Sg E w ⊆ A
  | [], A => by
    constructor
    · intro h
      refine ⟨fun _ => univ, fun _ => Filter.univ_mem, fun x hx => ?_⟩
      rw [show x = 0 from hx]
      exact (show A ∈ (pure 0 : Filter G) from h)
    · rintro ⟨E, _, h⟩
      show A ∈ (pure 0 : Filter G)
      exact h (show (0 : G) ∈ Sg E [] from rfl)
  | c :: w, A => by
    constructor
    · intro h
      obtain ⟨t1, h1, t2, h2, h⟩ := Filter.mem_map₂_iff.1 h
      obtain ⟨F, hF, hFt⟩ := (mem_letter s c t1).1 h1
      obtain ⟨E, hE, hEt⟩ := (mem_sig s w t2).1 h2
      refine ⟨fun i => if i = c.2 then E i ∩ F else E i, fun i => ?_, ?_⟩
      · show (if i = c.2 then E i ∩ F else E i) ∈ s i
        split_ifs with hi
        · subst hi
          exact Filter.inter_mem (hE _) hF
        · exact hE i
      · refine Subset.trans (image2_subset ?_ ?_) h
        · refine Subset.trans ?_ hFt
          have hsub : (if c.2 = c.2 then E c.2 ∩ F else E c.2) ⊆ F := by
            rw [if_pos rfl]
            exact inter_subset_right
          split_ifs
          all_goals first
            | exact inter_subset_right
            | exact preimage_mono inter_subset_right
            | exact hsub
            | exact preimage_mono hsub
        · refine Subset.trans (Sg_mono (fun i => ?_) w) hEt
          split_ifs
          · exact inter_subset_left
          · exact subset_rfl
    · rintro ⟨E, hE, h⟩
      refine Filter.mem_map₂_iff.2 ⟨_, (mem_letter s c _).2 ⟨E c.2, hE _, subset_rfl⟩, Sg E w,
        (mem_sig s w _).2 ⟨E, hE, subset_rfl⟩, h⟩

theorem sig_sumClosure (s : ℕ → Ultrafilter G) :
    ∀ w, SumClosure (Sel.ultraGen (range s)) (sig s w)
  | [] => SumClosure.zero
  | c :: w => by
    refine SumClosure.add ?_ (sig_sumClosure s w)
    have hg : SumClosure (Sel.ultraGen (range s)) (s c.2 : Filter G) :=
      SumClosure.gen ⟨s c.2, mem_range_self _, rfl⟩
    unfold letter
    split_ifs
    · exact hg
    · exact sumClosure_neg hg

theorem map₂_pure_zero (F : Filter G) : Filter.map₂ (· + ·) (pure 0) F = F := by
  rw [Filter.map₂_pure_left]
  have : (fun b : G => (0 : G) + b) = id := funext (fun b => zero_add b)
  rw [this, Filter.map_id]

theorem sig_append (s : ℕ → Ultrafilter G) : ∀ w w' : List (Bool × ℕ),
    sig s (w ++ w') = Filter.map₂ (· + ·) (sig s w) (sig s w')
  | [], w' => (map₂_pure_zero _).symm
  | c :: w, w' => by
    show Filter.map₂ (· + ·) (letter s c) (sig s (w ++ w'))
      = Filter.map₂ (· + ·) (Filter.map₂ (· + ·) (letter s c) (sig s w)) (sig s w')
    rw [sig_append s w w']
    exact (Filter.map₂_assoc (fun a b c => (add_assoc a b c))).symm

theorem sig_neg (s : ℕ → Ultrafilter G) : ∀ w : List (Bool × ℕ),
    Filter.map (fun x : G => -x) (sig s w) = sig s (w.map (fun c => (!c.1, c.2)))
  | [] => by
    show Filter.map (fun x : G => -x) (pure 0) = pure 0
    rw [Filter.map_pure, neg_zero]
  | c :: w => by
    show Filter.map (fun x : G => -x) (Filter.map₂ (· + ·) (letter s c) (sig s w))
      = Filter.map₂ (· + ·) (letter s (!c.1, c.2)) (sig s (w.map (fun c => (!c.1, c.2))))
    have hl : Filter.map (fun x : G => -x) (letter s c) = letter s (!c.1, c.2) := by
      unfold letter
      by_cases h : c.1
      · simp [h]
      · simp only [h, Bool.false_eq_true, if_false, Bool.not_false, if_true]
        rw [Filter.map_map]
        have : ((fun x : G => -x) ∘ fun x : G => -x) = id := funext (fun x => neg_neg x)
        rw [this, Filter.map_id]
    rw [← hl, ← sig_neg s w, Filter.map_map₂, Filter.map₂_map_left, Filter.map₂_map_right]
    congr 1
    funext a b
    exact neg_add a b

/-- Every filter of the sum closure is the filter sum of a word. -/
theorem sumClosure_eq_sig (s : ℕ → Ultrafilter G) {σ : Filter G} (h : SumClosure (Sel.ultraGen (range s)) σ) :
    ∃ w, σ = sig s w := by
  induction h with
  | zero => exact ⟨[], rfl⟩
  | gen hF =>
    obtain ⟨u, ⟨i, rfl⟩, rfl⟩ := hF
    refine ⟨[(true, i)], ?_⟩
    show (s i : Filter G) = Filter.map₂ (· + ·) (s i : Filter G) (pure 0)
    rw [Filter.map₂_pure_right]
    have : (fun a : G => a + (0 : G)) = id := funext (fun a => add_zero a)
    rw [this, Filter.map_id]
  | neg hF =>
    rename_i F
    obtain ⟨u, ⟨i, rfl⟩, rfl⟩ := hF
    refine ⟨[(false, i)], ?_⟩
    show Filter.map (fun x : G => -x) (s i : Filter G)
      = Filter.map₂ (· + ·) (Filter.map (fun x : G => -x) (s i : Filter G)) (pure 0)
    rw [Filter.map₂_pure_right]
    have : (fun a : G => a + (0 : G)) = id := funext (fun a => add_zero a)
    rw [this, Filter.map_id]
  | add _ _ ih1 ih2 =>
    obtain ⟨w1, h1⟩ := ih1
    obtain ⟨w2, h2⟩ := ih2
    exact ⟨w1 ++ w2, by rw [h1, h2, sig_append]⟩

/-! ### Null ultrafilters and vicinity sets -/

/-- The ultrafilter `q` converges to `0`. -/
def Null (s : ℕ → Ultrafilter G) (q : Ultrafilter G) : Prop := ∃ w, (q : Filter G) ≤ sig s w

/-- `A` belongs to every ultrafilter that converges to `0`. -/
def Vic (s : ℕ → Ultrafilter G) (A : Set G) : Prop := ∀ q, Null s q → A ∈ q

/-- Convergence to `0` in the generated PG. -/
theorem null_iff_genFam (s : ℕ → Ultrafilter G) (q : Ultrafilter G) :
    Null s q ↔ (q : Filter G) ∈ genFam (Sel.ultraGen (range s)) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨q.neBot, fun U hU => ⟨sig s w, sig_sumClosure s w, hU.trans hw⟩⟩
  · intro h
    obtain ⟨σ, hσ, hq⟩ := h.2 q le_rfl
    obtain ⟨w, rfl⟩ := sumClosure_eq_sig s hσ
    exact ⟨w, hq⟩

theorem null_zero (s : ℕ → Ultrafilter G) : Null s (pure 0) :=
  ⟨[], by rw [Ultrafilter.coe_pure]; exact le_rfl⟩

/-- The topological modification: `O` is open. -/
def IsOpenMod' (s : ℕ → Ultrafilter G) (O : Set G) : Prop := ∀ y ∈ O, Vic s {z | y + z ∈ O}

/-- The same open sets as in the topological modification of the generated PG. -/
theorem isOpenMod'_iff (s : ℕ → Ultrafilter G) (O : Set G) :
    IsOpenMod' s O ↔ IsOpenMod (genFam (Sel.ultraGen (range s))) O := by
  constructor
  · intro h x hx F _ hF
    refine Filter.mem_iff_ultrafilter.2 (fun U hU => ?_)
    have h1 : (U.map (fun y => y - x) : Filter G) ≤ Filter.map (fun y => y - x) F := Filter.map_mono hU
    have h2 : Null s (U.map (fun y => y - x)) := by
      rw [null_iff_genFam]
      exact (genFam_nullFamily _).finer _ hF _ h1 (U.map (fun y => y - x)).neBot
    have h3 : {z | x + z ∈ O} ∈ U.map (fun y => y - x) := h x hx _ h2
    refine Filter.mem_of_superset (Ultrafilter.mem_map.1 h3) (fun y hy => ?_)
    have h4 : x + (y - x) ∈ O := hy
    rwa [add_sub_cancel] at h4
  · intro h y hy q hq
    have e : Filter.map (fun z => z - y) (Filter.map (fun z => y + z) (q : Filter G)) = (q : Filter G) := by
      rw [Filter.map_map]
      have : ((fun z : G => z - y) ∘ fun z => y + z) = id := funext (fun z => add_sub_cancel_left y z)
      rw [this, Filter.map_id]
    have h1 : conv (genFam (Sel.ultraGen (range s))) (Filter.map (fun z => y + z) (q : Filter G)) y := by
      unfold conv
      rw [e]
      exact (null_iff_genFam s q).1 hq
    have h2 := h y hy _ (Filter.NeBot.map q.neBot _) h1
    exact Filter.mem_map.1 h2

/-! ### The criterion -/

theorem strict_of_escape [Countable G] [Infinite G] (s : ℕ → Ultrafilter G)
    (hsep : ∀ x : G, x ≠ 0 → ∃ A, Vic s A ∧ ∀ a ∈ A, x + a ∉ A)
    (p : Ultrafilter G) (hp : ∀ A, Vic s A → A ∈ p)
    (hesc : ∀ w, ∃ C ∈ sig s w, ∀ x : G, {y | x + y ∈ C} ∉ p) :
    ∃ A, Vic s A ∧ (∀ x : G, x ≠ 0 → ¬ Vic s {y | x + y ∈ A}) ∧
      ∀ O, IsOpenMod' s O → (0 : G) ∈ O → ¬ O ⊆ A := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat (List (Bool × ℕ))
  obtain ⟨x, hx⟩ := exists_surjective_nat G
  choose C hC hCp using hesc
  have hsepk : ∀ k, x k ≠ 0 → ∃ A, Vic s A ∧ ∀ a ∈ A, x k + a ∉ A := fun k hk => hsep (x k) hk
  choose! D hD hDd using hsepk
  set B : ℕ → Set G := fun k => {z | x k ≠ 0 ∧ z - x k ∈ D k ∧ ∀ n ≤ k, z ∉ C (e n)} with hB
  set A : Set G := (⋃ k, B k)ᶜ with hA
  have hAvic : Vic s A := by
    rintro q ⟨w, hw⟩
    obtain ⟨n, rfl⟩ := he w
    have h1 : C (e n) ∈ q := hw (hC (e n))
    have h2 : (⋂ k ∈ Finset.range n, {z | x k ≠ 0 → z ∈ D k}) ∈ q := by
      refine (biInter_finset_mem _).2 (fun k _ => ?_)
      by_cases hk : x k = 0
      · exact Filter.univ_mem' (fun z h => absurd hk h)
      · exact Filter.mem_of_superset (hD k hk q ⟨e n, hw⟩) (fun z hz _ => hz)
    refine Filter.mem_of_superset (Filter.inter_mem h1 h2) (fun z hz => ?_)
    rw [hA, mem_compl_iff, mem_iUnion]
    rintro ⟨k, hk0, hkD, hkC⟩
    by_cases hkn : k < n
    · have h3 : z ∈ D k := (mem_iInter₂.1 hz.2 k (Finset.mem_range.2 hkn)) hk0
      have h4 := hDd k hk0 _ hkD
      rw [add_sub_cancel] at h4
      exact h4 h3
    · exact hkC n (not_lt.1 hkn) hz.1
  have hshift : ∀ y : G, y ≠ 0 → ¬ Vic s {z | y + z ∈ A} := by
    intro y hy hvic
    obtain ⟨k, rfl⟩ := hx y
    have h1 : {z | x k + z ∈ B k} ∈ p := by
      have h2 : D k ∈ p := hp _ (hD k hy)
      have h3 : (⋂ n ∈ Finset.range (k + 1), {z | x k + z ∈ C (e n)}ᶜ) ∈ p :=
        (biInter_finset_mem _).2 (fun n _ => Ultrafilter.compl_mem_iff_notMem.2 (hCp (e n) (x k)))
      refine Filter.mem_of_superset (Filter.inter_mem h2 h3) (fun z hz => ?_)
      refine ⟨hy, ?_, fun n hn => ?_⟩
      · rw [add_sub_cancel_left]
        exact hz.1
      · exact mem_iInter₂.1 hz.2 n (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
    have h4 : {z | x k + z ∈ A} ∈ p := hp _ hvic
    obtain ⟨z, hz1, hz2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h1 h4)
    exact hz2 (mem_iUnion.2 ⟨k, hz1⟩)
  refine ⟨A, hAvic, hshift, fun O hO h0 hOA => ?_⟩
  have hOvic : Vic s O := by
    have h := hO 0 h0
    simpa using h
  have hsmall : ∀ y ∈ O, y = 0 := by
    intro y hy
    by_contra hy0
    exact hshift y hy0 (fun q hq => Filter.mem_of_superset (hO y hy q hq) (fun z hz => hOA hz))
  have h1 : ({0} : Set G) ∈ p := Filter.mem_of_superset (hp O hOvic) (fun y hy => hsmall y hy)
  have hp0 : (p : Filter G) ≤ pure 0 := by
    rw [le_pure_iff]
    exact h1
  have h2 : C [] ∈ (pure 0 : Filter G) := hC []
  have h3 : {y | 0 + y ∈ C []} ∈ p := by
    refine Filter.mem_of_superset h1 (fun y hy => ?_)
    rw [mem_singleton_iff.1 hy]
    show (0 : G) + 0 ∈ C []
    rw [add_zero]
    exact h2
  exact hCp [] 0 h3

/-- An ultrafilter in the closure of the null ultrafilters that is not one of them has no translate that is one, and is
not principal. -/
theorem translate_not_null (s : ℕ → Ultrafilter G) (hsep : ∀ x : G, x ≠ 0 → ∃ A, Vic s A ∧ ∀ a ∈ A, x + a ∉ A)
    (p : Ultrafilter G) (hp : ∀ A, Vic s A → A ∈ p) (hpn : ¬ Null s p) (z : G) :
    ¬ Null s (p.map (fun y => z + y)) ∧ {y | z + y = 0} ∉ p := by
  have h1 : ∀ z : G, ¬ Null s (p.map (fun y => z + y)) := by
    intro z hz
    by_cases h : z = 0
    · have e : p.map (fun y => z + y) = p := by
        have : (fun y : G => z + y) = id := funext (fun y => by rw [h, zero_add]; rfl)
        rw [this, Ultrafilter.map_id]
      rw [e] at hz
      exact hpn hz
    · obtain ⟨A, hA, hd⟩ := hsep z h
      have h2 : {y | z + y ∈ A} ∈ p := Ultrafilter.mem_map.1 (hA _ hz)
      obtain ⟨y, hy1, hy2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h2 (hp A hA))
      exact hd y hy2 hy1
  refine ⟨h1 z, fun h => h1 z ?_⟩
  have e : p.map (fun y => z + y) = pure 0 := by
    refine Ultrafilter.coe_le_coe.1 ?_
    rw [Ultrafilter.coe_pure, le_pure_iff]
    exact Ultrafilter.mem_map.2 (Filter.mem_of_superset h (fun y hy => hy))
  rw [e]
  exact null_zero s

/-! ### P-points -/

/-- The words of length at most `n` with indices at most `N`. -/
def words (N : ℕ) : ℕ → Finset (List (Bool × ℕ))
  | 0 => {[]}
  | n + 1 => insert [] (((Finset.univ ×ˢ Finset.range (N + 1)) ×ˢ words N n).image (fun r => r.1 :: r.2))

theorem mem_words (N : ℕ) : ∀ (n : ℕ) (w : List (Bool × ℕ)),
    w ∈ words N n ↔ w.length ≤ n ∧ ∀ c ∈ w, c.2 ≤ N
  | 0, w => by
    rw [words, Finset.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h, _⟩
      exact List.eq_nil_of_length_eq_zero (Nat.le_zero.1 h)
  | n + 1, w => by
    rw [words, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (rfl | ⟨⟨c, w'⟩, h, rfl⟩)
      · simp
      · rw [Finset.mem_product, Finset.mem_product] at h
        have h' := (mem_words N n w').1 h.2
        refine ⟨Nat.succ_le_succ h'.1, fun d hd => ?_⟩
        rcases List.mem_cons.1 hd with hd | hd
        · rw [hd]
          exact Nat.lt_succ_iff.1 (Finset.mem_range.1 h.1.2)
        · exact h'.2 d hd
    · rintro ⟨h1, h2⟩
      cases w with
      | nil => exact Or.inl rfl
      | cons c w' =>
        refine Or.inr ⟨(c, w'), ?_, rfl⟩
        rw [Finset.mem_product, Finset.mem_product]
        refine ⟨⟨Finset.mem_univ _, Finset.mem_range.2 (Nat.lt_succ_of_le (h2 c List.mem_cons_self))⟩,
          (mem_words N n w').2 ⟨Nat.le_of_succ_le_succ h1, fun d hd => h2 d (List.mem_cons_of_mem _ hd)⟩⟩

def Dn (E : ℕ → Set G) (N n : ℕ) : Set G := ⋃ w ∈ words N n, Sg E w

/-- Removing one letter whose point is exceptional. -/
theorem Sg_split (E F : ℕ → Set G) (N : ℕ) (R : Set G)
    (hR : ∀ i ≤ N, ∀ a ∈ F i, a ∉ E i → a ∈ R ∧ -a ∈ R) :
    ∀ w : List (Bool × ℕ), (∀ c ∈ w, c.2 ≤ N) → ∀ x ∈ Sg F w,
      x ∈ Sg E w ∨ ∃ r ∈ R, ∃ w' : List (Bool × ℕ), w'.length + 1 = w.length ∧ (∀ c ∈ w', c.2 ≤ N) ∧
        x - r ∈ Sg F w'
  | [], _, x, hx => Or.inl hx
  | c :: w, hw, x, hx => by
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    have hcN : c.2 ≤ N := hw c List.mem_cons_self
    have hwN : ∀ d ∈ w, d.2 ≤ N := fun d hd => hw d (List.mem_cons_of_mem _ hd)
    by_cases haE : a ∈ (if c.1 then E c.2 else (fun x : G => -x) ⁻¹' E c.2)
    · rcases Sg_split E F N R hR w hwN t ht with h | ⟨r, hr, w', hl, hN', h⟩
      · exact Or.inl ⟨a, haE, t, h, rfl⟩
      · refine Or.inr ⟨r, hr, c :: w', by rw [List.length_cons, List.length_cons, hl], fun d hd => ?_,
          a, ha, t - r, h, by dsimp only; abel⟩
        rcases List.mem_cons.1 hd with hd | hd
        · rw [hd]
          exact hcN
        · exact hN' d hd
    · refine Or.inr ⟨a, ?_, w, (List.length_cons).symm, hwN, ?_⟩
      · by_cases h : c.1
        · simp only [h, if_true] at ha haE
          exact (hR _ hcN a ha haE).1
        · simp only [h, Bool.false_eq_true, if_false] at ha haE
          have := (hR _ hcN (-a) ha haE).2
          rwa [neg_neg] at this
      · rw [add_sub_cancel_left]
        exact ht

theorem escape_of_ppoints [Countable G] (s : ℕ → Ultrafilter G)
    (hpp : ∀ i, ∀ E : ℕ → Set G, (∀ n, E n ∈ s i) → ∃ F ∈ s i, ∀ n, (F \ E n).Finite)
    (hsep : ∀ x : G, x ≠ 0 → ∃ A, Vic s A ∧ ∀ a ∈ A, x + a ∉ A)
    (p : Ultrafilter G) (hp : ∀ A, Vic s A → A ∈ p) (hpn : ¬ Null s p) :
    ∀ w, ∃ C ∈ sig s w, ∀ x : G, {y | x + y ∈ C} ∉ p := by
  classical
  -- for one triple there is a family
  have hone : ∀ t : ℕ × ℕ × G, ∃ E : ℕ → Set G, (∀ i, E i ∈ s i) ∧ {y | t.2.2 + y ∈ Dn E t.1 t.2.1} ∉ p := by
    rintro ⟨N, n, z⟩
    have hq := (translate_not_null s hsep p hp hpn z).1
    have hw : ∀ w : List (Bool × ℕ), ∃ E : ℕ → Set G, (∀ i, E i ∈ s i) ∧ Sg E w ∉ p.map (fun y => z + y) := by
      intro w
      have h1 : ¬ ((p.map (fun y => z + y) : Ultrafilter G) : Filter G) ≤ sig s w := fun h => hq ⟨w, h⟩
      obtain ⟨C, hC, hCq⟩ := Set.not_subset.1 h1
      obtain ⟨E, hE, hsub⟩ := (mem_sig s w C).1 hC
      exact ⟨E, hE, fun h => hCq (Filter.mem_of_superset h hsub)⟩
    choose Ew hEw hEwq using hw
    refine ⟨fun i => ⋂ w ∈ words N n, Ew w i, fun i => (biInter_finset_mem _).2 (fun w _ => hEw w i), ?_⟩
    intro h
    have h1 : Dn (fun i => ⋂ w ∈ words N n, Ew w i) N n ∈ p.map (fun y => z + y) := Ultrafilter.mem_map.2 h
    unfold Dn at h1
    obtain ⟨w, hw, h2⟩ := (Ultrafilter.finite_biUnion_mem_iff (words N n).finite_toSet).1 h1
    refine hEwq w (Filter.mem_of_superset h2 (Sg_mono (fun i => ?_) w))
    exact biInter_subset_of_mem (Finset.mem_coe.1 hw)
  choose E hE hEp using hone
  obtain ⟨en, hen⟩ := exists_surjective_nat (ℕ × ℕ × G)
  have hF : ∀ i, ∃ F ∈ s i, ∀ n, (F \ E (en n) i).Finite := fun i =>
    hpp i (fun n => E (en n) i) (fun n => hE (en n) i)
  choose F hF hFfin using hF
  have hfin : ∀ t i, (F i \ E t i).Finite := by
    intro t i
    obtain ⟨n, rfl⟩ := hen t
    exact hFfin i n
  have hmain : ∀ N n (z : G), {y | z + y ∈ Dn F N n} ∉ p := by
    intro N n
    induction n with
    | zero =>
      intro z h
      refine (translate_not_null s hsep p hp hpn z).2 (Filter.mem_of_superset h (fun y hy => ?_))
      unfold Dn at hy
      rw [mem_ofPred_eq, mem_iUnion₂] at hy
      obtain ⟨w, hw, hy⟩ := hy
      rw [words, Finset.mem_singleton] at hw
      subst hw
      exact hy
    | succ n ih =>
      intro z h
      set t : ℕ × ℕ × G := (N, n + 1, z) with ht
      set R : Set G := (⋃ i ∈ Finset.range (N + 1), (F i \ E t i)) with hR
      have hRfin : R.Finite := (Finset.range (N + 1)).finite_toSet.biUnion (fun i _ => hfin t i)
      set R' : Set G := R ∪ (fun x : G => -x) '' R with hR'
      have hR'fin : R'.Finite := hRfin.union (hRfin.image _)
      have hsub : {y | z + y ∈ Dn F N (n + 1)} ⊆
          {y | z + y ∈ Dn (E t) N (n + 1)} ∪ ⋃ r ∈ R', {y | (z - r) + y ∈ Dn F N n} := by
        intro y hy
        unfold Dn at hy
        rw [mem_ofPred_eq, mem_iUnion₂] at hy
        obtain ⟨w, hw, hy⟩ := hy
        obtain ⟨hwl, hwN⟩ := (mem_words N (n + 1) w).1 hw
        have hsplit := Sg_split (E t) F N R' (fun i hi a haF haE => by
          have h1 : a ∈ R := mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) ⟨haF, haE⟩
          exact ⟨Or.inl h1, Or.inr ⟨a, h1, rfl⟩⟩) w hwN _ hy
        rcases hsplit with h1 | ⟨r, hr, w', hl, hN', h1⟩
        · refine Or.inl ?_
          show z + y ∈ Dn (E t) N (n + 1)
          exact mem_biUnion hw h1
        · refine Or.inr (mem_iUnion₂.2 ⟨r, hr, ?_⟩)
          show (z - r) + y ∈ Dn F N n
          have e : (z - r) + y = z + y - r := by abel
          rw [e]
          exact mem_biUnion ((mem_words N n w').2 ⟨by omega, hN'⟩) h1
      have h2 := Filter.mem_of_superset h hsub
      rcases Ultrafilter.union_mem_iff.1 h2 with h3 | h3
      · exact hEp t h3
      · obtain ⟨r, _, h4⟩ := (Ultrafilter.finite_biUnion_mem_iff hR'fin).1 h3
        exact ih (z - r) h4
  intro w
  set N : ℕ := (w.map Prod.snd).sum with hN
  refine ⟨Sg F w, (mem_sig s w _).2 ⟨F, hF, subset_rfl⟩, fun x h => ?_⟩
  refine hmain N w.length x (Filter.mem_of_superset h (fun y hy => ?_))
  show x + y ∈ Dn F N w.length
  refine mem_biUnion ((mem_words N w.length w).2 ⟨le_rfl, fun c hc => ?_⟩) hy
  exact List.le_sum_of_mem (List.mem_map_of_mem hc)

/-- For P-points and principal ultrafilters: a PG that is not pretopological has a vicinity set with no open set. -/
theorem strict_of_ppoints [Countable G] [Infinite G] (s : ℕ → Ultrafilter G)
    (hpp : ∀ i, ∀ E : ℕ → Set G, (∀ n, E n ∈ s i) → ∃ F ∈ s i, ∀ n, (F \ E n).Finite)
    (hsep : ∀ x : G, x ≠ 0 → ∃ A, Vic s A ∧ ∀ a ∈ A, x + a ∉ A)
    (hnp : ∃ p : Ultrafilter G, (∀ A, Vic s A → A ∈ p) ∧ ¬ Null s p) :
    ∃ A, Vic s A ∧ (∀ x : G, x ≠ 0 → ¬ Vic s {y | x + y ∈ A}) ∧
      ∀ O, IsOpenMod' s O → (0 : G) ∈ O → ¬ O ⊆ A := by
  obtain ⟨p, hp, hpn⟩ := hnp
  exact strict_of_escape s hsep p hp (escape_of_ppoints s hpp hsep p hp hpn)

/-! ### Bounded length -/

/-- Each generator has a member of bounded length, and no ball is a vicinity set. -/
theorem strict_of_length [Countable G] [Infinite G] (s : ℕ → Ultrafilter G) (len : G → ℕ) (h0 : len 0 = 0)
    (hneg : ∀ x, len (-x) = len x) (hadd : ∀ x y, len (x + y) ≤ len x + len y)
    (hs : ∀ i, ∃ k, {x | len x ≤ k} ∈ s i) (hunb : ∀ k, ¬ Vic s {x | len x ≤ k})
    (hsep : ∀ x : G, x ≠ 0 → ∃ A, Vic s A ∧ ∀ a ∈ A, x + a ∉ A) :
    ∃ A, Vic s A ∧ (∀ x : G, x ≠ 0 → ¬ Vic s {y | x + y ∈ A}) ∧
      ∀ O, IsOpenMod' s O → (0 : G) ∈ O → ¬ O ⊆ A := by
  classical
  set V : Filter G := ⨆ q ∈ {q : Ultrafilter G | Null s q}, (q : Filter G) with hV
  have hmemV : ∀ A, A ∈ V ↔ Vic s A := by
    intro A
    rw [hV]
    simp only [Filter.mem_iSup]
    exact ⟨fun h q hq => h q hq, fun h q hq => h q hq⟩
  have hne : ∀ k, (V ⊓ 𝓟 {x | len x ≤ k}ᶜ).NeBot := by
    intro k
    refine ⟨fun h => hunb k ?_⟩
    have h1 := Filter.inf_principal_eq_bot.1 h
    rw [compl_compl] at h1
    exact (hmemV _).1 h1
  have hdir : Directed (· ≥ ·) (fun k => V ⊓ 𝓟 {x | len x ≤ k}ᶜ) :=
    Antitone.directed_ge (fun a b hab => inf_le_inf_left _ (principal_mono.2 (compl_subset_compl.2
      (fun x (hx : len x ≤ a) => le_trans hx hab))))
  have hinf : (⨅ k, V ⊓ 𝓟 {x | len x ≤ k}ᶜ).NeBot := iInf_neBot_of_directed' hdir hne
  set p : Ultrafilter G := Ultrafilter.of (⨅ k, V ⊓ 𝓟 {x | len x ≤ k}ᶜ) with hpdef
  have hple : ∀ k, (p : Filter G) ≤ V ⊓ 𝓟 {x | len x ≤ k}ᶜ := fun k =>
    (Ultrafilter.of_le _).trans (iInf_le _ k)
  have hp : ∀ A, Vic s A → A ∈ p := fun A hA => (hple 0).trans inf_le_left ((hmemV A).2 hA)
  have hpk : ∀ k, {x | len x ≤ k} ∉ p := by
    intro k h
    have h1 : {x | len x ≤ k}ᶜ ∈ p := (hple k).trans inf_le_right (mem_principal_self _)
    exact Ultrafilter.compl_mem_iff_notMem.1 h1 h
  have hball : ∀ w, ∃ m, {x | len x ≤ m} ∈ sig s w := by
    intro w
    induction w with
    | nil =>
      refine ⟨0, ?_⟩
      show len 0 ≤ 0
      rw [h0]
    | cons c w ih =>
      obtain ⟨m, hm⟩ := ih
      obtain ⟨k, hk⟩ := hs c.2
      refine ⟨k + m, Filter.mem_map₂_iff.2 ⟨_, (mem_letter s c _).2 ⟨_, hk, subset_rfl⟩, _, hm, ?_⟩⟩
      rintro _ ⟨a, ha, b, hb, rfl⟩
      have hak : len a ≤ k := by
        by_cases h : c.1
        · simp only [h, if_true] at ha
          exact ha
        · simp only [h, Bool.false_eq_true, if_false] at ha
          have h1 : len (-a) ≤ k := ha
          rwa [hneg] at h1
      exact le_trans (hadd a b) (Nat.add_le_add hak hb)
  refine strict_of_escape s hsep p hp (fun w => ?_)
  obtain ⟨m, hm⟩ := hball w
  refine ⟨_, hm, fun x h => hpk (m + len x) (Filter.mem_of_superset h (fun y hy => ?_))⟩
  have h1 : len (x + y) ≤ m := hy
  have h2 := hadd (x + y) (-x)
  have e : x + y + -x = y := by abel
  rw [e, hneg] at h2
  show len y ≤ m + len x
  omega

end Strict

end PG
