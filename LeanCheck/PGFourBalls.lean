import Mathlib
import LeanCheck.PGFourStrict

/-!
# PGfour: the balls of a family of members of the generators

`g 0, g 1, …` lists the countably infinite group `G`, and `E i ∈ s i`. The ball `Ball g E k` consists of the sums of at
most `k` terms, each `±e` with `e ∈ E i`, `i ≤ k`, or `±g j` with `j ≤ k`.

* `strict_of_balls` : if for some family no ball is a vicinity set, then some vicinity set contains no open set;
* `pretop_of_uniform` : if one radius `k` gives a vicinity set for every family, then every ultrafilter in the closure
  of the null ultrafilters is null.

In both the vicinity sets are assumed to separate points.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology Pointwise

namespace PG

namespace Strict

variable {G : Type} [AddCommGroup G]

/-- The sums of at most `n` letters, each `±g j` with `j ≤ k`. -/
def Zs (g : ℕ → G) (k : ℕ) : ℕ → Set G
  | 0 => {0}
  | n + 1 => Zs g k n + (insert 0 (g '' Iic k ∪ (fun x => -x) '' (g '' Iic k)))

/-- The sums of `a` letters `±g j`, `j ≤ k`, and of `b` letters from the members with indices `≤ k`, `a + b ≤ k`. -/
def Ball (g : ℕ → G) (E : ℕ → Set G) (k : ℕ) : Set G :=
  {x | ∃ a, ∃ z ∈ Zs g k a, ∃ w : List (Bool × ℕ), a + w.length ≤ k ∧ (∀ c ∈ w, c.2 ≤ k) ∧
    ∃ y ∈ Sg E w, x = z + y}

theorem Zs_finite (g : ℕ → G) (k : ℕ) : ∀ n, (Zs g k n).Finite
  | 0 => finite_singleton 0
  | n + 1 => (Zs_finite g k n).add (Finite.insert 0 ((((finite_Iic k).image g)).union
      (((finite_Iic k).image g).image _)))

theorem Zs_mono {g : ℕ → G} {k k' : ℕ} (h : k ≤ k') : ∀ n, Zs g k n ⊆ Zs g k' n
  | 0 => subset_rfl
  | n + 1 => add_subset_add (Zs_mono h n) (insert_subset_insert (union_subset_union
      (image_mono (Iic_subset_Iic.2 h)) (image_mono (image_mono (Iic_subset_Iic.2 h)))))

theorem Zs_add (g : ℕ → G) (k : ℕ) : ∀ (a b : ℕ), ∀ x ∈ Zs g k a, ∀ y ∈ Zs g k b, x + y ∈ Zs g k (a + b)
  | a, 0, x, hx, y, hy => by
    show x + y ∈ Zs g k a
    rw [mem_singleton_iff.1 hy, add_zero]
    exact hx
  | a, b + 1, x, hx, _, ⟨y, hy, l, hl, rfl⟩ => by
    show x + (y + l) ∈ Zs g k (a + b + 1)
    rw [← add_assoc]
    exact add_mem_add (Zs_add g k a b x hx y hy) hl

theorem Zs_neg (g : ℕ → G) (k : ℕ) : ∀ n, ∀ x ∈ Zs g k n, -x ∈ Zs g k n
  | 0, x, hx => by
    rw [mem_singleton_iff.1 hx, neg_zero]
    exact rfl
  | n + 1, _, ⟨y, hy, l, hl, rfl⟩ => by
    show -(y + l) ∈ Zs g k (n + 1)
    rw [neg_add]
    refine add_mem_add (Zs_neg g k n y hy) ?_
    rcases mem_insert_iff.1 hl with h | h
    · rw [h, neg_zero]
      exact mem_insert _ _
    · refine mem_insert_of_mem _ ?_
      rcases h with h | ⟨m, hm, rfl⟩
      · exact Or.inr ⟨l, h, rfl⟩
      · rw [neg_neg]
        exact Or.inl hm

theorem Sg_append (E : ℕ → Set G) : ∀ w w' : List (Bool × ℕ), ∀ x ∈ Sg E w, ∀ y ∈ Sg E w', x + y ∈ Sg E (w ++ w')
  | [], w', x, hx, y, hy => by
    rw [mem_singleton_iff.1 hx, zero_add]
    exact hy
  | c :: w, w', _, ⟨a, ha, t, ht, rfl⟩, y, hy => by
    show a + t + y ∈ Sg E (c :: (w ++ w'))
    rw [add_assoc]
    exact ⟨a, ha, t + y, Sg_append E w w' t ht y hy, rfl⟩

theorem Sg_neg (E : ℕ → Set G) : ∀ w : List (Bool × ℕ), ∀ x ∈ Sg E w, -x ∈ Sg E (w.map (fun c => (!c.1, c.2)))
  | [], x, hx => by
    rw [mem_singleton_iff.1 hx, neg_zero]
    exact rfl
  | c :: w, _, ⟨a, ha, t, ht, rfl⟩ => by
    show -(a + t) ∈ Sg E ((!c.1, c.2) :: w.map (fun c => (!c.1, c.2)))
    rw [neg_add]
    refine ⟨-a, ?_, -t, Sg_neg E w t ht, rfl⟩
    by_cases h : c.1
    · simp only [h, if_true] at ha
      simp only [h, Bool.not_true, Bool.false_eq_true, if_false]
      show -(-a) ∈ E c.2
      rwa [neg_neg]
    · simp only [h, Bool.false_eq_true, if_false] at ha
      simp only [h, Bool.not_false, if_true]
      exact ha

theorem zero_mem_Ball (g : ℕ → G) (E : ℕ → Set G) (k : ℕ) : (0 : G) ∈ Ball g E k :=
  ⟨0, 0, rfl, [], Nat.zero_le _, fun c hc => absurd hc List.not_mem_nil, 0, rfl, (add_zero 0).symm⟩

theorem Ball_neg (g : ℕ → G) (E : ℕ → Set G) (k : ℕ) : ∀ x ∈ Ball g E k, -x ∈ Ball g E k := by
  rintro _ ⟨a, z, hz, w, hl, hi, y, hy, rfl⟩
  refine ⟨a, -z, Zs_neg g k a z hz, w.map (fun c => (!c.1, c.2)), by rwa [List.length_map], fun c hc => ?_,
    -y, Sg_neg E w y hy, by rw [neg_add]⟩
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact hi d hd

theorem Ball_add (g : ℕ → G) (E : ℕ → Set G) (k l : ℕ) :
    ∀ x ∈ Ball g E k, ∀ y ∈ Ball g E l, x + y ∈ Ball g E (k + l) := by
  rintro _ ⟨a, z, hz, w, hl, hi, y, hy, rfl⟩ _ ⟨a', z', hz', w', hl', hi', y', hy', rfl⟩
  refine ⟨a + a', z + z', Zs_add g (k + l) a a' z (Zs_mono (Nat.le_add_right _ _) _ hz) z'
    (Zs_mono (Nat.le_add_left _ _) _ hz'), w ++ w', by rw [List.length_append]; omega, fun c hc => ?_,
    y + y', Sg_append E w w' y hy y' hy', by abel⟩
  rcases List.mem_append.1 hc with h | h
  · exact le_trans (hi c h) (Nat.le_add_right _ _)
  · exact le_trans (hi' c h) (Nat.le_add_left _ _)

theorem mem_Ball_gen (g : ℕ → G) (E : ℕ → Set G) (i : ℕ) : E i ⊆ Ball g E (i + 1) := by
  intro x hx
  refine ⟨0, 0, rfl, [(true, i)], by simp, fun c hc => ?_, x, ⟨x, hx, 0, rfl, add_zero x⟩, (zero_add x).symm⟩
  rw [List.mem_singleton.1 hc]
  exact Nat.le_succ i

theorem mem_Ball_pt (g : ℕ → G) (E : ℕ → Set G) (j : ℕ) : g j ∈ Ball g E (j + 1) := by
  refine ⟨1, g j, ⟨0, rfl, g j, ?_, zero_add _⟩, [], by simp, fun c hc => absurd hc List.not_mem_nil, 0, rfl,
    (add_zero _).symm⟩
  exact mem_insert_of_mem _ (Or.inl ⟨j, Nat.le_succ j, rfl⟩)

/-- If for some family no ball is a vicinity set, some vicinity set contains no open set. -/
theorem strict_of_balls [Countable G] [Infinite G] (s : ℕ → Ultrafilter G) (g : ℕ → G) (hg : Function.Surjective g)
    (E : ℕ → Set G) (hE : ∀ i, E i ∈ s i) (hunb : ∀ k, ¬ Vic s (Ball g E k))
    (hsep : ∀ x : G, x ≠ 0 → ∃ A, Vic s A ∧ ∀ a ∈ A, x + a ∉ A) :
    ∃ A, Vic s A ∧ (∀ x : G, x ≠ 0 → ¬ Vic s {y | x + y ∈ A}) ∧
      ∀ O, IsOpenMod' s O → (0 : G) ∈ O → ¬ O ⊆ A := by
  classical
  have hmono : ∀ k l, k ≤ l → Ball g E k ⊆ Ball g E l := by
    intro k l h x hx
    have h1 := Ball_add g E k (l - k) x hx 0 (zero_mem_Ball g E _)
    rwa [add_zero, Nat.add_sub_cancel' h] at h1
  have hcov : ∀ x : G, ∃ k, x ∈ Ball g E k := by
    intro x
    obtain ⟨j, rfl⟩ := hg x
    exact ⟨j + 1, mem_Ball_pt g E j⟩
  set len : G → ℕ := fun x => Nat.find (hcov x) with hlen
  have hspec : ∀ x, x ∈ Ball g E (len x) := fun x => Nat.find_spec (hcov x)
  have hle : ∀ x k, x ∈ Ball g E k → len x ≤ k := fun x k h => Nat.find_min' (hcov x) h
  have hball : ∀ k, {x | len x ≤ k} = Ball g E k := by
    intro k
    ext x
    exact ⟨fun h => hmono _ _ h (hspec x), fun h => hle x k h⟩
  refine strict_of_length s len ?_ (fun x => ?_) (fun x y => ?_) (fun i => ?_) (fun k => ?_) hsep
  · exact Nat.le_zero.1 (hle 0 0 (zero_mem_Ball g E 0))
  · refine le_antisymm (hle _ _ (Ball_neg g E _ x (hspec x))) (hle _ _ ?_)
    have h := Ball_neg g E _ (-x) (hspec (-x))
    rwa [neg_neg] at h
  · exact hle _ _ (Ball_add g E _ _ x (hspec x) y (hspec y))
  · refine ⟨i + 1, ?_⟩
    rw [hball]
    exact Filter.mem_of_superset (hE i) (mem_Ball_gen g E i)
  · rw [hball]
    exact hunb k

/-- If one radius gives a vicinity set for every family, the PG is pretopological: every ultrafilter finer than the
vicinity filter is null. -/
theorem pretop_of_uniform (s : ℕ → Ultrafilter G) (g : ℕ → G) (k : ℕ)
    (hk : ∀ E : ℕ → Set G, (∀ i, E i ∈ s i) → Vic s (Ball g E k))
    (hsep : ∀ x : G, x ≠ 0 → ∃ A, Vic s A ∧ ∀ a ∈ A, x + a ∉ A)
    (p : Ultrafilter G) (hp : ∀ A, Vic s A → A ∈ p) : Null s p := by
  classical
  set Zk : Set G := ⋃ a ∈ Iic k, Zs g k a with hZk
  have hZfin : Zk.Finite := (finite_Iic k).biUnion (fun a _ => Zs_finite g k a)
  set T : Set (G × List (Bool × ℕ)) := Zk ×ˢ (words k k : Set (List (Bool × ℕ))) with hT
  have hTfin : T.Finite := hZfin.prod (words k k).finite_toSet
  -- one translate of one filter sum serves all families
  have hone : ∃ t ∈ T, ∀ E : ℕ → Set G, (∀ i, E i ∈ s i) → (fun y => t.1 + y) '' Sg E t.2 ∈ p := by
    by_contra hno
    push Not at hno
    choose! Et hEt hEp using hno
    set E : ℕ → Set G := fun i => ⋂ t ∈ T, Et t i with hE
    have hEs : ∀ i, E i ∈ s i := fun i => (biInter_mem hTfin).2 (fun t ht => hEt t ht i)
    have h1 : Ball g E k ∈ p := hp _ (hk E hEs)
    have h2 : Ball g E k ⊆ ⋃ t ∈ T, (fun y => t.1 + y) '' Sg E t.2 := by
      rintro x ⟨a, z, hz, w, hl, hi, y, hy, rfl⟩
      refine mem_biUnion (x := (z, w)) ⟨?_, ?_⟩ ⟨y, hy, rfl⟩
      · exact mem_biUnion (x := a) (show a ≤ k by omega) hz
      · exact (mem_words k k w).2 ⟨by omega, hi⟩
    obtain ⟨t, ht, h3⟩ := (Ultrafilter.finite_biUnion_mem_iff hTfin).1 (Filter.mem_of_superset h1 h2)
    refine hEp t ht (Filter.mem_of_superset h3 (image_mono (Sg_mono (fun i => ?_) _)))
    exact biInter_subset_of_mem ht
  obtain ⟨t, _, ht⟩ := hone
  set q : Ultrafilter G := p.map (fun y => -t.1 + y) with hq
  have hqnull : Null s q := by
    refine ⟨t.2, fun C hC => ?_⟩
    obtain ⟨E, hE, hsub⟩ := (mem_sig s t.2 C).1 hC
    refine Ultrafilter.mem_map.2 (Filter.mem_of_superset (ht E hE) ?_)
    rintro _ ⟨y, hy, rfl⟩
    show -t.1 + (t.1 + y) ∈ C
    rw [neg_add_cancel_left]
    exact hsub hy
  have hz : t.1 = 0 := by
    by_contra h
    obtain ⟨A, hA, hd⟩ := hsep t.1 h
    have h1 : {y | -t.1 + y ∈ A} ∈ p := Ultrafilter.mem_map.1 (hA q hqnull)
    obtain ⟨y, hy1, hy2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h1 (hp A hA))
    have h2 := hd _ hy1
    rw [add_neg_cancel_left] at h2
    exact h2 hy2
  have e : q = p := by
    have : (fun y : G => -t.1 + y) = id := funext (fun y => by rw [hz, neg_zero, zero_add]; rfl)
    rw [hq, this, Ultrafilter.map_id]
  rwa [e] at hqnull

end Strict

end PG
