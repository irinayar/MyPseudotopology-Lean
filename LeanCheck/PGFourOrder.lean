import Mathlib
import LeanCheck.PGFourClassify
import LeanCheck.PGFourFinite

/-!
# PGfour: the classification theorems with the summation order of the article

`sumL` of `PGFourClassify` takes the last entry of the list outermost. The article writes `u = c₁ y(v₁) + ... + cₛ y(vₛ)`
with `A ∈ p + q` iff `{x | {z | x + z ∈ A} ∈ q} ∈ p`, so that the first summand is outermost. Addition of ultrafilters is
not commutative, so the two are matched here.

* `psum` : the sum with the first entry outermost; `psum_eq` : `psum l = sumL y l.reverse`;
* `classification_psum`, `classification_family_psum` : the two classification theorems for `psum`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

namespace Order

open Sums PPoint Classify FiniteFam

variable (y : ℕ → ℤ)

/-- The sum `c₁ y(v₁) + ... + cₛ y(vₛ)`, the first summand outermost. -/
noncomputable def psum : List (ℤ × Ultrafilter ℕ) → Ultrafilter ℤ
  | [] => pure 0
  | p :: l => p.2.bind (fun n => (psum l).map (fun z => p.1 * y n + z))

theorem mem_psum_cons (p : ℤ × Ultrafilter ℕ) (l : List (ℤ × Ultrafilter ℕ)) (A : Set ℤ) :
    A ∈ psum y (p :: l) ↔ {n | {z : ℤ | p.1 * y n + z ∈ A} ∈ psum y l} ∈ p.2 := Iff.rfl

/-- Appending an entry to `sumL` puts it outermost. -/
theorem mem_sumL_append (p : ℤ × Ultrafilter ℕ) (m : List (ℤ × Ultrafilter ℕ)) (A : Set ℤ) :
    A ∈ sumL y (m ++ [p]) ↔ {n | {z : ℤ | p.1 * y n + z ∈ A} ∈ sumL y m} ∈ p.2 := by
  induction m generalizing A with
  | nil =>
    rw [List.nil_append, mem_sumL_cons]
    have h1 : sumL y ([] : List (ℤ × Ultrafilter ℕ)) = pure 0 := rfl
    rw [h1, Ultrafilter.mem_pure]
    have e1 : (0 : ℤ) ∈ {z : ℤ | {n | z + p.1 * y n ∈ A} ∈ p.2} ↔ {n | p.1 * y n ∈ A} ∈ p.2 := by
      show {n | (0 : ℤ) + p.1 * y n ∈ A} ∈ p.2 ↔ _
      simp only [zero_add]
    have e2 : {n : ℕ | {z : ℤ | p.1 * y n + z ∈ A} ∈ (pure 0 : Ultrafilter ℤ)} = {n | p.1 * y n ∈ A} := by
      ext n
      show p.1 * y n + 0 ∈ A ↔ p.1 * y n ∈ A
      rw [add_zero]
    rw [e1, e2]
  | cons q m ih =>
    rw [List.cons_append, mem_sumL_cons, ih]
    have e : ∀ n : ℕ, {z : ℤ | p.1 * y n + z ∈ {x : ℤ | {k | x + q.1 * y k ∈ A} ∈ q.2}}
        = {x : ℤ | {k | x + q.1 * y k ∈ {z : ℤ | p.1 * y n + z ∈ A}} ∈ q.2} := by
      intro n
      ext x
      show {k | p.1 * y n + x + q.1 * y k ∈ A} ∈ q.2 ↔ {k | p.1 * y n + (x + q.1 * y k) ∈ A} ∈ q.2
      simp only [add_assoc]
    constructor
    · intro h
      refine Filter.mem_of_superset h fun n hn => ?_
      change _ ∈ sumL y m at hn
      show {z : ℤ | p.1 * y n + z ∈ A} ∈ sumL y (q :: m)
      rw [mem_sumL_cons, ← e n]
      exact hn
    · intro h
      refine Filter.mem_of_superset h fun n hn => ?_
      change _ ∈ sumL y (q :: m) at hn
      rw [mem_sumL_cons, ← e n] at hn
      exact hn

theorem psum_eq (l : List (ℤ × Ultrafilter ℕ)) : psum y l = sumL y l.reverse := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    apply Ultrafilter.ext
    intro A
    rw [mem_psum_cons, List.reverse_cons, mem_sumL_append, ih]

theorem S_reverse (w : Ultrafilter ℕ) (l : List (ℤ × Ultrafilter ℕ)) : S w l.reverse = S w l := by
  unfold S
  rw [List.map_reverse, List.sum_reverse]

/-- The classification of one sum, with the summation order of the article. -/
theorem classification_psum (l : List (ℤ × Ultrafilter ℕ)) (hl : l ≠ []) (hc : ∀ p ∈ l, p.1 ≠ 0)
    (hv : ∀ p ∈ l, ∀ a, p.2 ≠ pure a) (hpos : ∀ i, 0 < y i)
    (hgrow : ∀ B : ℕ, ∃ L : ℕ, ∀ l, L < l → 2 * (B : ℤ) * ∑ i ∈ Finset.range l, y i < y l) :
    (∃ t : TopologicalSpace ℤ, @IsTopologicalAddGroup ℤ t _ ∧
      ∀ O : Set ℤ, IsOpen[t] O ↔ IsOpenMod (genFam (Sel.ultraGen {psum y l})) O) ↔
    ∃ w : Ultrafilter ℕ, (∀ p ∈ l, p.2 = w) ∧ IsPPoint w ∧ ∃ d : ℕ, 0 < d ∧
      (d : ℤ) ∈ AddSubgroup.closure {c : ℤ | (c, w) ∈ l} ∧ (∀ p ∈ l, p.2 = w → (d : ℤ) ∣ p.1) ∧
      ((l.map Prod.fst).sum = d ∨ (l.map Prod.fst).sum = -(d : ℤ)) := by
  have h := classification y l.reverse (by simpa using hl) (fun p hp => hc p (List.mem_reverse.1 hp))
    (fun p hp => hv p (List.mem_reverse.1 hp)) hpos hgrow
  rw [← psum_eq] at h
  simpa only [List.mem_reverse, List.map_reverse, List.sum_reverse] using h

open scoped Classical in
/-- The classification of finitely many sums, with the summation order of the article. -/
theorem classification_family_psum (LL : List (List (ℤ × Ultrafilter ℕ)))
    (hv : ∀ l ∈ LL, ∀ p ∈ l, ∀ a, p.2 ≠ pure a) (hpos : ∀ i, 0 < y i)
    (hgrow : ∀ B : ℕ, ∃ L : ℕ, ∀ l, L < l → 2 * (B : ℤ) * ∑ i ∈ Finset.range l, y i < y l)
    (W : Finset (Ultrafilter ℕ)) (hWne : W.Nonempty) (hW : ∀ l ∈ LL, ∀ p ∈ l, p.2 ∈ W)
    (hWocc : ∀ w ∈ W, ∃ l ∈ LL, ∃ c : ℤ, (c, w) ∈ l)
    (d : Ultrafilter ℕ → ℕ) (hd0 : ∀ w ∈ W, 0 < d w)
    (hd : ∀ w ∈ W, (d w : ℤ) ∈ AddSubgroup.closure {c : ℤ | ∃ l ∈ LL, (c, w) ∈ l})
    (hdiv : ∀ l ∈ LL, ∀ p ∈ l, (d p.2 : ℤ) ∣ p.1) :
    (∃ t : TopologicalSpace ℤ, @IsTopologicalAddGroup ℤ t _ ∧
      ∀ O : Set ℤ, IsOpen[t] O ↔
        IsOpenMod (genFam (Sel.ultraGen {u | ∃ l ∈ LL, u = psum y l})) O) ↔
    (∀ w ∈ W, IsPPoint w) ∧
      ∀ w ∈ W, (fun w' => if w' = w then (d w : ℤ) else 0) ∈ FiniteFam.Lat LL := by
  classical
  set LR := LL.map List.reverse with hLR
  have hmem : ∀ m ∈ LR, ∃ l ∈ LL, m = l.reverse := by
    intro m hm
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hm
    exact ⟨l, hl, rfl⟩
  have hmem' : ∀ l ∈ LL, l.reverse ∈ LR := fun l hl => List.mem_map.2 ⟨l, hl, rfl⟩
  have hex : ∀ c : ℤ, ∀ w : Ultrafilter ℕ, (∃ m ∈ LR, (c, w) ∈ m) ↔ ∃ l ∈ LL, (c, w) ∈ l := by
    intro c w
    constructor
    · rintro ⟨m, hm, hcm⟩
      obtain ⟨l, hl, rfl⟩ := hmem m hm
      exact ⟨l, hl, List.mem_reverse.1 hcm⟩
    · rintro ⟨l, hl, hcl⟩
      exact ⟨l.reverse, hmem' l hl, List.mem_reverse.2 hcl⟩
  have h := classification_family y LR
    (fun m hm p hp => by
      obtain ⟨l, hl, rfl⟩ := hmem m hm
      exact hv l hl p (List.mem_reverse.1 hp))
    hpos hgrow W hWne
    (fun m hm p hp => by
      obtain ⟨l, hl, rfl⟩ := hmem m hm
      exact hW l hl p (List.mem_reverse.1 hp))
    (fun w hw => by
      obtain ⟨l, hl, c, hc⟩ := hWocc w hw
      exact ⟨l.reverse, hmem' l hl, c, List.mem_reverse.2 hc⟩)
    d hd0
    (fun w hw => by
      have : {c : ℤ | ∃ m ∈ LR, (c, w) ∈ m} = {c : ℤ | ∃ l ∈ LL, (c, w) ∈ l} := by
        ext c
        exact hex c w
      rw [this]
      exact hd w hw)
    (fun m hm p hp => by
      obtain ⟨l, hl, rfl⟩ := hmem m hm
      exact hdiv l hl p (List.mem_reverse.1 hp))
  have hgens : gens y LR = {u | ∃ l ∈ LL, u = psum y l} := by
    ext u
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨l, hl, rfl⟩ := hmem m hm
      exact ⟨l, hl, (psum_eq y l).symm⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l.reverse, hmem' l hl, psum_eq y l⟩
  have hlat : FiniteFam.Lat LR = FiniteFam.Lat LL := by
    unfold FiniteFam.Lat
    congr 1
    ext f
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨l, hl, rfl⟩ := hmem m hm
      exact ⟨l, hl, funext fun w => S_reverse w l⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l.reverse, hmem' l hl, funext fun w => (S_reverse w l).symm⟩
  rw [hgens, hlat] at h
  exact h

end Order

end PG
