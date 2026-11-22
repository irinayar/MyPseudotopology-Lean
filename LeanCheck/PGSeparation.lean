import Mathlib
import LeanCheck.PGBlock

/-!
# PG: the separation lemma for sums of signed powers (Lean check)

Scope. The lemma used in the finiteness step of `PG_v11` (Section 8): if `t = a + b` where `t` is a sum of signed
powers of `p` all of whose exponents are `> s + L`, `b` is a sum of signed powers with exponents `≤ s`, and `a` is a
sum of signed powers none of which has an exponent in `(s, s + L]`, and the total number of terms is `< p^{L+1}`, then `t`
is a sum of at most as many signed powers as `a` has terms (namely those of `a` with exponent `> s + L`).

* `separation` : the statement, with the terms given as lists `lt`, `la`, `lb` of (sign, exponent) pairs and
  `val p lt = val p la + val p lb`; the conclusion is `val p lt ∈ D p la.length`.

It is derived from `split_zero` of `PGBlock` (a relation among fewer than `p^{L+1}` terms splits at a gap longer than `L`).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open List

namespace PG

/-- Flipping the signs does not change the exponents. -/
theorem filter_flip (q : ℕ) (l : List (Bool × ℕ)) :
    (l.map (fun t => (!t.1, t.2))).filter (fun t => decide (q ≤ t.2)) =
      (l.filter (fun t => decide (q ≤ t.2))).map (fun t => (!t.1, t.2)) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    by_cases h : q ≤ t.2
    · simp [h, ih]
    · simp [h, ih]

theorem separation (p L s : ℕ) (hp : 2 ≤ p) (lt la lb : List (Bool × ℕ))
    (hrel : val p lt = val p la + val p lb)
    (hhigh : ∀ x ∈ lt, s + L + 1 ≤ x.2)
    (hlow : ∀ x ∈ lb, x.2 ≤ s)
    (hgap : ∀ x ∈ la, ¬ (s < x.2 ∧ x.2 ≤ s + L))
    (hcount : lt.length + la.length + lb.length < p ^ (L + 1)) :
    val p lt ∈ D p la.length := by
  set q := s + L + 1 with hq
  let u : List (Bool × ℕ) := lt ++ (la.map (fun t : Bool × ℕ => (!t.1, t.2)) ++ lb.map (fun t : Bool × ℕ => (!t.1, t.2)))
  have hu : val p u = 0 := by
    simp only [u, val_append, val_flip]
    linarith
  have hlen : u.length < p ^ (L + 1) := by
    simp only [u, List.length_append, List.length_map]
    omega
  have hnone : ∀ t ∈ u, ¬ (q ≤ t.2 + L ∧ t.2 < q) := by
    intro t ht
    simp only [u, List.mem_append, List.mem_map] at ht
    rcases ht with ht | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · have := hhigh t ht; omega
    · have := hgap x hx; simp only []; omega
    · have := hlow x hx; simp only []; omega
  obtain ⟨_, hhi⟩ := split_zero p L q hp u hnone hlen hu
  have h1 : u.filter (fun t => decide (q ≤ t.2)) =
      lt ++ (la.filter (fun t => decide (q ≤ t.2))).map (fun t : Bool × ℕ => (!t.1, t.2)) := by
    simp only [u, List.filter_append]
    have hlt : lt.filter (fun t => decide (q ≤ t.2)) = lt := by
      rw [List.filter_eq_self]
      intro x hx
      simpa using hhigh x hx
    have hlb : (lb.map (fun t : Bool × ℕ => (!t.1, t.2))).filter (fun t => decide (q ≤ t.2)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := hlow y hy
      simp only []
      simp
      omega
    rw [hlt, hlb, filter_flip, List.append_nil]
  rw [h1, val_append, val_flip] at hhi
  refine ⟨la.filter (fun t => decide (q ≤ t.2)), List.length_filter_le _ _, ?_⟩
  linarith

end PG
