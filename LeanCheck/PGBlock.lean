import Mathlib
import LeanCheck.PGDigit

/-!
# PG: the gap-splitting step of the block argument (Lean check)

Scope. The key step of the block arguments in Lemma 6.1 (weight of alternating sums) and in the closure lemma of
`PG_v3` (`D_{p,k}` is closed modulo powers of `p`). A relation `±p^{x_1} ± ... ± p^{x_T} = 0` among fewer than `p^{L+1}`
terms splits at every gap longer than `L` in the exponents into two relations (the terms with exponent `< q` and
those with exponent `≥ q`, when no exponent lies in `[q - L, q - 1]`).

* `abs_val_le` : if all exponents are `≤ e` then `|val p l| ≤ length(l) * p^e`;
* `dvd_val` : if all exponents are `≥ q` then `p^q` divides `val p l`;
* `gap_split` : the splitting of a relation `val low + val high = 0` with exponents of `low` `≤ q - L - 1`, exponents of
  `high` `≥ q` and `#low < p^{L+1}`: both sums are `0`;
* `split_zero` : the same for a list `l` with `val p l = 0`, `#l < p^{L+1}`, and no exponent in `[q - L, q - 1]`.

Not formalized: the iteration of `split_zero` into maximal blocks and the counting of terms in the blocks, which are used in
Lemma 6.1 and in the closure lemma of the article.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open List

namespace PG

theorem abs_sp (p : ℕ) (t : Bool × ℕ) : |sp p t| = (p : ℤ) ^ t.2 := by
  obtain ⟨b, z⟩ := t
  cases b <;> simp [sp, abs_pow]

theorem abs_val_le (p e : ℕ) (hp : 1 ≤ p) (l : List (Bool × ℕ)) (h : ∀ t ∈ l, t.2 ≤ e) :
    |val p l| ≤ (l.length : ℤ) * (p : ℤ) ^ e := by
  induction l with
  | nil => simp [val]
  | cons t l ih =>
    rw [val_cons]
    have h1 : |sp p t| ≤ (p : ℤ) ^ e := by
      rw [abs_sp]
      exact pow_le_pow_right₀ (by exact_mod_cast hp) (h t (by simp))
    have h2 := ih (fun s hs => h s (by simp [hs]))
    calc |sp p t + val p l| ≤ |sp p t| + |val p l| := abs_add_le _ _
      _ ≤ (p : ℤ) ^ e + (l.length : ℤ) * (p : ℤ) ^ e := add_le_add h1 h2
      _ = ((t :: l).length : ℤ) * (p : ℤ) ^ e := by simp; ring

theorem dvd_val (p q : ℕ) (l : List (Bool × ℕ)) (h : ∀ t ∈ l, q ≤ t.2) : (p : ℤ) ^ q ∣ val p l := by
  induction l with
  | nil => simp [val]
  | cons t l ih =>
    rw [val_cons]
    refine dvd_add ?_ (ih (fun s hs => h s (by simp [hs])))
    obtain ⟨b, z⟩ := t
    have hz : q ≤ z := h (b, z) (by simp)
    have : (p : ℤ) ^ q ∣ (p : ℤ) ^ z := pow_dvd_pow _ hz
    cases b <;> simp [sp] <;> exact this

theorem gap_split (p L q : ℕ) (hp : 2 ≤ p) (low high : List (Bool × ℕ))
    (hlow : ∀ t ∈ low, t.2 + L + 1 ≤ q) (hhigh : ∀ t ∈ high, q ≤ t.2)
    (hcount : low.length < p ^ (L + 1)) (hsum : val p low + val p high = 0) :
    val p high = 0 ∧ val p low = 0 := by
  have hppos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast (by omega : 0 < p)
  obtain ⟨c, hc⟩ := dvd_val p q high hhigh
  have hlt : |val p low| < (p : ℤ) ^ q := by
    by_cases hne : low = []
    · subst hne
      simp [val_nil]
      positivity
    · obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil low hne
      have hq : L + 1 ≤ q := by have := hlow t ht; omega
      have hb := abs_val_le p (q - (L + 1)) (by omega) low (fun s hs => by have := hlow s hs; omega)
      have hcast : (low.length : ℤ) < (p : ℤ) ^ (L + 1) := by exact_mod_cast hcount
      calc |val p low| ≤ (low.length : ℤ) * (p : ℤ) ^ (q - (L + 1)) := hb
        _ < (p : ℤ) ^ (L + 1) * (p : ℤ) ^ (q - (L + 1)) :=
            mul_lt_mul_of_pos_right hcast (by positivity)
        _ = (p : ℤ) ^ q := by rw [← pow_add]; congr 1; omega
  have h1 : val p low = - ((p : ℤ) ^ q * c) := by linarith
  have hc0 : c = 0 := by
    by_contra hne
    have h2 : (p : ℤ) ^ q ≤ |(p : ℤ) ^ q * c| := by
      rw [abs_mul, abs_of_pos (by positivity)]
      exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hne)
    rw [h1, abs_neg] at hlt
    linarith
  subst hc0
  refine ⟨by simpa using hc, ?_⟩
  rw [h1]; simp

theorem split_zero (p L q : ℕ) (hp : 2 ≤ p) (l : List (Bool × ℕ))
    (hnone : ∀ t ∈ l, ¬ (q ≤ t.2 + L ∧ t.2 < q))
    (hcount : l.length < p ^ (L + 1)) (hsum : val p l = 0) :
    val p (l.filter (fun t => decide (t.2 < q))) = 0 ∧
      val p (l.filter (fun t => decide (q ≤ t.2))) = 0 := by
  have hperm := List.filter_append_perm (fun t : Bool × ℕ => decide (t.2 < q)) l
  have hfun : (fun t : Bool × ℕ => !decide (t.2 < q)) = (fun t : Bool × ℕ => decide (q ≤ t.2)) := by
    funext t
    by_cases h : t.2 < q
    · have h' : ¬ q ≤ t.2 := Nat.not_le.mpr h
      simp [h, h']
    · have h' : q ≤ t.2 := Nat.not_lt.mp h
      simp [h, h']
  rw [hfun] at hperm
  have hs : val p (l.filter (fun t => decide (t.2 < q))) + val p (l.filter (fun t => decide (q ≤ t.2))) = 0 := by
    rw [← val_append]
    unfold val
    rw [(hperm.map (sp p)).sum_eq]
    exact hsum
  have := gap_split p L q hp (l.filter (fun t => decide (t.2 < q))) (l.filter (fun t => decide (q ≤ t.2)))
    (fun t ht => by
      rw [List.mem_filter] at ht
      have h1 := hnone t ht.1
      have h2 : t.2 < q := by simpa using ht.2
      omega)
    (fun t ht => by
      rw [List.mem_filter] at ht
      simpa using ht.2)
    (lt_of_le_of_lt (List.length_filter_le _ _) hcount) hs
  exact ⟨this.2, this.1⟩

end PG
