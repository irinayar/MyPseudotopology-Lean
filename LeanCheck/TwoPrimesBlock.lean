import Mathlib

/-!
# TwoPrimes: the finite counting steps of the block collision lemma

The block lemma (TwoPrimes_v7, Section "Collision energy") says: if `V = A - B` and `V ∩ (V + t) = ∅` for an
integer `t ≠ 0`, then the normalized collision energy `C` is bounded below by an explicit constant close to `8/3`.
Its proof uses two finite steps, checked here.

* `occupancy_le`: a set `S` of integers inside a window of `N` consecutive integers with no two elements at
  distance `|t|` has `2 |S| ≤ N + |t|` elements (so at most `(N + |t|)/2`).
* `block_cs`: Cauchy-Schwarz on one block: `(∑ μ)^2 ≤ |S| ∑ μ^2` (the form used for `∑ q_i^2 / n_i ≤ ∑ μ(n)^2`).
-/

namespace LeanCheck
namespace TwoPrimes

open Finset

/-- A set in a window of `N = b - a + 1` consecutive integers, with no two elements at distance `T > 0`,
satisfies `2 |S| ≤ N + T`. -/
lemma occupancy_le_nat (a b : ℤ) (T : ℕ) (hT : 0 < T) (S : Finset ℤ)
    (hS : S ⊆ Finset.Icc a b) (hgap : ∀ x ∈ S, x + (T : ℤ) ∉ S) :
    2 * S.card ≤ (b - a + 1).toNat + T := by
  have hinj : Function.Injective (fun x : ℤ => x + (T : ℤ)) := fun x y h => by simpa using h
  have himg : (S.image (fun x : ℤ => x + (T : ℤ))).card = S.card := Finset.card_image_of_injective _ hinj
  have hdisj : Disjoint S (S.image (fun x : ℤ => x + (T : ℤ))) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    rw [Finset.mem_image] at hy'
    obtain ⟨x, hx, hxy⟩ := hy'
    apply hgap x hx
    rw [hxy]; exact hy
  have hsub : S ∪ S.image (fun x : ℤ => x + (T : ℤ)) ⊆ Finset.Icc a (b + (T : ℤ)) := by
    intro y hy
    rw [Finset.mem_union] at hy
    rw [Finset.mem_Icc]
    rcases hy with hy | hy
    · have := Finset.mem_Icc.mp (hS hy); constructor <;> omega
    · rw [Finset.mem_image] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      have := Finset.mem_Icc.mp (hS hx); constructor <;> omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, himg, Int.card_Icc] at hcard
  have : ((b + (T : ℤ) + 1 - a).toNat : ℤ) = ((b - a + 1).toNat : ℤ) + T ∨ b - a + 1 < 0 := by
    by_cases h : 0 ≤ b - a + 1
    · left; omega
    · right; omega
  rcases this with h | h
  · omega
  · have hem : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := Finset.mem_Icc.mp (hS hx); omega
    subst hem; simp

/-- Integer form: `t ≠ 0`, no `x ∈ S` with `x + t ∈ S`. -/
lemma occupancy_le (a b t : ℤ) (ht : t ≠ 0) (S : Finset ℤ)
    (hS : S ⊆ Finset.Icc a b) (hgap : ∀ x ∈ S, x + t ∉ S) :
    2 * S.card ≤ (b - a + 1).toNat + t.natAbs := by
  have hT : 0 < t.natAbs := Int.natAbs_pos.mpr ht
  apply occupancy_le_nat a b t.natAbs hT S hS
  intro x hx hx'
  rcases Int.natAbs_eq t with h | h
  · apply hgap x hx
    rw [h]; exact hx'
  · apply hgap (x + (t.natAbs : ℤ)) hx'
    have : x + (t.natAbs : ℤ) + t = x := by omega
    rw [this]; exact hx

/-- Cauchy-Schwarz on one block. -/
lemma block_cs (S : Finset ℤ) (μ : ℤ → ℝ) :
    (∑ n ∈ S, μ n) ^ 2 ≤ (S.card : ℝ) * ∑ n ∈ S, μ n ^ 2 :=
  _root_.sq_sum_le_card_mul_sum_sq

end TwoPrimes
end LeanCheck
