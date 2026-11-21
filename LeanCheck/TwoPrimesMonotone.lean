import Mathlib

/-!
# TwoPrimes: monotonicity of the collision count (Lemma G1)

Let `G` be a finite additive commutative group, `X`, `Y` finite types and `φ : X → G`, `ψ : Y → G`.
Consider the "sum" `V = φ x + ψ y` of independent uniform `x ∈ X`, `y ∈ Y`.  The number of collisions of `V`,
`C(V) = #{(x, y, x', y') : φ x + ψ y = φ x' + ψ y'}`, satisfies
`C(V) ≤ |Y|² · #{(x, x') : φ x = φ x'}`, that is: the collision probability of `V` is at most the collision
probability of its summand `φ x` alone (`collision_le`).  This is Lemma G1 of the TwoPrimes note
(dropping levels of the digit model can only increase the collision probability), proved here for a finite
abelian group; the case of integers is obtained by reducing modulo a large integer (not formalized).

The key step is `card_diff_le`: `#{(x, x') : φ x - φ x' = d} ≤ #{(x, x') : φ x = φ x'}` for every `d`
(Cauchy-Schwarz on the fibre sizes).
-/

namespace LeanCheck
namespace TwoPrimes

open Finset

section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {X : Type*} [Fintype X]

/-- The size of the fibre of `φ` over `w`. -/
def fib (φ : X → G) (w : G) : ℕ := (univ.filter fun x => φ x = w).card

lemma card_diff_eq (φ : X → G) (d : G) :
    (univ.filter fun q : X × X => φ q.1 - φ q.2 = d).card = ∑ w, fib φ w * fib φ (w + d) := by
  classical
  have h1 : (univ.filter fun q : X × X => φ q.1 - φ q.2 = d).card
      = ∑ x' : X, fib φ (φ x' + d) := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x' _
    unfold fib
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro x _
    simp only [sub_eq_iff_eq_add]
    rw [add_comm d (φ x')]
  rw [h1]
  rw [← Finset.sum_fiberwise (s := (univ : Finset X)) (g := φ)]
  apply Finset.sum_congr rfl
  intro w _
  have : ∀ x' ∈ univ.filter (fun x' => φ x' = w), fib φ (φ x' + d) = fib φ (w + d) := by
    intro x' hx'
    rw [(Finset.mem_filter.mp hx').2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
  rfl

lemma card_same_eq (φ : X → G) :
    (univ.filter fun q : X × X => φ q.1 = φ q.2).card = ∑ w, fib φ w * fib φ w := by
  classical
  have h := card_diff_eq φ 0
  simpa [sub_eq_zero] using h

/-- Cauchy-Schwarz on the fibre sizes: shifting cannot increase the number of pairs. -/
theorem card_diff_le (φ : X → G) (d : G) :
    (univ.filter fun q : X × X => φ q.1 - φ q.2 = d).card ≤
      (univ.filter fun q : X × X => φ q.1 = φ q.2).card := by
  classical
  rw [card_diff_eq, card_same_eq]
  have hshift : ∑ w, fib φ (w + d) * fib φ (w + d) = ∑ w, fib φ w * fib φ w :=
    Equiv.sum_comp (Equiv.addRight d) (fun w => fib φ w * fib φ w)
  have h2 : ∀ w, 2 * (fib φ w * fib φ (w + d)) ≤ fib φ w * fib φ w + fib φ (w + d) * fib φ (w + d) := by
    intro w
    nlinarith [sq_nonneg ((fib φ w : ℤ) - fib φ (w + d))]
  have h3 : 2 * ∑ w, fib φ w * fib φ (w + d) ≤ 2 * ∑ w, fib φ w * fib φ w := by
    rw [Finset.mul_sum]
    calc ∑ w, 2 * (fib φ w * fib φ (w + d))
        ≤ ∑ w, (fib φ w * fib φ w + fib φ (w + d) * fib φ (w + d)) := Finset.sum_le_sum fun w _ => h2 w
      _ = ∑ w, fib φ w * fib φ w + ∑ w, fib φ (w + d) * fib φ (w + d) := Finset.sum_add_distrib
      _ = 2 * ∑ w, fib φ w * fib φ w := by rw [hshift]; ring
  omega

variable {Y : Type*} [Fintype Y]

/-- Lemma G1 (finite abelian group form): the collision count of a sum is at most `|Y|²` times the
collision count of one summand. -/
theorem collision_le (φ : X → G) (ψ : Y → G) :
    (univ.filter fun q : (X × Y) × (X × Y) => φ q.1.1 + ψ q.1.2 = φ q.2.1 + ψ q.2.2).card ≤
      Fintype.card Y ^ 2 * (univ.filter fun q : X × X => φ q.1 = φ q.2).card := by
  classical
  set s := (univ.filter fun q : (X × Y) × (X × Y) => φ q.1.1 + ψ q.1.2 = φ q.2.1 + ψ q.2.2) with hs
  have hfib : ∀ a ∈ s.image (fun q : (X × Y) × (X × Y) => (q.1.2, q.2.2)),
      (s.filter fun q => (q.1.2, q.2.2) = a).card ≤
        (univ.filter fun q : X × X => φ q.1 = φ q.2).card := by
    intro a _
    refine le_trans ?_ (card_diff_le φ (ψ a.2 - ψ a.1))
    refine Finset.card_le_card_of_injOn (fun q => (q.1.1, q.2.1)) ?_ ?_
    · intro q hq
      rw [Finset.mem_coe, Finset.mem_filter] at hq
      obtain ⟨hqs, hqa⟩ := hq
      rw [hs, Finset.mem_filter] at hqs
      have h1 := hqs.2
      have e1 : q.1.2 = a.1 := (Prod.mk.inj hqa).1
      have e2 : q.2.2 = a.2 := (Prod.mk.inj hqa).2
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show φ q.1.1 - φ q.2.1 = ψ a.2 - ψ a.1
      rw [← e1, ← e2, sub_eq_sub_iff_add_eq_add, add_comm (ψ q.2.2) (φ q.2.1)]
      exact h1
    · intro q hq q' hq' h
      rw [Finset.mem_coe, Finset.mem_filter] at hq hq'
      have e1 : q.1.2 = q'.1.2 := by
        have := hq.2.trans hq'.2.symm
        exact (Prod.mk.inj this).1
      have e2 : q.2.2 = q'.2.2 := by
        have := hq.2.trans hq'.2.symm
        exact (Prod.mk.inj this).2
      have h1 : q.1.1 = q'.1.1 := (Prod.mk.inj h).1
      have h2 : q.2.1 = q'.2.1 := (Prod.mk.inj h).2
      exact Prod.ext (Prod.ext h1 e1) (Prod.ext h2 e2)
  have h1 := Finset.card_le_mul_card_image s _ hfib
  have h2 : (s.image (fun q : (X × Y) × (X × Y) => (q.1.2, q.2.2))).card ≤ Fintype.card Y ^ 2 := by
    calc _ ≤ (univ : Finset (Y × Y)).card := Finset.card_le_univ _
      _ = Fintype.card Y ^ 2 := by simp [Fintype.card_prod, sq]
  calc s.card ≤ _ := h1
    _ ≤ (univ.filter fun q : X × X => φ q.1 = φ q.2).card * Fintype.card Y ^ 2 :=
        Nat.mul_le_mul_left _ h2
    _ = _ := by ring

end

end TwoPrimes
end LeanCheck
