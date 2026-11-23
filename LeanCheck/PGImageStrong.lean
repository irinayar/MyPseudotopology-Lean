import Mathlib

/-!
# PG: images of stable ordered-union ultrafilters are increasing along a large set (Lean check)

Scope. The homogeneity argument of the new lemma of `PG_v18` (Section 9): for a stable ordered-union ultrafilter `U`
and a sequence `x` of positive integers, the image of `U` under `φ(s) = ∑_{i ∈ s} x_i` is strongly summable.
Abstractly: blocks are the elements of a type `X` with an ordering relation `lt` (`max a < min b`), a union operation
`un` (the union of two ordered blocks) and a value function `f : X → ℕ` with `f a > 0` and `f (un a b) = f a + f b`
when `lt a b`. `U` is an ultrafilter on `X` that is stable (every partition of the ordered pairs has a homogeneous
member of `U`) and such that inside every `H ∈ U` there is an `lt`-increasing sequence `a` in `H` with all the
unions `un (a i) (a j)`, `i < j`, in `H` (in the article: `FU(a) ⊆ H`).

* `no_strictAnti_nat` : there is no strictly decreasing sequence of natural numbers;
* `stable_image_increasing` : there is `H ∈ U` with `f a < f b` whenever `a, b ∈ H` and `lt a b`.

In the article this gives, for a set `A` in the image ultrafilter, an ordered sequence `a` with `FU(a) ∈ U` inside
`H ∩ φ⁻¹(A)`, so that `b_i = φ(a_i)` is strictly increasing and `FS(b) ⊆ A`, `FS(b) ∈ p`; this last step is not formalized.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set

namespace PG

section imagestrong

variable {X : Type*}

theorem no_strictAnti_nat (g : ℕ → ℕ) (h : ∀ n, g (n + 1) < g n) : False := by
  have key : ∀ n, g n + n ≤ g 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := h n
      omega
  have h1 := key (g 0 + 1)
  omega

theorem stable_image_increasing (lt : X → X → Prop) (un : X → X → X) (f : X → ℕ) (U : Ultrafilter X)
    (hpos : ∀ a, 0 < f a)
    (hadd : ∀ a b, lt a b → f (un a b) = f a + f b)
    (hltun : ∀ a b c, lt a b → lt b c → lt a (un b c))
    (hstable : ∀ P : X → X → Prop, ∃ H ∈ (U : Filter X),
      (∀ a ∈ H, ∀ b ∈ H, lt a b → P a b) ∨ (∀ a ∈ H, ∀ b ∈ H, lt a b → ¬ P a b))
    (hbase : ∀ H ∈ (U : Filter X), ∃ a : ℕ → X, (∀ n, a n ∈ H) ∧ (∀ n, lt (a n) (a (n + 1))) ∧
        ∀ i j, i < j → un (a i) (a j) ∈ H) :
    ∃ H ∈ (U : Filter X), ∀ a ∈ H, ∀ b ∈ H, lt a b → f a < f b := by
  obtain ⟨H₁, h₁, hh₁⟩ := hstable (fun a b => f a < f b)
  obtain ⟨H₂, h₂, hh₂⟩ := hstable (fun a b => f a = f b)
  have hH : H₁ ∩ H₂ ∈ (U : Filter X) := Filter.inter_mem h₁ h₂
  rcases hh₁ with h | h
  · exact ⟨H₁, h₁, h⟩
  · exfalso
    obtain ⟨a, haH, hlt, hun⟩ := hbase (H₁ ∩ H₂) hH
    rcases hh₂ with h' | h'
    · have e1 : f (a 0) = f (a 1) := h' (a 0) (haH 0).2 (a 1) (haH 1).2 (hlt 0)
      have hl12 : lt (a 1) (a 2) := hlt 1
      have hl02 : lt (a 0) (un (a 1) (a 2)) := hltun _ _ _ (hlt 0) hl12
      have e2 : f (a 0) = f (un (a 1) (a 2)) :=
        h' (a 0) (haH 0).2 _ (hun 1 2 (by norm_num)).2 hl02
      rw [hadd _ _ hl12] at e2
      have := hpos (a 2)
      omega
    · apply no_strictAnti_nat (fun n => f (a n))
      intro n
      have h1 : ¬ f (a n) < f (a (n + 1)) := h _ (haH n).1 _ (haH (n + 1)).1 (hlt n)
      have h2 : ¬ f (a n) = f (a (n + 1)) := h' _ (haH n).2 _ (haH (n + 1)).2 (hlt n)
      omega

end imagestrong

end PG
