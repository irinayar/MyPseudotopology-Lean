import LeanCheck.ChainY1

/-!
# Divisibility chains and the run condition `H`
(TVGQ-v7 §17 / HamelCharactersTVG_v18 Appendix D)

A *chain* is a sequence `M : ℕ → ℕ` of positive integers with `M i ∣ M (i+1)` and `2 M i ≤ M (i+1)`; its ratios
are `α_i = M (i+1) / M i ≥ 2`.  A *run* from `a` to `b` with bound `A` is a block of consecutive steps all of whose
ratios are `< A`.  The condition `H(M)` says that for every `A > 2` there is `L` bounding the length of runs.

This file contains the elementary lemmas used in the proofs of Theorems F and G.
-/

namespace LeanCheck

open Filter Topology

/-- Hypotheses on a chain. -/
structure ChainSeq (M : ℕ → ℕ) : Prop where
  pos : ∀ i, 0 < M i
  dvd : ∀ i, M i ∣ M (i + 1)
  two : ∀ i, 2 * M i ≤ M (i + 1)

/-- A run of consecutive steps with ratios `< A`. -/
def IsRun (M : ℕ → ℕ) (A : ℝ) (a b : ℕ) : Prop :=
  ∀ j, a ≤ j → j < b → (M (j + 1) : ℝ) < A * M j

/-- The condition `H(M)`: for every `A > 2`, runs with ratios `< A` have bounded length. -/
def HSeq (M : ℕ → ℕ) : Prop :=
  ∀ A : ℝ, 2 < A → ∃ L : ℕ, ∀ a b : ℕ, IsRun M A a b → b ≤ a + L

namespace ChainSeq

variable {M : ℕ → ℕ} (hM : ChainSeq M)
include hM

lemma dvd_of_le {i j : ℕ} (h : i ≤ j) : M i ∣ M j := by
  induction j, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ j _ ih => exact ih.trans (hM.dvd j)

lemma pow_mul_le {i j : ℕ} (h : i ≤ j) : 2 ^ (j - i) * M i ≤ M j := by
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have := hM.two j
    calc 2 ^ (j + 1 - i) * M i = 2 * (2 ^ (j - i) * M i) := by
          rw [show j + 1 - i = (j - i) + 1 by omega]; ring
      _ ≤ 2 * M j := by gcongr
      _ ≤ M (j + 1) := this

lemma pow_le (i : ℕ) : 2 ^ i ≤ M i := by
  have := hM.pow_mul_le (Nat.zero_le i)
  have h0 := hM.pos 0
  simp only [Nat.sub_zero] at this
  nlinarith [this, h0]

lemma mono {i j : ℕ} (h : i ≤ j) : M i ≤ M j := Nat.le_of_dvd (hM.pos j) (hM.dvd_of_le h)

/-- The (exact) ratio `α_i = M(i+1)/M(i)`. -/
lemma ratio_spec (i : ℕ) : ∃ α : ℕ, M (i + 1) = α * M i ∧ 2 ≤ α := by
  obtain ⟨c, hc⟩ := hM.dvd i
  refine ⟨c, by rw [hc]; ring, ?_⟩
  have := hM.two i
  have hpos := hM.pos i
  by_contra hlt
  push_neg at hlt
  interval_cases c <;> simp at hc <;> omega

end ChainSeq

/-! ### Runs beyond any bound -/

lemma exists_run_beyond {M : ℕ → ℕ} (hnot : ¬ HSeq M) :
    ∃ A : ℝ, 2 < A ∧ ∀ N m : ℕ, ∃ p : ℕ × ℕ, N ≤ p.1 ∧ p.1 + m ≤ p.2 ∧ IsRun M A p.1 p.2 := by
  unfold HSeq at hnot
  push_neg at hnot
  obtain ⟨A, hA, hL⟩ := hnot
  refine ⟨A, hA, fun N m => ?_⟩
  obtain ⟨a, b, hrun, hb⟩ := hL (N + m)
  refine ⟨(a + N, b), by omega, by omega, fun j hj hjb => hrun j (by omega) hjb⟩

lemma exists_run_seq {M : ℕ → ℕ} (hnot : ¬ HSeq M) :
    ∃ A : ℝ, 2 < A ∧ ∃ a b : ℕ → ℕ, ∀ s, a s + (s + 1) ≤ b s ∧ IsRun M A (a s) (b s) ∧
      b s + (s + 1) ≤ a (s + 1) := by
  obtain ⟨A, hA, hR⟩ := exists_run_beyond hnot
  refine ⟨A, hA, ?_⟩
  let P : ℕ → ℕ × ℕ := fun s => Nat.rec (Classical.choose (hR 0 1))
    (fun s p => Classical.choose (hR (p.2 + (s + 1)) (s + 2))) s
  have hP0 : P 0 = Classical.choose (hR 0 1) := rfl
  have hPs : ∀ s, P (s + 1) = Classical.choose (hR ((P s).2 + (s + 1)) (s + 2)) := fun s => rfl
  have hspec0 := Classical.choose_spec (hR 0 1)
  have hspecs : ∀ s, (P s).2 + (s + 1) ≤ (P (s + 1)).1 ∧ (P (s + 1)).1 + (s + 2) ≤ (P (s + 1)).2 ∧
      IsRun M A (P (s + 1)).1 (P (s + 1)).2 := fun s => by
    have := Classical.choose_spec (hR ((P s).2 + (s + 1)) (s + 2))
    rw [← hPs] at this
    exact this
  refine ⟨fun s => (P s).1, fun s => (P s).2, fun s => ?_⟩
  refine ⟨?_, ?_, (hspecs s).1⟩
  · cases s with
    | zero => show (P 0).1 + (0 + 1) ≤ (P 0).2; rw [hP0]; simpa using hspec0.2.1
    | succ s => have := (hspecs s).2.1; simpa [add_assoc] using this
  · cases s with
    | zero => show IsRun M A (P 0).1 (P 0).2; rw [hP0]; exact hspec0.2.2
    | succ s => exact (hspecs s).2.2

/-! ### Contraction along a descending run -/

/-- If `y_j = r_j y_{j+1}` modulo integers on `[a, b]` with `2 ≤ r_j ≤ A` and `δ(1+A) < 1`, `|y_j| < δ`, then
`|y_b| 2^{b-a} ≤ |y_a|`. -/
lemma contract_down {δ A : ℝ} (hA : δ * (1 + A) < 1) (y : ℕ → ℝ) (r : ℕ → ℕ) (a : ℕ) :
    ∀ k : ℕ, (∀ j, a ≤ j → j < a + k → 2 ≤ r j) → (∀ j, a ≤ j → j < a + k → (r j : ℝ) ≤ A) →
      (∀ j, a ≤ j → j ≤ a + k → |y j| < δ) →
      (∀ j, a ≤ j → j < a + k → ∃ n : ℤ, y j - r j * y (j + 1) = n) →
      |y (a + k)| * 2 ^ k ≤ |y a| := by
  intro k
  induction k with
  | zero => intro _ _ _ _; simp
  | succ k ih =>
    intro hr2 hrA hy hint
    have ih' := ih (fun j h1 h2 => hr2 j h1 (by omega)) (fun j h1 h2 => hrA j h1 (by omega))
      (fun j h1 h2 => hy j h1 (by omega)) (fun j h1 h2 => hint j h1 (by omega))
    have hstep : y (a + k) = r (a + k) * y (a + k + 1) :=
      contraction_step (hrA (a + k) (by omega) (by omega)) hA (hy (a + k + 1) (by omega) le_rfl)
        (hy (a + k) (by omega) (by omega)) (hint (a + k) (by omega) (by omega))
    have hr2' : (2 : ℝ) ≤ r (a + k) := by exact_mod_cast hr2 (a + k) (by omega) (by omega)
    have habs : |y (a + k)| = r (a + k) * |y (a + k + 1)| := by
      rw [hstep, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r (a + k))]
    calc |y (a + (k + 1))| * 2 ^ (k + 1) = (|y (a + k + 1)| * 2) * 2 ^ k := by rw [← add_assoc]; ring
      _ ≤ |y (a + k)| * 2 ^ k := by
          have : |y (a + k + 1)| * 2 ≤ |y (a + k)| := by
            rw [habs]; nlinarith [abs_nonneg (y (a + k + 1))]
          gcongr
      _ ≤ |y a| := ih'

end LeanCheck
