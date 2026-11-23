import Mathlib

/-!
# PG: rigidity of representations by a rapidly growing sequence (Lean check)

Scope. The step of the proof of the theorem of `PG_v14` (strongly summable ultrafilters on `ℕ` are non-pretopological on
`ℤ`) in which an equation `m z = ε₁ y_{G_1} + ... + ε_N y_{G_N}` with `m = N + 1` is excluded.

Let `y : ℕ → ℤ` be nonnegative and let `D ≥ 0`. Suppose `y n > D * (y 0 + ... + y (n-1))` for all `n > N₀`.

* `fs_rigid` : if `d : ℕ → ℤ` has `|d n| ≤ D`, finite support (`d n = 0` for `n ≥ M`) and `∑_{n<M} d n * y n = 0`,
  then `d n = 0` for all `n > N₀`;
* `no_multiple` : for `N` terms `ε_j y_{G_j}` (`ε_j = ±1`, `G_j` finite sets of indices) and a nonempty finite set `F` of
  indices `> N₀`, if `y n > (2N+1) * (y 0 + ... + y (n-1))` for `n > N₀`, then `(N+1) * ∑_{n∈F} y n` is not equal to
  `∑_j ε_j * ∑_{n∈G_j} y n`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Finset

namespace PG

theorem fs_rigid (y : ℕ → ℤ) (hy : ∀ n, 0 ≤ y n) (D : ℤ) (N₀ : ℕ)
    (hgrow : ∀ n, N₀ < n → D * ∑ i ∈ range n, y i < y n) :
    ∀ M : ℕ, ∀ d : ℕ → ℤ, (∀ n, |d n| ≤ D) → (∀ n, M ≤ n → d n = 0) →
      ∑ n ∈ range M, d n * y n = 0 → ∀ n, N₀ < n → d n = 0 := by
  intro M
  induction M with
  | zero =>
    intro d _ hsupp _ n _
    exact hsupp n (Nat.zero_le n)
  | succ M ih =>
    intro d hd hsupp hsum n hn
    by_cases hM : N₀ < M
    · have hdM : d M = 0 := by
        by_contra hne
        have hsum' : ∑ k ∈ range M, d k * y k + d M * y M = 0 := by
          rw [← sum_range_succ]; exact hsum
        have h1 : |∑ k ∈ range M, d k * y k| ≤ D * ∑ i ∈ range M, y i := by
          calc |∑ k ∈ range M, d k * y k| ≤ ∑ k ∈ range M, |d k * y k| := abs_sum_le_sum_abs _ _
            _ ≤ ∑ k ∈ range M, D * y k := by
                apply sum_le_sum
                intro k _
                rw [abs_mul, abs_of_nonneg (hy k)]
                exact mul_le_mul_of_nonneg_right (hd k) (hy k)
            _ = D * ∑ i ∈ range M, y i := by rw [mul_sum]
        have h2 : y M ≤ |d M * y M| := by
          rw [abs_mul, abs_of_nonneg (hy M)]
          exact le_mul_of_one_le_left (hy M) (Int.one_le_abs hne)
        have h3 := hgrow M hM
        have h4 : d M * y M = - ∑ k ∈ range M, d k * y k := by linarith
        have h5 : |d M * y M| = |∑ k ∈ range M, d k * y k| := by rw [h4, abs_neg]
        linarith
      have hsupp' : ∀ k, M ≤ k → d k = 0 := by
        intro k hk
        rcases Nat.eq_or_lt_of_le hk with h | h
        · rw [← h]; exact hdM
        · exact hsupp k h
      have hsum'' : ∑ k ∈ range M, d k * y k = 0 := by
        rw [sum_range_succ, hdM, zero_mul, add_zero] at hsum; exact hsum
      exact ih d hd hsupp' hsum'' n hn
    · push Not at hM
      exact hsupp n (by omega)

theorem no_multiple (y : ℕ → ℤ) (hy : ∀ n, 0 ≤ y n) (N N₀ : ℕ)
    (hgrow : ∀ n, N₀ < n → ((2 * N + 1 : ℕ) : ℤ) * ∑ i ∈ range n, y i < y n)
    (F : Finset ℕ) (hF : F.Nonempty) (hFN : ∀ n ∈ F, N₀ < n)
    (G : Fin N → Finset ℕ) (ε : Fin N → ℤ) (hε : ∀ j, ε j = 1 ∨ ε j = -1) :
    ((N : ℤ) + 1) * ∑ n ∈ F, y n ≠ ∑ j, ε j * ∑ n ∈ G j, y n := by
  intro heq
  classical
  let M : ℕ := (F ∪ univ.biUnion G).sup id + 1
  have hMF : ∀ n ∈ F, n < M := fun n hn => by
    have : n ≤ (F ∪ univ.biUnion G).sup id := Finset.le_sup (f := id) (by simp [hn])
    omega
  have hMG : ∀ j, ∀ n ∈ G j, n < M := fun j n hn => by
    have : n ≤ (F ∪ univ.biUnion G).sup id :=
      Finset.le_sup (f := id) (by simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact Or.inr ⟨j, hn⟩)
    omega
  let d : ℕ → ℤ := fun n =>
    ((N : ℤ) + 1) * (if n ∈ F then 1 else 0) - ∑ j, ε j * (if n ∈ G j then 1 else 0)
  have hd : ∀ n, |d n| ≤ ((2 * N + 1 : ℕ) : ℤ) := by
    intro n
    have h1 : |((N : ℤ) + 1) * (if n ∈ F then (1 : ℤ) else 0)| ≤ (N : ℤ) + 1 := by
      by_cases h : n ∈ F
      · simp only [h, ite_true, mul_one]
        exact (abs_of_nonneg (by positivity : (0 : ℤ) ≤ (N : ℤ) + 1)).le
      · simp only [h, ite_false, mul_zero, abs_zero]
        positivity
    have h2 : |∑ j, ε j * (if n ∈ G j then (1 : ℤ) else 0)| ≤ (N : ℤ) := by
      calc |∑ j, ε j * (if n ∈ G j then (1 : ℤ) else 0)|
          ≤ ∑ j, |ε j * (if n ∈ G j then (1 : ℤ) else 0)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin N, (1 : ℤ) := by
            apply Finset.sum_le_sum
            intro j _
            rcases hε j with h | h <;> by_cases hn : n ∈ G j <;> simp [h, hn]
        _ = (N : ℤ) := by simp
    calc |d n| ≤ |((N : ℤ) + 1) * (if n ∈ F then (1 : ℤ) else 0)|
          + |∑ j, ε j * (if n ∈ G j then (1 : ℤ) else 0)| := abs_sub _ _
      _ ≤ ((2 * N + 1 : ℕ) : ℤ) := by push_cast; linarith
  have hsupp : ∀ n, M ≤ n → d n = 0 := by
    intro n hn
    have hnF : n ∉ F := fun h => by have := hMF n h; omega
    have hnG : ∀ j, n ∉ G j := fun j h => by have := hMG j n h; omega
    simp [d, hnF, hnG]
  have hsum : ∑ n ∈ range M, d n * y n = 0 := by
    have e1 : ∑ n ∈ range M, ((N : ℤ) + 1) * (if n ∈ F then (1 : ℤ) else 0) * y n
        = ((N : ℤ) + 1) * ∑ n ∈ F, y n := by
      have : ∀ n, ((N : ℤ) + 1) * (if n ∈ F then (1 : ℤ) else 0) * y n
          = ((N : ℤ) + 1) * (if n ∈ F then y n else 0) := by
        intro n; by_cases h : n ∈ F <;> simp [h]
      simp only [this, ← Finset.mul_sum]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (fun n hn => Finset.mem_range.2 (hMF n hn))]
    have e2 : ∀ j, ∑ n ∈ range M, ε j * (if n ∈ G j then (1 : ℤ) else 0) * y n
        = ε j * ∑ n ∈ G j, y n := by
      intro j
      have : ∀ n, ε j * (if n ∈ G j then (1 : ℤ) else 0) * y n = ε j * (if n ∈ G j then y n else 0) := by
        intro n; by_cases h : n ∈ G j <;> simp [h]
      simp only [this, ← Finset.mul_sum]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (fun n hn => Finset.mem_range.2 (hMG j n hn))]
    have e3 : ∑ n ∈ range M, d n * y n
        = ∑ n ∈ range M, ((N : ℤ) + 1) * (if n ∈ F then (1 : ℤ) else 0) * y n
          - ∑ j, ∑ n ∈ range M, ε j * (if n ∈ G j then (1 : ℤ) else 0) * y n := by
      simp only [d, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [e3, e1]
    simp only [e2]
    linarith
  have hz := fs_rigid y hy ((2 * N + 1 : ℕ) : ℤ) N₀ hgrow M d hd hsupp hsum
  obtain ⟨n, hn⟩ := hF
  have hdn := hz n (hFN n hn)
  have hdn' : ((N : ℤ) + 1) - ∑ j, ε j * (if n ∈ G j then (1 : ℤ) else 0) = 0 := by
    simpa [d, hn] using hdn
  have h2 : |∑ j, ε j * (if n ∈ G j then (1 : ℤ) else 0)| ≤ (N : ℤ) := by
    calc |∑ j, ε j * (if n ∈ G j then (1 : ℤ) else 0)|
        ≤ ∑ j, |ε j * (if n ∈ G j then (1 : ℤ) else 0)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin N, (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro j _
          rcases hε j with h | h <;> by_cases hn' : n ∈ G j <;> simp [h, hn']
      _ = (N : ℤ) := by simp
  have : (∑ j, ε j * (if n ∈ G j then (1 : ℤ) else 0)) = (N : ℤ) + 1 := by linarith
  rw [this] at h2
  have := abs_of_nonneg (show (0 : ℤ) ≤ (N : ℤ) + 1 by positivity)
  linarith [h2, this]

end PG
