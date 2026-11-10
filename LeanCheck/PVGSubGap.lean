import Mathlib
import LeanCheck.PVGSubIdeal

/-!
# PVG: the top-index estimate for `a₁S_A + … + a_kS_A` (Lean check)

Scope. Lemma X of Addendum N2 of the research note (first estimate of Theorem 8.61 of PVG_v27, planned). For `A ⊆ ℕ`, a list `l` of
coefficients and `m ≥ 0`: if `n ∉ A` is large, no `z = e + σ` with `|e| ≤ m`, `σ ∈ a₁S_A + … + a_kS_A`, has `γ₁ s_n ≤ |z| ≤ γ₂ s_n`.

* `rep_of_mem_sumSetA`: the representation `σ = ∑ d_n s_n` of `PVGLacCount.rep_of_mem_sumSet` with `d_n = 0` for `n ∉ A`;
* `sigma_dichotomy`: if `d_j = 0` then `|σ| ≤ 2 c₁ s_{j-1}` or `|σ| ≥ c₀ s_{j+1} / 2`;
* `top_index`: the estimate.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter
open scoped Classical

namespace PVG
namespace Lac

/-- Representation of the elements of `sumSetA A l`, supported in `A`. -/
lemma rep_of_mem_sumSetA (A : Set ℕ) : ∀ (l : List ℝ) (x : ℝ), x ∈ sumSetA A l →
    ∃ (N : ℕ) (d : ℕ → ℝ), (∀ n, d n ∈ Cset l) ∧ (∀ n, N ≤ n → d n = 0) ∧ (∀ n, n ∉ A → d n = 0) ∧
      x = ∑ n ∈ Finset.range N, d n * sS n
  | [], x, hx => by
    have : x = 0 := hx
    exact ⟨0, fun _ => 0, fun n => by simp [Cset], fun _ _ => rfl, fun _ _ => rfl, by simp [this]⟩
  | a :: l, x, hx => by
    obtain ⟨c, hc, y, hy, rfl⟩ := mem_sumSetA_cons.1 hx
    obtain ⟨N, d, hd, hd0, hdA, hyd⟩ := rep_of_mem_sumSetA A l y hy
    rcases hc with hc0 | ⟨j, hjA, hj1, hcj⟩
    · refine ⟨N, d, fun n => Cset_sub a l (hd n), hd0, hdA, ?_⟩
      simp [hc0, hyd]
    · have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → c = ε * sS j →
          ∃ (N' : ℕ) (d' : ℕ → ℝ), (∀ n, d' n ∈ Cset (a :: l)) ∧ (∀ n, N' ≤ n → d' n = 0) ∧
            (∀ n, n ∉ A → d' n = 0) ∧ (a * c + y) = ∑ n ∈ Finset.range N', d' n * sS n := by
        intro ε hε hcε
        refine ⟨max N (j + 1), fun n => d n + (if n = j then ε * a else 0), ?_, ?_, ?_, ?_⟩
        · intro n
          by_cases hn : n = j
          · simp only [hn, if_true]
            simp only [Cset, Finset.mem_union, Finset.mem_image]
            rcases hε with rfl | rfl
            · exact Or.inl (Or.inr ⟨d j, hd j, by ring⟩)
            · exact Or.inr ⟨d j, hd j, by ring⟩
          · simp only [hn, if_false, add_zero]; exact Cset_sub a l (hd n)
        · intro n hn
          have h1 : N ≤ n := le_trans (le_max_left _ _) hn
          have h2 : n ≠ j := by
            have := le_trans (le_max_right _ _) hn; omega
          simp [hd0 n h1, h2]
        · intro n hn
          have h2 : n ≠ j := fun h => hn (h ▸ hjA)
          simp [hdA n hn, h2]
        · have hs1 : ∑ n ∈ Finset.range (max N (j + 1)), d n * sS n = y := by
            rw [hyd]
            symm
            have hle : N ≤ max N (j + 1) := le_max_left _ _
            rw [← Finset.sum_range_add_sum_Ico _ hle]
            have : ∑ n ∈ Finset.Ico N (max N (j + 1)), d n * sS n = 0 :=
              Finset.sum_eq_zero (fun n hn => by rw [hd0 n (Finset.mem_Ico.1 hn).1]; simp)
            rw [this, add_zero]
          have hs2 : ∑ n ∈ Finset.range (max N (j + 1)), (if n = j then ε * a else 0) * sS n = ε * a * sS j := by
            have : ∀ n ∈ Finset.range (max N (j + 1)), (if n = j then ε * a else 0) * sS n =
                if n = j then ε * a * sS j else 0 := by
              intro n _; split_ifs with h
              · rw [h]
              · simp
            rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range (max N (j + 1))) j (fun _ => ε * a * sS j)]
            rw [if_pos]
            exact Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _))
          simp only [add_mul, Finset.sum_add_distrib, hs1, hs2]
          rw [hcε]; ring
      rcases hcj with h | h
      · exact key 1 (Or.inl rfl) (by rw [h]; ring)
      · exact key (-1) (Or.inr rfl) (by rw [h]; ring)

/-- If `d_j = 0`, then `|∑ d_n s_n|` is at most `2 c₁ s_{j-1}` or at least `c₀ s_{j+1} / 2`. -/
lemma sigma_dichotomy {c0 c1 : ℝ} (hc0 : 0 < c0) (hc1 : 1 ≤ c1) (N0 : ℕ) (hN0 : 1 ≤ N0)
    (hN0big : ∀ T, N0 ≤ T → 4 * c1 ≤ c0 * 2 ^ (2 * T - 1))
    (d : ℕ → ℝ) (hd : ∀ n, d n = 0 ∨ (c0 ≤ |d n| ∧ |d n| ≤ c1)) (N : ℕ) (hN : ∀ n, N ≤ n → d n = 0)
    (j : ℕ) (hj1 : 1 ≤ j) (hjN0 : N0 ≤ j) (hdj : d j = 0) :
    |∑ n ∈ Finset.range N, d n * sS n| ≤ 2 * c1 * sS (j - 1) ∨
      c0 * sS (j + 1) / 2 ≤ |∑ n ∈ Finset.range N, d n * sS n| := by
  have hcd : ∀ n, |d n| ≤ c1 := by
    intro n
    rcases hd n with h | h
    · rw [h, abs_zero]; linarith
    · exact h.2
  by_cases hA : ∀ n, j ≤ n → d n = 0
  · left
    set σ : ℝ := ∑ n ∈ Finset.range N, d n * sS n with hσ
    have h1 : ∑ n ∈ Finset.range N, |d n| * sS n = ∑ n ∈ Finset.range (N + j), |d n| * sS n := by
      refine Finset.sum_subset (Finset.range_mono (by omega)) (fun x hx hxn => ?_)
      have : N ≤ x := by simpa using hxn
      rw [hN x this]; simp
    have h2 : ∑ n ∈ Finset.range j, |d n| * sS n = ∑ n ∈ Finset.range (N + j), |d n| * sS n := by
      refine Finset.sum_subset (Finset.range_mono (by omega)) (fun x hx hxn => ?_)
      have : j ≤ x := by simpa using hxn
      rw [hA x this]; simp
    have h3 : ∑ n ∈ Finset.range j, |d n| * sS n ≤ ∑ n ∈ Finset.range j, c1 * sS n :=
      Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right (hcd n) (sS_pos n).le)
    have h4 : ∑ n ∈ Finset.range j, c1 * sS n ≤ c1 * (2 * sS (j - 1)) := by
      rw [← Finset.mul_sum]
      have := geom_sS (j - 1)
      rw [Nat.sub_add_cancel hj1] at this
      exact mul_le_mul_of_nonneg_left this (by linarith)
    have h5 : |σ| ≤ ∑ n ∈ Finset.range N, |d n| * sS n := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [abs_mul, abs_of_pos (sS_pos n)]
    calc |σ| ≤ ∑ n ∈ Finset.range N, |d n| * sS n := h5
      _ = ∑ n ∈ Finset.range j, |d n| * sS n := by rw [h1, h2]
      _ ≤ c1 * (2 * sS (j - 1)) := h3.trans h4
      _ = 2 * c1 * sS (j - 1) := by ring
  · right
    push Not at hA
    obtain ⟨n1, hn1j, hn1⟩ := hA
    have hn1N : n1 < N := by
      by_contra hcon
      exact hn1 (hN n1 (not_lt.1 hcon))
    set S : Finset ℕ := (Finset.range N).filter (fun n => d n ≠ 0) with hS
    have hne : S.Nonempty := ⟨n1, by simp [hS, hn1N, hn1]⟩
    set T := S.max' hne with hT
    have hTS : T ∈ S := Finset.max'_mem S hne
    have hTN : T < N := by simpa [hS] using (Finset.mem_filter.1 hTS).1
    have hdT : d T ≠ 0 := (Finset.mem_filter.1 hTS).2
    have hT1 : n1 ≤ T := Finset.le_max' S n1 (by simp [hS, hn1N, hn1])
    have hup : ∀ n, T < n → d n = 0 := by
      intro n hn
      by_contra hdn
      have hnN : n < N := by
        by_contra hcon
        exact hdn (hN n (not_lt.1 hcon))
      have : n ∈ S := by simp [hS, hnN, hdn]
      have := Finset.le_max' S n this
      omega
    have hTj : j + 1 ≤ T := by
      have : j ≤ T := le_trans hn1j hT1
      have hne' : T ≠ j := fun h => hdT (h ▸ hdj)
      omega
    have hlb := lower_bound hc0 (by linarith) N0 hN0 hN0big d hd T (by omega) hdT hup N hTN
    have hsT : sS (j + 1) ≤ sS T := sS_mono hTj
    have : c0 * sS (j + 1) / 2 ≤ c0 * sS T / 2 := by
      have := mul_le_mul_of_nonneg_left hsT hc0.le
      linarith
    linarith

/-- **Lemma X (top index), quantitative form.** If `n ∉ A` is large, no `z = e + σ` with `|e| ≤ m`, `σ ∈ a₁S_A + … + a_kS_A`, satisfies
`γ₁ s_n ≤ |z| ≤ γ₂ s_n`. -/
theorem top_index (A : Set ℕ) (l : List ℝ) {m γ1 γ2 : ℝ} (hm : 0 ≤ m) (hγ1 : 0 < γ1) (hγ2 : 0 < γ2) :
    ∃ N1 : ℕ, ∀ n : ℕ, N1 ≤ n → n ∉ A → ∀ e σ : ℝ, |e| ≤ m → σ ∈ sumSetA A l →
      ¬ (γ1 * sS n ≤ |e + σ| ∧ |e + σ| ≤ γ2 * sS n) := by
  obtain ⟨c0, c1, hc0, hc1, hlow, hup⟩ := exists_consts (Cset l)
  obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt (4 * c1 / c0) (by norm_num : (1 : ℝ) < 2)
  set N0 : ℕ := n0 + 1 with hN0def
  have hN0 : 1 ≤ N0 := by omega
  have hN0big : ∀ T, N0 ≤ T → 4 * c1 ≤ c0 * 2 ^ (2 * T - 1) := by
    intro T hT
    have h1 : (2 : ℝ) ^ n0 ≤ 2 ^ (2 * T - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_lt_iff₀ hc0] at hn0
    nlinarith
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt ((γ2 + m + 1) / c0) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨n2, hn2⟩ := pow_unbounded_of_one_lt (4 * c1 / γ1) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨L, hL⟩ := sS_unbounded (2 * m / γ1 + 1)
  refine ⟨max (max (N0 + 1) (max n1 n2)) L, fun n hn hnA e σ he hσ => ?_⟩
  have hnN0 : N0 + 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnn1 : n1 ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hn
  have hnn2 : n2 ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hn
  have hnL : L ≤ n := le_trans (le_max_right _ _) hn
  rintro ⟨hlo, hhi⟩
  obtain ⟨N, d, hdC, hd0, hdA, hσd⟩ := rep_of_mem_sumSetA A l σ hσ
  have hd : ∀ k, d k = 0 ∨ (c0 ≤ |d k| ∧ |d k| ≤ c1) := by
    intro k
    by_cases hk : d k = 0
    · exact Or.inl hk
    · exact Or.inr ⟨hlow _ (hdC k) hk, hup _ (hdC k)⟩
  have hdn : d n = 0 := hdA n hnA
  have hdich := sigma_dichotomy hc0 hc1 N0 hN0 hN0big d hd N hd0 n (by omega) (by omega) hdn
  rw [← hσd] at hdich
  have hsn1 : 1 ≤ sS n := one_le_sS n
  have hsnL : 2 * m / γ1 + 1 < sS n := lt_of_lt_of_le hL (sS_mono hnL)
  have hmsn : m < γ1 / 2 * sS n := by
    have h1 : 2 * m / γ1 < sS n := by linarith
    rw [div_lt_iff₀ hγ1] at h1
    nlinarith
  have hn1' : 1 ≤ n := by omega
  have hsrel : sS n = sS (n - 1) * 2 ^ (2 * n - 1) := by
    have := sS_succ (n - 1)
    rwa [Nat.sub_add_cancel hn1', show 2 * (n - 1) + 1 = 2 * n - 1 by omega] at this
  have hsrel2 : sS (n + 1) = sS n * 2 ^ (2 * n + 1) := sS_succ n
  have habs1 : |σ| ≥ |e + σ| - m := by
    have h := abs_sub_abs_le_abs_sub (e + σ) e
    rw [add_sub_cancel_left] at h
    linarith
  have habs3 : |σ| ≤ |e + σ| + m := by
    have h := abs_sub (e + σ) e
    rw [add_sub_cancel_left] at h
    linarith
  rcases hdich with h | h
  · -- `|σ| ≤ 2 c₁ s_{n-1}`
    have hp : (4 * c1 / γ1) < 2 ^ (2 * n - 1) := by
      calc 4 * c1 / γ1 < 2 ^ n2 := hn2
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hnn2
        _ ≤ 2 ^ (2 * n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_lt_iff₀ hγ1] at hp
    have hsm := sS_pos (n - 1)
    have h3 : 2 * c1 * sS (n - 1) ≤ γ1 / 2 * sS n := by
      rw [hsrel]
      nlinarith [mul_le_mul_of_nonneg_right hp.le hsm.le]
    linarith
  · -- `|σ| ≥ c₀ s_{n+1} / 2`
    have hp : (γ2 + m + 1) / c0 < 2 ^ (2 * n) := by
      calc (γ2 + m + 1) / c0 < 2 ^ n1 := hn1
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hnn1
        _ ≤ 2 ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_lt_iff₀ hc0] at hp
    have hpow : (2 : ℝ) ^ (2 * n + 1) = 2 * 2 ^ (2 * n) := by rw [pow_succ]; ring
    have h4 : c0 * sS (n + 1) / 2 = c0 * 2 ^ (2 * n) * sS n := by
      rw [hsrel2, hpow]; ring
    rw [h4] at h
    nlinarith [mul_le_mul_of_nonneg_right hp.le (sS_pos n).le, mul_le_mul_of_nonneg_left hsn1 hm]

#print axioms top_index

end Lac
end PVG
