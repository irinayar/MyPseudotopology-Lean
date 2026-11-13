import Mathlib
import LeanCheck.PVGLacCount
import LeanCheck.PVGLacIdeal
import LeanCheck.PVGDiffFinite

/-!
# PVG: the arithmetic part of Lemma 8.78 of PVG_v34 (Lean check)

Scope. With `s_n = 2^(n²)` (`sS n`), `c_i = 3^i` (`cc i`) and `M_i = 3 i + 4` (`MM i`; then `M_i ≥ i + 2` and `2^(2 M_i - 1) ≥ c_i^3`), let
`E_i = {s_{n-k} - s_{m-l} + c_i (s_n - s_m) : 1 ≤ k, l ≤ i, k ≠ l, M_i ≤ n < m}` (`Ei i`) and `E = ⋃_{i ≥ 2} E_i` (`Eall`).

* `Ei_ne_zero` : `0 ∉ E_i` (Lemma 8.78(a));
* `Ei_not_mem_piece` : for every piece `[-m₀, m₀] + b₁ S + … + b_r S` (`sumSet l`) there is `i₀` such that no element of `E_i`, `i ≥ i₀`, lies in it
  (Lemma 8.78(b)); the proof is the largest-index argument with the lower bound `lower_bound`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise
open scoped Classical

namespace PVG
namespace Lac

/-- `c_i = 3^i`. -/
def cc (i : ℕ) : ℝ := 3 ^ i

/-- `M_i = 3 i + 4`. -/
def MM (i : ℕ) : ℕ := 3 * i + 4

/-- `E_i`. -/
def Ei (i : ℕ) : Set ℝ :=
  {y | ∃ k l n m : ℕ, 1 ≤ k ∧ k ≤ i ∧ 1 ≤ l ∧ l ≤ i ∧ k ≠ l ∧ MM i ≤ n ∧ n < m ∧
    y = sS (n - k) - sS (m - l) + cc i * (sS n - sS m)}

/-- `E = ⋃_{i ≥ 2} E_i`. -/
def Eall : Set ℝ := {y | ∃ i, 2 ≤ i ∧ y ∈ Ei i}

lemma cc_pos (i : ℕ) : 0 < cc i := by unfold cc; positivity

lemma cc_ge (i : ℕ) : (i : ℝ) ≤ cc i := by
  unfold cc
  have h1 : (i : ℝ) < 2 ^ i := by exact_mod_cast Nat.lt_two_pow_self
  have h2 : (2 : ℝ) ^ i ≤ 3 ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
  linarith

lemma three_le_cc {i : ℕ} (hi : 1 ≤ i) : 3 ≤ cc i := by
  unfold cc
  calc (3 : ℝ) = 3 ^ 1 := by norm_num
    _ ≤ 3 ^ i := pow_le_pow_right₀ (by norm_num) hi

lemma eight_le_sS {n m : ℕ} (hn : 1 ≤ n) (hnm : n < m) : 8 * sS n ≤ sS m := by
  have h1 : sS (n + 1) ≤ sS m := sS_mono (Nat.succ_le_of_lt hnm)
  have h2 : sS (n + 1) = sS n * 2 ^ (2 * n + 1) := sS_succ n
  have h3 : (8 : ℝ) ≤ 2 ^ (2 * n + 1) := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have := sS_pos n
  nlinarith

/-- **Lemma 8.78(a)**: `0 ∉ E_i`. -/
lemma Ei_ne_zero {i : ℕ} (hi : 1 ≤ i) {y : ℝ} (hy : y ∈ Ei i) : y ≠ 0 := by
  obtain ⟨k, l, n, m, hk1, hki, hl1, hli, hkl, hn, hnm, rfl⟩ := hy
  have hMMi : MM i = 3 * i + 4 := rfl
  have hMM : 4 ≤ MM i := by omega
  have h1 : 8 * sS (n - k) ≤ sS m := eight_le_sS (by omega) (by omega)
  have h2 : 8 * sS n ≤ sS m := eight_le_sS (by omega) hnm
  have h3 := sS_pos (m - l)
  have hc := three_le_cc hi
  have hm := sS_pos m
  have h4 : 3 * (sS m - sS n) ≤ cc i * (sS m - sS n) :=
    mul_le_mul_of_nonneg_right hc (by linarith)
  have h5 : cc i * (sS n - sS m) = -(cc i * (sS m - sS n)) := by ring
  have hneg : sS (n - k) - sS (m - l) + cc i * (sS n - sS m) < 0 := by
    rw [h5]; linarith
  exact hneg.ne

/-- The coefficient of `s_j` in `s_{n-k} - s_{m-l} + c (s_n - s_m)`. -/
noncomputable def ey (c : ℝ) (k l n m : ℕ) (j : ℕ) : ℝ :=
  (if j = n - k then 1 else 0) + (if j = m - l then -1 else 0) + (if j = n then c else 0) +
    (if j = m then -c else 0)

lemma ey_sum (c : ℝ) (k l n m N : ℕ) (h1 : n - k < N) (h2 : m - l < N) (h3 : n < N) (h4 : m < N) :
    ∑ j ∈ Finset.range N, ey c k l n m j * sS j = sS (n - k) - sS (m - l) + c * (sS n - sS m) := by
  have e : ∀ j, ey c k l n m j * sS j = (if j = n - k then (1 : ℝ) else 0) * sS j +
      (if j = m - l then (-1 : ℝ) else 0) * sS j + (if j = n then c else 0) * sS j +
      (if j = m then -c else 0) * sS j := by
    intro j; unfold ey; ring
  simp only [e, Finset.sum_add_distrib]
  rw [sum_ite_sS N (n - k) 1 h1, sum_ite_sS N (m - l) (-1) h2, sum_ite_sS N n c h3,
    sum_ite_sS N m (-c) h4]
  ring

lemma ey_cases {c : ℝ} {k l n m : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hn : 1 ≤ n) (hnm : n < m) (j : ℕ) :
    (j = m ∧ ey c k l n m j = -c) ∨ (j = n ∧ (ey c k l n m j = c ∨ ey c k l n m j = c - 1)) ∨
      (j ≠ n ∧ j ≠ m ∧ (ey c k l n m j = 0 ∨ ey c k l n m j = 1 ∨ ey c k l n m j = -1)) := by
  by_cases hjm : j = m
  · left
    refine ⟨hjm, ?_⟩
    have h1 : ¬ j = n - k := by omega
    have h2 : ¬ j = m - l := by omega
    have h3 : ¬ j = n := by omega
    simp only [ey, if_neg h1, if_neg h2, if_neg h3, if_pos hjm]
    ring
  · by_cases hjn : j = n
    · right; left
      refine ⟨hjn, ?_⟩
      have h1 : ¬ j = n - k := by omega
      by_cases h2 : j = m - l
      · right
        simp only [ey, if_neg h1, if_pos h2, if_pos hjn, if_neg hjm]
        ring
      · left
        simp only [ey, if_neg h1, if_neg h2, if_pos hjn, if_neg hjm]
        ring
    · right; right
      refine ⟨hjn, hjm, ?_⟩
      by_cases h1 : j = n - k
      · by_cases h2 : j = m - l
        · left
          simp only [ey, if_pos h1, if_pos h2, if_neg hjn, if_neg hjm]
          ring
        · right; left
          simp only [ey, if_pos h1, if_neg h2, if_neg hjn, if_neg hjm]
          ring
      · by_cases h2 : j = m - l
        · right; right
          simp only [ey, if_neg h1, if_pos h2, if_neg hjn, if_neg hjm]
          ring
        · left
          simp only [ey, if_neg h1, if_neg h2, if_neg hjn, if_neg hjm]
          ring

/-- **Lemma 8.78(b)**: a piece `[-m₀, m₀] + b₁ S + … + b_r S` contains no element of `E_i` for `i` large. -/
theorem Ei_not_mem_piece (m0 : ℝ) (l : List ℝ) :
    ∃ i0 : ℕ, ∀ i, i0 ≤ i → ∀ y ∈ Ei i, y ∉ Icc (-m0) m0 + sumSet l := by
  classical
  set F : Finset ℝ := Cset l ∪ (Cset l).image (fun d => -d) ∪ (Cset l).image (fun d => 1 - d) ∪
    (Cset l).image (fun d => -1 - d) with hF
  obtain ⟨c0, c1, hc0, hc1, hlow, hup⟩ := exists_consts F
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (4 * (c1 + 2) / c0) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n1 + ⌈c0 + c1⌉₊ + ⌈2 * m0 / c0⌉₊ + 2, ?_⟩
  intro i hi y hy hmem
  obtain ⟨t, ht, w, hw, hty⟩ := hmem
  obtain ⟨k, l', n, m, hk1, hki, hl1, hli, hkl, hn, hnm, rfl⟩ := hy
  have hMMi : MM i = 3 * i + 4 := rfl
  set c : ℝ := cc i with hcdef
  have hi1 : 1 ≤ i := by omega
  have hceil : c0 + c1 ≤ (⌈c0 + c1⌉₊ : ℝ) := Nat.le_ceil _
  have hceil2 : 2 * m0 / c0 ≤ (⌈2 * m0 / c0⌉₊ : ℝ) := Nat.le_ceil _
  have hi' : (⌈c0 + c1⌉₊ : ℝ) + 2 ≤ (i : ℝ) := by exact_mod_cast (by omega : ⌈c0 + c1⌉₊ + 2 ≤ i)
  have hi'' : (⌈2 * m0 / c0⌉₊ : ℝ) + 2 ≤ (i : ℝ) := by
    exact_mod_cast (by omega : ⌈2 * m0 / c0⌉₊ + 2 ≤ i)
  have hcge : c0 + c1 + 2 ≤ c := by
    have := cc_ge i
    linarith
  -- the representation of `w`
  obtain ⟨N, d, hd, hd0, hw'⟩ := rep_of_mem_sumSet l w hw
  have hdF : ∀ j, d j ∈ F := by
    intro j
    simp only [hF, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (hd j)))
  have hdb : ∀ j, |d j| ≤ c1 := fun j => hup _ (hdF j)
  set N' : ℕ := max N (m + 1) with hN'
  have hmN' : m < N' := lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_right _ _)
  have hNN' : N ≤ N' := le_max_left _ _
  set D : ℕ → ℝ := fun j => ey c k l' n m j - d j with hD
  have hdD : ∀ j, D j = 0 ∨ (c0 ≤ |D j| ∧ |D j| ≤ c1 + c + 1) := by
    intro j
    have hdj := abs_le.1 (hdb j)
    rcases ey_cases (c := c) hk1 hl1 (by omega) hnm j with ⟨hjm, hey⟩ | ⟨hjn, hey⟩ | ⟨hjn, hjm, hey⟩
    · right
      have hDj : D j = -c - d j := by simp only [hD, hey]
      have hneg : D j < 0 := by rw [hDj]; linarith
      rw [abs_of_neg hneg, hDj]
      constructor <;> linarith
    · right
      have hDj : ∃ δ : ℝ, (δ = 0 ∨ δ = 1) ∧ D j = c - δ - d j := by
        rcases hey with h | h
        · exact ⟨0, Or.inl rfl, by simp only [hD, h]; ring⟩
        · exact ⟨1, Or.inr rfl, by simp only [hD, h]⟩
      obtain ⟨δ, hδ, hDj⟩ := hDj
      have hδ' : 0 ≤ δ ∧ δ ≤ 1 := by rcases hδ with h | h <;> subst h <;> norm_num
      have hpos : 0 < D j := by rw [hDj]; linarith
      rw [abs_of_pos hpos, hDj]
      constructor <;> linarith
    · by_cases hz : D j = 0
      · left; exact hz
      · right
        have hmemF : D j ∈ F := by
          rcases hey with h | h | h
          · have : D j = -d j := by simp only [hD, h]; ring
            rw [this]
            simp only [hF, Finset.mem_union, Finset.mem_image]
            exact Or.inl (Or.inl (Or.inr ⟨d j, hd j, rfl⟩))
          · have : D j = 1 - d j := by simp only [hD, h]
            rw [this]
            simp only [hF, Finset.mem_union, Finset.mem_image]
            exact Or.inl (Or.inr ⟨d j, hd j, rfl⟩)
          · have : D j = -1 - d j := by simp only [hD, h]
            rw [this]
            simp only [hF, Finset.mem_union, Finset.mem_image]
            exact Or.inr ⟨d j, hd j, rfl⟩
        exact ⟨hlow _ hmemF hz, by have := hup _ hmemF; linarith [cc_pos i]⟩
  have hDm : D m ≠ 0 := by
    have h := hdD m
    rcases ey_cases (c := c) hk1 hl1 (by omega) hnm m with ⟨_, hey⟩ | ⟨hjn, _⟩ | ⟨_, hjm, _⟩
    · have hdj := abs_le.1 (hdb m)
      have : D m = -c - d m := by simp only [hD, hey]
      rw [this]
      intro h0
      linarith
    · omega
    · exact absurd rfl hjm
  have hDzero : ∀ j, N' ≤ j → D j = 0 := by
    intro j hj
    have h1 : j ≠ n - k := by omega
    have h2 : j ≠ m - l' := by omega
    have h3 : j ≠ n := by omega
    have h4 : j ≠ m := by omega
    have h5 : N ≤ j := le_trans hNN' hj
    simp [hD, ey, h1, h2, h3, h4, hd0 j h5]
  have hdsum : ∑ j ∈ Finset.range N', d j * sS j = w := by
    rw [hw']
    have hle : N ≤ N' := hNN'
    rw [← Finset.sum_range_add_sum_Ico _ hle]
    have : ∑ j ∈ Finset.Ico N N', d j * sS j = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [hd0 j (Finset.mem_Ico.1 hj).1]; simp)
    rw [this, add_zero]
  have hsum : ∑ j ∈ Finset.range N', D j * sS j = t := by
    have e : ∀ j, D j * sS j = ey c k l' n m j * sS j - d j * sS j := by
      intro j; simp only [hD]; ring
    simp only [e, Finset.sum_sub_distrib]
    rw [ey_sum c k l' n m N' (by omega) (by omega) (by omega) hmN', hdsum]
    linarith [hty]
  -- the top nonzero index
  set S : Finset ℕ := (Finset.range N').filter (fun j => D j ≠ 0) with hS
  have hmS : m ∈ S := by simp [hS, hmN', hDm]
  have hSne : S.Nonempty := ⟨m, hmS⟩
  set T : ℕ := S.max' hSne with hT
  have hTS : T ∈ S := S.max'_mem hSne
  have hTN' : T < N' := by simpa [hS] using (Finset.mem_filter.1 hTS).1
  have hDT : D T ≠ 0 := (Finset.mem_filter.1 hTS).2
  have hmT : m ≤ T := S.le_max' m hmS
  have hupT : ∀ j, T < j → D j = 0 := by
    intro j hj
    by_contra hne
    by_cases hjN : j < N'
    · have : j ∈ S := by simp [hS, hjN, hne]
      have := S.le_max' j this
      omega
    · exact hne (hDzero j (not_lt.1 hjN))
  -- the lower bound
  have hN0big : ∀ T', MM i ≤ T' → 4 * (c1 + c + 1) ≤ c0 * 2 ^ (2 * T' - 1) := by
    intro T' hT'
    have hlt : 4 * (c1 + 2) / c0 < 2 ^ n1 := hn1
    rw [div_lt_iff₀ hc0] at hlt
    have hc3 : c = 3 ^ i := rfl
    have h4 : (1 : ℝ) ≤ 3 ^ i := one_le_pow₀ (by norm_num)
    have h3 : (3 : ℝ) ^ i ≤ 2 ^ (2 * i) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) i
    have h5 : (2 : ℝ) ^ (2 * i) * 2 ^ n1 = 2 ^ (2 * i + n1) := (pow_add _ _ _).symm
    have h6 : (2 : ℝ) ^ (2 * i + n1) ≤ 2 ^ (2 * T' - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h7 : (3 : ℝ) ^ i * 2 ^ n1 ≤ 2 ^ (2 * T' - 1) := by
      calc (3 : ℝ) ^ i * 2 ^ n1 ≤ 2 ^ (2 * i) * 2 ^ n1 :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = 2 ^ (2 * i + n1) := h5
        _ ≤ 2 ^ (2 * T' - 1) := h6
    calc 4 * (c1 + c + 1) ≤ 4 * (c1 + 2) * 3 ^ i := by rw [hc3]; nlinarith
      _ ≤ (2 ^ n1 * c0) * 3 ^ i := mul_le_mul_of_nonneg_right hlt.le (by positivity)
      _ = c0 * (3 ^ i * 2 ^ n1) := by ring
      _ ≤ c0 * 2 ^ (2 * T' - 1) := mul_le_mul_of_nonneg_left h7 hc0.le
  have hN0T : MM i ≤ T := by omega
  have hc1c : 0 ≤ c1 + c + 1 := by linarith [cc_pos i]
  have hlb := lower_bound hc0 hc1c (MM i) (by omega) hN0big D hdD T hN0T hDT hupT N' hTN'
  rw [hsum] at hlb
  have ht' : |t| ≤ m0 := abs_le.2 ⟨ht.1, ht.2⟩
  have h1 : c0 * sS T / 2 ≤ m0 := le_trans hlb ht'
  have h2 : (T : ℝ) ≤ sS T := sS_ge T
  have h3 : (i : ℝ) ≤ T := by exact_mod_cast (by omega : i ≤ T)
  have h4 : 2 * m0 / c0 ≤ i - 2 := by linarith
  have h5 : 2 * m0 ≤ (i - 2) * c0 := (div_le_iff₀ hc0).1 h4
  have h6 : c0 * (i : ℝ) ≤ c0 * sS T := mul_le_mul_of_nonneg_left (le_trans h3 h2) hc0.le
  nlinarith

end Lac
end PVG
