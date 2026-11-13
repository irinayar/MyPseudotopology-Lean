import Mathlib
import LeanCheck.PVGNotGroupArith

/-!
# PVG: Lemma 8.78(a), (b) for four arbitrary positions (Lean check)

Scope. `PVGNotGroupArith` proves Lemma 8.78(a), (b) for the positions `(n - k, m - l, n, m)`. Here the same arithmetic is proved for four
**arbitrary indices** `p₁, p₂, p₃, p₄` with `p₁ < p₄`, `p₂ < p₄`, `p₃ < p₄`, `p₁ ≠ p₃`, `M_i ≤ p₃`: the numbers
`s_{p₁} - s_{p₂} + c_i (s_{p₃} - s_{p₄})` do not lie in a fixed piece `[-m₀, m₀] + b₁ S + … + b_r S` for `i` large (`pos_not_mem_piece`), and are
nonzero (`pos_ne_zero`). Applied to `p = (φ(n-k), φ(m-l), φ n, φ m)` for a strictly increasing `φ` this gives the version of Lemma 8.78 for
the lacunary subsequences `s_{φ j}` (infinite sets `A` of indices), used in `PVGNotGroupA`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise
open scoped Classical

namespace PVG
namespace Lac

/-- The coefficient of `s_j` in `s_{p₁} - s_{p₂} + c (s_{p₃} - s_{p₄})`. -/
noncomputable def eyP (c : ℝ) (p1 p2 p3 p4 : ℕ) (j : ℕ) : ℝ :=
  (if j = p1 then 1 else 0) + (if j = p2 then -1 else 0) + (if j = p3 then c else 0) +
    (if j = p4 then -c else 0)

lemma eyP_sum (c : ℝ) (p1 p2 p3 p4 N : ℕ) (h1 : p1 < N) (h2 : p2 < N) (h3 : p3 < N) (h4 : p4 < N) :
    ∑ j ∈ Finset.range N, eyP c p1 p2 p3 p4 j * sS j = sS p1 - sS p2 + c * (sS p3 - sS p4) := by
  have e : ∀ j, eyP c p1 p2 p3 p4 j * sS j = (if j = p1 then (1 : ℝ) else 0) * sS j +
      (if j = p2 then (-1 : ℝ) else 0) * sS j + (if j = p3 then c else 0) * sS j +
      (if j = p4 then -c else 0) * sS j := by
    intro j; unfold eyP; ring
  simp only [e, Finset.sum_add_distrib]
  rw [sum_ite_sS N p1 1 h1, sum_ite_sS N p2 (-1) h2, sum_ite_sS N p3 c h3, sum_ite_sS N p4 (-c) h4]
  ring

lemma eyP_cases {c : ℝ} {p1 p2 p3 p4 : ℕ} (h14 : p1 < p4) (h24 : p2 < p4) (h34 : p3 < p4)
    (h13 : p1 ≠ p3) (j : ℕ) :
    (j = p4 ∧ eyP c p1 p2 p3 p4 j = -c) ∨
      (j = p3 ∧ (eyP c p1 p2 p3 p4 j = c ∨ eyP c p1 p2 p3 p4 j = c - 1)) ∨
      (j ≠ p3 ∧ j ≠ p4 ∧ (eyP c p1 p2 p3 p4 j = 0 ∨ eyP c p1 p2 p3 p4 j = 1 ∨
        eyP c p1 p2 p3 p4 j = -1)) := by
  by_cases hjm : j = p4
  · left
    refine ⟨hjm, ?_⟩
    have h1 : ¬ j = p1 := by omega
    have h2 : ¬ j = p2 := by omega
    have h3 : ¬ j = p3 := by omega
    simp only [eyP, if_neg h1, if_neg h2, if_neg h3, if_pos hjm]
    ring
  · by_cases hjn : j = p3
    · right; left
      refine ⟨hjn, ?_⟩
      have h1 : ¬ j = p1 := by omega
      by_cases h2 : j = p2
      · right
        simp only [eyP, if_neg h1, if_pos h2, if_pos hjn, if_neg hjm]
        ring
      · left
        simp only [eyP, if_neg h1, if_neg h2, if_pos hjn, if_neg hjm]
        ring
    · right; right
      refine ⟨hjn, hjm, ?_⟩
      by_cases h1 : j = p1
      · by_cases h2 : j = p2
        · left
          simp only [eyP, if_pos h1, if_pos h2, if_neg hjn, if_neg hjm]
          ring
        · right; left
          simp only [eyP, if_pos h1, if_neg h2, if_neg hjn, if_neg hjm]
          ring
      · by_cases h2 : j = p2
        · right; right
          simp only [eyP, if_neg h1, if_pos h2, if_neg hjn, if_neg hjm]
          ring
        · left
          simp only [eyP, if_neg h1, if_neg h2, if_neg hjn, if_neg hjm]
          ring

/-- Nonvanishing: `s_{p₁} - s_{p₂} + c_i (s_{p₃} - s_{p₄}) ≠ 0`. -/
lemma pos_ne_zero {i : ℕ} (hi : 1 ≤ i) {p1 p2 p3 p4 : ℕ} (hp1 : 1 ≤ p1) (hp3 : 1 ≤ p3)
    (h14 : p1 < p4) (h34 : p3 < p4) :
    sS p1 - sS p2 + cc i * (sS p3 - sS p4) ≠ 0 := by
  have h1 : 8 * sS p1 ≤ sS p4 := eight_le_sS hp1 h14
  have h2 : 8 * sS p3 ≤ sS p4 := eight_le_sS hp3 h34
  have h3 := sS_pos p2
  have hc := three_le_cc hi
  have hm := sS_pos p4
  have h4 : 3 * (sS p4 - sS p3) ≤ cc i * (sS p4 - sS p3) :=
    mul_le_mul_of_nonneg_right hc (by linarith)
  have h5 : cc i * (sS p3 - sS p4) = -(cc i * (sS p4 - sS p3)) := by ring
  have hneg : sS p1 - sS p2 + cc i * (sS p3 - sS p4) < 0 := by
    rw [h5]; linarith
  exact hneg.ne

/-- A piece `[-m₀, m₀] + b₁ S + … + b_r S` contains no `s_{p₁} - s_{p₂} + c_i (s_{p₃} - s_{p₄})` for `i` large. -/
theorem pos_not_mem_piece (m0 : ℝ) (l : List ℝ) :
    ∃ i0 : ℕ, ∀ i, i0 ≤ i → ∀ p1 p2 p3 p4 : ℕ, p1 < p4 → p2 < p4 → p3 < p4 → p1 ≠ p3 → MM i ≤ p3 →
      sS p1 - sS p2 + cc i * (sS p3 - sS p4) ∉ Icc (-m0) m0 + sumSet l := by
  classical
  set F : Finset ℝ := Cset l ∪ (Cset l).image (fun d => -d) ∪ (Cset l).image (fun d => 1 - d) ∪
    (Cset l).image (fun d => -1 - d) with hF
  obtain ⟨c0, c1, hc0, hc1, hlow, hup⟩ := exists_consts F
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (4 * (c1 + 2) / c0) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n1 + ⌈c0 + c1⌉₊ + ⌈2 * m0 / c0⌉₊ + 2, ?_⟩
  intro i hi p1 p2 p3 p4 h14 h24 h34 h13 hMp hmem
  obtain ⟨t, ht, w, hw, hty⟩ := hmem
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
  set N' : ℕ := max N (p4 + 1) with hN'
  have hmN' : p4 < N' := lt_of_lt_of_le (Nat.lt_succ_self p4) (le_max_right _ _)
  have hNN' : N ≤ N' := le_max_left _ _
  set D : ℕ → ℝ := fun j => eyP c p1 p2 p3 p4 j - d j with hD
  have hdD : ∀ j, D j = 0 ∨ (c0 ≤ |D j| ∧ |D j| ≤ c1 + c + 1) := by
    intro j
    have hdj := abs_le.1 (hdb j)
    rcases eyP_cases (c := c) h14 h24 h34 h13 j with ⟨hjm, hey⟩ | ⟨hjn, hey⟩ | ⟨hjn, hjm, hey⟩
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
  have hDm : D p4 ≠ 0 := by
    have h := hdD p4
    rcases eyP_cases (c := c) h14 h24 h34 h13 p4 with ⟨_, hey⟩ | ⟨hjn, _⟩ | ⟨_, hjm, _⟩
    · have hdj := abs_le.1 (hdb p4)
      have : D p4 = -c - d p4 := by simp only [hD, hey]
      rw [this]
      intro h0
      linarith
    · omega
    · exact absurd rfl hjm
  have hDzero : ∀ j, N' ≤ j → D j = 0 := by
    intro j hj
    have h1 : j ≠ p1 := by omega
    have h2 : j ≠ p2 := by omega
    have h3 : j ≠ p3 := by omega
    have h4 : j ≠ p4 := by omega
    have h5 : N ≤ j := le_trans hNN' hj
    simp [hD, eyP, h1, h2, h3, h4, hd0 j h5]
  have hdsum : ∑ j ∈ Finset.range N', d j * sS j = w := by
    rw [hw']
    have hle : N ≤ N' := hNN'
    rw [← Finset.sum_range_add_sum_Ico _ hle]
    have : ∑ j ∈ Finset.Ico N N', d j * sS j = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [hd0 j (Finset.mem_Ico.1 hj).1]; simp)
    rw [this, add_zero]
  have hsum : ∑ j ∈ Finset.range N', D j * sS j = t := by
    have e : ∀ j, D j * sS j = eyP c p1 p2 p3 p4 j * sS j - d j * sS j := by
      intro j; simp only [hD]; ring
    simp only [e, Finset.sum_sub_distrib]
    rw [eyP_sum c p1 p2 p3 p4 N' (by omega) (by omega) (by omega) hmN', hdsum]
    linarith [hty]
  -- the top nonzero index
  set S : Finset ℕ := (Finset.range N').filter (fun j => D j ≠ 0) with hS
  have hmS : p4 ∈ S := by simp [hS, hmN', hDm]
  have hSne : S.Nonempty := ⟨p4, hmS⟩
  set T : ℕ := S.max' hSne with hT
  have hTS : T ∈ S := S.max'_mem hSne
  have hTN' : T < N' := by simpa [hS] using (Finset.mem_filter.1 hTS).1
  have hDT : D T ≠ 0 := (Finset.mem_filter.1 hTS).2
  have hmT : p4 ≤ T := S.le_max' p4 hmS
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
