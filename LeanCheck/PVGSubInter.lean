import Mathlib
import LeanCheck.PVGSubMain

/-!
# PVG: `I_A ∩ I_B = I_{A ∩ B}` (Lean check)

Scope. Theorem 8.63 (d) of PVG_v27, Addendum N2 of the research note. Two expansions `σ = ∑ d_n s_n` (supported in `A`) and `σ' = ∑ d'_n s_n`
(supported in `B`) whose difference is bounded agree above a bound (the lower bound for the top coefficient), so the high part of `σ` is
supported in `A ∩ B` and is a sum of at most `k` terms with coefficients from the finite set of signed subset sums, hence an element of
`c₁S_{A∩B} + …` for a fixed list of coefficients.

* `rep2_of_mem_sumSetA`: the representation of `PVGSubGap` with the support in `A ∩ [1,∞)` and with at most `k` nonzero terms;
* `agree_above`: two such expansions with bounded difference agree above a bound `N₁` that depends only on the coefficient lists and the bound;
* `finite_sum_mem`: a sum of at most `k` terms `d_n s_n` with `d_n` in a finite set and `n ∈ A'` lies in `sumSetA A' (coefficient list)`;
* `IA_inter`, `IA_inter_iff`, `subConv_inter_iff`, `subConv_inter_coarsest`: the theorem.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise Filter Topology
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-- Representation with support in `A ∩ [1,∞)` and at most `l.length` nonzero terms. -/
lemma rep2_of_mem_sumSetA (A : Set ℕ) : ∀ (l : List ℝ) (x : ℝ), x ∈ sumSetA A l →
    ∃ (N : ℕ) (d : ℕ → ℝ), (∀ n, d n ∈ Cset l) ∧ (∀ n, N ≤ n → d n = 0) ∧ (∀ n, d n ≠ 0 → n ∈ A ∧ 1 ≤ n) ∧
      ((Finset.range N).filter (fun n => d n ≠ 0)).card ≤ l.length ∧ x = ∑ n ∈ Finset.range N, d n * sS n
  | [], x, hx => by
    have : x = 0 := hx
    exact ⟨0, fun _ => 0, fun n => by simp [Cset], fun _ _ => rfl, fun n h => absurd rfl h, by simp, by simp [this]⟩
  | a :: l, x, hx => by
    obtain ⟨c, hc, y, hy, rfl⟩ := mem_sumSetA_cons.1 hx
    obtain ⟨N, d, hd, hd0, hdA, hcard, hyd⟩ := rep2_of_mem_sumSetA A l y hy
    rcases hc with hc0 | ⟨j, hjA, hj1, hcj⟩
    · refine ⟨N, d, fun n => Cset_sub a l (hd n), hd0, hdA, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · simp [hc0, hyd]
    · have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → c = ε * sS j →
          ∃ (N' : ℕ) (d' : ℕ → ℝ), (∀ n, d' n ∈ Cset (a :: l)) ∧ (∀ n, N' ≤ n → d' n = 0) ∧
            (∀ n, d' n ≠ 0 → n ∈ A ∧ 1 ≤ n) ∧
            ((Finset.range N').filter (fun n => d' n ≠ 0)).card ≤ (a :: l).length ∧
            (a * c + y) = ∑ n ∈ Finset.range N', d' n * sS n := by
        intro ε hε hcε
        refine ⟨max N (j + 1), fun n => d n + (if n = j then ε * a else 0), ?_, ?_, ?_, ?_, ?_⟩
        · intro n
          by_cases hn : n = j
          · simp only [hn, ite_true]
            simp only [Cset, Finset.mem_union, Finset.mem_image]
            rcases hε with rfl | rfl
            · exact Or.inl (Or.inr ⟨d j, hd j, by ring⟩)
            · exact Or.inr ⟨d j, hd j, by ring⟩
          · simp only [hn, ite_false, add_zero]; exact Cset_sub a l (hd n)
        · intro n hn
          have h1 : N ≤ n := le_trans (le_max_left _ _) hn
          have h2 : n ≠ j := by
            have := le_trans (le_max_right _ _) hn; omega
          simp [hd0 n h1, h2]
        · intro n hn
          by_cases hnj : n = j
          · rw [hnj]; exact ⟨hjA, hj1⟩
          · apply hdA n
            intro h0
            apply hn
            simp [h0, hnj]
        · have hsub : (Finset.range (max N (j + 1))).filter (fun n => d n + (if n = j then ε * a else 0) ≠ 0) ⊆
              insert j ((Finset.range N).filter (fun n => d n ≠ 0)) := by
            intro n hn
            simp only [Finset.mem_filter, Finset.mem_range] at hn
            by_cases hnj : n = j
            · simp [hnj]
            · simp only [hnj, ite_false, add_zero] at hn
              simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
              right
              refine ⟨?_, hn.2⟩
              by_contra hcon
              exact hn.2 (hd0 n (not_lt.1 hcon))
          calc _ ≤ (insert j ((Finset.range N).filter (fun n => d n ≠ 0))).card := Finset.card_le_card hsub
            _ ≤ ((Finset.range N).filter (fun n => d n ≠ 0)).card + 1 := Finset.card_insert_le _ _
            _ ≤ (a :: l).length := by simp only [List.length_cons]; omega
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

lemma sum_range_extend (d : ℕ → ℝ) {N N2 : ℕ} (hN : ∀ n, N ≤ n → d n = 0) (h : N ≤ N2) :
    ∑ n ∈ Finset.range N2, d n * sS n = ∑ n ∈ Finset.range N, d n * sS n := by
  symm
  refine Finset.sum_subset (Finset.range_mono h) (fun n _ hn => ?_)
  have : N ≤ n := by simpa using hn
  rw [hN n this]; simp

/-- The top nonzero index of a finitely supported sequence. -/
lemma exists_top (d : ℕ → ℝ) (N : ℕ) (hN : ∀ n, N ≤ n → d n = 0) {n1 : ℕ} (h1 : d n1 ≠ 0) :
    ∃ T, n1 ≤ T ∧ d T ≠ 0 ∧ (∀ n, T < n → d n = 0) ∧ T < N := by
  have hn1N : n1 < N := by
    by_contra hcon
    exact h1 (hN n1 (not_lt.1 hcon))
  set S : Finset ℕ := (Finset.range N).filter (fun n => d n ≠ 0) with hS
  have hne : S.Nonempty := ⟨n1, by simp [hS, hn1N, h1]⟩
  set T := S.max' hne with hT
  have hTS : T ∈ S := Finset.max'_mem S hne
  have hTN : T < N := by simpa [hS] using (Finset.mem_filter.1 hTS).1
  have hdT : d T ≠ 0 := (Finset.mem_filter.1 hTS).2
  have hT1 : n1 ≤ T := Finset.le_max' S n1 (by simp [hS, hn1N, h1])
  refine ⟨T, hT1, hdT, ?_, hTN⟩
  intro n hn
  by_contra hdn
  have hnN : n < N := by
    by_contra hcon
    exact hdn (hN n (not_lt.1 hcon))
  have : n ∈ S := by simp [hS, hnN, hdn]
  have := Finset.le_max' S n this
  omega

/-- Two expansions supported in the finite coefficient sets, with bounded difference, agree above a bound. -/
lemma agree_above (l l' : List ℝ) (μ : ℝ) :
    ∃ N1 : ℕ, ∀ (d d' : ℕ → ℝ) (N : ℕ), (∀ n, d n ∈ Cset l) → (∀ n, d' n ∈ Cset l') →
      (∀ n, N ≤ n → d n = 0) → (∀ n, N ≤ n → d' n = 0) →
      |∑ n ∈ Finset.range N, d n * sS n - ∑ n ∈ Finset.range N, d' n * sS n| ≤ μ →
      ∀ n, N1 ≤ n → d n = d' n := by
  set F : Finset ℝ := (Cset l ×ˢ Cset l').image (fun p => p.1 - p.2) with hF
  obtain ⟨c0, c1, hc0, hc1, hlow, hup⟩ := exists_consts F
  obtain ⟨n0, hn0⟩ := pow_unbounded_of_one_lt (4 * c1 / c0) (by norm_num : (1 : ℝ) < 2)
  set N0 : ℕ := n0 + 1 with hN0def
  have hN0 : 1 ≤ N0 := by omega
  have hN0big : ∀ T, N0 ≤ T → 4 * c1 ≤ c0 * 2 ^ (2 * T - 1) := by
    intro T hT
    have h1 : (2 : ℝ) ^ n0 ≤ 2 ^ (2 * T - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_lt_iff₀ hc0] at hn0
    nlinarith
  obtain ⟨L, hL⟩ := sS_unbounded (2 * |μ| / c0)
  refine ⟨max N0 L, fun d d' N hd hd' hd0 hd0' hμ n hn => ?_⟩
  by_contra hne
  set δ : ℕ → ℝ := fun n => d n - d' n with hδ
  have hδF : ∀ n, δ n ∈ F := by
    intro n
    simp only [hF, Finset.mem_image, Finset.mem_product]
    exact ⟨(d n, d' n), ⟨hd n, hd' n⟩, rfl⟩
  have hδ' : ∀ k, δ k = 0 ∨ (c0 ≤ |δ k| ∧ |δ k| ≤ c1) := by
    intro k
    by_cases hk : δ k = 0
    · exact Or.inl hk
    · exact Or.inr ⟨hlow _ (hδF k) hk, hup _ (hδF k)⟩
  have hδ0 : ∀ k, N ≤ k → δ k = 0 := fun k hk => by simp [hδ, hd0 k hk, hd0' k hk]
  have hsumδ : ∑ k ∈ Finset.range N, δ k * sS k =
      ∑ k ∈ Finset.range N, d k * sS k - ∑ k ∈ Finset.range N, d' k * sS k := by
    simp only [hδ, sub_mul, Finset.sum_sub_distrib]
  have hδn : δ n ≠ 0 := fun h => hne (by simpa [hδ, sub_eq_zero] using h)
  obtain ⟨T, hnT, hdT, hup2, hTN⟩ := exists_top δ N hδ0 hδn
  have hlb := lower_bound hc0 (by linarith) N0 hN0 hN0big δ hδ' T
    (le_trans (le_trans (le_max_left _ _) hn) hnT) hdT hup2 N hTN
  rw [hsumδ] at hlb
  have hsT : sS L ≤ sS T := sS_mono (le_trans (le_trans (le_max_right _ _) hn) hnT)
  have h2 : 2 * |μ| / c0 < sS T := lt_of_lt_of_le hL hsT
  rw [div_lt_iff₀ hc0] at h2
  have h3 : c0 * sS T / 2 ≤ μ := le_trans hlb hμ
  have h4 : μ ≤ |μ| := le_abs_self μ
  linarith

/-- A sum of at most `k` terms `d_n s_n`, `n ∈ A'`, `d_n` in a finite set, lies in `sumSetA A'` of a fixed list. -/
lemma replicate_sum_mem (A' : Set ℕ) (c : ℝ) :
    ∀ (k : ℕ) (S : Finset ℕ), (∀ n ∈ S, n ∈ A' ∧ 1 ≤ n) → S.card ≤ k →
      c * ∑ n ∈ S, sS n ∈ sumSetA A' (List.replicate k c)
  | 0, S, _, hS => by
    have : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hS)
    subst this
    simp [sumSetA]
  | k + 1, S, hmem, hS => by
    by_cases hSe : S = ∅
    · subst hSe
      simpa using zero_mem_sumSetA A' (List.replicate (k + 1) c)
    · obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.2 hSe
      have hcard : (S.erase n).card ≤ k := by
        have := Finset.card_erase_of_mem hn
        omega
      have ih := replicate_sum_mem A' c k (S.erase n) (fun m hm => hmem m (Finset.mem_of_mem_erase hm)) hcard
      rw [List.replicate_succ]
      refine mem_sumSetA_cons.2 ⟨sS n, Or.inr ⟨n, (hmem n hn).1, (hmem n hn).2, Or.inl rfl⟩,
        c * ∑ m ∈ S.erase n, sS m, ih, ?_⟩
      rw [← Finset.add_sum_erase S sS hn]
      ring

lemma list_sum_mem (A' : Set ℕ) (k : ℕ) (S : Finset ℕ) (hmem : ∀ n ∈ S, n ∈ A' ∧ 1 ≤ n) (hS : S.card ≤ k)
    (d : ℕ → ℝ) (cs : List ℝ) :
    (cs.map (fun c => c * ∑ n ∈ S.filter (fun n => d n = c), sS n)).sum ∈
      sumSetA A' (cs.flatMap (fun c => List.replicate k c)) := by
  induction cs with
  | nil => simpa [sumSetA] using (zero_mem_sumSetA A' [])
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons]
    exact sumSetA_append_add A' _ _ _ _
      (replicate_sum_mem A' c k (S.filter (fun n => d n = c))
        (fun n hn => hmem n (Finset.mem_filter.1 hn).1)
        (le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hS)) ih

/-- A finitely supported sum with at most `k` nonzero terms from `A'` and coefficients in `C`. -/
lemma finite_sum_mem (A' : Set ℕ) (C : Finset ℝ) (k : ℕ) (d : ℕ → ℝ) (N : ℕ) (hd : ∀ n, d n ∈ C)
    (hA' : ∀ n, d n ≠ 0 → n ∈ A' ∧ 1 ≤ n) (hcard : ((Finset.range N).filter (fun n => d n ≠ 0)).card ≤ k) :
    ∑ n ∈ Finset.range N, d n * sS n ∈ sumSetA A' (C.toList.flatMap (fun c => List.replicate k c)) := by
  set S : Finset ℕ := (Finset.range N).filter (fun n => d n ≠ 0) with hS
  have hmem : ∀ n ∈ S, n ∈ A' ∧ 1 ≤ n := fun n hn => hA' n (Finset.mem_filter.1 hn).2
  have hsum : ∑ n ∈ Finset.range N, d n * sS n = ∑ n ∈ S, d n * sS n := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : d n = 0
    · simp [h]
    · simp [h]
  have hfib : ∑ n ∈ S, d n * sS n = ∑ c ∈ C, ∑ n ∈ S.filter (fun n => d n = c), d n * sS n :=
    (Finset.sum_fiberwise_of_maps_to (fun n _ => hd n) (fun n => d n * sS n)).symm
  have hfib2 : ∀ c ∈ C, ∑ n ∈ S.filter (fun n => d n = c), d n * sS n =
      c * ∑ n ∈ S.filter (fun n => d n = c), sS n := by
    intro c _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [(Finset.mem_filter.1 hn).2]
  rw [hsum, hfib, Finset.sum_congr rfl hfib2, ← Finset.sum_map_toList C (fun c => c * ∑ n ∈ S.filter (fun n => d n = c), sS n)]
  exact list_sum_mem A' k S hmem hcard d C.toList

/-! ### The theorem -/

lemma idx_inter {A B : Set ℕ} {n : ℕ} (hA : n ∈ A ∧ 1 ≤ n) (hB : n ∈ B ∧ 1 ≤ n) : n ∈ A ∩ B ∧ 1 ≤ n :=
  ⟨⟨hA.1, hB.1⟩, hA.2⟩

/-- **Theorem 8.63 (d).** `I_A ∩ I_B ⊆ I_{A ∩ B}`. -/
theorem IA_inter {A B : Set ℕ} {J : Set ℝ} (hA : J ∈ IA A) (hB : J ∈ IA B) : J ∈ IA (A ∩ B) := by
  obtain ⟨m, l, hJA⟩ := mem_IA_iff.1 hA
  obtain ⟨m', l', hJB⟩ := mem_IA_iff.1 hB
  obtain ⟨N1, hN1⟩ := agree_above l l' (|m| + |m'|)
  obtain ⟨c0, c1, hc0, hc1, hlow, hup⟩ := exists_consts (Cset l)
  rw [mem_IA_iff]
  refine ⟨m + 2 * c1 * sS N1, (Cset l).toList.flatMap (fun c => List.replicate l.length c), fun z hz => ?_⟩
  obtain ⟨y, σ, hy, hσ, hzσ⟩ := hJA z hz
  obtain ⟨y', σ', hy', hσ', hzσ'⟩ := hJB z hz
  obtain ⟨N, d, hd, hd0, hdA, hcard, hσd⟩ := rep2_of_mem_sumSetA A l σ hσ
  obtain ⟨M, d', hd', hd0', hdB, hcard', hσd'⟩ := rep2_of_mem_sumSetA B l' σ' hσ'
  have hσσ : σ - σ' = y' - y := by linarith
  have hext : ∀ n, max N M ≤ n → d n = 0 := fun n hn => hd0 n (le_trans (le_max_left _ _) hn)
  have hext' : ∀ n, max N M ≤ n → d' n = 0 := fun n hn => hd0' n (le_trans (le_max_right _ _) hn)
  have hs1 := sum_range_extend d hd0 (le_max_left N M)
  have hs2 := sum_range_extend d' hd0' (le_max_right N M)
  have hdiff : |∑ n ∈ Finset.range (max N M), d n * sS n - ∑ n ∈ Finset.range (max N M), d' n * sS n| ≤ |m| + |m'| := by
    rw [hs1, hs2, ← hσd, ← hσd', hσσ]
    calc |y' - y| ≤ |y'| + |y| := abs_sub _ _
      _ ≤ |m'| + |m| := add_le_add (hy'.trans (le_abs_self _)) (hy.trans (le_abs_self _))
      _ = |m| + |m'| := add_comm _ _
  have hagree := hN1 d d' (max N M) hd hd' hext hext' hdiff
  -- the high part
  set d2 : ℕ → ℝ := fun n => if N1 ≤ n then d n else 0 with hd2
  have hd2C : ∀ n, d2 n ∈ Cset l := by
    intro n
    simp only [hd2]
    split_ifs
    · exact hd n
    · exact zero_mem_Cset l
  have hd2A : ∀ n, d2 n ≠ 0 → n ∈ A ∩ B ∧ 1 ≤ n := by
    intro n hn
    simp only [hd2] at hn
    by_cases hn1 : N1 ≤ n
    · rw [if_pos hn1] at hn
      have h1 := hdA n hn
      have h2 : d' n ≠ 0 := by rw [← hagree n hn1]; exact hn
      exact idx_inter h1 (hdB n h2)
    · rw [if_neg hn1] at hn; exact absurd rfl hn
  have hd2card : ((Finset.range (max N M)).filter (fun n => d2 n ≠ 0)).card ≤ l.length := by
    refine le_trans (Finset.card_le_card ?_) hcard
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    refine ⟨?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      have := hd0 n hcon
      apply hn.2
      simp only [hd2]; split_ifs <;> simp [this]
    · intro h0
      apply hn.2
      simp only [hd2]; split_ifs <;> simp [h0]
  have hhigh := finite_sum_mem (A ∩ B) (Cset l) l.length d2 (max N M) hd2C hd2A hd2card
  -- the low part
  set low : ℝ := ∑ n ∈ Finset.range (max N M), (d n - d2 n) * sS n with hlowdef
  have hσsplit : σ = low + ∑ n ∈ Finset.range (max N M), d2 n * sS n := by
    rw [hσd, ← hs1, hlowdef, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    ring
  have hlowb : |low| ≤ 2 * c1 * sS N1 := by
    have h1 : ∀ n, |d n - d2 n| ≤ if n < N1 then c1 else 0 := by
      intro n
      simp only [hd2]
      by_cases hn : N1 ≤ n
      · have hn2 : ¬ n < N1 := not_lt.2 hn
        simp [hn, hn2]
      · have hn' : n < N1 := not_le.1 hn
        simp only [hn, if_false, hn', if_true, sub_zero]
        by_cases h0 : d n = 0
        · rw [h0, abs_zero]; linarith
        · exact hup _ (hd n)
    have h2 : |low| ≤ ∑ n ∈ Finset.range (max N M), |d n - d2 n| * sS n := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [abs_mul, abs_of_pos (sS_pos n)]
    have h3 : ∑ n ∈ Finset.range (max N M), |d n - d2 n| * sS n ≤
        ∑ n ∈ Finset.range (max N M), (if n < N1 then c1 * sS n else 0) := by
      refine Finset.sum_le_sum (fun n _ => ?_)
      by_cases hn : n < N1
      · simp only [hn, if_true]
        have := h1 n
        simp only [hn, if_true] at this
        exact mul_le_mul_of_nonneg_right this (sS_pos n).le
      · simp only [hn, if_false]
        have := h1 n
        simp only [hn, if_false] at this
        have h0 : |d n - d2 n| = 0 := le_antisymm this (abs_nonneg _)
        rw [h0]; simp
    have h4 : ∑ n ∈ Finset.range (max N M), (if n < N1 then c1 * sS n else 0) ≤
        ∑ n ∈ Finset.range N1, c1 * sS n := by
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => mul_nonneg (by linarith) (sS_pos n).le)
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact hn.2
    have h5 : ∑ n ∈ Finset.range N1, c1 * sS n ≤ c1 * (2 * sS (N1 - 1)) := by
      rw [← Finset.mul_sum]
      by_cases hN1z : N1 = 0
      · subst hN1z; simp; nlinarith [sS_pos 0]
      · have := geom_sS (N1 - 1)
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN1z)] at this
        exact mul_le_mul_of_nonneg_left this (by linarith)
    have h6 : sS (N1 - 1) ≤ sS N1 := sS_mono (Nat.sub_le _ _)
    have h7 := mul_le_mul_of_nonneg_left h6 (by linarith : (0 : ℝ) ≤ c1)
    linarith
  refine ⟨y + low, σ - low, ?_, ?_, ?_⟩
  · calc |y + low| ≤ |y| + |low| := abs_add_le _ _
      _ ≤ m + 2 * c1 * sS N1 := add_le_add hy hlowb
  · have : σ - low = ∑ n ∈ Finset.range (max N M), d2 n * sS n := by rw [hσsplit]; ring
    rw [this]; exact hhigh
  · rw [hzσ]; ring

theorem IA_inter_iff {A B : Set ℕ} {J : Set ℝ} : J ∈ IA (A ∩ B) ↔ J ∈ IA A ∧ J ∈ IA B :=
  ⟨fun h => ⟨IA_mono Set.inter_subset_left h, IA_mono Set.inter_subset_right h⟩, fun h => IA_inter h.1 h.2⟩

/-- `ξ_{A ∩ B}`-convergent filters are those that are `ξ_A`- and `ξ_B`-convergent. -/
theorem subConv_inter_iff {A B : Set ℕ} {F : Filter ℝ} {x : ℝ} :
    subConv (A ∩ B) F x ↔ subConv A F x ∧ subConv B F x := by
  constructor
  · intro h
    obtain ⟨J, hJF, hJI⟩ := h.2
    exact ⟨⟨h.1, J, hJF, IA_mono Set.inter_subset_left hJI⟩, ⟨h.1, J, hJF, IA_mono Set.inter_subset_right hJI⟩⟩
  · rintro ⟨⟨h1, J1, hJ1F, hJ1⟩, ⟨-, J2, hJ2F, hJ2⟩⟩
    refine ⟨h1, J1 ∩ J2, Filter.inter_mem hJ1F hJ2F, IA_inter ?_ ?_⟩
    · exact (IA_isIdeal A).mono hJ1 Set.inter_subset_left
    · exact (IA_isIdeal B).mono hJ2 Set.inter_subset_right

/-- `ξ_{A ∩ B}` is the coarsest PVG finer than `ξ_A` and `ξ_B`. -/
theorem subConv_inter_coarsest (A B : Set ℕ) :
    IsPVG (subConv (A ∩ B)) ∧ (∀ (F : Filter ℝ) (x : ℝ), subConv (A ∩ B) F x → subConv A F x) ∧
      (∀ (F : Filter ℝ) (x : ℝ), subConv (A ∩ B) F x → subConv B F x) ∧
      ∀ conv : Filter ℝ → ℝ → Prop, IsPVG conv → (∀ F x, conv F x → subConv A F x) →
        (∀ F x, conv F x → subConv B F x) → ∀ F x, conv F x → subConv (A ∩ B) F x :=
  ⟨subConv_isPVG _, fun F x h => (subConv_inter_iff.1 h).1, fun F x h => (subConv_inter_iff.1 h).2,
    fun conv _ hA hB F x h => subConv_inter_iff.2 ⟨hA F x h, hB F x h⟩⟩

#print axioms IA_inter
#print axioms subConv_inter_coarsest

end Lac
end PVG
