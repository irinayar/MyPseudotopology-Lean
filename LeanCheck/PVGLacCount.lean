import Mathlib

/-!
# PVG: the lacunary set `S` and its sum sets (Lean check): the counting lemma

Scope. First module of the formalization of Section 7 of `PVG_v19` ("A lacunary ideal"). With `s_n = 2^(n²)` and
`S = {0} ∪ {±s_n : n ≥ 1}`, `sumSet [a₁,…,a_k] = a₁S + … + a_kS`.

* `rep_of_mem_sumSet`: every element of `sumSet l` is `∑_n d_n s_n` with all `d_n` in the finite set `Cset l` of signed subset
  sums of the coefficients (and `d_n = 0` for large `n`);
* `lower_bound`: if the top nonzero coefficient sits at an index `T ≥ N₀` then `|∑ d_n s_n| ≥ c₀ s_T / 2`
  (`s_{n+1}/s_n → ∞`);
* `count_bound` (counting lemma, Lemma 7.1 in a form with power saving): for every `ρ > 0` there is `K` such that for every `L`
  the set `sumSet l ∩ [-ρ s_L, ρ s_L]` is finite with `ncard² ≤ K s_L`, i.e. `ncard ≤ √K √(s_L)`. The article states the sharper
  polylogarithmic bound `K (log r)^k`; the power saving `ncard = O(√r)` at the scales `r = ρ s_L` is what Lemmas 7.2 and 7.3 use
  (the measure of `[-m,m] + Σ` in `[-r,r]` and the Borel–Cantelli sum).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Finset Pointwise Set
open scoped Classical

namespace PVG
namespace Lac

/-- `s_n = 2^(n²)`. -/
def sS (n : ℕ) : ℝ := 2 ^ (n ^ 2)

lemma sS_pos (n : ℕ) : 0 < sS n := by unfold sS; positivity

lemma one_le_sS (n : ℕ) : 1 ≤ sS n := by unfold sS; exact one_le_pow₀ (by norm_num)

lemma sS_succ (n : ℕ) : sS (n + 1) = sS n * 2 ^ (2 * n + 1) := by
  unfold sS; rw [← pow_add]; congr 1; ring

lemma sS_mono {n m : ℕ} (h : n ≤ m) : sS n ≤ sS m := by
  unfold sS
  exact pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_left h 2)

/-- The lacunary set `S = {0} ∪ {±s_n : n ≥ 1}`. -/
def Sset : Set ℝ := {x | x = 0 ∨ ∃ n : ℕ, 1 ≤ n ∧ (x = sS n ∨ x = -sS n)}

lemma zero_mem_Sset : (0 : ℝ) ∈ Sset := Or.inl rfl

/-- `a₁S + … + a_kS`. -/
def sumSet : List ℝ → Set ℝ
  | [] => {0}
  | a :: l => a • Sset + sumSet l

lemma zero_mem_sumSet : ∀ l : List ℝ, (0 : ℝ) ∈ sumSet l
  | [] => rfl
  | a :: l => ⟨0, ⟨0, zero_mem_Sset, by simp⟩, 0, zero_mem_sumSet l, by simp⟩

/-- The finite set of signed subset sums of the coefficients. -/
noncomputable def Cset : List ℝ → Finset ℝ
  | [] => {0}
  | a :: l => Cset l ∪ (Cset l).image (· + a) ∪ (Cset l).image (· - a)

lemma zero_mem_Cset : ∀ l : List ℝ, (0 : ℝ) ∈ Cset l
  | [] => by simp [Cset]
  | a :: l => by
    simp only [Cset, Finset.mem_union]
    exact Or.inl (Or.inl (zero_mem_Cset l))

lemma Cset_sub (a : ℝ) (l : List ℝ) : Cset l ⊆ Cset (a :: l) := by
  intro x hx; simp only [Cset, Finset.mem_union]; exact Or.inl (Or.inl hx)

/-- Representation of the elements of `sumSet l`. -/
lemma rep_of_mem_sumSet : ∀ (l : List ℝ) (x : ℝ), x ∈ sumSet l →
    ∃ (N : ℕ) (d : ℕ → ℝ), (∀ n, d n ∈ Cset l) ∧ (∀ n, N ≤ n → d n = 0) ∧
      x = ∑ n ∈ Finset.range N, d n * sS n
  | [], x, hx => by
    have : x = 0 := hx
    exact ⟨0, fun _ => 0, fun n => by simp [Cset], fun _ _ => rfl, by simp [this]⟩
  | a :: l, x, hx => by
    obtain ⟨u, ⟨c, hc, rfl⟩, y, hy, rfl⟩ := hx
    obtain ⟨N, d, hd, hd0, hyd⟩ := rep_of_mem_sumSet l y hy
    rcases hc with hc0 | ⟨j, hj, hcj⟩
    · refine ⟨N, d, fun n => Cset_sub a l (hd n), hd0, ?_⟩
      simp [hc0, hyd]
    · -- `c = ε s_j`
      have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → c = ε * sS j →
          ∃ (N' : ℕ) (d' : ℕ → ℝ), (∀ n, d' n ∈ Cset (a :: l)) ∧ (∀ n, N' ≤ n → d' n = 0) ∧
            (a • c + y) = ∑ n ∈ Finset.range N', d' n * sS n := by
        intro ε hε hcε
        refine ⟨max N (j + 1), fun n => d n + (if n = j then ε * a else 0), ?_, ?_, ?_⟩
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
          rw [hcε, smul_eq_mul]; ring
      rcases hcj with h | h
      · obtain ⟨N', d', h1, h2, h3⟩ := key 1 (Or.inl rfl) (by rw [h]; ring)
        exact ⟨N', d', h1, h2, h3⟩
      · obtain ⟨N', d', h1, h2, h3⟩ := key (-1) (Or.inr rfl) (by rw [h]; ring)
        exact ⟨N', d', h1, h2, h3⟩

/-- `∑_{n ≤ N} s_n ≤ 2 s_N`. -/
lemma geom_sS (N : ℕ) : ∑ n ∈ Finset.range (N + 1), sS n ≤ 2 * sS N := by
  induction N with
  | zero => norm_num [sS]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h1 : 2 * sS N ≤ sS (N + 1) := by
      rw [sS_succ]
      have : (2 : ℝ) ≤ 2 ^ (2 * N + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * N + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith [sS_pos N]
    linarith

/-- Existence of the constants `c₀ > 0`, `c₁ ≥ 1` for a finite set of reals. -/
lemma exists_consts (F : Finset ℝ) :
    ∃ c0 c1 : ℝ, 0 < c0 ∧ 1 ≤ c1 ∧ (∀ c ∈ F, c ≠ 0 → c0 ≤ |c|) ∧ (∀ c ∈ F, |c| ≤ c1) := by
  induction F using Finset.induction_on with
  | empty => exact ⟨1, 1, one_pos, le_rfl, by simp, by simp⟩
  | insert a F ha ih =>
    obtain ⟨c0, c1, h0, h1, hlow, hup⟩ := ih
    refine ⟨if a = 0 then c0 else min c0 |a|, max c1 |a|, ?_, ?_, ?_, ?_⟩
    · split_ifs with h
      · exact h0
      · exact lt_min h0 (abs_pos.2 h)
    · exact le_trans h1 (le_max_left _ _)
    · intro c hc hc0
      rw [Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · simp [hc0]
      · split_ifs
        · exact hlow c hc hc0
        · exact le_trans (min_le_left _ _) (hlow c hc hc0)
    · intro c hc
      rw [Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · exact le_max_right _ _
      · exact le_trans (hup c hc) (le_max_left _ _)

/-- **Lower bound**: if the top nonzero coefficient is at `T ≥ N₀` then `|∑ d_n s_n| ≥ c₀ s_T / 2`. -/
lemma lower_bound {c0 c1 : ℝ} (hc0 : 0 < c0) (hc1 : 0 ≤ c1) (N0 : ℕ) (hN0 : 1 ≤ N0)
    (hN0big : ∀ T, N0 ≤ T → 4 * c1 ≤ c0 * 2 ^ (2 * T - 1))
    (d : ℕ → ℝ) (hd : ∀ n, d n = 0 ∨ (c0 ≤ |d n| ∧ |d n| ≤ c1)) (T : ℕ) (hT : N0 ≤ T)
    (hdT : d T ≠ 0) (hup : ∀ n, T < n → d n = 0) (N : ℕ) (hN : T < N) :
    c0 * sS T / 2 ≤ |∑ n ∈ Finset.range N, d n * sS n| := by
  have hT1 : 1 ≤ T := le_trans hN0 hT
  have hsplit : ∑ n ∈ Finset.range N, d n * sS n = ∑ n ∈ Finset.range T, d n * sS n + d T * sS T := by
    have h1 : ∑ n ∈ Finset.range N, d n * sS n = ∑ n ∈ Finset.range (T + 1), d n * sS n := by
      rw [← Finset.sum_range_add_sum_Ico _ (show T + 1 ≤ N from hN)]
      have : ∑ n ∈ Finset.Ico (T + 1) N, d n * sS n = 0 :=
        Finset.sum_eq_zero (fun n hn => by rw [hup n (by have := (Finset.mem_Ico.1 hn).1; omega)]; simp)
      rw [this, add_zero]
    rw [h1, Finset.sum_range_succ]
  have hdTbd : c0 ≤ |d T| := by
    rcases hd T with h | h
    · exact absurd h hdT
    · exact h.1
  have hbelow : |∑ n ∈ Finset.range T, d n * sS n| ≤ c1 * ∑ n ∈ Finset.range T, sS n := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun n _ => ?_)
    rw [abs_mul, abs_of_pos (sS_pos n)]
    have : |d n| ≤ c1 := by
      rcases hd n with h | h
      · rw [h, abs_zero]; exact hc1
      · exact h.2
    exact mul_le_mul_of_nonneg_right this (sS_pos n).le
  have hgeo : ∑ n ∈ Finset.range T, sS n ≤ 2 * sS (T - 1) := by
    have := geom_sS (T - 1); rwa [Nat.sub_add_cancel hT1] at this
  have hsT : sS T = sS (T - 1) * 2 ^ (2 * (T - 1) + 1) := by
    have := sS_succ (T - 1); rwa [Nat.sub_add_cancel hT1] at this
  have hexp : 2 * (T - 1) + 1 = 2 * T - 1 := by omega
  rw [hexp] at hsT
  have hbig := hN0big T hT
  have hsm := sS_pos (T - 1)
  have h4 : 4 * c1 * sS (T - 1) ≤ c0 * sS T := by
    rw [hsT]; nlinarith [mul_le_mul_of_nonneg_right hbig hsm.le]
  have hTpos := sS_pos T
  have hdTs : c0 * sS T ≤ |d T * sS T| := by
    rw [abs_mul, abs_of_pos hTpos]; exact mul_le_mul_of_nonneg_right hdTbd hTpos.le
  rw [hsplit]
  have habs := abs_sub (∑ n ∈ Finset.range T, d n * sS n + d T * sS T) (∑ n ∈ Finset.range T, d n * sS n)
  rw [add_sub_cancel_left] at habs
  have hc1g := mul_le_mul_of_nonneg_left hgeo hc1
  linarith

/-- **Counting lemma** (power-saving form): for `ρ > 0` there is `K` with, for all `L`, `sumSet l ∩ [-ρ s_L, ρ s_L]` finite and
`ncard² ≤ K s_L`. -/
theorem count_bound (l : List ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, (sumSet l ∩ Icc (-(ρ * sS L)) (ρ * sS L)).Finite ∧
      (((sumSet l ∩ Icc (-(ρ * sS L)) (ρ * sS L)).ncard : ℝ)) ^ 2 ≤ K * sS L := by
  obtain ⟨c0, c1, hc0, hc1, hlow, hup⟩ := exists_consts (Cset l)
  -- `N₀` with `4 c1 ≤ c0 2^(2T-1)` for `T ≥ N₀`
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (4 * c1 / c0) (by norm_num : (1 : ℝ) < 2)
  set N0 : ℕ := n1 + 1 with hN0
  have hN0big : ∀ T, N0 ≤ T → 4 * c1 ≤ c0 * 2 ^ (2 * T - 1) := by
    intro T hT
    have h1 : (2 : ℝ) ^ n1 ≤ 2 ^ (2 * T - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_lt_iff₀ hc0] at hn1
    nlinarith
  obtain ⟨b, hb⟩ := pow_unbounded_of_one_lt (2 * ρ / c0) (by norm_num : (1 : ℝ) < 2)
  set j : ℕ := (Cset l).card with hj
  have hjpow : (Cset l).card ≤ 2 ^ j := (Nat.lt_two_pow_self).le
  refine ⟨2 ^ (j ^ 2 + 2 * j * (b + N0 + 1)), by positivity, fun L => ?_⟩
  set M : ℕ := L + b + N0 + 1 with hM
  let Φ : (Fin M → ↥(Cset l)) → ℝ := fun e => ∑ i : Fin M, (e i : ℝ) * sS i
  set FS : Finset ℝ := (Finset.univ : Finset (Fin M → ↥(Cset l))).image Φ with hFS
  have hcardFS : FS.card ≤ (Cset l).card ^ M := by
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
  have hext : ∀ (d : ℕ → ℝ) (A B : ℕ), A ≤ B → (∀ n, A ≤ n → d n = 0) →
      ∑ n ∈ Finset.range B, d n * sS n = ∑ n ∈ Finset.range A, d n * sS n := by
    intro d A B hAB hz
    rw [← Finset.sum_range_add_sum_Ico _ hAB]
    have : ∑ n ∈ Finset.Ico A B, d n * sS n = 0 :=
      Finset.sum_eq_zero (fun n hn => by rw [hz n (Finset.mem_Ico.1 hn).1]; simp)
    rw [this, add_zero]
  have hsub : sumSet l ∩ Icc (-(ρ * sS L)) (ρ * sS L) ⊆ ↑FS := by
    rintro x ⟨hx, hxI⟩
    obtain ⟨N, d, hd, hd0, hxd⟩ := rep_of_mem_sumSet l x hx
    have hdb : ∀ n, d n = 0 ∨ (c0 ≤ |d n| ∧ |d n| ≤ c1) := fun n => by
      by_cases h : d n = 0
      · exact Or.inl h
      · exact Or.inr ⟨hlow _ (hd n) h, hup _ (hd n)⟩
    have hxabs : |x| ≤ ρ * sS L := abs_le.2 ⟨by have := hxI.1; linarith, hxI.2⟩
    have hvan : ∀ n, M ≤ n → d n = 0 := by
      intro n hn
      by_contra hne
      have hnN : n < N := by
        by_contra h; exact hne (hd0 n (not_lt.1 h))
      have hTspec : d (Nat.findGreatest (fun n => d n ≠ 0) N) ≠ 0 :=
        Nat.findGreatest_spec (P := fun n => d n ≠ 0) (m := n) hnN.le hne
      have hnT : n ≤ Nat.findGreatest (fun n => d n ≠ 0) N :=
        Nat.le_findGreatest hnN.le hne
      set T := Nat.findGreatest (fun n => d n ≠ 0) N with hTdef
      have hTN : T < N := by
        have hle : T ≤ N := Nat.findGreatest_le N
        rcases hle.lt_or_eq with h | h
        · exact h
        · exfalso; apply hTspec; rw [h]; exact hd0 N le_rfl
      have hupT : ∀ m, T < m → d m = 0 := by
        intro m hm
        by_cases hmN : m ≤ N
        · have := Nat.findGreatest_is_greatest (P := fun n => d n ≠ 0) hm hmN
          simpa using this
        · exact hd0 m (by omega)
      have hTN0 : N0 ≤ T := by omega
      have hlb := lower_bound hc0 (by linarith) N0 (by omega) hN0big d hdb T hTN0 hTspec hupT N hTN
      rw [← hxd] at hlb
      have h1 : sS T ≤ 2 * ρ / c0 * sS L := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc0]; nlinarith
      have h2 : sS T ≤ 2 ^ b * sS L := h1.trans (mul_le_mul_of_nonneg_right hb.le (sS_pos L).le)
      have h3 : (2 : ℝ) ^ (T ^ 2) ≤ 2 ^ (b + L ^ 2) := by
        unfold sS at h2; rw [pow_add]; exact h2
      have h4 : T ^ 2 ≤ b + L ^ 2 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h3
      have h5 : L + b + 1 ≤ T := by omega
      nlinarith
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨fun i => ⟨d i, hd i⟩, Finset.mem_univ _, ?_⟩)
    show ∑ i : Fin M, d i * sS i = x
    rw [Fin.sum_univ_eq_sum_range (fun n => d n * sS n) M, hxd]
    have hP1 := hext d N (max N M) (le_max_left _ _) hd0
    have hP2 := hext d M (max N M) (le_max_right _ _) hvan
    exact hP2.symm.trans hP1
  have hfin : (sumSet l ∩ Icc (-(ρ * sS L)) (ρ * sS L)).Finite := FS.finite_toSet.subset hsub
  refine ⟨hfin, ?_⟩
  have hnc : (sumSet l ∩ Icc (-(ρ * sS L)) (ρ * sS L)).ncard ≤ FS.card :=
    (Set.ncard_le_ncard hsub FS.finite_toSet).trans_eq (Set.ncard_coe_finset FS)
  have hnat : (sumSet l ∩ Icc (-(ρ * sS L)) (ρ * sS L)).ncard ≤ 2 ^ (j * M) := by
    refine hnc.trans (hcardFS.trans ?_)
    calc (Cset l).card ^ M ≤ (2 ^ j) ^ M := Nat.pow_le_pow_left hjpow M
      _ = 2 ^ (j * M) := by rw [← pow_mul]
  have hreal : ((sumSet l ∩ Icc (-(ρ * sS L)) (ρ * sS L)).ncard : ℝ) ≤ 2 ^ (j * M) := by exact_mod_cast hnat
  have hnn : (0 : ℝ) ≤ ((sumSet l ∩ Icc (-(ρ * sS L)) (ρ * sS L)).ncard : ℝ) := Nat.cast_nonneg _
  calc ((sumSet l ∩ Icc (-(ρ * sS L)) (ρ * sS L)).ncard : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (j * M)) ^ 2 :=
        pow_le_pow_left₀ hnn hreal 2
    _ = 2 ^ (2 * (j * M)) := by rw [← pow_mul]; ring_nf
    _ ≤ 2 ^ ((j ^ 2 + 2 * j * (b + N0 + 1)) + L ^ 2) := by
        apply pow_le_pow_right₀ (by norm_num)
        have := two_mul_le_add_sq j L
        simp only [hM]; nlinarith
    _ = 2 ^ (j ^ 2 + 2 * j * (b + N0 + 1)) * sS L := by rw [pow_add]; rfl

#print axioms rep_of_mem_sumSet
#print axioms lower_bound
#print axioms count_bound

end Lac
end PVG
