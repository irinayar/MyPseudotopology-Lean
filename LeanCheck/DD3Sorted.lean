import Mathlib
import LeanCheck.JASorted
import LeanCheck.JAProduct2
import LeanCheck.JAFinal2

/-!
# Diagonal density for three primes: the sorted enumeration of three chains (Lean check)

Scope. Sixth piece of the Lean version of the conditional proof of `DD({2,3,5})` (phase 5b of the research note
`TVGplus_conditional_DD235_2026-11-07.md`). `JASorted` and `JAProduct2.arc_mass_product` treat the chains of the bases
`2` and `3`; here the chain of `5` is added.

* `pairs3Of`, `key_inj3`, `sortedPairs3`, `sorted_strict3`: the pairs `(base, exponent)` of the chains of `2, 3, 5`, the scales
  `b^(e²)` are pairwise distinct, and the list sorted by the scale is strictly increasing;
* `exists_sorted3`: sequences `b, n` with `b i ∈ {2,3,5}`, `lp (b i) (n i)` strictly increasing for `i < na + nb + nc`, each
  `(b j, n j)` a level of one of the three chains, and the list of normalized kernels `normK(b_j^{n_j²})` a permutation of
  `normKernList (chain 2) ++ (normKernList (chain 3) ++ normKernList (chain 5))`;
* `arc_mass_product3`: for nonnegative seeds `A, B, C` and any order `ks'` of the merged kernel list, the arc mass of
  `Mavg_a ∗ (Mavg_b ∗ Mavg_c)` is at most `2 · Sa Sb Sc · S_0 · ∏ f_i` (the three-chain counterpart of `arc_mass_product`);
* `arc_mass_sorted3`: the same along the sorted list of the scales of the three chains.

`arc_mass_sorted3` is the form to which `DD3Assemble.prod_f_bound3` is applied (the product `∏ f_i` for the sorted list).
Not formalized: the expected-energy identity for three random translations, the Fejér step, buffered heights, the assembly
of `CentralBound3`. A Lean proof verifies its formal statement under its hypotheses; the correspondence with the
research note requires mathematical review.
-/

namespace LeanCheck
namespace DD3Sorted

open Finset JAMerged JAProduct JAProduct2 JAMulti JAFinal2 JAWindowQ JAFarSep JATransfer JALocalize JASorted

/-! ### Pairs of the three chains -/

/-- The pairs `(base, exponent)` of the levels of the chains of `2`, `3` and `5`. -/
def pairs3Of (sa na sb nb sc nc : ℕ) : List (ℕ × ℕ) :=
  pairsOf sa na sb nb ++ (List.range nc).map (fun k => (5, sc + k + 1))

lemma mem_pairs3Of {sa na sb nb sc nc : ℕ} {p : ℕ × ℕ} :
    p ∈ pairs3Of sa na sb nb sc nc ↔
      (∃ k, k < na ∧ p = (2, sa + k + 1)) ∨ (∃ k, k < nb ∧ p = (3, sb + k + 1)) ∨
        (∃ k, k < nc ∧ p = (5, sc + k + 1)) := by
  unfold pairs3Of
  rw [List.mem_append, mem_pairsOf]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ((h | h) | ⟨k, hk, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨k, hk, rfl⟩)
  · rintro (h | h | ⟨k, hk, rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨k, hk, rfl⟩

lemma key_ne (b b' e f : ℕ) (hb : b.Prime) (hne : ¬ b ∣ b') (he : e ≠ 0) : b ^ e ≠ b' ^ f := by
  intro h
  have h1 : b ∣ b ^ e := dvd_pow_self b he
  rw [h] at h1
  exact hne (hb.dvd_of_dvd_pow h1)

lemma key_inj3 {sa na sb nb sc nc : ℕ} :
    ∀ p ∈ pairs3Of sa na sb nb sc nc, ∀ q ∈ pairs3Of sa na sb nb sc nc, key p = key q → p = q := by
  intro p hp q hq h
  rw [mem_pairs3Of] at hp hq
  unfold key at h
  have hpe : ∀ x : ℕ, ((x + 1) ^ 2 ≠ 0) := fun x => by positivity
  rcases hp with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ <;>
    rcases hq with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · simp only at h
    have h1 : (sa + x + 1) ^ 2 = (sa + y + 1) ^ 2 := Nat.pow_right_injective (le_refl 2) h
    have h2 : sa + x + 1 = sa + y + 1 := Nat.pow_left_injective (by norm_num) h1
    have : x = y := by omega
    rw [this]
  · exact absurd h (key_ne 2 3 _ _ Nat.prime_two (by norm_num) (by positivity))
  · exact absurd h (key_ne 2 5 _ _ Nat.prime_two (by norm_num) (by positivity))
  · exact absurd h.symm (key_ne 2 3 _ _ Nat.prime_two (by norm_num) (by positivity))
  · simp only at h
    have h1 : (sb + x + 1) ^ 2 = (sb + y + 1) ^ 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
    have h2 : sb + x + 1 = sb + y + 1 := Nat.pow_left_injective (by norm_num) h1
    have : x = y := by omega
    rw [this]
  · exact absurd h (key_ne 3 5 _ _ Nat.prime_three (by norm_num) (by positivity))
  · exact absurd h.symm (key_ne 2 5 _ _ Nat.prime_two (by norm_num) (by positivity))
  · exact absurd h.symm (key_ne 3 5 _ _ Nat.prime_three (by norm_num) (by positivity))
  · simp only at h
    have h1 : (sc + x + 1) ^ 2 = (sc + y + 1) ^ 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 5) h
    have h2 : sc + x + 1 = sc + y + 1 := Nat.pow_left_injective (by norm_num) h1
    have : x = y := by omega
    rw [this]

lemma pairs3Of_nodup (sa na sb nb sc nc : ℕ) : (pairs3Of sa na sb nb sc nc).Nodup := by
  unfold pairs3Of
  rw [List.nodup_append]
  refine ⟨pairsOf_nodup sa na sb nb, ?_, ?_⟩
  · refine List.Nodup.map (fun x y h => ?_) (List.nodup_range)
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro p hp q hq hpq
    rw [mem_pairsOf] at hp
    simp only [List.mem_map, List.mem_range] at hq
    obtain ⟨l, _, rfl⟩ := hq
    rcases hp with ⟨k, _, hk⟩ | ⟨k, _, hk⟩ <;> rw [hk] at hpq <;> simp only [Prod.mk.injEq] at hpq <;> omega

/-- The sorted list of pairs. -/
def sortedPairs3 (sa na sb nb sc nc : ℕ) : List (ℕ × ℕ) :=
  (pairs3Of sa na sb nb sc nc).mergeSort (fun p q => decide (key p ≤ key q))

lemma sortedPairs3_perm (sa na sb nb sc nc : ℕ) :
    (sortedPairs3 sa na sb nb sc nc).Perm (pairs3Of sa na sb nb sc nc) :=
  List.mergeSort_perm _ _

lemma sortedPairs3_length (sa na sb nb sc nc : ℕ) :
    (sortedPairs3 sa na sb nb sc nc).length = na + nb + nc := by
  unfold sortedPairs3
  rw [List.length_mergeSort]
  simp [pairs3Of, pairsOf]
  omega

lemma sortedPairs3_pairwise (sa na sb nb sc nc : ℕ) :
    (sortedPairs3 sa na sb nb sc nc).Pairwise (fun p q => key p ≤ key q) := by
  have := List.pairwise_mergeSort (le := fun p q => decide (key p ≤ key q))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega) (pairs3Of sa na sb nb sc nc)
  simpa [sortedPairs3] using this

/-- The sorted list is strictly increasing in the scale. -/
lemma sorted_strict3 (sa na sb nb sc nc : ℕ) (a c : ℕ) (hac : a < c) (hc : c < na + nb + nc) :
    key ((sortedPairs3 sa na sb nb sc nc).getD a (2, 0)) <
      key ((sortedPairs3 sa na sb nb sc nc).getD c (2, 0)) := by
  have hlen := sortedPairs3_length sa na sb nb sc nc
  have ha : a < (sortedPairs3 sa na sb nb sc nc).length := by omega
  have hc' : c < (sortedPairs3 sa na sb nb sc nc).length := by omega
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hc']
  have hle : key ((sortedPairs3 sa na sb nb sc nc)[a]) ≤ key ((sortedPairs3 sa na sb nb sc nc)[c]) := by
    have := (List.pairwise_iff_getElem.mp (sortedPairs3_pairwise sa na sb nb sc nc)) a c ha hc' hac
    exact this
  have hne : (sortedPairs3 sa na sb nb sc nc)[a] ≠ (sortedPairs3 sa na sb nb sc nc)[c] := by
    have hnd : (sortedPairs3 sa na sb nb sc nc).Nodup :=
      (sortedPairs3_perm sa na sb nb sc nc).nodup_iff.mpr (pairs3Of_nodup _ _ _ _ _ _)
    intro h
    have := (List.Nodup.getElem_inj_iff hnd).mp h
    omega
  have hmem : ∀ i (hi : i < (sortedPairs3 sa na sb nb sc nc).length),
      (sortedPairs3 sa na sb nb sc nc)[i] ∈ pairs3Of sa na sb nb sc nc := fun i hi =>
    (sortedPairs3_perm sa na sb nb sc nc).subset (List.getElem_mem hi)
  refine lt_of_le_of_ne hle (fun h => hne (key_inj3 _ (hmem a ha) _ (hmem c hc') h))

section kerns

variable {N : ℕ} [NeZero N]

lemma pairs3_map_Fker (D : ℝ) (sa na sb nb sc nc : ℕ) :
    (pairs3Of sa na sb nb sc nc).map (Fker N D) =
      normKernList N (chainP 2 sa D) na ++
        (normKernList N (chainP 3 sb D) nb ++ normKernList N (chainP 5 sc D) nc) := by
  unfold pairs3Of
  rw [List.map_append, pairs_map_Fker, ← List.append_assoc]
  congr 1
  unfold normKernList
  rw [List.map_map]
  congr 1

end kerns

lemma getD_mem3 (sa na sb nb sc nc j : ℕ) (hj : j < na + nb + nc) :
    (sortedPairs3 sa na sb nb sc nc).getD j (2, 0) ∈ pairs3Of sa na sb nb sc nc := by
  have hlen := sortedPairs3_length sa na sb nb sc nc
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact (sortedPairs3_perm sa na sb nb sc nc).subset (List.getElem_mem _)

/-- **The sorted enumeration of the scales of the three chains.** -/
theorem exists_sorted3 (N : ℕ) [NeZero N] (D : ℝ) (sa na sb nb sc nc : ℕ) :
    ∃ b n : ℕ → ℕ, (∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5) ∧
      (∀ a c, a < c → c < na + nb + nc → lp (b a) (n a) < lp (b c) (n c)) ∧
      (∀ j, j < na + nb + nc → (b j = 2 ∧ sa < n j ∧ n j ≤ sa + na) ∨ (b j = 3 ∧ sb < n j ∧ n j ≤ sb + nb) ∨
        (b j = 5 ∧ sc < n j ∧ n j ≤ sc + nc)) ∧
      ∀ [inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2))],
        ((List.range (na + nb + nc)).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
          (wQ D ((b j) ^ ((n j) ^ 2))))).Perm
          (normKernList N (chainP 2 sa D) na ++
            (normKernList N (chainP 3 sb D) nb ++ normKernList N (chainP 5 sc D) nc)) := by
  classical
  set S := sortedPairs3 sa na sb nb sc nc with hS
  have hlen : S.length = na + nb + nc := sortedPairs3_length sa na sb nb sc nc
  have hb2 : ∀ j, j < na + nb + nc → 2 ≤ (S.getD j (2, 0)).1 := by
    intro j hj
    have := getD_mem3 sa na sb nb sc nc j hj
    rw [mem_pairs3Of] at this
    rcases this with ⟨k, _, hk⟩ | ⟨k, _, hk⟩ | ⟨k, _, hk⟩ <;> rw [hk] <;> norm_num
  refine ⟨fun j => (S.getD j (2, 0)).1, fun j => (S.getD j (2, 0)).2, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i < na + nb + nc
    · have := getD_mem3 sa na sb nb sc nc i hi
      rw [mem_pairs3Of] at this
      rcases this with ⟨k, _, hk⟩ | ⟨k, _, hk⟩ | ⟨k, _, hk⟩
      · left; show (S.getD i (2, 0)).1 = 2; rw [hk]
      · right; left; show (S.getD i (2, 0)).1 = 3; rw [hk]
      · right; right; show (S.getD i (2, 0)).1 = 5; rw [hk]
    · left
      show (S.getD i (2, 0)).1 = 2
      rw [List.getD_eq_default _ _ (by omega)]
  · intro a c hac hc
    have hk := sorted_strict3 sa na sb nb sc nc a c hac hc
    have hba := hb2 a (by omega)
    have hbc := hb2 c hc
    have h1 : Real.log (((S.getD a (2, 0)).1 ^ ((S.getD a (2, 0)).2 ^ 2) : ℕ) : ℝ) =
        lp (S.getD a (2, 0)).1 (S.getD a (2, 0)).2 := log_scale _ _ hba
    have h2 : Real.log (((S.getD c (2, 0)).1 ^ ((S.getD c (2, 0)).2 ^ 2) : ℕ) : ℝ) =
        lp (S.getD c (2, 0)).1 (S.getD c (2, 0)).2 := log_scale _ _ hbc
    show lp (S.getD a (2, 0)).1 (S.getD a (2, 0)).2 < lp (S.getD c (2, 0)).1 (S.getD c (2, 0)).2
    rw [← h1, ← h2]
    apply Real.log_lt_log
    · have : 0 < (S.getD a (2, 0)).1 ^ ((S.getD a (2, 0)).2 ^ 2) := pow_pos (by omega) _
      exact_mod_cast this
    · exact_mod_cast hk
  · intro j hj
    have := getD_mem3 sa na sb nb sc nc j hj
    rw [mem_pairs3Of] at this
    rcases this with ⟨k, hk, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, h⟩
    · left
      show (S.getD j (2, 0)).1 = 2 ∧ sa < (S.getD j (2, 0)).2 ∧ (S.getD j (2, 0)).2 ≤ sa + na
      rw [h]; refine ⟨rfl, ?_, ?_⟩ <;> dsimp only <;> omega
    · right; left
      show (S.getD j (2, 0)).1 = 3 ∧ sb < (S.getD j (2, 0)).2 ∧ (S.getD j (2, 0)).2 ≤ sb + nb
      rw [h]; refine ⟨rfl, ?_, ?_⟩ <;> dsimp only <;> omega
    · right; right
      show (S.getD j (2, 0)).1 = 5 ∧ sc < (S.getD j (2, 0)).2 ∧ (S.getD j (2, 0)).2 ≤ sc + nc
      rw [h]; refine ⟨rfl, ?_, ?_⟩ <;> dsimp only <;> omega
  · intro inst
    have h1 : (List.range (na + nb + nc)).map (fun j => normK N ((S.getD j (2, 0)).1 ^ ((S.getD j (2, 0)).2 ^ 2))
          (wQ D ((S.getD j (2, 0)).1 ^ ((S.getD j (2, 0)).2 ^ 2)))) =
        (List.range (na + nb + nc)).map (fun j => Fker N D (S.getD j (2, 0))) := by
      apply List.map_congr_left
      intro j hj
      have hj' : j < na + nb + nc := List.mem_range.mp hj
      have : NeZero (key (S.getD j (2, 0))) := inst j
      exact (Fker_eq D (S.getD j (2, 0)) (by have := hb2 j hj'; omega)).symm
    have h2 : (List.range (na + nb + nc)).map (fun j => Fker N D (S.getD j (2, 0))) =
        S.map (Fker N D) := by
      rw [← hlen]
      exact map_range_getD (Fker N D) S (2, 0)
    have h3 : (S.map (Fker N D)).Perm ((pairs3Of sa na sb nb sc nc).map (Fker N D)) :=
      (sortedPairs3_perm sa na sb nb sc nc).map _
    show ((List.range (na + nb + nc)).map (fun j => normK N ((S.getD j (2, 0)).1 ^ ((S.getD j (2, 0)).2 ^ 2))
          (wQ D ((S.getD j (2, 0)).1 ^ ((S.getD j (2, 0)).2 ^ 2))))).Perm _
    rw [h1, h2, ← pairs3_map_Fker D sa na sb nb sc nc]
    exact h3

/-! ### The arc mass of three chains -/

variable {N : ℕ} [NeZero N]

/-- **Arc mass reduction and kernel merging, three chains** (copy of `JAProduct2.arc_mass_product`). -/
theorem arc_mass_product3 (ca cb cc : Chain) (na nb nc : ℕ) (hZa : ∀ k, 0 < ∑ y, ca.w (k + 1) y)
    (hZb : ∀ k, 0 < ∑ y, cb.w (k + 1) y) (hZc : ∀ k, 0 < ∑ y, cc.w (k + 1) y)
    (A B C : ZMod N → ℝ) (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x) (hC : ∀ x, 0 ≤ C x)
    (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N) (ks' : List (ZMod N → ℝ))
    (hperm : ks'.Perm (normKernList N ca na ++ (normKernList N cb nb ++ normKernList N cc nc))) :
    ∑ t ∈ arc N (m - 1),
        conv (Mavg N na ca A) (conv (Mavg N nb cb B) (Mavg N nc cc C)) t ≤
      2 * ((∏ k ∈ range na, ((∑ y, ca.w (k + 1) y) ^ 2 / ((ca.q k : ℕ) : ℝ) ^ 2)) *
          (∏ k ∈ range nb, ((∑ y, cb.w (k + 1) y) ^ 2 / ((cb.q k : ℕ) : ℝ) ^ 2)) *
          (∏ k ∈ range nc, ((∑ y, cc.w (k + 1) y) ^ 2 / ((cc.q k : ℕ) : ℝ) ^ 2))) *
        ((conv (conv A (conv B C)) (Hs (Ftri N m) ks') 0 / Hs (Ftri N m) ks' 0) *
          ∏ i ∈ range ks'.length,
            (Hs (Ftri N m) (ks'.drop i) 0 / Hs (Ftri N m) (ks'.drop (i + 1)) 0)) := by
  classical
  set F := Ftri N m with hFdef
  set Sa := ∏ k ∈ range na, ((∑ y, ca.w (k + 1) y) ^ 2 / ((ca.q k : ℕ) : ℝ) ^ 2) with hSa
  set Sb := ∏ k ∈ range nb, ((∑ y, cb.w (k + 1) y) ^ 2 / ((cb.q k : ℕ) : ℝ) ^ 2) with hSb
  set Sc := ∏ k ∈ range nc, ((∑ y, cc.w (k + 1) y) ^ 2 / ((cc.q k : ℕ) : ℝ) ^ 2) with hSc
  have hnormk : ∀ (c : Chain) (n : ℕ), (∀ k, 0 < ∑ y, c.w (k + 1) y) →
      ∀ K ∈ normKernList N c n, (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 := by
    intro c n hZ K hK
    unfold normKernList at hK
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hK
    exact ⟨normK_nonneg _ _, normK_zero_ge _ _ (hZ k)⟩
  have hks' : ∀ K ∈ ks', (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 := by
    intro K hK
    rcases List.mem_append.mp (hperm.subset hK) with h | h
    · exact hnormk ca na hZa K h
    · rcases List.mem_append.mp h with h' | h'
      · exact hnormk cb nb hZb K h'
      · exact hnormk cc nc hZc K h'
  have hF0 : F 0 = 1 := Ftri_zero m hm h2m
  have hFnn : ∀ x, 0 ≤ F x := Ftri_nonneg m
  obtain ⟨hHnn, hH1⟩ := Hs_atom F hFnn (by rw [hF0]) ks' hks'
  have hSa0 : 0 ≤ Sa := Finset.prod_nonneg (fun k _ => by positivity)
  have hSb0 : 0 ≤ Sb := Finset.prod_nonneg (fun k _ => by positivity)
  have hSc0 : 0 ≤ Sc := Finset.prod_nonneg (fun k _ => by positivity)
  have hbc : conv (Mavg N nb cb B) (Mavg N nc cc C) =
      fun x => (Sb * Sc) * convList (conv B C) (normKernList N cb nb ++ normKernList N cc nc) x := by
    rw [Mavg_eq_norm cb nb hZb, Mavg_eq_norm cc nc hZc]
    funext x
    rw [JARealization.conv_smul, conv_convList, ← convList_append]
  have hν : conv (Mavg N na ca A) (conv (Mavg N nb cb B) (Mavg N nc cc C)) =
      fun x => (Sa * (Sb * Sc)) * convList (conv A (conv B C)) ks' x := by
    rw [hbc, Mavg_eq_norm ca na hZa]
    funext x
    rw [JARealization.conv_smul, conv_convList, ← convList_append, convList_perm hperm.symm]
  have hksnn : ∀ K ∈ ks', ∀ x, 0 ≤ K x := fun K hK => (hks' K hK).1
  have hconvnn : ∀ x, 0 ≤ convList (conv A (conv B C)) ks' x :=
    convList_nonneg ks' hksnn _
      (fun x => JAFinal.conv_nonneg' _ _ hA (fun y => JAFinal.conv_nonneg' _ _ hB hC y) x)
  have hνnn : ∀ x, 0 ≤ conv (Mavg N na ca A) (conv (Mavg N nb cb B) (Mavg N nc cc C)) x := by
    intro x
    rw [hν]
    exact mul_nonneg (mul_nonneg hSa0 (mul_nonneg hSb0 hSc0)) (hconvnn x)
  have h1 := arc_mass_le m hm h2m _ hνnn
  have h2 : conv (conv (Mavg N na ca A) (conv (Mavg N nb cb B) (Mavg N nc cc C))) F 0 =
      (Sa * (Sb * Sc)) * conv (convList (conv A (conv B C)) ks') F 0 := by
    rw [hν]
    exact conv_smul_left N (Sa * (Sb * Sc)) (convList (conv A (conv B C)) ks') F 0
  have hpos : ∀ i ≤ ks'.length, 0 < Hs F (ks'.drop i) 0 := by
    intro i _
    have := Hs_atom F hFnn (by rw [hF0]) (ks'.drop i) (fun K hK => hks' K (List.mem_of_mem_drop hK))
    linarith [this.2]
  have h3 := product_identity (conv A (conv B C)) F ks' hpos
  rw [hF0, mul_one] at h3
  calc ∑ t ∈ arc N (m - 1), conv (Mavg N na ca A) (conv (Mavg N nb cb B) (Mavg N nc cc C)) t
      ≤ 2 * conv (conv (Mavg N na ca A) (conv (Mavg N nb cb B) (Mavg N nc cc C))) F 0 := h1
    _ = 2 * ((Sa * (Sb * Sc)) * conv (convList (conv A (conv B C)) ks') F 0) := by rw [h2]
    _ = _ := by rw [h3]; ring

/-- **The arc mass along the sorted list of the scales of the three chains.** -/
theorem arc_mass_sorted3 (D : ℝ) (sa na sb nb sc nc : ℕ) (A B C : ZMod N → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x) (hC : ∀ x, 0 ≤ C x) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N) :
    ∃ b n : ℕ → ℕ, (∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5) ∧
      (∀ a c, a < c → c < na + nb + nc → lp (b a) (n a) < lp (b c) (n c)) ∧
      (∀ j, j < na + nb + nc → (b j = 2 ∧ sa < n j ∧ n j ≤ sa + na) ∨ (b j = 3 ∧ sb < n j ∧ n j ≤ sb + nb) ∨
        (b j = 5 ∧ sc < n j ∧ n j ≤ sc + nc)) ∧
      ∀ [inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2))],
        ∑ t ∈ arc N (m - 1), conv (Mavg N na (chainP 2 sa D) A)
            (conv (Mavg N nb (chainP 3 sb D) B) (Mavg N nc (chainP 5 sc D) C)) t ≤
          2 * ((∏ k ∈ range na, ((∑ y, (chainP 2 sa D).w (k + 1) y) ^ 2 / (((chainP 2 sa D).q k : ℕ) : ℝ) ^ 2)) *
              (∏ k ∈ range nb, ((∑ y, (chainP 3 sb D).w (k + 1) y) ^ 2 / (((chainP 3 sb D).q k : ℕ) : ℝ) ^ 2)) *
              (∏ k ∈ range nc, ((∑ y, (chainP 5 sc D).w (k + 1) y) ^ 2 / (((chainP 5 sc D).q k : ℕ) : ℝ) ^ 2))) *
            ((conv (conv A (conv B C)) (Hs (Ftri N m)
                  ((List.range (na + nb + nc)).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
                    (wQ D ((b j) ^ ((n j) ^ 2)))))) 0 /
                Hs (Ftri N m) ((List.range (na + nb + nc)).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
                    (wQ D ((b j) ^ ((n j) ^ 2))))) 0) *
              ∏ i ∈ range (na + nb + nc),
                (Hs (Ftri N m) (((List.range (na + nb + nc)).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
                    (wQ D ((b j) ^ ((n j) ^ 2))))).drop i) 0 /
                  Hs (Ftri N m) (((List.range (na + nb + nc)).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
                    (wQ D ((b j) ^ ((n j) ^ 2))))).drop (i + 1)) 0)) := by
  obtain ⟨b, n, hb, hmono, hmem, hperm⟩ := exists_sorted3 N D sa na sb nb sc nc
  refine ⟨b, n, hb, hmono, hmem, fun {inst} => ?_⟩
  have hZa : ∀ k, 0 < ∑ y, (chainP 2 sa D).w (k + 1) y := fun k => JAFinal.sum_wQ_pos D
  have hZb : ∀ k, 0 < ∑ y, (chainP 3 sb D).w (k + 1) y := fun k => JAFinal.sum_wQ_pos D
  have hZc : ∀ k, 0 < ∑ y, (chainP 5 sc D).w (k + 1) y := fun k => JAFinal.sum_wQ_pos D
  have h := arc_mass_product3 (chainP 2 sa D) (chainP 3 sb D) (chainP 5 sc D) na nb nc hZa hZb hZc A B C
    hA hB hC m hm h2m _ (hperm (inst := inst))
  simpa only [List.length_map, List.length_range] using h

end DD3Sorted
end LeanCheck
