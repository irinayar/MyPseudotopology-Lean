import Mathlib
import LeanCheck.JAFarSep
import LeanCheck.JAFinal2

/-!
# The central bound, step 5b: the sorted enumeration of the scales of the two chains

The levels `1, …, n_a` of the chain of `2` have scales `2^{(s_a+k)^2}` and the levels `1, …, n_b` of the chain of `3` have scales
`3^{(s_b+k)^2}`.  Here the pairs `(base, exponent)` of both chains are sorted by scale.

* `pairsOf`, `key`: the list of pairs and the scale `key (b, e) = b^{e^2}`;
* `key_inj_on`: distinct pairs have distinct scales (for `2^{x^2} = 3^{y^2}` use parity);
* `sorted_strict`: the sorted list is strictly increasing in the scale;
* `exists_sorted` : there are sequences `b, n : ℕ → ℕ` with `b i ∈ {2, 3}`, `lp (b i) (n i)` strictly increasing for `i < n_a + n_b`,
  each `(b j, n j)` one of the pairs of the two chains, and
  `[normK(b_j^{n_j^2}) : j < n_a + n_b]` a permutation of `normKernList (chain 2) ++ normKernList (chain 3)`.
-/

namespace LeanCheck
namespace JASorted

open Finset JAMerged JAProduct JAProduct2 JAMulti JAFinal2 JAWindowQ JAFarSep

/-- The pairs `(base, exponent)` of the levels of the two chains. -/
def pairsOf (sa na sb nb : ℕ) : List (ℕ × ℕ) :=
  (List.range na).map (fun k => (2, sa + k + 1)) ++ (List.range nb).map (fun k => (3, sb + k + 1))

/-- The scale of a pair. -/
def key (p : ℕ × ℕ) : ℕ := p.1 ^ (p.2 ^ 2)

lemma mem_pairsOf {sa na sb nb : ℕ} {p : ℕ × ℕ} :
    p ∈ pairsOf sa na sb nb ↔ (∃ k, k < na ∧ p = (2, sa + k + 1)) ∨ (∃ k, k < nb ∧ p = (3, sb + k + 1)) := by
  unfold pairsOf
  simp only [List.mem_append, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr ⟨k, hk, rfl⟩
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr ⟨k, hk, rfl⟩

lemma key_inj_on {sa na sb nb : ℕ} :
    ∀ p ∈ pairsOf sa na sb nb, ∀ q ∈ pairsOf sa na sb nb, key p = key q → p = q := by
  intro p hp q hq h
  rw [mem_pairsOf] at hp hq
  unfold key at h
  rcases hp with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ <;> rcases hq with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · simp only at h
    have h1 : (sa + x + 1) ^ 2 = (sa + y + 1) ^ 2 := Nat.pow_right_injective (le_refl 2) h
    have h2 : sa + x + 1 = sa + y + 1 := Nat.pow_left_injective (by norm_num) h1
    have : x = y := by omega
    rw [this]
  · exfalso
    simp only at h
    have h2 : 2 ∣ 2 ^ ((sa + x + 1) ^ 2) := dvd_pow_self 2 (by positivity)
    rw [h] at h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    omega
  · exfalso
    simp only at h
    have h2 : 2 ∣ 2 ^ ((sa + y + 1) ^ 2) := dvd_pow_self 2 (by positivity)
    rw [← h] at h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    omega
  · simp only at h
    have h1 : (sb + x + 1) ^ 2 = (sb + y + 1) ^ 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
    have h2 : sb + x + 1 = sb + y + 1 := Nat.pow_left_injective (by norm_num) h1
    have : x = y := by omega
    rw [this]

lemma pairsOf_nodup (sa na sb nb : ℕ) : (pairsOf sa na sb nb).Nodup := by
  unfold pairsOf
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · refine List.Nodup.map (fun x y h => ?_) (List.nodup_range)
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · refine List.Nodup.map (fun x y h => ?_) (List.nodup_range)
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro p hp q hq hpq
    simp only [List.mem_map, List.mem_range] at hp hq
    obtain ⟨k, _, rfl⟩ := hp
    obtain ⟨l, _, rfl⟩ := hq
    simp only [Prod.mk.injEq] at hpq
    omega

/-- The sorted list of pairs. -/
def sortedPairs (sa na sb nb : ℕ) : List (ℕ × ℕ) :=
  (pairsOf sa na sb nb).mergeSort (fun p q => decide (key p ≤ key q))

lemma sortedPairs_perm (sa na sb nb : ℕ) : (sortedPairs sa na sb nb).Perm (pairsOf sa na sb nb) :=
  List.mergeSort_perm _ _

lemma sortedPairs_length (sa na sb nb : ℕ) : (sortedPairs sa na sb nb).length = na + nb := by
  unfold sortedPairs
  rw [List.length_mergeSort]
  simp [pairsOf]

lemma sortedPairs_pairwise (sa na sb nb : ℕ) :
    (sortedPairs sa na sb nb).Pairwise (fun p q => key p ≤ key q) := by
  have := List.pairwise_mergeSort (le := fun p q => decide (key p ≤ key q))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega) (pairsOf sa na sb nb)
  simpa [sortedPairs] using this

/-- The sorted list is strictly increasing in the scale. -/
lemma sorted_strict (sa na sb nb : ℕ) (a c : ℕ) (hac : a < c) (hc : c < na + nb) :
    key ((sortedPairs sa na sb nb).getD a (2, 0)) < key ((sortedPairs sa na sb nb).getD c (2, 0)) := by
  have hlen := sortedPairs_length sa na sb nb
  have ha : a < (sortedPairs sa na sb nb).length := by omega
  have hc' : c < (sortedPairs sa na sb nb).length := by omega
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hc']
  have hle : key ((sortedPairs sa na sb nb)[a]) ≤ key ((sortedPairs sa na sb nb)[c]) := by
    have := (List.pairwise_iff_getElem.mp (sortedPairs_pairwise sa na sb nb)) a c ha hc' hac
    exact this
  have hne : (sortedPairs sa na sb nb)[a] ≠ (sortedPairs sa na sb nb)[c] := by
    have hnd : (sortedPairs sa na sb nb).Nodup := (sortedPairs_perm sa na sb nb).nodup_iff.mpr (pairsOf_nodup _ _ _ _)
    intro h
    have := (List.Nodup.getElem_inj_iff hnd).mp h
    omega
  have hmem : ∀ i (hi : i < (sortedPairs sa na sb nb).length),
      (sortedPairs sa na sb nb)[i] ∈ pairsOf sa na sb nb := fun i hi =>
    (sortedPairs_perm sa na sb nb).subset (List.getElem_mem hi)
  refine lt_of_le_of_ne hle (fun h => hne (key_inj_on _ (hmem a ha) _ (hmem c hc') h))

/-! ### The kernel list of a pair -/

section kerns

variable {N : ℕ} [NeZero N]

/-- The unit-atom kernel of the window at the scale of a pair (zero for a pair with base `0`). -/
noncomputable def Fker (N : ℕ) [NeZero N] (D : ℝ) (p : ℕ × ℕ) : ZMod N → ℝ :=
  if h : 0 < p.1 then
    haveI : NeZero (key p) := ⟨(pow_pos h _).ne'⟩
    normK N (key p) (wQ D (key p))
  else 0

lemma Fker_eq (D : ℝ) (p : ℕ × ℕ) (hp : 0 < p.1) [NeZero (key p)] :
    Fker N D p = normK N (key p) (wQ D (key p)) := by
  unfold Fker
  rw [dif_pos hp]

lemma map_range_getD {α β : Type*} (f : α → β) (l : List α) (d : α) :
    (List.range l.length).map (fun j => f (l.getD j d)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using h2)]

lemma pairs_map_Fker (D : ℝ) (sa na sb nb : ℕ) :
    (pairsOf sa na sb nb).map (Fker N D) =
      normKernList N (chainP 2 sa D) na ++ normKernList N (chainP 3 sb D) nb := by
  unfold pairsOf normKernList
  rw [List.map_append, List.map_map, List.map_map]
  congr 1

end kerns

lemma getD_mem (sa na sb nb j : ℕ) (hj : j < na + nb) :
    (sortedPairs sa na sb nb).getD j (2, 0) ∈ pairsOf sa na sb nb := by
  have hlen := sortedPairs_length sa na sb nb
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact (sortedPairs_perm sa na sb nb).subset (List.getElem_mem _)

/-- **The sorted enumeration of the scales of the two chains.** -/
theorem exists_sorted (N : ℕ) [NeZero N] (D : ℝ) (sa na sb nb : ℕ) :
    ∃ b n : ℕ → ℕ, (∀ i, b i = 2 ∨ b i = 3) ∧
      (∀ a c, a < c → c < na + nb → lp (b a) (n a) < lp (b c) (n c)) ∧
      (∀ j, j < na + nb → (b j = 2 ∧ sa < n j ∧ n j ≤ sa + na) ∨ (b j = 3 ∧ sb < n j ∧ n j ≤ sb + nb)) ∧
      ∀ [inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2))],
        ((List.range (na + nb)).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
          (wQ D ((b j) ^ ((n j) ^ 2))))).Perm
          (normKernList N (chainP 2 sa D) na ++ normKernList N (chainP 3 sb D) nb) := by
  classical
  set S := sortedPairs sa na sb nb with hS
  have hlen : S.length = na + nb := sortedPairs_length sa na sb nb
  have hb2 : ∀ j, j < na + nb → 2 ≤ (S.getD j (2, 0)).1 := by
    intro j hj
    have := getD_mem sa na sb nb j hj
    rw [mem_pairsOf] at this
    rcases this with ⟨k, _, hk⟩ | ⟨k, _, hk⟩ <;> rw [hk] <;> norm_num
  refine ⟨fun j => (S.getD j (2, 0)).1, fun j => (S.getD j (2, 0)).2, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i < na + nb
    · have := getD_mem sa na sb nb i hi
      rw [mem_pairsOf] at this
      rcases this with ⟨k, _, hk⟩ | ⟨k, _, hk⟩
      · left; show (S.getD i (2, 0)).1 = 2; rw [hk]
      · right; show (S.getD i (2, 0)).1 = 3; rw [hk]
    · left
      show (S.getD i (2, 0)).1 = 2
      rw [List.getD_eq_default _ _ (by omega)]
  · intro a c hac hc
    have hk := sorted_strict sa na sb nb a c hac hc
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
    have := getD_mem sa na sb nb j hj
    rw [mem_pairsOf] at this
    rcases this with ⟨k, hk, h⟩ | ⟨k, hk, h⟩
    · left
      show (S.getD j (2, 0)).1 = 2 ∧ sa < (S.getD j (2, 0)).2 ∧ (S.getD j (2, 0)).2 ≤ sa + na
      rw [h]; refine ⟨rfl, ?_, ?_⟩ <;> dsimp only <;> omega
    · right
      show (S.getD j (2, 0)).1 = 3 ∧ sb < (S.getD j (2, 0)).2 ∧ (S.getD j (2, 0)).2 ≤ sb + nb
      rw [h]; refine ⟨rfl, ?_, ?_⟩ <;> dsimp only <;> omega
  · intro inst
    have h1 : (List.range (na + nb)).map (fun j => normK N ((S.getD j (2, 0)).1 ^ ((S.getD j (2, 0)).2 ^ 2))
          (wQ D ((S.getD j (2, 0)).1 ^ ((S.getD j (2, 0)).2 ^ 2)))) =
        (List.range (na + nb)).map (fun j => Fker N D (S.getD j (2, 0))) := by
      apply List.map_congr_left
      intro j hj
      have hj' : j < na + nb := List.mem_range.mp hj
      haveI : NeZero (key (S.getD j (2, 0))) := inst j
      exact (Fker_eq D (S.getD j (2, 0)) (by have := hb2 j hj'; omega)).symm
    have h2 : (List.range (na + nb)).map (fun j => Fker N D (S.getD j (2, 0))) = S.map (Fker N D) := by
      rw [← hlen]
      exact map_range_getD (Fker N D) S (2, 0)
    have h3 : (S.map (Fker N D)).Perm ((pairsOf sa na sb nb).map (Fker N D)) :=
      (sortedPairs_perm sa na sb nb).map _
    show ((List.range (na + nb)).map (fun j => normK N ((S.getD j (2, 0)).1 ^ ((S.getD j (2, 0)).2 ^ 2))
          (wQ D ((S.getD j (2, 0)).1 ^ ((S.getD j (2, 0)).2 ^ 2))))).Perm _
    rw [h1, h2, ← pairs_map_Fker D sa na sb nb]
    exact h3

#print axioms sorted_strict
#print axioms key_inj_on
#print axioms exists_sorted

/-- **The arc mass along the sorted list.**  For the chains of `2` and `3` and ANY nonnegative seed measures, there is a sorted
enumeration `(b_j, n_j)` of the scales of both chains such that the arc mass of `Mavg_a ∗ Mavg_b` is at most
`2 · Sc · S_0 · ∏ f_i` along the list of normalized kernels in increasing order of the scale. -/
theorem arc_mass_sorted (N : ℕ) [NeZero N] (D : ℝ) (sa na sb nb : ℕ) (A B : ZMod N → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N) :
    ∃ b n : ℕ → ℕ, (∀ i, b i = 2 ∨ b i = 3) ∧
      (∀ a c, a < c → c < na + nb → lp (b a) (n a) < lp (b c) (n c)) ∧
      (∀ j, j < na + nb → (b j = 2 ∧ sa < n j ∧ n j ≤ sa + na) ∨ (b j = 3 ∧ sb < n j ∧ n j ≤ sb + nb)) ∧
      ∀ [inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2))],
        ∑ t ∈ JALocalize.arc N (m - 1), JATransfer.conv (Mavg N na (chainP 2 sa D) A)
            (Mavg N nb (chainP 3 sb D) B) t ≤
          2 * ((∏ k ∈ range na, ((∑ y, (chainP 2 sa D).w (k + 1) y) ^ 2 / (((chainP 2 sa D).q k : ℕ) : ℝ) ^ 2)) *
              (∏ k ∈ range nb, ((∑ y, (chainP 3 sb D).w (k + 1) y) ^ 2 / (((chainP 3 sb D).q k : ℕ) : ℝ) ^ 2))) *
            ((JATransfer.conv (JATransfer.conv A B) (Hs (Ftri N m)
                  ((List.range (na + nb)).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
                    (wQ D ((b j) ^ ((n j) ^ 2)))))) 0 /
                Hs (Ftri N m) ((List.range (na + nb)).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
                    (wQ D ((b j) ^ ((n j) ^ 2))))) 0) *
              ∏ i ∈ range (na + nb),
                (Hs (Ftri N m) (((List.range (na + nb)).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
                    (wQ D ((b j) ^ ((n j) ^ 2))))).drop i) 0 /
                  Hs (Ftri N m) (((List.range (na + nb)).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
                    (wQ D ((b j) ^ ((n j) ^ 2))))).drop (i + 1)) 0)) := by
  obtain ⟨b, n, hb, hmono, hmem, hperm⟩ := exists_sorted N D sa na sb nb
  refine ⟨b, n, hb, hmono, hmem, fun {inst} => ?_⟩
  have hZa : ∀ k, 0 < ∑ y, (chainP 2 sa D).w (k + 1) y := fun k => JAFinal.sum_wQ_pos D
  have hZb : ∀ k, 0 < ∑ y, (chainP 3 sb D).w (k + 1) y := fun k => JAFinal.sum_wQ_pos D
  have h := arc_mass_product (chainP 2 sa D) (chainP 3 sb D) na nb hZa hZb A B hA hB m hm h2m _
    (hperm (inst := inst))
  simpa only [List.length_map, List.length_range] using h

#print axioms arc_mass_sorted

end JASorted
end LeanCheck
