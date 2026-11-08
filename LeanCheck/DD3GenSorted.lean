import Mathlib
import LeanCheck.DD3Sorted

/-!
# Three chains with general exponents: the chains and the sorted enumeration (Lean check)

Scope. First piece of the Lean version of the modified chains `5^{e_n}` of `TVGplus_v29` (Section 10: deletion rule, tilted
chains). In `DD3Sorted` the level `k` of the chain of the base `b` has the scale `b^{k²}`; here the exponent of the level `k`
of the chain of `b ∈ {2, 3, 5}` is an arbitrary strictly increasing sequence `E b k` (`E b k = k²` is the original case).

* `E3 e2 e3 e5`: the exponent family of three strictly increasing sequences; `keyE E`, `lpE E`: the scale `b^{E b k}` and its
  logarithm; `log_scaleE`;
* `chainE p e s D`: the chain `q_k = p^{e (s+k)}` with windows `w_{q_k}` (a `JAMulti.Chain`; `chainE_sq`: for `e k = k²` it is
  `chainP p s D`);
* `keyE_inj3`, `sortedPairs3E`, `sorted_strict3E`: distinct levels have distinct scales and the sorted list is strictly
  increasing;
* `exists_sorted3E`: the counterpart of `DD3Sorted.exists_sorted3`: sequences `b, n` with `b i ∈ {2,3,5}`, `lpE (b i) (n i)`
  strictly increasing for `i < na + nb + nc`, each `(b j, n j)` a level of one of the three chains, and the list of normalized
  kernels `normK(b_j^{E b_j n_j})` a permutation of `normKernList (chain 2) ++ (normKernList (chain 3) ++ normKernList (chain 5))`.

* `arc_mass_sorted3E`: the arc mass of `Mavg_a ∗ (Mavg_b ∗ Mavg_c)` along the sorted list (counterpart of `DD3Sorted.arc_mass_sorted3`);
* `GapE b e`: the log-gap hypothesis `sqrt (lp) < lp(n+1) - lp(n)`; `same_chain_gapE` (two distinct levels of one chain), `GapE_sq` (the
  original chains `e k = k²` satisfy it).

No growth condition on the exponents is needed for the combinatorial steps (sorting, arc mass); the gap hypothesis `GapE` is what the
later pieces use.
A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open Finset JAMerged JAProduct JAProduct2 JAMulti JAFinal2 JAWindowQ JAFarSep JATransfer JALocalize JASorted DD3Sorted

/-! ### The exponent family -/

/-- The exponents of the levels of the chains of `2`, `3`, `5`. -/
def E3 (e2 e3 e5 : ℕ → ℕ) (b : ℕ) : ℕ → ℕ := if b = 2 then e2 else if b = 3 then e3 else e5

@[simp] lemma E3_two (e2 e3 e5 : ℕ → ℕ) : E3 e2 e3 e5 2 = e2 := by simp [E3]
@[simp] lemma E3_three (e2 e3 e5 : ℕ → ℕ) : E3 e2 e3 e5 3 = e3 := by simp [E3]
@[simp] lemma E3_five (e2 e3 e5 : ℕ → ℕ) : E3 e2 e3 e5 5 = e5 := by simp [E3]

lemma E3_strictMono {e2 e3 e5 : ℕ → ℕ} (h2 : StrictMono e2) (h3 : StrictMono e3) (h5 : StrictMono e5) (b : ℕ)
    (hb : b = 2 ∨ b = 3 ∨ b = 5) : StrictMono (E3 e2 e3 e5 b) := by
  rcases hb with rfl | rfl | rfl
  · simpa using h2
  · simpa using h3
  · simpa using h5

/-- The scale of the level `k` of the chain of `b`. -/
def keyE (E : ℕ → ℕ → ℕ) (p : ℕ × ℕ) : ℕ := p.1 ^ E p.1 p.2

/-- The logarithm of the scale. -/
noncomputable def lpE (E : ℕ → ℕ → ℕ) (b n : ℕ) : ℝ := (E b n : ℝ) * Real.log b

lemma log_scaleE (E : ℕ → ℕ → ℕ) (b n : ℕ) : Real.log ((b ^ (E b n) : ℕ) : ℝ) = lpE E b n := by
  unfold lpE
  push_cast
  rw [Real.log_pow]

/-! ### The chain with general exponents -/

/-- The chain `q_k = p^{e (s+k)}` with windows `w_{q_k}`. -/
noncomputable def chainE (p : ℕ) [NeZero p] (e : ℕ → ℕ) (he : Monotone e) (s : ℕ) (D : ℝ) : Chain where
  q := fun k => p ^ (e (s + k))
  pos := fun k => Nat.pos_of_ne_zero (NeZero.ne _)
  dvd := fun k => pow_dvd_pow p (he (by omega))
  w := fun k => wQ D (p ^ (e (s + k)))

/-- The original chains are the case `e k = k²`. -/
lemma chainE_sq (p : ℕ) [NeZero p] (s : ℕ) (D : ℝ) :
    chainE p (fun n => n ^ 2) (fun a b h => Nat.pow_le_pow_left h 2) s D = chainP p s D := rfl

lemma chainE_q (p : ℕ) [NeZero p] (e : ℕ → ℕ) (he : Monotone e) (s : ℕ) (D : ℝ) (k : ℕ) :
    (chainE p e he s D).q k = p ^ (e (s + k)) := rfl

/-! ### Injectivity of the scale -/

lemma E_ne_zero {E : ℕ → ℕ → ℕ} {b : ℕ} (hE : StrictMono (E b)) {k : ℕ} (hk : 1 ≤ k) : E b k ≠ 0 := by
  have h : k ≤ E b k := hE.id_le k
  omega

lemma prime235 {b : ℕ} (hb : b = 2 ∨ b = 3 ∨ b = 5) : b.Prime := by
  rcases hb with rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three
  · exact Nat.prime_five

lemma keyE_inj_gen {E : ℕ → ℕ → ℕ} (hE : ∀ b, (b = 2 ∨ b = 3 ∨ b = 5) → StrictMono (E b)) {b k b' k' : ℕ}
    (hb : b = 2 ∨ b = 3 ∨ b = 5) (hb' : b' = 2 ∨ b' = 3 ∨ b' = 5) (hk : 1 ≤ k) (hk' : 1 ≤ k')
    (h : b ^ E b k = b' ^ E b' k') : b = b' ∧ k = k' := by
  by_cases hbb : b = b'
  · subst hbb
    refine ⟨rfl, ?_⟩
    have h1 : E b k = E b k' := Nat.pow_right_injective (by rcases hb with rfl | rfl | rfl <;> norm_num) h
    exact (hE b hb).injective h1
  · exfalso
    have hnd : ¬ b ∣ b' := fun hd => hbb ((Nat.prime_dvd_prime_iff_eq (prime235 hb) (prime235 hb')).mp hd)
    exact key_ne b b' _ _ (prime235 hb) hnd (E_ne_zero (hE b hb) hk) h

lemma mem_pairs3Of_props {sa na sb nb sc nc : ℕ} {p : ℕ × ℕ} (hp : p ∈ pairs3Of sa na sb nb sc nc) :
    (p.1 = 2 ∨ p.1 = 3 ∨ p.1 = 5) ∧ 1 ≤ p.2 := by
  rw [mem_pairs3Of] at hp
  rcases hp with ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩
  · exact ⟨Or.inl rfl, by dsimp only; omega⟩
  · exact ⟨Or.inr (Or.inl rfl), by dsimp only; omega⟩
  · exact ⟨Or.inr (Or.inr rfl), by dsimp only; omega⟩

lemma keyE_inj3 {E : ℕ → ℕ → ℕ} (hE : ∀ b, (b = 2 ∨ b = 3 ∨ b = 5) → StrictMono (E b)) {sa na sb nb sc nc : ℕ} :
    ∀ p ∈ pairs3Of sa na sb nb sc nc, ∀ q ∈ pairs3Of sa na sb nb sc nc, keyE E p = keyE E q → p = q := by
  intro p hp q hq h
  obtain ⟨hp1, hp2⟩ := mem_pairs3Of_props hp
  obtain ⟨hq1, hq2⟩ := mem_pairs3Of_props hq
  obtain ⟨h1, h2⟩ := keyE_inj_gen hE hp1 hq1 hp2 hq2 h
  exact Prod.ext h1 h2

/-! ### Sorting the levels by scale -/

/-- The sorted list of pairs. -/
def sortedPairs3E (E : ℕ → ℕ → ℕ) (sa na sb nb sc nc : ℕ) : List (ℕ × ℕ) :=
  (pairs3Of sa na sb nb sc nc).mergeSort (fun p q => decide (keyE E p ≤ keyE E q))

lemma sortedPairs3E_perm (E : ℕ → ℕ → ℕ) (sa na sb nb sc nc : ℕ) :
    (sortedPairs3E E sa na sb nb sc nc).Perm (pairs3Of sa na sb nb sc nc) :=
  List.mergeSort_perm _ _

lemma sortedPairs3E_length (E : ℕ → ℕ → ℕ) (sa na sb nb sc nc : ℕ) :
    (sortedPairs3E E sa na sb nb sc nc).length = na + nb + nc := by
  unfold sortedPairs3E
  rw [List.length_mergeSort]
  simp [pairs3Of, pairsOf]
  omega

lemma sortedPairs3E_pairwise (E : ℕ → ℕ → ℕ) (sa na sb nb sc nc : ℕ) :
    (sortedPairs3E E sa na sb nb sc nc).Pairwise (fun p q => keyE E p ≤ keyE E q) := by
  have := List.pairwise_mergeSort (le := fun p q => decide (keyE E p ≤ keyE E q))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega) (pairs3Of sa na sb nb sc nc)
  simpa [sortedPairs3E] using this

/-- The sorted list is strictly increasing in the scale. -/
lemma sorted_strict3E {E : ℕ → ℕ → ℕ} (hE : ∀ b, (b = 2 ∨ b = 3 ∨ b = 5) → StrictMono (E b))
    (sa na sb nb sc nc : ℕ) (a c : ℕ) (hac : a < c) (hc : c < na + nb + nc) :
    keyE E ((sortedPairs3E E sa na sb nb sc nc).getD a (2, 0)) <
      keyE E ((sortedPairs3E E sa na sb nb sc nc).getD c (2, 0)) := by
  have hlen := sortedPairs3E_length E sa na sb nb sc nc
  have ha : a < (sortedPairs3E E sa na sb nb sc nc).length := by omega
  have hc' : c < (sortedPairs3E E sa na sb nb sc nc).length := by omega
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hc']
  have hle : keyE E ((sortedPairs3E E sa na sb nb sc nc)[a]) ≤ keyE E ((sortedPairs3E E sa na sb nb sc nc)[c]) := by
    have := (List.pairwise_iff_getElem.mp (sortedPairs3E_pairwise E sa na sb nb sc nc)) a c ha hc' hac
    exact this
  have hne : (sortedPairs3E E sa na sb nb sc nc)[a] ≠ (sortedPairs3E E sa na sb nb sc nc)[c] := by
    have hnd : (sortedPairs3E E sa na sb nb sc nc).Nodup :=
      (sortedPairs3E_perm E sa na sb nb sc nc).nodup_iff.mpr (pairs3Of_nodup _ _ _ _ _ _)
    intro h
    have := (List.Nodup.getElem_inj_iff hnd).mp h
    omega
  have hmem : ∀ i (hi : i < (sortedPairs3E E sa na sb nb sc nc).length),
      (sortedPairs3E E sa na sb nb sc nc)[i] ∈ pairs3Of sa na sb nb sc nc := fun i hi =>
    (sortedPairs3E_perm E sa na sb nb sc nc).subset (List.getElem_mem hi)
  exact lt_of_le_of_ne hle (fun h => hne (keyE_inj3 hE _ (hmem a ha) _ (hmem c hc') h))

lemma getD_mem3E (E : ℕ → ℕ → ℕ) (sa na sb nb sc nc j : ℕ) (hj : j < na + nb + nc) :
    (sortedPairs3E E sa na sb nb sc nc).getD j (2, 0) ∈ pairs3Of sa na sb nb sc nc := by
  have hlen := sortedPairs3E_length E sa na sb nb sc nc
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact (sortedPairs3E_perm E sa na sb nb sc nc).subset (List.getElem_mem _)

/-! ### The kernel list of a pair -/

section kerns

variable {N : ℕ} [NeZero N]

/-- The unit-atom kernel of the window at the scale of a pair (zero for a pair with base `0`). -/
noncomputable def FkerE (E : ℕ → ℕ → ℕ) (N : ℕ) [NeZero N] (D : ℝ) (p : ℕ × ℕ) : ZMod N → ℝ :=
  if h : 0 < p.1 then
    haveI : NeZero (keyE E p) := ⟨(pow_pos h _).ne'⟩
    normK N (keyE E p) (wQ D (keyE E p))
  else 0

lemma FkerE_eq (E : ℕ → ℕ → ℕ) (D : ℝ) (p : ℕ × ℕ) (hp : 0 < p.1) [NeZero (keyE E p)] :
    FkerE E N D p = normK N (keyE E p) (wQ D (keyE E p)) := by
  unfold FkerE
  rw [dif_pos hp]

lemma pairs3_map_FkerE {e2 e3 e5 : ℕ → ℕ} (h2 : Monotone e2) (h3 : Monotone e3) (h5 : Monotone e5) (D : ℝ)
    (sa na sb nb sc nc : ℕ) :
    (pairs3Of sa na sb nb sc nc).map (FkerE (E3 e2 e3 e5) N D) =
      normKernList N (chainE 2 e2 h2 sa D) na ++
        (normKernList N (chainE 3 e3 h3 sb D) nb ++ normKernList N (chainE 5 e5 h5 sc D) nc) := by
  unfold pairs3Of pairsOf normKernList
  simp only [List.map_append, List.map_map, List.append_assoc]
  congr 1

end kerns

/-! ### The sorted enumeration -/

/-- **The sorted enumeration of the scales of the three chains with general exponents.** -/
theorem exists_sorted3E {e2 e3 e5 : ℕ → ℕ} (h2 : StrictMono e2) (h3 : StrictMono e3) (h5 : StrictMono e5)
    (N : ℕ) [NeZero N] (D : ℝ) (sa na sb nb sc nc : ℕ) :
    ∃ b n : ℕ → ℕ, (∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5) ∧
      (∀ a c, a < c → c < na + nb + nc →
        lpE (E3 e2 e3 e5) (b a) (n a) < lpE (E3 e2 e3 e5) (b c) (n c)) ∧
      (∀ j, j < na + nb + nc → (b j = 2 ∧ sa < n j ∧ n j ≤ sa + na) ∨ (b j = 3 ∧ sb < n j ∧ n j ≤ sb + nb) ∨
        (b j = 5 ∧ sc < n j ∧ n j ≤ sc + nc)) ∧
      ∀ [inst : ∀ j, NeZero ((b j) ^ (E3 e2 e3 e5 (b j) (n j)))],
        ((List.range (na + nb + nc)).map (fun j => normK N ((b j) ^ (E3 e2 e3 e5 (b j) (n j)))
          (wQ D ((b j) ^ (E3 e2 e3 e5 (b j) (n j)))))).Perm
          (normKernList N (chainE 2 e2 h2.monotone sa D) na ++
            (normKernList N (chainE 3 e3 h3.monotone sb D) nb ++
              normKernList N (chainE 5 e5 h5.monotone sc D) nc)) := by
  classical
  set E := E3 e2 e3 e5 with hEdef
  have hE : ∀ b, (b = 2 ∨ b = 3 ∨ b = 5) → StrictMono (E b) := E3_strictMono h2 h3 h5
  set S := sortedPairs3E E sa na sb nb sc nc with hS
  have hlen : S.length = na + nb + nc := sortedPairs3E_length E sa na sb nb sc nc
  have hb2 : ∀ j, j < na + nb + nc → 2 ≤ (S.getD j (2, 0)).1 := by
    intro j hj
    have := getD_mem3E E sa na sb nb sc nc j hj
    rw [mem_pairs3Of] at this
    rcases this with ⟨k, _, hk⟩ | ⟨k, _, hk⟩ | ⟨k, _, hk⟩ <;> rw [hk] <;> norm_num
  refine ⟨fun j => (S.getD j (2, 0)).1, fun j => (S.getD j (2, 0)).2, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i < na + nb + nc
    · have := getD_mem3E E sa na sb nb sc nc i hi
      rw [mem_pairs3Of] at this
      rcases this with ⟨k, _, hk⟩ | ⟨k, _, hk⟩ | ⟨k, _, hk⟩
      · left; show (S.getD i (2, 0)).1 = 2; rw [hk]
      · right; left; show (S.getD i (2, 0)).1 = 3; rw [hk]
      · right; right; show (S.getD i (2, 0)).1 = 5; rw [hk]
    · left
      show (S.getD i (2, 0)).1 = 2
      rw [List.getD_eq_default _ _ (by omega)]
  · intro a c hac hc
    have hk := sorted_strict3E hE sa na sb nb sc nc a c hac hc
    have hba := hb2 a (by omega)
    have hbc := hb2 c hc
    have h1 : Real.log (((S.getD a (2, 0)).1 ^ (E (S.getD a (2, 0)).1 (S.getD a (2, 0)).2) : ℕ) : ℝ) =
        lpE E (S.getD a (2, 0)).1 (S.getD a (2, 0)).2 := log_scaleE _ _ _
    have h2' : Real.log (((S.getD c (2, 0)).1 ^ (E (S.getD c (2, 0)).1 (S.getD c (2, 0)).2) : ℕ) : ℝ) =
        lpE E (S.getD c (2, 0)).1 (S.getD c (2, 0)).2 := log_scaleE _ _ _
    show lpE E (S.getD a (2, 0)).1 (S.getD a (2, 0)).2 < lpE E (S.getD c (2, 0)).1 (S.getD c (2, 0)).2
    rw [← h1, ← h2']
    apply Real.log_lt_log
    · have : 0 < (S.getD a (2, 0)).1 ^ (E (S.getD a (2, 0)).1 (S.getD a (2, 0)).2) := pow_pos (by omega) _
      exact_mod_cast this
    · exact_mod_cast hk
  · intro j hj
    have := getD_mem3E E sa na sb nb sc nc j hj
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
    have h1 : (List.range (na + nb + nc)).map (fun j => normK N ((S.getD j (2, 0)).1 ^ (E (S.getD j (2, 0)).1 (S.getD j (2, 0)).2))
          (wQ D ((S.getD j (2, 0)).1 ^ (E (S.getD j (2, 0)).1 (S.getD j (2, 0)).2)))) =
        (List.range (na + nb + nc)).map (fun j => FkerE E N D (S.getD j (2, 0))) := by
      apply List.map_congr_left
      intro j hj
      have hj' : j < na + nb + nc := List.mem_range.mp hj
      have : NeZero (keyE E (S.getD j (2, 0))) := inst j
      exact (FkerE_eq E D (S.getD j (2, 0)) (by have := hb2 j hj'; omega)).symm
    have h2'' : (List.range (na + nb + nc)).map (fun j => FkerE E N D (S.getD j (2, 0))) =
        S.map (FkerE E N D) := by
      rw [← hlen]
      exact map_range_getD (FkerE E N D) S (2, 0)
    have h3' : (S.map (FkerE E N D)).Perm ((pairs3Of sa na sb nb sc nc).map (FkerE E N D)) :=
      (sortedPairs3E_perm E sa na sb nb sc nc).map _
    show ((List.range (na + nb + nc)).map (fun j => normK N ((S.getD j (2, 0)).1 ^ (E (S.getD j (2, 0)).1 (S.getD j (2, 0)).2))
          (wQ D ((S.getD j (2, 0)).1 ^ (E (S.getD j (2, 0)).1 (S.getD j (2, 0)).2))))).Perm _
    rw [h1, h2'', ← pairs3_map_FkerE h2.monotone h3.monotone h5.monotone D sa na sb nb sc nc]
    exact h3'

/-! ### The arc mass along the sorted list -/

section arcmass

variable {N : ℕ} [NeZero N]

/-- **The arc mass along the sorted list of the scales of the three chains with general exponents**
(counterpart of `DD3Sorted.arc_mass_sorted3`). -/
theorem arc_mass_sorted3E {e2 e3 e5 : ℕ → ℕ} (h2 : StrictMono e2) (h3 : StrictMono e3) (h5 : StrictMono e5)
    (D : ℝ) (sa na sb nb sc nc : ℕ) (A B C : ZMod N → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x) (hC : ∀ x, 0 ≤ C x) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N) :
    ∃ b n : ℕ → ℕ, (∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5) ∧
      (∀ a c, a < c → c < na + nb + nc →
        lpE (E3 e2 e3 e5) (b a) (n a) < lpE (E3 e2 e3 e5) (b c) (n c)) ∧
      (∀ j, j < na + nb + nc → (b j = 2 ∧ sa < n j ∧ n j ≤ sa + na) ∨ (b j = 3 ∧ sb < n j ∧ n j ≤ sb + nb) ∨
        (b j = 5 ∧ sc < n j ∧ n j ≤ sc + nc)) ∧
      ∀ [inst : ∀ j, NeZero ((b j) ^ (E3 e2 e3 e5 (b j) (n j)))],
        ∑ t ∈ arc N (m - 1), conv (Mavg N na (chainE 2 e2 h2.monotone sa D) A)
            (conv (Mavg N nb (chainE 3 e3 h3.monotone sb D) B) (Mavg N nc (chainE 5 e5 h5.monotone sc D) C)) t ≤
          2 * ((∏ k ∈ range na, ((∑ y, (chainE 2 e2 h2.monotone sa D).w (k + 1) y) ^ 2 /
                  (((chainE 2 e2 h2.monotone sa D).q k : ℕ) : ℝ) ^ 2)) *
              (∏ k ∈ range nb, ((∑ y, (chainE 3 e3 h3.monotone sb D).w (k + 1) y) ^ 2 /
                  (((chainE 3 e3 h3.monotone sb D).q k : ℕ) : ℝ) ^ 2)) *
              (∏ k ∈ range nc, ((∑ y, (chainE 5 e5 h5.monotone sc D).w (k + 1) y) ^ 2 /
                  (((chainE 5 e5 h5.monotone sc D).q k : ℕ) : ℝ) ^ 2))) *
            ((conv (conv A (conv B C)) (Hs (Ftri N m)
                  ((List.range (na + nb + nc)).map (fun j => normK N ((b j) ^ (E3 e2 e3 e5 (b j) (n j)))
                    (wQ D ((b j) ^ (E3 e2 e3 e5 (b j) (n j))))))) 0 /
                Hs (Ftri N m) ((List.range (na + nb + nc)).map (fun j => normK N ((b j) ^ (E3 e2 e3 e5 (b j) (n j)))
                    (wQ D ((b j) ^ (E3 e2 e3 e5 (b j) (n j)))))) 0) *
              ∏ i ∈ range (na + nb + nc),
                (Hs (Ftri N m) (((List.range (na + nb + nc)).map (fun j => normK N ((b j) ^ (E3 e2 e3 e5 (b j) (n j)))
                    (wQ D ((b j) ^ (E3 e2 e3 e5 (b j) (n j)))))).drop i) 0 /
                  Hs (Ftri N m) (((List.range (na + nb + nc)).map (fun j => normK N ((b j) ^ (E3 e2 e3 e5 (b j) (n j)))
                    (wQ D ((b j) ^ (E3 e2 e3 e5 (b j) (n j)))))).drop (i + 1)) 0)) := by
  obtain ⟨b, n, hb, hmono, hmem, hperm⟩ := exists_sorted3E h2 h3 h5 N D sa na sb nb sc nc
  refine ⟨b, n, hb, hmono, hmem, fun {inst} => ?_⟩
  have hZa : ∀ k, 0 < ∑ y, (chainE 2 e2 h2.monotone sa D).w (k + 1) y := fun k => JAFinal.sum_wQ_pos D
  have hZb : ∀ k, 0 < ∑ y, (chainE 3 e3 h3.monotone sb D).w (k + 1) y := fun k => JAFinal.sum_wQ_pos D
  have hZc : ∀ k, 0 < ∑ y, (chainE 5 e5 h5.monotone sc D).w (k + 1) y := fun k => JAFinal.sum_wQ_pos D
  have h := arc_mass_product3 (chainE 2 e2 h2.monotone sa D) (chainE 3 e3 h3.monotone sb D)
    (chainE 5 e5 h5.monotone sc D) na nb nc hZa hZb hZc A B C hA hB hC m hm h2m _ (hperm (inst := inst))
  simpa only [List.length_map, List.length_range] using h

end arcmass

/-! ### The gap hypothesis -/

/-- The log-gap hypothesis for the chain of `b` with exponent sequence `e`: consecutive logarithms of the scales differ by more
than the square root of the smaller one (this is `JAMerged.same_chain_gap` for `n < n + 1`). -/
def GapE (b : ℕ) (e : ℕ → ℕ) : Prop :=
  ∀ n, Real.sqrt ((e n : ℝ) * Real.log b) < (e (n + 1) : ℝ) * Real.log b - (e n : ℝ) * Real.log b

/-- Two distinct levels of one chain: the logarithms differ by more than the square root of the smaller one. -/
lemma same_chain_gapE {b : ℕ} (hb : 2 ≤ b) {e : ℕ → ℕ} (he : StrictMono e) (hg : GapE b e) {n m : ℕ}
    (hnm : n < m) :
    Real.sqrt (lpE (fun _ => e) b n) < lpE (fun _ => e) b m - lpE (fun _ => e) b n := by
  have hlog : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b))
  have h1 := hg n
  have h2 : (e (n + 1) : ℝ) ≤ e m := by exact_mod_cast he.monotone hnm
  unfold lpE
  have := mul_le_mul_of_nonneg_right h2 hlog
  linarith

/-- The original chains `e k = k²` satisfy the gap hypothesis. -/
lemma GapE_sq {b : ℕ} (hb : 2 ≤ b) : GapE b (fun n => n ^ 2) := by
  intro n
  have h := JAMerged.same_chain_gap hb (Nat.lt_succ_self n)
  unfold JAMerged.lp at h
  push_cast
  simpa using h

end DD3Gen
end LeanCheck
