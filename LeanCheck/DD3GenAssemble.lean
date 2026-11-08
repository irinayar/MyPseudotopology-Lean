import Mathlib
import LeanCheck.DD3Assemble
import LeanCheck.DD3GenProduct

/-!
# Three chains with general exponents: classification of the levels and the product bound (Lean check)

Scope. Counterpart of `DD3Assemble` (and of `JAAssemble.klist`, `fac_bounds`) for the chains with general exponents `Ex b k`
(`DD3GenSorted`), under the log-gap hypothesis `OK3 Ex` (`DD3GenGrowth`). The text is that of `DD3Assemble` with the exponent
`n²` replaced by `Ex b n` (`lpE Ex b n` for `lp b n`) and the lemmas of `DD3GenGrowth` and `DD3GenProduct` in place of their
square counterparts:

* `HTT3E Ex a T₁`, `BadTripleE`, `HFinE`: the two-term separation and the finiteness of bad triples for the levels with
  exponents `Ex` (the hypotheses of the density theorem for the modified chains);
* `klistE`, `fac_boundsE`: the list of normalized kernels of the scales `b_j^(Ex b_j n_j)` and the bounds `1 ≤ f_i ≤ 30 D/7`;
* `bases_differE`, `level_sep3E`, `level_close3E`: the per-level bounds (the cluster estimates of `DD3Cluster` are stated for an
  arbitrary scale sequence; the growth hypotheses come from `hgrow3_of_mergedE`, `hmon_of_mergedE`);
* `non_deep_card_le_threeE`: at most three non-deep levels (`window_card_le_threeE`);
* `prod_f_bound3E`: for large `X`, `∏ f_i ≤ Cp` with `Cp` independent of `L`, `N`, `m`, under `HTT3E` and `HFinE`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open Finset JATransfer JAProduct JAProduct2 JAMulti JAFinal2 JAWindowQ JAFarSep JACenter JASep JAClose JAFar JAAssemble
  JANonDeep

/-- The list of normalized kernels of the scales `b_j^(Ex b_j n_j)`, `j < L`. -/
noncomputable def klistE (Ex : ℕ → ℕ → ℕ) (N : ℕ) [NeZero N] (D : ℝ) (L : ℕ) (b n : ℕ → ℕ)
    [∀ j, NeZero ((b j) ^ (Ex (b j) (n j)))] : List (ZMod N → ℝ) :=
  (List.range L).map (fun j => normK N ((b j) ^ (Ex (b j) (n j))) (wQ D ((b j) ^ (Ex (b j) (n j)))))

/-- The factors lie in `[1, 30 D / 7]`. -/
lemma fac_boundsE {Ex : ℕ → ℕ → ℕ} {N : ℕ} [NeZero N] (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (b n : ℕ → ℕ) [inst : ∀ j, NeZero ((b j) ^ (Ex (b j) (n j)))]
    (hQ : ∀ j, j < L → 25 * D ≤ (((b j) ^ (Ex (b j) (n j)) : ℕ) : ℝ))
    (hQN : ∀ j, j < L → (b j) ^ (Ex (b j) (n j)) ∣ N) :
    ∀ i, i < L → 1 ≤ Hs (Ftri N m) ((klistE Ex N D L b n).drop i) 0 / Hs (Ftri N m) ((klistE Ex N D L b n).drop (i + 1)) 0 ∧
      Hs (Ftri N m) ((klistE Ex N D L b n).drop i) 0 / Hs (Ftri N m) ((klistE Ex N D L b n).drop (i + 1)) 0 ≤ 30 * D / 7 := by
  have hgood : ∀ K ∈ klistE Ex N D L b n, PD K ∧ (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 ∧ ∑ x, K x ≤ 30 * D / 7 := by
    intro K hK
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hK
    have hjL : j < L := List.mem_range.mp hj
    obtain ⟨h1, h2, h3⟩ := normK_props (N := N) D hD ((b j) ^ (Ex (b j) (n j))) (hQ j hjL) (hQN j hjL)
    exact ⟨h1, normK_nonneg _ _, h2, h3⟩
  have hlen : (klistE Ex N D L b n).length = L := by simp [klistE]
  have key := factors_bounded (N := N) (Ftri N m) (Ftri_PD m) (by rw [Ftri_zero m hm h2m]) (30 * D / 7)
    (klistE Ex N D L b n) hgood
  intro i hi
  exact key i (by rw [hlen]; exact hi)

/-- The two-term separation for ordered pairs of distinct bases in `{2,3,5}`. -/
def HTT3E (Ex : ℕ → ℕ → ℕ) (a : ℝ → ℝ) (T₁ : ℝ) : Prop :=
  ∀ (b n b' n' : ℕ), (b = 2 ∨ b = 3 ∨ b = 5) → (b' = 2 ∨ b' = 3 ∨ b' = 5) → b ≠ b' → 1 ≤ n → 1 ≤ n' →
      T₁ ≤ Real.sqrt (Real.log ((b ^ (Ex b n) : ℕ) : ℝ)) → b ^ (Ex b n) < b' ^ (Ex b' n') →
      ((b' ^ (Ex b' n') : ℕ) : ℝ) < Real.sqrt (Real.log ((b ^ (Ex b n) : ℕ) : ℝ)) * ((b ^ (Ex b n) : ℕ) : ℝ) →
      ∀ r s : ℤ, r ≠ 0 → |r| ≤ (⌈(Real.sqrt (Real.log ((b ^ (Ex b n) : ℕ) : ℝ))) ^ 2⌉₊ : ℤ) →
        |s| ≤ (⌈4 * (Real.sqrt (Real.log ((b ^ (Ex b n) : ℕ) : ℝ))) ^ 3⌉₊ : ℤ) →
        Real.exp (-(a (Real.sqrt (Real.log ((b ^ (Ex b n) : ℕ) : ℝ))))) /
            ((b ^ (Ex b n) : ℕ) : ℝ) ≤
          MixedPrime.nrm ((r : ℝ) / ((b ^ (Ex b n) : ℕ) : ℝ) + (s : ℝ) / ((b' ^ (Ex b' n') : ℕ) : ℝ))

/-- A *bad triple* of levels: three levels of the bases `2,3,5` in increasing order, the second a close pair with the first
and the third inside the window `Q_p exp(a(t) + log t)` (`t = sqrt (log Q_p)`). -/
def BadTripleE (Ex : ℕ → ℕ → ℕ) (a : ℝ → ℝ) (x : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) : Prop :=
  (x.1.1 = 2 ∨ x.1.1 = 3 ∨ x.1.1 = 5) ∧ (x.2.1.1 = 2 ∨ x.2.1.1 = 3 ∨ x.2.1.1 = 5) ∧
  (x.2.2.1 = 2 ∨ x.2.2.1 = 3 ∨ x.2.2.1 = 5) ∧ 1 ≤ x.1.2 ∧ 1 ≤ x.2.1.2 ∧ 1 ≤ x.2.2.2 ∧
  lpE Ex x.1.1 x.1.2 < lpE Ex x.2.1.1 x.2.1.2 ∧
  lpE Ex x.2.1.1 x.2.1.2 < lpE Ex x.2.2.1 x.2.2.2 ∧
  (((x.2.1.1) ^ (Ex x.2.1.1 x.2.1.2) : ℕ) : ℝ) <
    Real.sqrt (lpE Ex x.1.1 x.1.2) * (((x.1.1) ^ (Ex x.1.1 x.1.2) : ℕ) : ℝ) ∧
  (((x.2.2.1) ^ (Ex x.2.2.1 x.2.2.2) : ℕ) : ℝ) <
    (((x.1.1) ^ (Ex x.1.1 x.1.2) : ℕ) : ℝ) *
      Real.exp (a (Real.sqrt (lpE Ex x.1.1 x.1.2)) + Real.log (Real.sqrt (lpE Ex x.1.1 x.1.2)))

/-- **`H(2,3,5)` in the form used here**: at most `K₁` bad triples. -/
def HFinE (Ex : ℕ → ℕ → ℕ) (a : ℝ → ℝ) (K₁ : ℕ) : Prop :=
  ∀ s : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)), (∀ x ∈ s, BadTripleE Ex a x) → s.card ≤ K₁

/-! ### Copies of the per-level lemmas for three bases -/

/-- Close levels have different primes. -/
lemma bases_differE {Ex : ℕ → ℕ → ℕ} (hEx : OK3 Ex) (L : ℕ) (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : ∀ a c, a < c → c < L → lpE Ex (b a) (n a) < lpE Ex (b c) (n c))
    (p : ℕ) (hp1 : p + 1 < L)
    (hclose : (((b (p + 1)) ^ (Ex (b (p + 1)) (n (p + 1))) : ℕ) : ℝ) <
      Real.sqrt (lpE Ex (b p) (n p)) * (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ)) :
    b p ≠ b (p + 1) := by
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h | h <;> omega
  intro heq
  have hlt := hmono p (p + 1) (Nat.lt_succ_self p) hp1
  rw [← heq] at hlt
  have hnm : n p < n (p + 1) := lpE_strict (hb2 p) (hEx _ (hb p)).1 hlt
  have hgap := same_chain_gapE' (E := Ex) (hb2 p) (hEx _ (hb p)).1 (hEx _ (hb p)).2 hnm
  have e1 := exp_lpE Ex (b p) (n p) (hb2 p)
  have e2 := exp_lpE Ex (b p) (n (p + 1)) (hb2 p)
  rw [← heq] at hclose
  rw [← e1, ← e2] at hclose
  set l0 := lpE Ex (b p) (n p)
  set l1 := lpE Ex (b p) (n (p + 1))
  have hexp : Real.exp l1 = Real.exp l0 * Real.exp (l1 - l0) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : (l1 - l0) + 1 ≤ Real.exp (l1 - l0) := by linarith [Real.add_one_le_exp (l1 - l0)]
  have hpos : 0 < Real.exp l0 := Real.exp_pos _
  rw [hexp] at hclose
  nlinarith

/-- Separated levels (`f_p ≤ 1 + Cs t⁻³`), three bases. -/
theorem level_sep3E {Ex : ℕ → ℕ → ℕ} (hEx : OK3 Ex) {N : ℕ} [NeZero N] (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    [inst : ∀ j, NeZero ((b j) ^ (Ex (b j) (n j)))]
    (hmono : ∀ a c, a < c → c < L → lpE Ex (b a) (n a) < lpE Ex (b c) (n c))
    (hQ : ∀ j, j < L → 25 * D ≤ (((b j) ^ (Ex (b j) (n j)) : ℕ) : ℝ))
    (hQN : ∀ j, j < L → (b j) ^ (Ex (b j) (n j)) ∣ N)
    (p : ℕ) (hp : p < L)
    (ht2 : 2 ≤ Real.sqrt (lpE Ex (b p) (n p)))
    (htop : (8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (lpE Ex (b p) (n p)))) ≤ 1 / 2)
    (hε : (2 * m : ℝ) / N ≤ 3 / (4 * (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ)))
    (hsep : p + 1 < L → Real.sqrt (lpE Ex (b p) (n p)) * (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ) ≤
      (((b (p + 1)) ^ (Ex (b (p + 1)) (n (p + 1))) : ℕ) : ℝ)) :
    Hs (Ftri N m) ((klistE Ex N D L b n).drop p) 0 / Hs (Ftri N m) ((klistE Ex N D L b n).drop (p + 1)) 0 ≤
      1 + (200 * D ^ 4 + 30 * D / 7 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
        ((1 + 8 * (30 * D / 7)) + 48 * (30 * D / 7) * (8 * (30 * D / 7)) ^ 3))) *
        (1 / Real.sqrt (lpE Ex (b p) (n p))) ^ 3 := by
  classical
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h | h <;> omega
  set t : ℝ := Real.sqrt (lpE Ex (b p) (n p)) with ht
  set M : ℕ := ⌈t * (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ)⌉₊ + 1 with hM
  obtain ⟨sc, hsc, hscM, hpos⟩ : ∃ sc : ℕ → ℕ, (∀ j, j < L → sc j = (b j) ^ (Ex (b j) (n j))) ∧
      (∀ j, L ≤ j → sc j = M) ∧ (∀ j, 0 < sc j) := by
    refine ⟨fun j => if j < L then (b j) ^ (Ex (b j) (n j)) else M, ?_, ?_, ?_⟩
    · intro j hj; simp [hj]
    · intro j hj; simp [not_lt.mpr hj]
    · intro j
      by_cases hj : j < L
      · simp only [hj, ite_true]
        exact Nat.pos_of_ne_zero (inst j).out
      · simp only [hj, ite_false]; omega
  haveI : ∀ j, NeZero (sc j) := fun j => ⟨(hpos j).ne'⟩
  have hlist : (List.range L).map (fun j => normK N (sc j) (wQ D (sc j))) = klistE Ex N D L b n := by
    unfold klistE
    apply List.map_congr_left
    intro j hj
    exact normK_congr D (hsc j (List.mem_range.mp hj))
  have hlog : Real.log ((sc p : ℕ) : ℝ) = lpE Ex (b p) (n p) := by
    rw [hsc p hp]; exact log_scaleE Ex _ _
  have hsq : Real.sqrt (Real.log ((sc p : ℕ) : ℝ)) = t := by rw [hlog]
  have hgrow : ∀ p' k, p' + k < L → (sc p' : ℝ) * Real.exp (Real.sqrt (Real.log (sc p')) * ((k / 3 : ℕ) : ℝ)) ≤
      sc (p' + k) := by
    intro p' k h
    have h1 : p' < L := by omega
    rw [hsc p' h1, hsc (p' + k) h]
    exact hgrow3_of_mergedE hEx b n L hb hmono p' k h
  have hmon' : ∀ i j, i ≤ j → j < L → sc i ≤ sc j := by
    intro i j hij hj
    rw [hsc i (by omega), hsc j hj]
    exact hmon_of_mergedE b n L hb hmono i j hij hj
  have key := DD3Cluster.separated_factor3 (N := N) D hD m hm h2m L sc
    (fun j hj => by rw [hsc j hj]; exact hQ j hj) (fun j hj => by rw [hsc j hj]; exact hQN j hj)
    hmon' hgrow p (by omega) (by rw [hsq]; exact htop) (by rw [hsc p hp]; exact hε)
    (by rw [hsq]; exact ht2)
    (by
      rw [hsq]
      by_cases h1 : p + 1 < L
      · rw [hsc p hp, hsc (p + 1) h1]; exact hsep h1
      · have h2 : p + 1 = L := by omega
        rw [hscM (p + 1) (by omega), hsc p hp]
        have := Nat.le_ceil (t * (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ))
        rw [hM, Nat.cast_add, Nat.cast_one]; linarith)
  rw [hlist, hsq] at key
  have hS := DD3Cluster.sep_cube3 D t hD (by linarith)
  linarith


set_option maxHeartbeats 1600000 in
/-- Close levels, three bases: the third level must lie outside the window `Q_p exp(a(t) + log t)`. -/
theorem level_close3E {Ex : ℕ → ℕ → ℕ} (hEx : OK3 Ex) {N : ℕ} [NeZero N] (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5) (hn : ∀ i, i < L → 1 ≤ n i)
    [inst : ∀ j, NeZero ((b j) ^ (Ex (b j) (n j)))]
    (hmono : ∀ a c, a < c → c < L → lpE Ex (b a) (n a) < lpE Ex (b c) (n c))
    (hQ : ∀ j, j < L → 25 * D ≤ (((b j) ^ (Ex (b j) (n j)) : ℕ) : ℝ))
    (hQN : ∀ j, j < L → (b j) ^ (Ex (b j) (n j)) ∣ N)
    (a : ℝ → ℝ) (T₁ : ℝ) (htt : HTT3E Ex a T₁)
    (p : ℕ) (hp1 : p + 1 < L)
    (ht2 : 2 ≤ Real.sqrt (lpE Ex (b p) (n p)))
    (hT : T₁ ≤ Real.sqrt (lpE Ex (b p) (n p)))
    (htop : (8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (lpE Ex (b p) (n p)))) ≤ 1 / 2)
    (hε : (2 * m : ℝ) / N ≤
      3 * (Real.exp (-(a (Real.sqrt (lpE Ex (b p) (n p))))) /
        (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ)) / 4)
    (hclose : (((b (p + 1)) ^ (Ex (b (p + 1)) (n (p + 1))) : ℕ) : ℝ) <
      Real.sqrt (lpE Ex (b p) (n p)) * (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ))
    (hthird : p + 2 < L → (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ) *
      Real.exp (a (Real.sqrt (lpE Ex (b p) (n p))) + Real.log (Real.sqrt (lpE Ex (b p) (n p)))) ≤
        (((b (p + 2)) ^ (Ex (b (p + 2)) (n (p + 2))) : ℕ) : ℝ)) :
    Hs (Ftri N m) ((klistE Ex N D L b n).drop p) 0 / Hs (Ftri N m) ((klistE Ex N D L b n).drop (p + 1)) 0 ≤
      1 + (200 * D ^ 4 / (Real.sqrt (lpE Ex (b p) (n p))) ^ 6 +
          30 * D / 7 * (200 * D ^ 4 / (4 * (Real.sqrt (lpE Ex (b p) (n p))) ^ 3) ^ 3) +
          (30 * D / 7) ^ 2 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
            (1 / (Real.exp (-(a (Real.sqrt (lpE Ex (b p) (n p))))) /
              (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ) * (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ))) ^ 3 *
            (Real.exp (-(3 * (a (Real.sqrt (lpE Ex (b p) (n p))) +
                Real.log (Real.sqrt (lpE Ex (b p) (n p)))))) +
              6 * ((8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (lpE Ex (b p) (n p)))))))) := by
  classical
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h | h <;> omega
  have hlog : ∀ j, Real.log (((b j) ^ (Ex (b j) (n j)) : ℕ) : ℝ) = lpE Ex (b j) (n j) :=
    fun j => log_scaleE Ex _ _
  have hbd := bases_differE hEx L b n hb hmono p hp1 hclose
  have hQQ : (b p) ^ (Ex (b p) (n p)) < (b (p + 1)) ^ (Ex (b (p + 1)) (n (p + 1))) := by
    have hlt := hmono p (p + 1) (Nat.lt_succ_self p) hp1
    rw [← hlog p, ← hlog (p + 1)] at hlt
    have hp0 : (0 : ℝ) < (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ) := by
      have : 0 < (b p) ^ (Ex (b p) (n p)) := Nat.pos_of_ne_zero (inst p).out
      exact_mod_cast this
    have := (Real.log_lt_log_iff hp0 (by
      have : 0 < (b (p + 1)) ^ (Ex (b (p + 1)) (n (p + 1))) := Nat.pos_of_ne_zero (inst (p + 1)).out
      exact_mod_cast this)).mp hlt
    exact_mod_cast this
  have hTT : ∀ r s : ℤ, r ≠ 0 →
      |r| ≤ (⌈(Real.sqrt (Real.log (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ))) ^ 2⌉₊ : ℤ) →
      |s| ≤ (⌈4 * (Real.sqrt (Real.log (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ))) ^ 3⌉₊ : ℤ) →
      Real.exp (-(a (Real.sqrt (Real.log (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ))))) /
          (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ) ≤
        MixedPrime.nrm ((r : ℝ) / (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ) +
          (s : ℝ) / (((b (p + 1)) ^ (Ex (b (p + 1)) (n (p + 1))) : ℕ) : ℝ)) := by
    exact htt (b p) (n p) (b (p + 1)) (n (p + 1)) (hb p) (hb (p + 1)) hbd (hn p (by omega)) (hn (p + 1) hp1) (by rw [hlog p]; exact hT) hQQ
      (by rw [hlog p]; exact hclose)
  have key := DD3Cluster.close_factor3 (N := N) D hD m hm h2m L (fun j => (b j) ^ (Ex (b j) (n j))) hQ hQN
    (hgrow3_of_mergedE hEx b n L hb hmono) p (by omega) (by rw [hlog p]; exact htop)
    (by rw [hlog p]; exact ht2) a (fun h2 => by rw [hlog p]; exact hthird h2) (by rw [hlog p]; exact hε) hTT
  unfold klistE
  rw [hlog p] at key
  linarith

theorem non_deep_card_le_threeE {Ex : ℕ → ℕ → ℕ} (hEx : OK3 Ex) (D : ℝ) (a : ℝ → ℝ) (hD : 1 ≤ D) (hp : WindowProfile a) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ s : Finset (ℕ × ℕ),
      (∀ p ∈ s, (p.1 = 2 ∨ p.1 = 3 ∨ p.1 = 5) ∧ 1 ≤ p.2 ∧ ((p.1 ^ (Ex p.1 p.2) : ℕ) : ℝ) ≤ D * X ∧
        X < 4 * ((p.1 ^ (Ex p.1 p.2) : ℕ) : ℝ) *
          Real.exp (a (Real.sqrt (Real.log ((p.1 ^ (Ex p.1 p.2) : ℕ) : ℝ))))) →
      s.card ≤ 3 := by
  set c : ℝ := Real.log D + Real.log 4 with hc
  have hc0 : 0 ≤ c := by
    have h1 : 0 ≤ Real.log D := Real.log_nonneg hD
    have h2 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [hc]; linarith
  obtain ⟨S₀, hS₀0, hS₀⟩ := hp.window c hc0
  refine ⟨Real.exp (S₀ ^ 2), ?_⟩
  intro X hX s hs
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hDX : 0 < D * X := by positivity
  have hlogDX : S₀ ^ 2 ≤ Real.log (D * X) := by
    have h1 : S₀ ^ 2 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
    have h2 : 0 ≤ Real.log D := Real.log_nonneg hD
    rw [Real.log_mul (by linarith) hXpos.ne']
    linarith
  set S : ℝ := Real.sqrt (Real.log (D * X)) with hS
  have hlogDX0 : 0 ≤ Real.log (D * X) := le_trans (sq_nonneg _) hlogDX
  have hS2 : S ^ 2 = Real.log (D * X) := Real.sq_sqrt hlogDX0
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSS₀ : S₀ ≤ S := by
    rw [hS]; exact Real.le_sqrt_of_sq_le hlogDX
  have hpoly := hS₀ S hSS₀
  set w : ℝ := c + a S with hw
  have hw0 : 0 ≤ w := by
    have := hp.nonneg S hS0
    rw [hw]; linarith
  have hlogDX_split : Real.log (D * X) = Real.log D + Real.log X := Real.log_mul (by linarith) hXpos.ne'
  apply window_card_le_threeE hEx s (S ^ 2 - w) (S ^ 2)
  · -- window width
    have hu : w ^ 2 ≤ S ^ 2 - w := by linarith
    have : w ≤ Real.sqrt (S ^ 2 - w) :=
      calc w = Real.sqrt (w ^ 2) := (Real.sqrt_sq hw0).symm
        _ ≤ Real.sqrt (S ^ 2 - w) := Real.sqrt_le_sqrt hu
    linarith
  · intro p hp'
    obtain ⟨hb, hn, hQle, hnd⟩ := hs p hp'
    have hbpos : 2 ≤ p.1 := by rcases hb with h | h | h <;> omega
    have hQpos : (0 : ℝ) < ((p.1 ^ (Ex p.1 p.2) : ℕ) : ℝ) := by
      have : 0 < p.1 ^ (Ex p.1 p.2) := pow_pos (by omega) _
      exact_mod_cast this
    have hlp : lpE Ex p.1 p.2 = Real.log ((p.1 ^ (Ex p.1 p.2) : ℕ) : ℝ) := (log_scaleE Ex _ _).symm
    refine ⟨hb, ?_, ?_⟩
    · -- lower end
      rw [hlp]
      set Q : ℝ := ((p.1 ^ (Ex p.1 p.2) : ℕ) : ℝ) with hQ
      set tq : ℝ := Real.sqrt (Real.log Q) with htq
      have hlogQ_le : Real.log Q ≤ S ^ 2 := by
        rw [hS2]; exact Real.log_le_log hQpos hQle
      have htq_le : tq ≤ S := by
        rw [htq, hS]
        apply Real.sqrt_le_sqrt
        rw [← hS2]; exact hlogQ_le
      have htq0 : 0 ≤ tq := Real.sqrt_nonneg _
      have hexp : Real.exp (a tq) ≤ Real.exp (a S) :=
        Real.exp_le_exp.mpr (hp.mono tq S htq0 htq_le)
      have hnd' : X < 4 * Q * Real.exp (a S) :=
        lt_of_lt_of_le hnd (by
          apply mul_le_mul_of_nonneg_left hexp (by positivity))
      have hlogX : Real.log X < Real.log (4 * Q * Real.exp (a S)) :=
        Real.log_lt_log hXpos hnd'
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by norm_num) hQpos.ne',
        Real.log_exp] at hlogX
      rw [hw, hc]
      linarith
    · rw [hlp, hS2]
      exact Real.log_le_log hQpos hQle


/-! ### The product of the factors is bounded, three bases -/

/-- **The product of the factors is bounded** for the sorted list of prime-square scales of the bases `2, 3, 5`
(analogue of `JACentral.prod_f_bound`), under the separation hypothesis `HTT3` and the finiteness hypothesis `HFin`. -/
theorem prod_f_bound3E {Ex : ℕ → ℕ → ℕ} (hEx : OK3 Ex) (D : ℝ) (a : ℝ → ℝ) (hD : 3 ≤ D) (ha : WindowProfile a) (hG : CloseGrowth a)
    (T₁ : ℝ) (htt : HTT3E Ex a T₁) (K₁ : ℕ) (hH : HFinE Ex a K₁) :
    ∃ Cp X₀ : ℝ, 0 < Cp ∧ ∀ (X N m L : ℕ) [NeZero N] (b n : ℕ → ℕ)
      [inst : ∀ j, NeZero ((b j) ^ (Ex (b j) (n j)))],
      X₀ ≤ (X : ℝ) → (∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5) → (∀ i, i < L → 1 ≤ n i) →
      (∀ a c, a < c → c < L → lpE Ex (b a) (n a) < lpE Ex (b c) (n c)) →
      1 ≤ m → 2 * m ≤ N →
      (∀ j, j < L → 25 * D ≤ (((b j) ^ (Ex (b j) (n j)) : ℕ) : ℝ)) →
      (∀ j, j < L → (b j) ^ (Ex (b j) (n j)) ∣ N) →
      (∀ j, j < L → (((b j) ^ (Ex (b j) (n j)) : ℕ) : ℝ) ≤ D * X) →
      (2 * m : ℝ) / N ≤ 3 / X →
      ∏ i ∈ range L, (Hs (Ftri N m) ((klistE Ex N D L b n).drop i) 0 /
        Hs (Ftri N m) ((klistE Ex N D L b n).drop (i + 1)) 0) ≤ Cp := by
  classical
  obtain ⟨Tc, hTc1, hcc⟩ := DD3Cluster.close_cube3_G D a hD hG
  obtain ⟨X₀', hX₀'⟩ := non_deep_card_le_threeE hEx D a (by linarith) ha
  have hD0 : 0 < D := by linarith
  have hB1 : 1 ≤ 30 * D / 7 := by linarith
  obtain ⟨Cs, hCs⟩ : ∃ Cs : ℝ, Cs = 200 * D ^ 4 + 30 * D / 7 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
        ((1 + 8 * (30 * D / 7)) + 48 * (30 * D / 7) * (8 * (30 * D / 7)) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = 200 * D ^ 4 + 30 * D / 7 * (200 * D ^ 4) +
        (30 * D / 7) ^ 2 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) * (1 + 6 * (8 * (30 * D / 7)) ^ 3)) :=
    ⟨_, rfl⟩
  have hCs0 : 0 ≤ Cs := by rw [hCs]; positivity
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  obtain ⟨Tbig, hTbig⟩ : ∃ T : ℝ, T = max (max 2 ((8 * (30 * D / 7)) ^ 3)) (max T₁ Tc) := ⟨_, rfl⟩
  have hTb2 : 2 ≤ Tbig := by
    rw [hTbig]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hTbB : (8 * (30 * D / 7)) ^ 3 ≤ Tbig := by
    rw [hTbig]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hTbT : T₁ ≤ Tbig := by
    rw [hTbig]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hTbc : Tc ≤ Tbig := by
    rw [hTbig]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨(30 * D / 7) ^ (3 + K₁ + 3 * ⌊4 * Tbig ^ 2⌋₊) * Real.exp ((Cs + Cc) * (3 * (8 * Zeta32))),
    max X₀' 1, by positivity, ?_⟩
  intro X N m L _ b n inst hX hb hn hmono hm h2m hQ hQN hQX hmN
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hXN : X₀' ≤ (X : ℝ) := le_trans (le_max_left _ _) hX
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h | h <;> omega
  have hlog : ∀ j, Real.log (((b j) ^ (Ex (b j) (n j)) : ℕ) : ℝ) = lpE Ex (b j) (n j) :=
    fun j => log_scaleE Ex _ _
  have hQpos : ∀ j, (0 : ℝ) < (((b j) ^ (Ex (b j) (n j)) : ℕ) : ℝ) := fun j => by
    have : 0 < (b j) ^ (Ex (b j) (n j)) := Nat.pos_of_ne_zero (inst j).out
    exact_mod_cast this
  -- the non-deep levels
  set E₀ : Finset ℕ := (range L).filter (fun i => ¬ (4 * (((b i) ^ (Ex (b i) (n i)) : ℕ) : ℝ) *
      Real.exp (a (Real.sqrt (Real.log (((b i) ^ (Ex (b i) (n i)) : ℕ) : ℝ)))) ≤ X)) with hE₀
  have hE₀card : E₀.card ≤ 3 := by
    have hinj := period_injE L b n hmono
    have h1 : (E₀.image (fun i => (b i, n i))).card = E₀.card :=
      Finset.card_image_of_injOn (hinj.mono (fun i hi => Finset.mem_coe.mpr (Finset.mem_filter.mp hi).1))
    rw [← h1]
    apply hX₀' X hXN
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hiL, hiE⟩ := Finset.mem_filter.mp hi
    have hiL' := Finset.mem_range.mp hiL
    exact ⟨hb i, hn i hiL', hQX i hiL', not_le.mp hiE⟩
  -- the close pairs with the third level inside the window
  set E₁ : Finset ℕ := (range L).filter (fun i => i + 2 < L ∧
      (((b (i + 1)) ^ (Ex (b (i + 1)) (n (i + 1))) : ℕ) : ℝ) <
        Real.sqrt (lpE Ex (b i) (n i)) * (((b i) ^ (Ex (b i) (n i)) : ℕ) : ℝ) ∧
      ¬ ((((b i) ^ (Ex (b i) (n i)) : ℕ) : ℝ) *
        Real.exp (a (Real.sqrt (lpE Ex (b i) (n i))) + Real.log (Real.sqrt (lpE Ex (b i) (n i)))) ≤
          (((b (i + 2)) ^ (Ex (b (i + 2)) (n (i + 2))) : ℕ) : ℝ))) with hE₁
  have hE₁card : E₁.card ≤ K₁ := by
    have hinj := period_injE L b n hmono
    set g : ℕ → (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) :=
      fun i => ((b i, n i), (b (i + 1), n (i + 1)), (b (i + 2), n (i + 2))) with hg
    have hginj : Set.InjOn g (E₁ : Set ℕ) := by
      intro i hi j hj hij
      have hiL := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
      have hjL := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1
      have h1 : (b i, n i) = (b j, n j) := congrArg (fun x => x.1) hij
      exact hinj (Finset.mem_coe.mpr (Finset.mem_range.mpr hiL))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr hjL)) h1
    rw [← Finset.card_image_of_injOn hginj]
    apply hH
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hiL, h2L, hcl, hnt⟩ := Finset.mem_filter.mp hi
    have hiL' := Finset.mem_range.mp hiL
    exact ⟨hb i, hb (i + 1), hb (i + 2), hn i hiL', hn (i + 1) (by omega), hn (i + 2) h2L,
      hmono i (i + 1) (by omega) (by omega), hmono (i + 1) (i + 2) (by omega) h2L, hcl, not_le.mp hnt⟩
  set E : Finset ℕ := E₀ ∪ E₁ with hE
  have hEcard : E.card ≤ 3 + K₁ := by
    have : E.card ≤ E₀.card + E₁.card := Finset.card_union_le E₀ E₁
    omega
  have hfB := fac_boundsE D hD m hm h2m L b n hQ hQN
  have hgood : ∀ i, i < L → i ∉ E → Tbig ≤ Real.sqrt (lpE Ex (b i) (n i)) →
      Hs (Ftri N m) ((klistE Ex N D L b n).drop i) 0 / Hs (Ftri N m) ((klistE Ex N D L b n).drop (i + 1)) 0 ≤
        1 + (Cs + Cc) * (1 / Real.sqrt (lpE Ex (b i) (n i))) ^ 3 := by
    intro p hp hpE hT
    have hpE₀ : p ∉ E₀ := fun h => hpE (Finset.mem_union_left _ h)
    have hpE₁ : p ∉ E₁ := fun h => hpE (Finset.mem_union_right _ h)
    have hdeep : 4 * (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ) *
        Real.exp (a (Real.sqrt (Real.log (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ)))) ≤ X := by
      by_contra h
      exact hpE₀ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, h⟩)
    rw [hlog p] at hdeep
    have hQp := hQpos p
    have ht2 : 2 ≤ Real.sqrt (lpE Ex (b p) (n p)) := le_trans hTb2 hT
    have htB : (8 * (30 * D / 7)) ^ 3 ≤ Real.sqrt (lpE Ex (b p) (n p)) := le_trans hTbB hT
    have htT : T₁ ≤ Real.sqrt (lpE Ex (b p) (n p)) := le_trans hTbT hT
    have htc : Tc ≤ Real.sqrt (lpE Ex (b p) (n p)) := le_trans hTbc hT
    have htop := DD3Assemble.htop3_of_large (30 * D / 7) _ (by linarith) htB
    have hs0 : 0 ≤ (1 / Real.sqrt (lpE Ex (b p) (n p))) ^ 3 := by positivity
    have hexp1 : 1 ≤ Real.exp (a (Real.sqrt (lpE Ex (b p) (n p)))) :=
      Real.one_le_exp (ha.nonneg _ (Real.sqrt_nonneg _))
    have h4Q : 4 * (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ) ≤ X := by nlinarith
    have hrad := JANonDeep.deep_radius X (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ)
      (a (Real.sqrt (lpE Ex (b p) (n p)))) hX0 hQp hdeep
    have h3X : 3 / (X : ℝ) = 3 * (2 * (2 / X)) / 4 := by ring
    by_cases hcl : p + 1 < L ∧ (((b (p + 1)) ^ (Ex (b (p + 1)) (n (p + 1))) : ℕ) : ℝ) <
        Real.sqrt (lpE Ex (b p) (n p)) * (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ)
    · have hthird : p + 2 < L → (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ) *
          Real.exp (a (Real.sqrt (lpE Ex (b p) (n p))) +
            Real.log (Real.sqrt (lpE Ex (b p) (n p)))) ≤
          (((b (p + 2)) ^ (Ex (b (p + 2)) (n (p + 2))) : ℕ) : ℝ) := by
        intro h2
        by_contra hnt
        exact hpE₁ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, h2, hcl.2, hnt⟩)
      have h1 := level_close3E hEx D hD m hm h2m L b n hb hn hmono hQ hQN a T₁ htt p hcl.1 ht2 htT htop
        (by
          calc (2 * m : ℝ) / N ≤ 3 / X := hmN
            _ = 3 * (2 * (2 / X)) / 4 := h3X
            _ ≤ _ := by linarith) hcl.2 hthird
      have h2 := hcc (Real.sqrt (lpE Ex (b p) (n p))) (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ) htc hQp
      rw [← hCc] at h2
      have h5 : Cc * (1 / Real.sqrt (lpE Ex (b p) (n p))) ^ 3 ≤
          (Cs + Cc) * (1 / Real.sqrt (lpE Ex (b p) (n p))) ^ 3 := by
        rw [add_mul]; linarith [mul_nonneg hCs0 hs0]
      linarith
    · have h1 := level_sep3E hEx D hD m hm h2m L b n hb hmono hQ hQN p hp ht2 htop
        (by
          calc (2 * m : ℝ) / N ≤ 3 / X := hmN
            _ ≤ 3 / (4 * (((b p) ^ (Ex (b p) (n p)) : ℕ) : ℝ)) :=
                div_le_div_of_nonneg_left (by norm_num) (by positivity) h4Q)
        (fun h => by
          by_contra hh
          push Not at hh
          exact hcl ⟨h, hh⟩)
      rw [← hCs] at h1
      have h5 : Cs * (1 / Real.sqrt (lpE Ex (b p) (n p))) ^ 3 ≤
          (Cs + Cc) * (1 / Real.sqrt (lpE Ex (b p) (n p))) ^ 3 := by
        rw [add_mul]; linarith [mul_nonneg hCc0 hs0]
      linarith
  exact product_final3E hEx L b n hb hn hmono
    (fun i => Hs (Ftri N m) ((klistE Ex N D L b n).drop i) 0 /
      Hs (Ftri N m) ((klistE Ex N D L b n).drop (i + 1)) 0)
    (30 * D / 7) (Cs + Cc) Tbig hB1 (by linarith) (fun i hi => hfB i hi) E (3 + K₁) hEcard hgood


end DD3Gen
end LeanCheck
