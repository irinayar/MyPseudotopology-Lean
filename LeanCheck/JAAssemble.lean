import Mathlib
import LeanCheck.JAProductFinal
import LeanCheck.JAClose
import LeanCheck.JASorted
import LeanCheck.JAScalar

/-!
# The central bound: assembly of the per-level estimates (part 1)

For the sorted list of prime-square scales `Q_j = b_j^(n_j^2)`, `j < L`, with `f_i = H_{i-1}(0)/H_i(0)` the factors of the product
identity (`H_i` = convolution of the normalized kernels after level `i` with the triangle function), this module combines

* `separated_factor` (S6a) and `close_factor` (S6b, with the two-term separation as a hypothesis in the form `HTT`),
* the bounds `1 ≤ f_i ≤ 30 D/7` (`fac_bounds`),
* the number of non-deep levels (S6c) and the abstract product bound (S7)

to the uniform bound `prod_f_bound`: `∏_{i<L} f_i ≤ Cp` with `Cp` independent of `L`, `N`, `m`, `X` (for large `X`).
-/

namespace LeanCheck
namespace JAAssemble

open Finset JATransfer JAProduct JAProduct2 JAMulti JAFinal2 JAWindowQ JAFarSep JACenter JASep JAClose JAFar

/-- The list of normalized kernels of the periods `b_j^(n_j^2)`, `j < L`. -/
noncomputable def klist (N : ℕ) [NeZero N] (D : ℝ) (L : ℕ) (b n : ℕ → ℕ)
    [∀ j, NeZero ((b j) ^ ((n j) ^ 2))] : List (ZMod N → ℝ) :=
  (List.range L).map (fun j => normK N ((b j) ^ ((n j) ^ 2)) (wQ D ((b j) ^ ((n j) ^ 2))))

lemma normK_congr {N : ℕ} [NeZero N] (D : ℝ) {Q Q' : ℕ} [NeZero Q] [NeZero Q'] (h : Q = Q') :
    normK N Q (wQ D Q) = normK N Q' (wQ D Q') := by
  subst h; rfl

/-- The conclusion of `hTT_of_two_term`, as a predicate. -/
def HTT (A T₁ : ℝ) : Prop :=
  ∀ (b n b' n' : ℕ), ((b = 2 ∧ b' = 3) ∨ (b = 3 ∧ b' = 2)) → 1 ≤ n → 1 ≤ n' →
      T₁ ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) → b ^ (n ^ 2) < b' ^ (n' ^ 2) →
      ((b' ^ (n' ^ 2) : ℕ) : ℝ) < Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) * ((b ^ (n ^ 2) : ℕ) : ℝ) →
      ∀ r s : ℤ, r ≠ 0 → |r| ≤ (⌈(Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 2⌉₊ : ℤ) →
        |s| ≤ (⌈4 * (Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 3⌉₊ : ℤ) →
        Real.exp (-(A * (Real.log (2 + Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)))) ^ 2)) /
            ((b ^ (n ^ 2) : ℕ) : ℝ) ≤
          MixedPrime.nrm ((r : ℝ) / ((b ^ (n ^ 2) : ℕ) : ℝ) + (s : ℝ) / ((b' ^ (n' ^ 2) : ℕ) : ℝ))

lemma htt_exists (A : ℝ) (hA : 0 ≤ A) (hP : TwoTermSeparation A) : ∃ T₁ : ℝ, HTT A T₁ :=
  hTT_of_two_term A hA hP

/-- Close levels have different primes. -/
lemma bases_differ (L : ℕ) (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3)
    (hmono : ∀ a c, a < c → c < L → JAMerged.lp (b a) (n a) < JAMerged.lp (b c) (n c))
    (p : ℕ) (hp1 : p + 1 < L)
    (hclose : (((b (p + 1)) ^ ((n (p + 1)) ^ 2) : ℕ) : ℝ) <
      Real.sqrt (JAMerged.lp (b p) (n p)) * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)) :
    b p ≠ b (p + 1) := by
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h <;> omega
  intro heq
  have hlt := hmono p (p + 1) (Nat.lt_succ_self p) hp1
  rw [← heq] at hlt
  have hnm : n p < n (p + 1) := JAMerged.lp_strict (hb2 p) hlt
  have hgap := JAMerged.same_chain_gap (hb2 p) hnm
  have e1 := JAFarSep.exp_lp (b p) (n p) (hb2 p)
  have e2 := JAFarSep.exp_lp (b p) (n (p + 1)) (hb2 p)
  rw [← heq] at hclose
  rw [← e1, ← e2] at hclose
  set l0 := JAMerged.lp (b p) (n p)
  set l1 := JAMerged.lp (b p) (n (p + 1))
  have hexp : Real.exp l1 = Real.exp l0 * Real.exp (l1 - l0) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : (l1 - l0) + 1 ≤ Real.exp (l1 - l0) := by linarith [Real.add_one_le_exp (l1 - l0)]
  have hpos : 0 < Real.exp l0 := Real.exp_pos _
  rw [hexp] at hclose
  nlinarith

/-- The factors lie in `[1, 30 D / 7]`. -/
lemma fac_bounds {N : ℕ} [NeZero N] (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (b n : ℕ → ℕ) [inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2))]
    (hQ : ∀ j, j < L → 25 * D ≤ (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ))
    (hQN : ∀ j, j < L → (b j) ^ ((n j) ^ 2) ∣ N) :
    ∀ i, i < L → 1 ≤ Hs (Ftri N m) ((klist N D L b n).drop i) 0 / Hs (Ftri N m) ((klist N D L b n).drop (i + 1)) 0 ∧
      Hs (Ftri N m) ((klist N D L b n).drop i) 0 / Hs (Ftri N m) ((klist N D L b n).drop (i + 1)) 0 ≤ 30 * D / 7 := by
  have hgood : ∀ K ∈ klist N D L b n, PD K ∧ (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 ∧ ∑ x, K x ≤ 30 * D / 7 := by
    intro K hK
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hK
    have hjL : j < L := List.mem_range.mp hj
    obtain ⟨h1, h2, h3⟩ := normK_props (N := N) D hD ((b j) ^ ((n j) ^ 2)) (hQ j hjL) (hQN j hjL)
    exact ⟨h1, normK_nonneg _ _, h2, h3⟩
  have hlen : (klist N D L b n).length = L := by simp [klist]
  have key := factors_bounded (N := N) (Ftri N m) (Ftri_PD m) (by rw [Ftri_zero m hm h2m]) (30 * D / 7)
    (klist N D L b n) hgood
  intro i hi
  exact key i (by rw [hlen]; exact hi)

/-- Separated levels (S6a in the form `f_p ≤ 1 + C_s t^{-3}`), including the final level (a dummy finer scale is adjoined). -/
theorem level_sep {N : ℕ} [NeZero N] (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3)
    [inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2))]
    (hmono : ∀ a c, a < c → c < L → JAMerged.lp (b a) (n a) < JAMerged.lp (b c) (n c))
    (hQ : ∀ j, j < L → 25 * D ≤ (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ))
    (hQN : ∀ j, j < L → (b j) ^ ((n j) ^ 2) ∣ N)
    (p : ℕ) (hp : p < L)
    (ht2 : 2 ≤ Real.sqrt (JAMerged.lp (b p) (n p)))
    (htop : (8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (JAMerged.lp (b p) (n p)))) ≤ 1 / 2)
    (hε : (2 * m : ℝ) / N ≤ 3 / (4 * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)))
    (hsep : p + 1 < L → Real.sqrt (JAMerged.lp (b p) (n p)) * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) ≤
      (((b (p + 1)) ^ ((n (p + 1)) ^ 2) : ℕ) : ℝ)) :
    Hs (Ftri N m) ((klist N D L b n).drop p) 0 / Hs (Ftri N m) ((klist N D L b n).drop (p + 1)) 0 ≤
      1 + (200 * D ^ 4 + 30 * D / 7 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
        (1 + 4 * (8 * (30 * D / 7)) ^ 2))) * (1 / Real.sqrt (JAMerged.lp (b p) (n p))) ^ 3 := by
  classical
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h <;> omega
  set t : ℝ := Real.sqrt (JAMerged.lp (b p) (n p)) with ht
  set M : ℕ := ⌈t * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)⌉₊ + 1 with hM
  obtain ⟨sc, hsc, hscM, hpos⟩ : ∃ sc : ℕ → ℕ, (∀ j, j < L → sc j = (b j) ^ ((n j) ^ 2)) ∧
      (∀ j, L ≤ j → sc j = M) ∧ (∀ j, 0 < sc j) := by
    refine ⟨fun j => if j < L then (b j) ^ ((n j) ^ 2) else M, ?_, ?_, ?_⟩
    · intro j hj; simp [hj]
    · intro j hj; simp [not_lt.mpr hj]
    · intro j
      by_cases hj : j < L
      · simp only [hj, ite_true]
        exact Nat.pos_of_ne_zero (inst j).out
      · simp only [hj, ite_false]; omega
  haveI : ∀ j, NeZero (sc j) := fun j => ⟨(hpos j).ne'⟩
  have hlist : (List.range L).map (fun j => normK N (sc j) (wQ D (sc j))) = klist N D L b n := by
    unfold klist
    apply List.map_congr_left
    intro j hj
    exact normK_congr D (hsc j (List.mem_range.mp hj))
  have hlog : Real.log ((sc p : ℕ) : ℝ) = JAMerged.lp (b p) (n p) := by
    rw [hsc p hp]; exact JAFarSep.log_scale _ _ (hb2 p)
  have hsq : Real.sqrt (Real.log ((sc p : ℕ) : ℝ)) = t := by rw [hlog]
  have hgrow : ∀ p' k, p' + k < L → (sc p' : ℝ) * Real.exp (Real.sqrt (Real.log (sc p')) * ((k / 2 : ℕ) : ℝ)) ≤
      sc (p' + k) := by
    intro p' k h
    have h1 : p' < L := by omega
    rw [hsc p' h1, hsc (p' + k) h]
    exact hgrow_of_merged b n L hb hmono p' k h
  have key := separated_factor (N := N) D hD m hm h2m L sc
    (fun j hj => by rw [hsc j hj]; exact hQ j hj) (fun j hj => by rw [hsc j hj]; exact hQN j hj)
    hgrow p (by omega) (by rw [hsq]; exact htop) (by rw [hsc p hp]; exact hε)
    (by rw [hsq]; exact ht2)
    (by
      rw [hsq]
      by_cases h1 : p + 1 < L
      · rw [hsc p hp, hsc (p + 1) h1]; exact hsep h1
      · have h2 : p + 1 = L := by omega
        rw [hscM (p + 1) (by omega), hsc p hp]
        have := Nat.le_ceil (t * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ))
        rw [hM, Nat.cast_add, Nat.cast_one]; linarith)
  rw [hlist, hsq] at key
  have hS := JAProductFinal.sep_cube D t hD (by linarith)
  linarith

/-- Close levels (S6b in the form of the right-hand side of `close_factor`). -/
theorem level_close {N : ℕ} [NeZero N] (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3) (hn : ∀ i, i < L → 1 ≤ n i)
    [inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2))]
    (hmono : ∀ a c, a < c → c < L → JAMerged.lp (b a) (n a) < JAMerged.lp (b c) (n c))
    (hQ : ∀ j, j < L → 25 * D ≤ (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ))
    (hQN : ∀ j, j < L → (b j) ^ ((n j) ^ 2) ∣ N)
    (A T₁ : ℝ) (htt : HTT A T₁)
    (p : ℕ) (hp1 : p + 1 < L)
    (ht2 : 2 ≤ Real.sqrt (JAMerged.lp (b p) (n p)))
    (hT : T₁ ≤ Real.sqrt (JAMerged.lp (b p) (n p)))
    (htop : (8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (JAMerged.lp (b p) (n p)))) ≤ 1 / 2)
    (hε : (2 * m : ℝ) / N ≤
      3 * (Real.exp (-(A * (Real.log (2 + Real.sqrt (JAMerged.lp (b p) (n p))))^ 2)) /
        (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)) / 4)
    (hclose : (((b (p + 1)) ^ ((n (p + 1)) ^ 2) : ℕ) : ℝ) <
      Real.sqrt (JAMerged.lp (b p) (n p)) * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)) :
    Hs (Ftri N m) ((klist N D L b n).drop p) 0 / Hs (Ftri N m) ((klist N D L b n).drop (p + 1)) 0 ≤
      1 + (200 * D ^ 4 / (Real.sqrt (JAMerged.lp (b p) (n p))) ^ 6 +
          30 * D / 7 * (200 * D ^ 4 / (4 * (Real.sqrt (JAMerged.lp (b p) (n p))) ^ 3) ^ 3) +
          (30 * D / 7) ^ 2 * (2048 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
            (1 / (Real.exp (-(A * (Real.log (2 + Real.sqrt (JAMerged.lp (b p) (n p)))) ^ 2)) /
              (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ))) ^ 3 *
            ((8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (JAMerged.lp (b p) (n p))))))) := by
  classical
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h <;> omega
  have hlog : ∀ j, Real.log (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ) = JAMerged.lp (b j) (n j) :=
    fun j => JAFarSep.log_scale _ _ (hb2 j)
  have hbd := bases_differ L b n hb hmono p hp1 hclose
  have hbases : (b p = 2 ∧ b (p + 1) = 3) ∨ (b p = 3 ∧ b (p + 1) = 2) := by
    rcases hb p with h | h <;> rcases hb (p + 1) with h' | h' <;>
      first | (exfalso; exact hbd (h.trans h'.symm)) | (left; exact ⟨h, h'⟩) | (right; exact ⟨h, h'⟩)
  have hQQ : (b p) ^ ((n p) ^ 2) < (b (p + 1)) ^ ((n (p + 1)) ^ 2) := by
    have hlt := hmono p (p + 1) (Nat.lt_succ_self p) hp1
    rw [← hlog p, ← hlog (p + 1)] at hlt
    have hp0 : (0 : ℝ) < (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) := by
      have : 0 < (b p) ^ ((n p) ^ 2) := Nat.pos_of_ne_zero (inst p).out
      exact_mod_cast this
    have := (Real.log_lt_log_iff hp0 (by
      have : 0 < (b (p + 1)) ^ ((n (p + 1)) ^ 2) := Nat.pos_of_ne_zero (inst (p + 1)).out
      exact_mod_cast this)).mp hlt
    exact_mod_cast this
  have hTT : ∀ r s : ℤ, r ≠ 0 →
      |r| ≤ (⌈(Real.sqrt (Real.log (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ))) ^ 2⌉₊ : ℤ) →
      |s| ≤ (⌈4 * (Real.sqrt (Real.log (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ))) ^ 3⌉₊ : ℤ) →
      Real.exp (-(A * (Real.log (2 + Real.sqrt (Real.log (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)))) ^ 2)) /
          (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) ≤
        MixedPrime.nrm ((r : ℝ) / (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) +
          (s : ℝ) / (((b (p + 1)) ^ ((n (p + 1)) ^ 2) : ℕ) : ℝ)) := by
    exact htt (b p) (n p) (b (p + 1)) (n (p + 1)) hbases (hn p (by omega)) (hn (p + 1) hp1) (by rw [hlog p]; exact hT) hQQ
      (by rw [hlog p]; exact hclose)
  have key := close_factor (N := N) D hD m hm h2m L (fun j => (b j) ^ ((n j) ^ 2)) hQ hQN
    (hgrow_of_merged b n L hb hmono) p (by omega) (by rw [hlog p]; exact htop)
    (by rw [hlog p]; exact ht2) A (by rw [hlog p]; exact hε) hTT
  unfold klist
  rw [hlog p] at key
  linarith

#print axioms bases_differ
#print axioms fac_bounds
#print axioms level_sep
#print axioms level_close

end JAAssemble
end LeanCheck
