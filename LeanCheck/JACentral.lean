import Mathlib
import LeanCheck.JAAssemble
import LeanCheck.JAHeights

/-!
# The central bound: assembly of `CentralBound` from the two-term separation

`prod_f_bound`: for large `X`, the product of the factors `f_i` of the sorted list of prime-square scales is at most a constant
`Cp(D, A)`, independent of the number of levels, of `N`, and of `m` (assuming `2m/N ≤ 3/X`).  Hypothesis: `TwoTermSeparation A`.

`central_bound`: for `D ≥ 3`, `A ≥ 0` and `TwoTermSeparation A`, there is `C > 0` with `CentralBound D C`.
-/

namespace LeanCheck
namespace JACentral

open Finset JATransfer JAProduct JAProduct2 JAMulti JAFinal2 JAWindowQ JACenter JAAssemble

lemma htop_of_large (B t : ℝ) (ht : (8 * B) ^ 2 ≤ t) :
    (8 * B) ^ 2 * Real.exp (-(3 * t)) ≤ 1 / 2 := by
  have hc : 0 ≤ (8 * B) ^ 2 := sq_nonneg _
  have ht0 : 0 ≤ t := le_trans hc ht
  have h1 := Real.add_one_le_exp (3 * t)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-- **The product of the factors is bounded** (S7 applied to the actual list). -/
theorem prod_f_bound (D : ℝ) (a : ℝ → ℝ) (hD : 3 ≤ D) (ha : WindowProfile a) (hG : CloseGrowth a)
    (hP : JAClose.TwoTermSep a) :
    ∃ Cp X₀ : ℝ, 0 < Cp ∧ ∀ (X N m L : ℕ) [NeZero N] (b n : ℕ → ℕ)
      [inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2))],
      X₀ ≤ (X : ℝ) → (∀ i, b i = 2 ∨ b i = 3) → (∀ i, i < L → 1 ≤ n i) →
      (∀ a c, a < c → c < L → JAMerged.lp (b a) (n a) < JAMerged.lp (b c) (n c)) →
      1 ≤ m → 2 * m ≤ N →
      (∀ j, j < L → 25 * D ≤ (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ)) →
      (∀ j, j < L → (b j) ^ ((n j) ^ 2) ∣ N) →
      (∀ j, j < L → (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ) ≤ D * X) →
      (2 * m : ℝ) / N ≤ 3 / X →
      ∏ i ∈ range L, (Hs (Ftri N m) ((klist N D L b n).drop i) 0 /
        Hs (Ftri N m) ((klist N D L b n).drop (i + 1)) 0) ≤ Cp := by
  classical
  obtain ⟨T₁, htt⟩ := htt_exists a ha.nonneg hP
  obtain ⟨Tc, hTc1, hcc⟩ := JAProductFinal.close_cube_G D a hD hG
  obtain ⟨X₀', hX₀'⟩ := JANonDeep.non_deep_card_le_two D a (by linarith) ha
  have hD0 : 0 < D := by linarith
  have hB1 : 1 ≤ 30 * D / 7 := by linarith
  obtain ⟨Cs, hCs⟩ : ∃ Cs : ℝ, Cs = 200 * D ^ 4 + 30 * D / 7 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
        (1 + 4 * (8 * (30 * D / 7)) ^ 2)) := ⟨_, rfl⟩
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = 200 * D ^ 4 + 30 * D / 7 * (200 * D ^ 4) +
        (30 * D / 7) ^ 2 * (2048 * (200 * D ^ 4 + 8 * (30 * D / 7)) * (8 * (30 * D / 7)) ^ 2) := ⟨_, rfl⟩
  have hCs0 : 0 ≤ Cs := by rw [hCs]; positivity
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  obtain ⟨Tbig, hTbig⟩ : ∃ T : ℝ, T = max (max 2 ((8 * (30 * D / 7)) ^ 2)) (max T₁ Tc) := ⟨_, rfl⟩
  have hTb2 : 2 ≤ Tbig := by
    rw [hTbig]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hTbB : (8 * (30 * D / 7)) ^ 2 ≤ Tbig := by
    rw [hTbig]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hTbT : T₁ ≤ Tbig := by
    rw [hTbig]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hTbc : Tc ≤ Tbig := by
    rw [hTbig]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨(30 * D / 7) ^ (2 + 2 * ⌊2 * Tbig⌋₊) * Real.exp ((Cs + Cc) *
      (2 * (1 / (Real.sqrt (Real.log 2)) ^ 3 + 1 / (Real.sqrt (Real.log 3)) ^ 3))),
    max X₀' 1, by positivity, ?_⟩
  intro X N m L _ b n inst hX hb hn hmono hm h2m hQ hQN hQX hmN
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hXN : X₀' ≤ (X : ℝ) := le_trans (le_max_left _ _) hX
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h <;> omega
  have hlog : ∀ j, Real.log (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ) = JAMerged.lp (b j) (n j) :=
    fun j => JAFarSep.log_scale _ _ (hb2 j)
  have hQpos : ∀ j, (0 : ℝ) < (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ) := fun j => by
    have : 0 < (b j) ^ ((n j) ^ 2) := Nat.pos_of_ne_zero (inst j).out
    exact_mod_cast this
  set E : Finset ℕ := (range L).filter (fun i => ¬ (4 * (((b i) ^ ((n i) ^ 2) : ℕ) : ℝ) *
      Real.exp (a (Real.sqrt (Real.log (((b i) ^ ((n i) ^ 2) : ℕ) : ℝ)))) ≤ X)) with hE
  have hEcard : E.card ≤ 2 := by
    have hinj := JAProductFinal.period_inj L b n hmono
    have h1 : (E.image (fun i => (b i, n i))).card = E.card :=
      Finset.card_image_of_injOn (hinj.mono (fun i hi => Finset.mem_coe.mpr (Finset.mem_filter.mp hi).1))
    rw [← h1]
    apply hX₀' X hXN
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hiL, hiE⟩ := Finset.mem_filter.mp hi
    have hiL' := Finset.mem_range.mp hiL
    exact ⟨hb i, hn i hiL', hQX i hiL', not_le.mp hiE⟩
  have hfB := fac_bounds D hD m hm h2m L b n hQ hQN
  have hgood : ∀ i, i < L → i ∉ E → Tbig ≤ Real.sqrt (JAMerged.lp (b i) (n i)) →
      Hs (Ftri N m) ((klist N D L b n).drop i) 0 / Hs (Ftri N m) ((klist N D L b n).drop (i + 1)) 0 ≤
        1 + (Cs + Cc) * (1 / Real.sqrt (JAMerged.lp (b i) (n i))) ^ 3 := by
    intro p hp hpE hT
    have hdeep : 4 * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) *
        Real.exp (a (Real.sqrt (Real.log (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)))) ≤ X := by
      by_contra h
      exact hpE (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, h⟩)
    rw [hlog p] at hdeep
    have hQp := hQpos p
    have ht2 : 2 ≤ Real.sqrt (JAMerged.lp (b p) (n p)) := le_trans hTb2 hT
    have htB : (8 * (30 * D / 7)) ^ 2 ≤ Real.sqrt (JAMerged.lp (b p) (n p)) := le_trans hTbB hT
    have htT : T₁ ≤ Real.sqrt (JAMerged.lp (b p) (n p)) := le_trans hTbT hT
    have htc : Tc ≤ Real.sqrt (JAMerged.lp (b p) (n p)) := le_trans hTbc hT
    have htop := htop_of_large (30 * D / 7) _ htB
    have hs0 : 0 ≤ (1 / Real.sqrt (JAMerged.lp (b p) (n p))) ^ 3 := by positivity
    have hexp1 : 1 ≤ Real.exp (a (Real.sqrt (JAMerged.lp (b p) (n p)))) :=
      Real.one_le_exp (ha.nonneg _ (Real.sqrt_nonneg _))
    have h4Q : 4 * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) ≤ X := by nlinarith
    have hrad := JANonDeep.deep_radius X (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)
      (a (Real.sqrt (JAMerged.lp (b p) (n p)))) hX0 hQp hdeep
    have h3X : 3 / (X : ℝ) = 3 * (2 * (2 / X)) / 4 := by ring
    by_cases hcl : p + 1 < L ∧ (((b (p + 1)) ^ ((n (p + 1)) ^ 2) : ℕ) : ℝ) <
        Real.sqrt (JAMerged.lp (b p) (n p)) * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)
    · have h1 := level_close D hD m hm h2m L b n hb hn hmono hQ hQN a T₁ htt p hcl.1 ht2 htT htop
        (by
          calc (2 * m : ℝ) / N ≤ 3 / X := hmN
            _ = 3 * (2 * (2 / X)) / 4 := h3X
            _ ≤ _ := by linarith) hcl.2
      have h2 := hcc (Real.sqrt (JAMerged.lp (b p) (n p))) (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) htc hQp
      rw [← hCc] at h2
      have h5 : Cc * (1 / Real.sqrt (JAMerged.lp (b p) (n p))) ^ 3 ≤
          (Cs + Cc) * (1 / Real.sqrt (JAMerged.lp (b p) (n p))) ^ 3 := by
        rw [add_mul]; linarith [mul_nonneg hCs0 hs0]
      linarith
    · have h1 := level_sep D hD m hm h2m L b n hb hmono hQ hQN p hp ht2 htop
        (by
          calc (2 * m : ℝ) / N ≤ 3 / X := hmN
            _ ≤ 3 / (4 * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)) :=
                div_le_div_of_nonneg_left (by norm_num) (by positivity) h4Q)
        (fun h => by
          by_contra hh
          push Not at hh
          exact hcl ⟨h, hh⟩)
      rw [← hCs] at h1
      have h5 : Cs * (1 / Real.sqrt (JAMerged.lp (b p) (n p))) ^ 3 ≤
          (Cs + Cc) * (1 / Real.sqrt (JAMerged.lp (b p) (n p))) ^ 3 := by
        rw [add_mul]; linarith [mul_nonneg hCc0 hs0]
      linarith
  exact JAProductFinal.product_final L b n hb hn hmono
    (fun i => Hs (Ftri N m) ((klist N D L b n).drop i) 0 /
      Hs (Ftri N m) ((klist N D L b n).drop (i + 1)) 0)
    (30 * D / 7) (Cs + Cc) Tbig hB1 (by linarith) (fun i hi => hfB i hi) E 2 hEcard hgood

#print axioms prod_f_bound

end JACentral
end LeanCheck
