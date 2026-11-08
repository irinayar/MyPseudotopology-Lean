import Mathlib
import LeanCheck.DD3Central
import LeanCheck.DD3Multi
import LeanCheck.DD3Dense
import LeanCheck.JAMain

/-!
# Diagonal density for three primes: from the central bound to `DD {2,3,5}` (Lean check)

Scope. Second half of phase 5f of the Lean version of the conditional proof of `DD({2,3,5})` (research note
`TVGplus_conditional_DD235_2026-11-07.md`). It is the three-prime counterpart of `JAMulti2.dense_step_multi`,
`JAFinal2.denseDifferences_of_heightBounds2`, `JAHeights.heightBound2_of_central` and `JAMain.JA_of_profile`.

* `final_ineq3`: the scalar inequality turning `B ≤ C Y²` and the mass bounds into the energy bound `≤ 700 C P²/(2X+1)²`;
* `energy_step3`: at one buffered height with `CentralAt3`, the shifts of `DD3Multi.multi_realization3` give sets
  `A, B, C ⊆ [0, X]` (supports of the three realized weights, self-differences small in `P₂, P₃, P₅`) and weights with the
  three-fold collision energy at most `700 C M² / (2X+1)²` (`DD3Energy.collision_support`, `collision_Aset_eq_energyE3`);
* `energyInput3_of_central`: `CentralBound3 D C` with `2/D ≤ ε` gives `DD3Dense.EnergyInput3 ε` (buffered heights
  `DD3Heights.exists_buffered3`);
* `DD235_of_central3`: `CompactQuotientCriterion3` and `CentralBound3` at every precision give `TVGPlus.DD {2,3,5}`;
* `DD235_of_profile`, `DD235_of_inputs`: the same from `HTT3` and `HFin` (via `DD3Central.central_bound3`), for a window
  profile `a`, resp. the profile `A log²(2+t)`.

Remaining hypotheses (not proved here): `CompactQuotientCriterion3`, `HTT3` (the two-term separations for the three pairs) and
`HFin` (finitely many bad triples, `H(2,3,5)`). A Lean proof verifies its formal statement under its hypotheses; the
correspondence with the research note requires mathematical review.
-/

namespace LeanCheck
namespace DD3Final

open Finset MixedPrime JATransfer JARandom JAEnergyLink JAEnergyIdentity JAAssembly JAWindowQ JABlocks JALocalize
  JASupport JADense JAFinal JAMulti JAMulti2 JAFinal2 DD3Energy DD3Multi DD3Heights DD3Central JAHeights

/-! ### The scalar inequality -/

set_option maxHeartbeats 800000 in
lemma final_ineq3 (X Qa Qb Qc ma mb mc B C : ℝ) (hX : 1 ≤ X) (hQa : 0 < Qa) (hQb : 0 < Qb) (hQc : 0 < Qc)
    (h4a : 4 * Qa ≤ X) (h4b : 4 * Qb ≤ X) (h4c : 4 * Qc ≤ X) (hma : 0 < ma) (hmb : 0 < mb) (hmc : 0 < mc)
    (hB : 0 ≤ B) (hC : 0 < C) (hBY : B ≤ C * (ma * mb * mc) ^ 2) :
    3 * (X + 1 + Qa + Qb + Qc) ^ 4 * B / (Qa * Qb * Qc) ^ 2 ≤
      700 * C * ((((X + 1 - Qa) / Qa * ma) * ((X + 1 - Qb) / Qb * mb) * ((X + 1 - Qc) / Qc * mc))) ^ 2 /
        (2 * X + 1) ^ 2 := by
  set t : ℝ := X + 1 with ht
  have ht2 : 2 ≤ t := by rw [ht]; linarith
  have ht0 : 0 < t := by linarith
  set L : ℝ := X + 1 + Qa + Qb + Qc with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  have hLle : L ≤ 7 / 4 * t := by rw [hL, ht]; linarith
  have hL4 : L ^ 4 ≤ (7 / 4 * t) ^ 4 := pow_le_pow_left₀ hL0.le hLle 4
  have h2X : 2 * X + 1 ≤ 2 * t := by rw [ht]; linarith
  have hsq : (2 * X + 1) ^ 2 ≤ (2 * t) ^ 2 := pow_le_pow_left₀ (by linarith) h2X 2
  have fa : 3 / 4 * t ≤ X + 1 - Qa := by rw [ht]; linarith
  have fb : 3 / 4 * t ≤ X + 1 - Qb := by rw [ht]; linarith
  have fc : 3 / 4 * t ≤ X + 1 - Qc := by rw [ht]; linarith
  set u : ℝ := (X + 1 - Qa) * (X + 1 - Qb) * (X + 1 - Qc) with hu
  have hu1 : 27 / 64 * t ^ 3 ≤ u := by
    have h1 : (3 / 4 * t) * (3 / 4 * t) ≤ (X + 1 - Qa) * (X + 1 - Qb) :=
      mul_le_mul fa fb (by positivity) (by linarith)
    have h2 : (3 / 4 * t) * (3 / 4 * t) * (3 / 4 * t) ≤ (X + 1 - Qa) * (X + 1 - Qb) * (X + 1 - Qc) :=
      mul_le_mul h1 fc (by positivity) (mul_nonneg (by linarith) (by linarith))
    calc 27 / 64 * t ^ 3 = (3 / 4 * t) * (3 / 4 * t) * (3 / 4 * t) := by ring
      _ ≤ u := h2
  have hu2 : (27 / 64 * t ^ 3) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hu1 2
  have key : 3 * L ^ 4 * (2 * X + 1) ^ 2 ≤ 700 * u ^ 2 := by
    have s1 : 3 * L ^ 4 * (2 * X + 1) ^ 2 ≤ 3 * (7 / 4 * t) ^ 4 * (2 * t) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL4 (by norm_num)) hsq (by positivity) (by positivity)
    have e1 : 3 * (7 / 4 * t) ^ 4 * (2 * t) ^ 2 = (28812 / 256) * t ^ 6 := by ring
    have e2 : 700 * (27 / 64 * t ^ 3) ^ 2 = (510300 / 4096) * t ^ 6 := by ring
    have s2 : (28812 / 256) * t ^ 6 ≤ (510300 / 4096) * t ^ 6 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have s3 : 700 * (27 / 64 * t ^ 3) ^ 2 ≤ 700 * u ^ 2 := by linarith [hu2]
    linarith [s1, s2, e1, e2, s3]
  have hq : 0 < Qa * Qb * Qc := by positivity
  have hY : 0 ≤ (ma * mb * mc) ^ 2 := by positivity
  have hP : ((X + 1 - Qa) / Qa * ma) * ((X + 1 - Qb) / Qb * mb) * ((X + 1 - Qc) / Qc * mc) =
      u * (ma * mb * mc) / (Qa * Qb * Qc) := by
    rw [hu]; field_simp
  rw [hP]
  have h2X0 : 0 < (2 * X + 1) := by linarith
  have eR : 700 * C * (u * (ma * mb * mc) / (Qa * Qb * Qc)) ^ 2 / (2 * X + 1) ^ 2 =
      (700 * C * (u * (ma * mb * mc)) ^ 2) / ((Qa * Qb * Qc) ^ 2 * (2 * X + 1) ^ 2) := by
    field_simp
  rw [eR, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (3 * L ^ 4 * (2 * X + 1) ^ 2) * B ≤ (700 * u ^ 2) * (C * (ma * mb * mc) ^ 2) :=
    mul_le_mul key hBY hB (by positivity)
  have h3 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Qa * Qb * Qc))
  linarith [h3]

/-! ### The supports have small differences -/

lemma hdiff_chainP (p : ℕ) [NeZero p] (hp : 2 ≤ p) (s n X : ℕ) (D ε : ℝ) (hD0 : 0 < D) (hDε : 2 / D ≤ ε)
    (hL : D * X < (p : ℝ) ^ ((s + n + 1) ^ 2)) (τ : ∀ k, ZMod ((chainP p s D).q k)) :
    ∀ a ∈ suppSet ((chainP p s D).weights τ (deltaSeed (p ^ ((s + 0) ^ 2))) n) X,
      ∀ a' ∈ suppSet ((chainP p s D).weights τ (deltaSeed (p ^ ((s + 0) ^ 2))) n) X,
        Pn (sqScales p) (a - a') < ε := by
  intro a ha a' ha'
  obtain ⟨hX, hg⟩ := mem_suppSet _ X ha
  obtain ⟨hX', hg'⟩ := mem_suppSet _ X ha'
  obtain ⟨hdv, hlev⟩ := support_chain (chainP p s D) D hD0 (chainP_w p s D) τ _
    (deltaSeed_support _) n a a' hg hg'
  exact lt_of_lt_of_le (Pn_of_chainP hp s n X D hD0 hL a a' hX hX' hdv hlev) hDε

/-! ### One height -/

set_option maxHeartbeats 1600000 in
/-- **One buffered height gives the energy data of `EnergyInput3`.** -/
theorem energy_step3 (D C ε : ℝ) (hD : 3 ≤ D) (hC : 0 < C) (hDε : 2 / D ≤ ε) (X na nb nc : ℕ)
    (hbuf : Buffered3 D X na nb nc) (hcen : CentralAt3 D C X (sD D) na (sD D) nb (sD D) nc) :
    ∃ (A B C' : Finset ℤ) (f g h : ℤ → ℝ),
      (∀ a ∈ A, 0 ≤ a ∧ a ≤ X) ∧ (∀ a ∈ B, 0 ≤ a ∧ a ≤ X) ∧ (∀ a ∈ C', 0 ≤ a ∧ a ≤ X) ∧
      (∀ a ∈ A, ∀ a' ∈ A, Pn (sqScales 2) (a - a') < ε) ∧
      (∀ a ∈ B, ∀ a' ∈ B, Pn (sqScales 3) (a - a') < ε) ∧
      (∀ a ∈ C', ∀ a' ∈ C', Pn (sqScales 5) (a - a') < ε) ∧
      (∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C', h c) ≠ 0 ∧
      ∑ p ∈ A ×ˢ (B ×ˢ C'), ∑ q ∈ A ×ˢ (B ×ˢ C'),
          (if DD3.phi p = DD3.phi q then DD3.wt f g h p * DD3.wt f g h q else 0) ≤
        700 * C * ((∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C', h c)) ^ 2 / (2 * (X : ℝ) + 1) ^ 2 := by
  classical
  have hD0 : 0 < D := by linarith
  obtain ⟨hL₂, hL₃, hL₅, h4a, h4b, h4c⟩ := hbuf
  obtain ⟨m, hm1, hmN, hLm, hcen⟩ := hcen
  set sa : ℕ := sD D with hsa
  have hsa3 : 3 ≤ sa := by
    have : (3 : ℝ) ≤ (sa : ℝ) := le_trans hD (Nat.le_ceil D)
    exact_mod_cast this
  set N : ℕ := NN sa na sa nb sa nc with hN
  have hNe : N = 2 ^ ((sa + na) ^ 2) * 3 ^ ((sa + nb) ^ 2) * 5 ^ ((sa + nc) ^ 2) := rfl
  have hdA : (chainP 2 sa D).q na ∣ N := by
    rw [hNe]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _
  have hdB : (chainP 3 sa D).q nb ∣ N := by
    rw [hNe]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _
  have hdC : (chainP 5 sa D).q nc ∣ N := by
    rw [hNe]; exact Dvd.dvd.mul_left dvd_rfl _
  have hNa : ∀ k, k ≤ na → (chainP 2 sa D).q k ∣ N := fun k hk =>
    (chain_dvd_of_le (chainP 2 sa D) k na hk).trans hdA
  have hNb : ∀ k, k ≤ nb → (chainP 3 sa D).q k ∣ N := fun k hk =>
    (chain_dvd_of_le (chainP 3 sa D) k nb hk).trans hdB
  have hNc : ∀ k, k ≤ nc → (chainP 5 sa D).q k ∣ N := fun k hk =>
    (chain_dvd_of_le (chainP 5 sa D) k nc hk).trans hdC
  -- the seeds
  have hsum2 : ∑ y, deltaSeed ((chainP 2 sa D).q 0) y = 1 := sum_deltaSeed _
  have hsum3 : ∑ y, deltaSeed ((chainP 3 sa D).q 0) y = 1 := sum_deltaSeed _
  have hsum5 : ∑ y, deltaSeed ((chainP 5 sa D).q 0) y = 1 := sum_deltaSeed _
  -- positivity of the central mass
  have hMa := Mavg_nonneg_pos0 (N := N) D na (chainP 2 sa D) (chainP_w 2 sa D)
    (kernq N ((chainP 2 sa D).q 0) (deltaSeed ((chainP 2 sa D).q 0))) (fun x => kern_nonneg' _ _ _ x)
    (lt_of_lt_of_le (by rw [hsum2]; norm_num)
      (kern_zero_ge (N := N) ((chainP 2 sa D).q 0) (N / (chainP 2 sa D).q 0)
        (deltaSeed ((chainP 2 sa D).q 0))))
  have hMb := Mavg_nonneg_pos0 (N := N) D nb (chainP 3 sa D) (chainP_w 3 sa D)
    (kernq N ((chainP 3 sa D).q 0) (deltaSeed ((chainP 3 sa D).q 0))) (fun x => kern_nonneg' _ _ _ x)
    (lt_of_lt_of_le (by rw [hsum3]; norm_num)
      (kern_zero_ge (N := N) ((chainP 3 sa D).q 0) (N / (chainP 3 sa D).q 0)
        (deltaSeed ((chainP 3 sa D).q 0))))
  have hMc := Mavg_nonneg_pos0 (N := N) D nc (chainP 5 sa D) (chainP_w 5 sa D)
    (kernq N ((chainP 5 sa D).q 0) (deltaSeed ((chainP 5 sa D).q 0))) (fun x => kern_nonneg' _ _ _ x)
    (lt_of_lt_of_le (by rw [hsum5]; norm_num)
      (kern_zero_ge (N := N) ((chainP 5 sa D).q 0) (N / (chainP 5 sa D).q 0)
        (deltaSeed ((chainP 5 sa D).q 0))))
  set Ma := Mavg N na (chainP 2 sa D) (kernq N ((chainP 2 sa D).q 0) (deltaSeed ((chainP 2 sa D).q 0))) with hMa_def
  set Mb := Mavg N nb (chainP 3 sa D) (kernq N ((chainP 3 sa D).q 0) (deltaSeed ((chainP 3 sa D).q 0))) with hMb_def
  set Mc := Mavg N nc (chainP 5 sa D) (kernq N ((chainP 5 sa D).q 0) (deltaSeed ((chainP 5 sa D).q 0))) with hMc_def
  have hBpos : 0 < ∑ t ∈ arc N (m - 1), conv Ma (conv Mb Mc) t := by
    have h0arc : (0 : ZMod N) ∈ arc N (m - 1) := by
      unfold arc
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), by simp⟩)
    have hbcnn : ∀ x, 0 ≤ conv Mb Mc x := fun x => conv_nonneg' _ _ hMb.1 hMc.1 x
    have hsingle := Finset.single_le_sum (f := fun t => conv Ma (conv Mb Mc) t)
      (fun t _ => conv_nonneg' _ _ hMa.1 hbcnn t) h0arc
    have hbc0 : 0 < conv Mb Mc 0 :=
      lt_of_lt_of_le (mul_pos hMb.2 hMc.2) (conv_zero_ge _ _ hMb.1 hMc.1)
    exact lt_of_lt_of_le (lt_of_lt_of_le (mul_pos hMa.2 hbc0) (conv_zero_ge _ _ hMa.1 hbcnn)) hsingle
  obtain ⟨τa, τb, τc, hE⟩ := multi_realization3 (N := N) na nb nc (chainP 2 sa D) (chainP 3 sa D) (chainP 5 sa D)
    hNa hNb hNc (chainP_w0 2 sa D) (chainP_w0 3 sa D) (chainP_w0 5 sa D)
    (deltaSeed ((chainP 2 sa D).q 0)) (deltaSeed ((chainP 3 sa D).q 0)) (deltaSeed ((chainP 5 sa D).q 0))
    (deltaSeed_nonneg _) (deltaSeed_nonneg _) (deltaSeed_nonneg _) X m hm1 hmN hLm
  set fa := (chainP 2 sa D).weights τa (deltaSeed ((chainP 2 sa D).q 0)) na with hfa
  set fb := (chainP 3 sa D).weights τb (deltaSeed ((chainP 3 sa D).q 0)) nb with hfb
  set fc := (chainP 5 sa D).weights τc (deltaSeed ((chainP 5 sa D).q 0)) nc with hfc
  have hQa : (0 : ℝ) < (chainP 2 sa D).q na := by exact_mod_cast (chainP 2 sa D).pos na
  have hQb : (0 : ℝ) < (chainP 3 sa D).q nb := by exact_mod_cast (chainP 3 sa D).pos nb
  have hQc : (0 : ℝ) < (chainP 5 sa D).q nc := by exact_mod_cast (chainP 5 sa D).pos nc
  have hQa4 : (4 : ℝ) * (chainP 2 sa D).q na ≤ X := by exact_mod_cast h4a
  have hQb4 : (4 : ℝ) * (chainP 3 sa D).q nb ≤ X := by exact_mod_cast h4b
  have hQc4 : (4 : ℝ) * (chainP 5 sa D).q nc ≤ X := by exact_mod_cast h4c
  have hX1 : (1 : ℝ) ≤ X := by
    have : 4 * 2 ^ ((sa + na) ^ 2) ≤ X := h4a
    have h1 : 1 ≤ 2 ^ ((sa + na) ^ 2) := Nat.one_le_pow _ _ (by norm_num)
    have : 1 ≤ X := by omega
    exact_mod_cast this
  have hq2 : (chainP 2 sa D).q na ≤ X + 1 :=
    le_trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) h4a) (Nat.le_succ X)
  have hq3 : (chainP 3 sa D).q nb ≤ X + 1 :=
    le_trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) h4b) (Nat.le_succ X)
  have hq5 : (chainP 5 sa D).q nc ≤ X + 1 :=
    le_trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) h4c) (Nat.le_succ X)
  have hIa : ∀ k, k < na → 2 < (((2 ^ (2 * (sa + k) + 1) : ℕ) : ℝ) * (16 / (15 * D))) :=
    fun k _ => alpha_large 2 le_rfl D hD k
  have hIb : ∀ k, k < nb → 2 < (((3 ^ (2 * (sa + k) + 1) : ℕ) : ℝ) * (16 / (15 * D))) :=
    fun k _ => alpha_large 3 (by norm_num) D hD k
  have hIc : ∀ k, k < nc → 2 < (((5 ^ (2 * (sa + k) + 1) : ℕ) : ℝ) * (16 / (15 * D))) :=
    fun k _ => alpha_large 5 (by norm_num) D hD k
  have hTa := total_lower_chain (chainP 2 sa D) D hD (chainP_w 2 sa D) (chainP_w0 2 sa D)
    (fun k => 2 ^ (2 * (sa + k) + 1)) (chainP_α 2 sa D) τa (deltaSeed ((chainP 2 sa D).q 0))
    (deltaSeed_nonneg _) na hIa X hq2
  have hTb := total_lower_chain (chainP 3 sa D) D hD (chainP_w 3 sa D) (chainP_w0 3 sa D)
    (fun k => 3 ^ (2 * (sa + k) + 1)) (chainP_α 3 sa D) τb (deltaSeed ((chainP 3 sa D).q 0))
    (deltaSeed_nonneg _) nb hIb X hq3
  have hTc := total_lower_chain (chainP 5 sa D) D hD (chainP_w 5 sa D) (chainP_w0 5 sa D)
    (fun k => 5 ^ (2 * (sa + k) + 1)) (chainP_α 5 sa D) τc (deltaSeed ((chainP 5 sa D).q 0))
    (deltaSeed_nonneg _) nc hIc X hq5
  rw [hsum2, mul_one] at hTa
  rw [hsum3, mul_one] at hTb
  rw [hsum5, mul_one] at hTc
  set ma := ∏ k ∈ range na, (((2 ^ (2 * (sa + k) + 1) : ℕ) : ℝ) * (16 / (15 * D)) - 2) with hma
  set mb := ∏ k ∈ range nb, (((3 ^ (2 * (sa + k) + 1) : ℕ) : ℝ) * (16 / (15 * D)) - 2) with hmb
  set mc := ∏ k ∈ range nc, (((5 ^ (2 * (sa + k) + 1) : ℕ) : ℝ) * (16 / (15 * D)) - 2) with hmc
  have hpa : 0 < ma := Finset.prod_pos (fun k hk => by linarith [hIa k (Finset.mem_range.mp hk)])
  have hpb : 0 < mb := Finset.prod_pos (fun k hk => by linarith [hIb k (Finset.mem_range.mp hk)])
  have hpc : 0 < mc := Finset.prod_pos (fun k hk => by linarith [hIc k (Finset.mem_range.mp hk)])
  have hXa : (0 : ℝ) < (X : ℝ) + 1 - (chainP 2 sa D).q na := by linarith
  have hXb : (0 : ℝ) < (X : ℝ) + 1 - (chainP 3 sa D).q nb := by linarith
  have hXc : (0 : ℝ) < (X : ℝ) + 1 - (chainP 5 sa D).q nc := by linarith
  have hca : 0 < ((X : ℝ) + 1 - (chainP 2 sa D).q na) / (chainP 2 sa D).q na * ma := by positivity
  have hcb : 0 < ((X : ℝ) + 1 - (chainP 3 sa D).q nb) / (chainP 3 sa D).q nb * mb := by positivity
  have hcc : 0 < ((X : ℝ) + 1 - (chainP 5 sa D).q nc) / (chainP 5 sa D).q nc * mc := by positivity
  have hMT := mul_le_mul (mul_le_mul hTa hTb hcb.le (le_trans hca.le hTa)) hTc hcc.le
    (mul_nonneg (le_trans hca.le hTa) (le_trans hcb.le hTb))
  set Pm : ℝ := (((X : ℝ) + 1 - (chainP 2 sa D).q na) / (chainP 2 sa D).q na * ma) *
    (((X : ℝ) + 1 - (chainP 3 sa D).q nb) / (chainP 3 sa D).q nb * mb) *
    (((X : ℝ) + 1 - (chainP 5 sa D).q nc) / (chainP 5 sa D).q nc * mc) with hPm
  have hPm0 : 0 < Pm := by rw [hPm]; positivity
  set B := ∑ t ∈ arc N (m - 1), conv Ma (conv Mb Mc) t with hB
  have hBY : B ≤ C * (ma * mb * mc) ^ 2 := hcen
  have hB0 : 0 ≤ B := hBpos.le
  have hR := final_ineq3 (X : ℝ) ((chainP 2 sa D).q na) ((chainP 3 sa D).q nb) ((chainP 5 sa D).q nc) ma mb mc B C
    hX1 hQa hQb hQc hQa4 hQb4 hQc4 hpa hpb hpc hB0 hC hBY
  -- the sets and weights
  have hsuppA := suppSet_subset fa X
  have hsuppB := suppSet_subset fb X
  have hsuppC := suppSet_subset fc X
  refine ⟨suppSet fa X, suppSet fb X, suppSet fc X, Fw fa, Fw fb, Fw fc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; exact (mem_suppSet fa X ha).1
  · intro a ha; exact (mem_suppSet fb X ha).1
  · intro a ha; exact (mem_suppSet fc X ha).1
  · exact hdiff_chainP 2 le_rfl sa na X D ε hD0 hDε hL₂ τa
  · exact hdiff_chainP 3 (by norm_num) sa nb X D ε hD0 hDε hL₃ τb
  · exact hdiff_chainP 5 (by norm_num) sa nc X D ε hD0 hDε hL₅ τc
  all_goals
    have hTa' : ∑ a ∈ suppSet fa X, Fw fa a = ∑ x ∈ range (X + 1), fn fa x := by
      rw [JAEnergyFinal.sum_support (Aset X) (suppSet fa X) _ hsuppA (suppSet_vanish fa X), sum_Aset]
      simp [Fw]
    have hTb' : ∑ a ∈ suppSet fb X, Fw fb a = ∑ x ∈ range (X + 1), fn fb x := by
      rw [JAEnergyFinal.sum_support (Aset X) (suppSet fb X) _ hsuppB (suppSet_vanish fb X), sum_Aset]
      simp [Fw]
    have hTc' : ∑ a ∈ suppSet fc X, Fw fc a = ∑ x ∈ range (X + 1), fn fc x := by
      rw [JAEnergyFinal.sum_support (Aset X) (suppSet fc X) _ hsuppC (suppSet_vanish fc X), sum_Aset]
      simp [Fw]
    have hMpos : 0 < (∑ x ∈ range (X + 1), fn fa x) * (∑ x ∈ range (X + 1), fn fb x) *
        (∑ x ∈ range (X + 1), fn fc x) := lt_of_lt_of_le hPm0 hMT
  · rw [hTa', hTb', hTc']
    exact hMpos.ne'
  · rw [hTa', hTb', hTc']
    have hcoll := collision_support (Aset X) (suppSet fa X) (Aset X) (suppSet fb X) (Aset X) (suppSet fc X)
      (Fw fa) (Fw fb) (Fw fc) hsuppA hsuppB hsuppC (suppSet_vanish fa X) (suppSet_vanish fb X)
      (suppSet_vanish fc X)
    rw [hcoll, collision_Aset_eq_energyE3]
    have hR' : energyE3 fa fb fc X ≤
        700 * C * Pm ^ 2 / (2 * (X : ℝ) + 1) ^ 2 := by
      refine le_trans hE (le_trans (le_of_eq ?_) hR)
      simp only [hB]
      push_cast
      rfl
    refine le_trans hR' ?_
    have hX2 : (0 : ℝ) < (2 * (X : ℝ) + 1) ^ 2 := by positivity
    apply div_le_div_of_nonneg_right _ hX2.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ hPm0.le hMT 2

/-! ### The assembly -/

/-- **`EnergyInput3` from `CentralBound3`.** -/
theorem energyInput3_of_central {D C ε : ℝ} (hD : 3 ≤ D) (hC : 0 < C) (hDε : 2 / D ≤ ε)
    (hcb : CentralBound3 D C) : DD3Dense.EnergyInput3 ε := by
  obtain ⟨X₀, hX₀⟩ := hcb
  refine ⟨700 * C, by positivity, fun M => ?_⟩
  obtain ⟨X, hX, na, nb, nc, hbuf⟩ := exists_buffered3 D hD (max M X₀)
  obtain ⟨A, B, C', f, g, h, hA, hB, hC', hdA, hdB, hdC, hM, hE⟩ :=
    energy_step3 D C ε hD hC hDε X na nb nc hbuf (hX₀ X na nb nc (le_trans (le_max_right _ _) hX) hbuf)
  exact ⟨X, le_trans (le_max_left _ _) hX, A, B, C', f, g, h, hA, hB, hC', hdA, hdB, hdC, hM, hE⟩

/-- **`DD {2,3,5}` from `CentralBound3` at every precision and the compact-quotient step.** -/
theorem DD235_of_central3 (hQ : DD3Dense.CompactQuotientCriterion3)
    (h : ∀ ε : ℝ, 0 < ε → ∃ D C : ℝ, 3 ≤ D ∧ 2 / D ≤ ε ∧ 0 < C ∧ CentralBound3 D C) :
    TVGPlus.DD ({2, 3, 5} : Finset ℕ) := by
  refine DD3Dense.DD235_of_energy hQ (fun ε hε => ?_)
  obtain ⟨D, C, hD, hDε, hC, hcb⟩ := h ε hε
  exact energyInput3_of_central hD hC hDε hcb

/-- **`DD {2,3,5}` for a general separation profile `a`**: the compact-quotient step for `ℤ²`, the two-term separations for the
three pairs (`HTT3`) and the finiteness of bad triples (`HFin`, the hypothesis `H(2,3,5)`). -/
theorem DD235_of_profile (hQ : DD3Dense.CompactQuotientCriterion3) (a : ℝ → ℝ) (ha : WindowProfile a)
    (hG : CloseGrowth a) (T₁ : ℝ) (htt : DD3Assemble.HTT3 a T₁) (K₁ : ℕ) (hH : DD3Assemble.HFin a K₁) :
    TVGPlus.DD ({2, 3, 5} : Finset ℕ) := by
  refine DD235_of_central3 hQ (fun ε hε => ?_)
  refine ⟨max 3 (2 / ε), ?_⟩
  have hD : 3 ≤ max 3 (2 / ε) := le_max_left _ _
  obtain ⟨C, hC, hcb⟩ := central_bound3 (max 3 (2 / ε)) a hD ha hG T₁ htt K₁ hH
  refine ⟨C, hD, ?_, hC, hcb⟩
  have h0 : 0 < max 3 (2 / ε) := by linarith
  rw [div_le_iff₀ h0]
  have h1 : 2 / ε ≤ max 3 (2 / ε) := le_max_right _ _
  have h2 : 2 / ε * ε = 2 := by field_simp
  nlinarith

/-- **`DD {2,3,5}` in the original form of the profile `A log²(2+t)`.** -/
theorem DD235_of_inputs (hQ : DD3Dense.CompactQuotientCriterion3) (A : ℝ) (hA : 0 ≤ A) (T₁ : ℝ) (K₁ : ℕ)
    (htt : DD3Assemble.HTT3 (fun t => A * (Real.log (2 + t)) ^ 2) T₁)
    (hH : DD3Assemble.HFin (fun t => A * (Real.log (2 + t)) ^ 2) K₁) :
    TVGPlus.DD ({2, 3, 5} : Finset ℕ) :=
  DD235_of_profile hQ _ (JANonDeep.windowProfile_A A hA) (JAProductFinal.closeGrowth_A A hA) T₁ htt K₁ hH

#print axioms final_ineq3
#print axioms hdiff_chainP
#print axioms energy_step3
#print axioms energyInput3_of_central
#print axioms DD235_of_central3
#print axioms DD235_of_profile
#print axioms DD235_of_inputs

end DD3Final
end LeanCheck
