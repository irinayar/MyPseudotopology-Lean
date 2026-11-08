import Mathlib
import LeanCheck.DD3Final
import LeanCheck.DD3GenCentral
import LeanCheck.DD3GenDense
import LeanCheck.DD3GenPn

/-!
# Three chains with general exponents: from the central bound to diagonal density (Lean check)

Scope. Counterpart of `DD3Final` for the chains with general exponents `Ex b k` satisfying `Mod3 Ex` (`DD3GenScalar`), with the
target `DD3GenDense.DDS (scalesE Ex) {2,3,5}` (diagonal density for the scale sets `{p^(Ex p n)}`; for `Ex p k = k²` this is
`TVGPlus.DD {2,3,5}`). The text is that of `DD3Final` with the chains `chainE`, the scale sets `scalesE`, the buffered heights
`exists_buffered3E`, the central bound `central_bound3E` and the endgame `DD3GenDense`:

* `hdiff_chainE`: the supports of the cascade weights have small differences in `P_p` for the scale set `scalesE Ex p`
  (`Pn_of_chainE`);
* `energy_step3E`: at one buffered height with `CentralAt3E`, the shifts of `DD3Multi.multi_realization3` give sets
  `A, B, C ⊆ [0, X]` with small differences in `scalesE Ex 2, 3, 5` and weights with the three-fold collision energy at most
  `700 C M² / (2X+1)²`;
* `energyInput3_of_central`: `CentralBound3E` with `2/D ≤ ε` gives `DD3GenDense.EnergyInput3 (scalesE Ex) ε`;
* `DD235_of_central3`: the compact-quotient criterion for `scalesE Ex` and `CentralBound3E` at every precision give
  `DDS (scalesE Ex) {2,3,5}`;
* `DD235_of_profile`, `DD235_of_inputs`: the same from `HTT3E` and `HFinE` (via `central_bound3E`), for a window profile `a`,
  resp. the profile `A log²(2+t)`.

Remaining hypotheses (not proved here): the compact-quotient criterion for `scalesE Ex` (`DD3GenDense.CompactQuotientCriterion3`),
`HTT3E` (the two-term separations for the three pairs, for the exponents `Ex`) and `HFinE` (finitely many bad triples). A Lean
proof verifies its formal statement under its hypotheses; the correspondence with the research note requires mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open Finset MixedPrime JATransfer JARandom JAEnergyLink JAEnergyIdentity JAAssembly JAWindowQ JABlocks JALocalize
  JASupport JADense JAFinal JAMulti JAMulti2 JAFinal2 DD3Energy DD3Multi JAHeights

/-! ### The supports have small differences -/

lemma hdiff_chainE {Ex : ℕ → ℕ → ℕ} (p : ℕ) [NeZero p] (hp : 2 ≤ p) (he : Monotone (Ex p)) (s n X : ℕ) (D ε : ℝ) (hD0 : 0 < D) (hDε : 2 / D ≤ ε)
    (hL : D * X < (p : ℝ) ^ (Ex p (s + n + 1))) (τ : ∀ k, ZMod ((chainE p (Ex p) he s D).q k)) :
    ∀ a ∈ suppSet ((chainE p (Ex p) he s D).weights τ (deltaSeed (p ^ (Ex p (s + 0)))) n) X,
      ∀ a' ∈ suppSet ((chainE p (Ex p) he s D).weights τ (deltaSeed (p ^ (Ex p (s + 0)))) n) X,
        Pn (scalesE Ex p) (a - a') < ε := by
  intro a ha a' ha'
  obtain ⟨hX, hg⟩ := mem_suppSet _ X ha
  obtain ⟨hX', hg'⟩ := mem_suppSet _ X ha'
  obtain ⟨hdv, hlev⟩ := support_chain (chainE p (Ex p) he s D) D hD0 (fun k => rfl) τ _
    (deltaSeed_support _) n a a' hg hg'
  exact lt_of_lt_of_le (Pn_of_chainE hp he s n X D hD0 hL a a' hX hX' hdv hlev) hDε

/-! ### One height -/

set_option maxHeartbeats 1600000 in
/-- **One buffered height gives the energy data of `EnergyInput3`.** -/
theorem energy_step3E {Ex : ℕ → ℕ → ℕ} (hEx : Mod3 Ex) (D C ε : ℝ) (hD : 3 ≤ D) (hC : 0 < C) (hDε : 2 / D ≤ ε) (X na nb nc : ℕ)
    (hbuf : Buffered3E Ex D X na nb nc) (hcen : CentralAt3E Ex hEx.mono2 hEx.mono3 hEx.mono5 D C X (sE D) na (sE D) nb (sE D) nc) :
    ∃ (A B C' : Finset ℤ) (f g h : ℤ → ℝ),
      (∀ a ∈ A, 0 ≤ a ∧ a ≤ X) ∧ (∀ a ∈ B, 0 ≤ a ∧ a ≤ X) ∧ (∀ a ∈ C', 0 ≤ a ∧ a ≤ X) ∧
      (∀ a ∈ A, ∀ a' ∈ A, Pn (scalesE Ex 2) (a - a') < ε) ∧
      (∀ a ∈ B, ∀ a' ∈ B, Pn (scalesE Ex 3) (a - a') < ε) ∧
      (∀ a ∈ C', ∀ a' ∈ C', Pn (scalesE Ex 5) (a - a') < ε) ∧
      (∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C', h c) ≠ 0 ∧
      ∑ p ∈ A ×ˢ (B ×ˢ C'), ∑ q ∈ A ×ˢ (B ×ˢ C'),
          (if DD3.phi p = DD3.phi q then DD3.wt f g h p * DD3.wt f g h q else 0) ≤
        700 * C * ((∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C', h c)) ^ 2 / (2 * (X : ℝ) + 1) ^ 2 := by
  classical
  have hD0 : 0 < D := by linarith
  obtain ⟨hL₂, hL₃, hL₅, h4a, h4b, h4c⟩ := hbuf
  obtain ⟨m, hm1, hmN, hLm, hcen⟩ := hcen
  set sa : ℕ := sE D with hsa
  have hm2 : Monotone (Ex 2) := hEx.mono2
  have hm3 : Monotone (Ex 3) := hEx.mono3
  have hm5 : Monotone (Ex 5) := hEx.mono5
  have hsa3 : 3 ≤ sa := by
    have : (3 : ℝ) ≤ (sa : ℝ) := le_trans hD (le_trans (Nat.le_ceil D) (Nat.cast_le.2 (le_max_left _ _)))
    exact_mod_cast this
  set N : ℕ := NNE Ex sa na sa nb sa nc with hN
  have hNe : N = 2 ^ (Ex 2 (sa + na)) * 3 ^ (Ex 3 (sa + nb)) * 5 ^ (Ex 5 (sa + nc)) := rfl
  have hdA : (chainE 2 (Ex 2) hm2 sa D).q na ∣ N := by
    rw [hNe]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_right dvd_rfl _) _
  have hdB : (chainE 3 (Ex 3) hm3 sa D).q nb ∣ N := by
    rw [hNe]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _
  have hdC : (chainE 5 (Ex 5) hm5 sa D).q nc ∣ N := by
    rw [hNe]; exact Dvd.dvd.mul_left dvd_rfl _
  have hNa : ∀ k, k ≤ na → (chainE 2 (Ex 2) hm2 sa D).q k ∣ N := fun k hk =>
    (chain_dvd_of_le (chainE 2 (Ex 2) hm2 sa D) k na hk).trans hdA
  have hNb : ∀ k, k ≤ nb → (chainE 3 (Ex 3) hm3 sa D).q k ∣ N := fun k hk =>
    (chain_dvd_of_le (chainE 3 (Ex 3) hm3 sa D) k nb hk).trans hdB
  have hNc : ∀ k, k ≤ nc → (chainE 5 (Ex 5) hm5 sa D).q k ∣ N := fun k hk =>
    (chain_dvd_of_le (chainE 5 (Ex 5) hm5 sa D) k nc hk).trans hdC
  -- the seeds
  have hsum2 : ∑ y, deltaSeed ((chainE 2 (Ex 2) hm2 sa D).q 0) y = 1 := sum_deltaSeed _
  have hsum3 : ∑ y, deltaSeed ((chainE 3 (Ex 3) hm3 sa D).q 0) y = 1 := sum_deltaSeed _
  have hsum5 : ∑ y, deltaSeed ((chainE 5 (Ex 5) hm5 sa D).q 0) y = 1 := sum_deltaSeed _
  -- positivity of the central mass
  have hMa := Mavg_nonneg_pos0 (N := N) D na (chainE 2 (Ex 2) hm2 sa D) ((fun k => rfl))
    (kernq N ((chainE 2 (Ex 2) hm2 sa D).q 0) (deltaSeed ((chainE 2 (Ex 2) hm2 sa D).q 0))) (fun x => kern_nonneg' _ _ _ x)
    (lt_of_lt_of_le (by rw [hsum2]; norm_num)
      (kern_zero_ge (N := N) ((chainE 2 (Ex 2) hm2 sa D).q 0) (N / (chainE 2 (Ex 2) hm2 sa D).q 0)
        (deltaSeed ((chainE 2 (Ex 2) hm2 sa D).q 0))))
  have hMb := Mavg_nonneg_pos0 (N := N) D nb (chainE 3 (Ex 3) hm3 sa D) ((fun k => rfl))
    (kernq N ((chainE 3 (Ex 3) hm3 sa D).q 0) (deltaSeed ((chainE 3 (Ex 3) hm3 sa D).q 0))) (fun x => kern_nonneg' _ _ _ x)
    (lt_of_lt_of_le (by rw [hsum3]; norm_num)
      (kern_zero_ge (N := N) ((chainE 3 (Ex 3) hm3 sa D).q 0) (N / (chainE 3 (Ex 3) hm3 sa D).q 0)
        (deltaSeed ((chainE 3 (Ex 3) hm3 sa D).q 0))))
  have hMc := Mavg_nonneg_pos0 (N := N) D nc (chainE 5 (Ex 5) hm5 sa D) ((fun k => rfl))
    (kernq N ((chainE 5 (Ex 5) hm5 sa D).q 0) (deltaSeed ((chainE 5 (Ex 5) hm5 sa D).q 0))) (fun x => kern_nonneg' _ _ _ x)
    (lt_of_lt_of_le (by rw [hsum5]; norm_num)
      (kern_zero_ge (N := N) ((chainE 5 (Ex 5) hm5 sa D).q 0) (N / (chainE 5 (Ex 5) hm5 sa D).q 0)
        (deltaSeed ((chainE 5 (Ex 5) hm5 sa D).q 0))))
  set Ma := Mavg N na (chainE 2 (Ex 2) hm2 sa D) (kernq N ((chainE 2 (Ex 2) hm2 sa D).q 0) (deltaSeed ((chainE 2 (Ex 2) hm2 sa D).q 0))) with hMa_def
  set Mb := Mavg N nb (chainE 3 (Ex 3) hm3 sa D) (kernq N ((chainE 3 (Ex 3) hm3 sa D).q 0) (deltaSeed ((chainE 3 (Ex 3) hm3 sa D).q 0))) with hMb_def
  set Mc := Mavg N nc (chainE 5 (Ex 5) hm5 sa D) (kernq N ((chainE 5 (Ex 5) hm5 sa D).q 0) (deltaSeed ((chainE 5 (Ex 5) hm5 sa D).q 0))) with hMc_def
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
  obtain ⟨τa, τb, τc, hE⟩ := multi_realization3 (N := N) na nb nc (chainE 2 (Ex 2) hm2 sa D) (chainE 3 (Ex 3) hm3 sa D) (chainE 5 (Ex 5) hm5 sa D)
    hNa hNb hNc ((fun k x => wQ_nonneg D x)) ((fun k x => wQ_nonneg D x)) ((fun k x => wQ_nonneg D x))
    (deltaSeed ((chainE 2 (Ex 2) hm2 sa D).q 0)) (deltaSeed ((chainE 3 (Ex 3) hm3 sa D).q 0)) (deltaSeed ((chainE 5 (Ex 5) hm5 sa D).q 0))
    (deltaSeed_nonneg _) (deltaSeed_nonneg _) (deltaSeed_nonneg _) X m hm1 hmN hLm
  set fa := (chainE 2 (Ex 2) hm2 sa D).weights τa (deltaSeed ((chainE 2 (Ex 2) hm2 sa D).q 0)) na with hfa
  set fb := (chainE 3 (Ex 3) hm3 sa D).weights τb (deltaSeed ((chainE 3 (Ex 3) hm3 sa D).q 0)) nb with hfb
  set fc := (chainE 5 (Ex 5) hm5 sa D).weights τc (deltaSeed ((chainE 5 (Ex 5) hm5 sa D).q 0)) nc with hfc
  have hQa : (0 : ℝ) < (chainE 2 (Ex 2) hm2 sa D).q na := by exact_mod_cast (chainE 2 (Ex 2) hm2 sa D).pos na
  have hQb : (0 : ℝ) < (chainE 3 (Ex 3) hm3 sa D).q nb := by exact_mod_cast (chainE 3 (Ex 3) hm3 sa D).pos nb
  have hQc : (0 : ℝ) < (chainE 5 (Ex 5) hm5 sa D).q nc := by exact_mod_cast (chainE 5 (Ex 5) hm5 sa D).pos nc
  have hQa4 : (4 : ℝ) * (chainE 2 (Ex 2) hm2 sa D).q na ≤ X := by exact_mod_cast h4a
  have hQb4 : (4 : ℝ) * (chainE 3 (Ex 3) hm3 sa D).q nb ≤ X := by exact_mod_cast h4b
  have hQc4 : (4 : ℝ) * (chainE 5 (Ex 5) hm5 sa D).q nc ≤ X := by exact_mod_cast h4c
  have hX1 : (1 : ℝ) ≤ X := by
    have : 4 * 2 ^ (Ex 2 (sa + na)) ≤ X := h4a
    have h1 : 1 ≤ 2 ^ (Ex 2 (sa + na)) := Nat.one_le_pow _ _ (by norm_num)
    have : 1 ≤ X := by omega
    exact_mod_cast this
  have hq2 : (chainE 2 (Ex 2) hm2 sa D).q na ≤ X + 1 :=
    le_trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) h4a) (Nat.le_succ X)
  have hq3 : (chainE 3 (Ex 3) hm3 sa D).q nb ≤ X + 1 :=
    le_trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) h4b) (Nat.le_succ X)
  have hq5 : (chainE 5 (Ex 5) hm5 sa D).q nc ≤ X + 1 :=
    le_trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) h4c) (Nat.le_succ X)
  have hIa : ∀ k, k < na → 2 < (((2 ^ (Ex 2 (sa + k + 1) - Ex 2 (sa + k)) : ℕ) : ℝ) * (16 / (15 * D))) :=
    fun k _ => (by have := alpha_I_ge4 hEx (p := 2) (by simp) D hD k; linarith)
  have hIb : ∀ k, k < nb → 2 < (((3 ^ (Ex 3 (sa + k + 1) - Ex 3 (sa + k)) : ℕ) : ℝ) * (16 / (15 * D))) :=
    fun k _ => (by have := alpha_I_ge4 hEx (p := 3) (by simp) D hD k; linarith)
  have hIc : ∀ k, k < nc → 2 < (((5 ^ (Ex 5 (sa + k + 1) - Ex 5 (sa + k)) : ℕ) : ℝ) * (16 / (15 * D))) :=
    fun k _ => (by have := alpha_I_ge4 hEx (p := 5) (by simp) D hD k; linarith)
  have hTa := total_lower_chain (chainE 2 (Ex 2) hm2 sa D) D hD ((fun k => rfl)) ((fun k x => wQ_nonneg D x))
    (fun k => 2 ^ (Ex 2 (sa + k + 1) - Ex 2 (sa + k))) (chainE_alpha 2 (Ex 2) hm2 sa D) τa (deltaSeed ((chainE 2 (Ex 2) hm2 sa D).q 0))
    (deltaSeed_nonneg _) na hIa X hq2
  have hTb := total_lower_chain (chainE 3 (Ex 3) hm3 sa D) D hD ((fun k => rfl)) ((fun k x => wQ_nonneg D x))
    (fun k => 3 ^ (Ex 3 (sa + k + 1) - Ex 3 (sa + k))) (chainE_alpha 3 (Ex 3) hm3 sa D) τb (deltaSeed ((chainE 3 (Ex 3) hm3 sa D).q 0))
    (deltaSeed_nonneg _) nb hIb X hq3
  have hTc := total_lower_chain (chainE 5 (Ex 5) hm5 sa D) D hD ((fun k => rfl)) ((fun k x => wQ_nonneg D x))
    (fun k => 5 ^ (Ex 5 (sa + k + 1) - Ex 5 (sa + k))) (chainE_alpha 5 (Ex 5) hm5 sa D) τc (deltaSeed ((chainE 5 (Ex 5) hm5 sa D).q 0))
    (deltaSeed_nonneg _) nc hIc X hq5
  rw [hsum2, mul_one] at hTa
  rw [hsum3, mul_one] at hTb
  rw [hsum5, mul_one] at hTc
  set ma := ∏ k ∈ range na, (((2 ^ (Ex 2 (sa + k + 1) - Ex 2 (sa + k)) : ℕ) : ℝ) * (16 / (15 * D)) - 2) with hma
  set mb := ∏ k ∈ range nb, (((3 ^ (Ex 3 (sa + k + 1) - Ex 3 (sa + k)) : ℕ) : ℝ) * (16 / (15 * D)) - 2) with hmb
  set mc := ∏ k ∈ range nc, (((5 ^ (Ex 5 (sa + k + 1) - Ex 5 (sa + k)) : ℕ) : ℝ) * (16 / (15 * D)) - 2) with hmc
  have hpa : 0 < ma := Finset.prod_pos (fun k hk => by linarith [hIa k (Finset.mem_range.mp hk)])
  have hpb : 0 < mb := Finset.prod_pos (fun k hk => by linarith [hIb k (Finset.mem_range.mp hk)])
  have hpc : 0 < mc := Finset.prod_pos (fun k hk => by linarith [hIc k (Finset.mem_range.mp hk)])
  have hXa : (0 : ℝ) < (X : ℝ) + 1 - (chainE 2 (Ex 2) hm2 sa D).q na := by linarith
  have hXb : (0 : ℝ) < (X : ℝ) + 1 - (chainE 3 (Ex 3) hm3 sa D).q nb := by linarith
  have hXc : (0 : ℝ) < (X : ℝ) + 1 - (chainE 5 (Ex 5) hm5 sa D).q nc := by linarith
  have hca : 0 < ((X : ℝ) + 1 - (chainE 2 (Ex 2) hm2 sa D).q na) / (chainE 2 (Ex 2) hm2 sa D).q na * ma := by positivity
  have hcb : 0 < ((X : ℝ) + 1 - (chainE 3 (Ex 3) hm3 sa D).q nb) / (chainE 3 (Ex 3) hm3 sa D).q nb * mb := by positivity
  have hcc : 0 < ((X : ℝ) + 1 - (chainE 5 (Ex 5) hm5 sa D).q nc) / (chainE 5 (Ex 5) hm5 sa D).q nc * mc := by positivity
  have hMT := mul_le_mul (mul_le_mul hTa hTb hcb.le (le_trans hca.le hTa)) hTc hcc.le
    (mul_nonneg (le_trans hca.le hTa) (le_trans hcb.le hTb))
  set Pm : ℝ := (((X : ℝ) + 1 - (chainE 2 (Ex 2) hm2 sa D).q na) / (chainE 2 (Ex 2) hm2 sa D).q na * ma) *
    (((X : ℝ) + 1 - (chainE 3 (Ex 3) hm3 sa D).q nb) / (chainE 3 (Ex 3) hm3 sa D).q nb * mb) *
    (((X : ℝ) + 1 - (chainE 5 (Ex 5) hm5 sa D).q nc) / (chainE 5 (Ex 5) hm5 sa D).q nc * mc) with hPm
  have hPm0 : 0 < Pm := by rw [hPm]; positivity
  set B := ∑ t ∈ arc N (m - 1), conv Ma (conv Mb Mc) t with hB
  have hBY : B ≤ C * (ma * mb * mc) ^ 2 := hcen
  have hB0 : 0 ≤ B := hBpos.le
  have hR := DD3Final.final_ineq3 (X : ℝ) ((chainE 2 (Ex 2) hm2 sa D).q na) ((chainE 3 (Ex 3) hm3 sa D).q nb) ((chainE 5 (Ex 5) hm5 sa D).q nc) ma mb mc B C
    hX1 hQa hQb hQc hQa4 hQb4 hQc4 hpa hpb hpc hB0 hC hBY
  -- the sets and weights
  have hsuppA := suppSet_subset fa X
  have hsuppB := suppSet_subset fb X
  have hsuppC := suppSet_subset fc X
  refine ⟨suppSet fa X, suppSet fb X, suppSet fc X, Fw fa, Fw fb, Fw fc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; exact (mem_suppSet fa X ha).1
  · intro a ha; exact (mem_suppSet fb X ha).1
  · intro a ha; exact (mem_suppSet fc X ha).1
  · exact hdiff_chainE 2 le_rfl hEx.mono2 sa na X D ε hD0 hDε hL₂ τa
  · exact hdiff_chainE 3 (by norm_num) hEx.mono3 sa nb X D ε hD0 hDε hL₃ τb
  · exact hdiff_chainE 5 (by norm_num) hEx.mono5 sa nc X D ε hD0 hDε hL₅ τc
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
theorem energyInput3_of_central {Ex : ℕ → ℕ → ℕ} (hEx : Mod3 Ex) {D C ε : ℝ} (hD : 3 ≤ D) (hC : 0 < C) (hDε : 2 / D ≤ ε)
    (hcb : CentralBound3E Ex hEx.mono2 hEx.mono3 hEx.mono5 D C) : DD3GenDense.EnergyInput3 (scalesE Ex) ε := by
  obtain ⟨X₀, hX₀⟩ := hcb
  refine ⟨700 * C, by positivity, fun M => ?_⟩
  obtain ⟨X, hX, na, nb, nc, hbuf⟩ := exists_buffered3E hEx.ok D hD (max M X₀)
  obtain ⟨A, B, C', f, g, h, hA, hB, hC', hdA, hdB, hdC, hM, hE⟩ :=
    energy_step3E hEx D C ε hD hC hDε X na nb nc hbuf (hX₀ X na nb nc (le_trans (le_max_right _ _) hX) hbuf)
  exact ⟨X, le_trans (le_max_left _ _) hX, A, B, C', f, g, h, hA, hB, hC', hdA, hdB, hdC, hM, hE⟩

/-- **`DD {2,3,5}` from `CentralBound3` at every precision and the compact-quotient step.** -/
theorem DD235_of_central3 {Ex : ℕ → ℕ → ℕ} (hEx : Mod3 Ex) (hQ : DD3GenDense.CompactQuotientCriterion3 (scalesE Ex))
    (h : ∀ ε : ℝ, 0 < ε → ∃ D C : ℝ, 3 ≤ D ∧ 2 / D ≤ ε ∧ 0 < C ∧ CentralBound3E Ex hEx.mono2 hEx.mono3 hEx.mono5 D C) :
    DD3GenDense.DDS (scalesE Ex) ({2, 3, 5} : Finset ℕ) := by
  refine DD3GenDense.DD235_of_energy (scalesE Ex) hQ (fun ε hε => ?_)
  obtain ⟨D, C, hD, hDε, hC, hcb⟩ := h ε hε
  exact energyInput3_of_central hEx hD hC hDε hcb

/-- **`DD {2,3,5}` for a general separation profile `a`**: the compact-quotient step for `ℤ²`, the two-term separations for the
three pairs (`HTT3`) and the finiteness of bad triples (`HFin`, the hypothesis `H(2,3,5)`). -/
theorem DD235_of_profile {Ex : ℕ → ℕ → ℕ} (hEx : Mod3 Ex) (hQ : DD3GenDense.CompactQuotientCriterion3 (scalesE Ex)) (a : ℝ → ℝ) (ha : WindowProfile a)
    (hG : CloseGrowth a) (T₁ : ℝ) (htt : HTT3E Ex a T₁) (K₁ : ℕ) (hH : HFinE Ex a K₁) :
    DD3GenDense.DDS (scalesE Ex) ({2, 3, 5} : Finset ℕ) := by
  refine DD235_of_central3 hEx hQ (fun ε hε => ?_)
  refine ⟨max 3 (2 / ε), ?_⟩
  have hD : 3 ≤ max 3 (2 / ε) := le_max_left _ _
  obtain ⟨C, hC, hcb⟩ := central_bound3E hEx (max 3 (2 / ε)) a hD ha hG T₁ htt K₁ hH
  refine ⟨C, hD, ?_, hC, hcb⟩
  have h0 : 0 < max 3 (2 / ε) := by linarith
  rw [div_le_iff₀ h0]
  have h1 : 2 / ε ≤ max 3 (2 / ε) := le_max_right _ _
  have h2 : 2 / ε * ε = 2 := by field_simp
  nlinarith

/-- **`DD {2,3,5}` in the original form of the profile `A log²(2+t)`.** -/
theorem DD235_of_inputs {Ex : ℕ → ℕ → ℕ} (hEx : Mod3 Ex) (hQ : DD3GenDense.CompactQuotientCriterion3 (scalesE Ex)) (A : ℝ) (hA : 0 ≤ A) (T₁ : ℝ) (K₁ : ℕ)
    (htt : HTT3E Ex (fun t => A * (Real.log (2 + t)) ^ 2) T₁)
    (hH : HFinE Ex (fun t => A * (Real.log (2 + t)) ^ 2) K₁) :
    DD3GenDense.DDS (scalesE Ex) ({2, 3, 5} : Finset ℕ) :=
  DD235_of_profile hEx hQ _ (JANonDeep.windowProfile_A A hA) (JAProductFinal.closeGrowth_A A hA) T₁ htt K₁ hH


end DD3Gen
end LeanCheck
