import Mathlib
import LeanCheck.JAMulti2

/-!
# `DenseDifferences` from a deterministic height hypothesis

`JAFinal.HeightBound` contained shifts of the earlier levels in its statement.  With the multi-level realization
(`JAMulti.multi_exists`, `JAMulti2.multi_realization`) the shifts at ALL levels are produced by the averaging argument, and the
hypothesis becomes a statement about the DETERMINISTIC expected kernel measures `Mavg` only:

`HeightBound2 D C X`: there are start levels `s_2, s_3` and depths `n_2, n_3` such that the chains
`q_k = p^{(s+k)^2}`, windows `w_{q_k}`, seed `δ_0` on `ZMod p^{s^2}` (the multiples of `p^{s^2}`; this takes care of the coarse
scales `p^{j^2}`, `j ≤ s`, where the window would only see `0`), satisfy: the last scales are the largest `p^{m^2} ≤ DX`
and buffered (`4 q ≤ X`), `α_k I_1 > 2` at every level, and for some `m` with `N ≤ (X+1+Q_a+Q_b) m` the central arc mass of
the product `Mavg_a ∗ Mavg_b` is at most `C (∏_a (α_kI_1-2) · ∏_b (α_kI_1-2))^2`.

Checked here (no axiom, no `sorry`): `chainP`, `deltaSeed`, `Pn_of_chainP`, `denseDifferences_of_heightBounds2`,
`JA_of_heightBounds2`.
-/

namespace LeanCheck
namespace JAFinal2

open Finset MixedPrime JATransfer JARandom JAEnergyLink JAEnergyIdentity JAAssembly JAWindowQ JABlocks JALocalize
  JASupport JADense JAFinal JAMulti JAMulti2

/-- The chain `q_k = p^{(s+k)^2}` with windows `w_{q_k}`. -/
noncomputable def chainP (p s : ℕ) [NeZero p] (D : ℝ) : Chain where
  q := fun k => p ^ ((s + k) ^ 2)
  pos := fun k => Nat.pos_of_ne_zero (NeZero.ne _)
  dvd := fun k => pow_dvd_pow p (Nat.pow_le_pow_left (by omega) 2)
  w := fun k => wQ D (p ^ ((s + k) ^ 2))

/-- The indicator of `0`. -/
noncomputable def deltaSeed (Q : ℕ) [NeZero Q] : ZMod Q → ℝ := fun x => if x = 0 then 1 else 0

lemma deltaSeed_nonneg (Q : ℕ) [NeZero Q] (x : ZMod Q) : 0 ≤ deltaSeed Q x := by
  unfold deltaSeed; split_ifs <;> norm_num

lemma deltaSeed_zero (Q : ℕ) [NeZero Q] : deltaSeed Q 0 = 1 := by simp [deltaSeed]

lemma sum_deltaSeed (Q : ℕ) [NeZero Q] : ∑ y, deltaSeed Q y = 1 := by
  unfold deltaSeed
  simp

lemma deltaSeed_support (Q : ℕ) [NeZero Q] (x : ZMod Q) (h : deltaSeed Q x ≠ 0) : x = 0 := by
  unfold deltaSeed at h
  by_contra hx
  exact h (by simp [hx])

section chainP_facts

variable (p s : ℕ) [NeZero p] (D : ℝ)

lemma chainP_w (k : ℕ) : (chainP p s D).w (k + 1) = wQ D ((chainP p s D).q (k + 1)) := rfl

lemma chainP_w0 (k : ℕ) (x : ZMod ((chainP p s D).q k)) : 0 ≤ (chainP p s D).w k x :=
  wQ_nonneg D x

lemma chainP_α (k : ℕ) :
    (chainP p s D).q (k + 1) = (chainP p s D).q k * p ^ (2 * (s + k) + 1) :=
  pow_succ_sq p (s + k)

end chainP_facts

/-- `P_p(a - a') < 2/D` from the levels of a `chainP` cascade. -/
lemma Pn_of_chainP {p : ℕ} [NeZero p] (hp : 2 ≤ p) (s n X : ℕ) (D : ℝ) (hD : 0 < D)
    (hL : D * X < (p : ℝ) ^ ((s + n + 1) ^ 2)) (a a' : ℤ) (haX : 0 ≤ a ∧ a ≤ X) (ha'X : 0 ≤ a' ∧ a' ≤ X)
    (hdv : ((p ^ (s ^ 2) : ℕ) : ℤ) ∣ a - a')
    (hlev : ∀ j : ℕ, 1 ≤ j → j ≤ n → nrm (((a - a' : ℤ) : ℝ) / ((p ^ ((s + j) ^ 2) : ℕ) : ℝ)) < 2 / D) :
    Pn (sqScales p) (a - a') < 2 / D := by
  refine Pn_of_levels hp D hD X (s + n) hL a a' haX ha'X ?_
  intro i hi1 hi2
  by_cases his : i ≤ s
  · have hd1 : ((p ^ (i ^ 2) : ℕ) : ℤ) ∣ a - a' :=
      (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (Nat.pow_le_pow_left his 2))).trans hdv
    obtain ⟨c, hc⟩ := hd1
    have hpos : (0 : ℝ) < ((p ^ (i ^ 2) : ℕ) : ℝ) := by
      have : 0 < p := by omega
      positivity
    have e : ((a - a' : ℤ) : ℝ) / ((p ^ (i ^ 2) : ℕ) : ℝ) = (c : ℝ) := by
      rw [hc]
      push_cast
      field_simp
    rw [e, nrm_int]
    positivity
  · have hj : i = s + (i - s) := by omega
    have := hlev (i - s) (by omega) (by omega)
    rwa [← hj] at this

/-! ### The deterministic height hypothesis -/

/-- **The deterministic central bound (not proved here)**: component 13 for the expected cascade measures at the height `X`
with start levels `sa, sb` and depths `na, nb`. -/
def CentralAt (D C : ℝ) (X sa na sb nb : ℕ) : Prop :=
  ∃ m : ℕ,
    1 ≤ m ∧ m ≤ 2 ^ ((sa + na) ^ 2) * 3 ^ ((sb + nb) ^ 2) ∧
    2 ^ ((sa + na) ^ 2) * 3 ^ ((sb + nb) ^ 2) ≤
      (X + 1 + 2 ^ ((sa + na) ^ 2) + 3 ^ ((sb + nb) ^ 2)) * m ∧
    ∑ t ∈ arc (2 ^ ((sa + na) ^ 2) * 3 ^ ((sb + nb) ^ 2)) (m - 1),
        conv (Mavg (2 ^ ((sa + na) ^ 2) * 3 ^ ((sb + nb) ^ 2)) na (chainP 2 sa D)
            (kernq (2 ^ ((sa + na) ^ 2) * 3 ^ ((sb + nb) ^ 2)) (2 ^ ((sa + 0) ^ 2))
              (deltaSeed (2 ^ ((sa + 0) ^ 2)))))
          (Mavg (2 ^ ((sa + na) ^ 2) * 3 ^ ((sb + nb) ^ 2)) nb (chainP 3 sb D)
            (kernq (2 ^ ((sa + na) ^ 2) * 3 ^ ((sb + nb) ^ 2)) (3 ^ ((sb + 0) ^ 2))
              (deltaSeed (3 ^ ((sb + 0) ^ 2))))) t ≤
      C * ((∏ k ∈ range na, (((2 ^ (2 * (sa + k) + 1) : ℕ) : ℝ) * (16 / (15 * D)) - 2)) *
        (∏ k ∈ range nb, (((3 ^ (2 * (sb + k) + 1) : ℕ) : ℝ) * (16 / (15 * D)) - 2))) ^ 2

/-- **The deterministic height hypothesis**: scales, buffer, large `α`, and the central bound. -/
def HeightBound2 (D C : ℝ) (X : ℕ) : Prop :=
  ∃ (sa na sb nb : ℕ),
    D * X < (2 : ℝ) ^ ((sa + na + 1) ^ 2) ∧ D * X < (3 : ℝ) ^ ((sb + nb + 1) ^ 2) ∧
    4 * 2 ^ ((sa + na) ^ 2) ≤ X ∧ 4 * 3 ^ ((sb + nb) ^ 2) ≤ X ∧
    (∀ k, k < na → 2 < ((2 ^ (2 * (sa + k) + 1) : ℕ) : ℝ) * (16 / (15 * D))) ∧
    (∀ k, k < nb → 2 < ((3 ^ (2 * (sb + k) + 1) : ℕ) : ℝ) * (16 / (15 * D))) ∧
    CentralAt D C X sa na sb nb

/-- **The assembly.**  `HeightBound2 D C X` for arbitrarily large `X` gives `DenseDifferences ε`. -/
theorem denseDifferences_of_heightBounds2 {ε : ℝ} (D C : ℝ) (hD : 3 ≤ D) (hDε : 2 / D ≤ ε) (hC : 0 < C)
    (hH : ∀ M : ℕ, ∃ X : ℕ, M ≤ X ∧ HeightBound2 D C X) : DenseDifferences ε := by
  have hD0 : 0 < D := by linarith
  refine ⟨1 / (64 * C), by positivity, ?_⟩
  intro M
  obtain ⟨X, hMX, sa, na, sb, nb, hL₂, hL₃, hb₂, hb₃, hI₂, hI₃, hcentral⟩ := hH M
  obtain ⟨m, hm1, hmN, hLm, hcen⟩ := hcentral
  refine ⟨X, hMX, ?_⟩
  have hdiffa : ∀ τ : ∀ k, ZMod ((chainP 2 sa D).q k), ∀ a ∈ suppSet ((chainP 2 sa D).weights τ
        (deltaSeed (2 ^ ((sa + 0) ^ 2))) na) X,
      ∀ a' ∈ suppSet ((chainP 2 sa D).weights τ (deltaSeed (2 ^ ((sa + 0) ^ 2))) na) X,
        Pn (sqScales 2) (a - a') < ε := by
    intro τ a ha a' ha'
    obtain ⟨hX, hg⟩ := mem_suppSet _ X ha
    obtain ⟨hX', hg'⟩ := mem_suppSet _ X ha'
    obtain ⟨hdv, hlev⟩ := support_chain (chainP 2 sa D) D hD0 (chainP_w 2 sa D) τ _
      (deltaSeed_support _) na a a' hg hg'
    exact lt_of_lt_of_le (Pn_of_chainP (p := 2) (by norm_num) sa na X D hD0 hL₂ a a' hX hX' hdv hlev) hDε
  have hdiffb : ∀ τ : ∀ k, ZMod ((chainP 3 sb D).q k), ∀ a ∈ suppSet ((chainP 3 sb D).weights τ
        (deltaSeed (3 ^ ((sb + 0) ^ 2))) nb) X,
      ∀ a' ∈ suppSet ((chainP 3 sb D).weights τ (deltaSeed (3 ^ ((sb + 0) ^ 2))) nb) X,
        Pn (sqScales 3) (a - a') < ε := by
    intro τ a ha a' ha'
    obtain ⟨hX, hg⟩ := mem_suppSet _ X ha
    obtain ⟨hX', hg'⟩ := mem_suppSet _ X ha'
    obtain ⟨hdv, hlev⟩ := support_chain (chainP 3 sb D) D hD0 (chainP_w 3 sb D) τ _
      (deltaSeed_support _) nb a a' hg hg'
    exact lt_of_lt_of_le (Pn_of_chainP (p := 3) (by norm_num) sb nb X D hD0 hL₃ a a' hX hX' hdv hlev) hDε
  have hsum2 : ∑ y, deltaSeed ((chainP 2 sa D).q 0) y = 1 := sum_deltaSeed _
  have hsum3 : ∑ y, deltaSeed ((chainP 3 sb D).q 0) y = 1 := sum_deltaSeed _
  refine dense_step_multi (chainP 2 sa D) (chainP 3 sb D) D C ε hD hC (chainP_w 2 sa D) (chainP_w 3 sb D)
    (chainP_w0 2 sa D) (chainP_w0 3 sb D) (fun k => 2 ^ (2 * (sa + k) + 1)) (fun k => 3 ^ (2 * (sb + k) + 1))
    (chainP_α 2 sa D) (chainP_α 3 sb D) (deltaSeed ((chainP 2 sa D).q 0))
    (deltaSeed ((chainP 3 sb D).q 0)) (deltaSeed_nonneg _) (deltaSeed_nonneg _) ?_ ?_ ?_ ?_ na nb hI₂ hI₃ X m
    hm1 hmN hLm hb₂ hb₃ ?_ hdiffa hdiffb
  · rw [deltaSeed_zero]; exact one_pos
  · rw [deltaSeed_zero]; exact one_pos
  · rw [hsum2]; exact one_pos
  · rw [hsum3]; exact one_pos
  · rw [hsum2, hsum3, mul_one, mul_one]
    exact hcen

/-- **JA from the two remaining hypotheses**: the compact-quotient criterion and the deterministic height bounds. -/
theorem JA_of_heightBounds2 (hQ : CompactQuotientCriterion)
    (h : ∀ ε : ℝ, 0 < ε → ∃ D C : ℝ, 3 ≤ D ∧ 2 / D ≤ ε ∧ 0 < C ∧
      ∀ M : ℕ, ∃ X : ℕ, M ≤ X ∧ HeightBound2 D C X) : JAProp := by
  refine JA_of_dense_differences hQ (fun ε hε => ?_)
  obtain ⟨D, C, hD, hDε, hC, hH⟩ := h ε hε
  exact denseDifferences_of_heightBounds2 D C hD hDε hC hH

#print axioms Pn_of_chainP
#print axioms denseDifferences_of_heightBounds2
#print axioms JA_of_heightBounds2

end JAFinal2
end LeanCheck
