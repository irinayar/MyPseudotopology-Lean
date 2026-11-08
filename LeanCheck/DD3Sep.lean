import Mathlib
import LeanCheck.DD3Quotient
import LeanCheck.JAClose

/-!
# Diagonal density for three primes: `HTT3` from the pair separations (Lean check)

Scope. Last piece of the reduction of the hypotheses of the conditional Lean proof of `DD({2,3,5})` (research note
`TVGplus_conditional_DD235_2026-11-07.md`, item 3). `DD3Assemble.HTT3` is the two-term separation for ordered pairs of distinct
bases in `{2,3,5}` and all sign patterns. Here it is reduced, as in `JAClose.hTT_of_two_term_G` for the pair `{2,3}`, to the
opposite-sign case for each unordered pair:

* `TwoTermSepPair p q a`: the opposite-sign two-term separation with profile `a` for the pair `{p,q}`; `TwoTermSepPair 2 3 a` is
  `JAClose.TwoTermSep a` (`twoTermSep_iff`);
* `HTT3_exists`: `TwoTermSepPair 2 3 a`, `TwoTermSepPair 2 5 a` and `TwoTermSepPair 3 5 a` (with `a ≥ 0`) give `HTT3 a T₁` for
  some `T₁`; the cases `s = 0` or `r s > 0` are elementary (`JAClose.two_term_easy`);
* `DD235_of_pairs`, `DD235_of_pairs_A`: `DD {2,3,5}` from the three pair separations and the finiteness of bad triples `HFin`
  alone (no other hypothesis): the compact-quotient step is `DD3Quotient.compactQuotientCriterion3`.

The separations for the pairs are the external input (Matveev's bound for linear forms in two logarithms, hand argument in the
article); `HFin` is the hypothesis `H(2,3,5)` of the note. A Lean proof verifies its formal statement under its hypotheses; the
correspondence with the research note requires mathematical review.
-/

namespace LeanCheck
namespace DD3Sep

open MixedPrime JAAssembly JAClose

/-- The opposite-sign separation for the pair `{p,q}` with threshold `T₀`. -/
def SepBody (a : ℝ → ℝ) (T₀ : ℝ) (p q : ℕ) : Prop :=
  ∀ (b n b' n' : ℕ) (r s : ℤ), ((b = p ∧ b' = q) ∨ (b = q ∧ b' = p)) → 1 ≤ n → 1 ≤ n' →
    T₀ ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) →
    b ^ (n ^ 2) < b' ^ (n' ^ 2) →
    ((b' ^ (n' ^ 2) : ℕ) : ℝ) < Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) * ((b ^ (n ^ 2) : ℕ) : ℝ) →
    r ≠ 0 → |r| ≤ (⌈(Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 2⌉₊ : ℤ) →
    |s| ≤ (⌈4 * (Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 3⌉₊ : ℤ) → r * s < 0 →
    Real.exp (-(a (Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))))) / ((b ^ (n ^ 2) : ℕ) : ℝ) ≤
      nrm ((r : ℝ) / ((b ^ (n ^ 2) : ℕ) : ℝ) + (s : ℝ) / ((b' ^ (n' ^ 2) : ℕ) : ℝ))

/-- The two-term separation (opposite signs) with profile `a` for the pair `{p,q}`. -/
def TwoTermSepPair (p q : ℕ) (a : ℝ → ℝ) : Prop := ∃ T₀ : ℝ, SepBody a T₀ p q

lemma twoTermSep_iff (a : ℝ → ℝ) : TwoTermSep a ↔ TwoTermSepPair 2 3 a := Iff.rfl

/-- The elementary cases `r s ≥ 0`. -/
lemma sep_easy (a : ℝ → ℝ) (ha : ∀ t, 0 ≤ t → 0 ≤ a t) (b n b' n' : ℕ) (hbpos : 0 < b)
    (hT18 : 18 ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) (hQQ : b ^ (n ^ 2) < b' ^ (n' ^ 2))
    (r s : ℤ) (hr0 : r ≠ 0) (hrM : |r| ≤ (⌈(Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 2⌉₊ : ℤ))
    (hsN : |s| ≤ (⌈4 * (Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 3⌉₊ : ℤ)) (hneg : 0 ≤ r * s) :
    Real.exp (-(a (Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))))) / ((b ^ (n ^ 2) : ℕ) : ℝ) ≤
      nrm ((r : ℝ) / ((b ^ (n ^ 2) : ℕ) : ℝ) + (s : ℝ) / ((b' ^ (n' ^ 2) : ℕ) : ℝ)) := by
  set Q : ℝ := ((b ^ (n ^ 2) : ℕ) : ℝ) with hQdef
  set Q' : ℝ := ((b' ^ (n' ^ 2) : ℕ) : ℝ) with hQ'def
  set t : ℝ := Real.sqrt (Real.log Q) with htdef
  have hQpos : 0 < Q := by rw [hQdef]; exact_mod_cast pow_pos hbpos _
  have hQQ' : Q ≤ Q' := by rw [hQdef, hQ'def]; exact_mod_cast hQQ.le
  have hlog : 0 ≤ Real.log Q := by
    have : (0 : ℝ) < t := by linarith
    by_contra h; push Not at h
    have := Real.sqrt_eq_zero_of_nonpos h.le
    linarith
  have ht2 : t ^ 2 = Real.log Q := Real.sq_sqrt hlog
  have hrad := radii_le_exp t hT18
  have hexpQ : Real.exp (t ^ 2) = Q := by rw [ht2, Real.exp_log hQpos]
  rw [hexpQ] at hrad
  have hrM' : |(r : ℝ)| ≤ (⌈t ^ 2⌉₊ : ℝ) := by
    have h2 : ((|r| : ℤ) : ℝ) ≤ (((⌈t ^ 2⌉₊ : ℤ)) : ℝ) := by exact_mod_cast hrM
    rw [Int.cast_abs] at h2; simpa using h2
  have hsN' : |(s : ℝ)| ≤ (⌈4 * t ^ 3⌉₊ : ℝ) := by
    have h2 : ((|s| : ℤ) : ℝ) ≤ (((⌈4 * t ^ 3⌉₊ : ℤ)) : ℝ) := by exact_mod_cast hsN
    rw [Int.cast_abs] at h2; simpa using h2
  clear_value t Q Q'
  have heasy := two_term_easy Q Q' hQpos hQQ' (⌈t ^ 2⌉₊ : ℝ) (⌈4 * t ^ 3⌉₊ : ℝ) hrad r s hr0 hrM' hsN' hneg
  refine le_trans ?_ heasy
  have hexp1 : Real.exp (-(a t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ a t := ha t (by linarith)
    linarith
  exact div_le_div_of_nonneg_right hexp1 hQpos.le

/-- **`HTT3` from the three pair separations.** -/
theorem HTT3_exists (a : ℝ → ℝ) (ha : ∀ t, 0 ≤ t → 0 ≤ a t) (h23 : TwoTermSepPair 2 3 a)
    (h25 : TwoTermSepPair 2 5 a) (h35 : TwoTermSepPair 3 5 a) : ∃ T₁ : ℝ, DD3Assemble.HTT3 a T₁ := by
  obtain ⟨T₂₃, hp23⟩ := h23
  obtain ⟨T₂₅, hp25⟩ := h25
  obtain ⟨T₃₅, hp35⟩ := h35
  refine ⟨max (max (max T₂₃ T₂₅) T₃₅) 18, ?_⟩
  intro b n b' n' hb hb' hne hn hn' hT hQQ hclose r s hr0 hrM hsN
  have hTa : T₂₃ ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hT
  have hTb : T₂₅ ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hT
  have hTc : T₃₅ ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT18 : 18 ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) := le_trans (le_max_right _ _) hT
  by_cases hneg : r * s < 0
  · rcases hb with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact hp23 _ _ _ _ r s (Or.inl ⟨rfl, rfl⟩) hn hn' hTa hQQ hclose hr0 hrM hsN hneg
    · exact hp25 _ _ _ _ r s (Or.inl ⟨rfl, rfl⟩) hn hn' hTb hQQ hclose hr0 hrM hsN hneg
    · exact hp23 _ _ _ _ r s (Or.inr ⟨rfl, rfl⟩) hn hn' hTa hQQ hclose hr0 hrM hsN hneg
    · exact absurd rfl hne
    · exact hp35 _ _ _ _ r s (Or.inl ⟨rfl, rfl⟩) hn hn' hTc hQQ hclose hr0 hrM hsN hneg
    · exact hp25 _ _ _ _ r s (Or.inr ⟨rfl, rfl⟩) hn hn' hTb hQQ hclose hr0 hrM hsN hneg
    · exact hp35 _ _ _ _ r s (Or.inr ⟨rfl, rfl⟩) hn hn' hTc hQQ hclose hr0 hrM hsN hneg
    · exact absurd rfl hne
  · push Not at hneg
    have hbpos : 0 < b := by rcases hb with h | h | h <;> omega
    exact sep_easy a ha b n b' n' hbpos hT18 hQQ r s hr0 hrM hsN hneg

/-- **`DD {2,3,5}` from the three pair separations and the finiteness of bad triples**, for a window profile `a`. -/
theorem DD235_of_pairs (a : ℝ → ℝ) (ha : WindowProfile a) (hG : CloseGrowth a)
    (h23 : TwoTermSepPair 2 3 a) (h25 : TwoTermSepPair 2 5 a) (h35 : TwoTermSepPair 3 5 a)
    (K₁ : ℕ) (hH : DD3Assemble.HFin a K₁) : TVGPlus.DD ({2, 3, 5} : Finset ℕ) := by
  obtain ⟨T₁, htt⟩ := HTT3_exists a (fun t ht => ha.nonneg t ht) h23 h25 h35
  exact DD3Quotient.DD235_of_profile' a ha hG T₁ htt K₁ hH

/-- The same for the profile `A log²(2+t)`. -/
theorem DD235_of_pairs_A (A : ℝ) (hA : 0 ≤ A)
    (h23 : TwoTermSepPair 2 3 (fun t => A * (Real.log (2 + t)) ^ 2))
    (h25 : TwoTermSepPair 2 5 (fun t => A * (Real.log (2 + t)) ^ 2))
    (h35 : TwoTermSepPair 3 5 (fun t => A * (Real.log (2 + t)) ^ 2))
    (K₁ : ℕ) (hH : DD3Assemble.HFin (fun t => A * (Real.log (2 + t)) ^ 2) K₁) :
    TVGPlus.DD ({2, 3, 5} : Finset ℕ) :=
  DD235_of_pairs _ (JANonDeep.windowProfile_A A hA) (JAProductFinal.closeGrowth_A A hA) h23 h25 h35 K₁ hH

#print axioms sep_easy
#print axioms HTT3_exists
#print axioms DD235_of_pairs
#print axioms DD235_of_pairs_A

end DD3Sep
end LeanCheck
