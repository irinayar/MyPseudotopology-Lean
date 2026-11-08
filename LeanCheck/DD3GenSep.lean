import Mathlib
import LeanCheck.DD3GenQuotient
import LeanCheck.DD3Sep
import LeanCheck.JAClose

/-!
# Diagonal density for three primes, general exponent chains: `HTT3E` from the pair separations (Lean check)

Scope. `DD3Sep` for the scale sets `{p^(E p n)}`. `HTT3E E a T₁` is the two-term separation for ordered pairs of distinct bases
in `{2,3,5}` and all sign patterns; it is reduced to the opposite-sign case for each unordered pair:

* `SepBodyE E a T₀ p q` / `TwoTermSepPairE E p q a`: the opposite-sign two-term separation with profile `a` for the pair `{p,q}`
  and the scales `p^(E p n)`; for `E p n = n²` it is `DD3Sep.TwoTermSepPair` (`twoTermSepPairE_sq`);
* `sep_easyE`: the cases `r s ≥ 0` are elementary (only `0 < Q ≤ Q'` is used, as in `DD3Sep.sep_easy`);
* `HTT3E_exists`: `TwoTermSepPairE` for `{2,3}`, `{2,5}`, `{3,5}` (and `a ≥ 0`) give `HTT3E E a T₁` for some `T₁`;
* `DD235_of_pairsE`, `DD235_of_pairsE_A`: `DDS (scalesE E) {2,3,5}` from the three pair separations and the finiteness of bad
  triples `HFinE` alone, under `Mod3 E`.

The separations for the pairs are the external input (Matveev's bound for linear forms in two logarithms, hand argument in the
article); `HFinE` is the hypothesis `H(2,3,5)` of the note. A Lean proof verifies its formal statement under its hypotheses; the
correspondence with the research note requires mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open MixedPrime JAAssembly JAClose

/-- The opposite-sign separation for the pair `{p,q}` with threshold `T₀` and scales `p^(E p n)`. -/
def SepBodyE (E : ℕ → ℕ → ℕ) (a : ℝ → ℝ) (T₀ : ℝ) (p q : ℕ) : Prop :=
  ∀ (b n b' n' : ℕ) (r s : ℤ), ((b = p ∧ b' = q) ∨ (b = q ∧ b' = p)) → 1 ≤ n → 1 ≤ n' →
    T₀ ≤ Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ)) →
    b ^ (E b n) < b' ^ (E b' n') →
    ((b' ^ (E b' n') : ℕ) : ℝ) < Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ)) * ((b ^ (E b n) : ℕ) : ℝ) →
    r ≠ 0 → |r| ≤ (⌈(Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ))) ^ 2⌉₊ : ℤ) →
    |s| ≤ (⌈4 * (Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ))) ^ 3⌉₊ : ℤ) → r * s < 0 →
    Real.exp (-(a (Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ))))) / ((b ^ (E b n) : ℕ) : ℝ) ≤
      nrm ((r : ℝ) / ((b ^ (E b n) : ℕ) : ℝ) + (s : ℝ) / ((b' ^ (E b' n') : ℕ) : ℝ))

/-- The two-term separation (opposite signs) with profile `a` for the pair `{p,q}` and the scales `p^(E p n)`. -/
def TwoTermSepPairE (E : ℕ → ℕ → ℕ) (p q : ℕ) (a : ℝ → ℝ) : Prop := ∃ T₀ : ℝ, SepBodyE E a T₀ p q

/-- For the squares `E p n = n²` this is the pair separation of `DD3Sep`. -/
lemma twoTermSepPairE_sq (p q : ℕ) (a : ℝ → ℝ) :
    TwoTermSepPairE (fun _ k => k ^ 2) p q a ↔ DD3Sep.TwoTermSepPair p q a := Iff.rfl

/-- The elementary cases `r s ≥ 0`. -/
lemma sep_easyE (E : ℕ → ℕ → ℕ) (a : ℝ → ℝ) (ha : ∀ t, 0 ≤ t → 0 ≤ a t) (b n b' n' : ℕ) (hbpos : 0 < b)
    (hT18 : 18 ≤ Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ))) (hQQ : b ^ (E b n) < b' ^ (E b' n'))
    (r s : ℤ) (hr0 : r ≠ 0) (hrM : |r| ≤ (⌈(Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ))) ^ 2⌉₊ : ℤ))
    (hsN : |s| ≤ (⌈4 * (Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ))) ^ 3⌉₊ : ℤ)) (hneg : 0 ≤ r * s) :
    Real.exp (-(a (Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ))))) / ((b ^ (E b n) : ℕ) : ℝ) ≤
      nrm ((r : ℝ) / ((b ^ (E b n) : ℕ) : ℝ) + (s : ℝ) / ((b' ^ (E b' n') : ℕ) : ℝ)) := by
  set Q : ℝ := ((b ^ (E b n) : ℕ) : ℝ) with hQdef
  set Q' : ℝ := ((b' ^ (E b' n') : ℕ) : ℝ) with hQ'def
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

/-- **`HTT3E` from the three pair separations.** -/
theorem HTT3E_exists (E : ℕ → ℕ → ℕ) (a : ℝ → ℝ) (ha : ∀ t, 0 ≤ t → 0 ≤ a t)
    (h23 : TwoTermSepPairE E 2 3 a) (h25 : TwoTermSepPairE E 2 5 a) (h35 : TwoTermSepPairE E 3 5 a) :
    ∃ T₁ : ℝ, HTT3E E a T₁ := by
  obtain ⟨T₂₃, hp23⟩ := h23
  obtain ⟨T₂₅, hp25⟩ := h25
  obtain ⟨T₃₅, hp35⟩ := h35
  refine ⟨max (max (max T₂₃ T₂₅) T₃₅) 18, ?_⟩
  intro b n b' n' hb hb' hne hn hn' hT hQQ hclose r s hr0 hrM hsN
  have hTa : T₂₃ ≤ Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ)) :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hT
  have hTb : T₂₅ ≤ Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ)) :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hT
  have hTc : T₃₅ ≤ Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ)) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT18 : 18 ≤ Real.sqrt (Real.log ((b ^ (E b n) : ℕ) : ℝ)) := le_trans (le_max_right _ _) hT
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
    exact sep_easyE E a ha b n b' n' hbpos hT18 hQQ r s hr0 hrM hsN hneg

/-- **`DD {2,3,5}` for the scales `p^(E p n)` from the three pair separations and the finiteness of bad triples**, for a window
profile `a`. -/
theorem DD235_of_pairsE {Ex : ℕ → ℕ → ℕ} (hEx : Mod3 Ex) (a : ℝ → ℝ) (ha : WindowProfile a) (hG : CloseGrowth a)
    (h23 : TwoTermSepPairE Ex 2 3 a) (h25 : TwoTermSepPairE Ex 2 5 a) (h35 : TwoTermSepPairE Ex 3 5 a)
    (K₁ : ℕ) (hH : HFinE Ex a K₁) : DD3GenDense.DDS (scalesE Ex) ({2, 3, 5} : Finset ℕ) := by
  obtain ⟨T₁, htt⟩ := HTT3E_exists Ex a (fun t ht => ha.nonneg t ht) h23 h25 h35
  exact DD235_of_profileQ hEx a ha hG T₁ htt K₁ hH

/-- The same for the profile `A log²(2+t)`. -/
theorem DD235_of_pairsE_A {Ex : ℕ → ℕ → ℕ} (hEx : Mod3 Ex) (A : ℝ) (hA : 0 ≤ A)
    (h23 : TwoTermSepPairE Ex 2 3 (fun t => A * (Real.log (2 + t)) ^ 2))
    (h25 : TwoTermSepPairE Ex 2 5 (fun t => A * (Real.log (2 + t)) ^ 2))
    (h35 : TwoTermSepPairE Ex 3 5 (fun t => A * (Real.log (2 + t)) ^ 2))
    (K₁ : ℕ) (hH : HFinE Ex (fun t => A * (Real.log (2 + t)) ^ 2) K₁) :
    DD3GenDense.DDS (scalesE Ex) ({2, 3, 5} : Finset ℕ) :=
  DD235_of_pairsE hEx _ (JANonDeep.windowProfile_A A hA) (JAProductFinal.closeGrowth_A A hA) h23 h25 h35 K₁ hH

#print axioms twoTermSepPairE_sq
#print axioms sep_easyE
#print axioms HTT3E_exists
#print axioms DD235_of_pairsE
#print axioms DD235_of_pairsE_A

end DD3Gen
end LeanCheck
