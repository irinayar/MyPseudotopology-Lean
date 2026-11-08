import Mathlib
import LeanCheck.DD3WeilZ2
import LeanCheck.DD3GenFinal
import LeanCheck.DD3GenOnePrime

/-!
# Diagonal density for three primes, general exponent chains: the compact-quotient step, proved (Lean check)

Scope. The compact-quotient step for `ℤ²` for the scale sets `{p^(E p n)}`, `p ∈ {2,3,5}` (`scalesE E p`), under the gap
hypothesis `OK3 E`; this is `DD3Quotient` with the squares `p^(n²)` replaced by `p^(E p n)` and the one-prime theorem by
`DD3Gen.oneprimeE`. It removes the hypothesis `DD3GenDense.CompactQuotientCriterion3 (scalesE E)` from the final theorems of
`DD3GenFinal`.

* `JsemE E` is the seminorm `J(u,v) = inf_k max (P₂(k+u), P₃(k), P₅(k-v))` on `ℤ × ℤ` (with `P_p` the pseudo-norm of the scale
  set `scalesE E p`); `JfunE_lt_iff`: `J w < ε ↔ w ∈ W3 ε`;
* `compactQuotientCriterion3E : OK3 E → CompactQuotientCriterion3 (scalesE E)`: `DD3WeilZ2.weil_seminorm2` gives a
  `J`-continuous character `e(n₁ α + n₂ β)` nontrivial at a point not in `W3 ε`; `α` is `P₂`-continuous, `β` is `P₅`-continuous
  and `β - α` is `P₃`-continuous, so by `oneprimeE` the numbers `2^(E 2 a) α`, `5^(E 5 c) β`, `3^(E 3 b) (β - α)` are integers,
  hence `α` and `β` are integers (the three prime powers are pairwise coprime) and the character is trivial, a contradiction;
* `DD235_of_profileQ`, `DD235_of_inputsQ`: `DDS (scalesE E) {2,3,5}` from `HTT3E` and `HFinE` alone, under `Mod3 E`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open MixedPrime JAAssembly DD3Sorted

section Quot

variable (E : ℕ → ℕ → ℕ)

lemma scalesE_ne (ℓ : ℕ) : (scalesE E ℓ).Nonempty := ⟨ℓ ^ (E ℓ 1), 1, le_rfl, rfl⟩

/-- `max (P₂ (k + u)) (max (P₃ k) (P₅ (k - v)))`. -/
noncomputable def fJE (w : ℤ × ℤ) (k : ℤ) : ℝ :=
  max (Pn (scalesE E 2) (k + w.1)) (max (Pn (scalesE E 3) k) (Pn (scalesE E 5) (k - w.2)))

lemma fJE_nonneg (w : ℤ × ℤ) (k : ℤ) : 0 ≤ fJE E w k := le_max_of_le_left (Pn_nonneg _ _)

lemma fJE_bdd (w : ℤ × ℤ) : BddBelow (Set.range (fJE E w)) :=
  ⟨0, by rintro _ ⟨k, rfl⟩; exact fJE_nonneg E w k⟩

/-- `J w = inf_k fJE w k`. -/
noncomputable def JfunE (w : ℤ × ℤ) : ℝ := ⨅ k : ℤ, fJE E w k

lemma JfunE_nonneg (w : ℤ × ℤ) : 0 ≤ JfunE E w := Real.iInf_nonneg (fJE_nonneg E w)

lemma JfunE_le (w : ℤ × ℤ) (k : ℤ) : JfunE E w ≤ fJE E w k := ciInf_le (fJE_bdd E w) k

lemma exists_lt_of_JfunE_lt {w : ℤ × ℤ} {ε : ℝ} (h : JfunE E w < ε) : ∃ k, fJE E w k < ε :=
  exists_lt_of_ciInf_lt h

lemma JfunE_zero : JfunE E 0 = 0 := by
  apply le_antisymm _ (JfunE_nonneg E 0)
  refine (JfunE_le E 0 0).trans ?_
  simp [fJE, Pn_zero]

lemma JfunE_neg_le (w : ℤ × ℤ) : JfunE E (-w) ≤ JfunE E w := by
  refine le_ciInf (fun k => ?_)
  refine (JfunE_le E (-w) (-k)).trans ?_
  have h1 : Pn (scalesE E 2) (-k + (-w).1) = Pn (scalesE E 2) (k + w.1) := by
    rw [show -k + (-w).1 = -(k + w.1) by simp only [Prod.fst_neg]; ring, Pn_neg]
  have h2 : Pn (scalesE E 3) (-k) = Pn (scalesE E 3) k := Pn_neg _ _
  have h3 : Pn (scalesE E 5) (-k - (-w).2) = Pn (scalesE E 5) (k - w.2) := by
    rw [show -k - (-w).2 = -(k - w.2) by simp only [Prod.snd_neg]; ring, Pn_neg]
  unfold fJE
  rw [h1, h2, h3]

lemma JfunE_add_le (a b : ℤ × ℤ) : JfunE E (a + b) ≤ JfunE E a + JfunE E b := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨k₁, hk₁⟩ := exists_lt_of_JfunE_lt E (show JfunE E a < JfunE E a + ε / 2 by linarith)
  obtain ⟨k₂, hk₂⟩ := exists_lt_of_JfunE_lt E (show JfunE E b < JfunE E b + ε / 2 by linarith)
  have h2 : Pn (scalesE E 2) (k₁ + k₂ + (a + b).1) ≤
      Pn (scalesE E 2) (k₁ + a.1) + Pn (scalesE E 2) (k₂ + b.1) := by
    have := Pn_add_le (scalesE_ne E 2) (k₁ + a.1) (k₂ + b.1)
    rwa [show k₁ + a.1 + (k₂ + b.1) = k₁ + k₂ + (a + b).1 by simp only [Prod.fst_add]; ring] at this
  have h3 : Pn (scalesE E 3) (k₁ + k₂) ≤ Pn (scalesE E 3) k₁ + Pn (scalesE E 3) k₂ :=
    Pn_add_le (scalesE_ne E 3) k₁ k₂
  have h5 : Pn (scalesE E 5) (k₁ + k₂ - (a + b).2) ≤
      Pn (scalesE E 5) (k₁ - a.2) + Pn (scalesE E 5) (k₂ - b.2) := by
    have := Pn_add_le (scalesE_ne E 5) (k₁ - a.2) (k₂ - b.2)
    rwa [show k₁ - a.2 + (k₂ - b.2) = k₁ + k₂ - (a + b).2 by simp only [Prod.snd_add]; ring] at this
  have e1 : Pn (scalesE E 2) (k₁ + a.1) ≤ fJE E a k₁ := le_max_left _ _
  have e2 : Pn (scalesE E 3) k₁ ≤ fJE E a k₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have e3 : Pn (scalesE E 5) (k₁ - a.2) ≤ fJE E a k₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  have f1 : Pn (scalesE E 2) (k₂ + b.1) ≤ fJE E b k₂ := le_max_left _ _
  have f2 : Pn (scalesE E 3) k₂ ≤ fJE E b k₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have f3 : Pn (scalesE E 5) (k₂ - b.2) ≤ fJE E b k₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have : fJE E (a + b) (k₁ + k₂) ≤ fJE E a k₁ + fJE E b k₂ := by
    unfold fJE at *
    apply max_le
    · linarith
    · apply max_le <;> linarith
  linarith [JfunE_le E (a + b) (k₁ + k₂)]

/-- The seminorm `J` on `ℤ × ℤ`. -/
noncomputable def JsemE : AddGroupSeminorm (ℤ × ℤ) where
  toFun := JfunE E
  map_zero' := JfunE_zero E
  add_le' := JfunE_add_le E
  neg' := fun w => le_antisymm (JfunE_neg_le E w) (by simpa using JfunE_neg_le E (-w))

lemma JsemE_apply (w : ℤ × ℤ) : JsemE E w = JfunE E w := rfl

/-- `J w < ε` iff `w ∈ W3 ε`. -/
lemma JfunE_lt_iff (w : ℤ × ℤ) (ε : ℝ) : JfunE E w < ε ↔ w ∈ DD3GenDense.W3 (scalesE E) ε := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_lt_of_JfunE_lt E h
    refine ⟨k + w.1, ?_, k, ?_, k - w.2, ?_, ?_⟩
    · exact lt_of_le_of_lt (le_max_left _ _) hk
    · exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hk
    · exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hk
    · ext <;> simp
  · rintro ⟨x, hx, y, hy, z, hz, rfl⟩
    refine lt_of_le_of_lt (JfunE_le E _ y) ?_
    have e1 : y + (x - y, y - z).1 = x := by simp
    have e2 : y - (x - y, y - z).2 = z := by simp
    unfold fJE
    rw [e1, e2]
    exact max_lt hx (max_lt hy hz)

/-- Integrality from the three one-prime conditions. -/
lemma integral_of_threeE (A B C : ℕ) (hA : IsCoprime (A : ℤ) ((B : ℤ) * C)) (hC : IsCoprime (C : ℤ) ((A : ℤ) * B))
    (hA0 : (A : ℝ) ≠ 0) (hC0 : (C : ℝ) ≠ 0) (α β : ℝ) (z₂ z₃ z₅ : ℤ) (h2 : (A : ℝ) * α = z₂)
    (h3 : (B : ℝ) * (β - α) = z₃) (h5 : (C : ℝ) * β = z₅) :
    (∃ t : ℤ, α = t) ∧ ∃ s : ℤ, β = s := by
  have key : (B : ℤ) * A * z₅ - (B : ℤ) * C * z₂ = (A : ℤ) * C * z₃ := by
    have : ((B : ℝ) * A * z₅ - (B : ℝ) * C * z₂) = (A : ℝ) * C * z₃ := by
      rw [← h2, ← h3, ← h5]; ring
    exact_mod_cast this
  constructor
  · have hd : (A : ℤ) ∣ (B : ℤ) * C * z₂ := ⟨(B : ℤ) * z₅ - (C : ℤ) * z₃, by linear_combination -key⟩
    have hd2 : (A : ℤ) ∣ z₂ := by
      have := hA.dvd_of_dvd_mul_left (show (A : ℤ) ∣ ((B : ℤ) * C) * z₂ from hd)
      exact this
    obtain ⟨t, ht⟩ := hd2
    refine ⟨t, ?_⟩
    have : (A : ℝ) * α = (A : ℝ) * t := by rw [h2, ht]; push_cast; ring
    exact mul_left_cancel₀ hA0 this
  · have hd : (C : ℤ) ∣ (A : ℤ) * B * z₅ := ⟨(A : ℤ) * z₃ + (B : ℤ) * z₂, by linear_combination key⟩
    have hd2 : (C : ℤ) ∣ z₅ := hC.dvd_of_dvd_mul_left (show (C : ℤ) ∣ ((A : ℤ) * B) * z₅ from hd)
    obtain ⟨s, hs⟩ := hd2
    refine ⟨s, ?_⟩
    have : (C : ℝ) * β = (C : ℝ) * s := by rw [h5, hs]; push_cast; ring
    exact mul_left_cancel₀ hC0 this

/-- **The compact-quotient criterion for `ℤ²` and the scale sets `scalesE E`** (`SyndeticW3 → JA3Prop`), proved from Weil's
theorem for two generators and the one-prime theorem for general exponents. -/
theorem compactQuotientCriterion3E (hE : OK3 E) : DD3GenDense.CompactQuotientCriterion3 (scalesE E) := by
  intro hS
  by_contra hJA
  unfold DD3GenDense.JA3Prop at hJA
  push Not at hJA
  obtain ⟨ε, hε, w, hw⟩ := hJA
  have hJw : ε ≤ JfunE E w := by
    by_contra h
    exact hw ((JfunE_lt_iff E w ε).mp (not_le.mp h))
  have hF : ∀ ε' > 0, ∃ F : Finset (ℤ × ℤ), ∀ z : ℤ × ℤ, ∃ f ∈ F, JsemE E (z - f) < ε' := by
    intro ε' hε'
    obtain ⟨F, hF⟩ := hS ε' hε'
    refine ⟨F, fun z => ?_⟩
    obtain ⟨f, hf, hzf⟩ := hF z
    exact ⟨f, hf, (JfunE_lt_iff E _ _).mpr hzf⟩
  obtain ⟨α, β, hcont, hpos⟩ := DD3WeilZ2.weil_seminorm2 (JsemE E) hF w (lt_of_lt_of_le hε hJw)
  obtain ⟨δ', hδ', hδ''⟩ := hcont (1 / 4) (by norm_num)
  -- `α` is `P₂`-continuous
  have h₂ : ∀ k : ℤ, Pn (scalesE E 2) k < δ' → nrm ((k : ℝ) * α) < 1 / 4 := by
    intro k hk
    have h := hδ'' (k, 0) (by
      show JfunE E (k, 0) < δ'
      refine lt_of_le_of_lt (JfunE_le E (k, 0) 0) ?_
      simp only [fJE, zero_add, sub_zero, Pn_zero]
      exact max_lt hk (max_lt hδ' hδ'))
    simpa using h
  -- `β` is `P₅`-continuous
  have h₅ : ∀ k : ℤ, Pn (scalesE E 5) k < δ' → nrm ((k : ℝ) * β) < 1 / 4 := by
    intro k hk
    have h := hδ'' (0, -k) (by
      show JfunE E (0, -k) < δ'
      refine lt_of_le_of_lt (JfunE_le E (0, -k) 0) ?_
      simp only [fJE, zero_add, zero_sub, neg_neg, Pn_zero]
      exact max_lt hδ' (max_lt hδ' hk))
    have e : ((0 : ℤ) : ℝ) * α + ((-k : ℤ) : ℝ) * β = -((k : ℝ) * β) := by push_cast; ring
    simp only at h
    rw [e, nrm_neg] at h
    exact h
  -- `β - α` is `P₃`-continuous
  have h₃ : ∀ k : ℤ, Pn (scalesE E 3) k < δ' → nrm ((k : ℝ) * (β - α)) < 1 / 4 := by
    intro k hk
    have h := hδ'' (-k, k) (by
      show JfunE E (-k, k) < δ'
      refine lt_of_le_of_lt (JfunE_le E (-k, k) k) ?_
      simp only [fJE, add_neg_cancel, sub_self, Pn_zero]
      exact max_lt hδ' (max_lt hk hδ'))
    have e : ((-k : ℤ) : ℝ) * α + (k : ℝ) * β = (k : ℝ) * (β - α) := by push_cast; ring
    simp only at h
    rw [e] at h
    exact h
  have o2 := hE 2 (Or.inl rfl)
  have o3 := hE 3 (Or.inr (Or.inl rfl))
  have o5 := hE 5 (Or.inr (Or.inr rfl))
  obtain ⟨a, z₂, hz₂⟩ := oneprimeE E 2 le_rfl o2.1 o2.2 α δ' hδ' h₂
  obtain ⟨b, z₃, hz₃⟩ := oneprimeE E 3 (by norm_num) o3.1 o3.2 (β - α) δ' hδ' h₃
  obtain ⟨c, z₅, hz₅⟩ := oneprimeE E 5 (by norm_num) o5.1 o5.2 β δ' hδ' h₅
  have c23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
  have c25 : IsCoprime (2 : ℤ) 5 := ⟨-2, 1, by norm_num⟩
  have c35 : IsCoprime (3 : ℤ) 5 := ⟨2, -1, by norm_num⟩
  have hA : IsCoprime (((2 ^ (E 2 a) : ℕ)) : ℤ) (((3 ^ (E 3 b) : ℕ) : ℤ) * ((5 ^ (E 5 c) : ℕ) : ℤ)) := by
    push_cast
    exact IsCoprime.mul_right (IsCoprime.pow c23) (IsCoprime.pow c25)
  have hC : IsCoprime (((5 ^ (E 5 c) : ℕ)) : ℤ) (((2 ^ (E 2 a) : ℕ) : ℤ) * ((3 ^ (E 3 b) : ℕ) : ℤ)) := by
    push_cast
    exact IsCoprime.mul_right (IsCoprime.pow c25.symm) (IsCoprime.pow c35.symm)
  have hA0 : (((2 ^ (E 2 a) : ℕ)) : ℝ) ≠ 0 := by positivity
  have hC0 : (((5 ^ (E 5 c) : ℕ)) : ℝ) ≠ 0 := by positivity
  obtain ⟨⟨t, ht⟩, ⟨s, hs⟩⟩ := integral_of_threeE (2 ^ (E 2 a)) (3 ^ (E 3 b)) (5 ^ (E 5 c)) hA hC hA0 hC0 α β z₂ z₃ z₅
    (by push_cast; exact hz₂) (by push_cast; exact hz₃) (by push_cast; exact hz₅)
  have hint : (w.1 : ℝ) * α + (w.2 : ℝ) * β = ((w.1 * t + w.2 * s : ℤ) : ℝ) := by
    rw [ht, hs]; push_cast; ring
  rw [hint, nrm_int] at hpos
  exact lt_irrefl _ hpos

/-- **`DD {2,3,5}` for scale sets `p^(E p n)` and a general separation profile `a`**, with the compact-quotient step proved. -/
theorem DD235_of_profileQ {Ex : ℕ → ℕ → ℕ} (hEx : Mod3 Ex) (a : ℝ → ℝ) (ha : WindowProfile a)
    (hG : CloseGrowth a) (T₁ : ℝ) (htt : HTT3E Ex a T₁) (K₁ : ℕ) (hH : HFinE Ex a K₁) :
    DD3GenDense.DDS (scalesE Ex) ({2, 3, 5} : Finset ℕ) :=
  DD235_of_profile hEx (compactQuotientCriterion3E Ex hEx.ok) a ha hG T₁ htt K₁ hH

/-- **`DD {2,3,5}` for the scale sets `p^(E p n)` from the two-term separations and the finiteness of bad triples alone**, for
the profile `A log²(2+t)`. -/
theorem DD235_of_inputsQ {Ex : ℕ → ℕ → ℕ} (hEx : Mod3 Ex) (A : ℝ) (hA : 0 ≤ A) (T₁ : ℝ) (K₁ : ℕ)
    (htt : HTT3E Ex (fun t => A * (Real.log (2 + t)) ^ 2) T₁)
    (hH : HFinE Ex (fun t => A * (Real.log (2 + t)) ^ 2) K₁) :
    DD3GenDense.DDS (scalesE Ex) ({2, 3, 5} : Finset ℕ) :=
  DD235_of_inputs hEx (compactQuotientCriterion3E Ex hEx.ok) A hA T₁ K₁ htt hH

end Quot

#print axioms JfunE_lt_iff
#print axioms integral_of_threeE
#print axioms compactQuotientCriterion3E
#print axioms DD235_of_profileQ
#print axioms DD235_of_inputsQ

end DD3Gen
end LeanCheck
