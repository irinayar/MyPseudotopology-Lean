import Mathlib
import LeanCheck.DD3WeilZ2
import LeanCheck.DD3Final
import LeanCheck.JAOnePrime

/-!
# Diagonal density for three primes: the compact-quotient step, proved (Lean check)

Scope. Third part of the compact-quotient step for `ℤ²` in the Lean version of the conditional proof of `DD({2,3,5})`
(research note `TVGplus_conditional_DD235_2026-11-07.md`, item 7); the counterpart of `JAWeilE`. It removes the hypothesis
`DD3Dense.CompactQuotientCriterion3` from the final theorems of `DD3Final`.

* `Jsem` is the seminorm `J(u,v) = inf_k max (P₂(k+u), P₃(k), P₅(k-v))` on `ℤ × ℤ`; `Jfun_lt_iff`: `J w < ε ↔ w ∈ W3 ε`, where
  `W3 ε = {(x - y, y - z) : P₂(x), P₃(y), P₅(z) < ε}`;
* `compactQuotientCriterion3 : CompactQuotientCriterion3`: syndeticity of all `W3 ε` is precompactness of `J`;
  `DD3WeilZ2.weil_seminorm2` gives a `J`-continuous character `e(n₁ α + n₂ β)` nontrivial at a point not in `W3 ε`;
  `α` is `P₂`-continuous, `β` is `P₅`-continuous and `β - α` is `P₃`-continuous, so by the one-prime theorem
  `2^{a²} α, 5^{c²} β, 3^{b²}(β - α)` are integers, hence `α` and `β` are integers (the three prime powers are pairwise coprime)
  and the character is trivial, a contradiction;
* `DD235_of_inputs'`, `DD235_of_profile'`: `DD {2,3,5}` from `HTT3` and `HFin` alone.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Quotient

open MixedPrime JAAssembly

private lemma sq_ne' (ℓ : ℕ) : (sqScales ℓ).Nonempty := ⟨ℓ ^ (1 ^ 2), 1, le_rfl, rfl⟩

/-- `max (P₂ (k + u)) (max (P₃ k) (P₅ (k - v)))`. -/
noncomputable def fJ (w : ℤ × ℤ) (k : ℤ) : ℝ :=
  max (Pn (sqScales 2) (k + w.1)) (max (Pn (sqScales 3) k) (Pn (sqScales 5) (k - w.2)))

lemma fJ_nonneg (w : ℤ × ℤ) (k : ℤ) : 0 ≤ fJ w k := le_max_of_le_left (Pn_nonneg _ _)

lemma fJ_bdd (w : ℤ × ℤ) : BddBelow (Set.range (fJ w)) :=
  ⟨0, by rintro _ ⟨k, rfl⟩; exact fJ_nonneg w k⟩

/-- `J w = inf_k fJ w k`. -/
noncomputable def Jfun (w : ℤ × ℤ) : ℝ := ⨅ k : ℤ, fJ w k

lemma Jfun_nonneg (w : ℤ × ℤ) : 0 ≤ Jfun w := Real.iInf_nonneg (fJ_nonneg w)

lemma Jfun_le (w : ℤ × ℤ) (k : ℤ) : Jfun w ≤ fJ w k := ciInf_le (fJ_bdd w) k

lemma exists_lt_of_Jfun_lt {w : ℤ × ℤ} {ε : ℝ} (h : Jfun w < ε) : ∃ k, fJ w k < ε :=
  exists_lt_of_ciInf_lt h

lemma Jfun_zero : Jfun 0 = 0 := by
  apply le_antisymm _ (Jfun_nonneg 0)
  refine (Jfun_le 0 0).trans ?_
  simp [fJ, Pn_zero]

lemma Jfun_neg_le (w : ℤ × ℤ) : Jfun (-w) ≤ Jfun w := by
  refine le_ciInf (fun k => ?_)
  refine (Jfun_le (-w) (-k)).trans ?_
  have h1 : Pn (sqScales 2) (-k + (-w).1) = Pn (sqScales 2) (k + w.1) := by
    rw [show -k + (-w).1 = -(k + w.1) by simp only [Prod.fst_neg]; ring, Pn_neg]
  have h2 : Pn (sqScales 3) (-k) = Pn (sqScales 3) k := Pn_neg _ _
  have h3 : Pn (sqScales 5) (-k - (-w).2) = Pn (sqScales 5) (k - w.2) := by
    rw [show -k - (-w).2 = -(k - w.2) by simp only [Prod.snd_neg]; ring, Pn_neg]
  unfold fJ
  rw [h1, h2, h3]

lemma Jfun_add_le (a b : ℤ × ℤ) : Jfun (a + b) ≤ Jfun a + Jfun b := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨k₁, hk₁⟩ := exists_lt_of_Jfun_lt (show Jfun a < Jfun a + ε / 2 by linarith)
  obtain ⟨k₂, hk₂⟩ := exists_lt_of_Jfun_lt (show Jfun b < Jfun b + ε / 2 by linarith)
  have h2 : Pn (sqScales 2) (k₁ + k₂ + (a + b).1) ≤
      Pn (sqScales 2) (k₁ + a.1) + Pn (sqScales 2) (k₂ + b.1) := by
    have := Pn_add_le (sq_ne' 2) (k₁ + a.1) (k₂ + b.1)
    rwa [show k₁ + a.1 + (k₂ + b.1) = k₁ + k₂ + (a + b).1 by simp only [Prod.fst_add]; ring] at this
  have h3 : Pn (sqScales 3) (k₁ + k₂) ≤ Pn (sqScales 3) k₁ + Pn (sqScales 3) k₂ :=
    Pn_add_le (sq_ne' 3) k₁ k₂
  have h5 : Pn (sqScales 5) (k₁ + k₂ - (a + b).2) ≤
      Pn (sqScales 5) (k₁ - a.2) + Pn (sqScales 5) (k₂ - b.2) := by
    have := Pn_add_le (sq_ne' 5) (k₁ - a.2) (k₂ - b.2)
    rwa [show k₁ - a.2 + (k₂ - b.2) = k₁ + k₂ - (a + b).2 by simp only [Prod.snd_add]; ring] at this
  have e1 : Pn (sqScales 2) (k₁ + a.1) ≤ fJ a k₁ := le_max_left _ _
  have e2 : Pn (sqScales 3) k₁ ≤ fJ a k₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have e3 : Pn (sqScales 5) (k₁ - a.2) ≤ fJ a k₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  have f1 : Pn (sqScales 2) (k₂ + b.1) ≤ fJ b k₂ := le_max_left _ _
  have f2 : Pn (sqScales 3) k₂ ≤ fJ b k₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have f3 : Pn (sqScales 5) (k₂ - b.2) ≤ fJ b k₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have : fJ (a + b) (k₁ + k₂) ≤ fJ a k₁ + fJ b k₂ := by
    unfold fJ at *
    apply max_le
    · linarith
    · apply max_le <;> linarith
  linarith [Jfun_le (a + b) (k₁ + k₂)]

/-- The seminorm `J` on `ℤ × ℤ`. -/
noncomputable def Jsem : AddGroupSeminorm (ℤ × ℤ) where
  toFun := Jfun
  map_zero' := Jfun_zero
  add_le' := Jfun_add_le
  neg' := fun w => le_antisymm (Jfun_neg_le w) (by simpa using Jfun_neg_le (-w))

lemma Jsem_apply (w : ℤ × ℤ) : Jsem w = Jfun w := rfl

/-- `J w < ε` iff `w ∈ W3 ε`. -/
lemma Jfun_lt_iff (w : ℤ × ℤ) (ε : ℝ) : Jfun w < ε ↔ w ∈ DD3Dense.W3 ε := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_lt_of_Jfun_lt h
    refine ⟨k + w.1, ?_, k, ?_, k - w.2, ?_, ?_⟩
    · exact lt_of_le_of_lt (le_max_left _ _) hk
    · exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hk
    · exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hk
    · ext <;> simp
  · rintro ⟨x, hx, y, hy, z, hz, rfl⟩
    refine lt_of_le_of_lt (Jfun_le _ y) ?_
    have e1 : y + (x - y, y - z).1 = x := by simp
    have e2 : y - (x - y, y - z).2 = z := by simp
    unfold fJ
    rw [e1, e2]
    exact max_lt hx (max_lt hy hz)

/-- Integrality from the three one-prime conditions. -/
lemma integral_of_three (A B C : ℕ) (hA : IsCoprime (A : ℤ) ((B : ℤ) * C)) (hC : IsCoprime (C : ℤ) ((A : ℤ) * B))
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

/-- **The compact-quotient criterion for `ℤ²`** (`SyndeticW3 → JA3Prop`), proved from Weil's theorem for two generators and
the one-prime theorem. -/
theorem compactQuotientCriterion3 : DD3Dense.CompactQuotientCriterion3 := by
  intro hS
  by_contra hJA
  unfold DD3Dense.JA3Prop at hJA
  push Not at hJA
  obtain ⟨ε, hε, w, hw⟩ := hJA
  have hJw : ε ≤ Jfun w := by
    by_contra h
    exact hw ((Jfun_lt_iff w ε).mp (not_le.mp h))
  have hF : ∀ ε' > 0, ∃ F : Finset (ℤ × ℤ), ∀ z : ℤ × ℤ, ∃ f ∈ F, Jsem (z - f) < ε' := by
    intro ε' hε'
    obtain ⟨F, hF⟩ := hS ε' hε'
    refine ⟨F, fun z => ?_⟩
    obtain ⟨f, hf, hzf⟩ := hF z
    exact ⟨f, hf, (Jfun_lt_iff _ _).mpr hzf⟩
  obtain ⟨α, β, hcont, hpos⟩ := DD3WeilZ2.weil_seminorm2 Jsem hF w (lt_of_lt_of_le hε hJw)
  obtain ⟨δ', hδ', hδ''⟩ := hcont (1 / 4) (by norm_num)
  -- `α` is `P₂`-continuous
  have h₂ : ∀ k : ℤ, Pn (sqScales 2) k < δ' → nrm ((k : ℝ) * α) < 1 / 4 := by
    intro k hk
    have h := hδ'' (k, 0) (by
      show Jfun (k, 0) < δ'
      refine lt_of_le_of_lt (Jfun_le (k, 0) 0) ?_
      simp only [fJ, zero_add, sub_zero, Pn_zero]
      exact max_lt hk (max_lt hδ' hδ'))
    simpa using h
  -- `β` is `P₅`-continuous
  have h₅ : ∀ k : ℤ, Pn (sqScales 5) k < δ' → nrm ((k : ℝ) * β) < 1 / 4 := by
    intro k hk
    have h := hδ'' (0, -k) (by
      show Jfun (0, -k) < δ'
      refine lt_of_le_of_lt (Jfun_le (0, -k) 0) ?_
      simp only [fJ, zero_add, zero_sub, neg_neg, Pn_zero]
      exact max_lt hδ' (max_lt hδ' hk))
    have e : ((0 : ℤ) : ℝ) * α + ((-k : ℤ) : ℝ) * β = -((k : ℝ) * β) := by push_cast; ring
    simp only at h
    rw [e, nrm_neg] at h
    exact h
  -- `β - α` is `P₃`-continuous
  have h₃ : ∀ k : ℤ, Pn (sqScales 3) k < δ' → nrm ((k : ℝ) * (β - α)) < 1 / 4 := by
    intro k hk
    have h := hδ'' (-k, k) (by
      show Jfun (-k, k) < δ'
      refine lt_of_le_of_lt (Jfun_le (-k, k) k) ?_
      simp only [fJ, add_neg_cancel, sub_self, Pn_zero]
      exact max_lt hδ' (max_lt hk hδ'))
    have e : ((-k : ℤ) : ℝ) * α + (k : ℝ) * β = (k : ℝ) * (β - α) := by push_cast; ring
    simp only at h
    rw [e] at h
    exact h
  obtain ⟨a, z₂, hz₂⟩ := JAOnePrime.oneprime 2 le_rfl α δ' hδ' h₂
  obtain ⟨b, z₃, hz₃⟩ := JAOnePrime.oneprime 3 (by norm_num) (β - α) δ' hδ' h₃
  obtain ⟨c, z₅, hz₅⟩ := JAOnePrime.oneprime 5 (by norm_num) β δ' hδ' h₅
  have c23 : IsCoprime (2 : ℤ) 3 := ⟨-1, 1, by norm_num⟩
  have c25 : IsCoprime (2 : ℤ) 5 := ⟨-2, 1, by norm_num⟩
  have c35 : IsCoprime (3 : ℤ) 5 := ⟨2, -1, by norm_num⟩
  have hA : IsCoprime (((2 ^ (a ^ 2) : ℕ)) : ℤ) (((3 ^ (b ^ 2) : ℕ) : ℤ) * ((5 ^ (c ^ 2) : ℕ) : ℤ)) := by
    push_cast
    exact IsCoprime.mul_right (IsCoprime.pow c23) (IsCoprime.pow c25)
  have hC : IsCoprime (((5 ^ (c ^ 2) : ℕ)) : ℤ) (((2 ^ (a ^ 2) : ℕ) : ℤ) * ((3 ^ (b ^ 2) : ℕ) : ℤ)) := by
    push_cast
    exact IsCoprime.mul_right (IsCoprime.pow c25.symm) (IsCoprime.pow c35.symm)
  have hA0 : (((2 ^ (a ^ 2) : ℕ)) : ℝ) ≠ 0 := by positivity
  have hC0 : (((5 ^ (c ^ 2) : ℕ)) : ℝ) ≠ 0 := by positivity
  obtain ⟨⟨t, ht⟩, ⟨s, hs⟩⟩ := integral_of_three (2 ^ (a ^ 2)) (3 ^ (b ^ 2)) (5 ^ (c ^ 2)) hA hC hA0 hC0 α β z₂ z₃ z₅
    (by push_cast; exact hz₂) (by push_cast; exact hz₃) (by push_cast; exact hz₅)
  have hint : (w.1 : ℝ) * α + (w.2 : ℝ) * β = ((w.1 * t + w.2 * s : ℤ) : ℝ) := by
    rw [ht, hs]; push_cast; ring
  rw [hint, nrm_int] at hpos
  exact lt_irrefl _ hpos

/-- **`DD {2,3,5}` for a general separation profile `a`**, with the compact-quotient step proved. -/
theorem DD235_of_profile' (a : ℝ → ℝ) (ha : WindowProfile a)
    (hG : CloseGrowth a) (T₁ : ℝ) (htt : DD3Assemble.HTT3 a T₁) (K₁ : ℕ) (hH : DD3Assemble.HFin a K₁) :
    TVGPlus.DD ({2, 3, 5} : Finset ℕ) :=
  DD3Final.DD235_of_profile compactQuotientCriterion3 a ha hG T₁ htt K₁ hH

/-- **`DD {2,3,5}` from the two-term separations and the finiteness of bad triples alone**, for the profile `A log²(2+t)`. -/
theorem DD235_of_inputs' (A : ℝ) (hA : 0 ≤ A) (T₁ : ℝ) (K₁ : ℕ)
    (htt : DD3Assemble.HTT3 (fun t => A * (Real.log (2 + t)) ^ 2) T₁)
    (hH : DD3Assemble.HFin (fun t => A * (Real.log (2 + t)) ^ 2) K₁) :
    TVGPlus.DD ({2, 3, 5} : Finset ℕ) :=
  DD3Final.DD235_of_inputs compactQuotientCriterion3 A hA T₁ K₁ htt hH

#print axioms Jfun_lt_iff
#print axioms integral_of_three
#print axioms compactQuotientCriterion3
#print axioms DD235_of_profile'
#print axioms DD235_of_inputs'

end DD3Quotient
end LeanCheck
