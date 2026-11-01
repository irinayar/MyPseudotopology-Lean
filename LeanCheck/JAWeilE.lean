import Mathlib
import LeanCheck.JAWeilD
import LeanCheck.JAOnePrime
import LeanCheck.JAMain

/-!
# The compact-quotient criterion, proved

`Jsem` is the seminorm `J_m = inf_k max (P_2 (k - m)) (P_3 k)` on `ℤ`; `{J < ε} = W_ε = U_{3,ε} - U_{2,ε}`.  Syndeticity of all `W_ε` is
precompactness of `J`; `weil_seminorm` gives a `J`-continuous character nontrivial at `1` if `J 1 > 0`; such a character is continuous
for `P_3` (take `n = k`) and `P_2` (take `n = -k`), hence an integer by `oneprime_two_three`, a contradiction.

`compactQuotientCriterion : CompactQuotientCriterion` and `JA_of_matveev : TwoTermSeparation A → JAProp`.
-/

namespace LeanCheck
namespace JAWeil

open MixedPrime JAAssembly

private lemma sq_ne' (ℓ : ℕ) : (sqScales ℓ).Nonempty := ⟨ℓ ^ (1 ^ 2), 1, le_rfl, rfl⟩

private lemma Pn_le_half (ℓ : ℕ) (k : ℤ) : Pn (sqScales ℓ) k ≤ 1 / 2 :=
  Pn_le (sq_ne' ℓ) (fun q _ => nrm_le_half _)

/-- `max (P_2 (k - m)) (P_3 k)`. -/
noncomputable def fJ (m k : ℤ) : ℝ := max (Pn (sqScales 2) (k - m)) (Pn (sqScales 3) k)

lemma fJ_nonneg (m k : ℤ) : 0 ≤ fJ m k := le_max_of_le_left (Pn_nonneg _ _)

lemma fJ_bdd (m : ℤ) : BddBelow (Set.range (fJ m)) := ⟨0, by rintro _ ⟨k, rfl⟩; exact fJ_nonneg m k⟩

/-- `J m = inf_k max (P_2 (k - m)) (P_3 k)`. -/
noncomputable def Jfun (m : ℤ) : ℝ := ⨅ k : ℤ, fJ m k

lemma Jfun_nonneg (m : ℤ) : 0 ≤ Jfun m := Real.iInf_nonneg (fJ_nonneg m)

lemma Jfun_le (m k : ℤ) : Jfun m ≤ fJ m k := ciInf_le (fJ_bdd m) k

lemma exists_lt_of_Jfun_lt {m : ℤ} {ε : ℝ} (h : Jfun m < ε) : ∃ k, fJ m k < ε :=
  exists_lt_of_ciInf_lt h

lemma Jfun_zero : Jfun 0 = 0 := by
  apply le_antisymm _ (Jfun_nonneg 0)
  refine (Jfun_le 0 0).trans ?_
  simp [fJ, Pn_zero]

lemma Jfun_neg_le (m : ℤ) : Jfun (-m) ≤ Jfun m := by
  refine le_ciInf (fun k => ?_)
  refine (Jfun_le (-m) (-k)).trans ?_
  have h1 : Pn (sqScales 2) (-k - -m) = Pn (sqScales 2) (k - m) := by
    rw [show -k - -m = -(k - m) by ring, Pn_neg]
  have h2 : Pn (sqScales 3) (-k) = Pn (sqScales 3) k := Pn_neg _ _
  unfold fJ
  rw [h1, h2]

lemma Jfun_add_le (a b : ℤ) : Jfun (a + b) ≤ Jfun a + Jfun b := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨k₁, hk₁⟩ := exists_lt_of_Jfun_lt (show Jfun a < Jfun a + ε / 2 by linarith)
  obtain ⟨k₂, hk₂⟩ := exists_lt_of_Jfun_lt (show Jfun b < Jfun b + ε / 2 by linarith)
  have h2 : Pn (sqScales 2) (k₁ + k₂ - (a + b)) ≤ Pn (sqScales 2) (k₁ - a) + Pn (sqScales 2) (k₂ - b) := by
    have := Pn_add_le (sq_ne' 2) (k₁ - a) (k₂ - b)
    rwa [show k₁ - a + (k₂ - b) = k₁ + k₂ - (a + b) by ring] at this
  have h3 : Pn (sqScales 3) (k₁ + k₂) ≤ Pn (sqScales 3) k₁ + Pn (sqScales 3) k₂ :=
    Pn_add_le (sq_ne' 3) k₁ k₂
  have e1 : Pn (sqScales 2) (k₁ - a) ≤ fJ a k₁ := le_max_left _ _
  have e2 : Pn (sqScales 3) k₁ ≤ fJ a k₁ := le_max_right _ _
  have e3 : Pn (sqScales 2) (k₂ - b) ≤ fJ b k₂ := le_max_left _ _
  have e4 : Pn (sqScales 3) k₂ ≤ fJ b k₂ := le_max_right _ _
  have : fJ (a + b) (k₁ + k₂) ≤ fJ a k₁ + fJ b k₂ := by
    apply max_le <;> linarith
  linarith [Jfun_le (a + b) (k₁ + k₂)]

/-- The seminorm `J` on `ℤ`. -/
noncomputable def Jsem : AddGroupSeminorm ℤ where
  toFun := Jfun
  map_zero' := Jfun_zero
  add_le' := Jfun_add_le
  neg' := fun m => le_antisymm (Jfun_neg_le m) (by simpa using Jfun_neg_le (-m))

lemma Jsem_apply (m : ℤ) : Jsem m = Jfun m := rfl

/-- `J m < ε` iff `m ∈ W_ε`. -/
lemma Jfun_lt_iff (m : ℤ) (ε : ℝ) :
    Jfun m < ε ↔ m ∈ DiffSet (Uset 3 ε) (Uset 2 ε) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_lt_of_Jfun_lt h
    refine ⟨k, ?_, k - m, ?_, by ring⟩
    · exact lt_of_le_of_lt (le_max_right _ _) hk
    · exact lt_of_le_of_lt (le_max_left _ _) hk
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine lt_of_le_of_lt (Jfun_le (a - b) a) ?_
    have : a - (a - b) = b := by ring
    simp only [fJ, this]
    exact max_lt hb ha

/-- **The compact-quotient criterion** (`SyndeticW → JAProp`), proved from Weil's theorem and the one-prime theorem. -/
theorem compactQuotientCriterion : CompactQuotientCriterion := by
  intro hS
  by_contra hJA
  have hex : ∃ δ : ℝ, 0 < δ ∧ δ ≤ Jfun 1 := by
    by_contra hcon
    push Not at hcon
    apply hJA
    intro δ hδ
    have h1 : Jfun 1 < δ := hcon δ hδ
    obtain ⟨a, ha, b, hb, hab⟩ := (Jfun_lt_iff 1 δ).mp h1
    refine ⟨a, ha, ?_⟩
    have : b = a - 1 := by omega
    rw [← this]; exact hb
  obtain ⟨δ, hδ, hδJ⟩ := hex
  have hF : ∀ ε > 0, ∃ F : Finset ℤ, ∀ z : ℤ, ∃ f ∈ F, Jsem (z - f) < ε := by
    intro ε hε
    obtain ⟨F, hF⟩ := hS ε hε
    refine ⟨F, fun z => ?_⟩
    obtain ⟨f, hf, hzf⟩ := hF z
    exact ⟨f, hf, (Jfun_lt_iff _ _).mpr hzf⟩
  obtain ⟨α, hcont, hpos⟩ := weil_seminorm Jsem hF 1 (lt_of_lt_of_le hδ hδJ)
  obtain ⟨δ', hδ', hδ''⟩ := hcont (1 / 4) (by norm_num)
  have h₃ : ∀ k : ℤ, Pn (sqScales 3) k < δ' → nrm ((k : ℝ) * α) < 1 / 4 := by
    intro k hk
    apply hδ'' k
    refine lt_of_le_of_lt (Jfun_le k k) ?_
    simp only [fJ, sub_self, Pn_zero]
    exact max_lt hδ' hk |>.trans_le' (le_max_right _ _) |> fun h => by simpa [hδ'] using h
  have h₂ : ∀ k : ℤ, Pn (sqScales 2) k < δ' → nrm ((k : ℝ) * α) < 1 / 4 := by
    intro k hk
    have h : nrm (((-k : ℤ) : ℝ) * α) < 1 / 4 := by
      apply hδ'' (-k)
      refine lt_of_le_of_lt (Jfun_le (-k) 0) ?_
      simp only [fJ, zero_sub, neg_neg, Pn_zero]
      exact max_lt hk hδ'
    have e : ((-k : ℤ) : ℝ) * α = -((k : ℝ) * α) := by push_cast; ring
    rwa [e, nrm_neg] at h
  obtain ⟨z, hz⟩ := JAOnePrime.oneprime_two_three α δ' δ' hδ' hδ' h₂ h₃
  rw [hz] at hpos
  have : ((1 : ℤ) : ℝ) * (z : ℝ) = ((z : ℤ) : ℝ) := by simp
  rw [this, nrm_int] at hpos
  exact lt_irrefl _ hpos

/-- **Joint approximation from Matveev's two-term separation alone** (all other steps are proved). -/
theorem JA_of_matveev (A : ℝ) (hA : 0 ≤ A) (hP : JAClose.TwoTermSeparation A) : JAProp :=
  JAMain.JA_of_inputs compactQuotientCriterion A hA hP

/-- **Joint approximation from the weak two-term separation**: if for some `c < 1` the separation holds with profile
`a(t) = c t`, i.e. `‖r/Q + s/Q'‖ ≥ Q⁻¹ exp(-c sqrt (log Q))`, then JA holds.  (Matveev's bound is of the stronger form
`exp(-A log^2(2+t))`; this theorem shows that a much weaker separation already suffices.) -/
theorem JA_of_weak_separation (c : ℝ) (h0 : 0 ≤ c) (h1 : c < 1)
    (hP : JAClose.TwoTermSep (fun t => c * t)) : JAProp :=
  JAMain.JA_of_profile compactQuotientCriterion _ (windowProfile_weak c h0 h1) (closeGrowth_weak c h1) hP

#print axioms compactQuotientCriterion
#print axioms JA_of_matveev
#print axioms JA_of_weak_separation

end JAWeil
end LeanCheck
