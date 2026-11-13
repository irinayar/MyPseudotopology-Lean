import Mathlib
import LeanCheck.PVGTotBdd
import LeanCheck.PVGBaireDigits

/-!
# PVG: the core of Proposition 8.88 (conditional on Step 1; Lean check)

Scope. Steps 2 to 6 of the proof of Proposition 8.88 of `PVG_v43` (Part II), with the Lebesgue-null part of Step 6 replaced by its
category version (`PVGBaireDigits`). **Step 1 is a hypothesis, not proved in Lean.** Step 1 says: if `γ` is a locally quasi-convex group
topology with `τ_B ⊊ γ ⊆ τ_E`, then there are a bounded infinite `γ`-equicontinuous set `E` of characters `x ↦ c x` and distinct
`c₀, c₁, … ∈ E` forming a Cauchy sequence, such that every `V_ε(E) = {x : ‖c x‖ < ε for all c ∈ E}` is a `γ`-neighbourhood of `0`. Here this
is the hypothesis `hV` (the neighbourhood property), `hcE` (the `c k` lie in `E`), `hC` (the Cauchy property of `c`) and `hinj`
(distinctness).

* `step5` : (pure real arithmetic) if the sequence `(a s_n)` is covered by finitely many translates of `V_{1/12}(E)`-points, then there
  is `K` with `‖(c_{K+1} - c_K) a s_n‖ < 1/4` for all `n ≥ 1`;
* `digit_of_trace` : if `γ` induces the Bohr topology on `J_a`, then `(c_{K+1} - c_K) a ∈ F` for some `K` (`F` the digit set
  of `PVGBaireDigits`), using `totbdd` (Proposition 8.91);
* `nolqc_core` : the set of `a` for which `γ` induces the Bohr topology on `J_a` is not Euclidean-dense in the complement: arbitrarily
  close to every real `x` there is an `a` for which the Bohr trace on `J_a` fails (the set of failing `a` is dense; the conull part of the
  statement is not formalized).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set

namespace PVG
namespace Lac
open Q95

lemma dint_add_le (u v : ℝ) : dint (u + v) ≤ dint u + dint v := by
  unfold dint
  rw [AddCircle.coe_add]
  exact norm_add_le _ _

lemma dint_neg (t : ℝ) : dint (-t) = dint t := by
  unfold dint
  rw [AddCircle.coe_neg]
  exact norm_neg _

lemma dint_le_abs (t : ℝ) : dint t ≤ |t| := by
  unfold dint
  have h := QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ)) (m := t)
  simpa [Real.norm_eq_abs] using h

/-- Step 5 of the article, as arithmetic. -/
lemma step5 (c : ℕ → ℝ) (hC : ∀ ε > 0, ∃ K : ℕ, ∀ k k' : ℕ, K ≤ k → K ≤ k' → |c k - c k'| < ε)
    (a : ℝ) (F : Finset ℝ)
    (hTB : ∀ n : ℕ, 1 ≤ n → ∃ f ∈ F, ∀ k : ℕ, dint (c k * (a * sS n - f)) < 1 / 12) :
    ∃ K : ℕ, ∀ n : ℕ, 1 ≤ n → dint ((c (K + 1) - c K) * (a * sS n)) < 1 / 4 := by
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ f ∈ F, |f| ≤ M := by
    refine ⟨1 + ∑ f ∈ F, |f|, by positivity, fun f hf => ?_⟩
    have := Finset.single_le_sum (fun g _ => abs_nonneg g) hf
    linarith
  obtain ⟨K, hK⟩ := hC (1 / (12 * M)) (by positivity)
  refine ⟨K, fun n hn => ?_⟩
  obtain ⟨f, hfF, hf⟩ := hTB n hn
  have hdiff : |c (K + 1) - c K| < 1 / (12 * M) := hK (K + 1) K (by omega) le_rfl
  have h3 : dint ((c (K + 1) - c K) * f) < 1 / 12 := by
    calc dint ((c (K + 1) - c K) * f) ≤ |(c (K + 1) - c K) * f| := dint_le_abs _
      _ = |c (K + 1) - c K| * |f| := abs_mul _ _
      _ ≤ |c (K + 1) - c K| * M := by
          exact mul_le_mul_of_nonneg_left (hM f hfF) (abs_nonneg _)
      _ < 1 / (12 * M) * M := mul_lt_mul_of_pos_right hdiff hM0
      _ = 1 / 12 := by field_simp
  have hsplit : (c (K + 1) - c K) * (a * sS n) =
      c (K + 1) * (a * sS n - f) + (-(c K * (a * sS n - f))) + (c (K + 1) - c K) * f := by ring
  rw [hsplit]
  have h1 := hf (K + 1)
  have h2 := hf K
  calc dint (c (K + 1) * (a * sS n - f) + -(c K * (a * sS n - f)) + (c (K + 1) - c K) * f)
      ≤ dint (c (K + 1) * (a * sS n - f) + -(c K * (a * sS n - f))) + dint ((c (K + 1) - c K) * f) :=
        dint_add_le _ _
    _ ≤ (dint (c (K + 1) * (a * sS n - f)) + dint (-(c K * (a * sS n - f)))) + dint ((c (K + 1) - c K) * f) := by
        gcongr; exact dint_add_le _ _
    _ < 1 / 12 + 1 / 12 + 1 / 12 := by
        rw [dint_neg]; linarith
    _ = 1 / 4 := by norm_num

/-- The conclusion of Steps 2 to 6 for one coefficient `a` with the Bohr trace on `J_a`. -/
theorem digit_of_trace (γ : TopologicalSpace ℝ) (E : Set ℝ)
    (hV : ∀ ε : ℝ, 0 < ε → {x : ℝ | ∀ c ∈ E, dint (c * x) < ε} ∈ @nhds ℝ γ 0)
    (c : ℕ → ℝ) (hcE : ∀ k, c k ∈ E)
    (hC : ∀ ε > 0, ∃ K : ℕ, ∀ k k' : ℕ, K ≤ k → K ≤ k' → |c k - c k'| < ε)
    (a : ℝ)
    (hind : TopologicalSpace.induced (Subtype.val : Ja a → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Ja a → ℝ) bohrTop) :
    ∃ K : ℕ, (c (K + 1) - c K) * a ∈ Fdig := by
  obtain ⟨F, hF⟩ := totbdd γ a hind _ (hV (1 / 12) (by norm_num))
  have hTB : ∀ n : ℕ, 1 ≤ n → ∃ f ∈ F, ∀ k : ℕ, dint (c k * (a * sS n - f)) < 1 / 12 := by
    intro n hn
    obtain ⟨f, hfF, hfW⟩ := hF (sS n) (sS_mem_Sset hn)
    exact ⟨f, hfF, fun k => hfW (c k) (hcE k)⟩
  obtain ⟨K, hK⟩ := step5 c hC a F hTB
  refine ⟨K, fun n hn => ?_⟩
  have := hK n hn
  have hs : sS n = (2 : ℝ) ^ (n ^ 2) := rfl
  have heq : (2 : ℝ) ^ (n ^ 2) * ((c (K + 1) - c K) * a) = (c (K + 1) - c K) * (a * sS n) := by
    rw [hs]; ring
  rw [heq]
  exact this.le

/-- A dense-set version of the Baire statement: arbitrarily close to every real `x` there is an `a` with `δ_K a ∉ F` for all `K`. -/
lemma exists_near_digits (δ : ℕ → ℝ) (hδ : ∀ K, δ K ≠ 0) (x r : ℝ) (hr : 0 < r) :
    ∃ a : ℝ, |x - a| < r ∧ ∀ K, δ K * a ∉ Fdig := by
  obtain ⟨a, ha, hxa⟩ := (baire_digits δ hδ).exists_dist_lt x hr
  exact ⟨a, by simpa [Real.dist_eq] using hxa, ha⟩

/-- Core of Proposition 8.88 (conditional on Step 1): arbitrarily close to every real number there is an `a` such that `γ` does not induce
the Bohr topology on `J_a`. -/
theorem nolqc_core (γ : TopologicalSpace ℝ) (E : Set ℝ)
    (hV : ∀ ε : ℝ, 0 < ε → {x : ℝ | ∀ c ∈ E, dint (c * x) < ε} ∈ @nhds ℝ γ 0)
    (c : ℕ → ℝ) (hcE : ∀ k, c k ∈ E) (hinj : Function.Injective c)
    (hC : ∀ ε > 0, ∃ K : ℕ, ∀ k k' : ℕ, K ≤ k → K ≤ k' → |c k - c k'| < ε)
    (x r : ℝ) (hr : 0 < r) :
    ∃ a : ℝ, |x - a| < r ∧ ¬ (TopologicalSpace.induced (Subtype.val : Ja a → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Ja a → ℝ) bohrTop) := by
  have hδ : ∀ K, c (K + 1) - c K ≠ 0 := fun K h =>
    (Nat.succ_ne_self K) (hinj (sub_eq_zero.1 h))
  obtain ⟨a, hxa, ha⟩ := exists_near_digits (fun K => c (K + 1) - c K) hδ x r hr
  refine ⟨a, hxa, fun hind => ?_⟩
  obtain ⟨K, hK⟩ := digit_of_trace γ E hV c hcE hC a hind
  exact ha K hK

end Lac
end PVG
