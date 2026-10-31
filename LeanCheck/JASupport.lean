import Mathlib
import LeanCheck.JADense
import LeanCheck.MixedPrimeRadii

/-!
# The support argument `A_p - A_p ⊆ U_{p,2/D}` (component 17)

The final weight of the cascade of prime `p` is built level by level on the scales `q_k = p^{k^2}`:
`g_{k+1}(x) = g_k(x mod q_k - τ_k) · w_{q_{k+1}}(x)` on `ZMod q_{k+1}` (`JARandom.rd` is the reduction).  Let `A_p ⊆ [0, X]`
be the set of integers `a` with `g_L(a) ≠ 0`.

Checked here (no axiom, no `sorry`):

* `wQ_ne_zero`, `window_diff`: if the window `w_Q` is nonzero at `a` and at `a'`, then `‖(a - a')/Q‖ < 2/D`
  (both balanced representatives lie within `Q/D` of `0`);
* `support_diff`: for any shifts and any `L`, if `g_L(a) ≠ 0` and `g_L(a') ≠ 0` then `‖(a - a')/q_i‖ < 2/D` for **every**
  level `1 ≤ i ≤ L` (induction on `L`; the shifts cancel in the difference, the last window handles `i = L`);
* `support_Pn`: if the next scale exceeds `D X`, i.e. `D X < p^{(L+1)^2}`, then for `a, a' ∈ [0, X]` in the support,
  `P_p(a - a') = sup_n ‖(a - a')/p^{n^2}‖ < 2/D`, i.e. `a - a' ∈ U_{p,2/D}`.  For `n ≤ L` this is `support_diff` (a finite
  maximum, so still `< 2/D`); for `n > L`, `‖(a-a')/p^{n^2}‖ ≤ X/p^{(L+1)^2} < 1/D`;
* `suppSet`, `suppSet_diff_Pn`: the support as a `Finset ℤ ⊆ Aset X`, outside of which the weight vanishes
  (`suppSet_vanish`), with `A - A ⊆ U_{p,2/D}`.

Together with `JADense.realized_difference_bound_supp` this is the hypothesis `A_p - A_p ⊆ U_{p,2/D}` of `DenseDifferences`
(the two supports `A_2`, `A_3` come from the cascades of `2` and of `3`).  Not checked here: that the cascade's shifts can be
chosen jointly so that the last-level energy bound holds, and the uniform central bound.
-/

namespace LeanCheck
namespace JASupport

open Finset MixedPrime JAWindowQ JAEnergyLink JAEnergyIdentity JARandom

/-! ### The window support -/

lemma wQ_ne_zero {D : ℝ} (hD : 0 < D) {Q : ℕ} [NeZero Q] (x : ZMod Q) (h : wQ D Q x ≠ 0) :
    |(x.valMinAbs : ℝ)| < Q / D := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  by_contra hge
  push Not at hge
  apply h
  unfold JAWindowQ.wQ
  apply JAWindow.wD_zero D hD
  rw [abs_div, abs_of_pos hQ, le_div_iff₀ hQ]
  have : 1 / D * Q = Q / D := by ring
  linarith

/-- Two points of the support of a window are `2/D`-close modulo `Q`. -/
lemma window_diff {D : ℝ} (hD : 0 < D) {Q : ℕ} [NeZero Q] (a a' : ℤ)
    (ha : wQ D Q (a : ZMod Q) ≠ 0) (ha' : wQ D Q (a' : ZMod Q) ≠ 0) :
    nrm (((a - a' : ℤ) : ℝ) / Q) < 2 / D := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have h1 := wQ_ne_zero hD _ ha
  have h2 := wQ_ne_zero hD _ ha'
  set x := (a : ZMod Q).valMinAbs with hx
  set x' := (a' : ZMod Q).valMinAbs with hx'
  have e1 : (Q : ℤ) ∣ a - x :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x a Q).mp (ZMod.coe_valMinAbs _)
  have e2 : (Q : ℤ) ∣ a' - x' :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x' a' Q).mp (ZMod.coe_valMinAbs _)
  obtain ⟨k, hk⟩ := e1
  obtain ⟨k', hk'⟩ := e2
  have hdecomp : a - a' = (x - x') + (Q : ℤ) * (k - k') := by
    rw [mul_sub]; linarith
  have e : ((a - a' : ℤ) : ℝ) / Q = ((x - x' : ℤ) : ℝ) / Q + ((k - k' : ℤ) : ℝ) := by
    rw [hdecomp]
    push_cast
    field_simp
  rw [e, nrm_add_int]
  refine lt_of_le_of_lt (nrm_le_abs _) ?_
  rw [abs_div, abs_of_pos hQ]
  have h3 : |((x - x' : ℤ) : ℝ)| ≤ |(x : ℝ)| + |(x' : ℝ)| := by
    push_cast
    exact abs_sub _ _
  have h4 : |((x - x' : ℤ) : ℝ)| < 2 * (Q / D) := by linarith
  rw [div_lt_iff₀ hQ]
  have : 2 / D * Q = 2 * (Q / D) := by ring
  linarith

/-! ### The cascade -/

section cascade

variable (D : ℝ) (q : ℕ → ℕ) [hq : ∀ k, NeZero (q k)] (hdvd : ∀ k, q k ∣ q (k + 1))
  (g : (k : ℕ) → ZMod (q k) → ℝ) (τ : (k : ℕ) → ZMod (q k))
  (hrec : ∀ (k : ℕ) (x : ZMod (q (k + 1))),
    g (k + 1) x = g k (rd (hdvd k) x - τ k) * wQ D (q (k + 1)) x)

include hrec in
/-- **Difference property of the support at every level.** -/
theorem support_diff (hD : 0 < D) :
    ∀ (L : ℕ) (a a' : ℤ), g L (a : ZMod (q L)) ≠ 0 → g L (a' : ZMod (q L)) ≠ 0 →
      ∀ i : ℕ, 1 ≤ i → i ≤ L → nrm (((a - a' : ℤ) : ℝ) / (q i : ℕ)) < 2 / D := by
  intro L
  induction L with
  | zero =>
    intro a a' _ _ i hi1 hi2
    omega
  | succ k ih =>
    intro a a' ha ha' i hi1 hi2
    have hshift : ∀ b : ℤ, rd (hdvd k) (b : ZMod (q (k + 1))) - τ k =
        ((b - ((τ k).val : ℤ) : ℤ) : ZMod (q k)) := by
      intro b
      rw [map_intCast, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hfa := hrec k (a : ZMod (q (k + 1)))
    have hfa' := hrec k (a' : ZMod (q (k + 1)))
    rw [hshift] at hfa hfa'
    rw [hfa] at ha
    rw [hfa'] at ha'
    have ha1 := left_ne_zero_of_mul ha
    have ha2 := right_ne_zero_of_mul ha
    have ha1' := left_ne_zero_of_mul ha'
    have ha2' := right_ne_zero_of_mul ha'
    rcases Nat.lt_or_ge k i with h | h
    · have hi : i = k + 1 := by omega
      subst hi
      exact window_diff hD a a' ha2 ha2'
    · have := ih (a - ((τ k).val : ℤ)) (a' - ((τ k).val : ℤ)) ha1 ha1' i hi1 h
      have e : (a - ((τ k).val : ℤ)) - (a' - ((τ k).val : ℤ)) = a - a' := by ring
      rwa [e] at this

end cascade

/-! ### From the support to `P_p` -/

lemma exists_lt_bound (s : Finset ℕ) (f : ℕ → ℝ) (r : ℝ) (h : ∀ i ∈ s, f i < r) :
    ∃ c < r, ∀ i ∈ s, f i ≤ c := by
  induction s using Finset.induction_on with
  | empty => exact ⟨r - 1, by linarith, by simp⟩
  | insert j s hj ih =>
    obtain ⟨c, hc, hcs⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨max c (f j), max_lt hc (h j (Finset.mem_insert_self _ _)), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact le_max_right _ _
    · exact (hcs i hi).trans (le_max_left _ _)

lemma sq_dvd (p k : ℕ) : p ^ (k ^ 2) ∣ p ^ ((k + 1) ^ 2) :=
  pow_dvd_pow p (Nat.pow_le_pow_left (Nat.le_succ k) 2)

/-- **The support argument.**  `A_p - A_p ⊆ U_{p,2/D}`. -/
theorem support_Pn {p : ℕ} [NeZero p] (hp : 2 ≤ p) (D : ℝ) (hD : 0 < D)
    (g : (k : ℕ) → ZMod (p ^ (k ^ 2)) → ℝ) (τ : (k : ℕ) → ZMod (p ^ (k ^ 2)))
    (hrec : ∀ (k : ℕ) (x : ZMod (p ^ ((k + 1) ^ 2))),
      g (k + 1) x = g k (rd (sq_dvd p k) x - τ k) * wQ D (p ^ ((k + 1) ^ 2)) x)
    (L X : ℕ) (hL : D * X < (p : ℝ) ^ ((L + 1) ^ 2))
    (a a' : ℤ) (ha : g L (a : ZMod (p ^ (L ^ 2))) ≠ 0) (ha' : g L (a' : ZMod (p ^ (L ^ 2))) ≠ 0)
    (haX : 0 ≤ a ∧ a ≤ X) (ha'X : 0 ≤ a' ∧ a' ≤ X) :
    Pn (sqScales p) (a - a') < 2 / D := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hdiff := support_diff D (fun k => p ^ (k ^ 2)) (sq_dvd p) g τ hrec hD L a a' ha ha'
  -- the finite part
  obtain ⟨c₁, hc₁, hc₁'⟩ := exists_lt_bound (Finset.Icc 1 L)
    (fun i => nrm (((a - a' : ℤ) : ℝ) / ((p ^ (i ^ 2) : ℕ) : ℝ))) (2 / D)
    (fun i hi => hdiff i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)
  -- the tail part
  have hXD : (X : ℝ) / (p : ℝ) ^ ((L + 1) ^ 2) < 1 / D := by
    rw [div_lt_div_iff₀ (by positivity) hD]
    linarith
  have hc₂ : (X : ℝ) / (p : ℝ) ^ ((L + 1) ^ 2) < 2 / D := by
    have : 1 / D < 2 / D := by
      apply div_lt_div_of_pos_right (by norm_num) hD
    linarith
  have hS : (sqScales p).Nonempty := ⟨p ^ (1 ^ 2), mem_sqScales (le_refl 1)⟩
  have hle : Pn (sqScales p) (a - a') ≤ max c₁ ((X : ℝ) / (p : ℝ) ^ ((L + 1) ^ 2)) := by
    apply Pn_le hS
    rintro s ⟨n, hn, rfl⟩
    by_cases hnL : n ≤ L
    · exact (hc₁' n (Finset.mem_Icc.mpr ⟨hn, hnL⟩)).trans (le_max_left _ _)
    · push Not at hnL
      refine le_trans ?_ (le_max_right _ _)
      refine (nrm_le_abs _).trans ?_
      have hpn : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by positivity
      rw [abs_div, abs_of_pos hpn]
      have habs : |((a - a' : ℤ) : ℝ)| ≤ X := by
        have h1 : ((a - a' : ℤ) : ℝ) ≤ X := by
          have : a - a' ≤ (X : ℤ) := by omega
          exact_mod_cast this
        have h2 : -(X : ℝ) ≤ ((a - a' : ℤ) : ℝ) := by
          have : -(X : ℤ) ≤ a - a' := by omega
          exact_mod_cast this
        exact abs_le.mpr ⟨h2, h1⟩
      have hmono : (p : ℝ) ^ ((L + 1) ^ 2) ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        push_cast
        apply pow_le_pow_right₀ hp1
        nlinarith
      calc |((a - a' : ℤ) : ℝ)| / ((p ^ (n ^ 2) : ℕ) : ℝ) ≤ (X : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right habs hpn.le
        _ ≤ (X : ℝ) / (p : ℝ) ^ ((L + 1) ^ 2) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hmono
  exact lt_of_le_of_lt hle (max_lt hc₁ hc₂)

/-! ### The support as a finite set -/

/-- The support in `[0, X]` of a weight, as a set of integers. -/
noncomputable def suppSet {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (X : ℕ) : Finset ℤ :=
  open Classical in (Aset X).filter (fun a => Fw f a ≠ 0)

lemma suppSet_subset {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (X : ℕ) : suppSet f X ⊆ Aset X :=
  Finset.filter_subset _ _

lemma suppSet_vanish {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (X : ℕ) :
    ∀ a ∈ Aset X, a ∉ suppSet f X → Fw f a = 0 := by
  classical
  intro a ha hna
  by_contra h
  exact hna (by unfold suppSet; exact Finset.mem_filter.mpr ⟨ha, h⟩)

lemma mem_suppSet {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (X : ℕ) {a : ℤ} (ha : a ∈ suppSet f X) :
    (0 ≤ a ∧ a ≤ X) ∧ f (a : ZMod q) ≠ 0 := by
  classical
  unfold suppSet at ha
  obtain ⟨hA, hne⟩ := Finset.mem_filter.mp ha
  unfold Aset at hA
  simp only [Finset.mem_image, Finset.mem_range] at hA
  obtain ⟨x, hx, rfl⟩ := hA
  refine ⟨⟨by positivity, by exact_mod_cast Nat.lt_succ_iff.mp hx⟩, ?_⟩
  simpa [Fw, fn] using hne

/-- **`A_p - A_p ⊆ U_{p,2/D}`** for the support of the last-level weight. -/
theorem suppSet_diff_Pn {p : ℕ} [NeZero p] (hp : 2 ≤ p) (D : ℝ) (hD : 0 < D)
    (g : (k : ℕ) → ZMod (p ^ (k ^ 2)) → ℝ) (τ : (k : ℕ) → ZMod (p ^ (k ^ 2)))
    (hrec : ∀ (k : ℕ) (x : ZMod (p ^ ((k + 1) ^ 2))),
      g (k + 1) x = g k (rd (sq_dvd p k) x - τ k) * wQ D (p ^ ((k + 1) ^ 2)) x)
    (L X : ℕ) (hL : D * X < (p : ℝ) ^ ((L + 1) ^ 2)) :
    ∀ a ∈ suppSet (g L) X, ∀ a' ∈ suppSet (g L) X, Pn (sqScales p) (a - a') < 2 / D := by
  intro a ha a' ha'
  obtain ⟨hX, hg⟩ := mem_suppSet (g L) X ha
  obtain ⟨hX', hg'⟩ := mem_suppSet (g L) X ha'
  exact support_Pn hp D hD g τ hrec L X hL a a' hg hg' hX hX'

#print axioms window_diff
#print axioms support_diff
#print axioms support_Pn
#print axioms suppSet_vanish
#print axioms suppSet_diff_Pn

end JASupport
end LeanCheck
