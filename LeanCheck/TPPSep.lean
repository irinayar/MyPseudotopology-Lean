import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# ThreePrimePlus: elementary parts of the two-term separation lemma

The lemma "Two-term separation" of ThreePrimePlus states, for `Q = p^e < Q' = q^e'` powers of distinct
primes and integers `(a,d) ≠ 0` with `|a|,|d| ≤ D < Q`, a lower bound for `|a/Q + d/Q'|` via Matveev's
theorem for `Λ = e' log q - e log p + log(|a|/|d|)`.  Here we formalize everything except Matveev's
theorem, which enters as the hypothesis `|Λ| ≥ m₀`:

* `exp_sub_one_lower`:  `|e^Λ - 1| ≥ (1/2) min(1,|Λ|)`;
* `not_eq_of_lt`:  `Λ ≠ 0`, i.e. `|a| q^e' ≠ |d| p^e` when `0 < |a| < p^e`;
* `abs_form_eq`:  for opposite signs, `|a/Q + d/Q'| = (|d|/Q') |e^Λ - 1|` with `Λ = log(|a|Q'/(|d|Q))`;
* `sep_of_matveev`:  the resulting lower bound `(1/2) min(1,m₀)/Q'`.
-/

namespace TPP

open Real

theorem exp_sub_one_lower (Λ : ℝ) : (1 / 2) * min 1 |Λ| ≤ |exp Λ - 1| := by
  rcases le_or_gt 0 Λ with h | h
  · have h1 : Λ ≤ exp Λ - 1 := by linarith [Real.add_one_le_exp Λ]
    have e1 : |exp Λ - 1| = exp Λ - 1 := abs_of_nonneg (by linarith)
    have e2 : |Λ| = Λ := abs_of_nonneg h
    rw [e1, e2]
    have h2 : min 1 Λ ≤ Λ := min_le_right _ _
    have h3 : 0 ≤ min 1 Λ := le_min zero_le_one h
    linarith
  · have hs : 0 < -Λ := by linarith
    have hexp : exp Λ * (1 + -Λ) ≤ 1 := by
      have h1 : 1 + -Λ ≤ exp (-Λ) := by linarith [Real.add_one_le_exp (-Λ)]
      have h2 : exp Λ * exp (-Λ) = 1 := by rw [← Real.exp_add]; simp
      have h3 : exp Λ * (1 + -Λ) ≤ exp Λ * exp (-Λ) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos Λ).le
      linarith
    have hlt : exp Λ < 1 := by
      have : exp Λ < exp 0 := Real.exp_lt_exp.mpr h
      simpa using this
    have e1 : |exp Λ - 1| = 1 - exp Λ := by
      rw [abs_of_neg (by linarith)]; ring
    have e2 : |Λ| = -Λ := abs_of_neg h
    rw [e1, e2]
    -- 1 - e^Λ ≥ s/(1+s) with s = -Λ
    have key : (-Λ) ≤ (1 - exp Λ) * (1 + -Λ) := by
      nlinarith [hexp]
    rcases le_or_gt (-Λ) 1 with hle | hgt
    · rw [min_eq_right hle]
      have h2 : (1 - exp Λ) * 2 ≥ (1 - exp Λ) * (1 + -Λ) := by
        have : 0 ≤ 1 - exp Λ := by linarith
        nlinarith
      nlinarith
    · rw [min_eq_left hgt.le]
      have h2 : (1 - exp Λ) * (1 + -Λ) ≤ (1 - exp Λ) * (2 * (-Λ)) := by
        have : 0 ≤ 1 - exp Λ := by linarith
        nlinarith
      have h3 : 0 ≤ 1 - exp Λ := by linarith
      nlinarith

/-- `|a| q^e' ≠ |d| p^e` when `0 < |a| < p^e` and `p ≠ q` are primes. -/
theorem not_eq_of_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e e' a d : ℕ)
    (ha : 0 < a) (hlt : a < p ^ e) : a * q ^ e' ≠ d * p ^ e := by
  intro h
  have hcop : Nat.Coprime (p ^ e) (q ^ e') :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)
  have hdvd : p ^ e ∣ a * q ^ e' := ⟨d, by rw [h]; ring⟩
  have h2 : p ^ e ∣ a := hcop.dvd_of_dvd_mul_right hdvd
  have h3 := Nat.le_of_dvd ha h2
  omega

/-- Opposite signs: `|a/Q + d/Q'| = (|d|/Q') |e^Λ - 1|`, `Λ = log(|a|Q'/(|d|Q))`. -/
theorem abs_form_eq (Q Q' a d : ℝ) (hQ : 0 < Q) (hQ' : 0 < Q') (ha : a ≠ 0) (hd : d ≠ 0)
    (had : a * d < 0) :
    |a / Q + d / Q'| = (|d| / Q') * |exp (Real.log (|a| * Q' / (|d| * Q))) - 1| := by
  have hapos : 0 < |a| := abs_pos.mpr ha
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have ht : 0 < |a| * Q' / (|d| * Q) := by positivity
  rw [Real.exp_log ht]
  have key : |a * Q' / (|d| * Q)| = |a| * Q' / (|d| * Q) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hQ', abs_of_pos hQ, abs_abs]
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · -- a < 0, d > 0
    have hd' : 0 < d := by nlinarith
    rw [abs_of_neg ha', abs_of_pos hd']
    have e1 : a / Q + d / Q' = -((d / Q') * ((-a) * Q' / (d * Q) - 1)) := by
      field_simp
      ring
    rw [e1, abs_neg, abs_mul, abs_of_pos (div_pos hd' hQ')]
  · -- a > 0, d < 0
    have hd' : d < 0 := by nlinarith
    rw [abs_of_pos ha', abs_of_neg hd']
    have e1 : a / Q + d / Q' = ((-d) / Q') * (a * Q' / ((-d) * Q) - 1) := by
      field_simp
      ring
    rw [e1, abs_mul, abs_of_pos (div_pos (by linarith) hQ')]

/-- Lower bound for `|a/Q + d/Q'|` from a lower bound for `|Λ|` (Matveev's theorem). -/
theorem sep_of_matveev (Q Q' a d m₀ : ℝ) (hQ : 0 < Q) (hQ' : 0 < Q') (ha : a ≠ 0) (hd : d ≠ 0)
    (had : a * d < 0) (hdint : 1 ≤ |d|) (hm₀ : 0 < m₀)
    (hΛ : m₀ ≤ |Real.log (|a| * Q' / (|d| * Q))|) :
    (1 / 2) * min 1 m₀ / Q' ≤ |a / Q + d / Q'| := by
  rw [abs_form_eq Q Q' a d hQ hQ' ha hd had]
  have h1 := exp_sub_one_lower (Real.log (|a| * Q' / (|d| * Q)))
  have h2 : min 1 m₀ ≤ min 1 |Real.log (|a| * Q' / (|d| * Q))| := min_le_min_left 1 hΛ
  have h3 : (1 / 2) * min 1 m₀ ≤ |exp (Real.log (|a| * Q' / (|d| * Q))) - 1| := by linarith
  have h4 : 0 ≤ (1 / 2) * min 1 m₀ := by
    have : 0 ≤ min 1 m₀ := le_min zero_le_one hm₀.le
    linarith
  calc (1 / 2) * min 1 m₀ / Q' = (1 / Q') * ((1 / 2) * min 1 m₀) := by ring
    _ ≤ (|d| / Q') * ((1 / 2) * min 1 m₀) := by
        apply mul_le_mul_of_nonneg_right _ h4
        exact div_le_div_of_nonneg_right hdint hQ'.le
    _ ≤ (|d| / Q') * |exp (Real.log (|a| * Q' / (|d| * Q))) - 1| :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

end TPP
