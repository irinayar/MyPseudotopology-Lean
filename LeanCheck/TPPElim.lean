import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-!
# ThreePrimePlus: the elimination argument of Lemmas F and E

* `elim_identity`: for integer vectors `(a,b,c)`, `(a',b',c')`,
  `(a'b - ab')/Q₂ + (a'c - ac')/Q₃ = a' S - a S'` with `S = a/Q₁ + b/Q₂ + c/Q₃`.
* `elim_bound`: if `|S|,|S'| < δ` and `|a|,|a'| ≤ M` then `|a'S - aS'| < 2Mδ`.
* `proportional_of_sep`: if every nonzero coefficient pair has `|e₂/Q₂ + e₃/Q₃| ≥ s` (the two-term
  separation, an input) and `|e₂/Q₂ + e₃/Q₃| < s`, then `e₂ = e₃ = 0`.
* `cross_of_elim`: `e₂ = e₃ = 0` with `a,a' ≠ 0` means the two vectors are proportional.
* `exists_primitive_gen`: pairwise proportional integer vectors with nonzero first coordinate are
  integer multiples of one primitive integer vector.
-/

namespace TPP

theorem elim_identity (Q1 Q2 Q3 : ℝ) (a b c a' b' c' : ℤ) :
    ((a' * b - a * b' : ℤ) : ℝ) / Q2 + ((a' * c - a * c' : ℤ) : ℝ) / Q3 =
      a' * ((a : ℝ) / Q1 + b / Q2 + c / Q3) - a * ((a' : ℝ) / Q1 + b' / Q2 + c' / Q3) := by
  push_cast
  ring

theorem elim_bound (S S' δ M : ℝ) (a a' : ℤ) (hM : 0 < M) (ha : |(a : ℝ)| ≤ M)
    (ha' : |(a' : ℝ)| ≤ M) (hS : |S| < δ) (hS' : |S'| < δ) :
    |(a' : ℝ) * S - a * S'| < 2 * M * δ := by
  have hδ : 0 < δ := lt_of_le_of_lt (abs_nonneg _) hS
  have e1 : |(a' : ℝ) * S| < M * δ := by
    rw [abs_mul]
    calc |(a' : ℝ)| * |S| ≤ M * |S| := mul_le_mul_of_nonneg_right ha' (abs_nonneg _)
      _ < M * δ := mul_lt_mul_of_pos_left hS hM
  have e2 : |(a : ℝ) * S'| < M * δ := by
    rw [abs_mul]
    calc |(a : ℝ)| * |S'| ≤ M * |S'| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      _ < M * δ := mul_lt_mul_of_pos_left hS' hM
  calc |(a' : ℝ) * S - a * S'| = |(a' : ℝ) * S + (-((a : ℝ) * S'))| := by rw [sub_eq_add_neg]
    _ ≤ |(a' : ℝ) * S| + |-((a : ℝ) * S')| := abs_add_le _ _
    _ = |(a' : ℝ) * S| + |(a : ℝ) * S'| := by rw [abs_neg]
    _ < M * δ + M * δ := add_lt_add e1 e2
    _ = 2 * M * δ := by ring

theorem proportional_of_sep (Q2 Q3 s : ℝ)
    (hsep : ∀ e2 e3 : ℤ, (e2 ≠ 0 ∨ e3 ≠ 0) → s ≤ |(e2 : ℝ) / Q2 + (e3 : ℝ) / Q3|)
    (e2 e3 : ℤ) (h : |(e2 : ℝ) / Q2 + (e3 : ℝ) / Q3| < s) : e2 = 0 ∧ e3 = 0 := by
  by_contra hne
  have : e2 ≠ 0 ∨ e3 ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hne ⟨h'.1, h'.2⟩
  exact absurd (hsep e2 e3 this) (not_le.mpr h)

theorem cross_of_elim (a b c a' b' c' : ℤ) (ha : a ≠ 0) (ha' : a' ≠ 0)
    (h2 : a' * b - a * b' = 0) (h3 : a' * c - a * c' = 0) :
    a' * b = a * b' ∧ a' * c = a * c' := ⟨by linarith, by linarith⟩

/-- Pairwise proportional integer vectors with nonzero first coordinate are integer multiples of one
primitive integer vector (primitive: `u₁γ₁ + u₂γ₂ + u₃γ₃ = 1` for some integers `u_i`). -/
theorem exists_primitive_gen (v1 v2 v3 : ℤ) (hv : v1 ≠ 0) (R : Set (ℤ × ℤ × ℤ))
    (hR : ∀ w ∈ R, w.1 * v2 = v1 * w.2.1 ∧ w.1 * v3 = v1 * w.2.2) :
    ∃ γ1 γ2 γ3 : ℤ, γ1 ≠ 0 ∧ (∃ u1 u2 u3 : ℤ, u1 * γ1 + u2 * γ2 + u3 * γ3 = 1) ∧
      ∀ w ∈ R, ∃ m : ℤ, w.1 = m * γ1 ∧ w.2.1 = m * γ2 ∧ w.2.2 = m * γ3 := by
  -- g = gcd(gcd(v1,v2),v3)
  set g1 : ℕ := Int.gcd v1 v2 with hg1
  set g : ℕ := Int.gcd (g1 : ℤ) v3 with hg
  have hg1v1 : (g1 : ℤ) ∣ v1 := Int.gcd_dvd_left v1 v2
  have hg1v2 : (g1 : ℤ) ∣ v2 := Int.gcd_dvd_right v1 v2
  have hgg1 : (g : ℤ) ∣ (g1 : ℤ) := Int.gcd_dvd_left (g1 : ℤ) v3
  have hgv3 : (g : ℤ) ∣ v3 := Int.gcd_dvd_right (g1 : ℤ) v3
  have hgv1 : (g : ℤ) ∣ v1 := dvd_trans hgg1 hg1v1
  have hgv2 : (g : ℤ) ∣ v2 := dvd_trans hgg1 hg1v2
  have hg0 : (g : ℤ) ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hgv1
    exact hv hgv1
  obtain ⟨γ1, hγ1⟩ := hgv1
  obtain ⟨γ2, hγ2⟩ := hgv2
  obtain ⟨γ3, hγ3⟩ := hgv3
  -- Bezout
  have b1 : (g1 : ℤ) = v1 * Int.gcdA v1 v2 + v2 * Int.gcdB v1 v2 := Int.gcd_eq_gcd_ab v1 v2
  have b2 : (g : ℤ) = (g1 : ℤ) * Int.gcdA (g1 : ℤ) v3 + v3 * Int.gcdB (g1 : ℤ) v3 :=
    Int.gcd_eq_gcd_ab (g1 : ℤ) v3
  have hbez : ∃ u1 u2 u3 : ℤ, u1 * γ1 + u2 * γ2 + u3 * γ3 = 1 := by
    refine ⟨Int.gcdA v1 v2 * Int.gcdA (g1 : ℤ) v3, Int.gcdB v1 v2 * Int.gcdA (g1 : ℤ) v3,
      Int.gcdB (g1 : ℤ) v3, ?_⟩
    apply mul_left_cancel₀ hg0
    have : (g : ℤ) * (Int.gcdA v1 v2 * Int.gcdA (↑g1) v3 * γ1 + Int.gcdB v1 v2 * Int.gcdA (↑g1) v3 * γ2
        + Int.gcdB (↑g1) v3 * γ3) = (g : ℤ) * 1 := by
      calc (g : ℤ) * (Int.gcdA v1 v2 * Int.gcdA (↑g1) v3 * γ1 + Int.gcdB v1 v2 * Int.gcdA (↑g1) v3 * γ2
            + Int.gcdB (↑g1) v3 * γ3)
          = (v1 * Int.gcdA v1 v2 + v2 * Int.gcdB v1 v2) * Int.gcdA (↑g1) v3 + v3 * Int.gcdB (↑g1) v3 := by
            rw [hγ1, hγ2, hγ3]; ring
        _ = (g1 : ℤ) * Int.gcdA (↑g1) v3 + v3 * Int.gcdB (↑g1) v3 := by rw [← b1]
        _ = (g : ℤ) := b2.symm
        _ = (g : ℤ) * 1 := by ring
    exact this
  have hγ10 : γ1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hγ1
    exact hv hγ1
  refine ⟨γ1, γ2, γ3, hγ10, hbez, ?_⟩
  intro w hw
  obtain ⟨e2, e3⟩ := hR w hw
  rw [hγ2] at e2
  rw [hγ3] at e3
  rw [hγ1] at e2 e3
  -- w.1 * γ2 = γ1 * w.2.1  and  w.1 * γ3 = γ1 * w.2.2
  have f2 : w.1 * γ2 = γ1 * w.2.1 := by
    apply mul_left_cancel₀ hg0
    linarith
  have f3 : w.1 * γ3 = γ1 * w.2.2 := by
    apply mul_left_cancel₀ hg0
    linarith
  obtain ⟨u1, u2, u3, hu⟩ := hbez
  -- γ1 divides w.1
  have hdvd : γ1 ∣ w.1 := by
    have e : w.1 = u1 * (w.1 * γ1) + u2 * (w.1 * γ2) + u3 * (w.1 * γ3) := by
      calc w.1 = w.1 * (u1 * γ1 + u2 * γ2 + u3 * γ3) := by rw [hu, mul_one]
        _ = _ := by ring
    rw [e, f2, f3]
    exact ⟨u1 * w.1 + u2 * w.2.1 + u3 * w.2.2, by ring⟩
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨m, by rw [hm]; ring, ?_, ?_⟩
  · apply mul_left_cancel₀ hγ10
    rw [hm] at f2
    linarith
  · apply mul_left_cancel₀ hγ10
    rw [hm] at f3
    linarith

end TPP
