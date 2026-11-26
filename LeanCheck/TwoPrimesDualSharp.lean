import Mathlib
import LeanCheck.TwoPrimesDual

/-!
# The dual criterion with a loss linear in `1/c`

Applying `rep_of_dual` to the digit ranges `H * J i`, with `H ≥ 1/(2c)`, gives representations with
`|z i| ≤ 2 h H J i`, where `h` only has to satisfy `log (7 h H R) ≤ 4h/3`.  So the digits grow like
`1/c` times a logarithm, not like `1/c²`.

* `rep_of_dual_dilated`: the abstract statement.
* `witness_of_dual_dilated`: for the weights `q^(n^2)`, `p^(n^2)`, a witness at the radius `4hH/D`,
  with `|k| ≤ (4hH/D) q^(Nq^2)`.
-/

namespace TwoPrimesDualSharp

open Finset Real TwoPrimesEffective TwoPrimesDual

theorem rep_of_dual_dilated {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℤ) (J : ι → ℕ) (t : ℤ)
    {c : ℝ} {H R h : ℕ} (hH : 1 ≤ 2 * c * H) (hR : ∑ i, |w i| * (J i : ℤ) ≤ R)
    (hR1 : 1 ≤ R) (h1 : 1 ≤ h) (hh : log (7 * h * ((H : ℝ) * R)) ≤ 4 * h / 3)
    (hvis : ∀ θ : ℝ, 1 / 10 < nd (t * θ) → ∃ i, 1 ≤ J i ∧ c ≤ J i * nd (w i * θ)) :
    ∃ z : ι → ℤ, (∀ i, |z i| ≤ 2 * (h : ℤ) * ((H : ℤ) * J i)) ∧ ∑ i, w i * z i = t := by
  have hH1 : 1 ≤ H := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · rw [h0] at hH; norm_num at hH
    · exact h0
  have hR' : ∑ i, |w i| * ((H * J i : ℕ) : ℤ) ≤ ((H * R : ℕ) : ℤ) := by
    have e : ∑ i, |w i| * ((H * J i : ℕ) : ℤ) = (H : ℤ) * ∑ i, |w i| * (J i : ℤ) := by
      rw [mul_sum]
      exact sum_congr rfl (fun i _ => by push_cast; ring)
    rw [e]; push_cast
    exact mul_le_mul_of_nonneg_left hR (by positivity)
  have hh' : log (7 * (h : ℝ) * ((H * R : ℕ) : ℝ)) ≤ 16 * (1 / 2 : ℝ) ^ 2 * h / 3 := by
    have e : 16 * (1 / 2 : ℝ) ^ 2 * h / 3 = 4 * h / 3 := by ring
    rw [e, Nat.cast_mul]; exact hh
  have hvis' : ∀ θ : ℝ, 1 / 10 < nd (t * θ) →
      ∃ i, 1 ≤ H * J i ∧ (1 / 2 : ℝ) ≤ ((H * J i : ℕ) : ℝ) * nd (w i * θ) := by
    intro θ hθ
    obtain ⟨i, hJ, hv⟩ := hvis θ hθ
    refine ⟨i, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    have h2 := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (α := ℝ) H)
    rw [Nat.cast_mul, mul_assoc]
    linarith
  obtain ⟨z, hz, hsum⟩ := rep_of_dual w (fun i => H * J i) t (c := 1 / 2) (by norm_num) le_rfl
    hR' (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) h1 hh' hvis'
  exact ⟨z, fun i => by simpa using hz i, hsum⟩

/-- Digit sums with digits `D |z_n| ≤ L q^(2n+1)` have `|value| ≤ (2L/D) q^(N^2)`. -/
lemma abs_value_of_digits {q D L N : ℕ} (hq : 2 ≤ q) (hD : 1 ≤ D) (z : Fin N → ℤ)
    (h : ∀ n : Fin N, (D : ℤ) * |z n| ≤ (L : ℤ) * (q : ℤ) ^ (2 * (n : ℕ) + 1)) :
    |((value q z : ℤ) : ℝ)| ≤ 2 * (L : ℝ) / D * (q : ℝ) ^ (N ^ 2) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : (D : ℤ) * |value q z| ≤ (L : ℤ) * ∑ n ∈ range N, (q : ℤ) ^ ((n + 1) ^ 2) := by
    have h2 : |value q z| ≤ ∑ n : Fin N, (q : ℤ) ^ ((n : ℕ) ^ 2) * |z n| := by
      unfold value
      refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun n _ => ?_)
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (q : ℤ) ^ ((n : ℕ) ^ 2))]
    refine le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) ?_
    rw [← Fin.sum_univ_eq_sum_range (fun n => (q : ℤ) ^ ((n + 1) ^ 2)) N, mul_sum, mul_sum]
    refine sum_le_sum fun n _ => ?_
    have e : (L : ℤ) * (q : ℤ) ^ (((n : ℕ) + 1) ^ 2)
        = (q : ℤ) ^ ((n : ℕ) ^ 2) * ((L : ℤ) * (q : ℤ) ^ (2 * (n : ℕ) + 1)) := by
      rw [show ((n : ℕ) + 1) ^ 2 = (n : ℕ) ^ 2 + (2 * (n : ℕ) + 1) by ring, pow_add]
      ring
    rw [e, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (h n) (by positivity)
  have h3 : ∑ n ∈ range N, (q : ℤ) ^ ((n + 1) ^ 2) ≤ 2 * (q : ℤ) ^ (N ^ 2) := by
    exact_mod_cast (sum_levels hq N).le
  have h4 : (D : ℤ) * |value q z| ≤ (L : ℤ) * (2 * (q : ℤ) ^ (N ^ 2)) :=
    le_trans h1 (mul_le_mul_of_nonneg_left h3 (by positivity))
  have h5 : (D : ℝ) * |((value q z : ℤ) : ℝ)| ≤ (L : ℝ) * (2 * (q : ℝ) ^ (N ^ 2)) := by
    exact_mod_cast h4
  have e : 2 * (L : ℝ) / D * (q : ℝ) ^ (N ^ 2) = (L : ℝ) * (2 * (q : ℝ) ^ (N ^ 2)) / D := by
    field_simp
  rw [e, le_div_iff₀ hD0, mul_comm]
  exact h5

/-- Witnesses for two prime bases, with the loss linear in `H` and a bound for `|k|`. -/
theorem witness_of_dual_dilated {p q D Np Nq R H h : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hD : 1 ≤ D)
    (t : ℤ) {c : ℝ} (hH : 1 ≤ 2 * c * H)
    (hR : ∑ n : Fin Nq, (q : ℤ) ^ ((n : ℕ) ^ 2) * ((q ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℤ)
      + ∑ n : Fin Np, (p : ℤ) ^ ((n : ℕ) ^ 2) * ((p ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℤ) ≤ R)
    (hR1 : 1 ≤ R) (h1 : 1 ≤ h) (hh : log (7 * h * ((H : ℝ) * R)) ≤ 4 * h / 3)
    (hvis : ∀ θ : ℝ, 1 / 10 < nd (t * θ) →
      (∃ n : Fin Nq, 1 ≤ q ^ (2 * (n : ℕ) + 1) / D ∧
          c ≤ ((q ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℝ) * nd ((q : ℝ) ^ ((n : ℕ) ^ 2) * θ))
      ∨ (∃ n : Fin Np, 1 ≤ p ^ (2 * (n : ℕ) + 1) / D ∧
          c ≤ ((p ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℝ) * nd ((p : ℝ) ^ ((n : ℕ) ^ 2) * θ))) :
    ∃ k : ℤ, Small q (4 * h * H / D) k ∧ Small p (4 * h * H / D) (k - t)
      ∧ |(k : ℝ)| ≤ 4 * h * H / D * (q : ℝ) ^ (Nq ^ 2) := by
  classical
  have hH1 : 1 ≤ H := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · rw [h0] at hH; norm_num at hH
    · exact h0
  set w : Fin Nq ⊕ Fin Np → ℤ := Sum.elim (fun n => (q : ℤ) ^ ((n : ℕ) ^ 2))
    (fun n => (p : ℤ) ^ ((n : ℕ) ^ 2)) with hw
  set J : Fin Nq ⊕ Fin Np → ℕ := Sum.elim (fun n => q ^ (2 * (n : ℕ) + 1) / D)
    (fun n => p ^ (2 * (n : ℕ) + 1) / D) with hJ
  have hR' : ∑ i, |w i| * (J i : ℤ) ≤ R := by
    rw [Fintype.sum_sum_type]
    simp only [hw, hJ, Sum.elim_inl, Sum.elim_inr]
    refine le_trans (le_of_eq ?_) hR
    congr 1 <;> exact sum_congr rfl (fun n _ => by rw [abs_of_nonneg (by positivity)])
  have hvis' : ∀ θ : ℝ, 1 / 10 < nd (t * θ) → ∃ i, 1 ≤ J i ∧ c ≤ J i * nd (w i * θ) := by
    intro θ hθ
    rcases hvis θ hθ with ⟨n, a, b⟩ | ⟨n, a, b⟩
    · exact ⟨Sum.inl n, a, by simpa [hw, hJ] using b⟩
    · exact ⟨Sum.inr n, a, by simpa [hw, hJ] using b⟩
  obtain ⟨z, hz, hsum⟩ := rep_of_dual_dilated w J t hH hR' hR1 h1 hh hvis'
  have hdig : ∀ (r n : ℕ) (y : ℤ),
      |y| ≤ 2 * (h : ℤ) * ((H : ℤ) * ((r ^ (2 * n + 1) / D : ℕ) : ℤ)) →
      (D : ℤ) * |y| ≤ ((2 * h * H : ℕ) : ℤ) * (r : ℤ) ^ (2 * n + 1) := by
    intro r n y hy
    have h2 : D * (r ^ (2 * n + 1) / D) ≤ r ^ (2 * n + 1) := Nat.mul_div_le _ _
    have h3 : (D : ℤ) * ((r ^ (2 * n + 1) / D : ℕ) : ℤ) ≤ (r : ℤ) ^ (2 * n + 1) := by
      exact_mod_cast h2
    calc (D : ℤ) * |y| ≤ D * (2 * (h : ℤ) * ((H : ℤ) * ((r ^ (2 * n + 1) / D : ℕ) : ℤ))) :=
          mul_le_mul_of_nonneg_left hy (by positivity)
      _ = ((2 * h * H : ℕ) : ℤ) * (D * ((r ^ (2 * n + 1) / D : ℕ) : ℤ)) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have e1 : (2 * ((2 * h * H : ℕ) : ℝ) / D) = 4 * h * H / D := by push_cast; ring
  have hpos : 1 ≤ 2 * h * H :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have sq' : Small q (2 * ((2 * h * H : ℕ) : ℝ) / D) (value q (fun n : Fin Nq => z (Sum.inl n))) :=
    small_of_digits hq hD hpos _ (fun n => hdig q n _ (by simpa [hJ] using hz (Sum.inl n)))
  have sp' : Small p (2 * ((2 * h * H : ℕ) : ℝ) / D) (value p (fun n : Fin Np => z (Sum.inr n))) :=
    small_of_digits hp hD hpos _ (fun n => hdig p n _ (by simpa [hJ] using hz (Sum.inr n)))
  rw [e1] at sq' sp'
  have hk : |((value q (fun n : Fin Nq => z (Sum.inl n)) : ℤ) : ℝ)|
      ≤ 4 * h * H / D * (q : ℝ) ^ (Nq ^ 2) := by
    have h0 := abs_value_of_digits hq hD (L := 2 * h * H) (fun n : Fin Nq => z (Sum.inl n))
      (fun n => hdig q n _ (by simpa [hJ] using hz (Sum.inl n)))
    have e3 : 2 * ((2 * h * H : ℕ) : ℝ) / D = 4 * h * H / D := by push_cast; ring
    rwa [e3] at h0
  refine ⟨value q (fun n : Fin Nq => z (Sum.inl n)), sq', ?_, hk⟩
  have e2 : value q (fun n : Fin Nq => z (Sum.inl n)) - t
      = -value p (fun n : Fin Np => z (Sum.inr n)) := by
    rw [Fintype.sum_sum_type] at hsum
    simp only [hw, Sum.elim_inl, Sum.elim_inr] at hsum
    unfold value
    linear_combination hsum
  rw [e2]
  exact sp'.neg

end TwoPrimesDualSharp
