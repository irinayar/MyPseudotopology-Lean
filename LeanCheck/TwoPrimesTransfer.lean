import LeanCheck.MixedPrimeSplit
import LeanCheck.MixedPrimeRadii

/-!
# TwoPrimes: from the unit target to an arbitrary integer target

For scale sets `S3` (the ternary chain) and `S2` (the binary chain) and radius `η > 0`, call an integer `m` a
*witness for the unit target at radius `η`* if `Pn S3 m < η` and `Pn S2 (m - 1) < η`.  The least `|m|` over
such witnesses is the quantity `h_η(1)` of the TwoPrimes notes.

* `transfer_unit`: if `m` is such a witness and `t ≠ 0` is an integer, then `k = t * m` satisfies
  `Pn S3 k < |t| η` and `Pn S2 (k - t) < |t| η`.  (Proof: `Pn (t x) ≤ |t| Pn x`, from `Pn_zsmul_le`.)
* `transfer_height`: the height of the new witness is at most `|t|` times the height of `m`, so
  `h_ε(t) ≤ |t| · h_{ε/|t|}(1)`.
* `transfer_unit_sq` specializes to the scales `sqScales 3`, `sqScales 2` of the article.
* `witness_mono`: witnesses at a smaller radius are witnesses at every larger radius (the staircase
  monotonicity of `h_ε`).

Only the subadditivity layer of `MixedPrimeSplit` is used; no diagonal density is assumed.
-/

namespace LeanCheck
namespace TwoPrimes

open LeanCheck.MixedPrime

section General

variable {S2 S3 : Set ℕ}

/-- A witness for the unit target at radius `η` yields a witness for the target `t` at radius `|t| η`. -/
theorem transfer_unit (h2 : S2.Nonempty) (h3 : S3.Nonempty) (t m : ℤ) {η : ℝ}
    (hm3 : Pn S3 m < η) (hm2 : Pn S2 (m - 1) < η) (ht : t ≠ 0) :
    Pn S3 (t * m) < |(t : ℝ)| * η ∧ Pn S2 (t * m - t) < |(t : ℝ)| * η := by
  have hpos : 0 < |(t : ℝ)| := abs_pos.mpr (by exact_mod_cast ht)
  refine ⟨?_, ?_⟩
  · exact lt_of_le_of_lt (Pn_zsmul_le h3 t m) (mul_lt_mul_of_pos_left hm3 hpos)
  · have e : t * m - t = t * (m - 1) := by ring
    rw [e]
    exact lt_of_le_of_lt (Pn_zsmul_le h2 t (m - 1)) (mul_lt_mul_of_pos_left hm2 hpos)

/-- Height form: if the unit-target witness has `|m| ≤ H`, the transferred witness has height `≤ |t| H`. -/
theorem transfer_height (h2 : S2.Nonempty) (h3 : S3.Nonempty) (t m : ℤ) (H : ℝ) {η : ℝ}
    (hm : |(m : ℝ)| ≤ H) (hm3 : Pn S3 m < η) (hm2 : Pn S2 (m - 1) < η) (ht : t ≠ 0) :
    ∃ k : ℤ, |(k : ℝ)| ≤ |(t : ℝ)| * H ∧ Pn S3 k < |(t : ℝ)| * η ∧ Pn S2 (k - t) < |(t : ℝ)| * η := by
  refine ⟨t * m, ?_, (transfer_unit h2 h3 t m hm3 hm2 ht).1, (transfer_unit h2 h3 t m hm3 hm2 ht).2⟩
  have e : |((t * m : ℤ) : ℝ)| = |(t : ℝ)| * |(m : ℝ)| := by push_cast; exact abs_mul _ _
  rw [e]
  exact mul_le_mul_of_nonneg_left hm (abs_nonneg _)

/-- Staircase monotonicity: a witness at radius `η` is a witness at every radius `η' ≥ η`. -/
theorem witness_mono {k : ℤ} {t : ℤ} {η η' : ℝ} (hη : η ≤ η')
    (h3 : Pn S3 k < η) (h2 : Pn S2 (k - t) < η) : Pn S3 k < η' ∧ Pn S2 (k - t) < η' :=
  ⟨lt_of_lt_of_le h3 hη, lt_of_lt_of_le h2 hη⟩

end General

/-- The specialization to the scales `{3^(n²)}` and `{2^(n²)}`. -/
theorem transfer_unit_sq (t m : ℤ) {η : ℝ}
    (hm3 : Pn (sqScales 3) m < η) (hm2 : Pn (sqScales 2) (m - 1) < η) (ht : t ≠ 0) :
    Pn (sqScales 3) (t * m) < |(t : ℝ)| * η ∧ Pn (sqScales 2) (t * m - t) < |(t : ℝ)| * η :=
  transfer_unit ⟨2 ^ (1 ^ 2), mem_sqScales le_rfl⟩ ⟨3 ^ (1 ^ 2), mem_sqScales le_rfl⟩ t m hm3 hm2 ht

end TwoPrimes
end LeanCheck
