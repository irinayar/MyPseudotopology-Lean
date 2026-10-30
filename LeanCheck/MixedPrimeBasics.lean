import Mathlib

/-!
# TVGaddmore_v17: basic layer for the mixed-prime pseudo-norm

`nrm x` is the distance from the real number `x` to the nearest integer (the norm in `ℝ/ℤ`).
For a set `S` of positive integers ("scales") put `Pn S k = sup_{q ∈ S} nrm (k / q)`.
The paper's `P_S` is `Pn` for the scale set `{ℓ ^ (n ^ 2) | ℓ ∈ S, n ≥ 1}`.
All results below hold for an arbitrary scale set `S`, so they cover every finite prime set.
-/

namespace LeanCheck
namespace MixedPrime

/-- The circle group `ℝ / ℤ`. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

/-- Distance from `x` to the nearest integer. -/
noncomputable def nrm (x : ℝ) : ℝ := ‖(x : Circ)‖

lemma nrm_eq (x : ℝ) : nrm x = |x - round x| := by
  simp [nrm, AddCircle.norm_eq]

lemma nrm_nonneg (x : ℝ) : 0 ≤ nrm x := norm_nonneg _

lemma nrm_neg (x : ℝ) : nrm (-x) = nrm x := by
  simp [nrm]

lemma nrm_add_le (x y : ℝ) : nrm (x + y) ≤ nrm x + nrm y := by
  simpa [nrm, AddCircle.coe_add] using norm_add_le (x : Circ) (y : Circ)

lemma nrm_le_half (x : ℝ) : nrm x ≤ 1 / 2 := by
  rw [nrm_eq]; exact abs_sub_round x

lemma coe_int_circ (n : ℤ) : ((n : ℝ) : Circ) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]; exact ⟨n, by simp⟩

lemma nrm_int (n : ℤ) : nrm (n : ℝ) = 0 := by
  simp [nrm, coe_int_circ]

lemma nrm_add_int (x : ℝ) (n : ℤ) : nrm (x + n) = nrm x := by
  simp [nrm]

lemma nrm_eq_abs {x : ℝ} (h : |x| ≤ 1 / 2) : nrm x = |x| := by
  simpa [nrm] using (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by simpa using h)

lemma nrm_le_abs (x : ℝ) : nrm x ≤ |x| := by
  by_cases h : |x| ≤ 1 / 2
  · exact (nrm_eq_abs h).le
  · exact (nrm_le_half x).trans (by linarith [not_le.mp h])

lemma nrm_nsmul_le (t : ℕ) (x : ℝ) : nrm ((t : ℝ) * x) ≤ t * nrm x := by
  have h : ‖t • (x : Circ)‖ ≤ t * ‖(x : Circ)‖ := norm_nsmul_le
  have e : t • (x : Circ) = (((t : ℝ) * x : ℝ) : Circ) := by
    rw [← AddCircle.coe_nsmul]; simp
  rw [e] at h
  simpa [nrm] using h

lemma nrm_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) : nrm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, nrm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nrm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (nrm_add_le _ _).trans (by linarith)

/-- If `x` is within `< 1/q` of an integer and `x = k / q`, then `q ∣ k`. -/
lemma dvd_of_nrm_lt (k : ℤ) (q : ℕ) (hq : 0 < q) (h : nrm ((k : ℝ) / q) < 1 / q) : (q : ℤ) ∣ k := by
  rw [nrm_eq] at h
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set r := round ((k : ℝ) / q)
  have h1 : |(k : ℝ) - r * q| < 1 := by
    have : |(k : ℝ) / q - r| * q < 1 := by
      calc |(k : ℝ) / q - r| * q < 1 / q * q := by gcongr
        _ = 1 := by field_simp
    have e : (k : ℝ) - r * q = ((k : ℝ) / q - r) * q := by field_simp
    rw [e, abs_mul, abs_of_pos hq']
    exact this
  have h2 : |k - r * q| < 1 := by
    have : ((|k - r * q| : ℤ) : ℝ) < 1 := by push_cast; exact h1
    exact_mod_cast this
  have h3 : k - r * q = 0 := by
    have := abs_lt.mp h2
    omega
  exact ⟨r, by linarith⟩

/-- The sup over the scale set `S`. -/
noncomputable def Pn (S : Set ℕ) (k : ℤ) : ℝ := ⨆ q : S, nrm ((k : ℝ) / (q : ℕ))

lemma bddAbove_Pn (S : Set ℕ) (k : ℤ) : BddAbove (Set.range fun q : S => nrm ((k : ℝ) / (q : ℕ))) :=
  ⟨1 / 2, by rintro _ ⟨q, rfl⟩; exact nrm_le_half _⟩

lemma le_Pn {S : Set ℕ} {q : ℕ} (hq : q ∈ S) (k : ℤ) : nrm ((k : ℝ) / q) ≤ Pn S k :=
  le_ciSup (bddAbove_Pn S k) (⟨q, hq⟩ : S)

lemma Pn_nonneg (S : Set ℕ) (k : ℤ) : 0 ≤ Pn S k :=
  Real.iSup_nonneg fun _ => nrm_nonneg _

lemma Pn_le {S : Set ℕ} (hS : S.Nonempty) {k : ℤ} {c : ℝ} (h : ∀ q ∈ S, nrm ((k : ℝ) / q) ≤ c) :
    Pn S k ≤ c := by
  have : Nonempty S := hS.to_subtype
  exact ciSup_le fun q => h q q.2

lemma Pn_nsmul_le {S : Set ℕ} (hS : S.Nonempty) (t : ℕ) (k : ℤ) :
    Pn S ((t : ℤ) * k) ≤ t * Pn S k := by
  apply Pn_le hS
  intro q hq
  have e : (((t : ℤ) * k : ℤ) : ℝ) / q = (t : ℝ) * ((k : ℝ) / q) := by push_cast; ring
  rw [e]
  exact (nrm_nsmul_le t _).trans (by gcongr; exact le_Pn hq k)

lemma Pn_pos {S : Set ℕ} (hpos : ∀ q ∈ S, 0 < q) (hinf : S.Infinite) {k : ℤ} (hk : k ≠ 0) :
    0 < Pn S k := by
  obtain ⟨q, hq, hqk⟩ := hinf.exists_gt (2 * k.natAbs)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hpos q hq
  have hle : |(k : ℝ) / q| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    have : (2 * k.natAbs : ℝ) < q := by exact_mod_cast hqk
    have h2 : (|(k : ℝ)|) = k.natAbs := by simp [Nat.cast_natAbs]
    rw [h2]; linarith
  have hpos' : 0 < |(k : ℝ) / q| := by
    rw [abs_pos]; exact div_ne_zero (by exact_mod_cast hk) hq0.ne'
  calc 0 < nrm ((k : ℝ) / q) := by rw [nrm_eq_abs hle]; exact hpos'
    _ ≤ Pn S k := le_Pn hq k

end MixedPrime
end LeanCheck
