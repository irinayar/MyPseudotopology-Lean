import Mathlib

/-!
# The spectral window: finite cosine-sum core (component 16 of the JA proof)

Lemma `lem:weighted-spectral` of `TVGaddmore_v27` compares `∫ Ψ_L dν`, with
`Ψ_L(θ) = ∑_{|h|<L} (L-|h|)^2 e^{ihθ}`, to a Fejér integral, for a nonnegative measure `ν` with nonnegative real
Fourier coefficients.  The measures that occur are finite sums of point masses, so everything below is stated for a
finite family of weights `w i ≥ 0` at angles `θ i`; the hypothesis "nonnegative real Fourier coefficients" is
`hpd`: `∑ w_i cos (h θ_i) ≥ 0` for every `h`.  No convergence of Fourier series is needed.

Checked here (no axiom, no `sorry`):

* `spectral_step`: `∑ w_i Ψ_L(θ_i) ≤ L ∑ w_i F_L(θ_i)` (the step `(L-|h|)^2 ≤ L (L-|h|)`);
* `fej_eq_sq`: `F_L(θ) = (∑_{j<L} cos jθ)^2 + (∑_{j<L} sin jθ)^2` (the Fejér kernel is a square, hence `≥ 0`);
* `fej_le_sq`: `F_L ≤ L^2`;
* `fej_mul`: `(2 - 2 cos θ) F_L(θ) = 2 - 2 cos (Lθ)`, hence `(2 - 2 cos θ) F_L(θ) ≤ 4` (the pointwise bound
  `F_L ≤ 1/ sin^2(θ/2)`).

Not checked here: the localization of mass (a positive-definite measure gives an interval of radius `1/(2L)` at most
twice the mass of the central interval of radius `1/L`), the summation over the blocks, and the passage from the
expected spectral measure to the weighted energy.
-/

namespace LeanCheck
namespace JASpectral

open Finset Real

/-- `F_L(θ) = L + 2 ∑_{h=1}^{L-1} (L-h) cos (hθ)` (unnormalized Fejér kernel). -/
noncomputable def Fej (L : ℕ) (θ : ℝ) : ℝ := L + 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) * Real.cos (h * θ)

/-- `Ψ_L(θ) = L^2 + 2 ∑_{h=1}^{L-1} (L-h)^2 cos (hθ)`. -/
noncomputable def Psi (L : ℕ) (θ : ℝ) : ℝ :=
  (L : ℝ) ^ 2 + 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 2 * Real.cos (h * θ)

lemma expand_sum {ι : Type*} (s : Finset ι) (w θ : ι → ℝ) (L : ℕ) (a : ℕ → ℝ) (K : ℝ) :
    ∑ i ∈ s, w i * (K + 2 * ∑ h ∈ Ico 1 L, a h * Real.cos (h * θ i)) =
      K * ∑ i ∈ s, w i + 2 * ∑ h ∈ Ico 1 L, a h * ∑ i ∈ s, w i * Real.cos (h * θ i) := by
  have hi : ∀ i, w i * (K + 2 * ∑ h ∈ Ico 1 L, a h * Real.cos (h * θ i)) =
      K * w i + 2 * ∑ h ∈ Ico 1 L, a h * (w i * Real.cos (h * θ i)) := by
    intro i
    rw [mul_add, show w i * (2 * ∑ h ∈ Ico 1 L, a h * Real.cos (h * θ i)) =
        2 * ∑ h ∈ Ico 1 L, a h * (w i * Real.cos (h * θ i)) from by
      rw [mul_left_comm, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro h _
      ring]
    ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  congr 2
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]

/-- **The spectral step.** -/
theorem spectral_step {ι : Type*} (s : Finset ι) (w θ : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hpd : ∀ h : ℕ, 0 ≤ ∑ i ∈ s, w i * Real.cos (h * θ i)) (L : ℕ) :
    ∑ i ∈ s, w i * Psi L (θ i) ≤ L * ∑ i ∈ s, w i * Fej L (θ i) := by
  unfold Psi Fej
  rw [expand_sum s w θ L (fun h => ((L : ℝ) - h) ^ 2) ((L : ℝ) ^ 2),
    expand_sum s w θ L (fun h => (L : ℝ) - h) (L : ℝ)]
  have hW : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hsum : ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 2 * ∑ i ∈ s, w i * Real.cos (h * θ i) ≤
      (L : ℝ) * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) * ∑ i ∈ s, w i * Real.cos (h * θ i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    rw [Finset.mem_Ico] at hh
    have hLh : (h : ℝ) + 1 ≤ L := by exact_mod_cast hh.2
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh.1
    have hc := hpd h
    have h0 : 0 ≤ (L : ℝ) - h := by linarith
    have : ((L : ℝ) - h) ^ 2 ≤ L * ((L : ℝ) - h) := by nlinarith
    nlinarith [mul_nonneg h0 hc]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) L) hW]

lemma fej_succ (L : ℕ) (θ : ℝ) :
    Fej (L + 1) θ = Fej L θ + (1 + 2 * ∑ h ∈ Ico 1 (L + 1), Real.cos (h * θ)) := by
  unfold Fej
  have e1 : ∑ h ∈ Ico 1 (L + 1), (((L + 1 : ℕ) : ℝ) - h) * Real.cos (h * θ) =
      ∑ h ∈ Ico 1 (L + 1), (((L : ℝ) - h) * Real.cos (h * θ) + Real.cos (h * θ)) := by
    apply Finset.sum_congr rfl
    intro h _
    push_cast
    ring
  rw [e1, Finset.sum_add_distrib]
  have e2 : ∑ h ∈ Ico 1 (L + 1), ((L : ℝ) - h) * Real.cos (h * θ) =
      ∑ h ∈ Ico 1 L, ((L : ℝ) - h) * Real.cos (h * θ) := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; simp
    · rw [Finset.sum_Ico_succ_top (by omega)]
      simp
  rw [e2]
  push_cast
  ring

lemma sum_cos_reflect (L : ℕ) (θ : ℝ) :
    ∑ j ∈ range L, Real.cos (((L : ℝ) - j) * θ) = ∑ h ∈ Ico 1 (L + 1), Real.cos (h * θ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  rw [← Finset.sum_range_reflect (fun j => Real.cos (((1 + j : ℕ) : ℝ) * θ)) L]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  congr 2
  have : 1 + (L - 1 - j) = L - j := by omega
  rw [this, Nat.cast_sub hj.le]

/-- The Fejér kernel is a sum of two squares. -/
theorem fej_eq_sq (L : ℕ) (θ : ℝ) :
    Fej L θ = (∑ j ∈ range L, Real.cos (j * θ)) ^ 2 + (∑ j ∈ range L, Real.sin (j * θ)) ^ 2 := by
  induction L with
  | zero => simp [Fej]
  | succ L ih =>
    rw [fej_succ, ih]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hcs : (∑ j ∈ range L, Real.cos (j * θ)) * Real.cos (L * θ) +
        (∑ j ∈ range L, Real.sin (j * θ)) * Real.sin (L * θ) =
        ∑ h ∈ Ico 1 (L + 1), Real.cos (h * θ) := by
      rw [← sum_cos_reflect, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [show ((L : ℝ) - j) * θ = L * θ - j * θ by ring, Real.cos_sub]
      ring
    have hsq : Real.cos (L * θ) ^ 2 + Real.sin (L * θ) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    push_cast
    nlinarith [hcs, hsq]

theorem fej_nonneg (L : ℕ) (θ : ℝ) : 0 ≤ Fej L θ := by
  rw [fej_eq_sq]; positivity

theorem fej_le_sq (L : ℕ) (θ : ℝ) : Fej L θ ≤ (L : ℝ) ^ 2 := by
  rw [fej_eq_sq]
  have h1 := sq_sum_le_card_mul_sum_sq (s := range L) (f := fun j : ℕ => Real.cos (j * θ))
  have h2 := sq_sum_le_card_mul_sum_sq (s := range L) (f := fun j : ℕ => Real.sin (j * θ))
  simp only [Finset.card_range] at h1 h2
  have h3 : ∑ j ∈ range L, (Real.cos (j * θ) ^ 2 + Real.sin (j * θ) ^ 2) = L := by
    simp [Real.cos_sq_add_sin_sq]
  rw [Finset.sum_add_distrib] at h3
  nlinarith [h1, h2, h3, Nat.cast_nonneg (α := ℝ) L]

/-- `D_L = 1 + 2 ∑_{h=1}^L cos hθ` satisfies `(2 - 2 cos θ) D_L = 2 cos Lθ - 2 cos (L+1)θ`. -/
lemma dirichlet_mul (L : ℕ) (θ : ℝ) :
    (2 - 2 * Real.cos θ) * (1 + 2 * ∑ h ∈ Ico 1 (L + 1), Real.cos (h * θ)) =
      2 * Real.cos (L * θ) - 2 * Real.cos ((L + 1) * θ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have e : (1 + 2 * (∑ h ∈ Ico 1 (L + 1), Real.cos (h * θ) + Real.cos (((L + 1 : ℕ) : ℝ) * θ))) =
        (1 + 2 * ∑ h ∈ Ico 1 (L + 1), Real.cos (h * θ)) + 2 * Real.cos (((L + 1 : ℕ) : ℝ) * θ) := by ring
    rw [e, mul_add, ih]
    push_cast
    have a1 : Real.cos (((L : ℝ) + 2) * θ) = Real.cos (((L : ℝ) + 1) * θ) * Real.cos θ -
        Real.sin (((L : ℝ) + 1) * θ) * Real.sin θ := by
      rw [show ((L : ℝ) + 2) * θ = ((L : ℝ) + 1) * θ + θ by ring, Real.cos_add]
    have a2 : Real.cos ((L : ℝ) * θ) = Real.cos (((L : ℝ) + 1) * θ) * Real.cos θ +
        Real.sin (((L : ℝ) + 1) * θ) * Real.sin θ := by
      rw [show (L : ℝ) * θ = ((L : ℝ) + 1) * θ - θ by ring, Real.cos_sub]
    rw [show ((L : ℝ) + 1 + 1) * θ = ((L : ℝ) + 2) * θ by ring]
    nlinarith [a1, a2]

/-- **Closed form**: `(2 - 2 cos θ) F_L(θ) = 2 - 2 cos (Lθ)`. -/
theorem fej_mul (L : ℕ) (θ : ℝ) : (2 - 2 * Real.cos θ) * Fej L θ = 2 - 2 * Real.cos (L * θ) := by
  induction L with
  | zero => simp [Fej]
  | succ L ih =>
    rw [fej_succ, mul_add, ih, dirichlet_mul]
    push_cast
    ring

/-- **Pointwise bound**: `(2 - 2 cos θ) F_L(θ) ≤ 4`, i.e. `F_L(θ) ≤ 1 / sin^2 (θ/2)`. -/
theorem fej_mul_le_four (L : ℕ) (θ : ℝ) : (2 - 2 * Real.cos θ) * Fej L θ ≤ 4 := by
  rw [fej_mul]
  nlinarith [Real.neg_one_le_cos (L * θ)]

#print axioms spectral_step
#print axioms fej_eq_sq
#print axioms fej_nonneg
#print axioms fej_le_sq
#print axioms fej_mul
#print axioms fej_mul_le_four

end JASpectral
end LeanCheck
