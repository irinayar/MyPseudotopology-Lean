import LeanCheck.TwoPrimesGolden

/-!
# A lower limit for the height of the rigidity lemma

At `θ = 1/2` every factor of the smoothing digits has modulus at least `9/10`, whatever the base.
Since `1/2` is far from the integers, any numbers of levels `Np, Nq` for which "a large product
forces `θ` near an integer" must satisfy `(9/10)^(Np+Nq) < η`.  With `η = exp (-4B/D²)` this
makes `Np + Nq` at least linear in `B`, so the largest square modulus has a logarithm which is at
least quadratic in `B`.

This limits the lemma for these digits.  It is not a bound for the witnesses themselves.
A first form of the obstruction (at `θ = 1/3`, bases 2 and 3) is due to Codex of OpenAI.
-/

namespace TwoPrimesHeightLimit

open Finset Real TwoPrimesEffective TwoPrimesSmoothing

lemma digit_half (J : ℕ) : digit J (1 / 2) = (-1 : ℝ) ^ J / (2 * J + 1) := by
  have h := dirichlet J (1 / 2)
  have h1 : sin (π * (1 / 2)) = 1 := by
    rw [show π * (1 / 2) = π / 2 by ring, sin_pi_div_two]
  have h2 : sin (π * (2 * J + 1) * (1 / 2)) = (-1 : ℝ) ^ J := by
    rw [show π * (2 * J + 1) * (1 / 2) = (J : ℝ) * π + π / 2 by ring, sin_add_pi_div_two,
      cos_nat_mul_pi]
  rw [h1, h2, one_mul] at h
  unfold digit
  rw [h]

/-- **At one half every factor has modulus at least `9/10`.** -/
lemma abs_phi_half (J : ℕ) : 9 / 10 ≤ |phi J (1 / 2)| := by
  have hc : cos (2 * π * J * (1 / 2)) = (-1 : ℝ) ^ J := by
    rw [show 2 * π * (J : ℝ) * (1 / 2) = (J : ℝ) * π by ring, cos_nat_mul_pi]
  have hform : phi J (1 / 2) = (-1 : ℝ) ^ J * (9 / 10 + 1 / 10 / (2 * J + 1)) := by
    unfold phi
    rw [hc, digit_half]
    ring
  have hpos : (0 : ℝ) ≤ 1 / 10 / (2 * J + 1) := by positivity
  rw [hform, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by linarith)]
  linarith

lemma phi_sub_int' (J : ℕ) (x : ℝ) (z : ℤ) : phi J (x - z) = phi J x := by
  unfold phi
  rw [digit_sub_int]
  have : 2 * π * (J : ℝ) * (x - z) = 2 * π * J * x - (((J : ℤ) * z : ℤ) : ℝ) * (2 * π) := by
    push_cast; ring
  rw [this, cos_sub_int_mul_two_pi]

lemma phi_zero (J : ℕ) : phi J 0 = 1 := by
  have hd : digit J 0 = 1 := by
    unfold digit
    simp only [mul_zero, cos_zero, sum_const, nsmul_eq_mul, mul_one, card_digits]
    push_cast
    exact div_self (by positivity)
  unfold phi
  rw [hd, mul_zero, cos_zero]
  norm_num

/-- Every half of a natural number gives a factor of modulus at least `9/10`. -/
lemma abs_phi_half_nat (J m : ℕ) : 9 / 10 ≤ |phi J ((m : ℝ) / 2)| := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
  · have h : (m : ℝ) / 2 = 0 - ((-(k : ℤ) : ℤ) : ℝ) := by
      rw [hk]; push_cast; ring
    rw [h, phi_sub_int', phi_zero, abs_one]
    norm_num
  · have h : (m : ℝ) / 2 = 1 / 2 - ((-(k : ℤ) : ℤ) : ℝ) := by
      rw [hk]; push_cast; ring
    rw [h, phi_sub_int']
    exact abs_phi_half J

/-- **The product at one half decays at most like `(9/10)^N`.** -/
theorem prodPhi_half_ge (p D N : ℕ) : (9 / 10 : ℝ) ^ N ≤ |prodPhi p D N (1 / 2)| := by
  unfold prodPhi
  rw [abs_prod]
  calc (9 / 10 : ℝ) ^ N = ∏ _n ∈ Finset.range N, (9 / 10 : ℝ) := by
        rw [prod_const, card_range]
    _ ≤ ∏ n ∈ Finset.range N, |phi (range' p D n) ((p : ℝ) ^ (n ^ 2) * (1 / 2))| := by
        refine prod_le_prod₀ (fun _ _ => by norm_num) (fun n _ => ?_)
        have h : (p : ℝ) ^ (n ^ 2) * (1 / 2) = ((p ^ (n ^ 2) : ℕ) : ℝ) / 2 := by
          push_cast; ring
        rw [h]
        exact abs_phi_half_nat _ _

lemma half_far {x0 : ℝ} (hx : x0 ≠ 0) :
    ¬ ∃ z : ℤ, |(1 / 2 : ℝ) - z| ≤ exp (-(2 * x0 ^ 2)) / 2 := by
  rintro ⟨z, hz⟩
  have hlt : exp (-(2 * x0 ^ 2)) < 1 := by
    rw [exp_lt_one_iff]
    have : 0 < x0 ^ 2 := by positivity
    linarith
  have hfar : (1 / 2 : ℝ) ≤ |(1 / 2 : ℝ) - z| := by
    rcases le_or_gt z 0 with h | h
    · have : (z : ℝ) ≤ 0 := by exact_mod_cast h
      exact le_trans (by linarith) (le_abs_self _)
    · have : (1 : ℝ) ≤ z := by exact_mod_cast (by omega : (1 : ℤ) ≤ z)
      exact le_trans (by linarith) (neg_le_abs _)
  linarith

/-- **A limit for every proof of rigidity with these digits.**  If a product of size `η` forces
`θ` near an integer, then `(9/10)^(Np+Nq) < η`. -/
theorem height_limit {p q D Np Nq : ℕ} {η x0 : ℝ} (hx : x0 ≠ 0)
    (h : ∀ θ : ℝ, η ≤ |prodPhi p D Np θ| * |prodPhi q D Nq θ| →
      ∃ z : ℤ, |θ - z| ≤ exp (-(2 * x0 ^ 2)) / 2) :
    (9 / 10 : ℝ) ^ (Np + Nq) < η := by
  by_contra hcon
  push Not at hcon
  refine half_far hx (h (1 / 2) (le_trans hcon ?_))
  rw [pow_add]
  exact mul_le_mul (prodPhi_half_ge p D Np) (prodPhi_half_ge q D Nq) (by positivity)
    (abs_nonneg _)

/-- With the threshold of the rigidity lemma the number of levels is at least linear in `B`. -/
theorem levels_limit {p q D B Np Nq : ℕ} (hD : 0 < D) {x0 : ℝ} (hx : x0 ≠ 0)
    (h : ∀ θ : ℝ, exp (-(4 * B / (D : ℝ) ^ 2)) ≤ |prodPhi p D Np θ| * |prodPhi q D Nq θ| →
      ∃ z : ℤ, |θ - z| ≤ exp (-(2 * x0 ^ 2)) / 2) :
    4 * (B : ℝ) / ((D : ℝ) ^ 2 * log (10 / 9)) < Np + Nq := by
  have h1 := height_limit hx h
  have h2 := log_lt_log (by positivity) h1
  rw [log_pow, log_exp] at h2
  have h3 : log (9 / 10 : ℝ) = -log (10 / 9) := by
    rw [← log_inv]; norm_num
  rw [h3] at h2
  have hL : 0 < log (10 / 9 : ℝ) := log_pos (by norm_num)
  have hD2 : (0 : ℝ) < (D : ℝ) ^ 2 := by
    have : (0 : ℝ) < D := by exact_mod_cast hD
    positivity
  push_cast at h2 ⊢
  rw [div_lt_iff₀ (mul_pos hD2 hL)]
  have h4 : 4 * (B : ℝ) / (D : ℝ) ^ 2 < ((Np : ℝ) + Nq) * log (10 / 9) := by linarith
  rw [div_lt_iff₀ hD2] at h4
  nlinarith [h4]

/-- **The logarithmic height is at least quadratic in `B`.** -/
theorem quadratic_height {p q D B Np Nq : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hD : 0 < D) {x0 : ℝ}
    (hx : x0 ≠ 0)
    (h : ∀ θ : ℝ, exp (-(4 * B / (D : ℝ) ^ 2)) ≤ |prodPhi p D Np θ| * |prodPhi q D Nq θ| →
      ∃ z : ℤ, |θ - z| ≤ exp (-(2 * x0 ^ 2)) / 2) :
    (2 * (B : ℝ) / ((D : ℝ) ^ 2 * log (10 / 9))) ^ 2 * log 2
      ≤ max ((Np : ℝ) ^ 2 * log p) ((Nq : ℝ) ^ 2 * log q) := by
  have h1 := levels_limit hD hx h
  set X := 2 * (B : ℝ) / ((D : ℝ) ^ 2 * log (10 / 9)) with hX
  have h2 : 2 * X < (Np : ℝ) + Nq := by
    have : 2 * X = 4 * (B : ℝ) / ((D : ℝ) ^ 2 * log (10 / 9)) := by rw [hX]; ring
    rw [this]; exact h1
  have hL : 0 < log (10 / 9 : ℝ) := log_pos (by norm_num)
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have key : ∀ (l N : ℕ), 2 ≤ l → X ≤ (N : ℝ) → X ^ 2 * log 2 ≤ (N : ℝ) ^ 2 * log l := by
    intro l N hl hN
    have hll : log (2 : ℝ) ≤ log l := log_le_log (by norm_num) (by exact_mod_cast hl)
    exact mul_le_mul (pow_le_pow_left₀ hX0 hN 2) hll hlog2.le (by positivity)
  rcases le_total (Np : ℝ) Nq with hle | hle
  · exact le_trans (key q Nq hq (by linarith)) (le_max_right _ _)
  · exact le_trans (key p Np hp (by linarith)) (le_max_left _ _)

end TwoPrimesHeightLimit
