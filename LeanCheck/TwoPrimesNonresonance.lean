import Mathlib

/-!
# Far-apart top steps: non-resonance holds

For primes `p ≠ q` and a radius `1/D`, let `u = q^(s^2)` and `v = p^(t^2)` be the two top steps.

* `U_upper`, `U_lower`: the largest element `U` of the lower digit set lies between
  (step)/(2D) and (step)/D.
* `bound`: if `v ≥ 20 D u` and `X ≥ D v`, then for every nonzero integer pair the expression
  `c (1 + (2 √A₀ + 1 + 2/G) / A_eff)` is at most `1.85`, where `c` is any number in the
  enclosure of the continuous energy and `G` the gauge of the pair. (Taking the minimizing pair,
  this is the quantity `Γ_D`.)
* `exists_far`: heights with `v ≥ K D u` exist for all large `D`.
* `nonresonance`: the two statements together, with the actual digit-set data.

**Assumed from the first article, not formalized here:** the enclosure
`C₀ - 2XW/Q² ≤ C_cont ≤ C₀`, the formulas for `A₀` and `H(0)` (these enter as definitions), and
the inequality `C_model ≤ Γ_D` (geometry of numbers).
-/

namespace TwoPrimesNonresonance

open Finset Real

/-! ## The lower hull -/

/-- The largest element of the digit set `T_N` for the base `q` at radius `1/D`. -/
def U (q D N : ℕ) : ℕ := ∑ k ∈ range N, (q ^ (2 * k + 1) / D) * q ^ (k ^ 2)

lemma U_upper {q D : ℕ} (_hq : 0 < q) (_hD : 0 < D) (hreg : ∀ k, ¬ D ∣ q ^ k) (N : ℕ) :
    D * U q D N < q ^ (N ^ 2) := by
  induction N with
  | zero => simp [U]
  | succ N ih =>
    have hmod : q ^ (2 * N + 1) % D ≠ 0 := fun h => hreg _ (Nat.dvd_of_mod_eq_zero h)
    have hsplit := Nat.div_add_mod (q ^ (2 * N + 1)) D
    have hlt : D * (q ^ (2 * N + 1) / D) + 1 ≤ q ^ (2 * N + 1) := by omega
    have hU : U q D (N + 1) = U q D N + (q ^ (2 * N + 1) / D) * q ^ (N ^ 2) := by
      unfold U; rw [sum_range_succ]
    have hpow : q ^ ((N + 1) ^ 2) = q ^ (2 * N + 1) * q ^ (N ^ 2) := by
      rw [← pow_add]; congr 1; ring
    rw [hU, hpow, mul_add, ← mul_assoc]
    calc D * U q D N + D * (q ^ (2 * N + 1) / D) * q ^ (N ^ 2)
        < q ^ (N ^ 2) + D * (q ^ (2 * N + 1) / D) * q ^ (N ^ 2) := by omega
      _ = (D * (q ^ (2 * N + 1) / D) + 1) * q ^ (N ^ 2) := by ring
      _ ≤ q ^ (2 * N + 1) * q ^ (N ^ 2) := Nat.mul_le_mul_right _ hlt

lemma U_lower {q D M : ℕ} (hD : 0 < D) (h : 2 * D ≤ q ^ (2 * M + 1)) :
    q ^ ((M + 1) ^ 2) ≤ 2 * D * U q D (M + 1) := by
  have hsplit := Nat.div_add_mod (q ^ (2 * M + 1)) D
  have hmod := Nat.mod_lt (q ^ (2 * M + 1)) hD
  have h2 : q ^ (2 * M + 1) ≤ 2 * D * (q ^ (2 * M + 1) / D) := by
    have : 2 * D * (q ^ (2 * M + 1) / D) = 2 * (D * (q ^ (2 * M + 1) / D)) := by ring
    omega
  have hterm : (q ^ (2 * M + 1) / D) * q ^ (M ^ 2) ≤ U q D (M + 1) := by
    unfold U; rw [sum_range_succ]; omega
  have hpow : q ^ ((M + 1) ^ 2) = q ^ (2 * M + 1) * q ^ (M ^ 2) := by
    rw [← pow_add]; congr 1; ring
  rw [hpow]
  calc q ^ (2 * M + 1) * q ^ (M ^ 2)
      ≤ (2 * D * (q ^ (2 * M + 1) / D)) * q ^ (M ^ 2) := Nat.mul_le_mul_right _ h2
    _ = 2 * D * ((q ^ (2 * M + 1) / D) * q ^ (M ^ 2)) := by ring
    _ ≤ 2 * D * U q D (M + 1) := Nat.mul_le_mul_left _ hterm

/-! ## The bound at far-apart steps -/

/-- The gauge of an integer pair for the body of the cluster model. -/
noncomputable def gauge (u v a b W : ℝ) (m n : ℤ) : ℝ :=
  max (|(m : ℝ)| / a) (max (|(n : ℝ)| / b) (|(m : ℝ) * u - n * v| / W))

lemma gauge_lower {u v a b W X D : ℝ} (hu : 0 < u) (hD : 100 ≤ D) (hv : 20 * D * u ≤ v)
    (hX : D * v ≤ X) (ha : 0 < a) (haX : u * a ≤ X * (1 + 2 / D))
    (hW0 : 0 < W) (hW1 : W ≤ 2 * (u + v) / D) (m n : ℤ) (hmn : (m, n) ≠ (0, 0)) :
    u / W ≤ gauge u v a b W m n ∨ 1 ≤ gauge u v a b W m n ∨
      0.95 * v / X ≤ gauge u v a b W m n := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  by_cases hn : n = 0
  · have hm : m ≠ 0 := fun h => hmn (by rw [h, hn])
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
    left
    have : u / W ≤ |(m : ℝ) * u - n * v| / W := by
      rw [hn]
      simp only [Int.cast_zero, zero_mul, sub_zero]
      rw [abs_mul, abs_of_pos hu]
      exact (div_le_div_iff_of_pos_right hW0).mpr (le_mul_of_one_le_left hu.le hm1)
    exact this.trans ((le_max_right _ _).trans (le_max_right _ _))
  · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    by_cases hbig : W ≤ |(m : ℝ) * u - n * v|
    · right; left
      have : (1 : ℝ) ≤ |(m : ℝ) * u - n * v| / W := by
        rw [le_div_iff₀ hW0, one_mul]; exact hbig
      exact this.trans ((le_max_right _ _).trans (le_max_right _ _))
    · right; right
      push Not at hbig
      have huv : u ≤ v / 2000 := by
        have : 20 * 100 * u ≤ 20 * D * u := by
          have := mul_le_mul_of_nonneg_right hD hu.le
          nlinarith
        linarith
      have hW2 : W ≤ 0.03 * v := by
        refine hW1.trans ?_
        rw [div_le_iff₀ hD0]
        nlinarith [mul_le_mul_of_nonneg_left hD hv0.le]
      have h1 : v ≤ |(n : ℝ) * v| := by
        rw [abs_mul, abs_of_pos hv0]
        exact le_mul_of_one_le_left hv0.le hn1
      have h2 : |(n : ℝ) * v| ≤ |(m : ℝ) * u| + |(m : ℝ) * u - n * v| := by
        have := abs_sub_abs_le_abs_sub ((n : ℝ) * v) ((m : ℝ) * u)
        rw [abs_sub_comm ((n : ℝ) * v)] at this
        linarith
      have h3 : 0.97 * v ≤ |(m : ℝ)| * u := by
        rw [abs_mul (m : ℝ) u, abs_of_pos hu] at h2
        linarith
      have h4 : 0.95 * v / X ≤ |(m : ℝ)| / a := by
        rw [div_le_div_iff₀ hX0 ha]
        have h5 : u * a ≤ X * 1.02 := by
          refine haX.trans (mul_le_mul_of_nonneg_left ?_ hX0.le)
          have : (2 : ℝ) / D ≤ 0.02 := by rw [div_le_iff₀ hD0]; linarith
          linarith
        have h6 : 0.97 * v * a ≤ |(m : ℝ)| * u * a := mul_le_mul_of_nonneg_right h3 ha.le
        have h7 : |(m : ℝ)| * (u * a) ≤ |(m : ℝ)| * (X * 1.02) :=
          mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
        have h8 : 0.97 * (v * a) ≤ |(m : ℝ)| * X * 1.02 := by nlinarith
        have h9 : 0 ≤ v * a := by positivity
        nlinarith
      exact h4.trans (le_max_left _ _)

set_option maxHeartbeats 1000000 in
/-- The bound at far-apart steps. `a = J_A + 1`, `b = J_B + 1`; `c` is any number in the
enclosure of the continuous energy. -/
theorem bound {u v D X UA UB a b c : ℝ} (hD : 100 ≤ D) (hu : 0 < u) (hv : 20 * D * u ≤ v)
    (hX : D * v ≤ X)
    (hUA0 : u / (2 * D) ≤ UA) (hUA1 : UA ≤ u / D)
    (hUB0 : v / (2 * D) ≤ UB) (hUB1 : UB ≤ v / D)
    (ha : 0 < a) (hb : 0 < b)
    (hPA0 : X ≤ u * a) (hPA1 : u * a ≤ X * (1 + 2 / D))
    (hPB0 : X ≤ v * b) (hPB1 : v * b ≤ X * (1 + 2 / D))
    (W P Q C0 H0 A0 Aeff : ℝ) (hW : W = 2 * (UA + UB))
    (hP : P = min (u * a) (v * b)) (hQ : Q = max (u * a) (v * b))
    (hC0 : C0 = 2 * X * (3 * Q - P) / (3 * Q ^ 2))
    (hc0 : C0 - 2 * X * W / Q ^ 2 ≤ c) (hc1 : c ≤ C0)
    (hH0 : H0 = (3 * UB - UA) / (6 * UB ^ 2))
    (hA0 : A0 = (4 * P * W - (max 0 (W - Q + P)) ^ 2 + (max 0 (W - P - Q)) ^ 2) / (u * v))
    (hAeff : Aeff = c * (a * b) / (2 * X * H0))
    (m n : ℤ) (hmn : (m, n) ≠ (0, 0)) :
    c * (1 + (2 * √A0 + 1 + 2 / gauge u v a b W m n) / Aeff) ≤ 1.85 := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  have h2D : (2 : ℝ) / D ≤ 0.02 := by rw [div_le_iff₀ hD0]; linarith
  have huv : u ≤ v / 2000 := by
    have := mul_le_mul_of_nonneg_right hD hu.le
    nlinarith
  have hvX : 100 * v ≤ X := le_trans (mul_le_mul_of_nonneg_right hD hv0.le) hX
  -- the two hull lengths
  have hP0 : X ≤ P := hP ▸ le_min hPA0 hPB0
  have hPQ : P ≤ Q := hP ▸ hQ ▸ min_le_max
  have hQ0 : X ≤ Q := hP0.trans hPQ
  have hs : X * (1 + 2 / D) ≤ X * 1.02 := mul_le_mul_of_nonneg_left (by linarith) hX0.le
  have hQ1 : Q ≤ X * 1.02 := (hQ ▸ max_le hPA1 hPB1).trans hs
  have hP1 : P ≤ X * 1.02 := hPQ.trans hQ1
  have hQpos : 0 < Q := lt_of_lt_of_le hX0 hQ0
  -- the width
  have hW0 : 0 < W := by
    have h1 : 0 < u / (2 * D) := by positivity
    have h2 : 0 < v / (2 * D) := by positivity
    rw [hW]; linarith
  have hW1 : W ≤ 2 * (u + v) / D := by
    rw [hW, mul_div_assoc, add_div]; linarith
  have hWv : W ≤ 0.03 * v := by
    refine hW1.trans ?_
    rw [div_le_iff₀ hD0]
    nlinarith [mul_le_mul_of_nonneg_left hD hv0.le]
  have hWX : W < X := by linarith
  -- the continuous energy
  have hC0up : C0 ≤ 1.347 := by
    rw [hC0, div_le_iff₀ (by positivity)]
    have h1 : 2 * X * (3 * Q - P) ≤ 2 * X * (3 * Q - X) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith [mul_nonneg (sub_nonneg.mpr hQ0) hX0.le, sq_nonneg (Q - X), sq_nonneg X]
  have hC0low : 1.307 ≤ C0 := by
    rw [hC0, le_div_iff₀ (by positivity)]
    have h1 : 2 * X * (2 * Q) ≤ 2 * X * (3 * Q - P) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : 3.921 * Q ≤ 4 * X := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hQpos.le
    linarith
  have hsmall : 2 * X * W / Q ^ 2 ≤ 0.001 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 2 * X * W ≤ 2 * Q * W := by
      have := mul_le_mul_of_nonneg_right hQ0 hW0.le
      linarith
    have h2 : 2000 * W ≤ Q := by
      have h3 : W * D ≤ 2 * (u + v) := by
        have := (le_div_iff₀ hD0).mp hW1
        linarith
      have h4 : W * D ≤ 2.001 * v := by linarith
      have h5 : 100 * W ≤ W * D := by
        have := mul_le_mul_of_nonneg_left hD hW0.le
        linarith
      have h6 : W ≤ 0.02001 * v := by linarith
      have h7 : 2000 * W ≤ 40.02 * v := by linarith
      linarith
    have h8 := mul_le_mul_of_nonneg_left h2 hQpos.le
    linarith
  have hclow : 1.3 ≤ c := by linarith
  have hcup : c ≤ 1.347 := hc1.trans hC0up
  have hc0' : 0 < c := by linarith
  -- the effective area
  have hUB0' : 0 < UB := lt_of_lt_of_le (by positivity) hUB0
  have hUAUB : UA ≤ UB := by
    have h1 : u / D ≤ v / (2 * D) := by
      rw [div_le_div_iff₀ hD0 (by positivity)]
      have := mul_le_mul_of_nonneg_right huv hD0.le
      nlinarith [mul_pos hv0 hD0]
    exact hUA1.trans (h1.trans hUB0)
  have hH0pos : 0 < H0 := by
    rw [hH0]; exact div_pos (by linarith) (by positivity)
  have hH0up : H0 ≤ D / v := by
    have h1 : H0 ≤ 1 / (2 * UB) := by
      rw [hH0, div_le_div_iff₀ (by positivity) (by positivity)]
      have hUA0' : 0 ≤ UA := le_trans (by positivity) hUA0
      nlinarith [mul_nonneg hUA0' hUB0'.le]
    have h2 : 1 / (2 * UB) ≤ D / v := by
      rw [div_le_div_iff₀ (by positivity) hv0]
      have := (div_le_iff₀ (show (0:ℝ) < 2 * D by positivity)).mp hUB0
      nlinarith
    exact h1.trans h2
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X / (u * D) := ⟨_, rfl⟩
  have hXY : X = Y * (u * D) := by rw [hY]; field_simp
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hY2000 : 2000 ≤ Y := by
    rw [hY, le_div_iff₀ (by positivity)]
    have h1 : D * (20 * D * u) ≤ X := le_trans (mul_le_mul_of_nonneg_left hv hD0.le) hX
    have h2 : 100 * (20 * D * u) ≤ D * (20 * D * u) :=
      mul_le_mul_of_nonneg_right hD (by positivity)
    linarith
  have hab : X ^ 2 ≤ (a * b) * (u * v) := by
    have h1 : X * X ≤ (u * a) * (v * b) := mul_le_mul hPA0 hPB0 hX0.le (by positivity)
    nlinarith
  have hAeff_low : 0.65 * Y ≤ Aeff := by
    rw [hAeff, le_div_iff₀ (by positivity)]
    have h1 : 0.65 * Y * (2 * X * H0) ≤ 0.65 * Y * (2 * X * (D / v)) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH0up (by linarith)) (by positivity)
    have h2 : 0.65 * Y * (2 * X * (D / v)) = 1.3 * (X ^ 2 / (u * v)) := by
      rw [hY]; field_simp; ring
    have h3 : X ^ 2 / (u * v) ≤ a * b := by
      rw [div_le_iff₀ (by positivity)]; exact hab
    have h4 : 1.3 * (X ^ 2 / (u * v)) ≤ c * (a * b) :=
      mul_le_mul hclow h3 (by positivity) hc0'.le
    linarith
  have hAeff0 : 0 < Aeff := lt_of_lt_of_le (by positivity) hAeff_low
  -- the area
  have hA0up : A0 ≤ 9 * Y := by
    have hz : max 0 (W - P - Q) = 0 := max_eq_left (by linarith)
    have h1 : A0 ≤ 4 * P * W / (u * v) := by
      rw [hA0, hz]
      refine (div_le_div_iff_of_pos_right (by positivity)).mpr ?_
      nlinarith [sq_nonneg (max 0 (W - Q + P))]
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h2 : P * W ≤ (X * 1.02) * (2 * (u + v) / D) :=
      mul_le_mul hP1 hW1 hW0.le (by positivity)
    have h3 : (X * 1.02) * (2 * (u + v) / D) = 2.04 * Y * u * (u + v) := by
      rw [hXY]; field_simp; ring
    have h4 : u + v ≤ 1.0005 * v := by linarith
    have h5 : 2.04 * Y * u * (u + v) ≤ 2.04 * Y * u * (1.0005 * v) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : 0 ≤ Y * u * v := by positivity
    nlinarith
  have hsqrt : √A0 ≤ 3 * √Y := by
    have h1 : √A0 ≤ √(9 * Y) := Real.sqrt_le_sqrt hA0up
    rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)] at h1
    exact h1
  have hsY : 44.7 ≤ √Y := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsY2 : √Y * √Y = Y := Real.mul_self_sqrt hY0.le
  obtain ⟨G, hGdef⟩ : ∃ G, G = gauge u v a b W m n := ⟨_, rfl⟩
  have hGnn : 0 ≤ G := by
    rw [hGdef]; exact le_trans (div_nonneg (abs_nonneg _) ha.le) (le_max_left _ _)
  have hGlow : u / W ≤ G ∨ 1 ≤ G ∨ 0.95 * v / X ≤ G := by
    rw [hGdef]; exact gauge_lower (b := b) hu hD hv hX ha hPA1 hW0 hW1 m n hmn
  rw [← hGdef]
  -- the three terms
  have t1 : 2 * √A0 / Aeff ≤ 0.207 := by
    rw [div_le_iff₀ hAeff0]
    have h1 : 6 * √Y ≤ 0.207 * (0.65 * Y) := by
      have h2 : 44.7 * √Y ≤ √Y * √Y := mul_le_mul_of_nonneg_right hsY (Real.sqrt_nonneg _)
      rw [hsY2] at h2
      linarith
    have h3 : 0.207 * (0.65 * Y) ≤ 0.207 * Aeff := mul_le_mul_of_nonneg_left hAeff_low (by norm_num)
    linarith only [h1, h3, hsqrt]
  have t2 : 1 / Aeff ≤ 0.001 := by
    rw [div_le_iff₀ hAeff0]; linarith only [hAeff_low, hY2000]
  have t3 : 2 / G / Aeff ≤ 0.163 := by
    have key : 2 ≤ 0.163 * (G * Aeff) := by
      have hmulY : ∀ g : ℝ, 0 ≤ g → g ≤ G → g * (0.65 * Y) ≤ G * Aeff := fun g _ hle =>
        mul_le_mul hle hAeff_low (mul_nonneg (by norm_num) hY0.le) hGnn
      rcases hGlow with h | h | h
      · have h1 := hmulY (u / W) (div_nonneg hu.le hW0.le) h
        have h2 : 32 ≤ u / W * (0.65 * Y) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hW0]
          have h3 : W * D ≤ 2.001 * v := by
            have h3a := (le_div_iff₀ hD0).mp hW1
            linarith only [h3a, huv]
          have h4 : u * (0.65 * Y) = 0.65 * X / D := by
            rw [hXY]; field_simp
          rw [h4, le_div_iff₀ hD0]
          have h5 : 0.65 * (D * v) ≤ 0.65 * X := mul_le_mul_of_nonneg_left hX (by norm_num)
          have h6 : 100 * v ≤ D * v := mul_le_mul_of_nonneg_right hD hv0.le
          linarith only [h3, h5, h6, hv0]
        linarith only [h1, h2]
      · have h1 := hmulY 1 zero_le_one h
        linarith only [h1, hY2000]
      · have h1 := hmulY (0.95 * v / X) (div_nonneg (mul_nonneg (by norm_num) hv0.le) hX0.le) h
        have h2 : 12.3 ≤ 0.95 * v / X * (0.65 * Y) := by
          have h3 : 0.95 * v / X * (0.65 * Y) = 0.95 * 0.65 * (v / (u * D)) := by
            rw [hY]; field_simp
          have h4 : 20 ≤ v / (u * D) := by
            rw [le_div_iff₀ (mul_pos hu hD0)]; linarith only [hv]
          rw [h3]; linarith only [h4]
        linarith only [h1, h2]
    have hG0 : 0 < G := by
      rcases lt_or_eq_of_le hGnn with h | h
      · exact h
      · rw [← h, zero_mul, mul_zero] at key
        linarith only [key]
    rw [div_div, div_le_iff₀ (mul_pos hG0 hAeff0)]
    exact key
  have hsum : (2 * √A0 + 1 + 2 / G) / Aeff ≤ 0.207 + 0.001 + 0.163 := by
    rw [add_div, add_div]; linarith only [t1, t2, t3]
  have h1 : 1 + (2 * √A0 + 1 + 2 / G) / Aeff ≤ 1.371 := by linarith only [hsum]
  have h2 : 0 ≤ 1 + (2 * √A0 + 1 + 2 / G) / Aeff := by
    have h3 : 0 ≤ 2 / G := div_nonneg (by norm_num) hGnn
    have h4 : 0 ≤ 2 * √A0 := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have h5 : 0 ≤ (2 * √A0 + 1 + 2 / G) / Aeff :=
      div_nonneg (by linarith only [h3, h4]) hAeff0.le
    linarith only [h5]
  calc c * (1 + (2 * √A0 + 1 + 2 / G) / Aeff)
      ≤ 1.347 * 1.371 := mul_le_mul hcup h1 h2 (by norm_num)
    _ ≤ 1.85 := by norm_num

/-! ## Existence of far-apart heights -/

/-- A bounded number of steps of an irrational rotation comes close to every point. -/
lemma rotation {γ : ℝ} (hγ : Irrational γ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ K : ℕ, ∀ y : ℝ, ∃ j : ℕ, j ≤ K ∧ Int.fract (j * γ - y) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨k, hk0, -, hk⟩ := Real.exists_nat_abs_mul_sub_round_le γ (n := n + 1) (by omega)
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = k * γ - round (k * γ) := ⟨_, rfl⟩
  have hdne : d ≠ 0 := by
    rw [hd]
    have : Irrational (k * γ) := hγ.natCast_mul (by omega)
    exact sub_ne_zero.mpr (this.ne_int _)
  have hdε : |d| < ε := by
    rw [hd]
    refine lt_of_le_of_lt hk (lt_of_le_of_lt ?_ hn)
    refine one_div_le_one_div_of_le (by positivity) ?_
    push_cast; linarith
  have hd0 : 0 < |d| := abs_pos.mpr hdne
  refine ⟨⌈2 / |d|⌉₊ * k, fun y => ?_⟩
  have hstep : ∀ i : ℕ, ∀ z : ℤ, Int.fract (((i * k : ℕ) : ℝ) * γ - y)
      = Int.fract (i * d - y + z) := by
    intro i z
    have : (((i * k : ℕ) : ℝ) * γ - y) = (i * d - y + z) + ((i * round (k * γ) - z : ℤ) : ℝ) := by
      rw [hd]; push_cast; ring
    rw [this, Int.fract_add_intCast]
  rcases lt_or_gt_of_ne hdne with hneg | hpos
  · -- d < 0
    have he : |d| = -d := abs_of_neg hneg
    have hed : 0 < -d := by linarith
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Int.fract (-y) := ⟨_, rfl⟩
    have hz0 : 0 ≤ z := hz ▸ Int.fract_nonneg _
    have hz1 : z < 1 := hz ▸ Int.fract_lt_one _
    refine ⟨⌊(z + 1) / (-d)⌋₊ * k, Nat.mul_le_mul_right _ ?_, ?_⟩
    · refine (Nat.floor_le_ceil _).trans (Nat.ceil_le_ceil ?_)
      rw [he]; exact (div_le_div_iff_of_pos_right hed).mpr (by linarith)
    · have h0 : 0 ≤ (z + 1) / (-d) := div_nonneg (by linarith) hed.le
      have h1 : (⌊(z + 1) / (-d)⌋₊ : ℝ) ≤ (z + 1) / (-d) := Nat.floor_le h0
      have h2 : (z + 1) / (-d) < ⌊(z + 1) / (-d)⌋₊ + 1 := Nat.lt_floor_add_one _
      rw [le_div_iff₀ hed] at h1
      rw [div_lt_iff₀ hed] at h2
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = z + 1 - ⌊(z + 1) / (-d)⌋₊ * (-d) := ⟨_, rfl⟩
      have ht0 : 0 ≤ t := by rw [ht]; linarith
      have ht1 : t < ε := by
        have : t < -d := by rw [ht]; linarith
        rw [he] at hdε; linarith
      rw [hstep _ (1 - ⌊-y⌋)]
      have heq : (⌊(z + 1) / (-d)⌋₊ : ℝ) * d - y + ((1 - ⌊-y⌋ : ℤ) : ℝ) = t := by
        have hfr : z = -y - (⌊-y⌋ : ℝ) := by rw [hz]; rfl
        rw [ht, hfr]; push_cast; ring
      rw [heq, Int.fract_eq_self.mpr ⟨ht0, lt_trans ht1 hε1⟩]
      exact ht1
  · -- d > 0
    have he : |d| = d := abs_of_pos hpos
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Int.fract y := ⟨_, rfl⟩
    have hz0 : 0 ≤ z := hz ▸ Int.fract_nonneg _
    have hz1 : z < 1 := hz ▸ Int.fract_lt_one _
    refine ⟨⌈z / d⌉₊ * k, Nat.mul_le_mul_right _ ?_, ?_⟩
    · refine Nat.ceil_le_ceil ?_
      rw [he]; exact (div_le_div_iff_of_pos_right hpos).mpr (by linarith)
    · have h1 : z / d ≤ ⌈z / d⌉₊ := Nat.le_ceil _
      have h2 : (⌈z / d⌉₊ : ℝ) < z / d + 1 := Nat.ceil_lt_add_one (div_nonneg hz0 hpos.le)
      rw [div_le_iff₀ hpos] at h1
      have h3 : (⌈z / d⌉₊ : ℝ) * d < z + d := by
        have := mul_lt_mul_of_pos_right h2 hpos
        rw [add_mul, div_mul_cancel₀ _ hpos.ne', one_mul] at this
        exact this
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ⌈z / d⌉₊ * d - z := ⟨_, rfl⟩
      have ht0 : 0 ≤ t := by rw [ht]; linarith
      have ht1 : t < ε := by
        have : t < d := by rw [ht]; linarith
        rw [he] at hdε; linarith
      rw [hstep _ ⌊y⌋]
      have heq : (⌈z / d⌉₊ : ℝ) * d - y + ((⌊y⌋ : ℤ) : ℝ) = t := by
        have hfr : z = y - (⌊y⌋ : ℝ) := by rw [hz]; rfl
        rw [ht, hfr]; push_cast; ring
      rw [heq, Int.fract_eq_self.mpr ⟨ht0, lt_trans ht1 hε1⟩]
      exact ht1

lemma irrational_ratio {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Irrational √(Real.log q / Real.log p) := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  rintro ⟨r, hr⟩
  have h1 : (r : ℝ) ^ 2 = Real.log q / Real.log p := by
    rw [hr, Real.sq_sqrt (div_nonneg hlq.le hlp.le)]
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have h2 : ((r.num.natAbs : ℝ)) ^ 2 * Real.log p = (r.den : ℝ) ^ 2 * Real.log q := by
    have h3 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
    have h4 : ((r.num.natAbs : ℝ)) ^ 2 = (r.num : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [h3, div_pow, div_eq_div_iff (pow_ne_zero 2 hden) hlp.ne'] at h1
    rw [h4]; linarith
  have h5 : p ^ (r.num.natAbs ^ 2) = q ^ (r.den ^ 2) := by
    have h6 : Real.log ((p : ℝ) ^ (r.num.natAbs ^ 2)) = Real.log ((q : ℝ) ^ (r.den ^ 2)) := by
      rw [Real.log_pow, Real.log_pow]; push_cast; exact_mod_cast h2
    have hp0 : (0 : ℝ) < (p : ℝ) ^ (r.num.natAbs ^ 2) := pow_pos (by exact_mod_cast hp.pos) _
    have hq0 : (0 : ℝ) < (q : ℝ) ^ (r.den ^ 2) := pow_pos (by exact_mod_cast hq.pos) _
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hp0) (Set.mem_Ioi.mpr hq0) h6
    exact_mod_cast this
  have h7 : q ∣ p ^ (r.num.natAbs ^ 2) := by
    rw [h5]; exact dvd_pow_self q (pow_ne_zero 2 r.den_ne_zero)
  have h8 : q ∣ p := hq.dvd_of_dvd_pow h7
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h8).symm

set_option maxHeartbeats 1000000 in
/-- Heights with far-apart steps exist for every large `D`. -/
theorem exists_far {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {x0 x2 : ℝ}
    (h1 : 1 < x0 * Real.log p) (h2 : 9 / 4 < x0 * Real.log q) (h02 : x0 < x2)
    {K : ℕ} (hK : 1 ≤ K) :
    ∃ L0 : ℝ, ∀ D : ℕ, 0 < D → L0 ≤ Real.log D → ∃ s t : ℕ,
      K * D * q ^ (s ^ 2) ≤ p ^ (t ^ 2) ∧
      D * D * p ^ (t ^ 2) < q ^ ((s + 1) ^ 2) ∧
      D * D * p ^ (t ^ 2) < p ^ ((t + 1) ^ 2) ∧
      x0 * (Real.log D) ^ 2 ≤ Real.log (D * p ^ (t ^ 2) : ℕ) ∧
      Real.log (D * p ^ (t ^ 2) : ℕ) ≤ x2 * (Real.log D) ^ 2 := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = Real.log p := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = Real.log q := ⟨_, rfl⟩
  have hα0 : 0 < α := hα ▸ Real.log_pos (by exact_mod_cast hp.one_lt)
  have hβ0 : 0 < β := hβ ▸ Real.log_pos (by exact_mod_cast hq.one_lt)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (x0 + x2) / 2 := ⟨_, rfl⟩
  have hx00 : 0 < x0 := by
    rw [← hα] at h1
    by_contra h
    push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hα0.le
    linarith
  have hx0x : x0 < x := by rw [hx]; linarith
  have hxx2 : x < x2 := by rw [hx]; linarith
  have hx0' : 0 < x := lt_trans hx00 hx0x
  have hxα : 1 < x * α := by
    rw [← hα] at h1; exact lt_trans h1 (mul_lt_mul_of_pos_right hx0x hα0)
  have hxβ : 9 / 4 < x * β := by
    rw [← hβ] at h2; exact lt_trans h2 (mul_lt_mul_of_pos_right hx0x hβ0)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = √(β / α) := ⟨_, rfl⟩
  have hγ0 : 0 < γ := hγ ▸ Real.sqrt_pos.mpr (div_pos hβ0 hα0)
  have hγirr : Irrational γ := by rw [hγ, hα, hβ]; exact irrational_ratio hp hq hpq
  have hγ2 : γ ^ 2 * α = β := by
    rw [hγ, Real.sq_sqrt (div_nonneg hβ0.le hα0.le)]; field_simp
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = √(x * α) := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = √(x / β) := ⟨_, rfl⟩
  have hw0 : 0 < w := hw ▸ Real.sqrt_pos.mpr (mul_pos hx0' hα0)
  have hσ0 : 0 < σ := hσ ▸ Real.sqrt_pos.mpr (div_pos hx0' hβ0)
  have hw2 : w ^ 2 = x * α := by rw [hw, Real.sq_sqrt (mul_nonneg hx0'.le hα0.le)]
  have hσ2 : σ ^ 2 * β = x := by
    rw [hσ, Real.sq_sqrt (div_nonneg hx0'.le hβ0.le)]; field_simp
  -- the identities between the square roots
  have hσγ : σ * (γ * α) = w := by
    have h3 : (σ * (γ * α)) ^ 2 = w ^ 2 := by
      have e : (σ * (γ * α)) ^ 2 = σ ^ 2 * (γ ^ 2 * α) * α := by ring
      rw [e, hγ2, hσ2, hw2]
    exact (pow_left_inj₀ (by positivity) hw0.le two_ne_zero).mp h3
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = σ * β := ⟨_, rfl⟩
  have hz2 : z ^ 2 = x * β := by
    have e : z ^ 2 = σ ^ 2 * β * β := by rw [hz]; ring
    rw [e, hσ2]
  have hz0 : 0 < z := hz ▸ mul_pos hσ0 hβ0
  have hz32 : 3 / 2 < z := by
    have h3 : (3 / 2 : ℝ) ^ 2 < z ^ 2 := by rw [hz2]; norm_num; linarith
    exact (pow_lt_pow_iff_left₀ (by norm_num) hz0.le two_ne_zero).mp h3
  have hwγ : w * γ = z := by
    have h3 : (w * γ) ^ 2 = z ^ 2 := by
      have e : (w * γ) ^ 2 = x * (γ ^ 2 * α) := by rw [mul_pow, hw2]; ring
      rw [e, hγ2, hz2]
    exact (pow_left_inj₀ (by positivity) hz0.le two_ne_zero).mp h3
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / (2 * w) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hwa : 2 * w * a = 1 := by rw [ha]; field_simp
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = γ - 3 / (2 * w) := ⟨_, rfl⟩
  have hwl : w * l = z - 3 / 2 := by
    rw [hl, mul_sub, hwγ]; field_simp
  have hl0 : 0 < l := by
    have : 0 < w * l := by rw [hwl]; linarith
    exact pos_of_mul_pos_right this hw0.le
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min l 1 / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; have := lt_min hl0 one_pos; linarith
  have hεl : 4 * ε ≤ l := by rw [hε]; have := min_le_left l 1; linarith
  have hε14 : ε ≤ 1 / 4 := by rw [hε]; have := min_le_right l 1; linarith
  obtain ⟨K0, hK0⟩ := rotation (γ := -γ) hγirr.neg hε0 (by linarith)
  obtain ⟨Bmax, hBmax⟩ : ∃ B : ℝ, B = 2 * (K0 + 1) * (γ * α) * (a + 1) + α * (a + 1) ^ 2 :=
    ⟨_, rfl⟩
  have hBmax0 : 0 ≤ Bmax := by rw [hBmax]; positivity
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  obtain ⟨L1, hL1⟩ : ∃ L1 : ℝ, L1 = Real.log K / (2 * w * ε) := ⟨_, rfl⟩
  obtain ⟨L2, hL2⟩ : ∃ L2 : ℝ, L2 = (Bmax + 2) / (z - 3 / 2) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (K0 : ℝ) + 2 := ⟨_, rfl⟩
  obtain ⟨L3, hL3⟩ : ∃ L3 : ℝ, L3 = (2 * σ * M * β + M ^ 2 * β) / (x2 - x) := ⟨_, rfl⟩
  refine ⟨max 1 (max L1 (max L2 L3)), fun D hD hLD => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log D := ⟨_, rfl⟩
  rw [← hL] at hLD ⊢
  have hL1' : 1 ≤ L := le_trans (le_max_left _ _) hLD
  have hLL1 : L1 ≤ L := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hLD
  have hLL2 : L2 ≤ L :=
    le_trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hLD
  have hLL3 : L3 ≤ L :=
    le_trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hLD
  have hL0 : 0 < L := by linarith
  -- choose s and t
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℕ, s0 = ⌈L * σ⌉₊ := ⟨_, rfl⟩
  obtain ⟨j, hj, hfr⟩ := hK0 (s0 * γ + (a + ε))
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = s0 + j := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = s * γ + (a + ε) := ⟨_, rfl⟩
  have hfr' : Int.fract (-y) < ε := by
    have : (j : ℝ) * -γ - (s0 * γ + (a + ε)) = -y := by rw [hy, hs]; push_cast; ring
    rwa [this] at hfr
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = ⌈y⌉₊ := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ε + Int.fract (-y) := ⟨_, rfl⟩
  have hte : (t : ℝ) = s * γ + (a + e) := by
    have h3 : ((⌈y⌉₊ : ℕ) : ℝ) = (⌈y⌉ : ℝ) := by
      have h4 : (0 : ℤ) ≤ ⌈y⌉ := Int.ceil_nonneg hy0
      have h5 : ((⌈y⌉₊ : ℕ) : ℤ) = ⌈y⌉ := by
        rw [← Int.ceil_toNat]; exact Int.toNat_of_nonneg h4
      exact_mod_cast h5
    have h6 : Int.fract (-y) = (⌈y⌉ : ℝ) - y := by
      unfold Int.fract
      rw [Int.floor_neg]; push_cast; ring
    rw [ht, h3, he, h6, hy]; ring
  have he0 : ε ≤ e := by rw [he]; have := Int.fract_nonneg (-y); linarith
  have he1 : e ≤ 2 * ε := by rw [he]; linarith
  have hepos : 0 ≤ e := le_trans hε0.le he0
  have heone : e ≤ 1 := by linarith
  -- the size of s
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = s - L * σ := ⟨_, rfl⟩
  have hsθ : (s : ℝ) = L * σ + θ := by rw [hθ]; ring
  have hθ0 : 0 ≤ θ := by
    have h3 : L * σ ≤ (s0 : ℝ) := hs0 ▸ Nat.le_ceil _
    have h4 : (s0 : ℝ) ≤ s := by rw [hs]; push_cast; have := Nat.cast_nonneg (α := ℝ) j; linarith
    rw [hθ]; linarith
  have hθ1 : θ ≤ K0 + 1 := by
    have h3 : (s0 : ℝ) < L * σ + 1 := hs0 ▸ Nat.ceil_lt_add_one (by positivity)
    have h4 : (s : ℝ) ≤ s0 + K0 := by
      rw [hs]; push_cast; have : (j : ℝ) ≤ K0 := by exact_mod_cast hj
      linarith
    rw [hθ]; linarith
  -- r = t²α - s²β
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * θ * (γ * α) * (a + e) + α * (a + e) ^ 2 := ⟨_, rfl⟩
  have hr : (t : ℝ) ^ 2 * α - (s : ℝ) ^ 2 * β = L + 2 * L * w * e + B := by
    have e1 : (t : ℝ) ^ 2 * α - (s : ℝ) ^ 2 * β
        = 2 * (s : ℝ) * (γ * α) * (a + e) + α * (a + e) ^ 2 := by
      rw [hte, ← hγ2]; ring
    have e2 : 2 * (s : ℝ) * (γ * α) * (a + e)
        = 2 * L * (σ * (γ * α)) * (a + e) + 2 * θ * (γ * α) * (a + e) := by
      rw [hsθ]; ring
    have e3 : 2 * L * (σ * (γ * α)) * (a + e) = L * (2 * w * a) + 2 * L * w * e := by
      rw [hσγ]; ring
    rw [e1, e2, e3, hwa, hB]; ring
  have hB0 : 0 ≤ B := by
    rw [hB]
    have h3 : 0 ≤ 2 * θ * (γ * α) * (a + e) :=
      mul_nonneg (mul_nonneg (by linarith) (by positivity)) (by linarith)
    have h4 : 0 ≤ α * (a + e) ^ 2 := mul_nonneg hα0.le (sq_nonneg _)
    linarith
  have hBle : B ≤ Bmax := by
    rw [hB, hBmax]
    have h3 : a + e ≤ a + 1 := by linarith
    have h4 : 2 * θ * (γ * α) * (a + e) ≤ 2 * (K0 + 1) * (γ * α) * (a + 1) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) h3
        (by linarith) (by positivity)
    have h5 : α * (a + e) ^ 2 ≤ α * (a + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h3 2) hα0.le
    linarith
  have hlow : L + Real.log K ≤ (t : ℝ) ^ 2 * α - (s : ℝ) ^ 2 * β := by
    rw [hr]
    have h3 : Real.log K ≤ L * (2 * w * ε) := by
      have := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * w * ε)).mp (hL1 ▸ hLL1)
      linarith
    have h4 : 2 * L * w * ε ≤ 2 * L * w * e :=
      mul_le_mul_of_nonneg_left he0 (by positivity)
    have h5 : L * (2 * w * ε) = 2 * L * w * ε := by ring
    linarith
  have hup : (t : ℝ) ^ 2 * α - (s : ℝ) ^ 2 * β ≤ (2 * s + 1) * β - 2 * L - 2 := by
    rw [hr]
    have h3 : 2 * w * e ≤ z - 3 / 2 := by
      have h4 : 2 * e ≤ l := by linarith
      have h5 := mul_le_mul_of_nonneg_left h4 hw0.le
      linarith [hwl]
    have h6 : 2 * L * w * e ≤ L * (z - 3 / 2) := by
      have := mul_le_mul_of_nonneg_left h3 hL0.le
      linarith
    have h7 : Bmax + 2 ≤ L * (z - 3 / 2) :=
      (div_le_iff₀ (by linarith : (0:ℝ) < z - 3 / 2)).mp (hL2 ▸ hLL2)
    have h8 : 2 * L * z ≤ 2 * (s : ℝ) * β := by
      have h9 : L * σ ≤ s := by rw [hsθ]; linarith
      have := mul_le_mul_of_nonneg_right h9 hβ0.le
      rw [hz]; linarith
    linarith [hBle, hβ0.le]
  have hbig : 2 * L < (2 * (t : ℝ) + 1) * α := by
    have h3 : (s : ℝ) * γ ≤ t := by rw [hte]; linarith
    have h4 : L * σ * γ ≤ (s : ℝ) * γ :=
      mul_le_mul_of_nonneg_right (by rw [hsθ]; linarith) hγ0.le
    have h5 : L * w ≤ (t : ℝ) * α := by
      have h6 := mul_le_mul_of_nonneg_right (h4.trans h3) hα0.le
      have e1 : L * σ * γ * α = L * (σ * (γ * α)) := by ring
      rw [e1, hσγ] at h6
      exact h6
    have h7 : 1 < w := by
      have h8 : (1 : ℝ) ^ 2 < w ^ 2 := by rw [hw2]; simpa using hxα
      exact (pow_lt_pow_iff_left₀ zero_le_one hw0.le two_ne_zero).mp h8
    have h9 : L * 1 ≤ L * w := mul_le_mul_of_nonneg_left h7.le hL0.le
    linarith
  -- translate to integers
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have lpow : ∀ (b : ℕ) (k : ℕ), (0 : ℝ) < b → Real.log ((b : ℝ) ^ k) = k * Real.log b :=
    fun b k _ => Real.log_pow _ _
  have hXlog : Real.log (D * p ^ (t ^ 2) : ℕ) = L + (t : ℝ) ^ 2 * α := by
    push_cast
    rw [Real.log_mul hDr.ne' (pow_pos hpr _).ne', Real.log_pow, ← hL, ← hα]
    push_cast; ring
  refine ⟨s, t, ?_, ?_, ?_, ?_, ?_⟩
  · have h3 : ((K * D * q ^ (s ^ 2) : ℕ) : ℝ) ≤ ((p ^ (t ^ 2) : ℕ) : ℝ) := by
      push_cast
      rw [← Real.log_le_log_iff (mul_pos (mul_pos hKr hDr) (pow_pos hqr _)) (pow_pos hpr _),
        Real.log_mul (mul_pos hKr hDr).ne' (pow_pos hqr _).ne',
        Real.log_mul hKr.ne' hDr.ne', Real.log_pow, Real.log_pow, ← hL, ← hα, ← hβ]
      push_cast; linarith
    exact_mod_cast h3
  · have h3 : ((D * D * p ^ (t ^ 2) : ℕ) : ℝ) < ((q ^ ((s + 1) ^ 2) : ℕ) : ℝ) := by
      push_cast
      rw [← Real.log_lt_log_iff (mul_pos (mul_pos hDr hDr) (pow_pos hpr _)) (pow_pos hqr _),
        Real.log_mul (mul_pos hDr hDr).ne' (pow_pos hpr _).ne',
        Real.log_mul hDr.ne' hDr.ne', Real.log_pow, Real.log_pow, ← hL, ← hα, ← hβ]
      push_cast
      have e1 : ((s : ℝ) + 1) ^ 2 * β = (s : ℝ) ^ 2 * β + (2 * s + 1) * β := by ring
      rw [e1]; linarith
    exact_mod_cast h3
  · have h3 : ((D * D * p ^ (t ^ 2) : ℕ) : ℝ) < ((p ^ ((t + 1) ^ 2) : ℕ) : ℝ) := by
      push_cast
      rw [← Real.log_lt_log_iff (mul_pos (mul_pos hDr hDr) (pow_pos hpr _)) (pow_pos hpr _),
        Real.log_mul (mul_pos hDr hDr).ne' (pow_pos hpr _).ne',
        Real.log_mul hDr.ne' hDr.ne', Real.log_pow, Real.log_pow, ← hL, ← hα]
      push_cast
      have e1 : ((t : ℝ) + 1) ^ 2 * α = (t : ℝ) ^ 2 * α + (2 * t + 1) * α := by ring
      rw [e1]; linarith
    exact_mod_cast h3
  · rw [hXlog]
    have h3 : x0 * L ^ 2 ≤ x * L ^ 2 := mul_le_mul_of_nonneg_right hx0x.le (sq_nonneg _)
    have h4 : x * L ^ 2 ≤ (s : ℝ) ^ 2 * β := by
      have h5 : (L * σ) ^ 2 ≤ (s : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by rw [hsθ]; linarith) 2
      have h6 := mul_le_mul_of_nonneg_right h5 hβ0.le
      have e1 : (L * σ) ^ 2 * β = (σ ^ 2 * β) * L ^ 2 := by ring
      rw [e1, hσ2] at h6
      exact h6
    linarith
  · rw [hXlog]
    have h3 : L + (t : ℝ) ^ 2 * α ≤ ((s : ℝ) + 1) ^ 2 * β := by
      have e1 : ((s : ℝ) + 1) ^ 2 * β = (s : ℝ) ^ 2 * β + (2 * s + 1) * β := by ring
      rw [e1]; linarith
    have h4 : (s : ℝ) + 1 ≤ L * σ + M := by rw [hsθ, hM]; linarith
    have h5 : ((s : ℝ) + 1) ^ 2 * β ≤ (L * σ + M) ^ 2 * β :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h4 2) hβ0.le
    have h6 : (L * σ + M) ^ 2 * β = x * L ^ 2 + (2 * σ * M * β) * L + M ^ 2 * β := by
      rw [← hσ2]; ring
    have h7 : 2 * σ * M * β + M ^ 2 * β ≤ L * (x2 - x) :=
      (div_le_iff₀ (by linarith : (0:ℝ) < x2 - x)).mp (hL3 ▸ hLL3)
    have hM0 : 0 ≤ M := by rw [hM]; positivity
    have h8 : M ^ 2 * β * 1 ≤ M ^ 2 * β * L :=
      mul_le_mul_of_nonneg_left hL1' (mul_nonneg (sq_nonneg _) hβ0.le)
    have h9 := mul_le_mul_of_nonneg_right h7 hL0.le
    linarith only [h3, h5, h6, h8, h9]

/-! ## Non-resonance with the actual digit-set data -/

set_option maxHeartbeats 1000000 in
/-- For all large `D` regular for `p` and `q` (with `p < q`) there is a window height `X = D v`
with `v ≥ 20 D u`, both top ranges at least `D`, at which the bound is at most `1.85`.
`u = q^(s^2)` is the smaller step, from the larger prime. -/
theorem nonresonance {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) {x0 x2 : ℝ}
    (h1 : 1 < x0 * Real.log p) (h2 : 9 / 4 < x0 * Real.log q) (h02 : x0 < x2) :
    ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D → (∀ k, ¬ D ∣ p ^ k) → (∀ k, ¬ D ∣ q ^ k) → ∃ s t X : ℕ,
      let u := q ^ (s ^ 2)
      let v := p ^ (t ^ 2)
      let UA := U q D s
      let UB := U p D t
      let JA := min (q ^ (2 * s + 1) / D) ((X + UA) / u)
      let JB := min (p ^ (2 * t + 1) / D) ((X + UB) / v)
      X = D * v ∧ 20 * D * u ≤ v ∧ D * X < q ^ ((s + 1) ^ 2) ∧ D * X < p ^ ((t + 1) ^ 2) ∧
      x0 * (Real.log D) ^ 2 ≤ Real.log X ∧ Real.log X ≤ x2 * (Real.log D) ^ 2 ∧
      D ≤ JA ∧ D ≤ JB ∧
      ∀ c : ℝ,
        let W : ℝ := 2 * ((UA : ℝ) + UB)
        let a : ℝ := (JA : ℝ) + 1
        let b : ℝ := (JB : ℝ) + 1
        let P : ℝ := min ((u : ℝ) * a) ((v : ℝ) * b)
        let Q : ℝ := max ((u : ℝ) * a) ((v : ℝ) * b)
        let C0 : ℝ := 2 * X * (3 * Q - P) / (3 * Q ^ 2)
        let H0 : ℝ := (3 * (UB : ℝ) - UA) / (6 * (UB : ℝ) ^ 2)
        let A0 : ℝ := (4 * P * W - (max 0 (W - Q + P)) ^ 2 + (max 0 (W - P - Q)) ^ 2)
          / ((u : ℝ) * v)
        let Aeff : ℝ := c * (a * b) / (2 * X * H0)
        C0 - 2 * X * W / Q ^ 2 ≤ c → c ≤ C0 →
          ∀ m n : ℤ, (m, n) ≠ (0, 0) →
            c * (1 + (2 * √A0 + 1 + 2 / gauge u v a b W m n) / Aeff) ≤ 1.85 := by
  obtain ⟨L0, hL0⟩ := exists_far hp hq hpq.ne h1 h2 h02 (K := 20) (by norm_num)
  refine ⟨max (max 100 (2 * q ^ 2)) (⌈Real.exp L0⌉₊), fun D hD hregp hregq => ?_⟩
  have hD100 : 100 ≤ D := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hD
  have hDq : 2 * q ^ 2 ≤ D := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hD
  have hD0 : 0 < D := by omega
  have hLD : L0 ≤ Real.log D := by
    have h3 : Real.exp L0 ≤ D := by
      refine (Nat.le_ceil _).trans ?_
      exact_mod_cast (le_max_right _ _).trans hD
    have h4 := Real.log_le_log (Real.exp_pos _) h3
    rwa [Real.log_exp] at h4
  obtain ⟨s, t, hfar, hcapq, hcapp, hwin0, hwin1⟩ := hL0 D hD0 hLD
  refine ⟨s, t, D * p ^ (t ^ 2), ?_⟩
  intro u v UA UB JA JB
  have hq0 : 0 < q := hq.pos
  have hp0 : 0 < p := hp.pos
  have hu0 : 0 < u := pow_pos hq0 _
  have hv0 : 0 < v := pow_pos hp0 _
  have hfar' : 20 * D * u ≤ v := hfar
  have hDXq : D * (D * v) < q ^ ((s + 1) ^ 2) := by rw [← mul_assoc]; exact hcapq
  have hDXp : D * (D * v) < p ^ ((t + 1) ^ 2) := by rw [← mul_assoc]; exact hcapp
  have hsq : q ^ ((s + 1) ^ 2) = q ^ (2 * s + 1) * u := by
    show _ = _ * q ^ (s ^ 2); rw [← pow_add]; congr 1; ring
  have htp : p ^ ((t + 1) ^ 2) = p ^ (2 * t + 1) * v := by
    show _ = _ * p ^ (t ^ 2); rw [← pow_add]; congr 1; ring
  -- sizes of the last powers
  have hbigq : 20 * D ^ 3 < q ^ (2 * s + 1) := by
    have h3 : (20 * D ^ 3) * u < q ^ (2 * s + 1) * u := by
      calc (20 * D ^ 3) * u = D * (D * (20 * D * u)) := by ring
        _ ≤ D * (D * v) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hfar')
        _ < q ^ (2 * s + 1) * u := hsq ▸ hDXq
    exact Nat.lt_of_mul_lt_mul_right h3
  have hbigp : D ^ 2 < p ^ (2 * t + 1) := by
    have h3 : D ^ 2 * v < p ^ (2 * t + 1) * v := by
      calc D ^ 2 * v = D * (D * v) := by ring
        _ < p ^ (2 * t + 1) * v := htp ▸ hDXp
    exact Nat.lt_of_mul_lt_mul_right h3
  have hpD : 2 * p ^ 2 ≤ D :=
    le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpq.le 2)) hDq
  have hqD : q ≤ D := by
    have : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
    omega
  have hpD' : p ≤ D := le_trans hpq.le hqD
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exfalso
      rw [h] at hbigq
      simp only [mul_zero, zero_add, pow_one] at hbigq
      have : D ≤ D ^ 3 := Nat.le_self_pow (by norm_num) D
      omega
    · exact h
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · exfalso
      rw [h] at hbigp
      simp only [mul_zero, zero_add, pow_one] at hbigp
      have : D ≤ D ^ 2 := Nat.le_self_pow two_ne_zero D
      omega
    · exact h
  obtain ⟨S, hS⟩ : ∃ S, s = S + 1 := ⟨s - 1, by omega⟩
  obtain ⟨T, hT⟩ : ∃ T, t = T + 1 := ⟨t - 1, by omega⟩
  have hlowq : 2 * D ≤ q ^ (2 * S + 1) := by
    have h3 : q ^ (2 * s + 1) = q ^ (2 * S + 1) * q ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have h4 : (2 * D) * q ^ 2 ≤ q ^ (2 * S + 1) * q ^ 2 := by
      rw [← h3]
      have h5 : (2 * D) * q ^ 2 ≤ (2 * D) * D := Nat.mul_le_mul_left _ (by omega)
      have h6 : (2 * D) * D ≤ 20 * D ^ 3 := by
        have : D ^ 2 ≤ D ^ 3 := Nat.pow_le_pow_right hD0 (by norm_num)
        nlinarith
      omega
    exact Nat.le_of_mul_le_mul_right h4 (pow_pos hq0 _)
  have hlowp : 2 * D ≤ p ^ (2 * T + 1) := by
    have h3 : p ^ (2 * t + 1) = p ^ (2 * T + 1) * p ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have h4 : (2 * D) * p ^ 2 ≤ p ^ (2 * T + 1) * p ^ 2 := by
      rw [← h3]
      have h5 : (2 * p ^ 2) * D ≤ D * D := Nat.mul_le_mul_right _ hpD
      have h6 : (2 * D) * p ^ 2 = (2 * p ^ 2) * D := by ring
      have h7 : D * D = D ^ 2 := by ring
      omega
    exact Nat.le_of_mul_le_mul_right h4 (pow_pos hp0 _)
  -- the hull bounds
  have hUAup : D * UA < u := U_upper hq0 hD0 hregq s
  have hUBup : D * UB < v := U_upper hp0 hD0 hregp t
  have hUAlow : u ≤ 2 * D * UA := by
    show q ^ (s ^ 2) ≤ 2 * D * U q D s
    rw [hS]; exact U_lower hD0 hlowq
  have hUBlow : v ≤ 2 * D * UB := by
    show p ^ (t ^ 2) ≤ 2 * D * U p D t
    rw [hT]; exact U_lower hD0 hlowp
  have hUAu : UA < u := lt_of_le_of_lt (Nat.le_mul_of_pos_left UA hD0) hUAup
  have hUBv : UB < v := lt_of_le_of_lt (Nat.le_mul_of_pos_left UB hD0) hUBup
  -- the top ranges
  have huv : u ≤ v := by
    have : u ≤ 20 * D * u := Nat.le_mul_of_pos_left u (by omega)
    omega
  obtain ⟨X, hX⟩ : ∃ X, X = D * v := ⟨_, rfl⟩
  have hXu : D * u ≤ X := hX ▸ Nat.mul_le_mul_left _ huv
  have hXdivu : X / u ≤ q ^ (2 * s + 1) / D := by
    rw [Nat.le_div_iff_mul_le hD0]
    have h3 : (X / u * D) * u ≤ q ^ (2 * s + 1) * u := by
      have h4 : X / u * u ≤ X := Nat.div_mul_le_self X u
      calc (X / u * D) * u = D * (X / u * u) := by ring
        _ ≤ D * X := Nat.mul_le_mul_left _ h4
        _ ≤ q ^ (2 * s + 1) * u := by rw [hX]; exact (hsq ▸ hDXq).le
    exact Nat.le_of_mul_le_mul_right h3 hu0
  have hXv : X / v = D := by rw [hX]; exact Nat.mul_div_cancel _ hv0
  have hDvdivp : D ≤ p ^ (2 * t + 1) / D := by
    rw [Nat.le_div_iff_mul_le hD0]
    have : D * D = D ^ 2 := by ring
    omega
  have hJA : JA = min (q ^ (2 * s + 1) / D) ((X + UA) / u) := by rw [hX]
  have hJB : JB = min (p ^ (2 * t + 1) / D) ((X + UB) / v) := by rw [hX]
  have hJAlow : X / u ≤ JA := by
    rw [hJA]; exact le_min hXdivu (Nat.div_le_div_right (Nat.le_add_right _ _))
  have hJBlow : X / v ≤ JB := by
    rw [hJB, hXv]
    exact le_min hDvdivp (hXv ▸ Nat.div_le_div_right (Nat.le_add_right _ _))
  have hDJA : D ≤ JA := le_trans ((Nat.le_div_iff_mul_le hu0).mpr hXu) hJAlow
  have hDJB : D ≤ JB := hXv ▸ hJBlow
  have hPA0 : X < u * (JA + 1) := by
    have h3 : X < u * (X / u + 1) := Nat.lt_mul_div_succ X hu0
    exact lt_of_lt_of_le h3 (Nat.mul_le_mul_left _ (by omega))
  have hPB0 : X < v * (JB + 1) := by
    have h3 : X < v * (X / v + 1) := Nat.lt_mul_div_succ X hv0
    exact lt_of_lt_of_le h3 (Nat.mul_le_mul_left _ (by omega))
  have hPA1 : u * (JA + 1) ≤ X + 2 * u := by
    have h3 : JA ≤ (X + UA) / u := hJA ▸ min_le_right _ _
    have h4 : u * ((X + UA) / u) ≤ X + UA := Nat.mul_div_le _ _
    have h5 : u * JA ≤ X + UA := le_trans (Nat.mul_le_mul_left _ h3) h4
    rw [mul_add]; omega
  have hPB1 : v * (JB + 1) ≤ X + 2 * v := by
    have h3 : JB ≤ (X + UB) / v := hJB ▸ min_le_right _ _
    have h4 : v * ((X + UB) / v) ≤ X + UB := Nat.mul_div_le _ _
    have h5 : v * JB ≤ X + UB := le_trans (Nat.mul_le_mul_left _ h3) h4
    rw [mul_add]; omega
  refine ⟨rfl, hfar', hDXq, hDXp, hwin0, hwin1, hDJA, hDJB, ?_⟩
  intro c
  rw [← hX]
  intro W a b P Q C0 H0 A0 Aeff hc0 hc1 m n hmn
  -- real versions
  have hDr : (100 : ℝ) ≤ D := by exact_mod_cast hD100
  have hDr0 : (0 : ℝ) < D := by linarith
  have hur : (0 : ℝ) < u := by exact_mod_cast hu0
  have hXr : (D : ℝ) * v ≤ X := by exact_mod_cast hX.ge
  have hfarr : 20 * (D : ℝ) * u ≤ v := by exact_mod_cast hfar'
  have hXr0 : (0 : ℝ) < X := by
    have : 0 < X := by rw [hX]; exact Nat.mul_pos hD0 hv0
    exact_mod_cast this
  have scale : ∀ w : ℕ, D * w ≤ X → (X : ℝ) + 2 * w ≤ X * (1 + 2 / D) := by
    intro w hw
    have h3 : (D : ℝ) * w ≤ X := by exact_mod_cast hw
    have h4 : (w : ℝ) ≤ X / D := by rw [le_div_iff₀ hDr0]; linarith
    have h5 : (X : ℝ) * (1 + 2 / D) = X + 2 * (X / D) := by ring
    rw [h5]; linarith
  have hUA0r : (u : ℝ) / (2 * D) ≤ UA := by
    rw [div_le_iff₀ (by positivity)]
    have : (u : ℝ) ≤ 2 * D * UA := by exact_mod_cast hUAlow
    linarith
  have hUA1r : (UA : ℝ) ≤ u / D := by
    rw [le_div_iff₀ hDr0]
    have : (D : ℝ) * UA ≤ u := by exact_mod_cast hUAup.le
    linarith
  have hUB0r : (v : ℝ) / (2 * D) ≤ UB := by
    rw [div_le_iff₀ (by positivity)]
    have : (v : ℝ) ≤ 2 * D * UB := by exact_mod_cast hUBlow
    linarith
  have hUB1r : (UB : ℝ) ≤ v / D := by
    rw [le_div_iff₀ hDr0]
    have : (D : ℝ) * UB ≤ v := by exact_mod_cast hUBup.le
    linarith
  have hPA0r : (X : ℝ) ≤ u * a := by
    show (X : ℝ) ≤ u * ((JA : ℝ) + 1)
    exact_mod_cast hPA0.le
  have hPB0r : (X : ℝ) ≤ v * b := by
    show (X : ℝ) ≤ v * ((JB : ℝ) + 1)
    exact_mod_cast hPB0.le
  have hPA1r : (u : ℝ) * a ≤ X * (1 + 2 / D) := by
    have h3 : (u : ℝ) * ((JA : ℝ) + 1) ≤ X + 2 * u := by exact_mod_cast hPA1
    exact h3.trans (scale u hXu)
  have hPB1r : (v : ℝ) * b ≤ X * (1 + 2 / D) := by
    have h3 : (v : ℝ) * ((JB : ℝ) + 1) ≤ X + 2 * v := by exact_mod_cast hPB1
    exact h3.trans (scale v hX.ge)
  have ha0 : (0 : ℝ) < a := by show (0:ℝ) < (JA : ℝ) + 1; positivity
  have hb0 : (0 : ℝ) < b := by show (0:ℝ) < (JB : ℝ) + 1; positivity
  exact bound (u := (u : ℝ)) (v := (v : ℝ)) (D := (D : ℝ)) (X := (X : ℝ)) (UA := (UA : ℝ))
    (UB := (UB : ℝ)) (a := a) (b := b) (c := c) hDr hur hfarr hXr hUA0r hUA1r hUB0r hUB1r
    ha0 hb0 hPA0r hPA1r hPB0r hPB1r W P Q C0 H0 A0 Aeff rfl rfl rfl rfl hc0 hc1 rfl rfl rfl
    m n hmn

/-- The hypotheses are satisfied for the primes `2`, `3` and the window `[3.4, 6]`. -/
theorem exists_far_two_three :
    ∃ L0 : ℝ, ∀ D : ℕ, 0 < D → L0 ≤ Real.log D → ∃ s t : ℕ,
      20 * D * 3 ^ (s ^ 2) ≤ 2 ^ (t ^ 2) ∧
      D * D * 2 ^ (t ^ 2) < 3 ^ ((s + 1) ^ 2) ∧
      D * D * 2 ^ (t ^ 2) < 2 ^ ((t + 1) ^ 2) ∧
      3.4 * (Real.log D) ^ 2 ≤ Real.log (D * 2 ^ (t ^ 2) : ℕ) ∧
      Real.log (D * 2 ^ (t ^ 2) : ℕ) ≤ 6 * (Real.log D) ^ 2 := by
  have h2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have h3 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  exact exists_far (p := 2) (q := 3) Nat.prime_two Nat.prime_three (by norm_num)
    (x0 := 3.4) (x2 := 6) (by push_cast; linarith) (by push_cast; linarith) (by norm_num)
    (K := 20) (by norm_num)

end TwoPrimesNonresonance
