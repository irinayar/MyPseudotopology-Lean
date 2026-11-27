import Mathlib
import LeanCheck.TwoPrimesFormula

/-!
# The normalized kernel decreases with the number of clusters

With `K_M = H M` and `W_M θ = H M θ / H M 0`:

* `weight_antitone`: `W_N θ ≤ W_M θ` for `1 ≤ M ≤ N` and every real `θ`.
* `kappa_antitone`: hence `κ_N ≤ κ_M` for the same lower sets.

The theorem and its proof are due to ChatGPT.
-/

namespace TwoPrimesKernel

open Finset Real TwoPrimesFormula

lemma mul_cos_le_sin {x : ℝ} (h0 : 0 ≤ x) (hπ : x ≤ π) : x * cos x ≤ sin x := by
  have hmono : MonotoneOn (fun t => sin t - t * cos t) (Set.Icc 0 π) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => t * sin t) (convex_Icc 0 π)
      (by fun_prop) (fun t _ => ?_) (fun t ht => ?_)
    · have h := (hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (hasDerivAt_cos t))
      refine (h.congr_deriv ?_).hasDerivWithinAt
      simp only [id_eq]
      ring
    · rw [interior_Icc] at ht
      exact mul_nonneg ht.1.le (sin_nonneg_of_nonneg_of_le_pi ht.1.le ht.2.le)
  have h := hmono (Set.left_mem_Icc.mpr pi_pos.le) ⟨h0, hπ⟩ h0
  simp only [sin_zero, zero_mul, sub_zero] at h
  linarith

/-- `x (1 + x²/3) cos x ≤ sin x` on `[0, π/2]`. -/
lemma cubic_cos_le_sin {x : ℝ} (h0 : 0 ≤ x) (hπ : x ≤ π / 2) :
    (x + x ^ 3 / 3) * cos x ≤ sin x := by
  have hmono : MonotoneOn (fun t => sin t - (t + t ^ 3 / 3) * cos t) (Set.Icc 0 (π / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun t => t * (sin t - t * cos t) + t ^ 3 / 3 * sin t) (convex_Icc _ _)
      (by fun_prop) (fun t _ => ?_) (fun t ht => ?_)
    · have h1 : HasDerivAt (fun t : ℝ => t + t ^ 3 / 3) (1 + 3 * t ^ 2 / 3) t := by
        have := (hasDerivAt_id t).add ((hasDerivAt_pow 3 t).div_const 3)
        exact this.congr_deriv (by norm_num)
      have h := (hasDerivAt_sin t).sub (h1.mul (hasDerivAt_cos t))
      exact (h.congr_deriv (by ring)).hasDerivWithinAt
    · rw [interior_Icc] at ht
      have htπ : t ≤ π := by linarith [ht.2, pi_pos]
      have h1 := mul_cos_le_sin ht.1.le htπ
      have h2 := sin_nonneg_of_nonneg_of_le_pi ht.1.le htπ
      have h3 : 0 ≤ t ^ 3 := pow_nonneg ht.1.le 3
      exact add_nonneg (mul_nonneg ht.1.le (by linarith)) (mul_nonneg (by linarith) h2)
  have h := hmono (Set.left_mem_Icc.mpr (by positivity)) ⟨h0, hπ⟩ h0
  simp only [sin_zero, cos_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, add_zero, zero_mul, sub_zero] at h
  linarith

/-- `sin y - y cos y ≤ y³/3`. -/
lemma sin_sub_le {y : ℝ} (h0 : 0 ≤ y) : sin y - y * cos y ≤ y ^ 3 / 3 := by
  have hmono : MonotoneOn (fun t => t ^ 3 / 3 - (sin t - t * cos t)) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => t * (t - sin t)) (convex_Ici _)
      (by fun_prop) (fun t _ => ?_) (fun t ht => ?_)
    · have h := ((hasDerivAt_pow 3 t).div_const 3).sub
        ((hasDerivAt_sin t).sub ((hasDerivAt_id t).mul (hasDerivAt_cos t)))
      refine (h.congr_deriv ?_).hasDerivWithinAt
      simp only [id_eq, Nat.cast_ofNat]
      ring
    · rw [interior_Ici] at ht
      exact mul_nonneg ht.le (sub_nonneg.mpr (sin_le ht.le))
  have h := hmono (Set.self_mem_Ici) h0 h0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sin_zero,
    zero_mul, sub_self] at h
  linarith

/-- `3 sin y ≤ y (2 + cos y)`. -/
lemma three_sin_le {y : ℝ} (h0 : 0 ≤ y) : 3 * sin y ≤ y * (2 + cos y) := by
  by_cases hπ : y ≤ π
  · have hmono : MonotoneOn (fun t => t * (2 + cos t) - 3 * sin t) (Set.Icc 0 π) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg
        (f' := fun t => 2 - 2 * cos t - t * sin t) (convex_Icc _ _)
        (by fun_prop) (fun t _ => ?_) (fun t ht => ?_)
      · have h := ((hasDerivAt_id t).mul ((hasDerivAt_const t (2 : ℝ)).add (hasDerivAt_cos t))).sub
          ((hasDerivAt_sin t).const_mul 3)
        refine (h.congr_deriv ?_).hasDerivWithinAt
        simp only [id_eq, Pi.add_apply]
        ring
      · rw [interior_Icc] at ht
        set a := t / 2 with ha
        have ha0 : 0 ≤ a := by rw [ha]; linarith [ht.1]
        have haπ : a ≤ π := by rw [ha]; linarith [ht.2, pi_pos]
        have ht2 : t = 2 * a := by rw [ha]; ring
        have e : 2 - 2 * cos t - t * sin t = 4 * sin a * (sin a - a * cos a) := by
          rw [ht2, cos_two_mul, sin_two_mul]
          have := sin_sq_add_cos_sq a
          linear_combination (-4 : ℝ) * this
        rw [e]
        have h1 := mul_cos_le_sin ha0 haπ
        have h2 := sin_nonneg_of_nonneg_of_le_pi ha0 haπ
        exact mul_nonneg (mul_nonneg (by norm_num) h2) (by linarith)
    have h := hmono (Set.left_mem_Icc.mpr pi_pos.le) ⟨h0, hπ⟩ h0
    simp only [zero_mul, sin_zero, mul_zero, sub_self] at h
    linarith
  · push Not at hπ
    have h1 : sin y ≤ 1 := sin_le_one y
    have h2 : 1 ≤ 2 + cos y := by linarith [neg_one_le_cos y]
    have h3 : y ≤ y * (2 + cos y) := le_mul_of_one_le_right h0 h2
    linarith [pi_gt_three]

lemma F_mul_sin (N : ℕ) (θ : ℝ) : F N θ * sin (π * θ) ^ 2 = sin (N * (π * θ)) ^ 2 := by
  have hF : F N θ = Complex.normSq (∑ k ∈ range N, Complex.exp (((2 * π * θ : ℝ) : ℂ) * Complex.I) ^ k) := by
    rw [F_eq_squares, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
    have h : ∀ k : ℕ, Complex.exp (((2 * π * θ : ℝ) : ℂ) * Complex.I) ^ k
        = Complex.exp (((2 * π * θ * k : ℝ) : ℂ) * Complex.I) := by
      intro k
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h1 : ∑ k ∈ range N, (Complex.exp (((2 * π * θ : ℝ) : ℂ) * Complex.I) ^ k).re = Cs N θ :=
      sum_congr rfl fun k _ => by rw [h, Complex.exp_ofReal_mul_I_re]
    have h2 : ∑ k ∈ range N, (Complex.exp (((2 * π * θ : ℝ) : ℂ) * Complex.I) ^ k).im = Sn N θ :=
      sum_congr rfl fun k _ => by rw [h, Complex.exp_ofReal_mul_I_im]
    rw [h1, h2, sq, sq]
  have hn : ∀ a : ℝ, Complex.normSq (Complex.exp ((a : ℂ) * Complex.I) - 1) = 4 * sin (a / 2) ^ 2 := by
    intro a
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero]
    have h1 := sin_sq_add_cos_sq a
    have h2 : sin (a / 2) ^ 2 = 1 / 2 - cos a / 2 := by
      rw [sin_sq_eq_half_sub]
      congr 3
      ring
    rw [h2]
    nlinarith
  set z := Complex.exp (((2 * π * θ : ℝ) : ℂ) * Complex.I) with hz
  have hg : (∑ k ∈ range N, z ^ k) * (z - 1) = z ^ N - 1 := geom_sum_mul z N
  have hzN : z ^ N = Complex.exp (((2 * π * θ * N : ℝ) : ℂ) * Complex.I) := by
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h := congrArg Complex.normSq hg
  rw [map_mul, ← hF, hzN, hz, hn, hn] at h
  have e1 : 2 * π * θ / 2 = π * θ := by ring
  have e2 : 2 * π * θ * (N : ℝ) / 2 = N * (π * θ) := by ring
  rw [e1, e2] at h
  linarith

/-- The closed form of the kernel. -/
lemma H_mul_sin (N : ℕ) (θ : ℝ) (hs : sin (π * θ) ≠ 0) :
    H N θ * sin (π * θ) ^ 2
      = N - cos (π * θ) / sin (π * θ) * sin (2 * N * (π * θ)) / 2 := by
  set x := π * θ with hx
  induction N with
  | zero => simp [H]
  | succ N ih =>
    rw [H_succ, add_mul, add_mul, ih, F_mul_sin, F_mul_sin, ← hx]
    have hc : cos x / sin x * (sin (2 * ((N : ℝ) + 1) * x) - sin (2 * N * x))
        = cos (2 * N * x) + cos (2 * ((N : ℝ) + 1) * x) := by
      have h1 : sin (2 * ((N : ℝ) + 1) * x) - sin (2 * N * x)
          = 2 * sin x * cos (2 * N * x + x) := by
        rw [sin_sub_sin]
        congr 2
        · congr 1; ring
        · ring
      have h2 : cos (2 * N * x) + cos (2 * ((N : ℝ) + 1) * x)
          = 2 * cos (2 * N * x + x) * cos x := by
        rw [cos_add_cos]
        have e1 : (2 * (N : ℝ) * x + 2 * ((N : ℝ) + 1) * x) / 2 = 2 * N * x + x := by ring
        have e2 : (2 * (N : ℝ) * x - 2 * ((N : ℝ) + 1) * x) / 2 = -x := by ring
        rw [e1, e2, cos_neg]
      rw [h1, h2]
      field_simp
    have h3 : ∀ a : ℝ, sin a ^ 2 = 1 / 2 - cos (2 * a) / 2 := fun a => sin_sq_eq_half_sub a
    rw [h3 ((N : ℝ) * x), h3 (((N + 1 : ℕ) : ℝ) * x)]
    push_cast
    have e1 : 2 * ((N : ℝ) * x) = 2 * N * x := by ring
    have e2 : 2 * (((N : ℝ) + 1) * x) = 2 * ((N : ℝ) + 1) * x := by ring
    rw [e1, e2]
    linear_combination (1 / 2 : ℝ) * hc

/-- The decreasing function behind the normalized kernel. -/
lemma antitone_aux {x : ℝ} (h0 : 0 < x) (hπ : x ≤ π / 2) :
    AntitoneOn (fun m : ℝ => (1 - cos x / sin x * sin (2 * m * x) / (2 * m)) / (2 * m ^ 2 + 1))
      (Set.Ici 1) := by
  have hxπ : x ≤ π := by linarith [pi_pos]
  have hsin : 0 < sin x := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
  have hcos : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hπ⟩
  set c := cos x / sin x with hc
  have hc0 : 0 ≤ c := div_nonneg hcos hsin.le
  set a := x * c with ha
  have ha0 : 0 ≤ a := mul_nonneg h0.le hc0
  have ha1 : a * (1 + x ^ 2 / 3) ≤ 1 := by
    have h := cubic_cos_le_sin h0.le hπ
    have e : a * (1 + x ^ 2 / 3) = (x + x ^ 3 / 3) * cos x / sin x := by
      rw [ha, hc]; ring
    rw [e, div_le_one hsin]
    exact h
  have hder : ∀ m : ℝ, 0 < m → HasDerivAt
      (fun m : ℝ => (1 - c * sin (2 * m * x) / (2 * m)) / (2 * m ^ 2 + 1))
      (((-(c * (cos (2 * m * x) * (2 * x)) * (2 * m) - c * sin (2 * m * x) * 2) / (2 * m) ^ 2)
          * (2 * m ^ 2 + 1) - (1 - c * sin (2 * m * x) / (2 * m)) * (4 * m))
        / (2 * m ^ 2 + 1) ^ 2) m := by
    intro m hm
    have h1 : HasDerivAt (fun m : ℝ => 2 * m * x) (2 * x) m := by
      simpa using ((hasDerivAt_id m).const_mul 2).mul_const x
    have h2 : HasDerivAt (fun m : ℝ => c * sin (2 * m * x)) (c * (cos (2 * m * x) * (2 * x))) m :=
      (h1.sin).const_mul c
    have h3 : HasDerivAt (fun m : ℝ => 2 * m) 2 m := by
      simpa using (hasDerivAt_id m).const_mul 2
    have h4 := (h2.div h3 (by positivity)).const_sub 1
    have h5 : HasDerivAt (fun m : ℝ => 2 * m ^ 2 + 1) (4 * m) m := by
      have := ((hasDerivAt_pow 2 m).const_mul 2).add_const 1
      refine this.congr_deriv ?_
      push_cast
      ring
    have h6 := h4.div h5 (by positivity)
    refine h6.congr_deriv ?_
    simp only [Pi.div_apply]
    ring
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
    (f' := fun m => (((-(c * (cos (2 * m * x) * (2 * x)) * (2 * m) - c * sin (2 * m * x) * 2)
          / (2 * m) ^ 2) * (2 * m ^ 2 + 1) - (1 - c * sin (2 * m * x) / (2 * m)) * (4 * m))
        / (2 * m ^ 2 + 1) ^ 2)) ?_ (fun m hm => ?_) (fun m hm => ?_)
  · intro m hm
    exact (hder m (lt_of_lt_of_le one_pos hm)).continuousAt.continuousWithinAt
  · rw [interior_Ici] at hm
    exact (hder m (lt_trans one_pos hm)).hasDerivWithinAt
  · rw [interior_Ici] at hm
    have hm0 : 0 < m := lt_trans one_pos hm
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    set y := 2 * m * x with hy
    have hy0 : 0 < y := by rw [hy]; positivity
    set s := sin y / y with hs
    have hsy : sin y = s * y := by rw [hs]; field_simp
    have e : (-(c * (cos y * (2 * x)) * (2 * m) - c * sin y * 2) / (2 * m) ^ 2)
          * (2 * m ^ 2 + 1) - (1 - c * sin y / (2 * m)) * (4 * m)
        = 2 * m * (a * (3 * s - cos y) + a * (s - cos y) / (2 * m ^ 2) - 2) := by
      rw [hsy, ha, hy]
      field_simp
      ring
    rw [e]
    have h1 : 3 * s - cos y ≤ 2 := by
      have h := three_sin_le hy0.le
      have h2 : 3 * s ≤ 2 + cos y := by
        rw [hs, mul_div_assoc', div_le_iff₀ hy0]
        linarith
      linarith
    have h2 : s - cos y ≤ y ^ 2 / 3 := by
      have h := sin_sub_le hy0.le
      have e1 : s - cos y = (sin y - y * cos y) / y := by
        rw [hs]; field_simp
      rw [e1, div_le_iff₀ hy0]
      refine le_trans h (le_of_eq ?_)
      ring
    have h3 : a * (s - cos y) / (2 * m ^ 2) ≤ a * (2 * x ^ 2 / 3) := by
      rw [div_le_iff₀ (by positivity)]
      have h4 := mul_le_mul_of_nonneg_left h2 ha0
      refine le_trans h4 (le_of_eq ?_)
      rw [hy]; ring
    have h5 := mul_le_mul_of_nonneg_left h1 ha0
    have h6 : a * (3 * s - cos y) + a * (s - cos y) / (2 * m ^ 2) - 2 ≤ 0 := by
      have e2 : a * (1 + x ^ 2 / 3) = a + a * x ^ 2 / 3 := by ring
      have e3 : a * (2 * x ^ 2 / 3) = 2 * (a * x ^ 2 / 3) := by ring
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h6

lemma H_even (N : ℕ) (θ : ℝ) : H N (-θ) = H N θ := by
  unfold H
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  congr 1
  unfold c
  rw [show 2 * π * -θ * ((((k : ℤ) - l : ℤ)) : ℝ) = -(2 * π * θ * ((((k : ℤ) - l : ℤ)) : ℝ)) by ring,
    cos_neg]

lemma H_add_int (N : ℕ) (θ : ℝ) (n : ℤ) : H N (θ + n) = H N θ := by
  unfold H
  refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
  rw [c_add_int]

/-- **The normalized kernel decreases with the number of clusters.** -/
theorem weight_antitone (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N) (θ : ℝ) :
    H N θ / H N 0 ≤ H M θ / H M 0 := by
  have hN : 1 ≤ N := le_trans hM hMN
  -- reduce to the distance from the nearest integer
  set φ := |θ - round θ| with hφ
  have hred : ∀ K : ℕ, H K θ = H K φ := by
    intro K
    have h1 : H K (θ - round θ) = H K θ := by
      have := H_add_int K θ (-round θ)
      rwa [Int.cast_neg, ← sub_eq_add_neg] at this
    rcases abs_choice (θ - round θ) with h | h
    · rw [hφ, h, h1]
    · rw [hφ, h, H_even, h1]
  rw [hred M, hred N]
  have hφ0 : 0 ≤ φ := abs_nonneg _
  have hφ2 : φ ≤ 1 / 2 := abs_sub_round θ
  rcases eq_or_lt_of_le hφ0 with h0 | h0
  · rw [← h0, div_self (H_at_zero_pos N hN).ne', div_self (H_at_zero_pos M hM).ne']
  set x := π * φ with hx
  have hx0 : 0 < x := mul_pos pi_pos h0
  have hx2 : x ≤ π / 2 := by
    have := mul_le_mul_of_nonneg_left hφ2 pi_pos.le
    rw [hx]; linarith
  have hsin : 0 < sin x := sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_pos])
  have hW : ∀ K : ℕ, 1 ≤ K → H K φ / H K 0
      = 3 / sin x ^ 2 * ((1 - cos x / sin x * sin (2 * (K : ℝ) * x) / (2 * (K : ℝ)))
          / (2 * (K : ℝ) ^ 2 + 1)) := by
    intro K hK
    have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    have h := H_mul_sin K φ (by rw [← hx]; exact hsin.ne')
    rw [← hx] at h
    have h' : H K φ = (K - cos x / sin x * sin (2 * K * x) / 2) / sin x ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hsin.ne')]
      exact h
    rw [h', H_at_zero]
    have h1 := hsin.ne'
    have h2 : (2 : ℝ) * (K : ℝ) ^ 2 + 1 ≠ 0 := by positivity
    have h3 := hKr.ne'
    field_simp
  rw [hW N hN, hW M hM]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact antitone_aux hx0 hx2 (Set.mem_Ici.mpr hMr) (Set.mem_Ici.mpr hNr) (by exact_mod_cast hMN)

/-- **More clusters never increase `κ`.** -/
theorem kappa_antitone (M N u v : ℕ) (Y Z : Finset ℤ) (hM : 1 ≤ M) (hMN : M ≤ N) :
    kappaD N u v Y Z ≤ kappaD M u v Y Z := by
  unfold kappaD
  refine sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left (weight_antitone M N hM hMN _) ?_
  unfold G
  exact div_nonneg (mul_nonneg (power_nonneg _ _ _) (power_nonneg _ _ _))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

end TwoPrimesKernel
