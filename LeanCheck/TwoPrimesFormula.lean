import Mathlib

/-!
# The energy at far-apart heights

Two top steps `u` and `v` with `v ≥ 20 D u`, the height `X = D v`, and two finite sets of integers `Y`, `Z`
(the lower digit sets) with `D |y| < u` and `D |z| < v`. The sets are

`A = {j u + y ∈ [0, X]}`,  `B = {k v + z ∈ [0, X]}`.

* `H N θ` is the kernel `K_N(θ) = ∑_{|m|<N} (N-|m|)² e(mθ)`, written as a double sum;
* `H_eq` : `K_N = 2 ∑_{j<N} F_j + F_N` (Fejer kernels), so `K_N ≥ 0`;
* `H_succ_le` : `K_{D+1} ≤ (1 + 4/(D-2)) K_D`;
* `H_ge_near`, `weight_le_far` : the two bounds for the weight `K_D(θ)/K_D(0)`;
* `energy_formula` : `(1 - 5/D) (4/3) κ_D ≤ C ≤ (1 + 5/D) (4/3) κ_D`;
* `energy_le_kappa` : `C ≤ 1.36 κ`;
* `energy_lower`, `energy_of_kappaD`, `kappaD_of_energy`, `near_sum_le` : the consequences.

**Assumed from the first article, not formalized here:** that the balls of radius `1/D` below the height are
the sets `A` and `B` formed with the digit sets (the digit theorem).
-/

namespace TwoPrimesFormula

open Finset Real

noncomputable section

/-! ## The kernels -/

/-- `cos (2 π θ m)`. -/
def c (θ : ℝ) (m : ℤ) : ℝ := Real.cos (2 * π * θ * m)

/-- The Fejer kernel `F_N(θ) = |∑_{k<N} e(kθ)|²`, as a double sum. -/
def F (N : ℕ) (θ : ℝ) : ℝ := ∑ k ∈ range N, ∑ l ∈ range N, c θ ((k : ℤ) - l)

/-- The kernel `K_N(θ) = ∑_{|m|<N} (N-|m|)² e(mθ)`, as a double sum. -/
def H (N : ℕ) (θ : ℝ) : ℝ :=
  ∑ k ∈ range N, ∑ l ∈ range N, ((N : ℝ) - |(((k : ℤ) - l : ℤ) : ℝ)|) * c θ ((k : ℤ) - l)

lemma c_neg (θ : ℝ) (m : ℤ) : c θ (-m) = c θ m := by
  unfold c
  rw [show 2 * π * θ * ((-m : ℤ) : ℝ) = -(2 * π * θ * (m : ℝ)) by push_cast; ring, Real.cos_neg]

lemma c_zero (θ : ℝ) : c θ 0 = 1 := by simp [c]

lemma c_le_one (θ : ℝ) (m : ℤ) : c θ m ≤ 1 := Real.cos_le_one _

lemma sum_sq_succ {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) (N : ℕ) :
    ∑ k ∈ range (N + 1), ∑ l ∈ range (N + 1), f k l
      = (∑ k ∈ range N, ∑ l ∈ range N, f k l) + (∑ k ∈ range N, f k N)
        + (∑ l ∈ range N, f N l) + f N N := by
  simp only [sum_range_succ, sum_add_distrib]
  abel

lemma F_succ (N : ℕ) (θ : ℝ) :
    F (N + 1) θ = F N θ + 2 * (∑ k ∈ range N, c θ ((N : ℤ) - k)) + 1 := by
  unfold F
  rw [sum_sq_succ]
  have h1 : ∑ k ∈ range N, c θ ((k : ℤ) - N) = ∑ k ∈ range N, c θ ((N : ℤ) - k) :=
    sum_congr rfl fun k _ => by rw [← c_neg θ ((N : ℤ) - k), neg_sub]
  rw [h1, sub_self, c_zero]
  ring

lemma F_eq (N : ℕ) (θ : ℝ) :
    F N θ = N + 2 * ∑ k ∈ range N, (k : ℝ) * c θ ((N : ℤ) - k) := by
  induction N with
  | zero => simp [F]
  | succ N ih =>
    rw [F_succ, ih]
    have h : ∑ k ∈ range (N + 1), (k : ℝ) * c θ (((N + 1 : ℕ) : ℤ) - k)
        = (∑ k ∈ range N, (k : ℝ) * c θ ((N : ℤ) - k)) + ∑ k ∈ range N, c θ ((N : ℤ) - k) := by
      rw [sum_range_succ', ← sum_add_distrib]
      simp only [Nat.cast_zero, zero_mul, add_zero]
      refine sum_congr rfl fun k _ => ?_
      have e1 : (((N + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ)) = (N : ℤ) - k := by push_cast; ring
      rw [e1]
      push_cast
      ring
    rw [h]
    push_cast
    ring

lemma H_succ (N : ℕ) (θ : ℝ) : H (N + 1) θ = H N θ + F N θ + F (N + 1) θ := by
  have hsplit : H (N + 1) θ = F (N + 1) θ
      + ∑ k ∈ range (N + 1), ∑ l ∈ range (N + 1),
          ((N : ℝ) - |(((k : ℤ) - l : ℤ) : ℝ)|) * c θ ((k : ℤ) - l) := by
    unfold H F
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    push_cast
    ring
  have hrest : ∑ k ∈ range (N + 1), ∑ l ∈ range (N + 1),
        ((N : ℝ) - |(((k : ℤ) - l : ℤ) : ℝ)|) * c θ ((k : ℤ) - l) = H N θ + F N θ := by
    rw [sum_sq_succ, F_eq N θ]
    have hw : ∀ k ∈ range N, ((N : ℝ) - |((((N : ℤ) - k : ℤ)) : ℝ)|) = k := by
      intro k hk
      have hk' : (k : ℝ) ≤ N := by exact_mod_cast (mem_range.mp hk).le
      push_cast
      rw [abs_of_nonneg (by linarith)]
      ring
    have h2 : ∑ l ∈ range N, ((N : ℝ) - |((((N : ℤ) - l : ℤ)) : ℝ)|) * c θ ((N : ℤ) - l)
        = ∑ k ∈ range N, (k : ℝ) * c θ ((N : ℤ) - k) :=
      sum_congr rfl fun k hk => by rw [hw k hk]
    have h1 : ∑ k ∈ range N, ((N : ℝ) - |((((k : ℤ) - N : ℤ)) : ℝ)|) * c θ ((k : ℤ) - N)
        = ∑ k ∈ range N, (k : ℝ) * c θ ((N : ℤ) - k) := by
      refine sum_congr rfl fun k hk => ?_
      have e1 : ((k : ℤ) - N) = -((N : ℤ) - k) := by ring
      rw [e1, c_neg, Int.cast_neg, abs_neg, hw k hk]
    rw [h1, h2, sub_self, c_zero, Int.cast_zero, abs_zero]
    unfold H
    ring
  rw [hsplit, hrest]
  ring

/-- `K_N = 2 ∑_{j<N} F_j + F_N`. -/
lemma H_eq (N : ℕ) (θ : ℝ) : H N θ = 2 * (∑ j ∈ range N, F j θ) + F N θ := by
  induction N with
  | zero => simp [H, F]
  | succ N ih =>
    rw [H_succ, ih, sum_range_succ]
    ring

/-- The sums of cosines and of sines. -/
def Cs (N : ℕ) (θ : ℝ) : ℝ := ∑ k ∈ range N, Real.cos (2 * π * θ * k)
def Sn (N : ℕ) (θ : ℝ) : ℝ := ∑ k ∈ range N, Real.sin (2 * π * θ * k)

lemma F_eq_squares (N : ℕ) (θ : ℝ) : F N θ = Cs N θ ^ 2 + Sn N θ ^ 2 := by
  unfold F Cs Sn
  rw [sq, sq, sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  unfold c
  rw [show 2 * π * θ * ((((k : ℤ) - l : ℤ)) : ℝ) = 2 * π * θ * k - 2 * π * θ * l by push_cast; ring,
    Real.cos_sub]

lemma F_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ F N θ := by
  rw [F_eq_squares]; positivity

lemma H_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ H N θ := by
  rw [H_eq]
  have := sum_nonneg (s := range N) fun j _ => F_nonneg j θ
  have := F_nonneg N θ
  linarith

lemma F_add_le (a b : ℕ) (θ : ℝ) : F (a + b) θ ≤ 2 * (F a θ + F b θ) := by
  set α := 2 * π * θ * a with hα
  have hC : Cs (a + b) θ = Cs a θ + (Real.cos α * Cs b θ - Real.sin α * Sn b θ) := by
    unfold Cs Sn
    rw [sum_range_add, mul_sum, mul_sum, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [show 2 * π * θ * (((a + k : ℕ)) : ℝ) = α + 2 * π * θ * k by rw [hα]; push_cast; ring,
      Real.cos_add]
  have hS : Sn (a + b) θ = Sn a θ + (Real.sin α * Cs b θ + Real.cos α * Sn b θ) := by
    unfold Cs Sn
    rw [sum_range_add, mul_sum, mul_sum, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [show 2 * π * θ * (((a + k : ℕ)) : ℝ) = α + 2 * π * θ * k by rw [hα]; push_cast; ring,
      Real.sin_add]
  rw [F_eq_squares, F_eq_squares, F_eq_squares, hC, hS]
  have hsc := Real.sin_sq_add_cos_sq α
  set x := Real.cos α * Cs b θ - Real.sin α * Sn b θ with hx
  set y := Real.sin α * Cs b θ + Real.cos α * Sn b θ with hy
  have hxy : x ^ 2 + y ^ 2 = Cs b θ ^ 2 + Sn b θ ^ 2 := by
    rw [hx, hy]
    linear_combination (Cs b θ ^ 2 + Sn b θ ^ 2) * hsc
  nlinarith [sq_nonneg (Cs a θ - x), sq_nonneg (Sn a θ - y)]

/-- `K_{D+1} ≤ (1 + 4/(D-2)) K_D`. -/
lemma H_succ_le (D : ℕ) (hD : 3 ≤ D) (θ : ℝ) :
    H (D + 1) θ ≤ (1 + 4 / ((D : ℝ) - 2)) * H D θ := by
  have hDr : (3 : ℝ) ≤ D := by exact_mod_cast hD
  have hnn : ∀ s : Finset ℕ, s ⊆ range D → ∑ j ∈ s, F j θ ≤ ∑ j ∈ range D, F j θ :=
    fun s hs => sum_le_sum_of_subset_of_nonneg hs fun j _ _ => F_nonneg j θ
  have h2sum : 2 * (∑ j ∈ range D, F j θ) ≤ H D θ := by
    rw [H_eq]; have := F_nonneg D θ; linarith
  have hA : ((D : ℝ) - 1) * F D θ ≤ 2 * H D θ := by
    have h1 : ∑ _a ∈ Ico 1 D, F D θ ≤ ∑ a ∈ Ico 1 D, 2 * (F a θ + F (D - a) θ) := by
      refine sum_le_sum fun a ha => ?_
      have ha' := mem_Ico.mp ha
      have e1 : a + (D - a) = D := by omega
      calc F D θ = F (a + (D - a)) θ := by rw [e1]
        _ ≤ _ := F_add_le _ _ _
    have h3 : ∑ a ∈ Ico 1 D, F (D - a) θ = ∑ a ∈ Ico 1 D, F a θ := by
      refine sum_nbij' (fun a => D - a) (fun a => D - a) ?_ ?_ ?_ ?_ ?_
      · intro a ha; simp only [mem_Ico, mem_coe] at ha ⊢; omega
      · intro a ha; simp only [mem_Ico, mem_coe] at ha ⊢; omega
      · intro a ha; simp only [mem_Ico, mem_coe] at ha ⊢; omega
      · intro a ha; simp only [mem_Ico, mem_coe] at ha ⊢; omega
      · intro a _; rfl
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul, ← mul_sum, sum_add_distrib, h3,
      Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_one] at h1
    have h4 := hnn (Ico 1 D) fun a ha => mem_range.mpr (mem_Ico.mp ha).2
    linarith
  have hB : ((D : ℝ) - 2) * F (D + 1) θ ≤ 2 * H D θ := by
    have h1 : ∑ _a ∈ Ico 2 D, F (D + 1) θ ≤ ∑ a ∈ Ico 2 D, 2 * (F a θ + F (D + 1 - a) θ) := by
      refine sum_le_sum fun a ha => ?_
      have ha' := mem_Ico.mp ha
      have e1 : a + (D + 1 - a) = D + 1 := by omega
      calc F (D + 1) θ = F (a + (D + 1 - a)) θ := by rw [e1]
        _ ≤ _ := F_add_le _ _ _
    have h3 : ∑ a ∈ Ico 2 D, F (D + 1 - a) θ = ∑ a ∈ Ico 2 D, F a θ := by
      refine sum_nbij' (fun a => D + 1 - a) (fun a => D + 1 - a) ?_ ?_ ?_ ?_ ?_
      · intro a ha; simp only [mem_Ico, mem_coe] at ha ⊢; omega
      · intro a ha; simp only [mem_Ico, mem_coe] at ha ⊢; omega
      · intro a ha; simp only [mem_Ico, mem_coe] at ha ⊢; omega
      · intro a ha; simp only [mem_Ico, mem_coe] at ha ⊢; omega
      · intro a _; rfl
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul, ← mul_sum, sum_add_distrib, h3,
      Nat.cast_sub (by omega : 2 ≤ D), Nat.cast_ofNat] at h1
    have h4 := hnn (Ico 2 D) fun a ha => mem_range.mpr (mem_Ico.mp ha).2
    linarith
  have hHD := H_nonneg D θ
  have hd2 : (0 : ℝ) < (D : ℝ) - 2 := by linarith
  have hFD : F D θ ≤ 2 * H D θ / ((D : ℝ) - 2) := by
    rw [le_div_iff₀ hd2]
    have := F_nonneg D θ
    nlinarith [hA]
  have hFD1 : F (D + 1) θ ≤ 2 * H D θ / ((D : ℝ) - 2) := by
    rw [le_div_iff₀ hd2]; linarith
  rw [H_succ]
  have e2 : (1 + 4 / ((D : ℝ) - 2)) * H D θ
      = H D θ + 2 * H D θ / ((D : ℝ) - 2) + 2 * H D θ / ((D : ℝ) - 2) := by ring
  linarith

lemma F_at_zero (N : ℕ) : F N 0 = (N : ℝ) ^ 2 := by
  have h : ∀ m : ℤ, c 0 m = 1 := fun m => by simp [c]
  simp only [F, h, sum_const, card_range, nsmul_eq_mul, mul_one]
  ring

/-- `K_N(0) = N (2 N² + 1) / 3`. -/
lemma H_at_zero (N : ℕ) : H N 0 = (N : ℝ) * (2 * (N : ℝ) ^ 2 + 1) / 3 := by
  induction N with
  | zero => simp [H]
  | succ N ih =>
    rw [H_succ, ih, F_at_zero, F_at_zero]
    push_cast
    ring

lemma H_at_zero_pos (N : ℕ) (hN : 1 ≤ N) : 0 < H N 0 := by
  rw [H_at_zero]
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  positivity

lemma F_le_at_zero (N : ℕ) (θ : ℝ) : F N θ ≤ F N 0 := by
  have h : ∀ m : ℤ, c 0 m = 1 := fun m => by simp [c]
  exact sum_le_sum fun k _ => sum_le_sum fun l _ => by rw [h]; exact c_le_one _ _

lemma H_le_at_zero (N : ℕ) (θ : ℝ) : H N θ ≤ H N 0 := by
  rw [H_eq, H_eq]
  have h1 : ∑ j ∈ range N, F j θ ≤ ∑ j ∈ range N, F j 0 := sum_le_sum fun j _ => F_le_at_zero j θ
  have h2 := F_le_at_zero N θ
  linarith

/-! ## The weight near and far from the integers -/

lemma c_add_int (θ : ℝ) (n m : ℤ) : c (θ + n) m = c θ m := by
  unfold c
  rw [show 2 * π * (θ + n) * (m : ℝ) = 2 * π * θ * m + ((n * m : ℤ) : ℝ) * (2 * π) by
    push_cast; ring, Real.cos_add_int_mul_two_pi]

lemma F_add_int (N : ℕ) (θ : ℝ) (n : ℤ) : F N (θ + n) = F N θ := by
  simp only [F, c_add_int]

lemma F_neg_theta (N : ℕ) (θ : ℝ) : F N (-θ) = F N θ := by
  have h : ∀ m : ℤ, c (-θ) m = c θ m := fun m => by
    unfold c
    rw [show 2 * π * -θ * (m : ℝ) = -(2 * π * θ * m) by ring, Real.cos_neg]
  simp only [F, h]

lemma F_abs_sub_int (N : ℕ) (θ : ℝ) (n : ℤ) : F N θ = F N |θ - n| := by
  have h : F N θ = F N (θ - n) := by
    have := F_add_int N (θ - n) n
    rwa [sub_add_cancel] at this
  rcases abs_choice (θ - n) with hc | hc
  · rw [h, hc]
  · rw [h, hc, F_neg_theta]

/-- The closed form `F_N(θ) sin²(πθ) = sin²(πNθ)`. -/
lemma F_closed (N : ℕ) (θ : ℝ) : F N θ * Real.sin (π * θ) ^ 2 = Real.sin (π * N * θ) ^ 2 := by
  set z : ℂ := Complex.exp (((2 * π * θ : ℝ) : ℂ) * Complex.I) with hz
  have hpow : ∀ k : ℕ, z ^ k = Complex.exp (((2 * π * θ * k : ℝ) : ℂ) * Complex.I) := by
    intro k
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum : F N θ = Complex.normSq (∑ k ∈ range N, z ^ k) := by
    rw [F_eq_squares, Complex.normSq_apply]
    have hre : (∑ k ∈ range N, z ^ k).re = Cs N θ := by
      rw [Complex.re_sum]
      exact sum_congr rfl fun k _ => by rw [hpow, Complex.exp_ofReal_mul_I_re]
    have him : (∑ k ∈ range N, z ^ k).im = Sn N θ := by
      rw [Complex.im_sum]
      exact sum_congr rfl fun k _ => by rw [hpow, Complex.exp_ofReal_mul_I_im]
    rw [hre, him]
    ring
  have hone : ∀ x : ℝ, Complex.normSq (Complex.exp ((x : ℂ) * Complex.I) - 1)
      = 4 * Real.sin (x / 2) ^ 2 := by
    intro x
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, Complex.one_re, Complex.one_im, sub_zero]
    have h1 := Real.sin_sq_add_cos_sq x
    have h2 : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      have h3 := Real.cos_two_mul' (x / 2)
      rw [show 2 * (x / 2) = x by ring] at h3
      have h4 := Real.sin_sq_add_cos_sq (x / 2)
      linarith
    nlinarith [h1, h2]
  have hgeo := geom_sum_mul z N
  have := congrArg Complex.normSq hgeo
  rw [map_mul, ← hsum, hpow N, hz, hone, hone] at this
  rw [show 2 * π * θ / 2 = π * θ by ring, show 2 * π * θ * N / 2 = π * N * θ by ring] at this
  linarith

/-- Near the integers the weight is at least `4/π²`. -/
lemma H_ge_near (D : ℕ) (θ : ℝ) (n : ℤ) (hθ : |θ - n| ≤ 1 / (2 * (D : ℝ))) (hD : 1 ≤ D) :
    4 / π ^ 2 * H D 0 ≤ H D θ := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hpi := Real.pi_pos
  have hF : ∀ j ≤ D, 4 / π ^ 2 * F j 0 ≤ F j θ := by
    intro j hj
    rw [F_abs_sub_int j θ n, F_at_zero]
    set x := |θ - n| with hx
    have hx0 : 0 ≤ x := abs_nonneg _
    rcases eq_or_lt_of_le hx0 with h0 | h0
    · rw [← h0, F_at_zero]
      have hp : 4 / π ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [Real.two_le_pi]
      nlinarith [sq_nonneg (j : ℝ)]
    · have hjx : (j : ℝ) * x ≤ 1 / 2 := by
        have h1 : (j : ℝ) ≤ D := by exact_mod_cast hj
        calc (j : ℝ) * x ≤ D * (1 / (2 * (D : ℝ))) := by
              exact mul_le_mul h1 hθ hx0 (by positivity)
          _ = 1 / 2 := by
              have : (D : ℝ) ≠ 0 := by positivity
              field_simp
      have hjx0 : 0 ≤ π * j * x := by positivity
      have hjx1 : π * j * x ≤ π / 2 := by nlinarith
      have hlow := Real.mul_le_sin hjx0 hjx1
      have e1 : 2 / π * (π * j * x) = 2 * (j : ℝ) * x := by
        field_simp
      rw [e1] at hlow
      have hx1 : x ≤ 1 / 2 := by
        refine le_trans hθ ?_
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have hs1 : Real.sin (π * x) ≤ π * x := Real.sin_le (by positivity)
      have hs0 : 0 < Real.sin (π * x) := by
        refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
        nlinarith
      have hcl := F_closed j x
      have hsin : (2 * (j : ℝ) * x) ^ 2 ≤ Real.sin (π * j * x) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hlow 2
      have hsq : Real.sin (π * x) ^ 2 ≤ (π * x) ^ 2 := pow_le_pow_left₀ hs0.le hs1 2
      have hFn := F_nonneg j x
      have h5 : (2 * (j : ℝ) * x) ^ 2 ≤ F j x * (π * x) ^ 2 := by
        refine le_trans hsin (hcl ▸ mul_le_mul_of_nonneg_left hsq hFn)
      have h6 : 4 * (j : ℝ) ^ 2 ≤ F j x * π ^ 2 := by
        have hx2 : 0 < x ^ 2 := by positivity
        refine le_of_mul_le_mul_right ?_ hx2
        calc 4 * (j : ℝ) ^ 2 * x ^ 2 = (2 * (j : ℝ) * x) ^ 2 := by ring
          _ ≤ F j x * (π * x) ^ 2 := h5
          _ = F j x * π ^ 2 * x ^ 2 := by ring
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact h6
  rw [H_eq, H_eq]
  have h1 : ∑ j ∈ range D, 4 / π ^ 2 * F j 0 ≤ ∑ j ∈ range D, F j θ :=
    sum_le_sum fun j hj => hF j (mem_range.mp hj).le
  rw [← mul_sum] at h1
  have h2 := hF D le_rfl
  have e : 4 / π ^ 2 * (2 * ∑ j ∈ range D, F j 0 + F D 0)
      = 2 * (4 / π ^ 2 * ∑ j ∈ range D, F j 0) + 4 / π ^ 2 * F D 0 := by ring
  rw [e]
  linarith

/-- Far from the integers `K_D(θ) ≤ (2D-1)/(4δ²)`, where `δ` is the distance to the integers. -/
lemma H_le_far (D : ℕ) (hD : 1 ≤ D) (θ : ℝ) (n : ℤ) (h0 : 0 < |θ - n|) (h1 : |θ - n| ≤ 1 / 2) :
    H D θ ≤ (2 * (D : ℝ) - 1) / (4 * |θ - n| ^ 2) := by
  have hpi := Real.pi_pos
  set x := |θ - n| with hx
  have hxpi : π * x ≤ π / 2 := by nlinarith
  have hlow := Real.mul_le_sin (x := π * x) (by positivity) hxpi
  have e1 : 2 / π * (π * x) = 2 * x := by field_simp
  rw [e1] at hlow
  have hs : (2 * x) ^ 2 ≤ Real.sin (π * x) ^ 2 := pow_le_pow_left₀ (by positivity) hlow 2
  have hF : ∀ j : ℕ, F j θ ≤ 1 / (4 * x ^ 2) := by
    intro j
    rw [F_abs_sub_int j θ n, ← hx, le_div_iff₀ (by positivity)]
    have hcl := F_closed j x
    have hFn := F_nonneg j x
    have h2 : F j x * (2 * x) ^ 2 ≤ 1 := by
      refine le_trans (mul_le_mul_of_nonneg_left hs hFn) ?_
      rw [hcl]
      exact Real.sin_sq_le_one _
    calc F j x * (4 * x ^ 2) = F j x * (2 * x) ^ 2 := by ring
      _ ≤ 1 := h2
  rw [H_eq]
  have hsum : ∑ j ∈ range D, F j θ ≤ ((D : ℝ) - 1) * (1 / (4 * x ^ 2)) := by
    obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
    rw [sum_range_succ']
    have h0' : F 0 θ = 0 := by simp [F]
    rw [h0', add_zero]
    refine le_trans (sum_le_sum fun j _ => hF (j + 1)) ?_
    rw [sum_const, card_range, nsmul_eq_mul]
    push_cast
    rw [add_sub_cancel_right]
  have h3 := hF D
  have e2 : (2 * (D : ℝ) - 1) / (4 * x ^ 2)
      = 2 * (((D : ℝ) - 1) * (1 / (4 * x ^ 2))) + 1 / (4 * x ^ 2) := by ring
  rw [e2]
  linarith

/-- Far from the integers the weight is at most `3/(4 D² δ²)`. -/
lemma weight_le_far (D : ℕ) (hD : 1 ≤ D) (θ : ℝ) (n : ℤ) (h0 : 0 < |θ - n|) (h1 : |θ - n| ≤ 1 / 2) :
    H D θ / H D 0 ≤ 3 / (4 * (D : ℝ) ^ 2 * |θ - n| ^ 2) := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hH := H_at_zero_pos D hD
  have h2 := H_le_far D hD θ n h0 h1
  set x := |θ - n| with hx
  rw [div_le_iff₀ hH]
  refine le_trans h2 ?_
  rw [H_at_zero, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (2 * (D : ℝ) - 1) * D ≤ 2 * (D : ℝ) ^ 2 + 1 := by nlinarith
  have h4 : 0 ≤ 4 * (D : ℝ) * x ^ 2 := by positivity
  have h5 := mul_le_mul_of_nonneg_right h3 h4
  nlinarith [h5]

/-! ## Characters -/

/-- `e(t) = exp(2πit)`. -/
def e (t : ℝ) : ℂ := Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I)

lemma e_add (s t : ℝ) : e (s + t) = e s * e t := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma conj_e (t : ℝ) : (starRingEnd ℂ) (e t) = e (-t) := by
  unfold e
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma e_re (t : ℝ) : (e t).re = Real.cos (2 * π * t) := by
  unfold e; rw [Complex.exp_ofReal_mul_I_re]

/-- The squared character sum of a finite set. -/
def power (u : ℕ) (Y : Finset ℤ) (ξ : ℕ) : ℝ :=
  Complex.normSq (∑ y ∈ Y, e ((ξ : ℝ) * y / u))

lemma power_nonneg (u : ℕ) (Y : Finset ℤ) (ξ : ℕ) : 0 ≤ power u Y ξ := Complex.normSq_nonneg _

lemma power_zero (u : ℕ) (Y : Finset ℤ) : power u Y 0 = (Y.card : ℝ) ^ 2 := by
  have h : ∀ y ∈ Y, e (((0 : ℕ) : ℝ) * y / u) = 1 := fun y _ => by simp [e]
  unfold power
  rw [sum_congr rfl h, sum_const, nsmul_eq_mul, mul_one, Complex.normSq_natCast]
  ring

/-- Orthogonality of the characters modulo `u`. -/
lemma sum_cos_mod (u : ℕ) (hu : 0 < u) (n : ℤ) :
    ∑ ξ ∈ range u, Real.cos (2 * π * ((ξ : ℝ) * n / u)) = if (u : ℤ) ∣ n then (u : ℝ) else 0 := by
  have hur : (u : ℝ) ≠ 0 := by positivity
  split
  · rename_i h
    obtain ⟨k, rfl⟩ := h
    have h1 : ∀ ξ ∈ range u, Real.cos (2 * π * ((ξ : ℝ) * (((u : ℤ) * k : ℤ) : ℝ) / u)) = 1 := by
      intro ξ _
      rw [show 2 * π * ((ξ : ℝ) * (((u : ℤ) * k : ℤ) : ℝ) / u) = (((ξ : ℤ) * k : ℤ) : ℝ) * (2 * π) by
        push_cast; field_simp]
      exact Real.cos_int_mul_two_pi _
    rw [sum_congr rfl h1]
    simp
  · rename_i h
    set z := e ((n : ℝ) / u) with hz
    have hpow : ∀ k : ℕ, z ^ k = e ((k : ℝ) * n / u) := by
      intro k
      rw [hz]
      unfold e
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hz1 : z ≠ 1 := by
      intro h1
      rw [hz] at h1
      unfold e at h1
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h1
      apply h
      have h2 := congrArg Complex.im hm
      simp [Complex.mul_im] at h2
      have h3 : (n : ℝ) = (u : ℝ) * m := by
        have hpi : π ≠ 0 := Real.pi_pos.ne'
        field_simp at h2
        linarith
      exact ⟨m, by exact_mod_cast h3⟩
    have hzu : z ^ u = 1 := by
      rw [hpow]
      unfold e
      rw [show (u : ℝ) * n / u = n by field_simp]
      have := Complex.exp_int_mul_two_pi_mul_I n
      rw [← this]
      congr 1
      push_cast
      ring
    have hsum : ∑ ξ ∈ range u, z ^ ξ = 0 := by
      rw [geom_sum_eq hz1, hzu, sub_self, zero_div]
    have := congrArg Complex.re hsum
    rw [Complex.re_sum, Complex.zero_re] at this
    rw [← this]
    exact sum_congr rfl fun ξ _ => by rw [hpow, e_re]

/-- The fourfold sum factors into the two squared character sums. -/
lemma sum_cos_quad (a β : ℝ) (Y Z : Finset ℤ) :
    ∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
        Real.cos (a + 2 * π * (β * (((z : ℝ) - z') - ((y : ℝ) - y'))))
      = Real.cos a * Complex.normSq (∑ y ∈ Y, e (β * y))
          * Complex.normSq (∑ z ∈ Z, e (β * z)) := by
  set w : ℂ := Complex.exp ((a : ℂ) * Complex.I) with hw
  set SY := ∑ y ∈ Y, e (β * y) with hSY
  set SZ := ∑ z ∈ Z, e (β * z) with hSZ
  have hterm : ∀ z z' y y' : ℤ,
      Real.cos (a + 2 * π * (β * (((z : ℝ) - z') - ((y : ℝ) - y'))))
        = (w * (e (β * z) * (starRingEnd ℂ) (e (β * z')))
            * ((starRingEnd ℂ) (e (β * y)) * e (β * y'))).re := by
    intro z z' y y'
    have h1 : w * (e (β * z) * (starRingEnd ℂ) (e (β * z')))
          * ((starRingEnd ℂ) (e (β * y)) * e (β * y'))
        = Complex.exp (((a + 2 * π * (β * (((z : ℝ) - z') - ((y : ℝ) - y'))) : ℝ) : ℂ)
            * Complex.I) := by
      rw [conj_e, conj_e, hw]
      unfold e
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [h1, Complex.exp_ofReal_mul_I_re]
  have hQY : ∑ y ∈ Y, ∑ y' ∈ Y, (starRingEnd ℂ) (e (β * y)) * e (β * y')
      = (starRingEnd ℂ) SY * SY := by
    rw [hSY, map_sum, sum_mul_sum]
  have hQZ : ∑ z ∈ Z, ∑ z' ∈ Z, e (β * z) * (starRingEnd ℂ) (e (β * z'))
      = SZ * (starRingEnd ℂ) SZ := by
    rw [hSZ, map_sum, sum_mul_sum]
  have hsum : ∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
        w * (e (β * z) * (starRingEnd ℂ) (e (β * z')))
          * ((starRingEnd ℂ) (e (β * y)) * e (β * y'))
      = w * (SZ * (starRingEnd ℂ) SZ) * ((starRingEnd ℂ) SY * SY) := by
    have h1 : ∀ z z' : ℤ, ∑ y ∈ Y, ∑ y' ∈ Y,
          w * (e (β * z) * (starRingEnd ℂ) (e (β * z')))
            * ((starRingEnd ℂ) (e (β * y)) * e (β * y'))
        = w * (e (β * z) * (starRingEnd ℂ) (e (β * z'))) * ((starRingEnd ℂ) SY * SY) := by
      intro z z'
      rw [← hQY]
      simp only [mul_sum]
    simp only [h1]
    rw [← hQZ]
    simp only [mul_sum, sum_mul]
  have h2 := congrArg Complex.re hsum
  simp only [Complex.re_sum] at h2
  simp only [hterm]
  rw [h2]
  have h3 : w * (SZ * (starRingEnd ℂ) SZ) * ((starRingEnd ℂ) SY * SY)
      = w * ((Complex.normSq SY * Complex.normSq SZ : ℝ) : ℂ) := by
    rw [Complex.mul_conj, mul_comm ((starRingEnd ℂ) SY) SY, Complex.mul_conj]
    push_cast
    ring
  rw [h3, Complex.re_mul_ofReal, hw, Complex.exp_ofReal_mul_I_re]
  ring

/-- The indicator of divisibility by `u`. -/
def ind (u : ℕ) (n : ℤ) : ℝ := if (u : ℤ) ∣ n then 1 else 0

lemma ind_nonneg (u : ℕ) (n : ℤ) : 0 ≤ ind u n := by unfold ind; split <;> norm_num

lemma ind_eq (u : ℕ) (hu : 0 < u) (n : ℤ) :
    ind u n = (1 / (u : ℝ)) * ∑ ξ ∈ range u, Real.cos (2 * π * ((ξ : ℝ) * n / u)) := by
  have hur : (u : ℝ) ≠ 0 := by positivity
  rw [sum_cos_mod u hu n]
  unfold ind
  split <;> simp [hur]

/-- The Fourier form of the weighted congruence count. -/
lemma fourier (u v : ℕ) (hu : 0 < u) (K : Finset ℕ) (W : ℤ → ℝ) (Y Z : Finset ℤ) :
    ∑ k ∈ K, ∑ k' ∈ K, W ((k : ℤ) - k') *
        (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
          ind u (((k : ℤ) - k') * v + (z - z') - (y - y')))
      = (1 / (u : ℝ)) * ∑ ξ ∈ range u, power u Y ξ * power u Z ξ *
          (∑ k ∈ K, ∑ k' ∈ K, W ((k : ℤ) - k') * c ((ξ : ℝ) * v / u) ((k : ℤ) - k')) := by
  have hcount : ∀ m : ℤ, (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
        ind u (m * v + (z - z') - (y - y')))
      = (1 / (u : ℝ)) * ∑ ξ ∈ range u,
          c ((ξ : ℝ) * v / u) m * power u Y ξ * power u Z ξ := by
    intro m
    have hq : ∀ ξ : ℕ, (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
          Real.cos (2 * π * ((ξ : ℝ) * ((m * v + (z - z') - (y - y') : ℤ) : ℝ) / u)))
        = c ((ξ : ℝ) * v / u) m * power u Y ξ * power u Z ξ := by
      intro ξ
      have h := sum_cos_quad (2 * π * ((ξ : ℝ) * v / u) * m) ((ξ : ℝ) / u) Y Z
      have h1 : ∀ S : Finset ℤ, Complex.normSq (∑ y ∈ S, e ((ξ : ℝ) / u * y)) = power u S ξ := by
        intro S
        unfold power
        exact congrArg _ (sum_congr rfl fun y _ => by rw [div_mul_eq_mul_div])
      rw [h1, h1] at h
      unfold c
      rw [← h]
      refine sum_congr rfl fun z _ => sum_congr rfl fun z' _ =>
        sum_congr rfl fun y _ => sum_congr rfl fun y' _ => ?_
      congr 1
      push_cast
      ring
    have hswap : (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y, ∑ ξ ∈ range u,
          Real.cos (2 * π * ((ξ : ℝ) * ((m * v + (z - z') - (y - y') : ℤ) : ℝ) / u)))
        = ∑ ξ ∈ range u, ∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
          Real.cos (2 * π * ((ξ : ℝ) * ((m * v + (z - z') - (y - y') : ℤ) : ℝ) / u)) := by
      symm
      rw [sum_comm]
      refine sum_congr rfl fun z _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun z' _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun y _ => ?_
      rw [sum_comm]
    simp only [ind_eq u hu, ← mul_sum]
    rw [hswap]
    simp only [hq]
  simp only [hcount]
  have h1 : ∀ k k' : ℕ, W ((k : ℤ) - k') * ((1 / (u : ℝ)) * ∑ ξ ∈ range u,
        c ((ξ : ℝ) * v / u) ((k : ℤ) - k') * power u Y ξ * power u Z ξ)
      = ∑ ξ ∈ range u, (1 / (u : ℝ)) * (power u Y ξ * power u Z ξ *
          (W ((k : ℤ) - k') * c ((ξ : ℝ) * v / u) ((k : ℤ) - k'))) := by
    intro k k'
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun ξ _ => by ring
  simp only [h1]
  rw [mul_sum]
  symm
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_comm]

/-! ## Product sets and the energy -/

/-- The numbers `j w + y`. -/
def prodSet (w : ℕ) (I : Finset ℕ) (Y : Finset ℤ) : Finset ℤ :=
  (I ×ˢ Y).image fun p => (p.1 : ℤ) * w + p.2

/-- The number of solutions of `a - a' = b - b'`. -/
def energy (A B : Finset ℤ) : ℝ :=
  ∑ b ∈ B, ∑ b' ∈ B, ∑ a ∈ A, ∑ a' ∈ A, if a - a' = b - b' then (1 : ℝ) else 0

lemma energy_mono {A A' B B' : Finset ℤ} (hA : A ⊆ A') (hB : B ⊆ B') :
    energy A B ≤ energy A' B' := by
  have hnn : ∀ a a' b b' : ℤ, (0 : ℝ) ≤ if a - a' = b - b' then (1 : ℝ) else 0 :=
    fun a a' b b' => by split <;> norm_num
  have hin : ∀ b b' : ℤ, (∑ a ∈ A, ∑ a' ∈ A, if a - a' = b - b' then (1 : ℝ) else 0)
      ≤ ∑ a ∈ A', ∑ a' ∈ A', if a - a' = b - b' then (1 : ℝ) else 0 := by
    intro b b'
    refine le_trans (sum_le_sum fun a _ =>
      sum_le_sum_of_subset_of_nonneg hA fun a' _ _ => hnn _ _ _ _) ?_
    exact sum_le_sum_of_subset_of_nonneg hA fun a _ _ => sum_nonneg fun a' _ => hnn _ _ _ _
  unfold energy
  refine le_trans (sum_le_sum fun b _ => sum_le_sum fun b' _ => hin b b') ?_
  refine le_trans (sum_le_sum fun b _ => sum_le_sum_of_subset_of_nonneg hB
    fun b' _ _ => sum_nonneg fun a _ => sum_nonneg fun a' _ => hnn _ _ _ _) ?_
  exact sum_le_sum_of_subset_of_nonneg hB fun b _ _ => sum_nonneg fun b' _ =>
    sum_nonneg fun a _ => sum_nonneg fun a' _ => hnn _ _ _ _

lemma digit_injOn (w : ℕ) (I : Finset ℕ) (Y : Finset ℤ) (hY : ∀ y ∈ Y, 2 * |y| < (w : ℤ)) :
    Set.InjOn (fun p : ℕ × ℤ => (p.1 : ℤ) * w + p.2) (I ×ˢ Y : Finset (ℕ × ℤ)) := by
  rintro ⟨j, y⟩ h ⟨j', y'⟩ h' heq
  simp only [mem_coe, mem_product] at h h'
  simp only at heq
  have h1 := hY y h.2
  have h2 := hY y' h'.2
  have h3 : ((j : ℤ) - j') * w = y' - y := by linear_combination heq
  have h4 : |y' - y| < (w : ℤ) := by
    have h5 := abs_sub y' y
    omega
  have h6 : y' - y = 0 := Int.eq_zero_of_abs_lt_dvd ⟨(j : ℤ) - j', by rw [mul_comm]; exact h3.symm⟩ h4
  have hw : (w : ℤ) ≠ 0 := by
    have := abs_nonneg y
    omega
  have h7 : (j : ℤ) - j' = 0 := by
    rcases mul_eq_zero.mp (h3.trans h6) with h8 | h8
    · exact h8
    · exact absurd h8 hw
  have hj : j = j' := by omega
  have hy : y = y' := by omega
  rw [hj, hy]

lemma sum_prodSet (w : ℕ) (I : Finset ℕ) (Y : Finset ℤ) (hY : ∀ y ∈ Y, 2 * |y| < (w : ℤ))
    (g : ℤ → ℝ) : ∑ a ∈ prodSet w I Y, g a = ∑ j ∈ I, ∑ y ∈ Y, g ((j : ℤ) * w + y) := by
  unfold prodSet
  rw [sum_image (digit_injOn w I Y hY), sum_product]

lemma card_prodSet (w : ℕ) (I : Finset ℕ) (Y : Finset ℤ) (hY : ∀ y ∈ Y, 2 * |y| < (w : ℤ)) :
    (prodSet w I Y).card = I.card * Y.card := by
  unfold prodSet
  rw [card_image_of_injOn (digit_injOn w I Y hY), card_product]

/-- The number of pairs of `M` consecutive integers with a given difference. -/
lemma card_diff (s M : ℕ) (h : ℤ) :
    ∑ j ∈ Ico s (s + M), ∑ j' ∈ Ico s (s + M), (if (j : ℤ) - j' = h then (1 : ℝ) else 0)
      = ((M - h.natAbs : ℕ) : ℝ) := by
  have hshift : ∑ j ∈ Ico s (s + M), ∑ j' ∈ Ico s (s + M), (if (j : ℤ) - j' = h then (1 : ℝ) else 0)
      = ∑ j ∈ range M, ∑ j' ∈ range M, (if (j : ℤ) - j' = h then (1 : ℝ) else 0) := by
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    refine sum_congr rfl fun j' _ => ?_
    have e1 : (((s + j : ℕ) : ℤ) - ((s + j' : ℕ) : ℤ)) = (j : ℤ) - j' := by push_cast; ring
    rw [e1]
  rw [hshift, ← sum_product', sum_boole]
  congr 1
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg h
  · have key : (range M ×ˢ range M).filter (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)
        = (range (M - n)).image (fun i => (i + n, i)) := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨b, by omega, by omega, rfl⟩
      · rintro ⟨i, hi, rfl, rfl⟩
        omega
    rw [key, card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).2), card_range]
    omega
  · have key : (range M ×ˢ range M).filter (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)
        = (range (M - n)).image (fun i => (i, i + n)) := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨a, by omega, rfl, by omega⟩
      · rintro ⟨i, hi, rfl, rfl⟩
        omega
    rw [key, card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).1), card_range]
    omega

/-- The weight of one difference `Δ`: the number of pairs of top digits. -/
def count (u M : ℕ) (Δ : ℤ) : ℝ := ind u Δ * ((M - (Δ / (u : ℤ)).natAbs : ℕ) : ℝ)

lemma count_pairs (u M s : ℕ) (hu : 0 < u) (Δ : ℤ) :
    ∑ j ∈ Ico s (s + M), ∑ j' ∈ Ico s (s + M),
        (if ((j : ℤ) - j') * u = Δ then (1 : ℝ) else 0) = count u M Δ := by
  have hu' : (u : ℤ) ≠ 0 := by exact_mod_cast hu.ne'
  unfold count ind
  split
  · rename_i h
    obtain ⟨k, rfl⟩ := h
    have h1 : ∀ j j' : ℕ, (((j : ℤ) - j') * u = (u : ℤ) * k) ↔ (j : ℤ) - j' = k := by
      intro j j'
      rw [mul_comm]
      exact ⟨fun h => mul_left_cancel₀ hu' h, fun h => by rw [h]⟩
    simp only [h1]
    rw [card_diff, Int.mul_ediv_cancel_left _ hu', one_mul]
  · rename_i h
    rw [zero_mul]
    refine sum_eq_zero fun j _ => sum_eq_zero fun j' _ => ?_
    rw [if_neg]
    intro h1
    exact h ⟨(j : ℤ) - j', by rw [← h1, mul_comm]⟩

lemma reorder (I : Finset ℕ) (Y : Finset ℤ) (f : ℕ → ℤ → ℕ → ℤ → ℝ) :
    ∑ j ∈ I, ∑ y ∈ Y, ∑ j' ∈ I, ∑ y' ∈ Y, f j y j' y'
      = ∑ y ∈ Y, ∑ y' ∈ Y, ∑ j ∈ I, ∑ j' ∈ I, f j y j' y' := by
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  have h1 : ∑ j ∈ I, ∑ j' ∈ I, ∑ y' ∈ Y, f j y j' y'
      = ∑ j ∈ I, ∑ y' ∈ Y, ∑ j' ∈ I, f j y j' y' :=
    sum_congr rfl fun j _ => sum_comm
  rw [h1, sum_comm]

/-- The exact energy of two product sets. -/
lemma energy_prod (u v M s : ℕ) (hu : 0 < u) (K : Finset ℕ) (Y Z : Finset ℤ)
    (hY : ∀ y ∈ Y, 2 * |y| < (u : ℤ)) (hZ : ∀ z ∈ Z, 2 * |z| < (v : ℤ)) :
    energy (prodSet u (Ico s (s + M)) Y) (prodSet v K Z)
      = ∑ k ∈ K, ∑ k' ∈ K, ∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
          count u M (((k : ℤ) - k') * v + (z - z') - (y - y')) := by
  have hr : ∀ h : ℤ, (∑ a ∈ prodSet u (Ico s (s + M)) Y, ∑ a' ∈ prodSet u (Ico s (s + M)) Y,
        if a - a' = h then (1 : ℝ) else 0)
      = ∑ y ∈ Y, ∑ y' ∈ Y, count u M (h - (y - y')) := by
    intro h
    rw [sum_prodSet u _ Y hY]
    simp only [sum_prodSet u _ Y hY]
    rw [reorder]
    refine sum_congr rfl fun y _ => sum_congr rfl fun y' _ => ?_
    rw [← count_pairs u M s hu]
    refine sum_congr rfl fun j _ => sum_congr rfl fun j' _ => ?_
    refine if_congr ?_ rfl rfl
    constructor
    · intro h1; linear_combination h1
    · intro h1; linear_combination h1
  unfold energy
  simp only [hr]
  rw [sum_prodSet v K Z hZ]
  simp only [sum_prodSet v K Z hZ]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun k' _ => sum_congr rfl fun z _ => sum_congr rfl fun z' _ =>
    sum_congr rfl fun y _ => sum_congr rfl fun y' _ => ?_
  congr 1
  ring

/-! ## The setting -/

/-- The set `A = {j u + y ∈ [0, D v]}`. -/
def setA (D u v : ℕ) (Y : Finset ℤ) : Finset ℤ :=
  (prodSet u (range (D * v / u + 2)) Y).filter fun a => 0 ≤ a ∧ a ≤ (D : ℤ) * v

/-- The set `B = {k v + z ∈ [0, D v]}`. -/
def setB (D v : ℕ) (Z : Finset ℤ) : Finset ℤ :=
  (prodSet v (range (D + 1)) Z).filter fun b => 0 ≤ b ∧ b ≤ (D : ℤ) * v

/-- The normalized collision energy `C = (2X+1) E / (|A| |B|)²`. -/
def C (D u v : ℕ) (Y Z : Finset ℤ) : ℝ :=
  (2 * ((D : ℝ) * v) + 1) * energy (setA D u v Y) (setB D v Z)
    / (((setA D u v Y).card : ℝ) * ((setB D v Z).card : ℝ)) ^ 2

/-- `|φ_Y(ξ/u)|² |φ_Z(ξ/u)|²`. -/
def G (u : ℕ) (Y Z : Finset ℤ) (ξ : ℕ) : ℝ :=
  power u Y ξ * power u Z ξ / ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2)

def kappa (u : ℕ) (Y Z : Finset ℤ) : ℝ := ∑ ξ ∈ range u, G u Y Z ξ

def kappaD (D u v : ℕ) (Y Z : Finset ℤ) : ℝ :=
  ∑ ξ ∈ range u, G u Y Z ξ * (H D ((ξ : ℝ) * v / u) / H D 0)

/-- The hypotheses of the theorems. -/
structure Setting (D u v : ℕ) (Y Z : Finset ℤ) : Prop where
  hD : 100 ≤ D
  hv : 20 * D * u ≤ v
  hYne : Y.Nonempty
  hY : ∀ y ∈ Y, (D : ℤ) * |y| < u
  hZ : ∀ z ∈ Z, (D : ℤ) * |z| < v
  hZ0 : (0 : ℤ) ∈ Z
  hZ5 : 5 ≤ Z.card

namespace Setting

variable {D u v : ℕ} {Y Z : Finset ℤ} (S : Setting D u v Y Z)
include S

lemma u_pos : 0 < u := by
  obtain ⟨y, hy⟩ := S.hYne
  have h1 := S.hY y hy
  have h2 : 0 ≤ (D : ℤ) * |y| := mul_nonneg (by positivity) (abs_nonneg _)
  omega

lemma v_pos : 0 < v := by
  have h1 := S.u_pos
  have h2 := S.hD
  have h3 : 0 < 20 * D * u := Nat.mul_pos (by omega) h1
  exact lt_of_lt_of_le h3 S.hv

lemma Y_small : ∀ y ∈ Y, 2 * |y| < (u : ℤ) := by
  intro y hy
  have h1 := S.hY y hy
  have h2 : (2 : ℤ) ≤ D := by have := S.hD; omega
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) h1

lemma Z_small : ∀ z ∈ Z, 2 * |z| < (v : ℤ) := by
  intro z hz
  have h1 := S.hZ z hz
  have h2 : (2 : ℤ) ≤ D := by have := S.hD; omega
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)) h1

lemma J_ge : 20 * D * D ≤ D * v / u := by
  rw [Nat.le_div_iff_mul_le S.u_pos]
  have := Nat.mul_le_mul_left D S.hv
  calc 20 * D * D * u = D * (20 * D * u) := by ring
    _ ≤ D * v := this

/-- The inner product sets. -/
lemma sub_setA : prodSet u (Ico 1 (D * v / u)) Y ⊆ setA D u v Y := by
  intro a ha
  unfold prodSet at ha
  obtain ⟨⟨j, y⟩, hp, rfl⟩ := mem_image.mp ha
  obtain ⟨hj, hy⟩ := mem_product.mp hp
  have hj' := mem_Ico.mp hj
  have hsmall := S.Y_small y hy
  have hy1 := abs_le.mp (le_refl |y|)
  unfold setA
  rw [mem_filter]
  refine ⟨?_, ?_, ?_⟩
  · unfold prodSet
    exact mem_image.mpr ⟨(j, y), mem_product.mpr ⟨mem_range.mpr (by omega), hy⟩, rfl⟩
  · have h1 : (u : ℤ) ≤ (j : ℤ) * u := by
      have : (1 : ℤ) ≤ j := by exact_mod_cast hj'.1
      nlinarith
    have := abs_nonneg y
    simp only
    omega
  · have h1 : ((j : ℤ) + 1) * u ≤ ((D * v / u : ℕ) : ℤ) * u := by
      have : (j : ℤ) + 1 ≤ ((D * v / u : ℕ) : ℤ) := by exact_mod_cast hj'.2
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h2 : ((D * v / u : ℕ) : ℤ) * u ≤ (D : ℤ) * v := by
      have := Nat.div_mul_le_self (D * v) u
      exact_mod_cast this
    have e1 : ((j : ℤ) + 1) * u = (j : ℤ) * u + u := by ring
    have := abs_nonneg y
    simp only
    omega

lemma setA_sub : setA D u v Y ⊆ prodSet u (Ico 0 (D * v / u + 2)) Y := by
  unfold setA
  rw [← range_eq_Ico]
  exact filter_subset _ _

lemma sub_setB : prodSet v (Ico 1 D) Z ⊆ setB D v Z := by
  intro b hb
  unfold prodSet at hb
  obtain ⟨⟨k, z⟩, hp, rfl⟩ := mem_image.mp hb
  obtain ⟨hk, hz⟩ := mem_product.mp hp
  have hk' := mem_Ico.mp hk
  have hsmall := S.Z_small z hz
  have hz1 := abs_le.mp (le_refl |z|)
  unfold setB
  rw [mem_filter]
  refine ⟨?_, ?_, ?_⟩
  · unfold prodSet
    exact mem_image.mpr ⟨(k, z), mem_product.mpr ⟨mem_range.mpr (by omega), hz⟩, rfl⟩
  · have h1 : (v : ℤ) ≤ (k : ℤ) * v := by
      have : (1 : ℤ) ≤ k := by exact_mod_cast hk'.1
      nlinarith
    have := abs_nonneg z
    simp only
    omega
  · have h1 : ((k : ℤ) + 1) * v ≤ (D : ℤ) * v := by
      have : (k : ℤ) + 1 ≤ (D : ℤ) := by exact_mod_cast hk'.2
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have e1 : ((k : ℤ) + 1) * v = (k : ℤ) * v + v := by ring
    have := abs_nonneg z
    simp only
    omega

lemma setB_sub : setB D v Z ⊆ prodSet v (Ico 0 (D + 1)) Z := by
  unfold setB
  rw [← range_eq_Ico]
  exact filter_subset _ _

/-- `|B| = D |Z| + 1`. -/
lemma card_setB : (setB D v Z).card = D * Z.card + 1 := by
  have hD := S.hD
  have hv0 := S.v_pos
  have himg : setB D v Z = ((range (D + 1) ×ˢ Z).filter fun p : ℕ × ℤ =>
        0 ≤ (p.1 : ℤ) * v + p.2 ∧ (p.1 : ℤ) * v + p.2 ≤ (D : ℤ) * v).image
        fun p => (p.1 : ℤ) * v + p.2 := by
    unfold setB prodSet
    rw [filter_image]
  rw [himg, card_image_of_injOn ((digit_injOn v _ Z S.Z_small).mono
    (coe_subset.mpr (filter_subset _ _))), card_filter, sum_product]
  obtain ⟨d, hd⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  have hbound : ∀ z ∈ Z, -(v : ℤ) < z ∧ z < v := by
    intro z hz
    have h1 := S.Z_small z hz
    have h2 := abs_le.mp (le_refl |z|)
    have := abs_nonneg z
    omega
  have hfirst : (∑ z ∈ Z, if 0 ≤ ((0 : ℕ) : ℤ) * v + z ∧ ((0 : ℕ) : ℤ) * v + z ≤ (D : ℤ) * v
        then 1 else 0) = (Z.filter fun z => 0 ≤ z).card := by
    rw [card_filter]
    refine sum_congr rfl fun z hz => ?_
    have h1 := hbound z hz
    have h2 : (v : ℤ) ≤ (D : ℤ) * v := by
      have : (1 : ℤ) ≤ D := by omega
      nlinarith
    refine if_congr ?_ rfl rfl
    simp only [Nat.cast_zero, zero_mul, zero_add]
    omega
  have hlast : (∑ z ∈ Z, if 0 ≤ ((D : ℕ) : ℤ) * v + z ∧ ((D : ℕ) : ℤ) * v + z ≤ (D : ℤ) * v
        then 1 else 0) = (Z.filter fun z => z ≤ 0).card := by
    rw [card_filter]
    refine sum_congr rfl fun z hz => ?_
    have h1 := hbound z hz
    have h2 : (v : ℤ) ≤ (D : ℤ) * v := by
      have : (1 : ℤ) ≤ D := by omega
      nlinarith
    refine if_congr ?_ rfl rfl
    omega
  have hmid : ∀ k ∈ range d, (∑ z ∈ Z,
        if 0 ≤ (((k + 1 : ℕ)) : ℤ) * v + z ∧ (((k + 1 : ℕ)) : ℤ) * v + z ≤ (D : ℤ) * v
        then 1 else 0) = Z.card := by
    intro k hk
    have hk' := mem_range.mp hk
    rw [card_eq_sum_ones]
    refine sum_congr rfl fun z hz => ?_
    have h1 := hbound z hz
    have h2 : (v : ℤ) ≤ (((k + 1 : ℕ)) : ℤ) * v := by
      have : (1 : ℤ) ≤ (((k + 1 : ℕ)) : ℤ) := by omega
      nlinarith
    have h3 : ((((k + 1 : ℕ)) : ℤ) + 1) * v ≤ (D : ℤ) * v := by
      have : (((k + 1 : ℕ)) : ℤ) + 1 ≤ D := by omega
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have e1 : ((((k + 1 : ℕ)) : ℤ) + 1) * v = (((k + 1 : ℕ)) : ℤ) * v + v := by ring
    rw [if_pos]
    omega
  have hsplit : ∀ f : ℕ → ℕ, ∑ k ∈ range (D + 1), f k
      = (∑ k ∈ range d, f (k + 1)) + f 0 + f D := by
    intro f
    rw [sum_range_succ, hd, sum_range_succ']
  rw [hsplit, sum_congr rfl hmid, hfirst, hlast, sum_const, card_range, smul_eq_mul]
  have hunion : (Z.filter fun z => 0 ≤ z).card + (Z.filter fun z => z ≤ 0).card = Z.card + 1 := by
    have h1 := card_union_add_card_inter (Z.filter fun z => 0 ≤ z) (Z.filter fun z => z ≤ 0)
    have h2 : (Z.filter fun z => 0 ≤ z) ∪ (Z.filter fun z => z ≤ 0) = Z := by
      ext z
      simp only [mem_union, mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        rcases le_total 0 z with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, h'⟩
    have h3 : (Z.filter fun z => 0 ≤ z) ∩ (Z.filter fun z => z ≤ 0) = {0} := by
      ext z
      simp only [mem_inter, mem_filter, mem_singleton]
      constructor
      · rintro ⟨⟨_, h4⟩, ⟨_, h5⟩⟩; omega
      · rintro rfl; exact ⟨⟨S.hZ0, le_refl _⟩, ⟨S.hZ0, le_refl _⟩⟩
    rw [h2, h3, card_singleton] at h1
    exact h1.symm
  have hDZ : D * Z.card = d * Z.card + Z.card := by rw [hd]; ring
  omega

lemma card_setA_lower : (((D * v / u : ℕ) : ℝ) - 1) * Y.card ≤ ((setA D u v Y).card : ℝ) := by
  have h1 := card_le_card S.sub_setA
  rw [card_prodSet u _ Y S.Y_small, Nat.card_Ico] at h1
  have hJ : 1 ≤ D * v / u := by
    have := S.J_ge
    have h2 : 1 ≤ 20 * D * D := by
      have := S.hD
      exact Nat.mul_pos (by omega) (by omega)
    omega
  have h3 : (((D * v / u - 1) * Y.card : ℕ) : ℝ) ≤ ((setA D u v Y).card : ℝ) := by exact_mod_cast h1
  rwa [Nat.cast_mul, Nat.cast_sub hJ, Nat.cast_one] at h3

lemma card_setA_upper : ((setA D u v Y).card : ℝ) ≤ (((D * v / u : ℕ) : ℝ) + 2) * Y.card := by
  have h1 := card_le_card S.setA_sub
  rw [card_prodSet u _ Y S.Y_small, Nat.card_Ico, Nat.sub_zero] at h1
  have h3 : ((setA D u v Y).card : ℝ) ≤ (((D * v / u + 2) * Y.card : ℕ) : ℝ) := by exact_mod_cast h1
  rwa [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at h3

/-- The two weight bounds, for a difference `Δ = m v + (z - z') - (y - y')` divisible by `u`. -/
lemma weight_bounds (m : ℤ) {y y' z z' : ℤ} (hy : y ∈ Y) (hy' : y' ∈ Y) (hz : z ∈ Z) (hz' : z' ∈ Z)
    (h : (u : ℤ) ∣ m * v + (z - z') - (y - y')) :
    let q := (m * v + (z - z') - (y - y')) / (u : ℤ)
    (v : ℝ) / u * ((D : ℝ) - 3 / D - |(m : ℝ)|) ≤ ((D * v / u : ℕ) : ℝ) - 1 - (q.natAbs : ℝ) ∧
    (((D * v / u : ℕ) : ℝ) + 2 - (q.natAbs : ℝ)) ≤ (v : ℝ) / u * ((D : ℝ) + 3 / D - |(m : ℝ)|) := by
  intro q
  have hur : (0 : ℝ) < u := by exact_mod_cast S.u_pos
  have hvr : (0 : ℝ) < v := by exact_mod_cast S.v_pos
  have hDr : (100 : ℝ) ≤ D := by exact_mod_cast S.hD
  have hD0 : (0 : ℝ) < D := by linarith
  have huv : 20 * (D : ℝ) * u ≤ v := by exact_mod_cast S.hv
  have hq : (q : ℝ) * u = (m : ℝ) * v + ((z : ℝ) - z') - ((y : ℝ) - y') := by
    have h1 : q * (u : ℤ) = m * v + (z - z') - (y - y') := Int.ediv_mul_cancel h
    exact_mod_cast h1
  have hnat : (q.natAbs : ℝ) = |(q : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hyb : ∀ y ∈ Y, |(y : ℝ)| ≤ u / D := by
    intro y hy
    rw [le_div_iff₀ hD0, mul_comm]
    have h1 := (S.hY y hy).le
    exact_mod_cast h1
  have hzb : ∀ z ∈ Z, |(z : ℝ)| ≤ v / D := by
    intro z hz
    rw [le_div_iff₀ hD0, mul_comm]
    have h1 := (S.hZ z hz).le
    exact_mod_cast h1
  have herr : |((z : ℝ) - z') - ((y : ℝ) - y')| ≤ 2 * (v / D) + 2 * (u / D) := by
    have h1 := abs_sub ((z : ℝ) - z') ((y : ℝ) - y')
    have h2 := abs_sub (z : ℝ) z'
    have h3 := abs_sub (y : ℝ) y'
    have h4 := hzb z hz
    have h5 := hzb z' hz'
    have h6 := hyb y hy
    have h7 := hyb y' hy'
    linarith
  have habs : |(|(q : ℝ)| * u - |(m : ℝ)| * v)| ≤ 2 * (v / D) + 2 * (u / D) := by
    have h1 : |(q : ℝ)| * u = |(q : ℝ) * u| := by rw [abs_mul, abs_of_pos hur]
    have h2 : |(m : ℝ)| * v = |(m : ℝ) * v| := by rw [abs_mul, abs_of_pos hvr]
    rw [h1, h2]
    refine le_trans (abs_abs_sub_abs_le_abs_sub _ _) ?_
    rw [hq, show (m : ℝ) * v + ((z : ℝ) - z') - ((y : ℝ) - y') - (m : ℝ) * v
      = ((z : ℝ) - z') - ((y : ℝ) - y') by ring]
    exact herr
  have hab := abs_le.mp habs
  have hJ1 : ((D * v / u : ℕ) : ℝ) * u ≤ (D : ℝ) * v := by
    have := Nat.div_mul_le_self (D * v) u
    exact_mod_cast this
  have hJ2 : (D : ℝ) * v ≤ (((D * v / u : ℕ) : ℝ) + 1) * u := by
    have h1 := Nat.lt_div_mul_add (a := D * v) S.u_pos
    have h2 : D * v ≤ (D * v / u + 1) * u := by
      have e1 : (D * v / u + 1) * u = D * v / u * u + u := by ring
      omega
    exact_mod_cast h2
  have hsmall : 2 * (u : ℝ) + 2 * (v / D) + 2 * (u / D) ≤ v * (3 / D) := by
    have key : 2 * (u : ℝ) * D + 2 * v + 2 * u ≤ 3 * v := by
      have h1 : (u : ℝ) * 100 ≤ u * D := mul_le_mul_of_nonneg_left hDr hur.le
      nlinarith
    have e1 : 2 * (u : ℝ) + 2 * (v / D) + 2 * (u / D) = (2 * (u : ℝ) * D + 2 * v + 2 * u) / D := by
      field_simp
    have e2 : (v : ℝ) * (3 / D) = 3 * v / D := by ring
    rw [e1, e2]
    exact (div_le_div_iff_of_pos_right hD0).mpr key
  set J : ℝ := ((D * v / u : ℕ) : ℝ) with hJdef
  rw [hnat]
  have hexp : ∀ t : ℝ, (v : ℝ) / u * t * u = v * t := by
    intro t
    field_simp
  constructor
  · refine le_of_mul_le_mul_right ?_ hur
    rw [hexp]
    have e1 : (J - 1 - |(q : ℝ)|) * u = (J + 1) * u - 2 * u - |(q : ℝ)| * u := by ring
    have e2 : (v : ℝ) * ((D : ℝ) - 3 / D - |(m : ℝ)|)
        = (D : ℝ) * v - v * (3 / D) - |(m : ℝ)| * v := by ring
    rw [e1, e2]
    linarith [hab.2]
  · refine le_of_mul_le_mul_right ?_ hur
    rw [hexp]
    have e1 : (J + 2 - |(q : ℝ)|) * u = J * u + 2 * u - |(q : ℝ)| * u := by ring
    have e2 : (v : ℝ) * ((D : ℝ) + 3 / D - |(m : ℝ)|)
        = (D : ℝ) * v + v * (3 / D) - |(m : ℝ)| * v := by ring
    rw [e1, e2]
    have h8 : 0 ≤ (u : ℝ) / D := by positivity
    have h9 : 0 ≤ (v : ℝ) / D := by positivity
    linarith [hab.1]

/-- The upper bound for the energy in Fourier form, before the kernel is simplified. -/
lemma energy_le_weights : energy (setA D u v Y) (setB D v Z)
    ≤ (v : ℝ) / u * ((1 / (u : ℝ)) * ∑ ξ ∈ range u, power u Y ξ * power u Z ξ *
        (∑ k ∈ range (D + 1), ∑ k' ∈ range (D + 1),
          ((D : ℝ) + 3 / D - |((((k : ℤ) - k' : ℤ)) : ℝ)|) * c ((ξ : ℝ) * v / u) ((k : ℤ) - k'))) := by
  have hu := S.u_pos
  have hmono := energy_mono S.setA_sub S.setB_sub
  have hIco : Ico 0 (D * v / u + 2) = Ico 0 (0 + (D * v / u + 2)) := by rw [Nat.zero_add]
  rw [hIco, energy_prod u v _ 0 hu _ Y Z S.Y_small S.Z_small, ← range_eq_Ico] at hmono
  refine le_trans hmono ?_
  set W : ℤ → ℝ := fun m => (v : ℝ) / u * ((D : ℝ) + 3 / D - |(m : ℝ)|) with hW
  have hstep : ∀ k ∈ range (D + 1), ∀ k' ∈ range (D + 1),
      (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
          count u (D * v / u + 2) (((k : ℤ) - k') * v + (z - z') - (y - y')))
        ≤ W ((k : ℤ) - k') * (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
            ind u (((k : ℤ) - k') * v + (z - z') - (y - y'))) := by
    intro k hk k' hk'
    have hk1 := mem_range.mp hk
    have hk2 := mem_range.mp hk'
    have hm : |((((k : ℤ) - k' : ℤ)) : ℝ)| ≤ (D : ℝ) := by
      have h1 : |(k : ℤ) - k'| ≤ (D : ℤ) := by rw [abs_le]; omega
      exact_mod_cast h1
    have hW0 : 0 ≤ W ((k : ℤ) - k') := by
      have : (0 : ℝ) ≤ 3 / D := by positivity
      exact mul_nonneg (by positivity) (by linarith)
    simp only [mul_sum]
    refine sum_le_sum fun z hz => sum_le_sum fun z' hz' => sum_le_sum fun y hy =>
      sum_le_sum fun y' hy' => ?_
    unfold count
    by_cases h : (u : ℤ) ∣ ((k : ℤ) - k') * v + (z - z') - (y - y')
    · have hi : ind u (((k : ℤ) - k') * v + (z - z') - (y - y')) = 1 := if_pos h
      rw [hi, one_mul, mul_one]
      have hb := (S.weight_bounds ((k : ℤ) - k') hy hy' hz hz' h).2
      set q := (((k : ℤ) - k') * v + (z - z') - (y - y')) / (u : ℤ)
      by_cases hle : q.natAbs ≤ D * v / u + 2
      · rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_ofNat]
        exact hb
      · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]
        exact hW0
    · have hi : ind u (((k : ℤ) - k') * v + (z - z') - (y - y')) = 0 := if_neg h
      rw [hi, zero_mul, mul_zero]
  refine le_trans (sum_le_sum fun k hk => sum_le_sum fun k' hk' => hstep k hk k' hk') ?_
  rw [fourier u v hu (range (D + 1)) W Y Z]
  refine le_of_eq ?_
  rw [mul_left_comm]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [mul_left_comm]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun k' _ => ?_
  rw [hW]
  ring

/-- The lower bound for the energy in Fourier form. -/
lemma weights_le_energy :
    (v : ℝ) / u * ((1 / (u : ℝ)) * ∑ ξ ∈ range u, power u Y ξ * power u Z ξ *
        H (D - 1) ((ξ : ℝ) * v / u))
      ≤ energy (setA D u v Y) (setB D v Z) := by
  have hu := S.u_pos
  have hD := S.hD
  have hDr : (100 : ℝ) ≤ D := by exact_mod_cast S.hD
  have hJ : 1 ≤ D * v / u := by
    have := S.J_ge
    have h2 : 1 ≤ 20 * D * D := Nat.mul_pos (by omega) (by omega)
    omega
  have hmono := energy_mono S.sub_setA S.sub_setB
  have hIco : Ico 1 (D * v / u) = Ico 1 (1 + (D * v / u - 1)) := by
    congr 1
    omega
  rw [hIco, energy_prod u v _ 1 hu _ Y Z S.Y_small S.Z_small] at hmono
  refine le_trans ?_ hmono
  set W : ℤ → ℝ := fun m => (v : ℝ) / u * ((D : ℝ) - 3 / D - |(m : ℝ)|) with hW
  have hstep : ∀ k ∈ Ico 1 D, ∀ k' ∈ Ico 1 D,
      W ((k : ℤ) - k') * (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
            ind u (((k : ℤ) - k') * v + (z - z') - (y - y')))
        ≤ ∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
          count u (D * v / u - 1) (((k : ℤ) - k') * v + (z - z') - (y - y')) := by
    intro k _ k' _
    simp only [mul_sum]
    refine sum_le_sum fun z hz => sum_le_sum fun z' hz' => sum_le_sum fun y hy =>
      sum_le_sum fun y' hy' => ?_
    unfold count
    by_cases h : (u : ℤ) ∣ ((k : ℤ) - k') * v + (z - z') - (y - y')
    · have hi : ind u (((k : ℤ) - k') * v + (z - z') - (y - y')) = 1 := if_pos h
      rw [hi, one_mul, mul_one]
      have hb := (S.weight_bounds ((k : ℤ) - k') hy hy' hz hz' h).1
      set q := (((k : ℤ) - k') * v + (z - z') - (y - y')) / (u : ℤ)
      refine le_trans hb ?_
      have h1 : D * v / u - 1 ≤ (D * v / u - 1 - q.natAbs) + q.natAbs := by omega
      have h2 : ((D * v / u - 1 : ℕ) : ℝ) ≤ ((D * v / u - 1 - q.natAbs : ℕ) : ℝ) + (q.natAbs : ℝ) := by
        exact_mod_cast h1
      rw [Nat.cast_sub hJ, Nat.cast_one] at h2
      linarith
    · have hi : ind u (((k : ℤ) - k') * v + (z - z') - (y - y')) = 0 := if_neg h
      rw [hi, zero_mul, mul_zero]
  refine le_trans ?_ (sum_le_sum fun k hk => sum_le_sum fun k' hk' => hstep k hk k' hk')
  rw [fourier u v hu (Ico 1 D) W Y Z]
  have hkernel : ∀ θ : ℝ, (v : ℝ) / u * H (D - 1) θ
      ≤ ∑ k ∈ Ico 1 D, ∑ k' ∈ Ico 1 D, W ((k : ℤ) - k') * c θ ((k : ℤ) - k') := by
    intro θ
    have hshift : ∑ k ∈ Ico 1 D, ∑ k' ∈ Ico 1 D, W ((k : ℤ) - k') * c θ ((k : ℤ) - k')
        = ∑ k ∈ range (D - 1), ∑ k' ∈ range (D - 1), W ((k : ℤ) - k') * c θ ((k : ℤ) - k') := by
      rw [sum_Ico_eq_sum_range]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_Ico_eq_sum_range]
      refine sum_congr rfl fun k' _ => ?_
      have e1 : (((1 + k : ℕ) : ℤ) - ((1 + k' : ℕ) : ℤ)) = (k : ℤ) - k' := by push_cast; ring
      rw [e1]
    have hdec : ∑ k ∈ range (D - 1), ∑ k' ∈ range (D - 1), W ((k : ℤ) - k') * c θ ((k : ℤ) - k')
        = (v : ℝ) / u * (H (D - 1) θ + (1 - 3 / (D : ℝ)) * F (D - 1) θ) := by
      unfold H F
      simp only [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun k _ => sum_congr rfl fun k' _ => ?_
      rw [hW, Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_one]
      ring
    rw [hshift, hdec]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : (0 : ℝ) ≤ 1 - 3 / (D : ℝ) := by
      rw [sub_nonneg, div_le_one (by positivity)]
      linarith
    have := mul_nonneg h1 (F_nonneg (D - 1) θ)
    linarith
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [mul_sum]
  refine sum_le_sum fun ξ _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hkernel _)
    (mul_nonneg (power_nonneg _ _ _) (power_nonneg _ _ _))

lemma Y_card_pos : (0 : ℝ) < Y.card := by exact_mod_cast S.hYne.card_pos

lemma Z_card_ge : (5 : ℝ) ≤ Z.card := by exact_mod_cast S.hZ5

lemma power_eq_G (ξ : ℕ) : power u Y ξ * power u Z ξ
    = (Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * G u Y Z ξ := by
  have h1 := S.Y_card_pos
  have h2 := S.Z_card_ge
  have h3 : (Z.card : ℝ) ≠ 0 := by linarith
  have h4 : (Y.card : ℝ) ≠ 0 := h1.ne'
  unfold G
  field_simp

lemma G_nonneg (ξ : ℕ) : 0 ≤ G u Y Z ξ := by
  unfold G
  exact div_nonneg (mul_nonneg (power_nonneg _ _ _) (power_nonneg _ _ _)) (by positivity)

lemma G_zero : G u Y Z 0 = 1 := by
  have h1 := S.Y_card_pos
  have h2 := S.Z_card_ge
  have h3 : (Z.card : ℝ) ≠ 0 := by linarith
  have h4 : (Y.card : ℝ) ≠ 0 := h1.ne'
  unfold G
  rw [power_zero, power_zero]
  field_simp

lemma one_le_kappaD : 1 ≤ kappaD D u v Y Z := by
  have hH := H_at_zero_pos D (by have := S.hD; omega)
  have h0 : G u Y Z 0 * (H D (((0 : ℕ) : ℝ) * v / u) / H D 0) = 1 := by
    rw [S.G_zero, show ((0 : ℕ) : ℝ) * v / u = 0 by simp, div_self hH.ne', mul_one]
  unfold kappaD
  rw [← h0]
  exact single_le_sum (f := fun ξ => G u Y Z ξ * (H D ((ξ : ℝ) * v / u) / H D 0))
    (fun ξ _ => mul_nonneg (S.G_nonneg ξ) (div_nonneg (H_nonneg _ _) hH.le))
    (mem_range.mpr S.u_pos)

lemma kappaD_le_kappa : kappaD D u v Y Z ≤ kappa u Y Z := by
  have hH := H_at_zero_pos D (by have := S.hD; omega)
  refine sum_le_sum fun ξ _ => ?_
  refine mul_le_of_le_one_right (S.G_nonneg ξ) ?_
  rw [div_le_one hH]
  exact H_le_at_zero _ _

lemma sum_H_eq : ∑ ξ ∈ range u, G u Y Z ξ * H D ((ξ : ℝ) * v / u) = H D 0 * kappaD D u v Y Z := by
  have hH := H_at_zero_pos D (by have := S.hD; omega)
  have hH' := hH.ne'
  unfold kappaD
  rw [mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  field_simp

/-- The common algebra of the two bounds for `C`. -/
lemma C_form (M T b : ℝ) (hM : M ≠ 0) (hb : b ≠ 0) :
    (2 * ((D : ℝ) * v) + 1) * ((v : ℝ) / u * ((1 / (u : ℝ)) *
        ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T))) / ((M * Y.card) * (b * Z.card)) ^ 2
      = (2 * ((D : ℝ) * v) + 1) * v * T / ((u : ℝ) ^ 2 * M ^ 2 * b ^ 2) := by
  have h1 := S.Y_card_pos.ne'
  have h2 : (Z.card : ℝ) ≠ 0 := by have := S.Z_card_ge; linarith
  have h3 : (u : ℝ) ≠ 0 := by have := S.u_pos; positivity
  field_simp

lemma sum_power (g : ℕ → ℝ) : ∑ ξ ∈ range u, power u Y ξ * power u Z ξ * g ξ
    = (Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * ∑ ξ ∈ range u, G u Y Z ξ * g ξ := by
  rw [mul_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [S.power_eq_G]
  ring

/-- The upper bound for `C` with a bound `T` for the weighted sum. -/
lemma C_upper (T : ℝ) (hT : 0 ≤ T)
    (hE : energy (setA D u v Y) (setB D v Z) ≤ (v : ℝ) / u * ((1 / (u : ℝ)) *
        ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T))) :
    C D u v Y Z ≤ (2 + 1 / ((D : ℝ) * v)) * T / ((D : ℝ) ^ 3 * (1 - 2 * u / ((D : ℝ) * v)) ^ 2) := by
  have hur : (0 : ℝ) < u := by exact_mod_cast S.u_pos
  have hvr : (0 : ℝ) < v := by exact_mod_cast S.v_pos
  have hDr : (100 : ℝ) ≤ D := by exact_mod_cast S.hD
  have hD0 : (0 : ℝ) < D := by linarith
  have huv : 20 * (D : ℝ) * u ≤ v := by exact_mod_cast S.hv
  have hY := S.Y_card_pos
  have hZ := S.Z_card_ge
  set r : ℝ := (D : ℝ) * v / u with hr
  have hr20 : 20 * (D : ℝ) ^ 2 ≤ r := by
    rw [hr, le_div_iff₀ hur]
    nlinarith
  have hr2 : 2 < r := by nlinarith
  have hJ : r - 1 ≤ ((D * v / u : ℕ) : ℝ) := by
    have h1 := Nat.lt_div_mul_add (a := D * v) S.u_pos
    have h2 : D * v ≤ (D * v / u + 1) * u := by
      have e1 : (D * v / u + 1) * u = D * v / u * u + u := by ring
      omega
    have h3 : (D : ℝ) * v ≤ (((D * v / u : ℕ) : ℝ) + 1) * u := by exact_mod_cast h2
    rw [hr, sub_le_iff_le_add, div_le_iff₀ hur]
    exact h3
  have hA : (r - 2) * Y.card ≤ ((setA D u v Y).card : ℝ) := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hY.le) S.card_setA_lower
    linarith
  have hB : (D : ℝ) * Z.card ≤ ((setB D v Z).card : ℝ) := by
    rw [S.card_setB]
    push_cast
    linarith
  have hlow : 0 < ((r - 2) * Y.card) * ((D : ℝ) * Z.card) := by
    have : (0 : ℝ) < Z.card := by linarith
    have : 0 < r - 2 := by linarith
    positivity
  have hprod : ((r - 2) * Y.card) * ((D : ℝ) * Z.card)
      ≤ ((setA D u v Y).card : ℝ) * ((setB D v Z).card : ℝ) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have h1 : C D u v Y Z ≤ (2 * ((D : ℝ) * v) + 1) * ((v : ℝ) / u * ((1 / (u : ℝ)) *
        ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T)))
      / (((r - 2) * Y.card) * ((D : ℝ) * Z.card)) ^ 2 := by
    unfold C
    refine div_le_div₀ ?_ (mul_le_mul_of_nonneg_left hE (by positivity)) (by positivity)
      (pow_le_pow_left₀ hlow.le hprod 2)
    have : 0 ≤ (v : ℝ) / u * ((1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T)) := by
      positivity
    positivity
  refine le_trans h1 (le_of_eq ?_)
  rw [S.C_form (r - 2) T (D : ℝ) (by linarith) hD0.ne']
  have h2 : r - 2 ≠ 0 := by linarith
  have h3 : (D : ℝ) * v - 2 * u ≠ 0 := by
    have : 2 * (u : ℝ) < (D : ℝ) * v := by
      have h4 : r * u = (D : ℝ) * v := by rw [hr]; field_simp
      nlinarith
    linarith
  rw [hr]
  field_simp

/-- The lower bound for `C` with a lower bound `T` for the weighted sum. -/
lemma C_lower (T : ℝ) (hT : 0 ≤ T)
    (hE : (v : ℝ) / u * ((1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T))
      ≤ energy (setA D u v Y) (setB D v Z)) :
    2 * T / ((D : ℝ) ^ 3 * (1 + 2 * u / ((D : ℝ) * v)) ^ 2 * (1 + 1 / ((D : ℝ) * Z.card)) ^ 2)
      ≤ C D u v Y Z := by
  have hur : (0 : ℝ) < u := by exact_mod_cast S.u_pos
  have hvr : (0 : ℝ) < v := by exact_mod_cast S.v_pos
  have hDr : (100 : ℝ) ≤ D := by exact_mod_cast S.hD
  have hD0 : (0 : ℝ) < D := by linarith
  have huv : 20 * (D : ℝ) * u ≤ v := by exact_mod_cast S.hv
  have hY := S.Y_card_pos
  have hZ := S.Z_card_ge
  have hZ0 : (0 : ℝ) < Z.card := by linarith
  set r : ℝ := (D : ℝ) * v / u with hr
  have hr20 : 20 * (D : ℝ) ^ 2 ≤ r := by
    rw [hr, le_div_iff₀ hur]
    nlinarith
  have hr0 : 0 < r := by nlinarith
  have hJ : ((D * v / u : ℕ) : ℝ) ≤ r := by
    have h1 := Nat.div_mul_le_self (D * v) u
    have h2 : ((D * v / u : ℕ) : ℝ) * u ≤ (D : ℝ) * v := by exact_mod_cast h1
    rw [hr, le_div_iff₀ hur]
    exact h2
  have hA : ((setA D u v Y).card : ℝ) ≤ (r + 2) * Y.card := by
    refine le_trans S.card_setA_upper (mul_le_mul_of_nonneg_right ?_ hY.le)
    linarith
  have hB : ((setB D v Z).card : ℝ) = ((D : ℝ) + 1 / Z.card) * Z.card := by
    rw [S.card_setB]
    push_cast
    field_simp
  have hApos : (0 : ℝ) < (setA D u v Y).card := by
    have h1 := S.card_setA_lower
    have h2 : (1 : ℝ) < ((D * v / u : ℕ) : ℝ) := by
      have h3 : 2 ≤ D * v / u := by
        have h4 := S.J_ge
        have h5 : 2 ≤ 20 * D * D := by
          have h6 : 1 ≤ D * D := Nat.mul_pos (by have := S.hD; omega) (by have := S.hD; omega)
          have e1 : 20 * D * D = 20 * (D * D) := by ring
          omega
        omega
      have h7 : (2 : ℝ) ≤ ((D * v / u : ℕ) : ℝ) := by exact_mod_cast h3
      linarith
    exact lt_of_lt_of_le (mul_pos (by linarith) hY) h1
  have hBpos : (0 : ℝ) < (setB D v Z).card := by
    rw [hB]
    have : (0 : ℝ) < (D : ℝ) + 1 / Z.card := by positivity
    positivity
  have hprod : ((setA D u v Y).card : ℝ) * ((setB D v Z).card : ℝ)
      ≤ ((r + 2) * Y.card) * (((D : ℝ) + 1 / Z.card) * Z.card) := by
    rw [hB]
    exact mul_le_mul_of_nonneg_right hA (by positivity)
  have h1 : (2 * ((D : ℝ) * v) + 1) * ((v : ℝ) / u * ((1 / (u : ℝ)) *
        ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * T)))
      / (((r + 2) * Y.card) * (((D : ℝ) + 1 / Z.card) * Z.card)) ^ 2 ≤ C D u v Y Z := by
    unfold C
    refine div_le_div₀ ?_ (mul_le_mul_of_nonneg_left hE (by positivity))
      (pow_pos (mul_pos hApos hBpos) 2)
      (pow_le_pow_left₀ (mul_nonneg hApos.le hBpos.le) hprod 2)
    have : 0 ≤ energy (setA D u v Y) (setB D v Z) := by
      refine le_trans ?_ hE
      positivity
    positivity
  refine le_trans ?_ h1
  have hb : (D : ℝ) + 1 / Z.card ≠ 0 := by
    have : (0 : ℝ) < (D : ℝ) + 1 / Z.card := by positivity
    exact this.ne'
  rw [S.C_form (r + 2) T ((D : ℝ) + 1 / Z.card) (by linarith) hb]
  have e1 : 2 * T / ((D : ℝ) ^ 3 * (1 + 2 * u / ((D : ℝ) * v)) ^ 2 * (1 + 1 / ((D : ℝ) * Z.card)) ^ 2)
      = (2 * ((D : ℝ) * v)) * v * T / ((u : ℝ) ^ 2 * (r + 2) ^ 2 * ((D : ℝ) + 1 / Z.card) ^ 2) := by
    have h2 : (D : ℝ) * v + 2 * u ≠ 0 := by positivity
    have h3 : (D : ℝ) * Z.card + 1 ≠ 0 := by positivity
    rw [hr]
    field_simp
  rw [e1]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hvr.le) hT
  linarith

/-- Elementary numbers. -/
lemma small_terms :
    1 / ((D : ℝ) * v) ≤ 1 / (D : ℝ) ^ 2 ∧ 2 * u / ((D : ℝ) * v) ≤ 1 / (10 * (D : ℝ) ^ 2)
      ∧ 0 ≤ 2 * u / ((D : ℝ) * v) := by
  have hur : (0 : ℝ) < u := by exact_mod_cast S.u_pos
  have hvr : (0 : ℝ) < v := by exact_mod_cast S.v_pos
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast S.u_pos
  have hDr : (100 : ℝ) ≤ D := by exact_mod_cast S.hD
  have hD0 : (0 : ℝ) < D := by linarith
  have huv : 20 * (D : ℝ) * u ≤ v := by exact_mod_cast S.hv
  refine ⟨?_, ?_, by positivity⟩
  · refine one_div_le_one_div_of_le (by positivity) ?_
    have h1 : (D : ℝ) * 1 ≤ D * u := mul_le_mul_of_nonneg_left hu1 hD0.le
    have h2 : (D : ℝ) ≤ v := by nlinarith
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left huv hD0.le
    nlinarith

end Setting

lemma num_upper (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 100) :
    (1 + x / 200) * (1 + x / 200) * (1 + 409 / 100 * x) * (1 + x / 100) ≤ 1 + 5 * x := by
  have h1 : (1 + x / 200) * (1 + x / 200) ≤ 1 + x / 90 := by nlinarith
  have h2 : (1 + x / 90) * (1 + 409 / 100 * x) ≤ 1 + 43 / 10 * x := by nlinarith
  have h3 : (1 + 43 / 10 * x) * (1 + x / 100) ≤ 1 + 5 * x := by nlinarith
  have h4 : 0 ≤ 1 + 409 / 100 * x := by linarith
  have h5 : 0 ≤ 1 + x / 100 := by linarith
  exact le_trans (mul_le_mul_of_nonneg_right
    (le_trans (mul_le_mul_of_nonneg_right h1 h4) h2) h5) h3

variable {D u v : ℕ} {Y Z : Finset ℤ}

set_option maxHeartbeats 2000000 in
/-- **The two-sided formula.** -/
theorem energy_formula (S : Setting D u v Y Z) :
    (1 - 5 / (D : ℝ)) * (4 / 3) * kappaD D u v Y Z ≤ C D u v Y Z ∧
      C D u v Y Z ≤ (1 + 5 / (D : ℝ)) * (4 / 3) * kappaD D u v Y Z := by
  have hur : (0 : ℝ) < u := by exact_mod_cast S.u_pos
  have hvr : (0 : ℝ) < v := by exact_mod_cast S.v_pos
  have hDr : (100 : ℝ) ≤ D := by exact_mod_cast S.hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hD3 : 3 ≤ D := by have := S.hD; omega
  have hκ := S.one_le_kappaD
  have hκ0 : 0 ≤ kappaD D u v Y Z := by linarith
  have hH0 := H_at_zero_pos D (by omega)
  obtain ⟨hs1, hs2, hs3⟩ := S.small_terms
  set x : ℝ := 1 / D with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hDr
  have hx2 : 1 / (D : ℝ) ^ 2 = x ^ 2 := by rw [hx]; ring
  have hx3 : 1 / (10 * (D : ℝ) ^ 2) = x ^ 2 / 10 := by rw [hx]; ring
  have h5D : 5 / (D : ℝ) = 5 * x := by rw [hx]; ring
  have hxx : x ^ 2 ≤ x / 100 := by nlinarith
  have hK : H D 0 / (D : ℝ) ^ 3 = 2 / 3 * (1 + x ^ 2 / 2) := by
    rw [H_at_zero, hx]
    field_simp
  set T := H D 0 * kappaD D u v Y Z with hTdef
  have hT0 : 0 ≤ T := mul_nonneg hH0.le hκ0
  have hsum : ∑ ξ ∈ range u, G u Y Z ξ * H D ((ξ : ℝ) * v / u) = T := S.sum_H_eq
  have hTD : T / (D : ℝ) ^ 3 = 2 / 3 * (1 + x ^ 2 / 2) * kappaD D u v Y Z := by
    rw [hTdef, mul_div_right_comm, hK]
  constructor
  · -- lower bound
    have hd3 : (0 : ℝ) ≤ (D : ℝ) - 3 := by linarith
    set a : ℝ := ((D : ℝ) - 3) / ((D : ℝ) + 1) with ha
    have ha0 : 0 ≤ a := div_nonneg hd3 (by linarith)
    have hker : ∀ θ : ℝ, a * H D θ ≤ H (D - 1) θ := by
      intro θ
      have h1 := H_succ_le (D - 1) (by have := S.hD; omega) θ
      rw [Nat.sub_add_cancel (by omega : 1 ≤ D)] at h1
      have h2 : (((D - 1 : ℕ)) : ℝ) - 2 = (D : ℝ) - 3 := by
        rw [Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_one]; ring
      rw [h2] at h1
      have h3 : (0 : ℝ) < (D : ℝ) - 3 := by linarith
      have e1 : 1 + 4 / ((D : ℝ) - 3) = ((D : ℝ) + 1) / ((D : ℝ) - 3) := by
        field_simp
        ring
      rw [e1, div_mul_eq_mul_div, le_div_iff₀ h3] at h1
      rw [ha, div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < (D : ℝ) + 1)]
      linarith
    have hE : (v : ℝ) / u * ((1 / (u : ℝ)) * ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * (a * T)))
        ≤ energy (setA D u v Y) (setB D v Z) := by
      refine le_trans ?_ S.weights_le_energy
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
      rw [S.sum_power]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← hsum, mul_sum]
      refine sum_le_sum fun ξ _ => ?_
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hker _) (S.G_nonneg ξ)
    have h1 := S.C_lower (a * T) (mul_nonneg ha0 hT0) hE
    refine le_trans ?_ h1
    have hZ5 := S.Z_card_ge
    set p : ℝ := 1 + 2 * u / ((D : ℝ) * v) with hp
    set q : ℝ := 1 + 1 / ((D : ℝ) * Z.card) with hq
    have hp1 : p ≤ 1 + x / 1000 := by
      have : x ^ 2 / 10 ≤ x / 1000 := by nlinarith
      linarith
    have hp0 : 0 < p := by linarith
    have hq1 : q ≤ 1 + x / 5 := by
      have h2 : 1 / ((D : ℝ) * Z.card) ≤ x / 5 := by
        have e1 : x / 5 = 1 / ((D : ℝ) * 5) := by rw [hx]; ring
        rw [e1]
        exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hZ5 hD0.le)
      linarith
    have hq0 : 0 < q := by
      have : (0 : ℝ) ≤ 1 / ((D : ℝ) * Z.card) := by positivity
      linarith
    have haval : 1 - 4 * x ≤ a := by
      have e1 : 1 - 4 * x = ((D : ℝ) - 4) / D := by rw [hx]; field_simp
      rw [e1, ha, div_le_div_iff₀ hD0 (by linarith)]
      nlinarith
    have hmain : (1 - 5 * x) * (p ^ 2 * q ^ 2) ≤ a := by
      have h2 : p * q ≤ 1 + 21 / 100 * x := by
        refine le_trans (mul_le_mul hp1 hq1 hq0.le (by linarith)) ?_
        nlinarith
      have h3 : p ^ 2 * q ^ 2 ≤ 1 + 43 / 100 * x := by
        have e1 : p ^ 2 * q ^ 2 = (p * q) ^ 2 := by ring
        rw [e1]
        refine le_trans (pow_le_pow_left₀ (mul_nonneg hp0.le hq0.le) h2 2) ?_
        nlinarith
      have h4 : (0 : ℝ) ≤ 1 - 5 * x := by linarith
      refine le_trans (mul_le_mul_of_nonneg_left h3 h4) (le_trans ?_ haval)
      nlinarith
    have hden : (0 : ℝ) < (D : ℝ) ^ 3 * p ^ 2 * q ^ 2 := by positivity
    rw [le_div_iff₀ hden]
    have hTD' : T = 2 / 3 * (1 + x ^ 2 / 2) * kappaD D u v Y Z * (D : ℝ) ^ 3 := by
      rw [← hTD]
      field_simp
    have h6 : (1 - 5 * x) * (p ^ 2 * q ^ 2) * ((4 / 3) * kappaD D u v Y Z * (D : ℝ) ^ 3)
        ≤ a * ((4 / 3) * kappaD D u v Y Z * (D : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_right hmain (by positivity)
    have h7 : a * ((4 / 3) * kappaD D u v Y Z * (D : ℝ) ^ 3) ≤ 2 * (a * T) := by
      have h8 : 0 ≤ a * kappaD D u v Y Z * (D : ℝ) ^ 3 * x ^ 2 :=
        mul_nonneg (mul_nonneg (mul_nonneg ha0 hκ0) (by positivity)) (sq_nonneg _)
      have e1 : 2 * (a * T) = a * ((4 / 3) * kappaD D u v Y Z * (D : ℝ) ^ 3)
          + 2 / 3 * (a * kappaD D u v Y Z * (D : ℝ) ^ 3 * x ^ 2) := by
        rw [hTD']; ring
      linarith
    have e2 : (1 - 5 / (D : ℝ)) * (4 / 3) * kappaD D u v Y Z * ((D : ℝ) ^ 3 * p ^ 2 * q ^ 2)
        = (1 - 5 * x) * (p ^ 2 * q ^ 2) * ((4 / 3) * kappaD D u v Y Z * (D : ℝ) ^ 3) := by
      rw [h5D]; ring
    rw [e2]
    exact le_trans h6 h7
  · -- upper bound
    set b : ℝ := 1 + 4 / ((D : ℝ) - 2) with hb
    have hd2 : (0 : ℝ) < (D : ℝ) - 2 := by linarith
    have hb0 : 0 ≤ b := by
      have : (0 : ℝ) ≤ 4 / ((D : ℝ) - 2) := div_nonneg (by norm_num) hd2.le
      linarith
    have hE : energy (setA D u v Y) (setB D v Z) ≤ (v : ℝ) / u * ((1 / (u : ℝ)) *
        ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * (b * T))) := by
      refine le_trans S.energy_le_weights ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
      rw [S.sum_power]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← hsum, mul_sum]
      refine sum_le_sum fun ξ _ => ?_
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (S.G_nonneg ξ)
      set θ : ℝ := (ξ : ℝ) * v / u
      have hdec : ∑ k ∈ range (D + 1), ∑ k' ∈ range (D + 1),
            ((D : ℝ) + 3 / D - |((((k : ℤ) - k' : ℤ)) : ℝ)|) * c θ ((k : ℤ) - k')
          = H (D + 1) θ - (1 - 3 / (D : ℝ)) * F (D + 1) θ := by
        unfold H F
        rw [mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun k _ => ?_
        rw [mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun k' _ => ?_
        push_cast
        ring
      rw [hdec]
      have h1 : (0 : ℝ) ≤ 1 - 3 / (D : ℝ) := by
        rw [sub_nonneg, div_le_one hD0]
        linarith
      have h2 := mul_nonneg h1 (F_nonneg (D + 1) θ)
      have h3 := H_succ_le D hD3 θ
      linarith
    have h1 := S.C_upper (b * T) (mul_nonneg hb0 hT0) hE
    refine le_trans h1 ?_
    set p : ℝ := 1 - 2 * u / ((D : ℝ) * v) with hp
    have hp1 : 1 - x ^ 2 / 10 ≤ p := by linarith
    have hp0 : 0 < p := by
      have : x ^ 2 / 10 ≤ x / 1000 := by nlinarith
      linarith
    have hbval : b ≤ 1 + 409 / 100 * x := by
      have h2 : 4 / ((D : ℝ) - 2) ≤ 409 / 100 * x := by
        have e1 : 409 / 100 * x = (409 / 100) / D := by rw [hx]; ring
        rw [e1, div_le_div_iff₀ hd2 hD0]
        linarith
      linarith
    have hpinv : 1 ≤ (1 + x / 100) * p ^ 2 := by
      have h2 : (1 - x ^ 2 / 10) ^ 2 ≤ p ^ 2 := by
        refine pow_le_pow_left₀ ?_ hp1 2
        nlinarith
      have h3 : 1 ≤ (1 + x / 100) * (1 - x ^ 2 / 10) ^ 2 := by
        have h4 : 1 - x ^ 2 / 5 ≤ (1 - x ^ 2 / 10) ^ 2 := by nlinarith [sq_nonneg (x ^ 2)]
        have h5 : 1 ≤ (1 + x / 100) * (1 - x ^ 2 / 5) := by nlinarith
        exact le_trans h5 (mul_le_mul_of_nonneg_left h4 (by linarith))
      exact le_trans h3 (mul_le_mul_of_nonneg_left h2 (by linarith))
    have hA : 2 + 1 / ((D : ℝ) * v) ≤ 2 * (1 + x / 200) := by
      have : x ^ 2 ≤ x / 100 := hxx
      linarith
    have hden : (0 : ℝ) < (D : ℝ) ^ 3 * p ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have hTD' : T = 2 / 3 * (1 + x ^ 2 / 2) * kappaD D u v Y Z * (D : ℝ) ^ 3 := by
      rw [← hTD]
      field_simp
    have hN := num_upper x hx0 hx1
    have hK2 : 1 + x ^ 2 / 2 ≤ 1 + x / 200 := by linarith
    have h6 : (2 + 1 / ((D : ℝ) * v)) * (b * T)
        ≤ (2 * (1 + x / 200)) * ((1 + 409 / 100 * x)
            * (2 / 3 * (1 + x / 200) * kappaD D u v Y Z * (D : ℝ) ^ 3)) := by
      refine mul_le_mul hA (mul_le_mul hbval ?_ hT0 (by linarith)) (mul_nonneg hb0 hT0)
        (by linarith)
      rw [hTD']
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hκ0) (by positivity)
      linarith
    have h7 : (1 + x / 200) * (1 + x / 200) * (1 + 409 / 100 * x) ≤ (1 + 5 * x) * p ^ 2 := by
      have h8 : (1 + x / 200) * (1 + x / 200) * (1 + 409 / 100 * x) * 1
          ≤ (1 + x / 200) * (1 + x / 200) * (1 + 409 / 100 * x) * ((1 + x / 100) * p ^ 2) :=
        mul_le_mul_of_nonneg_left hpinv (by positivity)
      have h9 : (1 + x / 200) * (1 + x / 200) * (1 + 409 / 100 * x) * (1 + x / 100) * p ^ 2
          ≤ (1 + 5 * x) * p ^ 2 := mul_le_mul_of_nonneg_right hN (sq_nonneg _)
      linarith
    have h10 := mul_le_mul_of_nonneg_right h7
      (show 0 ≤ (4 / 3) * kappaD D u v Y Z * (D : ℝ) ^ 3 by positivity)
    have e2 : (1 + 5 / (D : ℝ)) * (4 / 3) * kappaD D u v Y Z * ((D : ℝ) ^ 3 * p ^ 2)
        = (1 + 5 * x) * p ^ 2 * ((4 / 3) * kappaD D u v Y Z * (D : ℝ) ^ 3) := by
      rw [h5D]; ring
    have e3 : (2 * (1 + x / 200)) * ((1 + 409 / 100 * x)
          * (2 / 3 * (1 + x / 200) * kappaD D u v Y Z * (D : ℝ) ^ 3))
        = (1 + x / 200) * (1 + x / 200) * (1 + 409 / 100 * x)
          * ((4 / 3) * kappaD D u v Y Z * (D : ℝ) ^ 3) := by ring
    rw [e2]
    rw [e3] at h6
    exact le_trans h6 h10

/-- **The criterion with one modulus**: `C ≤ 1.36 κ`. -/
theorem energy_le_kappa (S : Setting D u v Y Z) : C D u v Y Z ≤ 136 / 100 * kappa u Y Z := by
  have hur : (0 : ℝ) < u := by exact_mod_cast S.u_pos
  have hvr : (0 : ℝ) < v := by exact_mod_cast S.v_pos
  have hDr : (100 : ℝ) ≤ D := by exact_mod_cast S.hD
  have hD0 : (0 : ℝ) < D := by linarith
  obtain ⟨hs1, hs2, hs3⟩ := S.small_terms
  set x : ℝ := 1 / D with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num) hDr
  have hx2 : 1 / (D : ℝ) ^ 2 = x ^ 2 := by rw [hx]; ring
  have hx3 : 1 / (10 * (D : ℝ) ^ 2) = x ^ 2 / 10 := by rw [hx]; ring
  have hκ0 : 0 ≤ kappa u Y Z := sum_nonneg fun ξ _ => S.G_nonneg ξ
  set W : ℝ := ∑ k ∈ range (D + 1), ∑ k' ∈ range (D + 1),
      ((D : ℝ) + 3 / D - |((((k : ℤ) - k' : ℤ)) : ℝ)|) with hWdef
  have h3D : (0 : ℝ) ≤ 3 / D := by positivity
  have hw0 : ∀ k ∈ range (D + 1), ∀ k' ∈ range (D + 1),
      0 ≤ (D : ℝ) + 3 / D - |((((k : ℤ) - k' : ℤ)) : ℝ)| := by
    intro k hk k' hk'
    have hk1 := mem_range.mp hk
    have hk2 := mem_range.mp hk'
    have h1 : |(k : ℤ) - k'| ≤ (D : ℤ) := by rw [abs_le]; omega
    have h2 : |((((k : ℤ) - k' : ℤ)) : ℝ)| ≤ (D : ℝ) := by exact_mod_cast h1
    linarith
  have hW0 : 0 ≤ W := sum_nonneg fun k hk => sum_nonneg fun k' hk' => hw0 k hk k' hk'
  have hWval : W = (D : ℝ) * (D + 1) * (2 * D + 1) / 3 + 3 * ((D : ℝ) + 1) ^ 2 / D := by
    have h1 : W = H (D + 1) 0 - (1 - 3 / (D : ℝ)) * F (D + 1) 0 := by
      have hc : ∀ m : ℤ, c 0 m = 1 := fun m => by simp [c]
      rw [hWdef]
      unfold H F
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun k' _ => ?_
      rw [hc]
      push_cast
      ring
    rw [h1, H_at_zero, F_at_zero]
    push_cast
    field_simp
    ring
  have hE : energy (setA D u v Y) (setB D v Z) ≤ (v : ℝ) / u * ((1 / (u : ℝ)) *
      ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * (W * kappa u Y Z))) := by
    refine le_trans S.energy_le_weights ?_
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
    rw [S.sum_power]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    unfold kappa
    rw [mul_sum]
    refine sum_le_sum fun ξ _ => ?_
    rw [mul_comm W]
    refine mul_le_mul_of_nonneg_left ?_ (S.G_nonneg ξ)
    refine sum_le_sum fun k hk => sum_le_sum fun k' hk' => ?_
    exact mul_le_of_le_one_right (hw0 k hk k' hk') (c_le_one _ _)
  have h1 := S.C_upper (W * kappa u Y Z) (mul_nonneg hW0 hκ0) hE
  refine le_trans h1 ?_
  set p : ℝ := 1 - 2 * u / ((D : ℝ) * v) with hp
  have hp1 : 9999 / 10000 ≤ p := by
    have : x ^ 2 / 10 ≤ 1 / 10000 := by nlinarith
    linarith
  have hp0 : 0 < p := by linarith
  have hden : (0 : ℝ) < (D : ℝ) ^ 3 * p ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  have hWD : W ≤ 1016 / 1000 * (2 / 3) * (D : ℝ) ^ 3 := by
    rw [hWval]
    have h2 : 3 * ((D : ℝ) + 1) ^ 2 / D ≤ 4 * (D : ℝ) := by
      rw [div_le_iff₀ hD0]
      nlinarith
    have h3 : (D : ℝ) ^ 2 * 100 ≤ (D : ℝ) ^ 3 := by
      have e1 : (D : ℝ) ^ 3 = (D : ℝ) ^ 2 * D := by ring
      rw [e1]
      exact mul_le_mul_of_nonneg_left hDr (sq_nonneg _)
    have h4 : (D : ℝ) * 100 ≤ (D : ℝ) ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left hDr hD0.le
    nlinarith
  have hA : 2 + 1 / ((D : ℝ) * v) ≤ 20001 / 10000 := by
    have : x ^ 2 ≤ 1 / 10000 := by nlinarith
    linarith
  have h6 : (2 + 1 / ((D : ℝ) * v)) * (W * kappa u Y Z)
      ≤ 20001 / 10000 * ((1016 / 1000 * (2 / 3) * (D : ℝ) ^ 3) * kappa u Y Z) :=
    mul_le_mul hA (mul_le_mul_of_nonneg_right hWD hκ0) (mul_nonneg hW0 hκ0) (by norm_num)
  have h7 : (9999 / 10000 : ℝ) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (by norm_num) hp1 2
  have h8 : 20001 / 10000 * (1016 / 1000 * (2 / 3)) ≤ 136 / 100 * p ^ 2 := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left h7 (by norm_num))
    norm_num
  have h9 := mul_le_mul_of_nonneg_right h8
    (show 0 ≤ (D : ℝ) ^ 3 * kappa u Y Z by positivity)
  have e1 : 20001 / 10000 * ((1016 / 1000 * (2 / 3) * (D : ℝ) ^ 3) * kappa u Y Z)
      = 20001 / 10000 * (1016 / 1000 * (2 / 3)) * ((D : ℝ) ^ 3 * kappa u Y Z) := by ring
  have e2 : 136 / 100 * kappa u Y Z * ((D : ℝ) ^ 3 * p ^ 2)
      = 136 / 100 * p ^ 2 * ((D : ℝ) ^ 3 * kappa u Y Z) := by ring
  rw [e2]
  rw [e1] at h6
  exact le_trans h6 h9

/-- The energy at such a height is never much below `4/3`. -/
theorem energy_lower (S : Setting D u v Y Z) : (1 - 5 / (D : ℝ)) * (4 / 3) ≤ C D u v Y Z := by
  have hDr : (100 : ℝ) ≤ D := by exact_mod_cast S.hD
  have h1 : (0 : ℝ) ≤ 1 - 5 / (D : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  refine le_trans ?_ (energy_formula S).1
  exact le_mul_of_one_le_right (mul_nonneg h1 (by norm_num)) S.one_le_kappaD

lemma five_div_le (S : Setting D u v Y Z) : 5 / (D : ℝ) ≤ 1 / 20 := by
  have hDr : (100 : ℝ) ≤ D := by exact_mod_cast S.hD
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- If `κ_D ≤ 1.64` then `C ≤ 2.3`. -/
theorem energy_of_kappaD (S : Setting D u v Y Z) (h : kappaD D u v Y Z ≤ 164 / 100) :
    C D u v Y Z ≤ 23 / 10 := by
  have h1 := (energy_formula S).2
  have h2 := five_div_le S
  have h3 := S.one_le_kappaD
  have h4 : (0 : ℝ) ≤ 5 / (D : ℝ) := by positivity
  have h5 : (1 + 5 / (D : ℝ)) * (4 / 3) * kappaD D u v Y Z
      ≤ (1 + 1 / 20) * (4 / 3) * (164 / 100) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (by norm_num)) h (by linarith)
      (by norm_num)
  have h6 : (1 + 1 / 20 : ℝ) * (4 / 3) * (164 / 100) ≤ 23 / 10 := by norm_num
  linarith

/-- If `C ≤ 2.3` then `κ_D ≤ 1.82`. -/
theorem kappaD_of_energy (S : Setting D u v Y Z) (h : C D u v Y Z ≤ 23 / 10) :
    kappaD D u v Y Z ≤ 182 / 100 := by
  have h1 := (energy_formula S).1
  have h2 := five_div_le S
  have h3 := S.one_le_kappaD
  have h4 : (19 / 20 : ℝ) * (4 / 3) * kappaD D u v Y Z
      ≤ (1 - 5 / (D : ℝ)) * (4 / 3) * kappaD D u v Y Z :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by norm_num))
      (by linarith)
  linarith

/-- The frequencies with `‖ξ v / u‖ ≤ 1/(2D)` carry at most `(π²/4)(κ_D - 1)`. -/
theorem near_sum_le (S : Setting D u v Y Z) (s : Finset ℕ) (hs : s ⊆ range u) (h0 : 0 ∉ s)
    (hnear : ∀ ξ ∈ s, ∃ n : ℤ, |(ξ : ℝ) * v / u - n| ≤ 1 / (2 * (D : ℝ))) :
    ∑ ξ ∈ s, G u Y Z ξ ≤ π ^ 2 / 4 * (kappaD D u v Y Z - 1) := by
  have hD1 : 1 ≤ D := by have := S.hD; omega
  have hH := H_at_zero_pos D hD1
  have hpi := Real.pi_pos
  set f : ℕ → ℝ := fun ξ => G u Y Z ξ * (H D ((ξ : ℝ) * v / u) / H D 0) with hf
  have hf0 : f 0 = 1 := by
    simp only [hf]
    rw [S.G_zero, show ((0 : ℕ) : ℝ) * v / u = 0 by simp, div_self hH.ne', mul_one]
  have hfnn : ∀ ξ, 0 ≤ f ξ := fun ξ =>
    mul_nonneg (S.G_nonneg ξ) (div_nonneg (H_nonneg _ _) hH.le)
  have h1 : 4 / π ^ 2 * ∑ ξ ∈ s, G u Y Z ξ ≤ ∑ ξ ∈ s, f ξ := by
    rw [mul_sum]
    refine sum_le_sum fun ξ hξ => ?_
    obtain ⟨n, hn⟩ := hnear ξ hξ
    have h2 := H_ge_near D _ n hn hD1
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (S.G_nonneg ξ)
    rw [le_div_iff₀ hH]
    exact h2
  have h3 : (∑ ξ ∈ s, f ξ) + f 0 ≤ kappaD D u v Y Z := by
    have h4 : insert 0 s ⊆ range u := insert_subset (mem_range.mpr S.u_pos) hs
    have h5 := sum_le_sum_of_subset_of_nonneg (f := f) h4 fun ξ _ _ => hfnn ξ
    rw [sum_insert h0, add_comm] at h5
    exact h5
  rw [hf0] at h3
  have h6 : 4 / π ^ 2 * ∑ ξ ∈ s, G u Y Z ξ ≤ kappaD D u v Y Z - 1 := by linarith
  have h7 := mul_le_mul_of_nonneg_left h6 (show 0 ≤ π ^ 2 / 4 by positivity)
  have e1 : π ^ 2 / 4 * (4 / π ^ 2 * ∑ ξ ∈ s, G u Y Z ξ) = ∑ ξ ∈ s, G u Y Z ξ := by
    field_simp
  rwa [e1] at h7

/-- The hypotheses are satisfiable. -/
theorem setting_satisfiable : Setting 100 1 2000 {0} {-2, -1, 0, 1, 2} where
  hD := le_refl _
  hv := by norm_num
  hYne := singleton_nonempty _
  hY := by
    intro y hy
    rw [mem_singleton] at hy
    subst hy
    norm_num
  hZ := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> norm_num
  hZ0 := by decide
  hZ5 := by decide

end

end TwoPrimesFormula
