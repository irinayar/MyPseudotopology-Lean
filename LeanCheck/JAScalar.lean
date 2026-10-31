import Mathlib
import LeanCheck.JAProduct2
import LeanCheck.JAHeights

/-!
# The central bound, step 2b: the scalar `Sc`

In `JAProduct2.arc_mass_product` the arc mass carries the scalar `∏_{k<n} Z_{k+1}^2 / q_k^2`, `Z_{k+1} = ∑ w_{k+1}`.  Here we
bound it by the normalization `(∏ (α_k I_1 - 2))^2` of `CentralAt`, uniformly in `n`:

`scalar_bound`: for a chain with windows `w_{q_{k+1}}`, `q_{k+1} = q_k α_k`, `4 ≤ α_0 I_1` and `4 α_k ≤ α_{k+1}`,
`∏_{k<n} Z_{k+1}^2/q_k^2 ≤ exp(16/3) · (∏_{k<n} (α_k I_1 - 2))^2`.

Proof: `Z_{k+1}/q_k ≤ α_k I_1 + 2` (`sum_wQ`), `(u+2)^2 ≤ exp(16/u)(u-2)^2` for `u ≥ 4` (`level_bound`, from
`1 + x ≤ e^x`), and `∑_k 16/(α_k I_1) ≤ 16/3` by the geometric growth `α_k ≥ 4^k α_0`.
-/

namespace LeanCheck
namespace JAScalar

open Finset JAMulti JAWindowQ

lemma level_bound (u : ℝ) (hu : 4 ≤ u) (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ u + 2) :
    z ^ 2 ≤ Real.exp (16 / u) * (u - 2) ^ 2 := by
  have hu2 : 0 < u - 2 := by linarith
  have h1 : u + 2 ≤ Real.exp (4 / (u - 2)) * (u - 2) := by
    have h := Real.add_one_le_exp (4 / (u - 2))
    have e : (4 / (u - 2) + 1) * (u - 2) = u + 2 := by field_simp; ring
    calc u + 2 = (4 / (u - 2) + 1) * (u - 2) := e.symm
      _ ≤ Real.exp (4 / (u - 2)) * (u - 2) := mul_le_mul_of_nonneg_right h hu2.le
  have h2 : (u + 2) ^ 2 ≤ (Real.exp (4 / (u - 2)) * (u - 2)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  have h3 : (Real.exp (4 / (u - 2)) * (u - 2)) ^ 2 = Real.exp (8 / (u - 2)) * (u - 2) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have h4 : Real.exp (8 / (u - 2)) ≤ Real.exp (16 / u) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ hu2 (by linarith)]
    nlinarith
  calc z ^ 2 ≤ (u + 2) ^ 2 := pow_le_pow_left₀ hz0 hz 2
    _ ≤ (Real.exp (4 / (u - 2)) * (u - 2)) ^ 2 := h2
    _ = Real.exp (8 / (u - 2)) * (u - 2) ^ 2 := h3
    _ ≤ Real.exp (16 / u) * (u - 2) ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)

lemma geom_quarter (n : ℕ) : ∑ k ∈ range n, ((1 : ℝ) / 4) ^ k ≤ 4 / 3 := by
  have h : ∀ n : ℕ, ∑ k ∈ range n, ((1 : ℝ) / 4) ^ k = 4 / 3 - 4 / 3 * ((1 : ℝ) / 4) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [h n]
  have : 0 ≤ 4 / 3 * ((1 : ℝ) / 4) ^ n := by positivity
  linarith

theorem scalar_bound (c : Chain) (D : ℝ) (hD : 3 ≤ D) (hw : ∀ k, c.w (k + 1) = wQ D (c.q (k + 1)))
    (α : ℕ → ℕ) (hα : ∀ k, c.q (k + 1) = c.q k * α k)
    (hI0 : 4 ≤ (α 0 : ℝ) * (16 / (15 * D))) (hgrow : ∀ k, 4 * α k ≤ α (k + 1)) (n : ℕ) :
    ∏ k ∈ range n, ((∑ y, c.w (k + 1) y) ^ 2 / ((c.q k : ℕ) : ℝ) ^ 2) ≤
      Real.exp (16 / 3) * (∏ k ∈ range n, ((α k : ℝ) * (16 / (15 * D)) - 2)) ^ 2 := by
  have hD0 : 0 < D := by linarith
  set I : ℝ := 16 / (15 * D) with hIdef
  have hI : 0 < I := by positivity
  have hpow : ∀ k, 4 ^ k * α 0 ≤ α k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; nlinarith [hgrow k]
  have hpowR : ∀ k, (4 : ℝ) ^ k * (α 0 : ℝ) ≤ (α k : ℝ) := by
    intro k; exact_mod_cast hpow k
  have hu : ∀ k, 4 * 4 ^ k ≤ (α k : ℝ) * I := by
    intro k
    have h1 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have h2 : (4 : ℝ) ^ k * (α 0 * I) ≤ α k * I := by
      have := mul_le_mul_of_nonneg_right (hpowR k) hI.le
      linarith
    nlinarith
  -- one level
  have hlevel : ∀ k, (∑ y, c.w (k + 1) y) ^ 2 / ((c.q k : ℕ) : ℝ) ^ 2 ≤
      Real.exp (16 / ((α k : ℝ) * I)) * ((α k : ℝ) * I - 2) ^ 2 := by
    intro k
    have hq : (1 : ℝ) ≤ (c.q k : ℝ) := by exact_mod_cast c.pos k
    have hq0 : (0 : ℝ) < (c.q k : ℝ) := by linarith
    have hQ : ((c.q (k + 1) : ℕ) : ℝ) = (c.q k : ℝ) * (α k : ℝ) := by
      rw [hα k]; push_cast; ring
    have hQ0 : (0 : ℝ) < ((c.q (k + 1) : ℕ) : ℝ) := by exact_mod_cast c.pos (k + 1)
    have hZ : (∑ y, c.w (k + 1) y) = ∑ y, wQ D (c.q (k + 1)) y := by rw [hw k]
    have hsum := sum_wQ (Q := c.q (k + 1)) D hD
    rw [← hZ] at hsum
    have hZle : (∑ y, c.w (k + 1) y) ≤ ((c.q (k + 1) : ℕ) : ℝ) * I + 2 := by
      have := (abs_le.mp hsum).2
      have h2 : (∑ y, c.w (k + 1) y) / ((c.q (k + 1) : ℕ) : ℝ) ≤ I + 2 / ((c.q (k + 1) : ℕ) : ℝ) := by
        linarith
      rw [div_le_iff₀ hQ0] at h2
      have e : (I + 2 / ((c.q (k + 1) : ℕ) : ℝ)) * ((c.q (k + 1) : ℕ) : ℝ) =
          ((c.q (k + 1) : ℕ) : ℝ) * I + 2 := by field_simp
      linarith
    have hZ0 : 0 ≤ (∑ y, c.w (k + 1) y) := Finset.sum_nonneg (fun y _ => by rw [hw k]; exact wQ_nonneg D y)
    have hz : (∑ y, c.w (k + 1) y) / (c.q k : ℝ) ≤ (α k : ℝ) * I + 2 := by
      rw [div_le_iff₀ hq0]
      have : ((c.q (k + 1) : ℕ) : ℝ) * I + 2 ≤ ((α k : ℝ) * I + 2) * (c.q k : ℝ) := by
        rw [hQ]
        have h1 : 0 ≤ (α k : ℝ) * I := by positivity
        nlinarith
      linarith
    have hz0 : 0 ≤ (∑ y, c.w (k + 1) y) / (c.q k : ℝ) := div_nonneg hZ0 hq0.le
    have hlb := level_bound ((α k : ℝ) * I) (by linarith [hu k, (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) : (1 : ℝ) ≤ 4 ^ k)])
      _ hz0 hz
    rw [← div_pow]
    exact hlb
  -- the product
  have hprod : ∏ k ∈ range n, ((∑ y, c.w (k + 1) y) ^ 2 / ((c.q k : ℕ) : ℝ) ^ 2) ≤
      ∏ k ∈ range n, (Real.exp (16 / ((α k : ℝ) * I)) * ((α k : ℝ) * I - 2) ^ 2) :=
    Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => hlevel k)
  have hsplit : ∏ k ∈ range n, (Real.exp (16 / ((α k : ℝ) * I)) * ((α k : ℝ) * I - 2) ^ 2) =
      Real.exp (∑ k ∈ range n, 16 / ((α k : ℝ) * I)) * (∏ k ∈ range n, ((α k : ℝ) * I - 2)) ^ 2 := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_pow]
  -- the exponent
  have hexp : ∑ k ∈ range n, 16 / ((α k : ℝ) * I) ≤ 16 / 3 := by
    have hterm : ∀ k, 16 / ((α k : ℝ) * I) ≤ 4 * ((1 : ℝ) / 4) ^ k := by
      intro k
      have h4k : (0 : ℝ) < 4 ^ k := by positivity
      rw [div_le_iff₀ (by have := hu k; nlinarith)]
      have hk : ((1 : ℝ) / 4) ^ k * 4 ^ k = 1 := by
        rw [← mul_pow]; norm_num
      have := hu k
      nlinarith [hk]
    calc ∑ k ∈ range n, 16 / ((α k : ℝ) * I) ≤ ∑ k ∈ range n, 4 * ((1 : ℝ) / 4) ^ k :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = 4 * ∑ k ∈ range n, ((1 : ℝ) / 4) ^ k := by rw [Finset.mul_sum]
      _ ≤ 4 * (4 / 3) := mul_le_mul_of_nonneg_left (geom_quarter n) (by norm_num)
      _ = 16 / 3 := by norm_num
  calc ∏ k ∈ range n, ((∑ y, c.w (k + 1) y) ^ 2 / ((c.q k : ℕ) : ℝ) ^ 2)
      ≤ Real.exp (∑ k ∈ range n, 16 / ((α k : ℝ) * I)) * (∏ k ∈ range n, ((α k : ℝ) * I - 2)) ^ 2 :=
        hprod.trans (le_of_eq hsplit)
    _ ≤ Real.exp (16 / 3) * (∏ k ∈ range n, ((α k : ℝ) * I - 2)) ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (sq_nonneg _)

#print axioms level_bound
#print axioms scalar_bound

/-! ### Application to the chains `chainP` with start level `⌈D⌉` -/

lemma alpha0_large (p : ℕ) (hp : 2 ≤ p) (D : ℝ) (hD : 3 ≤ D) :
    4 ≤ ((p ^ (2 * (JAHeights.sD D + 0) + 1) : ℕ) : ℝ) * (16 / (15 * D)) := by
  have hD0 : 0 < D := by linarith
  set s := JAHeights.sD D with hs
  have hsD : D ≤ (s : ℝ) := Nat.le_ceil D
  have hs3 : 3 ≤ s := by
    have : (3 : ℝ) ≤ s := by linarith
    exact_mod_cast this
  obtain ⟨t, ht⟩ : ∃ t, 2 * (s + 0) + 1 = t + 2 := ⟨2 * s - 1, by omega⟩
  have ht' : (t : ℝ) = 2 * s - 1 := by
    have : t = 2 * s - 1 := by omega
    rw [this, Nat.cast_sub (by omega)]; push_cast; ring
  have h1 := JAHeights.real_lt_pow p hp t
  have hpow : ((p ^ (2 * (s + 0) + 1) : ℕ) : ℝ) = (p : ℝ) ^ t * (p : ℝ) ^ 2 := by
    rw [ht]; push_cast; ring
  have hp2 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  have h2 : 15 * D / 4 ≤ ((p ^ (2 * (s + 0) + 1) : ℕ) : ℝ) := by
    rw [hpow]
    have ht0 : (0 : ℝ) ≤ (p : ℝ) ^ t := by positivity
    nlinarith
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith

/-- **The scalar bound for the chains of the assembly.** -/
theorem chainP_scalar_bound (p : ℕ) [NeZero p] (hp : 2 ≤ p) (D : ℝ) (hD : 3 ≤ D) (n : ℕ) :
    ∏ k ∈ range n, ((∑ y, (JAFinal2.chainP p (JAHeights.sD D) D).w (k + 1) y) ^ 2 /
        (((JAFinal2.chainP p (JAHeights.sD D) D).q k : ℕ) : ℝ) ^ 2) ≤
      Real.exp (16 / 3) * (∏ k ∈ range n,
        (((p ^ (2 * (JAHeights.sD D + k) + 1) : ℕ) : ℝ) * (16 / (15 * D)) - 2)) ^ 2 := by
  refine scalar_bound (JAFinal2.chainP p (JAHeights.sD D) D) D hD (JAFinal2.chainP_w p _ D)
    (fun k => p ^ (2 * (JAHeights.sD D + k) + 1)) (JAFinal2.chainP_α p _ D) (alpha0_large p hp D hD) ?_ n
  intro k
  have hp2 : 4 ≤ p ^ 2 := by nlinarith
  calc 4 * p ^ (2 * (JAHeights.sD D + k) + 1) ≤ p ^ 2 * p ^ (2 * (JAHeights.sD D + k) + 1) :=
        Nat.mul_le_mul_right _ hp2
    _ = p ^ (2 * (JAHeights.sD D + (k + 1)) + 1) := by rw [← pow_add]; congr 1; ring

#print axioms alpha0_large
#print axioms chainP_scalar_bound

end JAScalar
end LeanCheck
