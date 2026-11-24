import LeanCheck.ThreePrimesTheoremBM3

/-!
# ThreePrimes (exploration M6): the strict criterion of Proposition 3.10(d) and the uniform lower bound of Remark 3.4

`crit_core` is the real-analytic core of part (d) of the criterion for tuned sets: with `a = η ≥ 1`,
`0 ≤ s < 1`, `0 ≤ c < 1`, `γ ≥ 0`, `q = a² + aγ/(a+1)`, `t = (√q + √(q + 4(a − s)))/2`, `K₀ = a² + a + γ` and
`N = (1 − c)(a + 2) + 2s(a + 1) + γ`, one has `t² − a − K₀ + c < (2 − N)/(a + 2)`. The proof squares
`√(q (q + 4(a − s))) < R` with `R = 2(U − c + s + K₀) − q`, using `R > 0` and the exact identity
`R² − q (q + 4 (a − s)) = 4 (a s + a + γ)² / (a + 2)²`.

`discQR_identity` is the completed-square identity `Q = η² (g² − G) + 4 η + 4 ∑ b_p (a_p − η/(2 b_p))²`
(`b_p = log₂ p`, `G = ∑ 1/b_p`), `sumG_le` is `G ≤ g²`, `tstarR_lower` the consequence
`t* ≥ η (g + √(g² − G))/2` for every exponent vector and every real `η ≥ 0`, and `exponent_lower` the bound
`Δ + M ≥ ((g + √(g² − G))/2)² η² − η` for the exponent `Δ + M` of Theorem 3.1.

Not formalised here: parts (a), (c), (e) of Proposition 3.10, the passage from `Ψ > 0` to the existence of a
violating set (parts (b), (c)), and the inflated-`η` example.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- Core of Proposition 3.10(d): the strict inequality `t² − a − K₀ + c < (2 − N)/(a + 2)`. -/
theorem crit_core {a s c γ q t : ℝ} (ha : 1 ≤ a) (hs0 : 0 ≤ s) (hs1 : s < 1) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hγ : 0 ≤ γ) (hq : q = a ^ 2 + a * γ / (a + 1))
    (ht : t = (Real.sqrt q + Real.sqrt (q + 4 * (a - s))) / 2) :
    t ^ 2 - a - (a ^ 2 + a + γ) + c
      < (2 - ((1 - c) * (a + 2) + 2 * s * (a + 1) + γ)) / (a + 2) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a + 1 := by linarith
  have ha2 : 0 < a + 2 := by linarith
  have ha1' : a + 1 ≠ 0 := ha1.ne'
  have ha2' : a + 2 ≠ 0 := ha2.ne'
  have has : 0 < a - s := by linarith
  have hq0 : 0 < q := by
    rw [hq]
    have h1 : 0 < a ^ 2 := by positivity
    have h2 : 0 ≤ a * γ / (a + 1) := div_nonneg (mul_nonneg ha0.le hγ) ha1.le
    linarith
  have hw0 : 0 < q + 4 * (a - s) := by linarith
  -- t² = q/2 + (a - s) + (1/2) √(q w), w = q + 4 (a - s)
  have hsq : Real.sqrt q * Real.sqrt (q + 4 * (a - s)) = Real.sqrt (q * (q + 4 * (a - s))) :=
    (Real.sqrt_mul hq0.le (q + 4 * (a - s))).symm
  have ht2 : t ^ 2 = q / 2 + (a - s) + Real.sqrt (q * (q + 4 * (a - s))) / 2 := by
    rw [ht]
    have h1 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
    have h2 : Real.sqrt (q + 4 * (a - s)) ^ 2 = q + 4 * (a - s) := Real.sq_sqrt hw0.le
    have h3 : ((Real.sqrt q + Real.sqrt (q + 4 * (a - s))) / 2) ^ 2
        = (Real.sqrt q ^ 2 + Real.sqrt (q + 4 * (a - s)) ^ 2
            + 2 * (Real.sqrt q * Real.sqrt (q + 4 * (a - s)))) / 4 := by ring
    rw [h3, h1, h2, hsq]
    ring
  -- R and the exact identity
  have hRpos : 0 < a * (a ^ 2 + 4 * a + 2 - 2 * s) / (a + 2)
      + γ * (a ^ 2 + 2 * a + 2) / ((a + 1) * (a + 2)) := by
    have h1 : 0 < a ^ 2 + 4 * a + 2 - 2 * s := by nlinarith
    have h2 : 0 ≤ γ * (a ^ 2 + 2 * a + 2) / ((a + 1) * (a + 2)) :=
      div_nonneg (mul_nonneg hγ (by positivity)) (mul_pos ha1 ha2).le
    have h3 : 0 < a * (a ^ 2 + 4 * a + 2 - 2 * s) / (a + 2) := div_pos (mul_pos ha0 h1) ha2
    linarith
  have hid : (a * (a ^ 2 + 4 * a + 2 - 2 * s) / (a + 2)
      + γ * (a ^ 2 + 2 * a + 2) / ((a + 1) * (a + 2))) ^ 2 - q * (q + 4 * (a - s))
      = 4 * (a * s + a + γ) ^ 2 / (a + 2) ^ 2 := by
    rw [hq]
    field_simp
    ring
  have hrhs : 0 < 4 * (a * s + a + γ) ^ 2 / (a + 2) ^ 2 := by
    have h0 : 0 < a * s + a + γ := by
      have := mul_nonneg ha0.le hs0
      linarith
    positivity
  have hlt : q * (q + 4 * (a - s)) < (a * (a ^ 2 + 4 * a + 2 - 2 * s) / (a + 2)
      + γ * (a ^ 2 + 2 * a + 2) / ((a + 1) * (a + 2))) ^ 2 := by linarith
  have hsqrt : Real.sqrt (q * (q + 4 * (a - s))) < a * (a ^ 2 + 4 * a + 2 - 2 * s) / (a + 2)
      + γ * (a ^ 2 + 2 * a + 2) / ((a + 1) * (a + 2)) := (Real.sqrt_lt' hRpos).2 hlt
  -- R = 2 (U - c + s + K₀) - q
  have hRform : a * (a ^ 2 + 4 * a + 2 - 2 * s) / (a + 2)
      + γ * (a ^ 2 + 2 * a + 2) / ((a + 1) * (a + 2))
      = 2 * ((2 - ((1 - c) * (a + 2) + 2 * s * (a + 1) + γ)) / (a + 2) - c + s + (a ^ 2 + a + γ)) - q := by
    rw [hq]
    field_simp
    ring
  rw [ht2]
  rw [hRform] at hsqrt
  have h5 : q / 2 + (a - s) + (2 * ((2 - ((1 - c) * (a + 2) + 2 * s * (a + 1) + γ)) / (a + 2) - c + s
      + (a ^ 2 + a + γ)) - q) / 2 - a - (a ^ 2 + a + γ) + c
      = (2 - ((1 - c) * (a + 2) + 2 * s * (a + 1) + γ)) / (a + 2) := by ring
  linarith

/-- Consequence: `Ψ_{K₀} > 0` forces `N < 2`, hence `(1 − c)(η + 2) < 2` and `2 s (η + 1) < 2`. -/
theorem crit_necessary {a s c γ q t : ℝ} (ha : 1 ≤ a) (hs0 : 0 ≤ s) (hs1 : s < 1) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hγ : 0 ≤ γ) (hq : q = a ^ 2 + a * γ / (a + 1))
    (ht : t = (Real.sqrt q + Real.sqrt (q + 4 * (a - s))) / 2)
    (hpos : 0 < t ^ 2 - a - (a ^ 2 + a + γ) + c) :
    (1 - c) * (a + 2) + 2 * s * (a + 1) + γ < 2 ∧ (1 - c) * (a + 2) < 2 ∧ 2 * s * (a + 1) < 2 := by
  have h := crit_core ha hs0 hs1 hc0 hc1 hγ hq ht
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a + 1 := by linarith
  have ha2 : 0 < a + 2 := by linarith
  have ha2' : a + 2 ≠ 0 := ha2.ne'
  have hU : 0 < (2 - ((1 - c) * (a + 2) + 2 * s * (a + 1) + γ)) / (a + 2) := lt_trans hpos h
  have key : (2 - ((1 - c) * (a + 2) + 2 * s * (a + 1) + γ)) / (a + 2) * (a + 2)
      = 2 - ((1 - c) * (a + 2) + 2 * s * (a + 1) + γ) := by field_simp
  have hN : 0 < 2 - ((1 - c) * (a + 2) + 2 * s * (a + 1) + γ) := by
    have h0 := mul_pos hU ha2
    rw [key] at h0
    exact h0
  have hA : 0 ≤ (1 - c) * (a + 2) := mul_nonneg (by linarith) ha2.le
  have hB : 0 ≤ 2 * s * (a + 1) := by
    have := mul_nonneg hs0 ha1.le
    linarith
  refine ⟨by linarith, by linarith, by linarith⟩

/-- `G = ∑ 1 / log₂ p`. -/
noncomputable def sumG (S : Finset ℕ) : ℝ := ∑ p ∈ S, 1 / Real.logb 2 (p : ℝ)

/-- For nonnegative terms, the sum of squares is at most the square of the sum. -/
lemma sum_sq_le_sq_sum (S : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ p ∈ S, 0 ≤ g p) :
    ∑ p ∈ S, g p ^ 2 ≤ (∑ p ∈ S, g p) ^ 2 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have hgx : 0 ≤ g x := hg x (Finset.mem_insert_self x s)
    have hgs : ∀ p ∈ s, 0 ≤ g p := fun p hp => hg p (Finset.mem_insert_of_mem hp)
    have hs0 : 0 ≤ ∑ p ∈ s, g p := Finset.sum_nonneg hgs
    have h1 := ih hgs
    have h2 := mul_nonneg hgx hs0
    nlinarith

/-- `G ≤ g²` (the square of a sum of nonnegative terms is at least the sum of the squares). -/
lemma sumG_le {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) : sumG S ≤ (sumA S) ^ 2 := by
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb' (hS p hp)
  have h := sum_sq_le_sq_sum S (fun p => Real.sqrt (1 / Real.logb 2 (p : ℝ))) (fun p _ => Real.sqrt_nonneg _)
  have h2 : ∑ p ∈ S, (Real.sqrt (1 / Real.logb 2 (p : ℝ))) ^ 2 = sumG S := by
    unfold sumG
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hl := hlb p hp
    have hpos : 0 < Real.logb 2 (p : ℝ) := by linarith
    exact Real.sq_sqrt (by positivity)
  rw [h2] at h
  exact h

/-- The completed-square identity `Q = η² (g² − G) + 4 η + 4 ∑ b_p (a_p − η/(2 b_p))²`. -/
theorem discQR_identity {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (η : ℝ) :
    discQR S a η = η ^ 2 * ((sumA S) ^ 2 - sumG S) + 4 * η
      + 4 * ∑ p ∈ S, Real.logb 2 (p : ℝ) * ((a p : ℝ) - η / (2 * Real.logb 2 (p : ℝ))) ^ 2 := by
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb' (hS p hp)
  have key : ∀ p ∈ S, Real.logb 2 (p : ℝ) * ((a p : ℝ) - η / (2 * Real.logb 2 (p : ℝ))) ^ 2
      = (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ) - η * (a p : ℝ) + η ^ 2 / 4 * (1 / Real.logb 2 (p : ℝ)) := by
    intro p hp
    have hl := hlb p hp
    have hpos : Real.logb 2 (p : ℝ) ≠ 0 := by
      have : 0 < Real.logb 2 (p : ℝ) := by linarith
      exact this.ne'
    field_simp
    ring
  have hsum : ∑ p ∈ S, Real.logb 2 (p : ℝ) * ((a p : ℝ) - η / (2 * Real.logb 2 (p : ℝ))) ^ 2
      = sumDelta S a - η * sumAlpha S a + η ^ 2 / 4 * sumG S := by
    unfold sumDelta sumAlpha sumG
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl key
  rw [hsum]
  unfold discQR
  ring

/-- `t* ≥ η (g + √(g² − G))/2` for every exponent vector and every real `η ≥ 0`. -/
theorem tstarR_lower {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) {η : ℝ} (hη : 0 ≤ η) :
    η * (sumA S + Real.sqrt ((sumA S) ^ 2 - sumG S)) / 2 ≤ tstarR S a η := by
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb' (hS p hp)
  have hid := discQR_identity hS a η
  have hsum0 : 0 ≤ ∑ p ∈ S, Real.logb 2 (p : ℝ) * ((a p : ℝ) - η / (2 * Real.logb 2 (p : ℝ))) ^ 2 := by
    apply Finset.sum_nonneg
    intro p hp
    have hl := hlb p hp
    have : 0 ≤ Real.logb 2 (p : ℝ) := by linarith
    positivity
  have hGg : 0 ≤ (sumA S) ^ 2 - sumG S := sub_nonneg.2 (sumG_le hS)
  have hQ : η ^ 2 * ((sumA S) ^ 2 - sumG S) ≤ discQR S a η := by
    rw [hid]
    linarith
  have hsq : η * Real.sqrt ((sumA S) ^ 2 - sumG S) ≤ Real.sqrt (discQR S a η) := by
    have h1 : Real.sqrt (η ^ 2 * ((sumA S) ^ 2 - sumG S)) = η * Real.sqrt ((sumA S) ^ 2 - sumG S) := by
      rw [Real.sqrt_mul (sq_nonneg η), Real.sqrt_sq hη]
    rw [← h1]
    exact Real.sqrt_le_sqrt hQ
  unfold tstarR
  linarith

/-- The exponent `Δ + M` of Theorem 3.1 is at least `((g + √(g² − G))/2)² η² − η`, for every exponent vector
`a` and every real `η ≥ 0`. -/
theorem exponent_lower {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) {η : ℝ} (hη : 0 ≤ η) :
    ((sumA S + Real.sqrt ((sumA S) ^ 2 - sumG S)) / 2) ^ 2 * η ^ 2 - η
      ≤ sumDelta S a + (MstarR S a η : ℝ) := by
  have hGg : 0 ≤ (sumA S) ^ 2 - sumG S := sub_nonneg.2 (sumG_le hS)
  have hA0 : 0 ≤ sumA S := Finset.sum_nonneg (fun p _ => Real.sqrt_nonneg _)
  have hlow := tstarR_lower hS a hη
  have hτ : 0 ≤ η * (sumA S + Real.sqrt ((sumA S) ^ 2 - sumG S)) / 2 := by
    have := Real.sqrt_nonneg ((sumA S) ^ 2 - sumG S)
    positivity
  have h1 : (η * (sumA S + Real.sqrt ((sumA S) ^ 2 - sumG S)) / 2) ^ 2 ≤ (tstarR S a η) ^ 2 :=
    pow_le_pow_left₀ hτ hlow 2
  have hM : (tstarR S a η) ^ 2 - η - sumDelta S a ≤ (MstarR S a η : ℝ) := Nat.le_ceil _
  have h2 : ((sumA S + Real.sqrt ((sumA S) ^ 2 - sumG S)) / 2) ^ 2 * η ^ 2
      = (η * (sumA S + Real.sqrt ((sumA S) ^ 2 - sumG S)) / 2) ^ 2 := by ring
  rw [h2]
  linarith

end TVGPlus
end LeanCheck
