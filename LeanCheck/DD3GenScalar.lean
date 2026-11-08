import Mathlib
import LeanCheck.JAScalar
import LeanCheck.DD3GenHeights

/-!
# Three chains with general exponents: the scalar bound of the central estimate (Lean check)

Scope. Counterpart of `JAScalar` for the chains with general exponents `E b k`. The scalar `∏_{k<n} Z_{k+1}²/q_k²` carried by
the arc mass is bounded by the normalization `(∏ (α_k I₁ - 2))²` of the central bound, with `α_k = q_{k+1}/q_k` and
`I₁ = 16/(15 D)`. In `JAScalar.scalar_bound` the exponential factor comes from the geometric growth `4 α_k ≤ α_{k+1}`; here the
only inputs are `4 ≤ α_k I₁` and a uniform bound on `∑ 16/(α_k I₁)`:

* `Mod3 E`: `OK3 E` (strictly increasing exponents with the log-gap hypothesis) and the two properties of the modified
  families of `TVGplus_v29` (deletion rule `E k = m_k²` with `m_k ≥ k`, tilt `⌊λ k²⌋` with `λ ≥ 1`) that the central bound needs:
  `E b n ≥ n²` and `E b (n+1) ≤ 2 E b n` for `n ≥ 3`; `Mod3_sq`: the original chains satisfy it;
* `scalar_boundG`: the scalar bound from `4 ≤ α_k I₁` and `∑_{k<n} 16/(α_k I₁) ≤ S₀`, with the constant `exp S₀`;
* `alpha_lower`: under `Mod3`, `α_k = p^(E p (j+1) - E p j) ≥ exp(j/2)` (the gap `> sqrt(log Q_j) ≥ j/2` because `E ≥ n²`);
* `chainE_scalar_bound`: for the chain with start level `sE D = max(⌈D⌉, 30)`, the scalar bound with the constant `exp(45 D)`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open Finset JAMulti JAWindowQ JAHeights

/-- The exponent family satisfies the gap hypothesis and the two growth properties used by the central bound. -/
structure Mod3 (E : ℕ → ℕ → ℕ) : Prop where
  ok : OK3 E
  quad : ∀ b, (b = 2 ∨ b = 3 ∨ b = 5) → ∀ n, n ^ 2 ≤ E b n
  dbl : ∀ b, (b = 2 ∨ b = 3 ∨ b = 5) → ∀ n, 3 ≤ n → E b (n + 1) ≤ 2 * E b n

lemma Mod3_sq : Mod3 (fun _ k => k ^ 2) :=
  ⟨OK3_sq, fun _ _ _ => le_rfl, fun _ _ n hn => by nlinarith⟩

/-- **The scalar bound from `4 ≤ α_k I₁` and a uniform bound on `∑ 16/(α_k I₁)`.** -/
theorem scalar_boundG (c : Chain) (D : ℝ) (hD : 3 ≤ D) (hw : ∀ k, c.w (k + 1) = wQ D (c.q (k + 1)))
    (α : ℕ → ℕ) (hα : ∀ k, c.q (k + 1) = c.q k * α k)
    (hu : ∀ k, 4 ≤ (α k : ℝ) * (16 / (15 * D))) (S0 : ℝ)
    (hsum : ∀ n, ∑ k ∈ range n, 16 / ((α k : ℝ) * (16 / (15 * D))) ≤ S0) (n : ℕ) :
    ∏ k ∈ range n, ((∑ y, c.w (k + 1) y) ^ 2 / ((c.q k : ℕ) : ℝ) ^ 2) ≤
      Real.exp S0 * (∏ k ∈ range n, ((α k : ℝ) * (16 / (15 * D)) - 2)) ^ 2 := by
  have hD0 : 0 < D := by linarith
  set I : ℝ := 16 / (15 * D) with hIdef
  have hI : 0 < I := by positivity
  have hlevel : ∀ k, (∑ y, c.w (k + 1) y) ^ 2 / ((c.q k : ℕ) : ℝ) ^ 2 ≤
      Real.exp (16 / ((α k : ℝ) * I)) * ((α k : ℝ) * I - 2) ^ 2 := by
    intro k
    have hq : (1 : ℝ) ≤ (c.q k : ℝ) := by exact_mod_cast c.pos k
    have hq0 : (0 : ℝ) < (c.q k : ℝ) := by linarith
    have hQ : ((c.q (k + 1) : ℕ) : ℝ) = (c.q k : ℝ) * (α k : ℝ) := by
      rw [hα k]; push_cast; ring
    have hQ0 : (0 : ℝ) < ((c.q (k + 1) : ℕ) : ℝ) := by exact_mod_cast c.pos (k + 1)
    have hZ : (∑ y, c.w (k + 1) y) = ∑ y, wQ D (c.q (k + 1)) y := by rw [hw k]
    have hsum' := sum_wQ (Q := c.q (k + 1)) D hD
    rw [← hZ] at hsum'
    have hZle : (∑ y, c.w (k + 1) y) ≤ ((c.q (k + 1) : ℕ) : ℝ) * I + 2 := by
      have := (abs_le.mp hsum').2
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
    have hlb := JAScalar.level_bound ((α k : ℝ) * I) (hu k) _ hz0 hz
    rw [← div_pow]
    exact hlb
  have hprod : ∏ k ∈ range n, ((∑ y, c.w (k + 1) y) ^ 2 / ((c.q k : ℕ) : ℝ) ^ 2) ≤
      ∏ k ∈ range n, (Real.exp (16 / ((α k : ℝ) * I)) * ((α k : ℝ) * I - 2) ^ 2) :=
    Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => hlevel k)
  have hsplit : ∏ k ∈ range n, (Real.exp (16 / ((α k : ℝ) * I)) * ((α k : ℝ) * I - 2) ^ 2) =
      Real.exp (∑ k ∈ range n, 16 / ((α k : ℝ) * I)) * (∏ k ∈ range n, ((α k : ℝ) * I - 2)) ^ 2 := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_pow]
  calc ∏ k ∈ range n, ((∑ y, c.w (k + 1) y) ^ 2 / ((c.q k : ℕ) : ℝ) ^ 2)
      ≤ Real.exp (∑ k ∈ range n, 16 / ((α k : ℝ) * I)) * (∏ k ∈ range n, ((α k : ℝ) * I - 2)) ^ 2 :=
        hprod.trans (le_of_eq hsplit)
    _ ≤ Real.exp S0 * (∏ k ∈ range n, ((α k : ℝ) * I - 2)) ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hsum n)) (sq_nonneg _)

/-- Under `Mod3`, the ratio of consecutive scales is at least `exp(j/2)`. -/
lemma alpha_lower {E : ℕ → ℕ → ℕ} (hE : Mod3 E) {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5) (j : ℕ) :
    Real.exp ((j : ℝ) / 2) ≤ ((p ^ (E p (j + 1) - E p j) : ℕ) : ℝ) := by
  have hp2 : 2 ≤ p := by rcases hp with rfl | rfl | rfl <;> norm_num
  have hlogq : (1 / 4 : ℝ) ≤ Real.log p := JAMerged.log_ge_quarter hp2
  have hmono : E p j ≤ E p (j + 1) := ((hE.ok p hp).1).monotone (Nat.le_succ j)
  have hcast : ((E p (j + 1) - E p j : ℕ) : ℝ) = (E p (j + 1) : ℝ) - (E p j : ℝ) := by
    rw [Nat.cast_sub hmono]
  have hg := (hE.ok p hp).2 j
  have hquad : (j : ℝ) ^ 2 ≤ (E p j : ℝ) := by exact_mod_cast hE.quad p hp j
  have h1 : ((j : ℝ) / 2) ^ 2 ≤ (E p j : ℝ) * Real.log p := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (E p j)]
  have h2 : (j : ℝ) / 2 ≤ Real.sqrt ((E p j : ℝ) * Real.log p) := Real.le_sqrt_of_sq_le h1
  have h3 : (j : ℝ) / 2 ≤ ((E p (j + 1) - E p j : ℕ) : ℝ) * Real.log p := by
    rw [hcast]; nlinarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have h4 : Real.exp (((E p (j + 1) - E p j : ℕ) : ℝ) * Real.log p) = (p : ℝ) ^ (E p (j + 1) - E p j) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  calc Real.exp ((j : ℝ) / 2) ≤ Real.exp (((E p (j + 1) - E p j : ℕ) : ℝ) * Real.log p) :=
        Real.exp_le_exp.mpr h3
    _ = (p : ℝ) ^ (E p (j + 1) - E p j) := h4
    _ = ((p ^ (E p (j + 1) - E p j) : ℕ) : ℝ) := by push_cast; ring

lemma geom_two_thirds (n : ℕ) : ∑ k ∈ range n, ((2 : ℝ) / 3) ^ k ≤ 3 := by
  have h : ∀ n : ℕ, ∑ k ∈ range n, ((2 : ℝ) / 3) ^ k = 3 - 3 * ((2 : ℝ) / 3) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [h n]
  have : 0 ≤ 3 * ((2 : ℝ) / 3) ^ n := by positivity
  linarith

/-- **The scalar bound for the chains with general exponents**, start level `sE D`. -/
theorem chainE_scalar_bound {E : ℕ → ℕ → ℕ} (hE : Mod3 E) {p : ℕ} [NeZero p] (hp : p = 2 ∨ p = 3 ∨ p = 5)
    (D : ℝ) (hD : 3 ≤ D) (n : ℕ) :
    ∏ k ∈ range n, ((∑ y, (chainE p (E p) ((hE.ok p hp).1.monotone) (sE D) D).w (k + 1) y) ^ 2 /
        (((chainE p (E p) ((hE.ok p hp).1.monotone) (sE D) D).q k : ℕ) : ℝ) ^ 2) ≤
      Real.exp (45 * D) * (∏ k ∈ range n,
        (((p ^ (E p (sE D + k + 1) - E p (sE D + k)) : ℕ) : ℝ) * (16 / (15 * D)) - 2)) ^ 2 := by
  have hD0 : 0 < D := by linarith
  have hp2 : 2 ≤ p := by rcases hp with rfl | rfl | rfl <;> norm_num
  have hmono := (hE.ok p hp).1.monotone
  set s := sE D with hs
  have hsD : D ≤ (s : ℝ) := le_trans (Nat.le_ceil D) (Nat.cast_le.2 (le_max_left _ _))
  have hs30 : (30 : ℝ) ≤ (s : ℝ) := Nat.cast_le.2 (le_max_right _ _)
  have hIdef : (0 : ℝ) < 16 / (15 * D) := by positivity
  -- lower bound of α_k
  have hα : ∀ k : ℕ, Real.exp (((s : ℝ) + k) / 2) ≤
      ((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) := by
    intro k
    have := alpha_lower hE hp (s + k)
    rw [Nat.cast_add] at this
    exact this
  have hu : ∀ k : ℕ, 4 ≤ ((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) * (16 / (15 * D)) := by
    intro k
    have h1 : Real.exp ((s : ℝ) / 2) ≤ Real.exp (((s : ℝ) + k) / 2) :=
      Real.exp_le_exp.mpr (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
    have h2 : 1 + (s : ℝ) / 2 + ((s : ℝ) / 2) ^ 2 / 2 ≤ Real.exp ((s : ℝ) / 2) :=
      Real.quadratic_le_exp_of_nonneg (by positivity)
    have h3 : 15 * D / 4 ≤ ((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) := by
      have h4 : (s : ℝ) ^ 2 / 8 ≤ Real.exp ((s : ℝ) / 2) := by nlinarith [sq_nonneg (s : ℝ)]
      have h5 : 15 * D / 4 ≤ (s : ℝ) ^ 2 / 8 := by nlinarith
      exact le_trans h5 (le_trans h4 (le_trans h1 (hα k)))
    calc (4 : ℝ) = (15 * D / 4) * (16 / (15 * D)) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 hIdef.le
  have hexp12 : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
  have hsum : ∀ n, ∑ k ∈ range n, 16 / (((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) * (16 / (15 * D))) ≤
      45 * D := by
    intro n
    have hterm : ∀ k : ℕ, 16 / (((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) * (16 / (15 * D))) ≤
        15 * D * ((2 : ℝ) / 3) ^ k := by
      intro k
      have h1 : ((3 : ℝ) / 2) ^ k ≤ ((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) := by
        have h2 : ((3 : ℝ) / 2) ^ k ≤ Real.exp (1 / 2) ^ k := pow_le_pow_left₀ (by norm_num) hexp12 k
        have h3 : Real.exp (1 / 2) ^ k = Real.exp ((k : ℝ) / 2) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        have h4 : Real.exp ((k : ℝ) / 2) ≤ Real.exp (((s : ℝ) + k) / 2) :=
          Real.exp_le_exp.mpr (by linarith)
        exact le_trans h2 (h3 ▸ le_trans h4 (hα k))
      have hpos : (0 : ℝ) < ((3 : ℝ) / 2) ^ k := by positivity
      have hαpos : (0 : ℝ) < ((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) := lt_of_lt_of_le hpos h1
      rw [div_le_iff₀ (by positivity)]
      have h5 : ((2 : ℝ) / 3) ^ k * ((3 : ℝ) / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
      have h6 : 15 * D * ((2 : ℝ) / 3) ^ k * (((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) * (16 / (15 * D))) =
          16 * (((2 : ℝ) / 3) ^ k * ((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ)) := by
        field_simp
      rw [h6]
      have h7 : ((2 : ℝ) / 3) ^ k * ((3 : ℝ) / 2) ^ k ≤
          ((2 : ℝ) / 3) ^ k * ((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    calc ∑ k ∈ range n, 16 / (((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) * (16 / (15 * D)))
        ≤ ∑ k ∈ range n, 15 * D * ((2 : ℝ) / 3) ^ k := Finset.sum_le_sum (fun k _ => hterm k)
      _ = 15 * D * ∑ k ∈ range n, ((2 : ℝ) / 3) ^ k := by rw [Finset.mul_sum]
      _ ≤ 15 * D * 3 := mul_le_mul_of_nonneg_left (geom_two_thirds n) (by positivity)
      _ = 45 * D := by ring
  refine scalar_boundG (chainE p (E p) hmono s D) D hD (fun k => rfl)
    (fun k => p ^ (E p (s + k + 1) - E p (s + k))) ?_ hu (45 * D) hsum n
  intro k
  show p ^ (E p (s + (k + 1))) = p ^ (E p (s + k)) * p ^ (E p (s + k + 1) - E p (s + k))
  rw [← pow_add]
  congr 1
  have : E p (s + k) ≤ E p (s + k + 1) := hmono (Nat.le_succ _)
  rw [show s + (k + 1) = s + k + 1 from rfl]
  omega

/-- The ratio of consecutive scales of the chain `chainE`. -/
lemma chainE_alpha (p : ℕ) [NeZero p] (e : ℕ → ℕ) (he : Monotone e) (s : ℕ) (D : ℝ) (k : ℕ) :
    (chainE p e he s D).q (k + 1) = (chainE p e he s D).q k * p ^ (e (s + k + 1) - e (s + k)) := by
  show p ^ (e (s + (k + 1))) = p ^ (e (s + k)) * p ^ (e (s + k + 1) - e (s + k))
  rw [← pow_add]
  congr 1
  have : e (s + k) ≤ e (s + k + 1) := he (Nat.le_succ _)
  rw [show s + (k + 1) = s + k + 1 from rfl]
  omega

/-- Under `Mod3` and start level `sE D`, `α_k I₁ ≥ 4` (so `> 2`). -/
lemma alpha_I_ge4 {E : ℕ → ℕ → ℕ} (hE : Mod3 E) {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5) (D : ℝ) (hD : 3 ≤ D) (k : ℕ) :
    4 ≤ ((p ^ (E p (sE D + k + 1) - E p (sE D + k)) : ℕ) : ℝ) * (16 / (15 * D)) := by
  have hD0 : 0 < D := by linarith
  set s := sE D with hs
  have hsD : D ≤ (s : ℝ) := le_trans (Nat.le_ceil D) (Nat.cast_le.2 (le_max_left _ _))
  have hs30 : (30 : ℝ) ≤ (s : ℝ) := Nat.cast_le.2 (le_max_right _ _)
  have hIdef : (0 : ℝ) < 16 / (15 * D) := by positivity
  have hα : Real.exp (((s : ℝ) + k) / 2) ≤ ((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) := by
    have := alpha_lower hE hp (s + k)
    rw [Nat.cast_add] at this
    exact this
  have h1 : Real.exp ((s : ℝ) / 2) ≤ Real.exp (((s : ℝ) + k) / 2) :=
    Real.exp_le_exp.mpr (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  have h2 : 1 + (s : ℝ) / 2 + ((s : ℝ) / 2) ^ 2 / 2 ≤ Real.exp ((s : ℝ) / 2) :=
    Real.quadratic_le_exp_of_nonneg (by positivity)
  have h3 : 15 * D / 4 ≤ ((p ^ (E p (s + k + 1) - E p (s + k)) : ℕ) : ℝ) := by
    have h4 : (s : ℝ) ^ 2 / 8 ≤ Real.exp ((s : ℝ) / 2) := by nlinarith [sq_nonneg (s : ℝ)]
    have h5 : 15 * D / 4 ≤ (s : ℝ) ^ 2 / 8 := by nlinarith
    exact le_trans h5 (le_trans h4 (le_trans h1 hα))
  calc (4 : ℝ) = (15 * D / 4) * (16 / (15 * D)) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 hIdef.le

end DD3Gen
end LeanCheck
