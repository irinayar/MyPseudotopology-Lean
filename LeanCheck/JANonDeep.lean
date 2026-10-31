import Mathlib
import LeanCheck.JAMerged

/-!
# The central bound, step 6c: the non-deep levels

A level with period `Q = b^(n^2)` (`b ∈ {2,3}`), `t = sqrt (log Q)`, is *deep* when `X ≥ 4 Q exp(A log^2(2+t))` (equation (deep-level)
of the paper); then the two-term separation radius `u = Q^{-1} exp(-A log^2(2+t))` satisfies `u ≥ 2ε` with `ε = 2/X`.

Checked here (no axiom, no `sorry`):

* `deep_radius`: a deep level has `2 · (2/X) ≤ Q^{-1} exp(-A log^2(2+t))`;
* `log_le_four_rootroot`, `poly_eventually`: the elementary asymptotics `(c + A log^2(2+S))^2 + (c + A log^2(2+S)) ≤ S^2` for
  all large `S` (this is the statement that the non-deep window has width `O((log log X)^2)`, small against `sqrt(log X)`);
* `non_deep_card_le_two`: for `D ≥ 1`, `A ≥ 0` and all large `X`, any finite set of distinct periods `b^(n^2)` (`b ∈ {2,3}`, `n ≥ 1`) that
  are at most `D X` and are NOT deep contains at most two elements (the paper only needs "at most four").
-/

namespace LeanCheck
namespace JANonDeep

/-- `log (b^(n^2)) = lp b n`. -/
lemma log_period (b n : ℕ) : Real.log ((b ^ (n ^ 2) : ℕ) : ℝ) = JAMerged.lp b n := by
  rw [Nat.cast_pow, Real.log_pow]
  simp [JAMerged.lp]

/-- A deep level has separation radius at least `2ε = 4/X`. -/
lemma deep_radius (X Q a : ℝ) (hX : 0 < X) (hQ : 0 < Q) (h : 4 * Q * Real.exp a ≤ X) :
    2 * (2 / X) ≤ Real.exp (-a) / Q := by
  have hE : 0 < Real.exp a := Real.exp_pos a
  have e : Real.exp (-a) / Q = 1 / (Q * Real.exp a) := by
    rw [Real.exp_neg]; field_simp
  rw [e]
  have e2 : 2 * (2 / X) = 4 / X := by ring
  rw [e2, div_le_div_iff₀ hX (by positivity)]
  linarith

/-- `log z ≤ 4 sqrt (sqrt z)` for `z ≥ 1`. -/
lemma log_le_four_rootroot (z : ℝ) (hz : 1 ≤ z) : Real.log z ≤ 4 * Real.sqrt (Real.sqrt z) := by
  have hz0 : 0 < z := by linarith
  have h1 : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz0
  have h2 : 0 < Real.sqrt (Real.sqrt z) := Real.sqrt_pos.mpr h1
  have e1 : Real.log (Real.sqrt z) = Real.log z / 2 := Real.log_sqrt hz0.le
  have e2 : Real.log (Real.sqrt (Real.sqrt z)) = Real.log (Real.sqrt z) / 2 := Real.log_sqrt h1.le
  have h3 := Real.log_le_sub_one_of_pos h2
  linarith

/-- The square of the logarithm is at most `16 sqrt (2+S)`. -/
lemma log_sq_le (S : ℝ) (hS : 0 ≤ S) : (Real.log (2 + S)) ^ 2 ≤ 16 * Real.sqrt (2 + S) := by
  have hz : 1 ≤ 2 + S := by linarith
  have h := log_le_four_rootroot (2 + S) hz
  have h0 : 0 ≤ Real.log (2 + S) := Real.log_nonneg hz
  have hs : Real.sqrt (Real.sqrt (2 + S)) ^ 2 = Real.sqrt (2 + S) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  calc (Real.log (2 + S)) ^ 2 ≤ (4 * Real.sqrt (Real.sqrt (2 + S))) ^ 2 := by
        exact pow_le_pow_left₀ h0 h 2
    _ = 16 * Real.sqrt (2 + S) := by rw [mul_pow, hs]; norm_num

/-- **The non-deep window is small**: for large `S`, `w^2 + w ≤ S^2` with `w = c + A log^2(2+S)`. -/
lemma poly_eventually (c A : ℝ) (hc : 0 ≤ c) (hA : 0 ≤ A) :
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ S : ℝ, S₀ ≤ S →
      (c + A * (Real.log (2 + S)) ^ 2) ^ 2 + (c + A * (Real.log (2 + S)) ^ 2) ≤ S ^ 2 := by
  set K : ℝ := 2 * c ^ 2 + c + 512 * A ^ 2 + 16 * A with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨4 * K + 4, by linarith, ?_⟩
  intro S hS
  have hS0 : 0 ≤ S := by linarith
  set ρ : ℝ := Real.sqrt (2 + S) with hρ
  have hρ2 : ρ ^ 2 = 2 + S := Real.sq_sqrt (by linarith)
  have hρ1 : 1 ≤ ρ := by
    rw [hρ]; apply Real.one_le_sqrt.mpr; linarith
  have hlam := log_sq_le S hS0
  rw [← hρ] at hlam
  set lam : ℝ := (Real.log (2 + S)) ^ 2 with hlamdef
  have hlam0 : 0 ≤ lam := by positivity
  have hw : c + A * lam ≤ c + 16 * A * ρ := by nlinarith
  have hw0 : 0 ≤ c + A * lam := by positivity
  have hsq : (c + A * lam) ^ 2 ≤ (c + 16 * A * ρ) ^ 2 := pow_le_pow_left₀ hw0 hw 2
  have hρρ : ρ ≤ ρ ^ 2 := by nlinarith
  have hAρ : 0 ≤ A * ρ := by positivity
  have h1 : (c + 16 * A * ρ) ^ 2 ≤ 2 * c ^ 2 + 512 * A ^ 2 * ρ ^ 2 := by
    nlinarith [sq_nonneg (c - 16 * A * ρ)]
  have h2 : 2 * c ^ 2 + 512 * A ^ 2 * ρ ^ 2 + (c + 16 * A * ρ) ≤ K * ρ ^ 2 := by
    have hρ2' : 1 ≤ ρ ^ 2 := by nlinarith
    have hA2 : 0 ≤ A ^ 2 := by positivity
    have hc2 : 0 ≤ c ^ 2 := by positivity
    rw [hK]
    nlinarith [mul_nonneg hA hc, mul_le_mul_of_nonneg_left hρρ hA, mul_le_mul_of_nonneg_left hρ2' hc,
      mul_le_mul_of_nonneg_left hρ2' hc2]
  have h3 : K * ρ ^ 2 ≤ S ^ 2 := by
    rw [hρ2]
    have h4 : (4 * K + 4) * S ≤ S * S := by nlinarith
    nlinarith [mul_nonneg hK0 hS0]
  calc (c + A * lam) ^ 2 + (c + A * lam) ≤ (c + 16 * A * ρ) ^ 2 + (c + 16 * A * ρ) := by linarith
    _ ≤ 2 * c ^ 2 + 512 * A ^ 2 * ρ ^ 2 + (c + 16 * A * ρ) := by linarith
    _ ≤ K * ρ ^ 2 := h2
    _ ≤ S ^ 2 := h3

/-- **At most two non-deep levels** (S6c).  For `D ≥ 1`, `A ≥ 0` and every large `X`, a finite set of distinct periods `b^(n^2)` with
`b ∈ {2,3}`, `n ≥ 1`, each at most `D X` and each failing the depth condition `X ≥ 4 Q exp(A log^2(2+sqrt(log Q)))`, has at most two
elements. -/
theorem non_deep_card_le_two (D A : ℝ) (hD : 1 ≤ D) (hA : 0 ≤ A) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ s : Finset (ℕ × ℕ),
      (∀ p ∈ s, (p.1 = 2 ∨ p.1 = 3) ∧ 1 ≤ p.2 ∧ ((p.1 ^ (p.2 ^ 2) : ℕ) : ℝ) ≤ D * X ∧
        X < 4 * ((p.1 ^ (p.2 ^ 2) : ℕ) : ℝ) *
          Real.exp (A * (Real.log (2 + Real.sqrt (Real.log ((p.1 ^ (p.2 ^ 2) : ℕ) : ℝ)))) ^ 2)) →
      s.card ≤ 2 := by
  set c : ℝ := Real.log D + Real.log 4 with hc
  have hc0 : 0 ≤ c := by
    have h1 : 0 ≤ Real.log D := Real.log_nonneg hD
    have h2 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [hc]; linarith
  obtain ⟨S₀, hS₀0, hS₀⟩ := poly_eventually c A hc0 hA
  refine ⟨Real.exp (S₀ ^ 2), ?_⟩
  intro X hX s hs
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hDX : 0 < D * X := by positivity
  have hlogDX : S₀ ^ 2 ≤ Real.log (D * X) := by
    have h1 : S₀ ^ 2 ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
    have h2 : 0 ≤ Real.log D := Real.log_nonneg hD
    rw [Real.log_mul (by linarith) hXpos.ne']
    linarith
  set S : ℝ := Real.sqrt (Real.log (D * X)) with hS
  have hlogDX0 : 0 ≤ Real.log (D * X) := le_trans (sq_nonneg _) hlogDX
  have hS2 : S ^ 2 = Real.log (D * X) := Real.sq_sqrt hlogDX0
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSS₀ : S₀ ≤ S := by
    rw [hS]; exact Real.le_sqrt_of_sq_le hlogDX
  have hpoly := hS₀ S hSS₀
  set lam : ℝ := (Real.log (2 + S)) ^ 2 with hlam
  set w : ℝ := c + A * lam with hw
  have hlam0 : 0 ≤ lam := by positivity
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hlogDX_split : Real.log (D * X) = Real.log D + Real.log X := Real.log_mul (by linarith) hXpos.ne'
  apply JAMerged.window_card_le_two s (S ^ 2 - w) (S ^ 2)
  · -- window width
    have hu : w ^ 2 ≤ S ^ 2 - w := by linarith
    have : w ≤ Real.sqrt (S ^ 2 - w) :=
      calc w = Real.sqrt (w ^ 2) := (Real.sqrt_sq hw0).symm
        _ ≤ Real.sqrt (S ^ 2 - w) := Real.sqrt_le_sqrt hu
    linarith
  · intro p hp
    obtain ⟨hb, hn, hQle, hnd⟩ := hs p hp
    have hbpos : 2 ≤ p.1 := by rcases hb with h | h <;> omega
    have hQpos : (0 : ℝ) < ((p.1 ^ (p.2 ^ 2) : ℕ) : ℝ) := by
      have : 0 < p.1 ^ (p.2 ^ 2) := pow_pos (by omega) _
      exact_mod_cast this
    have hlp : JAMerged.lp p.1 p.2 = Real.log ((p.1 ^ (p.2 ^ 2) : ℕ) : ℝ) := (log_period _ _).symm
    refine ⟨hb, ?_, ?_⟩
    · -- lower end
      rw [hlp]
      set Q : ℝ := ((p.1 ^ (p.2 ^ 2) : ℕ) : ℝ) with hQ
      set tq : ℝ := Real.sqrt (Real.log Q) with htq
      have hlogQ_le : Real.log Q ≤ S ^ 2 := by
        rw [hS2]; exact Real.log_le_log hQpos hQle
      have hlogQ0 : 0 ≤ Real.log Q := by
        have : (1 : ℝ) ≤ Q := by
          rw [hQ]
          have : 1 ≤ p.1 ^ (p.2 ^ 2) := Nat.one_le_pow _ _ (by omega)
          exact_mod_cast this
        exact Real.log_nonneg this
      have htq_le : tq ≤ S := by
        rw [htq, hS]
        apply Real.sqrt_le_sqrt
        rw [← hS2]; exact hlogQ_le
      have htq0 : 0 ≤ tq := Real.sqrt_nonneg _
      have hlam_le : (Real.log (2 + tq)) ^ 2 ≤ lam := by
        have h1 : 0 ≤ Real.log (2 + tq) := Real.log_nonneg (by linarith)
        have h2 : Real.log (2 + tq) ≤ Real.log (2 + S) := Real.log_le_log (by linarith) (by linarith)
        exact pow_le_pow_left₀ h1 h2 2
      have hexp : Real.exp (A * (Real.log (2 + tq)) ^ 2) ≤ Real.exp (A * lam) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlam_le hA)
      have hnd' : X < 4 * Q * Real.exp (A * lam) :=
        lt_of_lt_of_le hnd (by
          apply mul_le_mul_of_nonneg_left hexp (by positivity))
      have hlogX : Real.log X < Real.log (4 * Q * Real.exp (A * lam)) :=
        Real.log_lt_log hXpos hnd'
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by norm_num) hQpos.ne',
        Real.log_exp] at hlogX
      rw [hw, hc]
      linarith
    · rw [hlp, hS2]
      exact Real.log_le_log hQpos hQle

#print axioms deep_radius
#print axioms poly_eventually
#print axioms non_deep_card_le_two

end JANonDeep
end LeanCheck
