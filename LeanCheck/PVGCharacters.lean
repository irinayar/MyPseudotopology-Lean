import Mathlib

/-!
# PVG: the trivial-intersection step of Proposition 8.17 (Lean check)

Scope. In `PVG_v9` (Pseudotopological Vector Groups on Real Line), Proposition 8.17 uses a
nonzero additive map `f : ℝ → ℚ` and the characters `χ_a (b) = f (a b) + ℤ` of `ℝ`, and
asserts `H₀ ∩ e(ℝ) = {0}`: if `χ_a = e x`, that is `f (a b) - x b ∈ ℤ` for all real `b`,
then `x = 0` and `a = 0`. `trivial_intersection` checks exactly this statement.
The group `Hom(ℝ, 𝕋)` itself is not formalized; the integrality condition is stated directly.
-/

namespace PVG

/-- If `f (a b) - x b` is an integer for every real `b`, with `f : ℝ →+ ℚ` nonzero, then
`x = 0` and `a = 0`. -/
theorem trivial_intersection (f : ℝ →+ ℚ) (hf : f ≠ 0) (a x : ℝ)
    (h : ∀ b : ℝ, ∃ n : ℤ, ((f (a * b) : ℚ) : ℝ) - x * b = n) : x = 0 ∧ a = 0 := by
  let φ : ℝ →+ ℝ :=
    (((Rat.castHom ℝ : ℚ →+* ℝ) : ℚ →+ ℝ).comp (f.comp (AddMonoidHom.mulLeft a))) -
      AddMonoidHom.mulLeft x
  have hφ : ∀ b, φ b = ((f (a * b) : ℚ) : ℝ) - x * b := fun b => by simp [φ]
  -- Step 1: `φ b = 0` for every `b` (an integer divisible by every positive integer).
  have hzero : ∀ b, ((f (a * b) : ℚ) : ℝ) - x * b = 0 := by
    intro b
    obtain ⟨n, hn⟩ := h b
    have hdvd : ∀ N : ℕ, 0 < N → (N : ℤ) ∣ n := by
      intro N hN
      obtain ⟨n', hn'⟩ := h (b / N)
      have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have h1 : φ b = N * φ (b / N) := by
        have hb : b = N • (b / N) := by
          rw [nsmul_eq_mul]; field_simp
        conv_lhs => rw [hb]
        rw [map_nsmul, nsmul_eq_mul]
      rw [hφ, hφ, hn, hn'] at h1
      have h2 : n = N * n' := by exact_mod_cast h1
      exact ⟨n', h2⟩
    have hn0 : n = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (hdvd (n.natAbs + 1) (Nat.succ_pos _))
      push_cast
      rw [Int.abs_eq_natAbs]
      omega
    rw [hn, hn0]; simp
  -- Step 2: `x = 0`.
  have hx : x = 0 := by
    by_contra hx0
    have hb := hzero (Real.sqrt 2 / x)
    have hxb : x * (Real.sqrt 2 / x) = Real.sqrt 2 := by field_simp
    rw [hxb] at hb
    have hq : Real.sqrt 2 = ((f (a * (Real.sqrt 2 / x)) : ℚ) : ℝ) := by linarith
    exact irrational_sqrt_two ⟨_, hq.symm⟩
  subst hx
  refine ⟨rfl, ?_⟩
  -- Step 3: `a = 0`.
  by_contra ha0
  apply hf
  ext c
  have := hzero (c / a)
  rw [zero_mul, sub_zero, mul_div_cancel₀ _ ha0] at this
  simpa using this

end PVG
