import LeanCheck.MixedPrimeFlat
import LeanCheck.ChainLemmas

/-!
# TVGaddmore_v17: continuity ⇔ Lipschitz ⇔ little-o (Proposition 2.5 and Theorem "flatness")

For an infinite set `S` of positive scales and `x : ℝ`, continuity of `k ↦ e(kx)` at `0` in the topology of
`Pn S` is `∀ ε > 0, ∃ δ > 0, ∀ k, Pn S k < δ → nrm (k x) < ε`.  We prove
quarter-arc continuity ⇒ Lipschitz (Prop. 2.5, necessity) and the equivalence of continuity with
the little-o condition (Theorem "flatness").
-/

namespace LeanCheck
namespace MixedPrime

/-- Quarter-arc continuity at `0` implies the Lipschitz bound `nrm (k x) ≤ P(k) / (2 δ)`. -/
theorem lipschitz_of_quarter {S : Set ℕ} (hpos : ∀ q ∈ S, 0 < q) (hinf : S.Infinite) {x δ : ℝ}
    (hδ : 0 < δ) (h : ∀ k : ℤ, Pn S k < δ → nrm ((k : ℝ) * x) < 1 / 4) (k : ℤ) :
    nrm ((k : ℝ) * x) ≤ (1 / (2 * δ)) * Pn S k := by
  have hSne : S.Nonempty := hinf.nonempty
  by_cases hk : k = 0
  · subst hk; simp [nrm]; exact mul_nonneg (by positivity) (Pn_nonneg S 0)
  set p := Pn S k with hp
  have hp0 : 0 < p := Pn_pos hpos hinf hk
  by_cases hpδ : δ ≤ p
  · calc nrm ((k : ℝ) * x) ≤ 1 / 2 := nrm_le_half _
      _ ≤ (1 / (2 * δ)) * p := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]; linarith
  · push_neg at hpδ
    set j : ℕ := ⌈δ / p⌉₊ - 1 with hj
    have hy : 1 < δ / p := by rw [lt_div_iff₀ hp0]; linarith
    have hcl : δ / p ≤ ⌈δ / p⌉₊ := Nat.le_ceil _
    have hj1 : 1 ≤ j := by
      have : 2 ≤ ⌈δ / p⌉₊ := by
        have h1 : (1 : ℝ) < ⌈δ / p⌉₊ := lt_of_lt_of_le hy hcl
        have : 1 < ⌈δ / p⌉₊ := by exact_mod_cast h1
        omega
      omega
    have hjc : (j : ℝ) + 1 = ⌈δ / p⌉₊ := by
      have : 1 ≤ ⌈δ / p⌉₊ := by omega
      rw [hj]; push_cast [Nat.cast_sub this]; ring
    have hjp : (j : ℝ) * p < δ := by
      have : (j : ℝ) < δ / p := by
        have h2 := Nat.ceil_lt_add_one (show 0 ≤ δ / p by positivity)
        linarith
      rwa [lt_div_iff₀ hp0] at this
    have hj1p : δ ≤ ((j : ℝ) + 1) * p := by
      rw [hjc]; rwa [← div_le_iff₀ hp0]
    -- all multiples up to j are within 1/4
    have hmult : ∀ ρ : ℕ, ρ ≤ j → ∃ n : ℤ, |(ρ : ℝ) * ((k : ℝ) * x) - n| < 1 / 4 := by
      intro ρ hρ
      have hP : Pn S ((ρ : ℤ) * k) ≤ ρ * p := Pn_nsmul_le hSne ρ k
      have hlt : Pn S ((ρ : ℤ) * k) < δ := by
        have : (ρ : ℝ) * p ≤ j * p := by gcongr
        linarith
      have := h _ hlt
      refine ⟨round ((ρ : ℝ) * ((k : ℝ) * x)), ?_⟩
      have e : (((ρ : ℤ) * k : ℤ) : ℝ) * x = (ρ : ℝ) * ((k : ℝ) * x) := by push_cast; ring
      rw [e, nrm_eq] at this
      exact this
    obtain ⟨m, hm⟩ := near_of_all_multiples (θ := (k : ℝ) * x) hj1 hmult
    have hn : nrm ((k : ℝ) * x) ≤ 1 / (4 * j) := by
      have : nrm ((k : ℝ) * x) ≤ |(k : ℝ) * x - m| := by
        have e : (k : ℝ) * x = ((k : ℝ) * x - m) + m := by ring
        calc nrm ((k : ℝ) * x) = nrm (((k : ℝ) * x - m) + m) := by rw [← e]
          _ = nrm ((k : ℝ) * x - m) := nrm_add_int _ m
          _ ≤ |(k : ℝ) * x - m| := nrm_le_abs _
      exact this.trans hm
    refine hn.trans ?_
    have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have h2 : δ ≤ 2 * j * p := by nlinarith
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- **Continuity ⇔ little-o** (Theorem "flatness", Proposition 2.5): for an infinite set `S` of positive
scales, `x` defines a continuous character iff `‖k x‖ = o(P(k))` as `P(k) → 0`. -/
theorem continuity_iff_flat {S : Set ℕ} (hpos : ∀ q ∈ S, 0 < q) (hinf : S.Infinite) (x : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℤ, Pn S k < δ → nrm ((k : ℝ) * x) < ε) ↔
    (∀ κ : ℝ, 0 < κ → ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℤ, k ≠ 0 → Pn S k < ε → nrm ((k : ℝ) * x) < κ * Pn S k) := by
  constructor
  · intro hc κ hκ
    obtain ⟨δ, hδ, hδk⟩ := hc (1 / 4) (by norm_num)
    have hC : ∀ k : ℤ, nrm ((k : ℝ) * x) ≤ (1 / (2 * δ)) * Pn S k :=
      lipschitz_of_quarter hpos hinf hδ hδk
    exact flatness_necessity hpos hinf (by positivity) hC hκ
  · intro hf ε hε
    obtain ⟨ε0, hε0, h0⟩ := hf 1 one_pos
    refine ⟨min ε0 ε, lt_min hε0 hε, fun k hk => ?_⟩
    by_cases hk0 : k = 0
    · subst hk0; simp [nrm, hε]
    · have h1 := h0 k hk0 (lt_of_lt_of_le hk (min_le_left _ _))
      have h2 : Pn S k < ε := lt_of_lt_of_le hk (min_le_right _ _)
      linarith

end MixedPrime
end LeanCheck
