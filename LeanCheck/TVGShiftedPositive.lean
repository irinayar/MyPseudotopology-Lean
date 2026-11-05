import LeanCheck.TVGShiftedLongNull

/-!
# TVGplus: from a signed shifted witness to a positive one, without loss in the exponent

`positive_from_signed_long`: let `p ≠ q` be integers `≥ 2`, `0 < ε`, and let `k₀` with `|k₀| ≤ H` satisfy
`P_p(k₀ - 1) < ε/2` and `P_q(k₀) < ε/2`.  Choose `L` with `H + 1 ≤ 2^L` and `h ≥ 1` with `4 ≤ 2^h ε`.  Then there is an
integer `k` with `1 ≤ k ≤ H + 2^(2L + 16 h²)`, `P_p(k - 1) < ε` and `P_q(k) < ε`.

The proof adds a null witness `v ≥ H + 1` at radius `ε/2` (`explicit_long_null`, the pigeonhole argument of
`TVGPlusCount` with an additional residue class modulo `H + 1`); `k = k₀ + v` is positive and subadditivity of the
pseudonorms gives the errors.  Since `2^(2L) ≤ 4 (H + 1)²`, a signed bound `H ≤ exp(C log²(1/ε))` yields a positive bound
`exp(C' log²(1/ε))`: the exponent `2` is preserved.
-/

namespace LeanCheck.ShiftedHeight

open LeanCheck.MixedPrime LeanCheck.TVGPlus

theorem positive_from_signed_long {p q H L h : ℕ} {ε : ℝ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : p ≠ q) (hε : 0 < ε) (hh : 1 ≤ h)
    (hprec : 4 ≤ ((2 ^ h : ℕ) : ℝ) * ε) (hHL : H + 1 ≤ 2 ^ L)
    {k0 : ℤ} (hlo : -(H : ℤ) ≤ k0) (hhi : k0 ≤ H)
    (hP0 : Pn (sqScales p) (k0 - 1) < ε / 2) (hQ0 : Pn (sqScales q) k0 < ε / 2) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ (H : ℤ) + ((2 ^ (2 * L + 16 * h ^ 2) : ℕ) : ℤ) ∧
      Pn (sqScales p) (k - 1) < ε ∧ Pn (sqScales q) k < ε := by
  classical
  have hδ : 0 < ε / 2 := by positivity
  have hm : 2 ≤ ((2 ^ h : ℕ) : ℝ) * (ε / 2) := by linarith
  have hcard : ({p, q} : Finset ℕ).card = 2 := by simp [hpq]
  obtain ⟨v, hvlo, hvhi, hball⟩ := explicit_long_null (S := ({p, q} : Finset ℕ))
    (by intro r hr; simp at hr; rcases hr with rfl | rfl <;> assumption)
    (by simp [hpq]) hδ (2 ^ h) h L (H + 1) (by omega) hHL hm (Nat.le_refl _) hh
  simp only [hcard] at hvhi
  have hvhi' : v ≤ ((2 ^ (2 * L + 16 * h ^ 2) : ℕ) : ℤ) := by
    simpa only [Nat.reducePow, Nat.reduceMul] using hvhi
  have hpv : Pn (sqScales p) v < ε / 2 := hball p (by simp)
  have hqv : Pn (sqScales q) v < ε / 2 := hball q (by simp)
  refine ⟨k0 + v, ?_, ?_, ?_, ?_⟩
  · push_cast at hvlo; omega
  · omega
  · have e : k0 + v - 1 = (k0 - 1) + v := by ring
    rw [e]
    calc Pn (sqScales p) ((k0 - 1) + v)
        ≤ Pn (sqScales p) (k0 - 1) + Pn (sqScales p) v := Pn_add_le (sq_nonempty p) _ _
      _ < ε / 2 + ε / 2 := add_lt_add hP0 hpv
      _ = ε := by ring
  · calc Pn (sqScales q) (k0 + v)
        ≤ Pn (sqScales q) k0 + Pn (sqScales q) v := Pn_add_le (sq_nonempty q) _ _
      _ < ε / 2 + ε / 2 := add_lt_add hQ0 hqv
      _ = ε := by ring

#print axioms positive_from_signed_long

end LeanCheck.ShiftedHeight
