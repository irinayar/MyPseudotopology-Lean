import LeanCheck.TVGPlusOrderE
import LeanCheck.TVGPlusGcd

/-!
# TVGplus, Theorem "The logarithmic order" (two-sided form) and the exact one-prime value

`uS S δ = u_S(δ)` is the least positive integer in the ball `B^S_δ`.  With `L = log (1/δ)`:

* `uS_lower`: for every `b < c_S` there is `δ₀ > 0` with `exp (b L²) ≤ u_S(δ)` for `0 < δ < δ₀`;
  (this is `c_S ≤ liminf log u_S(δ) / L²`);
* `uS_upper`: for every `B > x_S` there is `δ₀ > 0` with `u_S(δ) ≤ 2 exp (B L²)` for `0 < δ < δ₀`;
  (this is `limsup log u_S(δ) / L² ≤ x_S`);
* `cS_le_xS`: `c_S ≤ x_S` (`OrderC`);
* `xS_singleton`: for one prime `p`, `x_{ {p} } = c_{ {p} } = 1 / (4 log p)`;
* `uS_singleton`: for one prime, `u_{ {p} }(δ) = p^(a_p(δ)²)` exactly, for every `δ > 0`.

The statements use the `δ₀`-formulation of `liminf`/`limsup` bounds (equivalent to the filter statements).
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- `u_S(δ)`: the least positive integer in the ball `B^S_δ` (`0` if there is none). -/
noncomputable def uS (S : Finset ℕ) (δ : ℝ) : ℕ := sInf {n : ℕ | 0 < n ∧ InBall S δ (n : ℤ)}

lemma uS_le {S : Finset ℕ} {δ : ℝ} {n : ℕ} (hn : 0 < n) (h : InBall S δ (n : ℤ)) : uS S δ ≤ n :=
  Nat.sInf_le ⟨hn, h⟩

lemma uS_mem {S : Finset ℕ} {δ : ℝ} (h : ∃ n : ℕ, 0 < n ∧ InBall S δ (n : ℤ)) :
    0 < uS S δ ∧ InBall S δ (uS S δ : ℤ) :=
  Nat.sInf_mem h

/-- Lower bound of the logarithmic order for `u_S`. -/
theorem uS_lower {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {b : ℝ} (hb : b < cS S) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      Real.exp (b * Real.log (1 / δ) ^ 2) ≤ (uS S δ : ℝ) := by
  obtain ⟨δ₁, hδ₁, h1⟩ := order_lower hS hb
  obtain ⟨δ₂, hδ₂, h2⟩ := order_upper hS (lt_add_one (xS S))
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro δ hδ hδ0
  obtain ⟨k, hk1, _, hk⟩ := h2 δ hδ (lt_of_lt_of_le hδ0 (min_le_right _ _))
  have hex : ∃ n : ℕ, 0 < n ∧ InBall S δ (n : ℤ) := by
    refine ⟨k.toNat, by omega, ?_⟩
    have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
    rw [this]; exact hk
  obtain ⟨hpos, hmem⟩ := uS_mem hex
  have := h1 δ hδ (lt_of_lt_of_le hδ0 (min_le_left _ _)) (uS S δ : ℤ) (by exact_mod_cast hpos) hmem
  exact_mod_cast this

/-- Upper bound of the logarithmic order for `u_S`. -/
theorem uS_upper {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {B : ℝ} (hB : xS S < B) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      (uS S δ : ℝ) ≤ 2 * Real.exp (B * Real.log (1 / δ) ^ 2) := by
  obtain ⟨δ₀, hδ₀, h⟩ := order_upper hS hB
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδ1
  obtain ⟨k, hk1, hkB, hk⟩ := h δ hδ hδ1
  have hkn : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
  have hle : uS S δ ≤ k.toNat := uS_le (by omega) (by rw [hkn]; exact hk)
  have : (uS S δ : ℝ) ≤ (k : ℝ) := by
    have h2 : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast hkn
    rw [← h2]; exact_mod_cast hle
  linarith

/-- For one prime, `x_S = c_S`. -/
theorem xS_singleton {p : ℕ} (hp : p.Prime) : xS {p} = cS {p} := by
  have hl := log_pos_of_prime hp
  have hA : aS {p} = 1 / Real.sqrt (Real.log p) := by simp [aS]
  have hc : cS {p} = 1 / (4 * Real.log p) := by simp [cS]
  have hsq : (1 / Real.sqrt (Real.log p)) ^ 2 = 1 / Real.log p := by
    rw [div_pow, Real.sq_sqrt hl.le]; simp
  have hd : aS {p} ^ 2 - 4 * cS {p} = 0 := by
    rw [hA, hc, hsq]; field_simp; ring
  unfold xS yPlus
  rw [hd, Real.sqrt_zero, add_zero, hA, hc]
  have e : (1 / Real.sqrt (Real.log p) / 2) ^ 2 = (1 / Real.sqrt (Real.log p)) ^ 2 / 4 := by ring
  rw [e, hsq]
  field_simp

/-- For one prime the least positive witness is exactly `p^(a_p(δ)²)`. -/
theorem uS_singleton {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) :
    uS {p} δ = p ^ (aThr p δ ^ 2) := by
  have hmem : 0 < p ^ (aThr p δ ^ 2) ∧ InBall {p} δ ((p ^ (aThr p δ ^ 2) : ℕ) : ℤ) := by
    refine ⟨pow_pos hp.pos _, ?_⟩
    intro q hq
    rw [Finset.mem_singleton] at hq
    subst hq
    push_cast
    exact sharp_prime hp hδ
  apply le_antisymm (uS_le hmem.1 hmem.2)
  obtain ⟨hpos, hball⟩ := uS_mem ⟨_, hmem⟩
  have hdiv := forced (S := {p}) (by simpa using hp) hδ hball
  have : Dvis {p} δ = p ^ (aThr p δ ^ 2) := by simp [Dvis]
  rw [this] at hdiv
  exact Nat.le_of_dvd hpos (by exact_mod_cast hdiv)

#print axioms uS_lower
#print axioms uS_upper
#print axioms xS_singleton
#print axioms uS_singleton

end TVGPlus
end LeanCheck
