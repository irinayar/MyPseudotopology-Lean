import LeanCheck.TVGPlusCert

/-!
# TVGplus: the gcd certificates of the finite table (Section "Exact finite certificates")

`gcd_cert` formalizes the logic of the table: if finitely many explicit integers lie in the ball of radius `1/den`
(checked coordinate by coordinate by `memCheck`) and their gcd equals the universal divisor
`D = ∏ p^(a_p^2)`, then `D` divides every element of the ball (universal divisor theorem `forced`) and every
common divisor of the ball divides `D`; hence the gcd of the ball is exactly `D`.

The instances in `TVGPlusCertRowsData.lean` are the five rows of the table.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

lemma dvd_foldr_gcd (g : ℕ) (ks : List ℕ) (h : ∀ k ∈ ks, g ∣ k) : g ∣ ks.foldr Nat.gcd 0 := by
  induction ks with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons]
    exact Nat.dvd_gcd (h x (by simp)) (ih (fun k hk => h k (by simp [hk])))

/-- The conclusion of `gcd_cert`: the listed integers lie in the ball, `D` divides the whole ball, and every
common divisor of the ball divides `D`. -/
def GcdStmt (S : Finset ℕ) (den : ℕ) (a : ℕ → ℕ) (ks : List ℕ) : Prop :=
  (∀ k ∈ ks, InBall S (1 / (den : ℝ)) (k : ℤ)) ∧
  (∀ k : ℤ, InBall S (1 / (den : ℝ)) k → ((∏ p ∈ S, p ^ (a p ^ 2) : ℕ) : ℤ) ∣ k) ∧
  (∀ g : ℕ, (∀ k : ℤ, InBall S (1 / (den : ℝ)) k → (g : ℤ) ∣ k) → g ∣ ∏ p ∈ S, p ^ (a p ^ 2))

theorem gcd_cert {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {den : ℕ} (a : ℕ → ℕ) (hden : 0 < den)
    (hsp : ∀ p ∈ S, den < p ^ (2 * a p + 1) ∧ ∀ b < a p, p ^ (2 * b + 1) ≤ den)
    (ca cb N : ℕ) (hcb : 0 < cb) (hc : ca * den < cb) (ks : List ℕ)
    (hm : ∀ p ∈ S, ∀ k ∈ ks, memCheck p k ca cb N = true)
    (hg : ks.foldr Nat.gcd 0 = ∏ p ∈ S, p ^ (a p ^ 2)) :
    GcdStmt S den a ks := by
  unfold GcdStmt
  have hd' : (0 : ℝ) < den := by exact_mod_cast hden
  have hcb' : (0 : ℝ) < cb := by exact_mod_cast hcb
  have hδ : (0 : ℝ) < 1 / (den : ℝ) := by positivity
  have hlt : (ca : ℝ) / cb < 1 / (den : ℝ) := by
    rw [div_lt_div_iff₀ hcb' hd']
    have : ((ca * den : ℕ) : ℝ) < (cb : ℝ) := by exact_mod_cast hc
    push_cast at this ⊢
    linarith
  have hD : Dvis S (1 / (den : ℝ)) = ∏ p ∈ S, p ^ (a p ^ 2) := by
    unfold Dvis
    exact Finset.prod_congr rfl (fun p hp => by
      rw [aThr_eq_of_nat (hS p hp).two_le hden (hsp p hp).1 (hsp p hp).2])
  have hmem : ∀ k ∈ ks, InBall S (1 / (den : ℝ)) (k : ℤ) := by
    intro k hk p hp
    exact lt_of_le_of_lt (memCheck_spec (hS p hp).two_le hcb (hm p hp k hk)) hlt
  refine ⟨hmem, ?_, ?_⟩
  · intro k hk
    have := forced hS hδ hk
    rwa [hD] at this
  · intro g hgd
    rw [← hg]
    apply dvd_foldr_gcd
    intro k hk
    exact Int.natCast_dvd_natCast.mp (hgd (k : ℤ) (hmem k hk))

end TVGPlus
end LeanCheck
