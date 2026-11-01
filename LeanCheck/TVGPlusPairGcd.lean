import LeanCheck.TVGPlusPair
import LeanCheck.TVGPlusGcd
import LeanCheck.TVGPlusOrder

/-!
# TVGplus: the exact gcd and the logarithmic order for the pair `{2, 3}`

Consequences of `gcd_iff` and the logarithmic-order theorems for `S = {2, 3}`, from joint approximation:

* `pair_gcd_iff_of_JA`: given `JAProp`, `D_{2,3}(δ)` is the gcd of the ball `B^{2,3}_δ`;
* `pair_gcd_iff_of_matveev`, `pair_gcd_iff_of_weak_separation`: the same under the Matveev two-term separation, respectively under the
  weaker separation `Q⁻¹ exp(-c sqrt (log Q))`, `c < 1`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime JAAssembly

lemma prime_pair : ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num

theorem pair_gcd_iff_of_JA (hJA : JAProp) {δ : ℝ} (hδ : 0 < δ) (d : ℕ) :
    (∀ k : ℤ, InBall ({2, 3} : Finset ℕ) δ k → (d : ℤ) ∣ k) ↔ d ∣ Dvis ({2, 3} : Finset ℕ) δ :=
  gcd_iff prime_pair (DD_pair_of_JA hJA) hδ d

theorem pair_gcd_iff_of_matveev (A : ℝ) (hA : 0 ≤ A) (hP : JAClose.TwoTermSeparation A) {δ : ℝ}
    (hδ : 0 < δ) (d : ℕ) :
    (∀ k : ℤ, InBall ({2, 3} : Finset ℕ) δ k → (d : ℤ) ∣ k) ↔ d ∣ Dvis ({2, 3} : Finset ℕ) δ :=
  pair_gcd_iff_of_JA (JAWeil.JA_of_matveev A hA hP) hδ d

theorem pair_gcd_iff_of_weak_separation (c : ℝ) (h0 : 0 ≤ c) (h1 : c < 1)
    (hP : JAClose.TwoTermSep (fun t => c * t)) {δ : ℝ} (hδ : 0 < δ) (d : ℕ) :
    (∀ k : ℤ, InBall ({2, 3} : Finset ℕ) δ k → (d : ℤ) ∣ k) ↔ d ∣ Dvis ({2, 3} : Finset ℕ) δ :=
  pair_gcd_iff_of_JA (JAWeil.JA_of_weak_separation c h0 h1 hP) hδ d

#print axioms pair_gcd_iff_of_JA
#print axioms pair_gcd_iff_of_matveev
#print axioms pair_gcd_iff_of_weak_separation

end TVGPlus
end LeanCheck
