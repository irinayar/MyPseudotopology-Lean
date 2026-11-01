import LeanCheck.TVGPlusDual
import LeanCheck.TVGPlusPairGcd

/-!
# TVGplus: the dual of the `{2, 3}` join

Consequences of `dual_of_DD` and `contAt_of_denominator` for `S = {2, 3}`:

* `pair_dual_iff_of_JA`: given `JAProp`, the character `k ↦ e(kα)` is continuous for the `P_{2,3}`-topology if and only if
  `M α ∈ ℤ` for some `M > 0` whose prime factors lie in `{2, 3}`; i.e. the dual group is `ℤ[1/6]/ℤ`.
* the same under the Matveev two-term separation and under the weaker separation `exp(-c sqrt (log Q))`, `c < 1`.

No `sorry`; the only external hypothesis is the one named in each statement.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime JAAssembly

theorem pair_dual_iff_of_JA (hJA : JAProp) (α : ℝ) :
    ContAt ({2, 3} : Finset ℕ) α ↔
      ∃ M : ℕ, 0 < M ∧ (∀ r : ℕ, r.Prime → r ∣ M → r ∈ ({2, 3} : Finset ℕ)) ∧ ∃ z : ℤ, (M : ℝ) * α = z := by
  constructor
  · exact fun h => dual_of_DD prime_pair (DD_pair_of_JA hJA) h
  · rintro ⟨M, hM0, hM, z, h⟩
    exact contAt_of_denominator prime_pair hM0 hM h

theorem pair_dual_iff_of_matveev (A : ℝ) (hA : 0 ≤ A) (hP : JAClose.TwoTermSeparation A) (α : ℝ) :
    ContAt ({2, 3} : Finset ℕ) α ↔
      ∃ M : ℕ, 0 < M ∧ (∀ r : ℕ, r.Prime → r ∣ M → r ∈ ({2, 3} : Finset ℕ)) ∧ ∃ z : ℤ, (M : ℝ) * α = z :=
  pair_dual_iff_of_JA (JAWeil.JA_of_matveev A hA hP) α

theorem pair_dual_iff_of_weak_separation (c : ℝ) (h0 : 0 ≤ c) (h1 : c < 1)
    (hP : JAClose.TwoTermSep (fun t => c * t)) (α : ℝ) :
    ContAt ({2, 3} : Finset ℕ) α ↔
      ∃ M : ℕ, 0 < M ∧ (∀ r : ℕ, r.Prime → r ∣ M → r ∈ ({2, 3} : Finset ℕ)) ∧ ∃ z : ℤ, (M : ℝ) * α = z :=
  pair_dual_iff_of_JA (JAWeil.JA_of_weak_separation c h0 h1 hP) α

#print axioms pair_dual_iff_of_JA
#print axioms pair_dual_iff_of_weak_separation

end TVGPlus
end LeanCheck
