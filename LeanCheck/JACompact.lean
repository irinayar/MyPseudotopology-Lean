import Mathlib
import LeanCheck.JAMain
import LeanCheck.JAOnePrime

/-!
# The compact-quotient criterion, reduced to a general fact about precompact groups

`PrecompactMAP` is the textbook statement (Weil, via Peter–Weyl) that a precompact (totally bounded) group topology on `ℤ`
is maximally almost periodic: if `m` is not in the closure of `{0}`, some continuous character `n ↦ e(nα)` is nontrivial at `m`.
It is stated for a neighbourhood base `V ε` of `0` and does not mention `P_2`, `P_3`.

`compactQuotient_of_MAP` proves `CompactQuotientCriterion` (`SyndeticW → JAProp`) from `PrecompactMAP` by the argument of the paper:
the sets `W_ε = U_{3,ε} − U_{2,ε}` form such a neighbourhood base, syndeticity is precompactness, a continuous character is continuous for
both `P_3` (take `n = k`) and `P_2` (take `n = −k`), hence an integer by the one-prime theorem (`oneprime_two_three`), hence trivial.
-/

namespace LeanCheck
namespace JACompact

open MixedPrime JAAssembly

/-- **Weil's theorem for `ℤ`** (precompact group topologies on `ℤ` are maximally almost periodic). -/
def PrecompactMAP : Prop :=
  ∀ V : ℝ → Set ℤ,
    (∀ ε, 0 < ε → (0 : ℤ) ∈ V ε) →
    (∀ ε, 0 < ε → ∀ m ∈ V ε, -m ∈ V ε) →
    (∀ ε ε', 0 < ε → ε ≤ ε' → V ε ⊆ V ε') →
    (∀ ε, 0 < ε → ∃ ε', 0 < ε' ∧ ∀ a ∈ V ε', ∀ b ∈ V ε', a + b ∈ V ε) →
    (∀ ε, 0 < ε → ∃ F : Finset ℤ, ∀ z : ℤ, ∃ f ∈ F, z - f ∈ V ε) →
    ∀ m : ℤ, (∃ ε, 0 < ε ∧ m ∉ V ε) →
      ∃ α : ℝ, (∀ η, 0 < η → ∃ ε, 0 < ε ∧ ∀ n ∈ V ε, nrm ((n : ℝ) * α) < η) ∧
        0 < nrm ((m : ℝ) * α)

private lemma sq_ne (ℓ : ℕ) (hℓ : 2 ≤ ℓ) : (sqScales ℓ).Nonempty := ⟨ℓ ^ (1 ^ 2), 1, le_rfl, rfl⟩

theorem compactQuotient_of_MAP (hMAP : PrecompactMAP) : CompactQuotientCriterion := by
  intro hS
  by_contra hJA
  have hex : ∃ δ : ℝ, 0 < δ ∧ (1 : ℤ) ∉ DiffSet (Uset 3 δ) (Uset 2 δ) := by
    by_contra hcon
    push_neg at hcon
    apply hJA
    intro δ hδ
    obtain ⟨a, ha, b, hb, hab⟩ := hcon δ hδ
    refine ⟨a, ha, ?_⟩
    have : b = a - 1 := by omega
    rw [← this]; exact hb
  obtain ⟨δ, hδ, h1⟩ := hex
  have hz3 : ∀ ε : ℝ, 0 < ε → (0 : ℤ) ∈ Uset 3 ε := by
    intro ε hε; show Pn (sqScales 3) 0 < ε; rw [Pn_zero]; exact hε
  have hz2 : ∀ ε : ℝ, 0 < ε → (0 : ℤ) ∈ Uset 2 ε := by
    intro ε hε; show Pn (sqScales 2) 0 < ε; rw [Pn_zero]; exact hε
  obtain ⟨α, hcont, hpos⟩ := hMAP (fun ε => DiffSet (Uset 3 ε) (Uset 2 ε))
    (fun ε hε => ⟨0, hz3 ε hε, 0, hz2 ε hε, by simp⟩)
    (by
      intro ε hε m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := hm
      refine ⟨-a, ?_, -b, ?_, by ring⟩
      · show Pn (sqScales 3) (-a) < ε; rw [Pn_neg]; exact ha
      · show Pn (sqScales 2) (-b) < ε; rw [Pn_neg]; exact hb)
    (by
      intro ε ε' _ hεε' m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := hm
      exact ⟨a, lt_of_lt_of_le ha hεε', b, lt_of_lt_of_le hb hεε', rfl⟩)
    (by
      intro ε hε
      refine ⟨ε / 2, by positivity, ?_⟩
      intro x hx y hy
      obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
      obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
      refine ⟨a₁ + a₂, ?_, b₁ + b₂, ?_, by ring⟩
      · show Pn (sqScales 3) (a₁ + a₂) < ε
        have h := Pn_add_le (sq_ne 3 (by norm_num)) a₁ a₂
        have h1' : Pn (sqScales 3) a₁ < ε / 2 := ha₁
        have h2' : Pn (sqScales 3) a₂ < ε / 2 := ha₂
        linarith
      · show Pn (sqScales 2) (b₁ + b₂) < ε
        have h := Pn_add_le (sq_ne 2 le_rfl) b₁ b₂
        have h1' : Pn (sqScales 2) b₁ < ε / 2 := hb₁
        have h2' : Pn (sqScales 2) b₂ < ε / 2 := hb₂
        linarith)
    (fun ε hε => hS ε hε) 1 ⟨δ, hδ, h1⟩
  obtain ⟨ε, hε, hε'⟩ := hcont (1 / 4) (by norm_num)
  have h₃ : ∀ k : ℤ, Pn (sqScales 3) k < ε → nrm ((k : ℝ) * α) < 1 / 4 := by
    intro k hk
    exact hε' k ⟨k, hk, 0, hz2 ε hε, by ring⟩
  have h₂ : ∀ k : ℤ, Pn (sqScales 2) k < ε → nrm ((k : ℝ) * α) < 1 / 4 := by
    intro k hk
    have := hε' (-k) ⟨0, hz3 ε hε, k, hk, by ring⟩
    have e : ((-k : ℤ) : ℝ) * α = -((k : ℝ) * α) := by push_cast; ring
    rw [e, nrm_neg] at this
    exact this
  obtain ⟨z, hz⟩ := JAOnePrime.oneprime_two_three α ε ε hε hε h₂ h₃
  rw [hz] at hpos
  have : ((1 : ℤ) : ℝ) * (z : ℝ) = ((z : ℤ) : ℝ) := by simp
  rw [this, nrm_int] at hpos
  exact lt_irrefl _ hpos

/-- **Joint approximation from Matveev's two-term separation and Weil's theorem for `ℤ`.** -/
theorem JA_of_matveev_and_MAP (hMAP : PrecompactMAP) (A : ℝ) (hA : 0 ≤ A)
    (hP : JAClose.TwoTermSeparation A) : JAProp :=
  JAMain.JA_of_inputs (compactQuotient_of_MAP hMAP) A hA hP

#print axioms compactQuotient_of_MAP
#print axioms JA_of_matveev_and_MAP

end JACompact
end LeanCheck
