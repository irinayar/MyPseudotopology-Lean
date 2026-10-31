import Mathlib

/-!
# Energy to difference-set size to disjoint translates (components of the JA proof)

Checked here, with all hypotheses explicit (no axiom, no `sorry`):

* `sum_rep`: for finite sets `A, B ⊆ ℤ` and weights `f, g`, the weighted representation function
  `rep d = ∑_{a-b=d} f a * g b` sums over any finite set `T` containing all differences to the product
  of the weight totals.
* `cs_difference`: the weighted Cauchy-Schwarz inequality
  `((∑ f)(∑ g))^2 ≤ |T| * ∑_d rep(d)^2`.  With `f = g = 1` this is `|A|^2 |B|^2 ≤ |A-B| * E(A,B)`;
  with a bound on the energy it is the step "weighted Cauchy-Schwarz gives `|V_X| ≥ c_D (2X+1)`".
* `cs_difference_interval`: the same with `T = [-X, X]`, `|T| = 2X+1`.
* `disjoint_translates_of_not_mem`: if two shifts differ by an element outside `V - V`, the two
  translates of `V` are disjoint.
* `packing_card_le`: pairwise disjoint translates of `V` inside a finite set `I` satisfy
  `|F| * |V| ≤ |I|`.

Not checked here: the energy bound itself (the normalized product argument), the choice of the
weights, the Matveev lower bound, the spectral window, and the compact-quotient deduction.
-/

namespace LeanCheck
namespace JAEnergy

open Finset

/-- Weighted representation function of the difference `a - b`. -/
noncomputable def rep (A B : Finset ℤ) (f g : ℤ → ℝ) (d : ℤ) : ℝ :=
  ∑ p ∈ (A ×ˢ B).filter (fun p => p.1 - p.2 = d), f p.1 * g p.2

theorem sum_rep (A B : Finset ℤ) (f g : ℤ → ℝ) (T : Finset ℤ)
    (hT : ∀ a ∈ A, ∀ b ∈ B, a - b ∈ T) :
    ∑ d ∈ T, rep A B f g d = (∑ a ∈ A, f a) * (∑ b ∈ B, g b) := by
  unfold rep
  have hmaps : ∀ p ∈ A ×ˢ B, (fun p : ℤ × ℤ => p.1 - p.2) p ∈ T := by
    intro p hp
    rw [Finset.mem_product] at hp
    exact hT p.1 hp.1 p.2 hp.2
  rw [Finset.sum_fiberwise_of_maps_to (s := A ×ˢ B) (t := T)
      (g := fun p : ℤ × ℤ => p.1 - p.2) hmaps (fun p => f p.1 * g p.2)]
  rw [Finset.sum_product, Finset.sum_mul_sum]

theorem cs_difference (A B : Finset ℤ) (f g : ℤ → ℝ) (T : Finset ℤ)
    (hT : ∀ a ∈ A, ∀ b ∈ B, a - b ∈ T) :
    ((∑ a ∈ A, f a) * (∑ b ∈ B, g b)) ^ 2 ≤ (T.card : ℝ) * ∑ d ∈ T, (rep A B f g d) ^ 2 := by
  rw [← sum_rep A B f g T hT]
  have h := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) (fun d => rep A B f g d)
  simpa using h

/-- Difference sets inside `[-X, X]`: `T = Icc (-X) X` has `2X+1` elements. -/
theorem cs_difference_interval (X : ℕ) (A B : Finset ℤ) (f g : ℤ → ℝ)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a ≤ X) (hB : ∀ b ∈ B, 0 ≤ b ∧ b ≤ X) :
    ((∑ a ∈ A, f a) * (∑ b ∈ B, g b)) ^ 2 ≤
      (2 * (X : ℝ) + 1) * ∑ d ∈ Finset.Icc (-(X : ℤ)) X, (rep A B f g d) ^ 2 := by
  have hT : ∀ a ∈ A, ∀ b ∈ B, a - b ∈ Finset.Icc (-(X : ℤ)) X := by
    intro a ha b hb
    rw [Finset.mem_Icc]
    have := hA a ha; have := hB b hb
    constructor <;> omega
  have h := cs_difference A B f g (Finset.Icc (-(X : ℤ)) X) hT
  have hc : ((Finset.Icc (-(X : ℤ)) X).card : ℝ) = 2 * (X : ℝ) + 1 := by
    rw [Int.card_Icc]
    have : (X : ℤ) + 1 - -(X : ℤ) = 2 * (X : ℤ) + 1 := by ring
    rw [this]
    have h2 : (2 * (X : ℤ) + 1).toNat = 2 * X + 1 := by omega
    rw [h2]; push_cast; ring
  rwa [hc] at h

/-- The unweighted case: `|A|^2 |B|^2 ≤ |T| * E` where `E = ∑ r(d)^2` is the additive energy. -/
theorem card_sq_le_card_mul_energy (A B : Finset ℤ) (T : Finset ℤ)
    (hT : ∀ a ∈ A, ∀ b ∈ B, a - b ∈ T) :
    ((A.card : ℝ) * B.card) ^ 2 ≤
      (T.card : ℝ) * ∑ d ∈ T, (rep A B (fun _ => 1) (fun _ => 1) d) ^ 2 := by
  have h := cs_difference A B (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) T hT
  simpa using h

/-- Two translates of `V` by shifts whose difference is not in `V - V` are disjoint. -/
theorem disjoint_translates_of_not_mem (V : Finset ℤ) (f f' : ℤ)
    (h : ∀ v ∈ V, ∀ v' ∈ V, f - f' ≠ v' - v) :
    Disjoint (V.image (fun v => v + f)) (V.image (fun v => v + f')) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_image] at hx hx'
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨v', hv', hvv⟩ := hx'
  exact h v hv v' hv' (by omega)

/-- Pairwise disjoint translates of `V` contained in `I` satisfy `|F| |V| ≤ |I|`. -/
theorem packing_card_le (V F I : Finset ℤ)
    (hdisj : ∀ f ∈ F, ∀ f' ∈ F, f ≠ f' →
      Disjoint (V.image (fun v => v + f)) (V.image (fun v => v + f')))
    (hsub : ∀ f ∈ F, V.image (fun v => v + f) ⊆ I) :
    F.card * V.card ≤ I.card := by
  have hpw : (F : Set ℤ).PairwiseDisjoint (fun f => V.image (fun v => v + f)) := by
    intro f hf f' hf' hne
    exact hdisj f hf f' hf' hne
  have hcard : (F.biUnion (fun f => V.image (fun v => v + f))).card
      = ∑ f ∈ F, (V.image (fun v => v + f)).card := Finset.card_biUnion hpw
  have hinj : ∀ f : ℤ, (V.image (fun v => v + f)).card = V.card := by
    intro f
    exact Finset.card_image_of_injective _ (add_left_injective f)
  have hsubU : F.biUnion (fun f => V.image (fun v => v + f)) ⊆ I := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨f, hf, hx⟩ := hx
    exact hsub f hf hx
  have := Finset.card_le_card hsubU
  rw [hcard] at this
  simp only [hinj, Finset.sum_const, smul_eq_mul] at this
  exact this

#print axioms sum_rep
#print axioms cs_difference
#print axioms cs_difference_interval
#print axioms card_sq_le_card_mul_energy
#print axioms disjoint_translates_of_not_mem
#print axioms packing_card_le

end JAEnergy
end LeanCheck
