import Mathlib
import LeanCheck.JAAssembly
import LeanCheck.TVGPlusValuation
import LeanCheck.DD3Reduction

/-!
# Diagonal density for three primes: from the energy bound to `DD {2,3,5}` (Lean check)

Scope. Fifth piece of the Lean version of the conditional proof of `DD({2,3,5})` (research note
`TVGplus_conditional_DD235_2026-11-07.md`, items 5 to 7). It is the part of the assembly that comes *after* the energy
estimate; it is the three-prime counterpart of `JAAssembly` (`DenseDifferences`, `syndeticW_of_dense`,
`JA_of_dense_differences`) and uses the combinatorial results of `DD3Reduction`:

* `W3 r = {(x - y, y - z) : P_2(x), P_3(y), P_5(z) < r}`, `JA3Prop` (`W3 ε = ℤ²` for every `ε`: every integer target is
  attained), `SyndeticW3`, `CompactQuotientCriterion3 : SyndeticW3 → JA3Prop` (hypothesis: the compact-quotient step for `ℤ²`
  of the note, item 7);
* `DenseDifferences3 ε`: arbitrarily large finite `V ⊆ [-X,X]²` with `V - V ⊆ W3 ε` and `|V| ≥ c (2X+1)²`;
* `syndeticW3_of_dense`: dense differences at every precision give `SyndeticW3` (`syndetic_of_dense_difference3`);
* `dense_step3`: from finite sets `A, B, C ⊆ [0,X]` with self-differences small in `P_2`, `P_3`, `P_5`, weights `f, g, h`
  with nonzero total mass and three-fold collision energy at most `K (∑f ∑g ∑h)² / (2X+1)²`, a set `V` as above with
  `|V| ≥ (2X+1)²/K` (`card_V3_ge`, `sum_sq_rep3`);
* `EnergyInput3 ε`: the energy input at precision `ε` at arbitrarily large heights (what the three-weight random
  translation construction must supply); `denseDifferences3_of_energy`;
* `JA3_of_energy`: `CompactQuotientCriterion3` and `EnergyInput3` at every `ε` give `JA3Prop`;
* `DD_of_JA3`, `DD235_of_energy`: `JA3Prop S` gives `DDS S {2,3,5}` (target `(t 3 - t 2, t 5 - t 3)`, `k = z + t 5`).

Not formalized: `EnergyInput3` itself (the three-weight random translations, expected spectral measure, the Fourier step
and the selection of a realization, with `prod_f_bound3`), `CompactQuotientCriterion3`, `HTT3`, `HFin`. A Lean proof verifies
its formal statement under its hypotheses; the correspondence with the research note requires mathematical review.
-/

namespace LeanCheck
namespace DD3GenDense

open Finset MixedPrime JAAssembly

/-- Diagonal density for arbitrary families of scale sets `S p` (the original case is `S = sqScales`, `DDS_sq`). -/
def DDS (S : ℕ → Set ℕ) (P : Finset ℕ) : Prop :=
  ∀ (t : ℕ → ℤ) (ε : ℝ), 0 < ε → ∃ k : ℤ, ∀ p ∈ P, Pn (S p) (k - t p) < ε

lemma DDS_sq (P : Finset ℕ) : DDS sqScales P ↔ TVGPlus.DD P := Iff.rfl

variable (S : ℕ → Set ℕ)

/-- `W3 r = {(x - y, y - z) : x ∈ U_{2,r}, y ∈ U_{3,r}, z ∈ U_{5,r}}`. -/
def W3 (r : ℝ) : Set (ℤ × ℤ) :=
  {w | ∃ x : ℤ, Pn (S 2) x < r ∧ ∃ y : ℤ, Pn (S 3) y < r ∧ ∃ z : ℤ, Pn (S 5) z < r ∧ w = (x - y, y - z)}

/-- Every integer target is attained at every precision (`ℤ² = W3 ε`). -/
def JA3Prop : Prop := ∀ ε : ℝ, 0 < ε → ∀ w : ℤ × ℤ, w ∈ W3 S ε

/-- `W3 ε` is syndetic in `ℤ²` for every `ε > 0`. -/
def SyndeticW3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ F : Finset (ℤ × ℤ), ∀ z : ℤ × ℤ, ∃ f ∈ F, z - f ∈ W3 S ε

/-- **Hypothesis (not proved here)**: the compact-quotient step for `ℤ²` (the quotient of `X_2 × X_3 × X_5` by the closure of
the diagonal is totally bounded, hence compact, with trivial character group, hence trivial). -/
def CompactQuotientCriterion3 : Prop := SyndeticW3 S → JA3Prop S

/-- The density input at precision `ε`. -/
def DenseDifferences3 (ε : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ X : ℕ, M ≤ X ∧ ∃ V : Finset (ℤ × ℤ),
    (∀ v ∈ V, |v.1| ≤ X ∧ |v.2| ≤ X) ∧ (∀ v ∈ V, ∀ v' ∈ V, v' - v ∈ W3 S ε) ∧
    c * (2 * (X : ℝ) + 1) ^ 2 ≤ (V.card : ℝ)

theorem syndeticW3_of_dense (h : ∀ ε : ℝ, 0 < ε → DenseDifferences3 S ε) : SyndeticW3 S := by
  intro ε hε
  obtain ⟨c, hc, hV⟩ := h ε hε
  have hU : ∀ p : ℕ, ∀ x : ℤ, Pn (S p) x < ε → Pn (S p) (-x) < ε := by
    intro p x hx; rw [Pn_neg]; exact hx
  have hU0 : ∀ p : ℕ, Pn (S p) 0 < ε := by
    intro p; rw [Pn_zero]; exact hε
  have h0 : (0 : ℤ × ℤ) ∈ W3 S ε :=
    ⟨0, hU0 2, 0, hU0 3, 0, hU0 5, Prod.ext (by simp) (by simp)⟩
  have hsymm : ∀ w ∈ W3 S ε, -w ∈ W3 S ε := by
    rintro w ⟨x, hx, y, hy, z, hz, rfl⟩
    exact ⟨-x, hU 2 x hx, -y, hU 3 y hy, -z, hU 5 z hz,
      Prod.ext (by simp only [Prod.fst_neg]; ring) (by simp only [Prod.snd_neg]; ring)⟩
  exact DD3.syndetic_of_dense_difference3 (W3 S ε) h0 hsymm c hc hV

/-- **One height.** Large three-fold collision-energy bound gives a large set `V` with `V - V ⊆ W3 ε`. -/
theorem dense_step3 (ε : ℝ) (X : ℕ) (A B C : Finset ℤ) (f g h : ℤ → ℝ) (K : ℝ) (hK : 0 < K)
    (hA : ∀ a ∈ A, 0 ≤ a ∧ a ≤ X) (hB : ∀ a ∈ B, 0 ≤ a ∧ a ≤ X) (hC : ∀ a ∈ C, 0 ≤ a ∧ a ≤ X)
    (hdA : ∀ a ∈ A, ∀ a' ∈ A, Pn (S 2) (a - a') < ε)
    (hdB : ∀ a ∈ B, ∀ a' ∈ B, Pn (S 3) (a - a') < ε)
    (hdC : ∀ a ∈ C, ∀ a' ∈ C, Pn (S 5) (a - a') < ε)
    (hM : (∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C, h c) ≠ 0)
    (hE : ∑ p ∈ A ×ˢ (B ×ˢ C), ∑ q ∈ A ×ˢ (B ×ˢ C),
        (if DD3.phi p = DD3.phi q then DD3.wt f g h p * DD3.wt f g h q else 0) ≤
      K * ((∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C, h c)) ^ 2 / (2 * (X : ℝ) + 1) ^ 2) :
    ∃ V : Finset (ℤ × ℤ), (∀ v ∈ V, |v.1| ≤ X ∧ |v.2| ≤ X) ∧
      (∀ v ∈ V, ∀ v' ∈ V, v' - v ∈ W3 S ε) ∧ (2 * (X : ℝ) + 1) ^ 2 / K ≤ (V.card : ℝ) := by
  classical
  set V : Finset (ℤ × ℤ) := (A ×ˢ (B ×ˢ C)).image DD3.phi with hV
  have hT : ∀ p ∈ A ×ˢ (B ×ˢ C), DD3.phi p ∈ V := fun p hp => Finset.mem_image_of_mem _ hp
  refine ⟨V, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hx, hyz⟩ := Finset.mem_product.mp hp
    obtain ⟨hy, hz⟩ := Finset.mem_product.mp hyz
    have h1 := hA _ hx
    have h2 := hB _ hy
    have h3 := hC _ hz
    simp only [DD3.phi]
    constructor <;> apply abs_le.mpr <;> constructor <;> omega
  · intro v hv v' hv'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hv'
    obtain ⟨hx, hyz⟩ := Finset.mem_product.mp hp
    obtain ⟨hy, hz⟩ := Finset.mem_product.mp hyz
    obtain ⟨hx', hyz'⟩ := Finset.mem_product.mp hp'
    obtain ⟨hy', hz'⟩ := Finset.mem_product.mp hyz'
    refine ⟨p'.1 - p.1, hdA _ hx' _ hx, p'.2.1 - p.2.1, hdB _ hy' _ hy, p'.2.2 - p.2.2, hdC _ hz' _ hz, ?_⟩
    simp only [DD3.phi]
    exact Prod.ext (by simp only [Prod.fst_sub]; ring) (by simp only [Prod.snd_sub]; ring)
  · have hcs := DD3.card_V3_ge (A := A) (B := B) (C := C) f g h V hT
    have hsq := DD3.sum_sq_rep3 (A := A) (B := B) (C := C) f g h V hT
    rw [hsq] at hcs
    set M : ℝ := (∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C, h c) with hMdef
    have hM2 : 0 < M ^ 2 := by positivity
    have hX : 0 < (2 * (X : ℝ) + 1) ^ 2 := by positivity
    have h1 : M ^ 2 ≤ (V.card : ℝ) * (K * M ^ 2 / (2 * (X : ℝ) + 1) ^ 2) :=
      le_trans hcs (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _))
    have h2 : M ^ 2 * (2 * (X : ℝ) + 1) ^ 2 ≤ (V.card : ℝ) * K * M ^ 2 := by
      have h3 := mul_le_mul_of_nonneg_right h1 hX.le
      have e : (V.card : ℝ) * (K * M ^ 2 / (2 * (X : ℝ) + 1) ^ 2) * (2 * (X : ℝ) + 1) ^ 2 =
          (V.card : ℝ) * K * M ^ 2 := by field_simp
      linarith
    have h3 : M ^ 2 * (2 * (X : ℝ) + 1) ^ 2 ≤ M ^ 2 * ((V.card : ℝ) * K) := by nlinarith [h2]
    have h4 : (2 * (X : ℝ) + 1) ^ 2 ≤ (V.card : ℝ) * K := le_of_mul_le_mul_left h3 hM2
    rw [div_le_iff₀ hK]
    exact h4

/-- The energy input at precision `ε`, at arbitrarily large heights. -/
def EnergyInput3 (ε : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ M : ℕ, ∃ X : ℕ, M ≤ X ∧ ∃ (A B C : Finset ℤ) (f g h : ℤ → ℝ),
    (∀ a ∈ A, 0 ≤ a ∧ a ≤ X) ∧ (∀ a ∈ B, 0 ≤ a ∧ a ≤ X) ∧ (∀ a ∈ C, 0 ≤ a ∧ a ≤ X) ∧
    (∀ a ∈ A, ∀ a' ∈ A, Pn (S 2) (a - a') < ε) ∧
    (∀ a ∈ B, ∀ a' ∈ B, Pn (S 3) (a - a') < ε) ∧
    (∀ a ∈ C, ∀ a' ∈ C, Pn (S 5) (a - a') < ε) ∧
    (∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C, h c) ≠ 0 ∧
    ∑ p ∈ A ×ˢ (B ×ˢ C), ∑ q ∈ A ×ˢ (B ×ˢ C),
        (if DD3.phi p = DD3.phi q then DD3.wt f g h p * DD3.wt f g h q else 0) ≤
      K * ((∑ a ∈ A, f a) * (∑ b ∈ B, g b) * (∑ c ∈ C, h c)) ^ 2 / (2 * (X : ℝ) + 1) ^ 2

theorem denseDifferences3_of_energy {ε : ℝ} (h : EnergyInput3 S ε) : DenseDifferences3 S ε := by
  obtain ⟨K, hK, hall⟩ := h
  refine ⟨1 / K, by positivity, fun M => ?_⟩
  obtain ⟨X, hMX, A, B, C, f, g, h', hA, hB, hC, hdA, hdB, hdC, hM, hE⟩ := hall M
  obtain ⟨V, hV1, hV2, hV3⟩ := dense_step3 S ε X A B C f g h' K hK hA hB hC hdA hdB hdC hM hE
  refine ⟨X, hMX, V, hV1, hV2, ?_⟩
  have e : 1 / K * (2 * (X : ℝ) + 1) ^ 2 = (2 * (X : ℝ) + 1) ^ 2 / K := by ring
  rw [e]
  exact hV3

/-- **Stage A, three primes.** The energy input at every precision, with the compact-quotient step for `ℤ²`, gives `JA3Prop`. -/
theorem JA3_of_energy (hQ : CompactQuotientCriterion3 S) (h : ∀ ε : ℝ, 0 < ε → EnergyInput3 S ε) : JA3Prop S :=
  hQ (syndeticW3_of_dense S (fun ε hε => denseDifferences3_of_energy S (h ε hε)))

/-- `JA3Prop` gives the diagonal density hypothesis `DD {2,3,5}` of `TVGPlus`. -/
theorem DD_of_JA3 (hJ : JA3Prop S) : DDS S ({2, 3, 5} : Finset ℕ) := by
  intro t ε hε
  obtain ⟨x, hx, y, hy, z, hz, hw⟩ := hJ ε hε (t 3 - t 2, t 5 - t 3)
  obtain ⟨h1, h2⟩ := Prod.mk.inj hw
  refine ⟨z + t 5, ?_⟩
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · have e : z + t 5 - t 2 = x := by linarith
    rw [e]; exact hx
  · have e : z + t 5 - t 3 = y := by linarith
    rw [e]; exact hy
  · have e : z + t 5 - t 5 = z := by ring
    rw [e]; exact hz

/-- **`DD {2,3,5}` from the energy input and the compact-quotient step.** -/
theorem DD235_of_energy (hQ : CompactQuotientCriterion3 S) (h : ∀ ε : ℝ, 0 < ε → EnergyInput3 S ε) :
    DDS S ({2, 3, 5} : Finset ℕ) :=
  DD_of_JA3 S (JA3_of_energy S hQ h)

end DD3GenDense
end LeanCheck
