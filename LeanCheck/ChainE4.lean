import LeanCheck.ChainE3
import LeanCheck.ChainPW8

/-!
# Minimal precompact TVG topologies, and the absence of a least Hausdorff TVG topology
(HamelCharactersTVG_v18 Corollary 15.2 `cor:minimal`)

For a character `χ₀` of `ℝ`, `lineSub χ₀ = {a·χ₀ : a ∈ ℝ}` (with `(a·χ)(x) = χ(a x)`) is the real line through `χ₀` in the
real vector space `𝒜 = Hom(ℝ, 𝕋)`.  We prove, using the classification of precompact TVG topologies:

* `minimal_iff_line` : `θ_H` (for a separating real subspace `H`) is minimal among Hausdorff TVG topologies iff `H` is a
  real line, i.e. has real dimension one;
* `no_least_TVG`     : there is no least Hausdorff TVG topology on `ℝ`.
-/

namespace LeanCheck

open Filter Topology

section Lines

/-- The real line through `χ₀`. -/
def lineSub (χ₀ : Chars) : AddSubgroup Chars where
  carrier := {χ | ∃ a : ℝ, χ = χ₀.comp (AddMonoidHom.mulLeft a)}
  zero_mem' := ⟨0, by ext x; simp⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a + b, ?_⟩
    ext x
    simp [add_mul, map_add]
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    ext x
    simp [neg_mul, map_neg]

lemma mem_lineSub {χ₀ χ : Chars} : χ ∈ lineSub χ₀ ↔ ∃ a : ℝ, χ = χ₀.comp (AddMonoidHom.mulLeft a) := Iff.rfl

lemma lineSub_realInv (χ₀ : Chars) : RealInv (lineSub χ₀ : Set Chars) := by
  rintro _ ⟨a, rfl⟩ b
  refine ⟨b * a, ?_⟩
  ext x
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft]
  congr 1
  ring

lemma lineSub_separates {χ₀ : Chars} (h : χ₀ ≠ 0) : Separates (lineSub χ₀ : Set Chars) := by
  intro x hx
  obtain ⟨t, ht⟩ : ∃ t, χ₀ t ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h (AddMonoidHom.ext hall)
  refine ⟨χ₀.comp (AddMonoidHom.mulLeft (t / x)), ⟨t / x, rfl⟩, ?_⟩
  simpa [div_mul_cancel₀ t hx] using ht

lemma separates_ne_zero {H : AddSubgroup Chars} (h : Separates (H : Set Chars)) : ∃ χ ∈ H, χ ≠ 0 := by
  obtain ⟨χ, hχ, hne⟩ := h 1 one_ne_zero
  exact ⟨χ, hχ, fun h0 => hne (by rw [h0]; rfl)⟩

/-- **Corollary 15.2, first part.**  A Hausdorff precompact TVG topology `θ_H` is minimal among Hausdorff TVG topologies
iff `H` is a real line. -/
theorem minimal_iff_line (H : AddSubgroup Chars) (hs : Separates (H : Set Chars))
    (hr : RealInv (H : Set Chars)) :
    Maximal (· ∈ TVGcls) (theta (H : Set Chars)) ↔ ∃ χ₀ : Chars, χ₀ ≠ 0 ∧ H = lineSub χ₀ := by
  obtain ⟨hclass, hrep, hinj, hle⟩ := classification_TVG_unc
  constructor
  · intro hmax
    obtain ⟨χ₀, hχ₀H, hχ₀⟩ := separates_ne_zero hs
    refine ⟨χ₀, hχ₀, ?_⟩
    have hLH : lineSub χ₀ ≤ H := by
      rintro _ ⟨a, rfl⟩
      exact hr _ hχ₀H a
    have hLs := lineSub_separates hχ₀
    have hLr := lineSub_realInv χ₀
    have hL := hclass (lineSub χ₀) hLs hLr
    have hθ : theta (H : Set Chars) ≤ theta (lineSub χ₀ : Set Chars) := theta_mono hLH
    have hmem : theta (lineSub χ₀ : Set Chars) ∈ TVGcls := ⟨hL.1, hL.2.1, hL.2.2.2⟩
    have hback : theta (lineSub χ₀ : Set Chars) ≤ theta (H : Set Chars) := hmax.2 hmem hθ
    have heq : theta (H : Set Chars) = theta (lineSub χ₀ : Set Chars) := le_antisymm hθ hback
    exact ((hinj H (lineSub χ₀) hs hLs).1 heq)
  · rintro ⟨χ₀, hχ₀, rfl⟩
    have hP := hclass _ hs hr
    refine ⟨⟨hP.1, hP.2.1, hP.2.2.2⟩, fun τ hτ hθτ => ?_⟩
    -- `τ` is precompact, hence `τ = θ_{H'}` for a real subspace `H'`
    have hτp : Precompact τ := precompact_of_le hθτ hP.2.2.1
    have hτP : PTVG τ := ⟨hτ.1, hτ.2.1, hτp, hτ.2.2⟩
    obtain ⟨H', hs', hr', rfl⟩ := hrep τ hτP
    have hH'le : H' ≤ lineSub χ₀ := (hle H' (lineSub χ₀) hs' hs).1 hθτ
    obtain ⟨χ', hχ'H', hχ'⟩ := separates_ne_zero hs'
    obtain ⟨b, hb⟩ := hH'le hχ'H'
    have hb0 : b ≠ 0 := by
      rintro rfl
      apply hχ'
      rw [hb]; ext x; simp
    have hχ₀H' : χ₀ ∈ H' := by
      have := hr' χ' hχ'H' b⁻¹
      have e : χ'.comp (AddMonoidHom.mulLeft b⁻¹) = χ₀ := by
        rw [hb]; ext x
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft]
        rw [← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
      rwa [e] at this
    have hLH' : lineSub χ₀ ≤ H' := by
      rintro _ ⟨a, rfl⟩
      exact hr' χ₀ hχ₀H' a
    exact (hle (lineSub χ₀) H' hs hs').2 hLH'

/-- **Corollary 15.2, second part.**  There is no least (coarsest) Hausdorff TVG topology on `ℝ`. -/
theorem no_least_TVG : ¬ ∃ ν ∈ TVGcls, ∀ τ ∈ TVGcls, τ ≤ ν := by
  obtain ⟨hclass, hrep, hinj, hle⟩ := classification_TVG_unc
  obtain ⟨f, hf1⟩ := exists_coefficient
  rintro ⟨ν, hν, hgr⟩
  let χ1 : Chars := scalChar 1
  let χ2 : Chars := pfHom f 1
  have hχ1 : χ1 ≠ 0 := by
    intro h
    have := congrArg (fun m : Chars => m (1 / 2)) h
    apply half_ne_zero_circ
    simpa [χ1, scalChar_apply] using this
  have hχ2 : χ2 ≠ 0 := by
    intro h
    have e : f (1 * (1 / 2 : ℝ)) = 1 / 2 := by
      have := f_ratmul f (1 / 2 : ℚ) 1
      rw [show (1 * (1 / 2 : ℝ)) = (((1 / 2 : ℚ)) : ℝ) * 1 by push_cast; ring, this, hf1]; ring
    have h0 : (χ2 (1 / 2) : Circ) = 0 := by rw [h]; rfl
    rw [show χ2 (1 / 2) = (((f (1 * (1 / 2)) : ℚ) : ℝ) : Circ) from pfHom_apply f 1 (1 / 2), e] at h0
    apply half_ne_zero_circ
    simpa using h0
  have hA := lineSub_separates hχ1
  have hB := lineSub_separates hχ2
  have hAr := lineSub_realInv χ1
  have hBr := lineSub_realInv χ2
  have hPA := hclass (lineSub χ1) hA hAr
  have hPB := hclass (lineSub χ2) hB hBr
  have hθA : theta (lineSub χ1 : Set Chars) ≤ ν := hgr _ ⟨hPA.1, hPA.2.1, hPA.2.2.2⟩
  have hθB : theta (lineSub χ2 : Set Chars) ≤ ν := hgr _ ⟨hPB.1, hPB.2.1, hPB.2.2.2⟩
  have hνp : Precompact ν := precompact_of_le hθA hPA.2.2.1
  have hνP : PTVG ν := ⟨hν.1, hν.2.1, hνp, hν.2.2⟩
  obtain ⟨H', hs', hr', rfl⟩ := hrep ν hνP
  have h1 : H' ≤ lineSub χ1 := (hle H' (lineSub χ1) hs' hA).1 hθA
  have h2 : H' ≤ lineSub χ2 := (hle H' (lineSub χ2) hs' hB).1 hθB
  obtain ⟨χ, hχH, hχ0⟩ := separates_ne_zero hs'
  obtain ⟨a, ha⟩ := h1 hχH
  obtain ⟨b, hb⟩ := h2 hχH
  have hmix : ∀ x : ℝ, chiH f a (-b) x = 0 := by
    intro x
    have e1 := congrArg (fun m : Chars => m x) ha
    have e2 := congrArg (fun m : Chars => m x) hb
    simp only [χ1, χ2, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, scalChar_apply,
      pfHom_apply, one_mul] at e1 e2
    unfold chiH
    have : ((a * x + ((f (-b * x) : ℚ) : ℝ) : ℝ) : Circ) = ((a * x : ℝ) : Circ) - (((f (b * x) : ℚ) : ℝ) : Circ) := by
      rw [← AddCircle.coe_sub]
      congr 1
      rw [show -b * x = -(b * x) by ring, map_neg]; push_cast; ring
    rw [this, ← e1, ← e2, sub_self]
  obtain ⟨ha0, -⟩ := mixed_zero f 1 hf1 a (-b) hmix
  apply hχ0
  rw [ha]
  ext x
  simp [χ1, scalChar_apply, ha0]

end Lines

end LeanCheck
