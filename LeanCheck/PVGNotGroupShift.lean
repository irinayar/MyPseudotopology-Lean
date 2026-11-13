import Mathlib
import LeanCheck.PVGSequences
import LeanCheck.PVGLacCount

/-!
# PVG: shifts of free ultrafilters (used in Lemma 8.78 of PVG_v34; Lean check)

Scope. For an ultrafilter `Z` on `ℕ` and `d ∈ ℕ`, `shiftU d Z` is the image of `Z` under `n ↦ n - d`.

* `shiftU_free` : the shift of a free ultrafilter is free;
* `shiftU_ne` : a free ultrafilter is not fixed by a shift `d ≥ 1` (the parity argument of the article: `⌊n/d⌋` even or odd);
* `shiftU_inj` : for a free ultrafilter `Z`, `shiftU k Z ≠ shiftU l Z` when `k ≠ l`;
* `tendsto_e_comp` : `e(s_{g x})` converges along an ultrafilter `V` to `L_s(V.map g)`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Q95

/-- The shift of an ultrafilter on `ℕ`: the image under `n ↦ n - d`. -/
def shiftU (d : ℕ) (Z : Ultrafilter ℕ) : Ultrafilter ℕ := Z.map (fun n => n - d)

lemma shiftU_free {Z : Ultrafilter ℕ} (hZ : Free Z) (d : ℕ) : Free (shiftU d Z) := by
  unfold Free shiftU
  rw [Ultrafilter.coe_map]
  intro s hs
  rw [Filter.mem_map]
  have hfin : sᶜ.Finite := Filter.mem_cofinite.1 hs
  obtain ⟨B, hB⟩ := hfin.bddAbove
  have hsub : ((fun n : ℕ => n - d) ⁻¹' s)ᶜ ⊆ Set.Iic (B + d) := by
    intro n hn
    have : n - d ∈ sᶜ := hn
    have := hB this
    simp only [Set.mem_Iic]
    omega
  have : ((fun n : ℕ => n - d) ⁻¹' s)ᶜ.Finite := (Set.finite_Iic _).subset hsub
  exact hZ (Filter.mem_cofinite.2 this)

lemma shiftU_comp (d e' : ℕ) (Z : Ultrafilter ℕ) : shiftU d (shiftU e' Z) = shiftU (e' + d) Z := by
  unfold shiftU
  rw [Ultrafilter.map_map]
  congr 1
  funext n
  simp only [Function.comp]
  omega

/-- A free ultrafilter is not fixed by a nonzero shift. -/
lemma shiftU_ne {Z : Ultrafilter ℕ} (hZ : Free Z) {d : ℕ} (hd : 1 ≤ d) : shiftU d Z ≠ Z := by
  intro hfix
  set A : ℕ → Set ℕ := fun j => {n | d < n ∧ (n / d) % 2 = j} with hA
  have hIic : Set.Iic d ∉ (Z : Filter ℕ) := by
    intro h
    have hc : (Set.Iic d)ᶜ ∈ (Z : Filter ℕ) := hZ (Filter.mem_cofinite.2 (by simpa using Set.finite_Iic d))
    exact (Ultrafilter.compl_mem_iff_notMem.1 hc) h
  have hunion : A 0 ∪ A 1 ∪ Set.Iic d = Set.univ := by
    ext n
    simp only [hA, Set.mem_union, Set.mem_setOf_eq, Set.mem_Iic, Set.mem_univ, iff_true]
    by_cases h : n ≤ d
    · exact Or.inr h
    · left
      have : (n / d) % 2 = 0 ∨ (n / d) % 2 = 1 := by omega
      rcases this with h0 | h1
      · exact Or.inl ⟨by omega, h0⟩
      · exact Or.inr ⟨by omega, h1⟩
  have hmem : A 0 ∪ A 1 ∪ Set.Iic d ∈ (Z : Filter ℕ) := by rw [hunion]; exact Filter.univ_mem
  obtain ⟨j, hj⟩ : ∃ j, j ≤ 1 ∧ A j ∈ (Z : Filter ℕ) := by
    rcases (Ultrafilter.union_mem_iff).1 hmem with h | h
    · rcases (Ultrafilter.union_mem_iff).1 h with h0 | h1
      · exact ⟨0, by norm_num, h0⟩
      · exact ⟨1, le_rfl, h1⟩
    · exact absurd h hIic
  obtain ⟨hj1, hAj⟩ := hj
  have h2 : A j ∈ ((shiftU d Z : Ultrafilter ℕ) : Filter ℕ) := by rw [hfix]; exact hAj
  unfold shiftU at h2
  rw [Ultrafilter.coe_map, Filter.mem_map] at h2
  have hdisj : (fun n : ℕ => n - d) ⁻¹' A j ∩ A j = ∅ := by
    ext n
    simp only [hA, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨⟨h1, h2'⟩, h3, h4⟩
    have h5 : n / d = (n - d) / d + 1 := by
      have : n = (n - d) + d := by omega
      conv_lhs => rw [this]
      exact Nat.add_div_right _ (by omega)
    omega
  exact Z.empty_notMem (by rw [← hdisj]; exact Filter.inter_mem h2 hAj)

lemma shiftU_inj {Z : Ultrafilter ℕ} (hZ : Free Z) {k l : ℕ} (hkl : k ≠ l) :
    shiftU k Z ≠ shiftU l Z := by
  intro h
  rcases Nat.lt_or_gt_of_ne hkl with hlt | hlt
  · obtain ⟨d, rfl⟩ : ∃ d, l = k + d := ⟨l - k, by omega⟩
    have h1 : shiftU d (shiftU k Z) = shiftU (k + d) Z := shiftU_comp d k Z
    rw [← h] at h1
    exact shiftU_ne (shiftU_free hZ k) (by omega) h1
  · obtain ⟨d, rfl⟩ : ∃ d, k = l + d := ⟨k - l, by omega⟩
    have h1 : shiftU d (shiftU l Z) = shiftU (l + d) Z := shiftU_comp d l Z
    rw [h] at h1
    exact shiftU_ne (shiftU_free hZ l) (by omega) h1

/-- `e(s_{g x})` converges along `V` to `L_s` of the image ultrafilter. -/
lemma tendsto_e_comp {ι : Type*} (y : ℕ → ℝ) (V : Ultrafilter ι) (g : ι → ℕ) :
    Tendsto (fun q => e (y (g q))) V (𝓝 (L y (V.map g))) := by
  have h := tendsto_L y (V.map g)
  have h2 : Tendsto g (V : Filter ι) ((V.map g : Ultrafilter ℕ) : Filter ℕ) := by
    rw [Ultrafilter.coe_map]; exact Filter.tendsto_map
  exact h.comp h2

end Q95
end PVG
