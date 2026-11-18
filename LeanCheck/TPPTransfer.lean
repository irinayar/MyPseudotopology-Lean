import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# ThreePrimePlus: the pigeonhole transference lemma and the exclusion inequality

For a positive integer vector `z = (z0, z1, z2)` and integers `M`, `Z` with `z_i ≤ Z` and `3 M Z + 1 < (M+1)^3`, there is a nonzero integer
vector `h` with `|h_i| ≤ M` and `h · z = 0` (`exists_orthogonal`).  If `z = (n, m, l)` approximates `n (1, α, β)` within `δ`, then
`n |h0 + h1 α + h2 β| ≤ (|h1| + |h2|) δ` (`hv_bound`).  Combining with a lower bound `c ≤ |h·v| M²` (the exponent-2 hypothesis for `‖h‖ ≤ M`)
gives `c n ≤ 2 M³ δ` (`delta_lower`): the quantitative form of the exclusion of close triples used in Section "An exhaustive range ..." of ThreePrimePlus.
-/

namespace TPP

open Finset

/-- Pigeonhole: a nonzero integer vector of sup-norm at most `M` orthogonal to `z`. -/
theorem exists_orthogonal (z0 z1 z2 Z M : ℕ) (h0 : z0 ≤ Z) (h1 : z1 ≤ Z) (h2 : z2 ≤ Z)
    (hM : 3 * M * Z + 1 < (M + 1) ^ 3) :
    ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ |a| ≤ M ∧ |b| ≤ M ∧ |c| ≤ M ∧
      a * z0 + b * z1 + c * z2 = 0 := by
  let s : Finset (ℕ × ℕ × ℕ) := range (M + 1) ×ˢ range (M + 1) ×ˢ range (M + 1)
  let t : Finset ℕ := range (3 * M * Z + 1)
  let f : ℕ × ℕ × ℕ → ℕ := fun x => x.1 * z0 + x.2.1 * z1 + x.2.2 * z2
  have hcard : t.card < s.card := by
    simp only [s, t, card_product, card_range]
    nlinarith [hM]
  have hmaps : ∀ x ∈ s, f x ∈ t := by
    intro x hx
    simp only [s, mem_product, mem_range] at hx
    simp only [t, mem_range]
    obtain ⟨hx1, hx2, hx3⟩ := hx
    have e1 : x.1 * z0 ≤ M * Z := Nat.mul_le_mul (by omega) h0
    have e2 : x.2.1 * z1 ≤ M * Z := Nat.mul_le_mul (by omega) h1
    have e3 : x.2.2 * z2 ≤ M * Z := Nat.mul_le_mul (by omega) h2
    simp only [f]
    have e4 : 3 * M * Z = 3 * (M * Z) := by ring
    omega
  obtain ⟨x, hx, y, hy, hxy, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  simp only [s, mem_product, mem_range] at hx hy
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨(x.1 : ℤ) - y.1, (x.2.1 : ℤ) - y.2.1, (x.2.2 : ℤ) - y.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨c1, c2, c3⟩ := hcon
    apply hxy
    have e1 : x.1 = y.1 := by omega
    have e2 : x.2.1 = y.2.1 := by omega
    have e3 : x.2.2 = y.2.2 := by omega
    exact Prod.ext e1 (Prod.ext e2 e3)
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega
  · simp only [f] at hf
    have : ((x.1 * z0 + x.2.1 * z1 + x.2.2 * z2 : ℕ) : ℤ) = ((y.1 * z0 + y.2.1 * z1 + y.2.2 * z2 : ℕ) : ℤ) := by
      rw [hf]
    push_cast at this
    linarith

/-- `h · z = 0` and `z ≈ n v` give `n |h · v| ≤ (|h1| + |h2|) δ`. -/
theorem hv_bound (α β δ : ℝ) (n m l a b c : ℤ) (hz : a * n + b * m + c * l = 0)
    (hm : |(m : ℝ) - α * n| ≤ δ) (hl : |(l : ℝ) - β * n| ≤ δ) :
    |(n : ℝ)| * |(a : ℝ) + b * α + c * β| ≤ (|(b : ℝ)| + |(c : ℝ)|) * δ := by
  have hz' : (a : ℝ) * n + b * m + c * l = 0 := by exact_mod_cast hz
  have key : (n : ℝ) * ((a : ℝ) + b * α + c * β) = -((b : ℝ) * (m - α * n)) - (c : ℝ) * (l - β * n) := by
    linarith
  rw [← abs_mul, key]
  calc |-((b : ℝ) * (m - α * n)) - (c : ℝ) * (l - β * n)|
      ≤ |-((b : ℝ) * (m - α * n))| + |(c : ℝ) * (l - β * n)| := abs_sub _ _
    _ = |(b : ℝ)| * |(m : ℝ) - α * n| + |(c : ℝ)| * |(l : ℝ) - β * n| := by
        rw [abs_neg, abs_mul, abs_mul]
    _ ≤ |(b : ℝ)| * δ + |(c : ℝ)| * δ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hm (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left hl (abs_nonneg _)
    _ = (|(b : ℝ)| + |(c : ℝ)|) * δ := by ring

/-- The exclusion inequality: if `h ≠ 0`, `|h_i| ≤ M`, `h · z = 0`, and the exponent-2 bound `c ≤ |h · v| M²` holds for `h`,
then `c n ≤ 2 M³ δ`. -/
theorem delta_lower (α β δ c : ℝ) (n m l a b d : ℤ) (M : ℕ) (hn : 0 < n)
    (hb : |b| ≤ M) (hd : |d| ≤ M) (hz : a * n + b * m + d * l = 0)
    (hm : |(m : ℝ) - α * n| ≤ δ) (hl : |(l : ℝ) - β * n| ≤ δ)
    (hc : c ≤ |(a : ℝ) + b * α + d * β| * (M : ℝ) ^ 2) :
    c * n ≤ 2 * (M : ℝ) ^ 3 * δ := by
  have h1 := hv_bound α β δ n m l a b d hz hm hl
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_of_pos hnpos] at h1
  have hbM : |(b : ℝ)| ≤ M := by exact_mod_cast hb
  have hdM : |(d : ℝ)| ≤ M := by exact_mod_cast hd
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hm
  have h2 : (|(b : ℝ)| + |(d : ℝ)|) * δ ≤ 2 * (M : ℝ) * δ := by
    apply mul_le_mul_of_nonneg_right _ hδ
    linarith
  have hM2 : 0 ≤ (M : ℝ) ^ 2 := sq_nonneg _
  calc c * n ≤ (|(a : ℝ) + b * α + d * β| * (M : ℝ) ^ 2) * n :=
        mul_le_mul_of_nonneg_right hc hnpos.le
    _ = ((n : ℝ) * |(a : ℝ) + b * α + d * β|) * (M : ℝ) ^ 2 := by ring
    _ ≤ (2 * (M : ℝ) * δ) * (M : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hM2
        linarith
    _ = 2 * (M : ℝ) ^ 3 * δ := by ring

end TPP
