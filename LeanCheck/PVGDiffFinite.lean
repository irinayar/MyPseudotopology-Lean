import Mathlib
import LeanCheck.PVGLacCount
import LeanCheck.PVGLacIdeal

/-!
# PVG: the set `E_r = {r (s_n - s_l) : n > l ≥ 1}` meets every piece with coefficients outside `r` in a finite set (Lean check)

Scope. Lemma AS1 of the research note (Addendum AS; used there to show that the topologies `γ_{A + Zr}` are strictly coarser than `γ_A`).
With `s_n = 2^(n^2)` (`sS n`), `S = {0} ∪ {±s_n}` (`Sset`), and a piece `J ⊆ [-m, m] + b₁ S + … + b_k S` (`sumSet l`):

* `Er_pairs_finite` : if neither `r` nor `-r` is a signed subset sum of the coefficients `l` (`Cset l`), then only finitely many pairs `(n, l')` with
  `1 ≤ l' < n` satisfy `r (s_n - s_l') ∈ [-m, m] + b₁ S + … + b_k S`;
* `Er_inter_finite_of_sub` : hence `J ∩ E_r` is finite for every `J ⊆ [-m, m] + sumSet l`;
* `Er_inter_finite_of_subgroup` : the same for coefficients in an additive subgroup `A` of `ℝ` that does not contain `r` (Lemma AS1);
* `Er_inter_IS_finite` : the same for every member of the lacunary ideal `I_S` whose coefficient list avoids `±r`.

The proof follows the largest-index argument of the note: if `r (s_n - s_l') = t + ∑ d_j s_j` with `d_j` signed subset sums, the integer-weighted sum
`∑ D_j s_j = t` has `D_n = r - d_n ≠ 0` and all other nonzero `D_j` bounded away from `0`, so by the lower bound `lower_bound` the top index is bounded.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Pointwise
open scoped Classical

namespace PVG
namespace Lac

/-- `E_r = {r (s_n - s_l) : 1 ≤ l < n}`. -/
def Er (r : ℝ) : Set ℝ := {x | ∃ n l : ℕ, 1 ≤ l ∧ l < n ∧ x = r * (sS n - sS l)}

lemma sS_ge (n : ℕ) : (n : ℝ) ≤ sS n := by
  unfold sS
  have h1 : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  have h2 : (2 : ℝ) ^ n ≤ 2 ^ (n ^ 2) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_self_pow (by norm_num) n)
  linarith

lemma sum_ite_sS (N n : ℕ) (c : ℝ) (hn : n < N) :
    ∑ j ∈ Finset.range N, (if j = n then c else 0) * sS j = c * sS n := by
  have : ∀ j ∈ Finset.range N, (if j = n then c else 0) * sS j = if j = n then c * sS n else 0 := by
    intro j _; split_ifs with h
    · rw [h]
    · simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  simp [hn]

theorem Er_pairs_finite (l : List ℝ) (r : ℝ) (hr : r ∉ Cset l) (hr' : -r ∉ Cset l) (m : ℝ) :
    {p : ℕ × ℕ | 1 ≤ p.2 ∧ p.2 < p.1 ∧
      ∃ t ∈ Icc (-m) m, ∃ w ∈ sumSet l, r * (sS p.1 - sS p.2) = t + w}.Finite := by
  set Dset : Finset ℝ := (Cset l).image (fun d => -d) ∪ (Cset l).image (fun d => r - d) ∪
    (Cset l).image (fun d => -r - d) with hDset
  obtain ⟨c0, c1, hc0, hc1, hlow, hup⟩ := exists_consts Dset
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (4 * c1 / c0) (by norm_num : (1 : ℝ) < 2)
  set N0 : ℕ := n1 + 1 with hN0
  have hN0big : ∀ T, N0 ≤ T → 4 * c1 ≤ c0 * 2 ^ (2 * T - 1) := by
    intro T hT
    have h1 : (2 : ℝ) ^ n1 ≤ 2 ^ (2 * T - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_lt_iff₀ hc0] at hn1
    nlinarith
  set B : ℕ := max N0 (⌈2 * m / c0⌉₊) + 1 with hB
  refine Set.Finite.subset (Finset.finite_toSet (Finset.range B ×ˢ Finset.range B)) ?_
  rintro ⟨n, l'⟩ ⟨hl1, hln, t, ht, w, hw, hEq⟩
  dsimp only at hl1 hln hEq
  suffices hn : n < B by
    exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_range.2 hn, Finset.mem_range.2 (lt_trans hln hn)⟩)
  obtain ⟨N, d, hd, hd0, hw'⟩ := rep_of_mem_sumSet l w hw
  set N' : ℕ := max N (n + 1) with hN'
  have hnN' : n < N' := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
  have hlN' : l' < N' := lt_trans hln hnN'
  have hNN' : N ≤ N' := le_max_left _ _
  set D : ℕ → ℝ := fun j => (if j = n then r else 0) + (if j = l' then -r else 0) - d j with hD
  have hDmem : ∀ j, D j ∈ Dset := by
    intro j
    simp only [hD, hDset, Finset.mem_union, Finset.mem_image]
    by_cases h1 : j = n
    · have h2 : j ≠ l' := by omega
      left; right
      exact ⟨d j, hd j, by rw [if_pos h1, if_neg h2]; ring⟩
    · by_cases h2 : j = l'
      · right
        exact ⟨d j, hd j, by rw [if_neg h1, if_pos h2]; ring⟩
      · left; left
        exact ⟨d j, hd j, by rw [if_neg h1, if_neg h2]; ring⟩
  have hdD : ∀ j, D j = 0 ∨ (c0 ≤ |D j| ∧ |D j| ≤ c1) := by
    intro j
    by_cases h : D j = 0
    · exact Or.inl h
    · exact Or.inr ⟨hlow _ (hDmem j) h, hup _ (hDmem j)⟩
  have hDn : D n ≠ 0 := by
    intro h
    have h2 : n ≠ l' := by omega
    have : r = d n := by
      simp [hD, h2] at h
      linarith
    exact hr (this ▸ hd n)
  have hDzero : ∀ j, N' ≤ j → D j = 0 := by
    intro j hj
    have h1 : j ≠ n := by omega
    have h2 : j ≠ l' := by omega
    have h3 : N ≤ j := le_trans hNN' hj
    simp [hD, h1, h2, hd0 j h3]
  have hdsum : ∑ j ∈ Finset.range N', d j * sS j = w := by
    rw [hw']
    have hle : N ≤ N' := hNN'
    rw [← Finset.sum_range_add_sum_Ico _ hle]
    have : ∑ j ∈ Finset.Ico N N', d j * sS j = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [hd0 j (Finset.mem_Ico.1 hj).1]; simp)
    rw [this, add_zero]
  have hsum : ∑ j ∈ Finset.range N', D j * sS j = t := by
    have e : ∀ j, D j * sS j = (if j = n then r else 0) * sS j + (if j = l' then -r else 0) * sS j - d j * sS j := by
      intro j; simp only [hD]; ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [sum_ite_sS N' n r hnN', sum_ite_sS N' l' (-r) hlN', hdsum]
    linarith [hEq]
  -- the top nonzero index
  set S : Finset ℕ := (Finset.range N').filter (fun j => D j ≠ 0) with hS
  have hnS : n ∈ S := by simp [hS, hnN', hDn]
  have hSne : S.Nonempty := ⟨n, hnS⟩
  set T : ℕ := S.max' hSne with hT
  have hTS : T ∈ S := S.max'_mem hSne
  have hTN' : T < N' := by simpa [hS] using (Finset.mem_filter.1 hTS).1
  have hDT : D T ≠ 0 := (Finset.mem_filter.1 hTS).2
  have hnT : n ≤ T := S.le_max' n hnS
  have hupT : ∀ j, T < j → D j = 0 := by
    intro j hj
    by_contra hne
    by_cases hjN : j < N'
    · have : j ∈ S := by simp [hS, hjN, hne]
      have := S.le_max' j this
      omega
    · exact hne (hDzero j (not_lt.1 hjN))
  rw [hB]
  by_cases hTN0 : T < N0
  · have : n < max N0 ⌈2 * m / c0⌉₊ + 1 := by
      have := le_max_left N0 ⌈2 * m / c0⌉₊
      omega
    exact this
  · have hN0T : N0 ≤ T := not_lt.1 hTN0
    have hlb := lower_bound hc0 (by linarith) N0 (by omega) hN0big D hdD T hN0T hDT hupT N' hTN'
    rw [hsum] at hlb
    have ht' : |t| ≤ m := abs_le.2 ⟨ht.1, ht.2⟩
    have h1 : c0 * sS T / 2 ≤ m := le_trans hlb ht'
    have h2 : sS T ≤ 2 * m / c0 := by
      rw [le_div_iff₀ hc0]; linarith
    have h3 : (T : ℝ) ≤ ⌈2 * m / c0⌉₊ := by
      have := sS_ge T
      exact le_trans (le_trans this h2) (Nat.le_ceil _)
    have h4 : T ≤ ⌈2 * m / c0⌉₊ := by exact_mod_cast h3
    have := le_max_right N0 ⌈2 * m / c0⌉₊
    omega

/-- `J ∩ E_r` is finite for every `J ⊆ [-m, m] + b₁ S + … + b_k S` when `±r` is not a signed subset sum of the `b_i`. -/
theorem Er_inter_finite_of_sub {l : List ℝ} {r m : ℝ} (hr : r ∉ Cset l) (hr' : -r ∉ Cset l)
    {J : Set ℝ} (hJ : J ⊆ Icc (-m) m + sumSet l) : (J ∩ Er r).Finite := by
  have hfin := Er_pairs_finite l r hr hr' m
  refine (hfin.image (fun p : ℕ × ℕ => r * (sS p.1 - sS p.2))).subset ?_
  rintro x ⟨hxJ, n, l', hl1, hln, rfl⟩
  obtain ⟨t, ht, w, hw, hsum⟩ := hJ hxJ
  exact ⟨(n, l'), ⟨hl1, hln, t, ht, w, hw, hsum.symm⟩, rfl⟩

lemma Cset_mem_subgroup (A : AddSubgroup ℝ) :
    ∀ l : List ℝ, (∀ a ∈ l, a ∈ A) → ∀ x ∈ Cset l, x ∈ A
  | [], _, x, hx => by
    simp only [Cset, Finset.mem_singleton] at hx
    rw [hx]; exact A.zero_mem
  | a :: l, h, x, hx => by
    have hl : ∀ b ∈ l, b ∈ A := fun b hb => h b (List.mem_cons_of_mem a hb)
    have ha : a ∈ A := h a List.mem_cons_self
    simp only [Cset, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with (hx | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩
    · exact Cset_mem_subgroup A l hl x hx
    · exact A.add_mem (Cset_mem_subgroup A l hl y hy) ha
    · exact A.sub_mem (Cset_mem_subgroup A l hl y hy) ha

/-- **Lemma AS1.** If `A` is an additive subgroup of `ℝ`, `r ∉ A`, and `J ⊆ [-m, m] + b₁ S + … + b_k S` with all `b_i ∈ A`, then
`J ∩ {r (s_n - s_l) : n > l ≥ 1}` is finite. -/
theorem Er_inter_finite_of_subgroup (A : AddSubgroup ℝ) {r m : ℝ} (hr : r ∉ A) {l : List ℝ}
    (hl : ∀ a ∈ l, a ∈ A) {J : Set ℝ} (hJ : J ⊆ Icc (-m) m + sumSet l) : (J ∩ Er r).Finite := by
  refine Er_inter_finite_of_sub (fun h => hr (Cset_mem_subgroup A l hl r h)) (fun h => ?_) hJ
  exact hr (by simpa using A.neg_mem (Cset_mem_subgroup A l hl (-r) h))

/-- The same for a member of the lacunary ideal `I_S` whose coefficient list avoids `±r`. -/
theorem Er_inter_IS_finite {r : ℝ} {J : Set ℝ} (hJ : J ∈ IS) :
    ∃ (m : ℝ) (l : List ℝ), J ⊆ Icc (-m) m + sumSet l ∧
      ((r ∉ Cset l ∧ -r ∉ Cset l) → (J ∩ Er r).Finite) := by
  obtain ⟨m, l, hsub⟩ := hJ
  exact ⟨m, l, hsub, fun h => Er_inter_finite_of_sub h.1 h.2 hsub⟩

end Lac
end PVG
