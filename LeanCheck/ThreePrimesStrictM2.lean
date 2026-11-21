import LeanCheck.TVGPlusCount

/-!
# ThreePrimes (version M2): strict supremum from a finite strict part and a uniform tail

For `m δ ≥ 1` (the strict case `m = 1/δ`) one needs `P_p(k) < 1/m`, not only `≤ 1/m`. The coordinates
`n ≤ R` are finitely many and each is `< c`; the tail `n > R` is uniformly `≤ B < c`. Then the
supremum over all `n` is `< c`.
-/
namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- A finite family of values `< c` has a common bound `c' < c`. -/
lemma finite_lt_bound {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ℝ) {c : ℝ}
    (h : ∀ x ∈ T, f x < c) : ∃ c' : ℝ, c' < c ∧ ∀ x ∈ T, f x ≤ c' := by
  induction T using Finset.induction_on with
  | empty => exact ⟨c - 1, by linarith, by simp⟩
  | insert a T ha ih =>
    obtain ⟨c', hc', hT⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    have hfa : f a < c := h a (Finset.mem_insert_self a T)
    refine ⟨max c' (f a), max_lt hc' hfa, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_max_right _ _
    · exact (hT x hx).trans (le_max_left _ _)

/-- Strict supremum: `n ≤ R` strictly below `c`, tail `n > R` uniformly `≤ B < c`. -/
lemma Pn_sq_lt (p : ℕ) (k : ℤ) {c B : ℝ} (R : ℕ) (hB : B < c)
    (hfin : ∀ n : ℕ, 1 ≤ n → n ≤ R → nrm ((k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) < c)
    (htail : ∀ n : ℕ, R < n → nrm ((k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) ≤ B) :
    Pn (sqScales p) k < c := by
  classical
  obtain ⟨c', hc', hT⟩ := finite_lt_bound (Finset.Icc 1 R)
    (fun n => nrm ((k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)))
    (fun n hn => hfin n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2)
  have : Pn (sqScales p) k ≤ max c' B := by
    apply Pn_le (sq_nonempty p)
    rintro q ⟨n, hn, rfl⟩
    by_cases hnr : n ≤ R
    · exact (hT n (Finset.mem_Icc.mpr ⟨hn, hnr⟩)).trans (le_max_left _ _)
    · exact (htail n (by omega)).trans (le_max_right _ _)
  exact lt_of_le_of_lt this (max_lt hc' hB)

end TVGPlus
end LeanCheck
