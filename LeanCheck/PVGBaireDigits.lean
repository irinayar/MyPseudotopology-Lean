import Mathlib

/-!
# PVG: the digit set `F` is closed and nowhere dense; a countable union of its dilates is meagre (Lean check)

Scope. Step 6 of the proof of Proposition 8.88 of `PVG_v43` (Part II), in its category form. Let `‖t‖` be the distance from `t` to the
nearest integer (`dint t`, the norm of `t` in `AddCircle 1`) and
`F = { y : ‖2^(n²) y‖ ≤ 1/4 for all n ≥ 1 }` (`Fdig`). For `δ ≠ 0` let `δ⁻¹F = { a : δ a ∈ F }` (`FdigDil δ`).

* `isClosed_FdigDil` : `δ⁻¹F` is closed;
* `interior_FdigDil` : `δ⁻¹F` has empty interior for `δ ≠ 0` (hence it is nowhere dense);
* `baire_digits` : for every sequence `δ_K ≠ 0` the set of `a` with `δ_K a ∉ F` for all `K` is dense (Baire category theorem); in
  particular some `a` has `δ_K a ∉ F` for all `K`.

Not formalized here: the Lebesgue measure statement (`F` is a null set), which is the other half of Step 6 of the article.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Filter Topology

namespace PVG
namespace Lac

/-- The distance from `t` to the nearest integer, as the norm in the circle `ℝ / ℤ`. -/
noncomputable def dint (t : ℝ) : ℝ := ‖(t : AddCircle (1 : ℝ))‖

lemma continuous_dint : Continuous dint := by
  unfold dint
  exact continuous_norm.comp continuous_quotient_mk'

/-- The set `F` of the article: `‖2^(n²) y‖ ≤ 1/4` for every `n ≥ 1`. -/
def Fdig : Set ℝ := {y | ∀ n : ℕ, 1 ≤ n → dint ((2 : ℝ) ^ (n ^ 2) * y) ≤ 1 / 4}

/-- `δ⁻¹ F`. -/
def FdigDil (δ : ℝ) : Set ℝ := {a | δ * a ∈ Fdig}

lemma isClosed_Fdig : IsClosed Fdig := by
  have : Fdig = ⋂ n : ℕ, ⋂ (_ : 1 ≤ n), {y | dint ((2 : ℝ) ^ (n ^ 2) * y) ≤ 1 / 4} := by
    ext y; simp [Fdig]
  rw [this]
  refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
  exact isClosed_le (continuous_dint.comp (continuous_const.mul continuous_id)) continuous_const

lemma isClosed_FdigDil (δ : ℝ) : IsClosed (FdigDil δ) :=
  isClosed_Fdig.preimage (continuous_const.mul continuous_id)

lemma dint_half_int (k : ℤ) : dint ((k : ℝ) + 1 / 2) = 1 / 2 := by
  unfold dint
  have hk : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  have : (((k : ℝ) + 1 / 2 : ℝ) : AddCircle (1 : ℝ)) = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_add, hk, zero_add]
  rw [this]
  have h := AddCircle.norm_half_period_eq (p := (1 : ℝ))
  simpa using h

lemma two_pow_ge (n : ℕ) : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n + 1) ^ 2) := by
  have h1 : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (n + 1) ≤ 2 ^ ((n + 1) ^ 2) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h3 : n + 1 ≤ 2 ^ ((n + 1) ^ 2) := le_trans h1.le h2
  exact_mod_cast h3

theorem interior_FdigDil (δ : ℝ) (hδ : δ ≠ 0) : interior (FdigDil δ) = ∅ := by
  by_contra h
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 h
  have hnhds : interior (FdigDil δ) ∈ 𝓝 x := isOpen_interior.mem_nhds hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  have hδpos : 0 < |δ| := abs_pos.2 hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / (|δ| * r))
  set N : ℝ := (2 : ℝ) ^ ((n + 1) ^ 2) with hN
  have hNpos : 0 < N := by positivity
  have hNn : (n : ℝ) < N := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) (two_pow_ge n)
  have h4 : 4 < N * (|δ| * r) := by
    have hpos : 0 < |δ| * r := mul_pos hδpos hr
    have : 4 / (|δ| * r) < N := lt_trans hn hNn
    rwa [div_lt_iff₀ hpos] at this
  have hNδ : N * δ ≠ 0 := mul_ne_zero hNpos.ne' hδ
  set t : ℝ := N * δ * x with ht
  set k : ℤ := ⌈t⌉ with hk
  have hk1 : t ≤ k := Int.le_ceil t
  have hk2 : (k : ℝ) < t + 1 := Int.ceil_lt_add_one t
  set a : ℝ := x + ((k : ℝ) + 1 / 2 - t) / (N * δ) with ha
  have hdist : dist a x < r := by
    rw [Real.dist_eq, ha, add_sub_cancel_left, abs_div, abs_mul, abs_of_pos hNpos]
    have hnum : |(k : ℝ) + 1 / 2 - t| < 3 / 2 := by
      rw [abs_lt]; constructor <;> linarith
    rw [div_lt_iff₀ (mul_pos hNpos hδpos)]
    nlinarith
  have hamem : a ∈ FdigDil δ := interior_subset (hball hdist)
  have hval : (2 : ℝ) ^ ((n + 1) ^ 2) * (δ * a) = (k : ℝ) + 1 / 2 := by
    rw [← hN, ha, ht]
    field_simp
    ring
  have hle := hamem (n + 1) (by omega)
  rw [hval, dint_half_int] at hle
  norm_num at hle

/-- The set of `a` with `δ_K a ∉ F` for every `K` is dense (Baire category theorem). -/
theorem baire_digits (δ : ℕ → ℝ) (hδ : ∀ K, δ K ≠ 0) : Dense {a : ℝ | ∀ K, δ K * a ∉ Fdig} := by
  have : {a : ℝ | ∀ K, δ K * a ∉ Fdig} = ⋂ K, (FdigDil (δ K))ᶜ := by
    ext a; simp [FdigDil]
  rw [this]
  refine dense_iInter_of_isOpen_nat (fun K => (isClosed_FdigDil (δ K)).isOpen_compl) (fun K => ?_)
  exact interior_eq_empty_iff_dense_compl.1 (interior_FdigDil (δ K) (hδ K))

/-- In particular some real number `a` has `δ_K a ∉ F` for all `K`. -/
theorem exists_not_mem_digits (δ : ℕ → ℝ) (hδ : ∀ K, δ K ≠ 0) : ∃ a : ℝ, ∀ K, δ K * a ∉ Fdig :=
  (baire_digits δ hδ).nonempty

end Lac
end PVG
