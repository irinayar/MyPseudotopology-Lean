import Mathlib

/-!
# Elementary statements of the TwoPrimes article

* `box_sqnorm_lt`, `partial_le_sqnorm`, `coeff_expansion`, `no_point_lost`:
  the completeness statement for the lattice enumeration ("No lattice point is lost").
* `fibre_card`, `sum_sq_formula`, `parity_energy`, `parity_disjoint`:
  the near-uniform parity family which shows that the threshold 8/3 is sharp.
* `peak_sum`: the finite sum behind the resonance peak at finite size.
* `decomposition`: the exact three-term identity for `C - C_model`.
* `chain_estimate`: the approximation estimate for a general divisibility chain.

The interval arithmetic of the program `latcert` is **not** formalized.
-/

namespace TwoPrimesAppendix

open Finset

/-! ## No lattice point is lost -/

/-- A point of the open box `(-1,1)^n`, `n ≥ 1`, has squared norm below `n`. -/
theorem box_sqnorm_lt {n : ℕ} (hn : 0 < n) (v : EuclideanSpace ℝ (Fin n))
    (h : ∀ i, |v i| < 1) : ‖v‖ ^ 2 < n := by
  rw [EuclideanSpace.norm_sq_eq]
  have hlt : ∑ i : Fin n, ‖v i‖ ^ 2 < ∑ _i : Fin n, (1 : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty ?_ ?_
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    · intro i _
      rw [Real.norm_eq_abs]
      exact pow_lt_one₀ (abs_nonneg _) (h i) two_ne_zero
  simpa using hlt

/-- For pairwise orthogonal vectors, a partial sum of the squared terms is at most
the squared norm of the whole combination. -/
theorem partial_le_sqnorm {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (u : ι → E) (hu : Pairwise fun i j => inner ℝ (u i) (u j) = (0 : ℝ))
    (c : ι → ℝ) (T : Finset ι) :
    ∑ j ∈ T, c j ^ 2 * ‖u j‖ ^ 2 ≤ ‖∑ j, c j • u j‖ ^ 2 := by
  classical
  have key : ‖∑ j, c j • u j‖ ^ 2 = ∑ j, c j ^ 2 * ‖u j‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, Finset.sum_eq_single i]
    · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      ring
    · intro j _ hj
      rw [real_inner_smul_left, real_inner_smul_right, hu (Ne.symm hj)]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [key]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    fun j _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The coefficient of `w + ∑ z_i b_i` on the `j`-th Gram–Schmidt vector, for a
unitriangular expansion `b_i = b*_i + ∑_{j<i} μ_{ij} b*_j`. -/
theorem coeff_expansion {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (bs b : Fin n → E) (μ : Fin n → Fin n → ℝ) (ω z : Fin n → ℝ)
    (hb : ∀ i, b i = bs i + ∑ j ∈ univ.filter (· < i), μ i j • bs j) :
    (∑ j, ω j • bs j) + ∑ i, z i • b i
      = ∑ j, (ω j + z j + ∑ i ∈ univ.filter (j < ·), μ i j * z i) • bs j := by
  have hsum : ∑ i, z i • b i
      = (∑ j, z j • bs j) + ∑ j, (∑ i ∈ univ.filter (j < ·), μ i j * z i) • bs j := by
    simp_rw [hb, smul_add, Finset.sum_add_distrib]
    congr 1
    simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  rw [hsum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_smul, add_smul, add_assoc]

/-- **No lattice point is lost**: if `w + ∑ z_i b_i` lies in the open box, every partial
sum of the squared Gram–Schmidt terms is below `n`. -/
theorem no_point_lost {n : ℕ} (hn : 0 < n)
    (bs b : Fin n → EuclideanSpace ℝ (Fin n)) (μ : Fin n → Fin n → ℝ) (ω z : Fin n → ℝ)
    (hu : Pairwise fun i j => inner ℝ (bs i) (bs j) = (0 : ℝ))
    (hb : ∀ i, b i = bs i + ∑ j ∈ univ.filter (· < i), μ i j • bs j)
    (hbox : ∀ i, |((∑ j, ω j • bs j) + ∑ i, z i • b i) i| < 1) (T : Finset (Fin n)) :
    ∑ j ∈ T, (ω j + z j + ∑ i ∈ univ.filter (j < ·), μ i j * z i) ^ 2 * ‖bs j‖ ^ 2 < n := by
  refine lt_of_le_of_lt (partial_le_sqnorm bs hu _ T) ?_
  rw [← coeff_expansion bs b μ ω z hb]
  exact box_sqnorm_lt hn _ hbox

/-! ## The parity family -/

/-- The number of pairs `(i,j)` in `[0,m)²` with `i - j = d` is `m - |d|` (for `|d| < m`). -/
theorem fibre_card (m : ℕ) (d : ℤ) (hd : d.natAbs < m) :
    ((range m ×ˢ range m).filter (fun p => (p.1 : ℤ) - p.2 = d)).card = m - d.natAbs := by
  have : ((range m ×ˢ range m).filter (fun p => (p.1 : ℤ) - p.2 = d))
      = (range (m - d.natAbs)).image
          (fun t => if 0 ≤ d then (t + d.natAbs, t) else (t, t + d.natAbs)) := by
    ext ⟨i, j⟩
    simp only [mem_filter, mem_product, mem_range, mem_image]
    constructor
    · rintro ⟨⟨hi, hj⟩, h⟩
      by_cases h0 : 0 ≤ d
      · refine ⟨j, by omega, ?_⟩
        rw [if_pos h0, Prod.mk.injEq]; omega
      · refine ⟨i, by omega, ?_⟩
        rw [if_neg h0, Prod.mk.injEq]; omega
    · rintro ⟨t, ht, h⟩
      by_cases h0 : 0 ≤ d
      · rw [if_pos h0, Prod.mk.injEq] at h
        omega
      · rw [if_neg h0, Prod.mk.injEq] at h
        omega
  rw [this, card_image_of_injective, card_range]
  intro s t h
  by_cases h0 : 0 ≤ d
  · simp only [if_pos h0, Prod.mk.injEq] at h
    exact h.2
  · simp only [if_neg h0, Prod.mk.injEq] at h
    exact h.1

/-- `3 (m² + 2 ∑_{j<m} j²) = m (2 m² + 1)`. -/
theorem sum_sq_formula (m : ℕ) :
    3 * ((m : ℤ) ^ 2 + 2 * ∑ j ∈ range m, (j : ℤ) ^ 2) = m * (2 * (m : ℤ) ^ 2 + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination ih

/-- The energy identity of the parity family: with multiplicities `m - |d|` for `|d| < m`,
three times the sum of their squares is `m (2 m² + 1)`. -/
theorem parity_energy (m : ℕ) (hm : 0 < m) :
    3 * (((m : ℤ)) ^ 2 + 2 * ∑ k ∈ range (m - 1), ((m : ℤ) - (k + 1)) ^ 2)
      = m * (2 * (m : ℤ) ^ 2 + 1) := by
  have h : ∑ k ∈ range (m - 1), ((m : ℤ) - (k + 1)) ^ 2 = ∑ j ∈ range m, (j : ℤ) ^ 2 := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, sum_range_succ' (fun j => (j : ℤ) ^ 2)]
    rw [← sum_range_reflect (fun k => (((k + 1 : ℕ)) : ℤ) ^ 2) n]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    have : (((n - 1 - k + 1 : ℕ)) : ℤ) = (n : ℤ) - k := by omega
    rw [this]; push_cast; ring
  rw [h]
  exact sum_sq_formula m

/-- All differences of even numbers are even, so `A - B` and `A - B + 1` are disjoint. -/
theorem parity_disjoint (a b c d : ℤ) : 2 * a - 2 * b ≠ (2 * c - 2 * d) + 1 := by omega

/-! ## The resonance peak at finite size -/

/-- `3 ∑_{|k| ≤ K} (A - a|k|)(B - b|k|)`, written with the symmetric terms doubled. -/
theorem peak_sum (A B a b : ℤ) (K : ℕ) :
    3 * (A * B + 2 * ∑ k ∈ range K, (A - a * (k + 1)) * (B - b * (k + 1)))
      = 3 * (A * B * (2 * K + 1) - (b * A + a * B) * K * (K + 1))
        + a * b * K * (K + 1) * (2 * K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination ih

/-! ## The three-term decomposition -/

/-- `C - C_model` splits into the cut correction, the normalization correction and the
sampling error of the lower kernel. Here `Swc = ∑ w c`, `SwH = ∑ w H`. -/
theorem decomposition (C X R P Swc SwH : ℝ) (hX : X ≠ 0) (hR : R ≠ 0) (hP : P ≠ 0) :
    let Cmodel := 2 * X * SwH / R ^ 2
    let Cfill := (2 * X + 1) * Swc / (R * P) ^ 2
    C - Cmodel = (C - Cfill) + Cmodel / (2 * X)
      + (2 * X + 1) / R ^ 2 * (Swc / P ^ 2 - SwH) := by
  intro Cmodel Cfill
  simp only [Cmodel, Cfill]
  field_simp
  ring

/-! ## The estimate for a general divisibility chain -/

/-- Distance to the nearest integer. -/
noncomputable def nrm (t : ℝ) : ℝ := |t - round t|

theorem nrm_sub_le (y z : ℝ) : nrm (y - z) ≤ nrm y + |z| := by
  unfold nrm
  refine le_trans (round_le (y - z) (round y)) ?_
  have : y - z - (round y : ℝ) = (y - round y) - z := by ring
  rw [this]
  exact abs_sub _ _

/-- With residues `0 ≤ r < b_N` and a later modulus `q ≥ b_{N+1}`:
`‖(x - r)/q‖ ≤ ‖x/q‖ + b_N / b_{N+1}`. -/
theorem chain_estimate (x r bN bN1 q : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ bN) (h1 : 0 < bN1)
    (hq : bN1 ≤ q) : nrm ((x - r) / q) ≤ nrm (x / q) + bN / bN1 := by
  rw [sub_div]
  refine le_trans (nrm_sub_le _ _) ?_
  have hq0 : 0 < q := lt_of_lt_of_le h1 hq
  have : |r / q| ≤ bN / bN1 := by
    rw [abs_of_nonneg (div_nonneg hr0 hq0.le)]
    exact div_le_div₀ (le_trans hr0 hr) hr h1 hq
  linarith

end TwoPrimesAppendix
