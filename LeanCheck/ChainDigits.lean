import Mathlib

/-!
# The Cantor-digit calculus on `ℚ/ℤ` (Theorem G, `ChainSubsetTheorem_note.md`)

For a chain `M_0 = 1`, `M_{i+1} = α_i M_i` and a finite digit string `ρ`, put `x = ∑_{j<K} ρ_j / M_{j+1}` and
`w_i = ∑_{i ≤ j < K} ρ_j M_i / M_{j+1}`.  We check, in exact rational arithmetic:

* `digit_int`    : `M_i x - w_i` is an integer (so `w_i ≡ M_i x` modulo 1);
* `digit_rec`    : `w_i = (ρ_i + w_{i+1}) / α_i`;
* `digit_zeta`   : `(∑ e_i M_i) x - ∑ e_i w_i` is an integer (`ζ x ≡ ∑ e_i w_i`);
* `single_digit_small`, `single_digit_int` : the one-digit witness `x = ρ / M_{i+1}` has `M_j x ∈ [0, ρ/α_i]`
  for `j ≤ i` and `M_j x ∈ ℤ` for `j > i`.
-/

namespace LeanCheck

/-- `Mseq α i = α_0 ⋯ α_{i-1}`. -/
def Mseq (α : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => α i * Mseq α i

lemma Mseq_pos {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) (i : ℕ) : 0 < Mseq α i := by
  induction i with
  | zero => simp [Mseq]
  | succ i ih => simp only [Mseq]; exact Nat.mul_pos (hα i) ih

lemma Mseq_dvd (α : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : Mseq α i ∣ Mseq α j := by
  induction j, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ j _ ih => exact ih.trans (by simp only [Mseq]; exact Dvd.intro_left _ rfl)

lemma Mseq_le {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) {i j : ℕ} (h : i ≤ j) : Mseq α i ≤ Mseq α j :=
  Nat.le_of_dvd (Mseq_pos hα j) (Mseq_dvd α h)

/-- `x = ∑_{j<K} ρ_j / M_{j+1}`. -/
def xval (α : ℕ → ℕ) (ρ : ℕ → ℤ) (K : ℕ) : ℚ :=
  ∑ j ∈ Finset.range K, (ρ j : ℚ) / (Mseq α (j + 1) : ℚ)

/-- `w_i = ∑_{i ≤ j < K} ρ_j M_i / M_{j+1}`. -/
def wval (α : ℕ → ℕ) (ρ : ℕ → ℤ) (K i : ℕ) : ℚ :=
  ∑ j ∈ Finset.Ico i K, (ρ j : ℚ) * (Mseq α i : ℚ) / (Mseq α (j + 1) : ℚ)

lemma digit_int {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) (ρ : ℕ → ℤ) {K i : ℕ} (hi : i ≤ K) :
    ∃ n : ℤ, (Mseq α i : ℚ) * xval α ρ K - wval α ρ K i = n := by
  have hsplit : (Mseq α i : ℚ) * xval α ρ K =
      ∑ j ∈ Finset.range i, (ρ j : ℚ) * (Mseq α i : ℚ) / (Mseq α (j + 1) : ℚ) + wval α ρ K i := by
    unfold xval wval
    rw [Finset.mul_sum, ← Finset.sum_range_add_sum_Ico _ hi]
    congr 1 <;> (apply Finset.sum_congr rfl; intro j _; ring)
  have hint : ∃ n : ℤ, ∑ j ∈ Finset.range i, (ρ j : ℚ) * (Mseq α i : ℚ) / (Mseq α (j + 1) : ℚ) = n := by
    refine ⟨∑ j ∈ Finset.range i, ρ j * ((Mseq α i / Mseq α (j + 1) : ℕ) : ℤ), ?_⟩
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j + 1 ≤ i := Finset.mem_range.mp hj
    have hd : Mseq α (j + 1) ∣ Mseq α i := Mseq_dvd α hj'
    have hne : (Mseq α (j + 1) : ℚ) ≠ 0 := by
      have := Mseq_pos hα (j + 1); positivity
    have key : ((Mseq α i / Mseq α (j + 1) : ℕ) : ℚ) = (Mseq α i : ℚ) / Mseq α (j + 1) :=
      Nat.cast_div hd hne
    simp only [Int.cast_mul, Int.cast_natCast, key]
    ring
  obtain ⟨n, hn⟩ := hint
  exact ⟨n, by rw [hsplit, hn]; ring⟩

lemma digit_rec {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) (ρ : ℕ → ℤ) {K i : ℕ} (hi : i < K) :
    wval α ρ K i = ((ρ i : ℚ) + wval α ρ K (i + 1)) / (α i : ℚ) := by
  have hαi : (α i : ℚ) ≠ 0 := by have := hα i; positivity
  have hMi : (Mseq α i : ℚ) ≠ 0 := by have := Mseq_pos hα i; positivity
  have hMs : (Mseq α (i + 1) : ℚ) = α i * Mseq α i := by simp [Mseq]
  unfold wval
  rw [Finset.sum_eq_sum_Ico_succ_bot hi, add_div, Finset.sum_div]
  congr 1
  · rw [hMs]; field_simp
  · apply Finset.sum_congr rfl
    intro j _
    rw [hMs]
    have hMj : (Mseq α (j + 1) : ℚ) ≠ 0 := by have := Mseq_pos hα (j + 1); positivity
    field_simp

lemma digit_zeta {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) (ρ : ℕ → ℤ) (e : ℕ → ℤ) (K : ℕ) :
    ∃ n : ℤ, (∑ i ∈ Finset.range K, (e i : ℚ) * (Mseq α i : ℚ)) * xval α ρ K
      - ∑ i ∈ Finset.range K, (e i : ℚ) * wval α ρ K i = n := by
  have hterm : ∀ i ∈ Finset.range K, ∃ n : ℤ,
      (e i : ℚ) * ((Mseq α i : ℚ) * xval α ρ K - wval α ρ K i) = n := by
    intro i hi
    obtain ⟨n, hn⟩ := digit_int hα ρ (Finset.mem_range.mp hi).le
    exact ⟨e i * n, by rw [hn]; push_cast; ring⟩
  have hsum : ∃ n : ℤ, ∑ i ∈ Finset.range K, (e i : ℚ) * ((Mseq α i : ℚ) * xval α ρ K - wval α ρ K i) = n := by
    refine Finset.sum_induction _ (fun q : ℚ => ∃ n : ℤ, q = n) ?_ ⟨0, by simp⟩ hterm
    rintro a b ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, by push_cast; ring⟩
  obtain ⟨n, hn⟩ := hsum
  refine ⟨n, ?_⟩
  rw [← hn, Finset.sum_mul]
  simp only [mul_sub, Finset.sum_sub_distrib]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl; intro i _; ring
  · rfl

/-! ### The one-digit witness `x = ρ / M_{i+1}` -/

lemma single_digit_small {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) (ρ : ℕ) {i j : ℕ} (hj : j ≤ i) :
    0 ≤ (Mseq α j : ℚ) * ((ρ : ℚ) / Mseq α (i + 1)) ∧
      (Mseq α j : ℚ) * ((ρ : ℚ) / Mseq α (i + 1)) ≤ (ρ : ℚ) / α i := by
  have hMi : (0 : ℚ) < Mseq α i := by exact_mod_cast Mseq_pos hα i
  have hαi : (0 : ℚ) < α i := by exact_mod_cast hα i
  have hMs : (Mseq α (i + 1) : ℚ) = α i * Mseq α i := by simp [Mseq]
  have hle : (Mseq α j : ℚ) ≤ Mseq α i := by exact_mod_cast Mseq_le hα hj
  have hMj : (0 : ℚ) ≤ Mseq α j := by positivity
  have hρ : (0 : ℚ) ≤ ρ := by positivity
  constructor
  · positivity
  · rw [hMs]
    have : (Mseq α j : ℚ) * ((ρ : ℚ) / (α i * Mseq α i)) = (ρ : ℚ) / α i * ((Mseq α j : ℚ) / Mseq α i) := by
      field_simp
    rw [this]
    have h1 : (Mseq α j : ℚ) / Mseq α i ≤ 1 := by rw [div_le_one hMi]; exact hle
    have h2 : 0 ≤ (ρ : ℚ) / α i := by positivity
    calc (ρ : ℚ) / α i * ((Mseq α j : ℚ) / Mseq α i) ≤ (ρ : ℚ) / α i * 1 := by gcongr
      _ = (ρ : ℚ) / α i := by ring

lemma single_digit_int {α : ℕ → ℕ} (hα : ∀ i, 0 < α i) (ρ : ℕ) {i j : ℕ} (hj : i + 1 ≤ j) :
    ∃ n : ℤ, (Mseq α j : ℚ) * ((ρ : ℚ) / Mseq α (i + 1)) = n := by
  have hd : Mseq α (i + 1) ∣ Mseq α j := Mseq_dvd α hj
  have hne : (Mseq α (i + 1) : ℚ) ≠ 0 := by have := Mseq_pos hα (i + 1); positivity
  have key : ((Mseq α j / Mseq α (i + 1) : ℕ) : ℚ) = (Mseq α j : ℚ) / Mseq α (i + 1) :=
    Nat.cast_div hd hne
  refine ⟨ρ * ((Mseq α j / Mseq α (i + 1) : ℕ) : ℤ), ?_⟩
  simp only [Int.cast_mul, Int.cast_natCast, key]
  field_simp

end LeanCheck
