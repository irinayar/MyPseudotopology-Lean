import Mathlib

/-!
# Elementary lemmas behind Theorems F, G, H of `ChainSubsetTheorem_note.md`

Everything is stated over `ℝ` / `ℚ` with "distance to an integer" written as an existential integer, so no
circle group is needed.

* `contraction_step`, `run_contraction`  : the ratio-`≤ A` contraction along a run (Theorem G, failure direction;
  also Theorem F(a) and the use of Theorem G inside Theorem H).
* `near_of_all_multiples`                : the single-digit bound `dist(θ,ℤ) ≤ 1/(4R)` (Step 1 of the compatible direction).
* `crossing`                             : partial sums with steps `≤ 1/8` cross `1/4` and stop in `(1/4, 3/8]`
  (Case II of the compatible direction).
* `Mseq`, `digit_*`                      : the Cantor-digit calculus on `ℚ/ℤ` (`M_i x ≡ w_i`, the recursion
  `w_i = (ρ_i + w_{i+1})/α_i`, and `ζ x ≡ ∑ e_i w_i`).
* `geom_tail`                            : the geometric bound used for `P_C(x) ≤ 2η`.
-/

namespace LeanCheck

/-! ### Contraction along a run -/

/-- One step: if two reals are smaller than `δ`, `r ≤ A`, `δ (1 + A) < 1`, and `x' - r x` is an integer, then `x' = r x`. -/
lemma contraction_step {x x' δ A : ℝ} {r : ℕ} (hr : (r : ℝ) ≤ A) (hA : δ * (1 + A) < 1)
    (hx : |x| < δ) (hx' : |x'| < δ) (hint : ∃ n : ℤ, x' - r * x = n) : x' = r * x := by
  obtain ⟨n, hn⟩ := hint
  have hδ : 0 < δ := lt_of_le_of_lt (abs_nonneg _) hx
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hA0 : 0 ≤ A := le_trans hr0 hr
  have h1 : |x' - r * x| ≤ |x'| + r * |x| := by
    calc |x' - r * x| ≤ |x'| + |r * x| := abs_sub _ _
      _ = |x'| + r * |x| := by rw [abs_mul, abs_of_nonneg hr0]
  have h2 : r * |x| ≤ A * δ := by
    exact mul_le_mul hr hx.le (abs_nonneg _) hA0
  have h3 : |(n : ℝ)| < 1 := by
    rw [← hn]
    nlinarith
  have h4 : |n| < 1 := by exact_mod_cast h3
  have h5 : n = 0 := Int.abs_lt_one_iff.mp h4
  rw [h5] at hn
  simpa using sub_eq_zero.mp (by simpa using hn)

/-- Along a run of consecutive observations with ratios `2 ≤ r_i ≤ A` the bottom value is `2^L` times smaller than the top value. -/
lemma run_contraction {δ A : ℝ} (hA : δ * (1 + A) < 1) (r : ℕ → ℕ) (hr2 : ∀ i, 2 ≤ r i)
    (hrA : ∀ i, (r i : ℝ) ≤ A) (w : ℕ → ℝ) :
    ∀ L : ℕ, (∀ i ≤ L, |w i| < δ) → (∀ i < L, ∃ n : ℤ, w (i + 1) - r i * w i = n) →
      |w 0| * 2 ^ L ≤ |w L| := by
  intro L
  induction L with
  | zero => intro _ _; simp
  | succ L ih =>
    intro hw hint
    have ih' := ih (fun i hi => hw i (by omega)) (fun i hi => hint i (by omega))
    have hstep : w (L + 1) = r L * w L :=
      contraction_step (hrA L) hA (hw L (by omega)) (hw (L + 1) le_rfl) (hint L (by omega))
    have hr2' : (2 : ℝ) ≤ r L := by exact_mod_cast hr2 L
    have habs : |w (L + 1)| = r L * |w L| := by
      rw [hstep, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r L)]
    calc |w 0| * 2 ^ (L + 1) = (|w 0| * 2 ^ L) * 2 := by ring
      _ ≤ |w L| * 2 := by gcongr
      _ ≤ r L * |w L| := by nlinarith [abs_nonneg (w L)]
      _ = |w (L + 1)| := habs.symm

/-- Quantitative form: the bottom of a run of length `L` is below `δ / 2^L`. -/
lemma run_bottom_small {δ A : ℝ} (hA : δ * (1 + A) < 1) (r : ℕ → ℕ) (hr2 : ∀ i, 2 ≤ r i)
    (hrA : ∀ i, (r i : ℝ) ≤ A) (w : ℕ → ℝ) (L : ℕ) (hw : ∀ i ≤ L, |w i| < δ)
    (hint : ∀ i < L, ∃ n : ℤ, w (i + 1) - r i * w i = n) : |w 0| < δ / 2 ^ L := by
  have h := run_contraction hA r hr2 hrA w L hw hint
  have hpos : (0 : ℝ) < 2 ^ L := by positivity
  rw [lt_div_iff₀ hpos]
  exact lt_of_le_of_lt h (hw L le_rfl)

/-! ### The single-digit bound -/

/-- If `ρ θ` is within `1/4` of an integer for all `0 ≤ ρ ≤ R`, then `θ` is within `1/(4R)` of an integer. -/
lemma near_of_all_multiples {θ : ℝ} {R : ℕ} (hR : 1 ≤ R)
    (h : ∀ ρ : ℕ, ρ ≤ R → ∃ n : ℤ, |(ρ : ℝ) * θ - n| < 1 / 4) :
    ∃ m : ℤ, |θ - m| ≤ 1 / (4 * R) := by
  obtain ⟨m, hm⟩ := h 1 hR
  simp only [Nat.cast_one, one_mul] at hm
  refine ⟨m, ?_⟩
  by_contra hcon
  replace hcon := not_le.mp hcon
  set r : ℝ := θ - m with hr
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hr_pos : 0 < |r| := lt_trans (by positivity) hcon
  have hlt : 1 / (4 * |r|) < R := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hcon
    nlinarith
  set ρ : ℕ := ⌊1 / (4 * |r|)⌋₊ + 1 with hρ
  have hρR : ρ ≤ R := by
    have : ⌊1 / (4 * |r|)⌋₊ < R := (Nat.floor_lt (by positivity)).mpr hlt
    omega
  have hρ1 : 1 / 4 < ρ * |r| := by
    have h1 : 1 / (4 * |r|) < ρ := by
      have := Nat.lt_floor_add_one (1 / (4 * |r|))
      simpa [hρ] using this
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith
  have hρ2 : ρ * |r| < 1 / 2 := by
    have h1 : (⌊1 / (4 * |r|)⌋₊ : ℝ) ≤ 1 / (4 * |r|) := Nat.floor_le (by positivity)
    have h2 : (⌊1 / (4 * |r|)⌋₊ : ℝ) * |r| ≤ 1 / 4 := by
      calc (⌊1 / (4 * |r|)⌋₊ : ℝ) * |r| ≤ 1 / (4 * |r|) * |r| := by gcongr
        _ = 1 / 4 := by field_simp
    have hr4 : |r| < 1 / 4 := hm
    have : (ρ : ℝ) = ⌊1 / (4 * |r|)⌋₊ + 1 := by simp [hρ]
    rw [this]
    nlinarith
  obtain ⟨n, hn⟩ := h ρ hρR
  set k : ℤ := n - ρ * m with hk
  have hkey : |(ρ : ℝ) * r - k| < 1 / 4 := by
    have : (ρ : ℝ) * θ - n = ρ * r - k := by
      simp only [hk, hr]; push_cast; ring
    rw [← this]; exact hn
  by_cases hk0 : k = 0
  · rw [hk0] at hkey
    simp at hkey
    linarith
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : 1 ≤ |k| := Int.one_le_abs hk0
      exact_mod_cast this
    have hρr : |(ρ : ℝ) * r| = ρ * |r| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ρ)]
    have := abs_sub_abs_le_abs_sub (k : ℝ) ((ρ : ℝ) * r)
    rw [abs_sub_comm] at this
    linarith

/-! ### Crossing of the threshold 1/4 -/

/-- Positive steps of size between `c > 0` and `1/8` have a partial sum in `(1/4, 3/8]`. -/
lemma crossing {t : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (hlow : ∀ j, c ≤ t j) (hup : ∀ j, t j ≤ 1 / 8) :
    ∃ m : ℕ, 1 / 4 < ∑ j ∈ Finset.range m, t j ∧ ∑ j ∈ Finset.range m, t j ≤ 3 / 8 := by
  classical
  have hex : ∃ m : ℕ, 1 / 4 < ∑ j ∈ Finset.range m, t j := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((1 / 4) / c)
    refine ⟨N, ?_⟩
    have h1 : (N : ℝ) * c ≤ ∑ j ∈ Finset.range N, t j := by
      calc (N : ℝ) * c = ∑ _j ∈ Finset.range N, c := by simp
        _ ≤ ∑ j ∈ Finset.range N, t j := Finset.sum_le_sum (fun j _ => hlow j)
    have : (1 / 4 : ℝ) < N * c := by
      rw [div_lt_iff₀ hc] at hN; exact hN
    linarith
  set m := Nat.find hex with hm
  have hmspec : 1 / 4 < ∑ j ∈ Finset.range m, t j := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hmspec
    simp at hmspec
    linarith
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hmin : ¬ (1 / 4 < ∑ j ∈ Finset.range m', t j) := Nat.find_min hex (by omega)
  replace hmin := not_lt.mp hmin
  refine ⟨m, hmspec, ?_⟩
  rw [hm', Finset.sum_range_succ]
  have := hup m'
  linarith

/-! ### The geometric tail -/

/-- If each term is at most half the previous one, the sum is at most twice the first term. -/
lemma geom_tail {a : ℕ → ℝ} (hnn : ∀ j, 0 ≤ a j) (hhalf : ∀ j, a (j + 1) ≤ a j / 2) (m : ℕ) :
    ∑ j ∈ Finset.range m, a j ≤ 2 * a 0 := by
  have hterm : ∀ j, a j ≤ a 0 / 2 ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc a (j + 1) ≤ a j / 2 := hhalf j
        _ ≤ (a 0 / 2 ^ j) / 2 := by gcongr
        _ = a 0 / 2 ^ (j + 1) := by rw [pow_succ]; field_simp
  have hsum : ∑ j ∈ Finset.range m, a j ≤ ∑ j ∈ Finset.range m, a 0 * (1 / 2) ^ j := by
    apply Finset.sum_le_sum
    intro j _
    have := hterm j
    calc a j ≤ a 0 / 2 ^ j := this
      _ = a 0 * (1 / 2) ^ j := by rw [one_div, inv_pow]; field_simp
  have hgeom : ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j ≤ 2 := by
    have := geom_sum_eq (x := (1 / 2 : ℝ)) (by norm_num) m
    rw [this]
    have hp : (0 : ℝ) < (1 / 2) ^ m := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    nlinarith
  calc ∑ j ∈ Finset.range m, a j ≤ ∑ j ∈ Finset.range m, a 0 * (1 / 2) ^ j := hsum
    _ = a 0 * ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j := by rw [Finset.mul_sum]
    _ ≤ a 0 * 2 := by gcongr; exact hnn 0
    _ = 2 * a 0 := by ring

end LeanCheck
