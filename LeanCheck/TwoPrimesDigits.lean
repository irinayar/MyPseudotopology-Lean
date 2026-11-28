import LeanCheck.TwoPrimesSUnit

/-!
# Digits of one irrational number in two coprime bases

Two statements on the digit changes (and on the non-zero digits) of an irrational `ξ` in coprime
bases `p`, `q`.  A **mark** of a base is an index at which a sequence of rationals approximating
`ξ` changes; for the two sequences used below the marks are the digit changes, respectively the
non-zero digits.

* `golden_marks`: elementary and effective.  With windows growing like the powers of the golden
  ratio, at least `B + 1` marks lie below `w (B+2)`.
* `window_marks`: with `EvertseCor1` (Corollary 1 of J.-H. Evertse, Compositio Math. 53 (1984)),
  a **hypothesis** here: for every `K` and all large `Y` there are more than `K` marks with
  position in `(Y, 13Y/4]`.  Hence the number of marks is not `O(log n)` (`tendsto_marks`).

The position of the index `j` of the base `l` is `j log l`.
-/

namespace TwoPrimesDigits

open Finset Real TwoPrimesSUnit

/-! ## The two kinds of approximating rationals -/

/-- Rationals `α n` with denominator dividing `l^n (l-1)`, within `l^(-n)` of `ξ`, whose
successive differences have small numerators. -/
structure Approx (l : ℕ) (ξ : ℝ) (α : ℕ → ℚ) : Prop where
  num : ∀ n, ∃ r : ℤ, α n = r / ((l : ℚ) ^ n * ((l : ℚ) - 1))
  step : ∀ j, 1 ≤ j → ∃ e : ℤ, |(e : ℝ)| ≤ ((l : ℝ) - 1) ^ 2 ∧
    α j - α (j - 1) = e / (((l : ℚ) - 1) * (l : ℚ) ^ j)
  close : ∀ n, |ξ - (α n : ℝ)| ≤ 1 / (l : ℝ) ^ n

/-- The `k`-th digit of `ξ` in the base `l`, for `k ≥ 1`. -/
noncomputable def digit (l : ℕ) (ξ : ℝ) (k : ℕ) : ℤ :=
  ⌊ξ * (l : ℝ) ^ k⌋ - (l : ℤ) * ⌊ξ * (l : ℝ) ^ (k - 1)⌋

/-- Truncation followed by the next digit repeated for ever. -/
noncomputable def alphaDC (l : ℕ) (ξ : ℝ) (n : ℕ) : ℚ :=
  (⌊ξ * (l : ℝ) ^ n⌋ : ℚ) / (l : ℚ) ^ n
    + (digit l ξ (n + 1) : ℚ) / ((l : ℚ) ^ n * ((l : ℚ) - 1))

/-- Truncation. -/
noncomputable def alphaNZ (l : ℕ) (ξ : ℝ) (n : ℕ) : ℚ :=
  (⌊ξ * (l : ℝ) ^ n⌋ : ℚ) / (l : ℚ) ^ n

lemma digit_range {l : ℕ} (hl : 2 ≤ l) (ξ : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ digit l ξ k ∧ digit l ξ k ≤ (l : ℤ) - 1 ∧
      (digit l ξ k : ℝ) ≤ (l : ℝ) * Int.fract (ξ * (l : ℝ) ^ (k - 1)) ∧
      (l : ℝ) * Int.fract (ξ * (l : ℝ) ^ (k - 1)) < (digit l ξ k : ℝ) + 1 := by
  set y := ξ * (l : ℝ) ^ (k - 1) with hy
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have e : ξ * (l : ℝ) ^ k = (l : ℝ) * y := by
    have : (l : ℝ) ^ k = (l : ℝ) * (l : ℝ) ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this, hy]; ring
  have hd : digit l ξ k = ⌊(l : ℝ) * Int.fract y⌋ := by
    unfold digit
    rw [e, ← hy]
    have : (l : ℝ) * y = (l : ℝ) * Int.fract y + (((l : ℤ) * ⌊y⌋ : ℤ) : ℝ) := by
      have h := Int.floor_add_fract y
      push_cast
      linear_combination (-(l : ℝ)) * h
    rw [this, Int.floor_add_intCast]
    ring
  have h0 : 0 ≤ (l : ℝ) * Int.fract y := mul_nonneg hl0.le (Int.fract_nonneg y)
  have h1 : (l : ℝ) * Int.fract y < l := by
    have := mul_lt_mul_of_pos_left (Int.fract_lt_one y) hl0
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd]; exact Int.floor_nonneg.mpr h0
  · rw [hd]
    have : ⌊(l : ℝ) * Int.fract y⌋ < (l : ℤ) := by
      rw [Int.floor_lt]; exact_mod_cast h1
    omega
  · rw [hd]; exact Int.floor_le _
  · rw [hd]; exact Int.lt_floor_add_one _

lemma floor_succ (l : ℕ) (ξ : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    ⌊ξ * (l : ℝ) ^ j⌋ = (l : ℤ) * ⌊ξ * (l : ℝ) ^ (j - 1)⌋ + digit l ξ j := by
  unfold digit; ring

lemma alphaNZ_sub {l : ℕ} (hl : 2 ≤ l) (ξ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    alphaNZ l ξ j - alphaNZ l ξ (j - 1) = (digit l ξ j : ℚ) / (l : ℚ) ^ j := by
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
  have hp : (l : ℚ) ^ j = (l : ℚ) ^ (j - 1) * l := by
    rw [← pow_succ]; congr 1; omega
  unfold alphaNZ
  rw [floor_succ l ξ j hj, hp]
  push_cast
  field_simp
  ring

lemma alphaDC_sub {l : ℕ} (hl : 2 ≤ l) (ξ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    alphaDC l ξ j - alphaDC l ξ (j - 1)
      = ((digit l ξ (j + 1) - digit l ξ j : ℤ) : ℚ) / (((l : ℚ) - 1) * (l : ℚ) ^ j) := by
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
  have hl1 : (l : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ l := by exact_mod_cast hl
    intro h; linarith
  have hp : (l : ℚ) ^ j = (l : ℚ) ^ (j - 1) * l := by
    rw [← pow_succ]; congr 1; omega
  have ej : j - 1 + 1 = j := by omega
  unfold alphaDC
  rw [ej, floor_succ l ξ j hj, hp]
  push_cast
  field_simp
  ring

lemma trunc_error {l : ℕ} (hl : 2 ≤ l) (ξ : ℝ) (n : ℕ) :
    ξ - ((⌊ξ * (l : ℝ) ^ n⌋ : ℚ) / (l : ℚ) ^ n : ℚ)
      = Int.fract (ξ * (l : ℝ) ^ n) / (l : ℝ) ^ n := by
  have hl0 : (l : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : l ≠ 0))
  push_cast
  rw [eq_div_iff hl0, sub_mul, div_mul_cancel₀ _ hl0]
  exact (Int.self_sub_floor (ξ * (l : ℝ) ^ n))

lemma approxNZ {l : ℕ} (hl : 2 ≤ l) (ξ : ℝ) : Approx l ξ (alphaNZ l ξ) := by
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
  have hl1 : (l : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ l := by exact_mod_cast hl
    intro h; linarith
  have hlr : (2 : ℝ) ≤ l := by exact_mod_cast hl
  refine ⟨fun n => ⟨⌊ξ * (l : ℝ) ^ n⌋ * ((l : ℤ) - 1), ?_⟩, fun j hj => ?_, fun n => ?_⟩
  · unfold alphaNZ
    push_cast
    field_simp
  · refine ⟨((l : ℤ) - 1) * digit l ξ j, ?_, ?_⟩
    · obtain ⟨h0, h1, _, _⟩ := digit_range hl ξ hj
      have h0' : (0 : ℝ) ≤ digit l ξ j := by exact_mod_cast h0
      have h1' : (digit l ξ j : ℝ) ≤ (l : ℝ) - 1 := by exact_mod_cast h1
      push_cast
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (l : ℝ) - 1), abs_of_nonneg h0', sq]
      exact mul_le_mul_of_nonneg_left h1' (by linarith)
    · rw [alphaNZ_sub hl ξ hj]
      push_cast
      field_simp
  · have h := trunc_error hl ξ n
    unfold alphaNZ
    rw [h, abs_of_nonneg (div_nonneg (Int.fract_nonneg _) (by positivity))]
    gcongr
    exact (Int.fract_lt_one _).le

lemma approxDC {l : ℕ} (hl : 2 ≤ l) (ξ : ℝ) : Approx l ξ (alphaDC l ξ) := by
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
  have hl1 : (l : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ l := by exact_mod_cast hl
    intro h; linarith
  have hlr : (2 : ℝ) ≤ l := by exact_mod_cast hl
  refine ⟨fun n => ⟨⌊ξ * (l : ℝ) ^ n⌋ * ((l : ℤ) - 1) + digit l ξ (n + 1), ?_⟩,
    fun j hj => ?_, fun n => ?_⟩
  · unfold alphaDC
    push_cast
    field_simp
  · refine ⟨digit l ξ (j + 1) - digit l ξ j, ?_, alphaDC_sub hl ξ hj⟩
    obtain ⟨h0, h1, _, _⟩ := digit_range hl ξ hj
    obtain ⟨g0, g1, _, _⟩ := digit_range hl ξ (show 1 ≤ j + 1 by omega)
    have h : |digit l ξ (j + 1) - digit l ξ j| ≤ (l : ℤ) - 1 := by
      rw [abs_le]; constructor <;> omega
    have h' : |((digit l ξ (j + 1) - digit l ξ j : ℤ) : ℝ)| ≤ (l : ℝ) - 1 := by
      exact_mod_cast h
    refine le_trans h' ?_
    rw [sq]
    exact le_mul_of_one_le_left (by linarith) (by linarith)
  · obtain ⟨g0, g1, g2, g3⟩ := digit_range hl ξ (show 1 ≤ n + 1 by omega)
    simp only [Nat.add_sub_cancel] at g0 g1 g2 g3
    set f := Int.fract (ξ * (l : ℝ) ^ n) with hf
    set d : ℝ := (digit l ξ (n + 1) : ℝ) with hd
    have d0 : 0 ≤ d := by rw [hd]; exact_mod_cast g0
    have d1 : d ≤ (l : ℝ) - 1 := by rw [hd]; exact_mod_cast g1
    have hl' : (0 : ℝ) < (l : ℝ) - 1 := by linarith
    have hpow : (0 : ℝ) < (l : ℝ) ^ n := by positivity
    have e : ξ - (alphaDC l ξ n : ℝ) = (f - d / ((l : ℝ) - 1)) / (l : ℝ) ^ n := by
      have h := trunc_error hl ξ n
      rw [← hf] at h
      have : (alphaDC l ξ n : ℝ)
          = (((⌊ξ * (l : ℝ) ^ n⌋ : ℚ) / (l : ℚ) ^ n : ℚ) : ℝ)
            + d / ((l : ℝ) ^ n * ((l : ℝ) - 1)) := by
        unfold alphaDC
        rw [hd]
        push_cast
        ring
      rw [this, ← sub_sub, h]
      field_simp
    have hb : |f - d / ((l : ℝ) - 1)| ≤ 1 := by
      have f0 : 0 ≤ f := Int.fract_nonneg _
      have f1 : f < 1 := Int.fract_lt_one _
      have q0 : 0 ≤ d / ((l : ℝ) - 1) := div_nonneg d0 hl'.le
      have q1 : d / ((l : ℝ) - 1) ≤ 1 := (div_le_one hl').mpr d1
      rw [abs_le]; constructor <;> linarith
    rw [e, abs_div, abs_of_pos hpow]
    exact div_le_div_of_nonneg_right hb hpow.le

/-! ## Marks and free stretches -/

/-- The marks with index in `[1, n]`. -/
def marks (α : ℕ → ℚ) (n : ℕ) : Finset ℕ := (Icc 1 n).filter (fun j => α j ≠ α (j - 1))

/-- The marks with position in `(a, b]`. -/
noncomputable def marksIn (l : ℕ) (α : ℕ → ℚ) (a b : ℝ) : Finset ℕ :=
  (marks α ⌊b / log l⌋₊).filter (fun j => a < (j : ℝ) * log l)

lemma mem_marksIn {l j : ℕ} (hl : 2 ≤ l) {α : ℕ → ℚ} {a b : ℝ} (hb : 0 ≤ b) :
    j ∈ marksIn l α a b ↔
      1 ≤ j ∧ α j ≠ α (j - 1) ∧ a < (j : ℝ) * log l ∧ (j : ℝ) * log l ≤ b := by
  have hL : 0 < log (l : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < l))
  have h : j ≤ ⌊b / log l⌋₊ ↔ (j : ℝ) * log l ≤ b := by
    rw [Nat.le_floor_iff (div_nonneg hb hL.le), le_div_iff₀ hL]
  simp only [marksIn, marks, mem_filter, mem_Icc, h]
  tauto

lemma telescope (α : ℕ → ℚ) {n m : ℕ} (h : n ≤ m) :
    α m - α n = ∑ j ∈ (Ioc n m).filter (fun j => α j ≠ α (j - 1)), (α j - α (j - 1)) := by
  rw [sum_filter_of_ne (s := Ioc n m) (f := fun j : ℕ => α j - α (j - 1))
    (p := fun j : ℕ => α j ≠ α (j - 1)) (fun j _ hj => sub_ne_zero.mp hj)]
  induction m, h using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [sum_Ioc_succ_top hk, ← ih, Nat.add_sub_cancel]
    ring

lemma floor_pos_bounds {l : ℕ} (hl : 2 ≤ l) {c : ℝ} (hc : 0 ≤ c) :
    (⌊c / log l⌋₊ : ℝ) * log l ≤ c ∧ c < ((⌊c / log l⌋₊ : ℝ) + 1) * log l ∧
      (l : ℝ) ^ ⌊c / log l⌋₊ ≤ exp c := by
  have hL : 0 < log (l : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < l))
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have h1 : (⌊c / log l⌋₊ : ℝ) * log l ≤ c := by
    have := Nat.floor_le (div_nonneg hc hL.le)
    rwa [le_div_iff₀ hL] at this
  refine ⟨h1, ?_, ?_⟩
  · have := Nat.lt_floor_add_one (c / log l)
    rwa [div_lt_iff₀ hL] at this
  · rw [← exp_log (pow_pos hl0 _), log_pow]
    exact exp_le_exp.mpr h1

/-- **A free stretch.** -/
lemma free_close {l : ℕ} (hl : 2 ≤ l) {ξ : ℝ} {α : ℕ → ℚ} (h : Approx l ξ α) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d)
    (hfree : ∀ j : ℕ, 1 ≤ j → c < (j : ℝ) * log l → (j : ℝ) * log l ≤ d → α j = α (j - 1)) :
    |ξ - (α ⌊c / log l⌋₊ : ℝ)| < l * exp (-d) := by
  have hL : 0 < log (l : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < l))
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  set n := ⌊c / log l⌋₊ with hn
  set m := ⌊d / log l⌋₊ with hm
  have hnm : n ≤ m := Nat.floor_mono (div_le_div_of_nonneg_right hcd hL.le)
  have hd : 0 ≤ d := le_trans hc hcd
  have hconst : α m = α n := by
    have ht := telescope α hnm
    have hempty : (Ioc n m).filter (fun j => α j ≠ α (j - 1)) = ∅ := by
      rw [filter_eq_empty_iff]
      intro j hj
      rw [mem_Ioc] at hj
      rw [not_not]
      refine hfree j (by omega) ?_ ?_
      · have h1 := (floor_pos_bounds hl hc).2.1
        rw [← hn] at h1
        have h2 : (n : ℝ) + 1 ≤ j := by exact_mod_cast hj.1
        exact lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_right h2 hL.le)
      · have h1 := (floor_pos_bounds hl hd).1
        rw [← hm] at h1
        have h2 : (j : ℝ) ≤ m := by exact_mod_cast hj.2
        exact le_trans (mul_le_mul_of_nonneg_right h2 hL.le) h1
    rw [hempty, sum_empty, sub_eq_zero] at ht
    exact ht
  rw [← hconst]
  refine lt_of_le_of_lt (h.close m) ?_
  have h1 := (floor_pos_bounds hl hd).2.1
  rw [← hm] at h1
  have h2 : exp d < (l : ℝ) ^ m * l := by
    have e : (l : ℝ) ^ m * l = exp (((m : ℝ) + 1) * log l) := by
      rw [← pow_succ, ← exp_log (pow_pos hl0 (m + 1)), log_pow]
      push_cast; ring_nf
    rw [e]
    exact exp_lt_exp.mpr h1
  rw [exp_neg, ← div_eq_mul_inv, div_lt_div_iff₀ (pow_pos hl0 _) (exp_pos _), one_mul]
  exact h2.trans_eq (mul_comm _ _)

/-! ## Two coprime bases -/

/-- If the two rationals agree, their value has denominator dividing `(p-1)(q-1)`. -/
lemma common_value {p q n m : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q) {a : ℚ}
    {r s : ℤ} (h1 : a = r / ((p : ℚ) ^ n * ((p : ℚ) - 1)))
    (h2 : a = s / ((q : ℚ) ^ m * ((q : ℚ) - 1))) :
    ∃ z : ℤ, a = z / (((p : ℚ) - 1) * ((q : ℚ) - 1)) := by
  have key : ∀ (l k : ℕ), 2 ≤ l → ∀ t : ℤ, a = t / ((l : ℚ) ^ k * ((l : ℚ) - 1)) →
      a.den ∣ l ^ k * (l - 1) := by
    intro l k hl t ht
    have e : a = Rat.divInt t ((l ^ k * (l - 1) : ℕ) : ℤ) := by
      rw [ht, Rat.divInt_eq_div]
      push_cast [Nat.cast_sub (show 1 ≤ l by omega)]
      ring
    have := Rat.den_dvd t ((l ^ k * (l - 1) : ℕ) : ℤ)
    rw [← e] at this
    exact_mod_cast this
  have d1 := key p n hp r h1
  have d2 := key q m hq s h2
  have hden : a.den ∣ (p - 1) * (q - 1) := by
    have g1 : a.den ∣ p ^ n * ((p - 1) * (q - 1)) := by
      rw [← mul_assoc]; exact d1.mul_right _
    have g2 : a.den ∣ q ^ m * ((p - 1) * (q - 1)) := by
      rw [mul_comm (p - 1), ← mul_assoc]; exact d2.mul_right _
    have := Nat.dvd_gcd g1 g2
    rwa [Nat.gcd_mul_right, (Nat.Coprime.pow n m hpq).gcd_eq_one, one_mul] at this
  obtain ⟨c, hc⟩ := hden
  refine ⟨a.num * c, ?_⟩
  have hG : ((p : ℚ) - 1) * ((q : ℚ) - 1) = (a.den : ℚ) * c := by
    have : (((p - 1) * (q - 1) : ℕ) : ℚ) = ((a.den * c : ℕ) : ℚ) := by rw [hc]
    push_cast [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_sub (show 1 ≤ q by omega)] at this
    exact this
  have hpos : (0 : ℚ) < ((p : ℚ) - 1) * ((q : ℚ) - 1) := by
    have a1 : (2 : ℚ) ≤ p := by exact_mod_cast hp
    have a2 : (2 : ℚ) ≤ q := by exact_mod_cast hq
    exact mul_pos (by linarith) (by linarith)
  have hc0 : (c : ℚ) ≠ 0 := by
    intro h0
    rw [hG, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  rw [hG]
  push_cast
  rw [mul_div_mul_right _ _ hc0, Rat.num_div_den]

/-- The integer `(p-1)(q-1) p^n q^m (α n - β m)`. -/
lemma anchor_int {p q n m : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {a b : ℚ} {r s : ℤ}
    (h1 : a = r / ((p : ℚ) ^ n * ((p : ℚ) - 1))) (h2 : b = s / ((q : ℚ) ^ m * ((q : ℚ) - 1))) :
    ∃ N : ℤ, (N : ℚ) = ((p : ℚ) - 1) * ((q : ℚ) - 1) * (p : ℚ) ^ n * (q : ℚ) ^ m * (a - b) := by
  have p0 : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have q0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have p1 : (p : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp
    intro h; linarith
  have q1 : (q : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    intro h; linarith
  refine ⟨r * ((q : ℤ) - 1) * (q : ℤ) ^ m - s * ((p : ℤ) - 1) * (p : ℤ) ^ n, ?_⟩
  rw [h1, h2]
  push_cast
  field_simp

/-! ## The golden ratio, effective -/

/-- The window ends `γ^k (x0 + C) - C`. -/
noncomputable def ww (C x0 : ℝ) (k : ℕ) : ℝ := goldenRatio ^ k * (x0 + C) - C

lemma ww_rec (C x0 : ℝ) (k : ℕ) : ww C x0 (k + 2) = ww C x0 (k + 1) + ww C x0 k + C := by
  have h : goldenRatio ^ (k + 2) = goldenRatio ^ (k + 1) + goldenRatio ^ k := by
    rw [pow_add, goldenRatio_sq, pow_succ]; ring
  unfold ww
  rw [h]; ring

lemma ww_mono {C x0 : ℝ} (h : 0 ≤ x0 + C) {i j : ℕ} (hij : i ≤ j) : ww C x0 i ≤ ww C x0 j := by
  have := pow_le_pow_right₀ one_lt_goldenRatio.le hij
  exact sub_le_sub_right (mul_le_mul_of_nonneg_right this h) C

/-- **At least `B+1` marks below `w (B+2)`.**  Here `(p-1)(q-1)` times `ξ` is at distance at
least `q e^(-x0)` times that factor from the integers. -/
theorem golden_marks {p q : ℕ} (hp : 2 ≤ p) (hpq' : p < q) (hpq : Nat.Coprime p q) {ξ x0 C : ℝ}
    {α β : ℕ → ℚ} (hα : Approx p ξ α) (hβ : Approx q ξ β)
    (hC : C = log (((p : ℝ) + q) * (((p : ℝ) - 1) * ((q : ℝ) - 1)))) (hx0 : 0 ≤ x0)
    (hdist : ∀ z : ℤ, (q : ℝ) * exp (-x0) ≤ |ξ - z / (((p : ℝ) - 1) * ((q : ℝ) - 1))|) (B : ℕ) :
    B + 1 ≤ (marksIn p α x0 (ww C x0 (B + 2))).card
      + (marksIn q β x0 (ww C x0 (B + 2))).card := by
  have hq : 2 ≤ q := by omega
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqr : (3 : ℝ) ≤ q := by exact_mod_cast (by omega : 3 ≤ q)
  set G : ℝ := ((p : ℝ) - 1) * ((q : ℝ) - 1) with hG
  have hG1 : 1 ≤ G := by
    have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have h2 : (1 : ℝ) ≤ (q : ℝ) - 1 := by linarith
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hpos : (0 : ℝ) < ((p : ℝ) + q) * G := mul_pos (by linarith) (by linarith)
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith) hG1)
  have hCe : exp C = ((p : ℝ) + q) * G := by rw [hC, exp_log hpos]
  have h0 : 0 ≤ x0 + C := add_nonneg hx0 hC0
  by_contra hcon
  rw [not_le, Nat.lt_succ_iff] at hcon
  set X := ww C x0 (B + 2) with hX
  obtain ⟨k, hkB, i, j, hij, hfp, hfq⟩ := TwoPrimesGolden.exists_stagger (ww C x0)
    (fun i j h => ww_mono h0 h) (log p) (log q) (marksIn p α x0 X) (marksIn q β x0 X) B hcon
  have hw0 : ww C x0 0 = x0 := by unfold ww; rw [pow_zero]; ring
  have hge : ∀ t, x0 ≤ ww C x0 t := by
    intro t
    have := ww_mono (C := C) (x0 := x0) h0 (Nat.zero_le t)
    rwa [hw0] at this
  set b := ww C x0 (k + 2) with hb
  have hbX : b ≤ X := ww_mono h0 (by omega)
  have hbx : x0 ≤ b := hge _
  have hX0 : 0 ≤ X := le_trans hx0 (le_trans hbx hbX)
  have hik : ww C x0 i ≤ b ∧ ww C x0 j ≤ b := by
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨ww_mono h0 (by omega), ww_mono h0 (by omega)⟩
  have hsum : ww C x0 i + ww C x0 j + C = b := by
    have h := ww_rec C x0 k
    rw [hb, h]
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring
  have free : ∀ (l : ℕ) (hl : 2 ≤ l) (γ : ℕ → ℚ) (hγ : Approx l ξ γ) (a : ℝ), x0 ≤ a → a ≤ b →
      (∀ n ∈ marksIn l γ x0 X, ¬ (a < (n : ℝ) * log l ∧ (n : ℝ) * log l ≤ b)) →
      |ξ - (γ ⌊a / log l⌋₊ : ℝ)| < l * exp (-b) := by
    intro l hl γ hγ a ha hab hf
    refine free_close hl hγ (le_trans hx0 ha) hab (fun n hn h1 h2 => ?_)
    by_contra hne
    exact hf n ((mem_marksIn hl hX0).mpr ⟨hn, hne, lt_of_le_of_lt ha h1, le_trans h2 hbX⟩) ⟨h1, h2⟩
  have e1 := free p hp α hα _ (hge i) hik.1 hfp
  have e2 := free q hq β hβ _ (hge j) hik.2 hfq
  set n := ⌊ww C x0 i / log p⌋₊ with hn
  set m := ⌊ww C x0 j / log q⌋₊ with hm
  have pn : (p : ℝ) ^ n ≤ exp (ww C x0 i) := (floor_pos_bounds hp (le_trans hx0 (hge i))).2.2
  have qm : (q : ℝ) ^ m ≤ exp (ww C x0 j) := (floor_pos_bounds hq (le_trans hx0 (hge j))).2.2
  obtain ⟨r, hr⟩ := hα.num n
  obtain ⟨s, hs⟩ := hβ.num m
  obtain ⟨N, hN⟩ := anchor_int hp hq hr hs
  have hNr : (N : ℝ) = G * (p : ℝ) ^ n * (q : ℝ) ^ m * ((α n : ℝ) - (β m : ℝ)) := by
    have := congrArg (fun t : ℚ => (t : ℝ)) hN
    push_cast at this
    rw [this, hG]
  have hdiff : |(α n : ℝ) - (β m : ℝ)| < ((p : ℝ) + q) * exp (-b) := by
    have : (α n : ℝ) - (β m : ℝ) = (ξ - (β m : ℝ)) - (ξ - (α n : ℝ)) := by ring
    rw [this]
    refine lt_of_le_of_lt (abs_sub _ _) ?_
    linarith
  have hN0 : N = 0 := by
    have hlt : |(N : ℝ)| < 1 := by
      have hGpq : 0 < G * (p : ℝ) ^ n * (q : ℝ) ^ m := by positivity
      rw [hNr, abs_mul, abs_of_pos hGpq]
      have h1 : G * (p : ℝ) ^ n * (q : ℝ) ^ m
          ≤ G * exp (ww C x0 i) * exp (ww C x0 j) := by
        gcongr
      have h2 : G * exp (ww C x0 i) * exp (ww C x0 j) * (((p : ℝ) + q) * exp (-b)) = 1 := by
        have e : exp (ww C x0 i) * exp (ww C x0 j) * exp C = exp b := by
          rw [← exp_add, ← exp_add, hsum]
        calc G * exp (ww C x0 i) * exp (ww C x0 j) * (((p : ℝ) + q) * exp (-b))
            = (exp (ww C x0 i) * exp (ww C x0 j) * (((p : ℝ) + q) * G)) * exp (-b) := by ring
          _ = exp b * exp (-b) := by rw [← hCe, e]
          _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
      calc G * (p : ℝ) ^ n * (q : ℝ) ^ m * |(α n : ℝ) - (β m : ℝ)|
          ≤ G * exp (ww C x0 i) * exp (ww C x0 j) * |(α n : ℝ) - (β m : ℝ)| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ < G * exp (ww C x0 i) * exp (ww C x0 j) * (((p : ℝ) + q) * exp (-b)) :=
            mul_lt_mul_of_pos_left hdiff (by positivity)
        _ = 1 := h2
    have : |N| < 1 := by exact_mod_cast hlt
    exact Int.abs_lt_one_iff.mp this
  have heq : α n = β m := by
    rw [hN0, Int.cast_zero] at hN
    have h : ((p : ℚ) - 1) * ((q : ℚ) - 1) * (p : ℚ) ^ n * (q : ℚ) ^ m ≠ 0 := by
      have a1 : (2 : ℚ) ≤ p := by exact_mod_cast hp
      have a2 : (2 : ℚ) ≤ q := by exact_mod_cast hq
      have b1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
      have b2 : (0 : ℚ) < (q : ℚ) - 1 := by linarith
      have b3 : (0 : ℚ) < p := by linarith
      have b4 : (0 : ℚ) < q := by linarith
      exact (by positivity : (0 : ℚ) < _).ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hN.symm).resolve_left h)
  obtain ⟨z, hz⟩ := common_value hp hq hpq hr (heq ▸ hs)
  have hzr : (α n : ℝ) = z / G := by
    have := congrArg (fun t : ℚ => (t : ℝ)) hz
    push_cast at this
    rw [this, hG]
  have h1 := hdist z
  rw [← hzr] at h1
  have h2 : (p : ℝ) * exp (-b) ≤ (q : ℝ) * exp (-x0) := by
    have : (p : ℝ) ≤ q := by exact_mod_cast hpq'.le
    exact mul_le_mul this (exp_le_exp.mpr (by linarith)) (exp_pos _).le (by positivity)
  exact absurd (lt_of_lt_of_le e1 (le_trans h2 h1)) (lt_irrefl _)

/-! ## The part prime to a finite set of primes -/

/-- `|x| ∏_{r∈S} |x|_r`. -/
noncomputable def nuS (S : Finset ℕ) (x : ℤ) : ℝ :=
  |(x : ℝ)| * ∏ r ∈ S, (padicNorm r (x : ℚ) : ℝ)

/-- The part of `n` composed of the primes of `S`. -/
def sPart (S : Finset ℕ) (n : ℕ) : ℕ := ∏ r ∈ S, r ^ padicValNat r n

lemma sPart_pos {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) (n : ℕ) : 0 < sPart S n :=
  prod_pos (fun r hr => pow_pos (hS r hr).pos _)

lemma sPart_dvd {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) (n : ℕ) : sPart S n ∣ n := by
  revert hS
  induction S using Finset.induction with
  | empty => intro _; simp [sPart]
  | insert a s ha ih =>
    intro hS
    unfold sPart
    rw [prod_insert ha]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ pow_padicValNat_dvd
      (ih (fun r hr => hS r (mem_insert_of_mem hr)))
    refine Nat.Coprime.prod_right (fun b hb => Nat.Coprime.pow _ _ ?_)
    refine (Nat.coprime_primes (hS a (mem_insert_self _ _)) (hS b (mem_insert_of_mem hb))).mpr ?_
    rintro rfl
    exact ha hb

lemma nuS_mul_sPart {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) {a : ℤ} (ha : a ≠ 0) :
    nuS S a * (sPart S a.natAbs : ℝ) = |(a : ℝ)| := by
  have h : ∀ r ∈ S, (padicNorm r (a : ℚ) : ℝ) = ((r : ℝ) ^ padicValNat r a.natAbs)⁻¹ := by
    intro r hr
    have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    rw [padicNorm.eq_zpow_of_nonzero haq, padicValRat.of_int, padicValInt, Rat.cast_zpow,
      Rat.cast_natCast, zpow_neg, zpow_natCast]
  unfold nuS sPart
  rw [prod_congr rfl h, prod_inv_distrib]
  push_cast
  have : (∏ r ∈ S, (r : ℝ) ^ padicValNat r a.natAbs) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun r hr =>
      pow_ne_zero _ (by exact_mod_cast (hS r hr).pos.ne'))
  rw [mul_assoc, inv_mul_cancel₀ this, mul_one]

lemma one_le_nuS {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) {a : ℤ} (ha : a ≠ 0) : 1 ≤ nuS S a := by
  have h := nuS_mul_sPart hS ha
  have hs : (0 : ℝ) < sPart S a.natAbs := by exact_mod_cast sPart_pos hS _
  have hle : (sPart S a.natAbs : ℝ) ≤ |(a : ℝ)| := by
    have : sPart S a.natAbs ≤ a.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr ha) (sPart_dvd hS _)
    have h' : (sPart S a.natAbs : ℝ) ≤ (a.natAbs : ℝ) := by exact_mod_cast this
    rwa [Nat.cast_natAbs, Int.cast_abs] at h'
  rw [← h] at hle
  exact le_of_mul_le_mul_right (by linarith) hs

lemma nuS_le_abs {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) (a : ℤ) : nuS S a ≤ |(a : ℝ)| := by
  by_cases ha : a = 0
  · subst ha; simp [nuS]
  have h := nuS_mul_sPart hS ha
  have h1 : (1 : ℝ) ≤ sPart S a.natAbs := by exact_mod_cast sPart_pos hS _
  have h0 : 0 ≤ nuS S a := le_trans zero_le_one (one_le_nuS hS ha)
  rw [← h]
  exact le_mul_of_one_le_right h0 h1

lemma nuS_mul {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) (a b : ℤ) :
    nuS S (a * b) = nuS S a * nuS S b := by
  have h : ∀ r ∈ S, (padicNorm r ((a * b : ℤ) : ℚ) : ℝ)
      = (padicNorm r (a : ℚ) : ℝ) * (padicNorm r (b : ℚ) : ℝ) := by
    intro r hr
    have : Fact r.Prime := ⟨hS r hr⟩
    push_cast
    rw [padicNorm.mul]
    push_cast
    ring
  unfold nuS
  rw [prod_congr rfl h, prod_mul_distrib]
  push_cast
  rw [abs_mul]
  ring

lemma nuS_pow {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) (a : ℤ) (k : ℕ) :
    nuS S (a ^ k) = nuS S a ^ k := by
  induction k with
  | zero =>
    have : ∀ r ∈ S, (padicNorm r ((1 : ℤ) : ℚ) : ℝ) = 1 := by
      intro r hr
      have : Fact r.Prime := ⟨hS r hr⟩
      rw [Int.cast_one, padicNorm.one, Rat.cast_one]
    rw [pow_zero, pow_zero]
    unfold nuS
    rw [prod_congr rfl this, prod_const_one]
    simp
  | succ k ih => rw [pow_succ, nuS_mul hS, ih, pow_succ]

/-- A number all of whose primes lie in `S` has `nuS = 1`. -/
lemma nuS_unit {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) {l : ℕ} (hl : l ≠ 0)
    (hsub : l.primeFactors ⊆ S) : nuS S (l : ℤ) = 1 := by
  have hs : sPart S l = l := by
    unfold sPart
    rw [← prod_subset hsub]
    · conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hl]
      rw [Finsupp.prod, Nat.support_factorization]
      refine prod_congr rfl (fun r hr => ?_)
      rw [Nat.factorization_def l (Nat.prime_of_mem_primeFactors hr)]
    · intro r hr hnot
      have : ¬ r ∣ l := fun h => hnot (Nat.mem_primeFactors.mpr ⟨hS r hr, h, hl⟩)
      rw [padicValNat.eq_zero_of_not_dvd this, pow_zero]
  have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl
  have h := nuS_mul_sPart hS hl'
  rw [Int.natAbs_natCast, hs] at h
  have e : |((l : ℤ) : ℝ)| = (l : ℝ) := by
    push_cast
    exact abs_of_nonneg (Nat.cast_nonneg l)
  rw [e] at h
  have hl0 : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  exact mul_right_cancel₀ hl0 (by rw [one_mul]; exact h)

/-- Units attached to a number do not count. -/
lemma nuS_attach {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) {p q : ℕ} (hp : nuS S (p : ℤ) = 1)
    (hq : nuS S (q : ℤ) = 1) (c : ℤ) (a b : ℕ) :
    nuS S (c * (p : ℤ) ^ a * (q : ℤ) ^ b) ≤ |(c : ℝ)| := by
  rw [nuS_mul hS, nuS_mul hS, nuS_pow hS, nuS_pow hS, hp, hq, one_pow, one_pow, mul_one, mul_one]
  exact nuS_le_abs hS c

/-! ## The cited theorem as an inequality -/

/-- For a nondegenerate zero sum with a chosen term `i1`, only the part prime to `S` of the
other terms enters. -/
theorem sum_bound {S : Finset ℕ} (hS : ∀ r ∈ S, r.Prime) (hE : EvertseCor1 S) (N : ℕ) {d : ℝ}
    (hd : 0 < d) (hd1 : d < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ι : Type} [DecidableEq ι] (T : Finset ι) (x : ι → ℤ) (i1 : ι),
      i1 ∈ T → 2 ≤ T.card → T.card ≤ N → ∑ i ∈ T, x i = 0 →
      (∀ U ⊆ T, U.Nonempty → U ≠ T → ∑ i ∈ U, x i ≠ 0) →
      ∀ i ∈ T, |(x i : ℝ)| ≤ C * (|(x i1 : ℝ)| * ∏ k ∈ T.erase i1, nuS S (x k)) ^ (1 / d) := by
  classical
  have hfin : ∀ n : ℕ, ∃ M : ℕ, 1 ≤ n → ∀ y : Fin (n + 1) → ℤ, ∑ i, y i = 0 →
      (∀ I : Finset (Fin (n + 1)), I.Nonempty → I ≠ univ → ∑ i ∈ I, y i ≠ 0) →
      univ.gcd y = 1 →
      ∏ i, (|(y i : ℝ)| * ∏ r ∈ S, (padicNorm r (y i : ℚ) : ℝ))
        ≤ 1 * (height y : ℝ) ^ d → height y ≤ M := by
    intro n
    by_cases hn : 1 ≤ n
    · have h := hE n hn 1 d one_pos hd.le hd1
      refine ⟨h.toFinset.sup height, fun _ y h1 h2 h3 h4 => ?_⟩
      refine Finset.le_sup (f := height) ?_
      rw [Set.Finite.mem_toFinset]
      exact ⟨h1, h2, h3, h4⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose M hM using hfin
  set C : ℝ := 1 + ∑ n ∈ range N, (M n : ℝ) with hC
  have hC1 : 1 ≤ C := by
    have : (0 : ℝ) ≤ ∑ n ∈ range N, (M n : ℝ) := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    linarith
  refine ⟨C, hC1, ?_⟩
  intro ι _ T x i1 hi1 h2 hN hsum hsub i hi
  -- every term is non-zero
  have hne0 : ∀ a ∈ T, x a ≠ 0 := by
    intro a ha h0
    refine hsub {a} (singleton_subset_iff.mpr ha) (singleton_nonempty a) ?_ ?_
    · intro h
      have := congrArg Finset.card h
      rw [card_singleton] at this
      omega
    · rw [sum_singleton, h0]
  -- divide by the greatest common divisor
  have hTne : T.Nonempty := ⟨i1, hi1⟩
  set g : ℤ := T.gcd x with hg
  have hg0 : g ≠ 0 := by
    intro h
    exact hne0 i1 hi1 (Finset.gcd_eq_zero_iff.mp h i1 hi1)
  have hgpos : 0 < g := by
    have h : 0 ≤ g := by
      rw [hg, ← Finset.normalize_gcd, ← Int.abs_eq_normalize]; exact abs_nonneg _
    exact lt_of_le_of_ne h (Ne.symm hg0)
  have hdvd : ∀ a ∈ T, g ∣ x a := fun a ha => Finset.gcd_dvd ha
  set y' : ι → ℤ := fun a => x a / g with hy'
  have hxy : ∀ a ∈ T, x a = g * y' a := fun a ha => (Int.mul_ediv_cancel' (hdvd a ha)).symm
  have hgcd : T.gcd y' = 1 := by
    obtain ⟨b, hb, hb0⟩ : ∃ b ∈ T, x b ≠ 0 := ⟨i1, hi1, hne0 i1 hi1⟩
    exact Finset.gcd_div_eq_one hb hb0
  have hsumy : ∑ a ∈ T, y' a = 0 := by
    have : g * ∑ a ∈ T, y' a = 0 := by
      rw [mul_sum, ← sum_congr rfl hxy]; exact hsum
    exact (mul_eq_zero.mp this).resolve_left hg0
  have hsuby : ∀ U ⊆ T, U.Nonempty → U ≠ T → ∑ a ∈ U, y' a ≠ 0 := by
    intro U hU hUne hUT h
    refine hsub U hU hUne hUT ?_
    rw [sum_congr rfl (fun a ha => hxy a (hU ha)), ← mul_sum, h, mul_zero]
  have hy0 : ∀ a ∈ T, y' a ≠ 0 := by
    intro a ha h
    exact hne0 a ha (by rw [hxy a ha, h, mul_zero])
  -- the finiteness statement for the primitive tuple
  have prim : |(y' i : ℝ)| ≤ C * (∏ k ∈ T, nuS S (y' k)) ^ (1 / d) := by
    obtain ⟨n, hn⟩ : ∃ n, T.card = n + 1 := ⟨T.card - 1, by omega⟩
    have hn1 : 1 ≤ n := by omega
    set f : Fin (n + 1) ≃ T := (T.equivFinOfCardEq hn).symm with hf
    set y : Fin (n + 1) → ℤ := fun j => y' (f j) with hy
    set emb : Fin (n + 1) ↪ ι := f.toEmbedding.trans (Function.Embedding.subtype _) with hemb
    have hmap : (univ : Finset (Fin (n + 1))).map emb = T := by
      ext a
      simp only [mem_map, mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        exact (f j).2
      · intro ha
        refine ⟨f.symm ⟨a, ha⟩, ?_⟩
        show ((f (f.symm ⟨a, ha⟩) : T) : ι) = a
        rw [Equiv.apply_symm_apply]
    have hyx : ∀ I : Finset (Fin (n + 1)), ∑ j ∈ I, y j = ∑ a ∈ I.map emb, y' a := by
      intro I
      rw [sum_map]
      rfl
    have h1 : ∑ j, y j = 0 := by rw [hyx, hmap, hsumy]
    have h3 : ∀ I : Finset (Fin (n + 1)), I.Nonempty → I ≠ univ → ∑ j ∈ I, y j ≠ 0 := by
      intro I hI hIu
      rw [hyx]
      refine hsuby _ ?_ (hI.map) ?_
      · rw [← hmap]
        exact map_subset_map.mpr (subset_univ _)
      · intro h
        rw [← hmap] at h
        exact hIu (map_injective emb h)
    have h4 : univ.gcd y = 1 := by
      have hdvd' : univ.gcd y ∣ T.gcd y' := by
        refine Finset.dvd_gcd (fun a ha => ?_)
        have : y (f.symm ⟨a, ha⟩) = y' a := by
          show y' (f (f.symm ⟨a, ha⟩)) = y' a
          rw [Equiv.apply_symm_apply]
        rw [← this]
        exact Finset.gcd_dvd (mem_univ _)
      rw [hgcd] at hdvd'
      rw [← Finset.normalize_gcd]
      exact normalize_eq_one.mpr (isUnit_of_dvd_one hdvd')
    have hprod1 : 1 ≤ ∏ k ∈ T, nuS S (y' k) := by
      refine le_trans (le_of_eq prod_const_one.symm) (prod_le_prod₀ (fun _ _ => zero_le_one) ?_)
      exact fun k hk => one_le_nuS hS (hy0 k hk)
    have hprody : ∏ j, (|(y j : ℝ)| * ∏ r ∈ S, (padicNorm r (y j : ℚ) : ℝ))
        = ∏ k ∈ T, nuS S (y' k) := by
      conv_rhs => rw [← hmap]
      rw [prod_map]
      rfl
    have hxh : |(y' i : ℝ)| ≤ (height y : ℝ) := by
      have : y (f.symm ⟨i, hi⟩) = y' i := by
        show y' (f (f.symm ⟨i, hi⟩)) = y' i
        rw [Equiv.apply_symm_apply]
      rw [← this]
      have h : (y (f.symm ⟨i, hi⟩)).natAbs ≤ height y :=
        Finset.le_sup (f := fun j => (y j).natAbs) (mem_univ _)
      have h' : ((y (f.symm ⟨i, hi⟩)).natAbs : ℝ) ≤ (height y : ℝ) := by exact_mod_cast h
      rwa [Nat.cast_natAbs, Int.cast_abs] at h'
    have hpow1 : 1 ≤ (∏ k ∈ T, nuS S (y' k)) ^ (1 / d) :=
      one_le_rpow hprod1 (by positivity)
    by_cases hex : ∏ j, (|(y j : ℝ)| * ∏ r ∈ S, (padicNorm r (y j : ℚ) : ℝ))
        ≤ 1 * (height y : ℝ) ^ d
    · have hMn := hM n hn1 y h1 h3 h4 hex
      have hnN : n ∈ range N := by rw [mem_range]; omega
      have h5 : (height y : ℝ) ≤ C := by
        have h6 : (height y : ℝ) ≤ (M n : ℝ) := by exact_mod_cast hMn
        have h7 : (M n : ℝ) ≤ ∑ m ∈ range N, (M m : ℝ) :=
          single_le_sum (f := fun m => (M m : ℝ)) (fun _ _ => Nat.cast_nonneg _) hnN
        linarith
      exact le_trans (le_trans hxh h5) (le_mul_of_one_le_right (by linarith) hpow1)
    · rw [one_mul, hprody, not_le] at hex
      have h5 : (height y : ℝ) ≤ (∏ k ∈ T, nuS S (y' k)) ^ (1 / d) := by
        have h6 := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg _) _) hex.le
          (show (0 : ℝ) ≤ 1 / d by positivity)
        rwa [← rpow_mul (Nat.cast_nonneg _), mul_one_div_cancel hd.ne', rpow_one] at h6
      exact le_trans (le_trans hxh h5) (le_mul_of_one_le_left (by linarith) hC1)
  -- put the greatest common divisor back
  have he1 : (1 : ℝ) ≤ 1 / d := by
    rw [le_div_iff₀ hd, one_mul]; exact hd1.le
  set G : ℝ := nuS S g with hG
  set s : ℝ := (sPart S g.natAbs : ℝ) with hs
  have hG1 : 1 ≤ G := one_le_nuS hS hg0
  have hs1 : 1 ≤ s := by rw [hs]; exact_mod_cast sPart_pos hS _
  have hgabs : |(g : ℝ)| = G * s := (nuS_mul_sPart hS hg0).symm
  have hQ : ∀ k ∈ T, 0 ≤ nuS S (y' k) :=
    fun k hk => le_trans zero_le_one (one_le_nuS hS (hy0 k hk))
  have hxk : ∀ k ∈ T, nuS S (x k) = G * nuS S (y' k) := by
    intro k hk
    rw [hxy k hk, nuS_mul hS]
  set R : ℝ := ∏ k ∈ T.erase i1, nuS S (x k) with hR
  have hR0 : 0 ≤ R := prod_nonneg (fun k hk =>
    le_trans zero_le_one (one_le_nuS hS (hne0 k (mem_of_mem_erase hk))))
  set A : ℝ := nuS S (y' i1) with hA
  set B' : ℝ := ∏ k ∈ T.erase i1, nuS S (y' k) with hB'
  have hA0 : 0 ≤ A := hQ i1 hi1
  have hB0 : 0 ≤ B' := prod_nonneg (fun k hk => hQ k (mem_of_mem_erase hk))
  have hsplit : ∏ k ∈ T, nuS S (y' k) = A * B' := (mul_prod_erase T _ hi1).symm
  have hBR : B' ≤ R := by
    refine prod_le_prod₀ (fun k hk => hQ k (mem_of_mem_erase hk)) (fun k hk => ?_)
    rw [hxk k (mem_of_mem_erase hk)]
    exact le_mul_of_one_le_left (hQ k (mem_of_mem_erase hk)) hG1
  -- `s * G * A ≤ |x i1|`
  have hsA : s * (G * A) ≤ |(x i1 : ℝ)| := by
    have hx1 := hne0 i1 hi1
    have h := nuS_mul_sPart hS hx1
    rw [← h, ← hxk i1 hi1, mul_comm s]
    refine mul_le_mul_of_nonneg_left ?_ (le_trans zero_le_one (one_le_nuS hS hx1))
    have hd' : sPart S g.natAbs ∣ sPart S (x i1).natAbs := by
      unfold sPart
      refine prod_dvd_prod_of_dvd _ _ (fun r hr => pow_dvd_pow r ?_)
      have : Fact r.Prime := ⟨hS r hr⟩
      have hab : g.natAbs ∣ (x i1).natAbs := Int.natAbs_dvd_natAbs.mpr (hdvd i1 hi1)
      have h0 : (x i1).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx1
      exact (padicValNat_dvd_iff_le h0).mp (dvd_trans pow_padicValNat_dvd hab)
    rw [hs]
    exact_mod_cast Nat.le_of_dvd (sPart_pos hS _) hd'
  have key : |(g : ℝ)| * (A * B') ^ (1 / d) ≤ (|(x i1 : ℝ)| * R) ^ (1 / d) := by
    have h1 : G * s ≤ (G * s) ^ (1 / d) := by
      have h := rpow_le_rpow_of_exponent_le (one_le_mul_of_one_le_of_one_le hG1 hs1) he1
      rwa [rpow_one] at h
    rw [hgabs]
    refine le_trans (mul_le_mul_of_nonneg_right h1 (rpow_nonneg (mul_nonneg hA0 hB0) _)) ?_
    rw [← mul_rpow (by positivity) (mul_nonneg hA0 hB0)]
    refine rpow_le_rpow (mul_nonneg (by positivity) (mul_nonneg hA0 hB0)) ?_ (by positivity)
    have : G * s * (A * B') = (s * (G * A)) * B' := by ring
    rw [this]
    exact mul_le_mul hsA hBR hB0 (abs_nonneg _)
  have hxi : |(x i : ℝ)| = |(g : ℝ)| * |(y' i : ℝ)| := by
    rw [hxy i hi]; push_cast; rw [abs_mul]
  rw [hxi]
  rw [hsplit] at prim
  calc |(g : ℝ)| * |(y' i : ℝ)| ≤ |(g : ℝ)| * (C * (A * B') ^ (1 / d)) :=
        mul_le_mul_of_nonneg_left prim (abs_nonneg _)
    _ = C * (|(g : ℝ)| * (A * B') ^ (1 / d)) := by ring
    _ ≤ C * (|(x i1 : ℝ)| * R) ^ (1 / d) := mul_le_mul_of_nonneg_left key (by linarith)

/-! ## More than `K` marks in every late window -/

lemma exists_free {K : ℕ} {Mp Mq : Finset ℕ} (hcard : Mp.card + Mq.card ≤ K) (sp sq a h : ℝ)
    (hh : 0 ≤ h) :
    ∃ i : ℕ, i ≤ K ∧
      (∀ n ∈ Mp, ¬ (a + i * h < (n : ℝ) * sp ∧ (n : ℝ) * sp ≤ a + i * h + h)) ∧
      (∀ n ∈ Mq, ¬ (a + i * h < (n : ℝ) * sq ∧ (n : ℝ) * sq ≤ a + i * h + h)) := by
  classical
  by_contra hcon
  have hex : ∀ i : Fin (K + 1), ∃ m : ℕ ⊕ ℕ, m ∈ Mp.disjSum Mq ∧
      a + (i : ℕ) * h < Sum.elim (fun n : ℕ => (n : ℝ) * sp) (fun n : ℕ => (n : ℝ) * sq) m ∧
      Sum.elim (fun n : ℕ => (n : ℝ) * sp) (fun n : ℕ => (n : ℝ) * sq) m
        ≤ a + (i : ℕ) * h + h := by
    intro i
    by_contra hno
    refine hcon ⟨i, by omega, fun n hn hc => hno ⟨Sum.inl n, inl_mem_disjSum.mpr hn, hc⟩,
      fun n hn hc => hno ⟨Sum.inr n, inr_mem_disjSum.mpr hn, hc⟩⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have key : ∀ i j : Fin (K + 1), (i : ℕ) < j → f i = f j → False := by
      intro i j hlt e
      have h1 := (hf i).2.2
      have h2 := (hf j).2.1
      rw [e] at h1
      have h3 : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlt
      have h4 := mul_le_mul_of_nonneg_right h3 hh
      linarith
    rcases Nat.lt_or_gt_of_ne (fun e => hne (Fin.ext e)) with h | h
    · exact key i j h hij
    · exact key j i h hij.symm
  have : (univ : Finset (Fin (K + 1))).card ≤ (Mp.disjSum Mq).card :=
    card_le_card_of_injOn f (fun i _ => (hf i).1) hinj.injOn
  rw [card_univ, Fintype.card_fin, card_disjSum] at this
  omega

set_option maxHeartbeats 4000000 in
/-- **More than `K` marks in `(Y, 13Y/4]`** for all large `Y`. -/
theorem window_marks {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hE : EvertseCor1 (p * q).primeFactors) {ξ : ℝ} (hξ : Irrational ξ)
    {α β : ℕ → ℚ} (hα : Approx p ξ α) (hβ : Approx q ξ β) (K : ℕ) :
    ∃ Y1 : ℝ, 0 < Y1 ∧ ∀ Y, Y1 ≤ Y →
      K + 1 ≤ (marksIn p α Y (13 / 4 * Y)).card + (marksIn q β Y (13 / 4 * Y)).card := by
  classical
  set S := (p * q).primeFactors with hSdef
  have hS : ∀ r ∈ S, r.Prime := fun r hr => Nat.prime_of_mem_primeFactors hr
  have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hup : nuS S (p : ℤ) = 1 :=
    nuS_unit hS (by omega) (Nat.primeFactors_mono (dvd_mul_right p q) hpq0)
  have huq : nuS S (q : ℤ) = 1 :=
    nuS_unit hS (by omega) (Nat.primeFactors_mono (dvd_mul_left q p) hpq0)
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hLp : 0 < log (p : ℝ) := log_pos (by linarith)
  have hLq : 0 < log (q : ℝ) := log_pos (by linarith)
  set G : ℝ := ((p : ℝ) - 1) * ((q : ℝ) - 1) with hG
  have hG1 : 1 ≤ G := by
    have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have h2 : (1 : ℝ) ≤ (q : ℝ) - 1 := by linarith
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hG0 : 0 < G := by linarith
  set E : ℝ := G ^ 2 with hEE
  have hE1 : 1 ≤ E := one_le_pow₀ hG1
  set Cc : ℝ := log (G * ((p : ℝ) + q)) with hCc
  have hCcpos : 0 < G * ((p : ℝ) + q) := mul_pos hG0 (by linarith)
  have hCc0 : 0 ≤ Cc := log_nonneg (one_le_mul_of_one_le_of_one_le hG1 (by linarith))
  -- distance of `ξ` from the fractions with denominator `G`
  obtain ⟨δ, hδ, hdist⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℤ, δ ≤ |ξ - z / G| := by
    set k : ℕ := (p - 1) * (q - 1) with hk
    have hkG : (k : ℝ) = G := by
      rw [hk, hG]
      push_cast [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_sub (show 1 ≤ q by omega)]
      ring
    have hk0 : k ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have hirr : Irrational (ξ * k) := hξ.mul_natCast hk0
    have hpos : 0 < |ξ * k - round (ξ * k)| := by
      refine abs_pos.mpr (sub_ne_zero.mpr ?_)
      exact hirr.ne_int _
    refine ⟨|ξ * k - round (ξ * k)| / G, div_pos hpos hG0, fun z => ?_⟩
    have e : ξ - z / G = (ξ * k - z) / G := by rw [hkG]; field_simp
    rw [e, abs_div, abs_of_pos hG0]
    exact div_le_div_of_nonneg_right (round_le _ _) hG0.le
  set eps : ℝ := 1 / (26 * ((K : ℝ) + 1)) with heps
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have heps0 : 0 < eps := by positivity
  have heps26 : eps ≤ 1 / 26 := by
    rw [heps]
    have h1 : (26 : ℝ) ≤ 26 * ((K : ℝ) + 1) := by
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      linarith
    exact one_div_le_one_div_of_le (by norm_num) h1
  set d : ℝ := 1 / (1 + eps) with hd
  have hd0 : 0 < d := by positivity
  have hd1 : d < 1 := by
    rw [hd, div_lt_one (by positivity)]; linarith
  have hdinv : 1 / d = 1 + eps := by rw [hd, one_div_one_div]
  obtain ⟨C, hC1, hsb⟩ := sum_bound hS hE (K + 3) hd0 hd1
  have hlC : 0 ≤ log C := log_nonneg hC1
  have hlE : 0 ≤ log E := log_nonneg hE1
  set A : ℝ := log C + (1 + eps) * (K * log E) + (1 + 2 * eps) * Cc + log p + log q with hA
  have hA0 : 0 ≤ A := by positivity
  set qq : ℝ := (q : ℝ) + p with hqq
  set Y1 : ℝ := 1 + 8 * ((K : ℝ) + 1) * (A + 1) + 4 * ((K : ℝ) + 1) * (log p + log q)
    + (|log (qq / δ)| + 1) with hY1
  have hY1pos : 0 < Y1 := by positivity
  refine ⟨Y1, hY1pos, fun Y hY => ?_⟩
  have hY0 : 0 < Y := lt_of_lt_of_le hY1pos hY
  have hYa : 8 * ((K : ℝ) + 1) * (A + 1) ≤ Y := by
    have : 0 ≤ 4 * ((K : ℝ) + 1) * (log p + log q) + (|log (qq / δ)| + 1) := by positivity
    linarith
  have hYb : 4 * ((K : ℝ) + 1) * (log p + log q) ≤ Y := by
    have : 0 ≤ 8 * ((K : ℝ) + 1) * (A + 1) + (|log (qq / δ)| + 1) := by positivity
    linarith
  have hYc : |log (qq / δ)| < Y := by
    have : 0 ≤ 8 * ((K : ℝ) + 1) * (A + 1) + 4 * ((K : ℝ) + 1) * (log p + log q) := by positivity
    linarith
  by_contra hcon
  rw [not_le, Nat.lt_succ_iff] at hcon
  set Mp := marksIn p α Y (13 / 4 * Y) with hMp
  set Mq := marksIn q β Y (13 / 4 * Y) with hMq
  have hX0 : 0 ≤ 13 / 4 * Y := by positivity
  set h : ℝ := Y / (4 * ((K : ℝ) + 1)) with hh
  have hh0 : 0 < h := div_pos hY0 (by positivity)
  have hhY : (K : ℝ) * h + h = Y / 4 := by
    rw [hh]; field_simp
  -- two free stretches
  obtain ⟨i0, hi0, f0p, f0q⟩ := exists_free hcon (log p) (log q) Y h hh0.le
  obtain ⟨i1, hi1, f1p, f1q⟩ := exists_free hcon (log p) (log q) (3 * Y) h hh0.le
  set c0 : ℝ := Y + i0 * h with hc0
  set c1 : ℝ := 3 * Y + i1 * h with hc1
  have hih : ∀ i : ℕ, i ≤ K → 0 ≤ (i : ℝ) * h ∧ (i : ℝ) * h + h ≤ Y / 4 := by
    intro i hi
    have : (i : ℝ) ≤ K := by exact_mod_cast hi
    have := mul_le_mul_of_nonneg_right this hh0.le
    exact ⟨mul_nonneg (Nat.cast_nonneg _) hh0.le, by linarith⟩
  have c0lo : Y ≤ c0 := by have := (hih i0 hi0).1; linarith
  have c0hi : c0 + h ≤ 5 / 4 * Y := by have := (hih i0 hi0).2; linarith
  have c1lo : 3 * Y ≤ c1 := by have := (hih i1 hi1).1; linarith
  have c1hi : c1 + h ≤ 13 / 4 * Y := by have := (hih i1 hi1).2; linarith
  -- the rationals and the integer at a free stretch
  have at_free : ∀ c : ℝ, Y ≤ c → c + h ≤ 13 / 4 * Y →
      (∀ n ∈ Mp, ¬ (c < (n : ℝ) * log p ∧ (n : ℝ) * log p ≤ c + h)) →
      (∀ n ∈ Mq, ¬ (c < (n : ℝ) * log q ∧ (n : ℝ) * log q ≤ c + h)) →
      ∃ N : ℤ, (N : ℚ) = ((p : ℚ) - 1) * ((q : ℚ) - 1) * (p : ℚ) ^ ⌊c / log p⌋₊
          * (q : ℚ) ^ ⌊c / log q⌋₊ * (α ⌊c / log p⌋₊ - β ⌊c / log q⌋₊) ∧
        N ≠ 0 ∧ log |(N : ℝ)| ≤ Cc + c - h := by
    intro c hcY hcX hfp hfq
    have hc00 : 0 ≤ c := le_trans hY0.le hcY
    have free : ∀ (l : ℕ) (hl : 2 ≤ l) (γ : ℕ → ℚ) (hγ : Approx l ξ γ),
        (∀ n ∈ marksIn l γ Y (13 / 4 * Y),
          ¬ (c < (n : ℝ) * log l ∧ (n : ℝ) * log l ≤ c + h)) →
        |ξ - (γ ⌊c / log l⌋₊ : ℝ)| < l * exp (-(c + h)) := by
      intro l hl γ hγ hf
      refine free_close hl hγ hc00 (by linarith) (fun n hn h1 h2 => ?_)
      by_contra hne
      exact hf n ((mem_marksIn hl hX0).mpr ⟨hn, hne, lt_of_le_of_lt hcY h1, le_trans h2 hcX⟩)
        ⟨h1, h2⟩
    have e1 := free p hp α hα hfp
    have e2 := free q hq β hβ hfq
    set n := ⌊c / log p⌋₊ with hn
    set m := ⌊c / log q⌋₊ with hm
    have pn : (p : ℝ) ^ n ≤ exp c := (floor_pos_bounds hp hc00).2.2
    have qm : (q : ℝ) ^ m ≤ exp c := (floor_pos_bounds hq hc00).2.2
    obtain ⟨r, hr⟩ := hα.num n
    obtain ⟨s, hs⟩ := hβ.num m
    obtain ⟨N, hN⟩ := anchor_int hp hq hr hs
    have hN0 : N ≠ 0 := by
      intro h0
      have heq : α n = β m := by
        rw [h0, Int.cast_zero] at hN
        have h' : ((p : ℚ) - 1) * ((q : ℚ) - 1) * (p : ℚ) ^ n * (q : ℚ) ^ m ≠ 0 := by
          have a1 : (2 : ℚ) ≤ p := by exact_mod_cast hp
          have a2 : (2 : ℚ) ≤ q := by exact_mod_cast hq
          have b1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
          have b2 : (0 : ℚ) < (q : ℚ) - 1 := by linarith
          have b3 : (0 : ℚ) < p := by linarith
          have b4 : (0 : ℚ) < q := by linarith
          exact (by positivity : (0 : ℚ) < _).ne'
        exact sub_eq_zero.mp ((mul_eq_zero.mp hN.symm).resolve_left h')
      obtain ⟨z, hz⟩ := common_value hp hq hpq hr (heq ▸ hs)
      have hzr : (α n : ℝ) = z / G := by
        have := congrArg (fun t : ℚ => (t : ℝ)) hz
        push_cast at this
        rw [this, hG]
      have h1 := hdist z
      rw [← hzr] at h1
      have h2 : (p : ℝ) * exp (-(c + h)) < δ := by
        have hqq0 : 0 < qq := by positivity
        have h3 : log (qq / δ) < c + h :=
          lt_of_le_of_lt (le_abs_self _) (lt_of_lt_of_le hYc (by linarith))
        have h4 : qq / δ < exp (c + h) := by
          rw [← exp_log (div_pos hqq0 hδ)]
          exact exp_lt_exp.mpr h3
        have h5 : (p : ℝ) < δ * exp (c + h) := by
          rw [div_lt_iff₀ hδ, mul_comm] at h4
          have : (p : ℝ) ≤ qq := by
            rw [hqq]
            have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
            linarith
          linarith
        rw [exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (exp_pos _)]
        exact h5
      linarith
    refine ⟨N, hN, hN0, ?_⟩
    have hNr : (N : ℝ) = G * (p : ℝ) ^ n * (q : ℝ) ^ m * ((α n : ℝ) - (β m : ℝ)) := by
      have := congrArg (fun t : ℚ => (t : ℝ)) hN
      push_cast at this
      rw [this, hG]
    have hdiff : |(α n : ℝ) - (β m : ℝ)| ≤ ((p : ℝ) + q) * exp (-(c + h)) := by
      have : (α n : ℝ) - (β m : ℝ) = (ξ - (β m : ℝ)) - (ξ - (α n : ℝ)) := by ring
      rw [this]
      refine le_trans (abs_sub _ _) ?_
      linarith
    have hbound : |(N : ℝ)| ≤ G * ((p : ℝ) + q) * exp (c - h) := by
      have hGpq : 0 < G * (p : ℝ) ^ n * (q : ℝ) ^ m := by positivity
      rw [hNr, abs_mul, abs_of_pos hGpq]
      have h1 : G * (p : ℝ) ^ n * (q : ℝ) ^ m ≤ G * exp c * exp c := by gcongr
      refine le_trans (mul_le_mul h1 hdiff (abs_nonneg _) (by positivity)) (le_of_eq ?_)
      have e : exp c * exp c * exp (-(c + h)) = exp (c - h) := by
        rw [← exp_add, ← exp_add]; ring_nf
      rw [← e]; ring
    have hNpos : 0 < |(N : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hN0)
    have := log_le_log hNpos hbound
    rw [log_mul hCcpos.ne' (exp_ne_zero _), log_exp, ← hCc] at this
    linarith
  obtain ⟨N0, hN0e, hN0, hN0l⟩ := at_free c0 c0lo (by linarith) f0p f0q
  obtain ⟨N1, hN1e, hN1, hN1l⟩ := at_free c1 (by linarith) c1hi f1p f1q
  set n0 := ⌊c0 / log p⌋₊ with hn0
  set m0 := ⌊c0 / log q⌋₊ with hm0
  set n1 := ⌊c1 / log p⌋₊ with hn1
  set m1 := ⌊c1 / log q⌋₊ with hm1
  have c00 : 0 ≤ c0 := le_trans hY0.le c0lo
  have c10 : 0 ≤ c1 := by linarith
  have hc01 : c0 ≤ c1 := by linarith
  have hn01 : n0 ≤ n1 := Nat.floor_mono (div_le_div_of_nonneg_right hc01 hLp.le)
  have hm01 : m0 ≤ m1 := Nat.floor_mono (div_le_div_of_nonneg_right hc01 hLq.le)
  -- the marks between the two stretches
  set J := (Ioc n0 n1).filter (fun j => α j ≠ α (j - 1)) with hJ
  set J' := (Ioc m0 m1).filter (fun j => β j ≠ β (j - 1)) with hJ'
  have between : ∀ (l : ℕ) (hl : 2 ≤ l) (γ : ℕ → ℚ),
      (Ioc ⌊c0 / log l⌋₊ ⌊c1 / log l⌋₊).filter (fun j => γ j ≠ γ (j - 1))
        ⊆ marksIn l γ Y (13 / 4 * Y) := by
    intro l hl γ j hj
    have hL : 0 < log (l : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < l))
    rw [mem_filter, mem_Ioc] at hj
    rw [mem_marksIn hl hX0]
    refine ⟨by omega, hj.2, ?_, ?_⟩
    · have h1 := (floor_pos_bounds hl c00).2.1
      have h2 : (⌊c0 / log l⌋₊ : ℝ) + 1 ≤ j := by exact_mod_cast hj.1.1
      exact lt_of_le_of_lt c0lo (lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_right h2 hL.le))
    · have h1 := (floor_pos_bounds hl c10).1
      have h2 : (j : ℝ) ≤ ⌊c1 / log l⌋₊ := by exact_mod_cast hj.1.2
      exact le_trans (mul_le_mul_of_nonneg_right h2 hL.le)
        (le_trans h1 (by linarith))
  have hJcard : J.card + J'.card ≤ K :=
    le_trans (add_le_add (card_le_card (between p hp α)) (card_le_card (between q hq β))) hcon
  -- the numerators of the differences
  have hstep : ∀ (l : ℕ) (γ : ℕ → ℚ) (hγ : Approx l ξ γ), ∃ e : ℕ → ℤ, ∀ j, 1 ≤ j →
      |(e j : ℝ)| ≤ ((l : ℝ) - 1) ^ 2 ∧
        γ j - γ (j - 1) = e j / (((l : ℚ) - 1) * (l : ℚ) ^ j) := by
    intro l γ hγ
    have : ∀ j, ∃ e : ℤ, 1 ≤ j → |(e : ℝ)| ≤ ((l : ℝ) - 1) ^ 2 ∧
        γ j - γ (j - 1) = e / (((l : ℚ) - 1) * (l : ℚ) ^ j) := by
      intro j
      by_cases hj : 1 ≤ j
      · obtain ⟨e, he⟩ := hγ.step j hj
        exact ⟨e, fun _ => he⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose e he using this
    exact ⟨e, he⟩
  obtain ⟨ep, hep⟩ := hstep p α hα
  obtain ⟨eq', heq'⟩ := hstep q β hβ
  -- the tuple
  set x : Fin 2 ⊕ (ℕ ⊕ ℕ) → ℤ := Sum.elim
    (fun i : Fin 2 => if i = 0 then N0 * (p : ℤ) ^ (n1 - n0) * (q : ℤ) ^ (m1 - m0) else -N1)
    (Sum.elim
      (fun j => ep j * ((q : ℤ) - 1) * (p : ℤ) ^ (n1 - j) * (q : ℤ) ^ m1)
      (fun k => -(eq' k * ((p : ℤ) - 1)) * (p : ℤ) ^ n1 * (q : ℤ) ^ (m1 - k))) with hx
  set a0 : Fin 2 ⊕ (ℕ ⊕ ℕ) := Sum.inl 0 with ha0
  set a1 : Fin 2 ⊕ (ℕ ⊕ ℕ) := Sum.inl 1 with ha1
  set T0 : Finset (Fin 2 ⊕ (ℕ ⊕ ℕ)) := (univ : Finset (Fin 2)).disjSum (J.disjSum J') with hT0
  have xa0 : x a0 = N0 * (p : ℤ) ^ (n1 - n0) * (q : ℤ) ^ (m1 - m0) := by simp [hx, ha0]
  have xa1 : x a1 = -N1 := by simp [hx, ha1]
  have hp1q : (1 : ℤ) ≤ (q : ℤ) - 1 := by
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq
    omega
  have hp1p : (1 : ℤ) ≤ (p : ℤ) - 1 := by
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp
    omega
  have p0q : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have q0q : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have p1q : (p : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp
    intro e; linarith
  have q1q : (q : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    intro e; linarith
  set Q : ℚ := ((p : ℚ) - 1) * ((q : ℚ) - 1) * (p : ℚ) ^ n1 * (q : ℚ) ^ m1 with hQdef
  have hjn : ∀ j ∈ J, 1 ≤ j ∧ j ≤ n1 ∧ α j ≠ α (j - 1) := by
    intro j hj
    rw [hJ, mem_filter, mem_Ioc] at hj
    exact ⟨by omega, hj.1.2, hj.2⟩
  have hkm : ∀ k ∈ J', 1 ≤ k ∧ k ≤ m1 ∧ β k ≠ β (k - 1) := by
    intro k hk
    rw [hJ', mem_filter, mem_Ioc] at hk
    exact ⟨by omega, hk.1.2, hk.2⟩
  have vp : ∀ j ∈ J, (x (Sum.inr (Sum.inl j)) : ℚ) = Q * (α j - α (j - 1)) := by
    intro j hj
    obtain ⟨hj1, hjn1, _⟩ := hjn j hj
    have e := (hep j hj1).2
    have hs : (p : ℚ) ^ n1 = (p : ℚ) ^ (n1 - j) * (p : ℚ) ^ j := by
      rw [← pow_add]; congr 1; omega
    simp only [hx, Sum.elim_inr, Sum.elim_inl]
    push_cast
    rw [e, hQdef, hs]
    field_simp
  have vq : ∀ k ∈ J', (x (Sum.inr (Sum.inr k)) : ℚ) = -(Q * (β k - β (k - 1))) := by
    intro k hk
    obtain ⟨hk1, hkm1, _⟩ := hkm k hk
    have e := (heq' k hk1).2
    have hs : (q : ℚ) ^ m1 = (q : ℚ) ^ (m1 - k) * (q : ℚ) ^ k := by
      rw [← pow_add]; congr 1; omega
    simp only [hx, Sum.elim_inr]
    push_cast
    rw [e, hQdef, hs]
    field_simp
  have v0 : (x a0 : ℚ) = Q * (α n0 - β m0) := by
    have hs : (p : ℚ) ^ n1 = (p : ℚ) ^ (n1 - n0) * (p : ℚ) ^ n0 := by
      rw [← pow_add]; congr 1; omega
    have ht : (q : ℚ) ^ m1 = (q : ℚ) ^ (m1 - m0) * (q : ℚ) ^ m0 := by
      rw [← pow_add]; congr 1; omega
    rw [xa0]
    push_cast
    rw [hN0e, hQdef, hs, ht]
    ring
  have v1 : (x a1 : ℚ) = -(Q * (α n1 - β m1)) := by
    rw [xa1]
    push_cast
    rw [hN1e, hQdef]
  have hsum0 : ∑ i ∈ T0, x i = 0 := by
    have h : ((∑ i ∈ T0, x i : ℤ) : ℚ) = 0 := by
      rw [hT0, sum_disjSum, sum_disjSum, Fin.sum_univ_two, ← ha0, ← ha1]
      push_cast
      rw [v0, v1, sum_congr rfl vp, sum_congr rfl vq, sum_neg_distrib, ← mul_sum, ← mul_sum,
        ← telescope α hn01, ← telescope β hm01]
      ring
    exact_mod_cast h
  -- a smallest vanishing subsum containing the second anchor
  have ha1T : a1 ∈ T0 := by
    rw [hT0, ha1]
    exact inl_mem_disjSum.mpr (mem_univ _)
  set F := T0.powerset.filter (fun T => a1 ∈ T ∧ ∑ i ∈ T, x i = 0) with hF
  have hFne : F.Nonempty :=
    ⟨T0, by rw [hF, mem_filter, mem_powerset]; exact ⟨subset_rfl, ha1T, hsum0⟩⟩
  obtain ⟨T, hTF, hmin⟩ := F.exists_min_image card hFne
  rw [hF, mem_filter, mem_powerset] at hTF
  obtain ⟨hTsub, ha1m, hTsum⟩ := hTF
  have hnd : ∀ U ⊆ T, U.Nonempty → U ≠ T → ∑ i ∈ U, x i ≠ 0 := by
    intro U hU hUne hUT h0
    have hss : U.card < T.card := card_lt_card ⟨hU, fun h => hUT (Subset.antisymm hU h)⟩
    by_cases h1 : a1 ∈ U
    · have := hmin U (by rw [hF, mem_filter, mem_powerset]; exact ⟨hU.trans hTsub, h1, h0⟩)
      omega
    · have hmem : T \ U ∈ F := by
        rw [hF, mem_filter, mem_powerset]
        refine ⟨(sdiff_subset).trans hTsub, mem_sdiff.mpr ⟨ha1m, h1⟩, ?_⟩
        have h := sum_sdiff (f := x) hU
        rw [h0, add_zero, hTsum] at h
        exact h
      have h2 := hmin _ hmem
      have h3 : (T \ U).card < T.card := by
        rw [card_sdiff_of_subset hU]
        have := hUne.card_pos
        have := card_le_card hU
        omega
      omega
  have hx1 : x a1 ≠ 0 := by rw [xa1]; exact neg_ne_zero.mpr hN1
  have hT2 : 2 ≤ T.card := by
    by_contra hlt
    have h1 : T.card ≤ 1 := by omega
    have : T = {a1} :=
      eq_singleton_iff_unique_mem.mpr ⟨ha1m, fun b hb => card_le_one.mp h1 b hb a1 ha1m⟩
    rw [this, sum_singleton] at hTsum
    exact hx1 hTsum
  have hTK : T.card ≤ K + 3 := by
    refine le_trans (card_le_card hTsub) ?_
    rw [hT0, card_disjSum, card_disjSum, card_univ, Fintype.card_fin]
    omega
  have hbound := hsb T x a1 ha1m hT2 hTK hTsum hnd
  -- the parts prime to `pq`
  have hx0 : x a0 ≠ 0 := by
    rw [xa0]
    exact mul_ne_zero (mul_ne_zero hN0 (pow_ne_zero _ (by exact_mod_cast (by omega : p ≠ 0))))
      (pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0)))
  have hdig : ∀ a ∈ T0, a ≠ a0 → a ≠ a1 →
      x a ≠ 0 ∧ nuS S (x a) ≤ E ∧
        (exp c1 / p ≤ |(x a : ℝ)| ∨ exp c1 / q ≤ |(x a : ℝ)|) := by
    intro a ha h0 h1
    have pn1 : exp c1 / p ≤ (p : ℝ) ^ n1 := by
      have h := (floor_pos_bounds hp c10).2.1
      rw [← hn1] at h
      have e : (p : ℝ) ^ n1 * p = exp (((n1 : ℝ) + 1) * log p) := by
        rw [← pow_succ, ← exp_log (pow_pos (by linarith : (0 : ℝ) < p) (n1 + 1)), log_pow]
        push_cast; ring_nf
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < p), e]
      exact (exp_lt_exp.mpr h).le
    have qm1 : exp c1 / q ≤ (q : ℝ) ^ m1 := by
      have h := (floor_pos_bounds hq c10).2.1
      rw [← hm1] at h
      have e : (q : ℝ) ^ m1 * q = exp (((m1 : ℝ) + 1) * log q) := by
        rw [← pow_succ, ← exp_log (pow_pos (by linarith : (0 : ℝ) < q) (m1 + 1)), log_pow]
        push_cast; ring_nf
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < q), e]
      exact (exp_lt_exp.mpr h).le
    have hsmall : ∀ (l l' : ℕ), 2 ≤ l → 2 ≤ l' → ∀ e : ℤ, |(e : ℝ)| ≤ ((l : ℝ) - 1) ^ 2 →
        ((l : ℝ) - 1) ^ 2 * ((l' : ℝ) - 1) ≤ (((l : ℝ) - 1) * ((l' : ℝ) - 1)) ^ 2 →
        |((e * ((l' : ℤ) - 1) : ℤ) : ℝ)| ≤ (((l : ℝ) - 1) * ((l' : ℝ) - 1)) ^ 2 := by
      intro l l' _ hl' e he hle
      have : (2 : ℝ) ≤ l' := by exact_mod_cast hl'
      push_cast
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (l' : ℝ) - 1)]
      exact le_trans (mul_le_mul_of_nonneg_right he (by linarith)) hle
    have hsq : ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → u ^ 2 * v ≤ (u * v) ^ 2 := by
      intro u v hu hv
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg u)
      rw [sq]
      exact le_mul_of_one_le_left (by linarith) hv
    have u1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have u2 : (1 : ℝ) ≤ (q : ℝ) - 1 := by linarith
    rcases a with i | j | k
    · fin_cases i
      · exact absurd rfl h0
      · exact absurd rfl h1
    · have hj : j ∈ J := by
        rw [hT0] at ha
        exact inl_mem_disjSum.mp (inr_mem_disjSum.mp ha)
      obtain ⟨hj1, _, hne⟩ := hjn j hj
      have he := hep j hj1
      have he0 : ep j ≠ 0 := by
        intro h
        have h2 := he.2
        rw [h, Int.cast_zero, zero_div, sub_eq_zero] at h2
        exact hne h2
      have xv : x (Sum.inr (Sum.inl j))
          = (ep j * ((q : ℤ) - 1)) * (p : ℤ) ^ (n1 - j) * (q : ℤ) ^ m1 := by
        simp only [hx, Sum.elim_inr, Sum.elim_inl]
      have hc0' : ep j * ((q : ℤ) - 1) ≠ 0 := mul_ne_zero he0 (by omega)
      refine ⟨?_, ?_, Or.inr ?_⟩
      · rw [xv]
        exact mul_ne_zero (mul_ne_zero hc0' (pow_ne_zero _ (by exact_mod_cast (by omega : p ≠ 0))))
          (pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0)))
      · rw [xv]
        refine le_trans (nuS_attach hS hup huq _ _ _) ?_
        rw [hEE, hG]
        exact hsmall p q hp hq _ he.1 (hsq _ _ u1 u2)
      · rw [xv]
        refine le_trans qm1 ?_
        push_cast
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ m1)]
        refine le_mul_of_one_le_left (by positivity) ?_
        have h1c : (1 : ℤ) ≤ |ep j * ((q : ℤ) - 1) * (p : ℤ) ^ (n1 - j)| :=
          Int.one_le_abs (mul_ne_zero hc0' (pow_ne_zero _ (by exact_mod_cast (by omega : p ≠ 0))))
        exact_mod_cast h1c
    · have hk : k ∈ J' := by
        rw [hT0] at ha
        exact inr_mem_disjSum.mp (inr_mem_disjSum.mp ha)
      obtain ⟨hk1, _, hne⟩ := hkm k hk
      have he := heq' k hk1
      have he0 : eq' k ≠ 0 := by
        intro h
        have h2 := he.2
        rw [h, Int.cast_zero, zero_div, sub_eq_zero] at h2
        exact hne h2
      have xv : x (Sum.inr (Sum.inr k))
          = (-(eq' k * ((p : ℤ) - 1))) * (p : ℤ) ^ n1 * (q : ℤ) ^ (m1 - k) := by
        simp only [hx, Sum.elim_inr]
      have hc0' : -(eq' k * ((p : ℤ) - 1)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero he0 (by omega))
      refine ⟨?_, ?_, Or.inl ?_⟩
      · rw [xv]
        exact mul_ne_zero (mul_ne_zero hc0' (pow_ne_zero _ (by exact_mod_cast (by omega : p ≠ 0))))
          (pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0)))
      · rw [xv]
        refine le_trans (nuS_attach hS hup huq _ _ _) ?_
        have h := hsmall q p hq hp _ he.1 (hsq _ _ u2 u1)
        rw [hEE, hG, mul_comm ((p : ℝ) - 1)]
        rwa [Int.cast_neg, abs_neg]
      · rw [xv]
        refine le_trans pn1 ?_
        have e : (-(eq' k * ((p : ℤ) - 1))) * (p : ℤ) ^ n1 * (q : ℤ) ^ (m1 - k)
            = (-(eq' k * ((p : ℤ) - 1)) * (q : ℤ) ^ (m1 - k)) * (p : ℤ) ^ n1 := by ring
        rw [e]
        push_cast
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ n1)]
        refine le_mul_of_one_le_left (by positivity) ?_
        have h1c : (1 : ℤ) ≤ |-(eq' k * ((p : ℤ) - 1)) * (q : ℤ) ^ (m1 - k)| :=
          Int.one_le_abs (mul_ne_zero hc0' (pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))))
        exact_mod_cast h1c
  have hxne : ∀ a ∈ T, x a ≠ 0 := by
    intro a ha
    by_cases h0 : a = a0
    · rw [h0]; exact hx0
    by_cases h1 : a = a1
    · rw [h1]; exact hx1
    exact (hdig a (hTsub ha) h0 h1).1
  have hN1abs : |(x a1 : ℝ)| = |(N1 : ℝ)| := by rw [xa1]; push_cast; rw [abs_neg]
  have hN1pos : 0 < |(N1 : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hN1)
  have hN0pos : 0 < |(N0 : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hN0)
  have hnu0 : ∀ a ∈ T, 0 ≤ nuS S (x a) :=
    fun a ha => le_trans zero_le_one (one_le_nuS hS (hxne a ha))
  -- the product over the digit terms
  have hprodD : ∀ U ⊆ T.erase a1, a0 ∉ U → ∏ a ∈ U, nuS S (x a) ≤ E ^ K := by
    intro U hU h0
    have hmem : ∀ a ∈ U, a ∈ T0 ∧ a ≠ a0 ∧ a ≠ a1 := by
      intro a ha
      have h := mem_erase.mp (hU ha)
      exact ⟨hTsub h.2, fun e => h0 (e ▸ ha), h.1⟩
    have hsubD : U ⊆ (∅ : Finset (Fin 2)).disjSum (J.disjSum J') := by
      intro a ha
      obtain ⟨h1, h2, h3⟩ := hmem a ha
      rcases a with i | y
      · fin_cases i
        · exact absurd rfl h2
        · exact absurd rfl h3
      · rw [hT0] at h1
        exact inr_mem_disjSum.mpr (inr_mem_disjSum.mp h1)
    have hcardU : U.card ≤ K := by
      refine le_trans (card_le_card hsubD) ?_
      rw [card_disjSum, card_disjSum, card_empty, zero_add]
      exact hJcard
    have h1 : ∏ a ∈ U, nuS S (x a) ≤ ∏ _a ∈ U, E := by
      refine prod_le_prod₀ (fun a ha => ?_) (fun a ha => ?_)
      · exact hnu0 a (mem_of_mem_erase (hU ha))
      · exact (hdig a (hmem a ha).1 (hmem a ha).2.1 (hmem a ha).2.2).2.1
    rw [prod_const] at h1
    exact le_trans h1 (pow_le_pow_right₀ hE1 hcardU)
  have hexp : ∀ z : ℝ, 0 < z → (z * E ^ K) ^ (1 + eps) = exp ((1 + eps) * (log z + K * log E)) := by
    intro z hz
    have hEK : (0 : ℝ) < E ^ K := pow_pos (by linarith) _
    rw [rpow_def_of_pos (mul_pos hz hEK), log_mul hz.ne' hEK.ne', log_pow, mul_comm]
  have hlogp : log (p : ℝ) ≤ log p + log q := by linarith
  have hlogq : log (q : ℝ) ≤ log p + log q := by linarith
  have hC0 : 0 < C := by linarith
  have hAeps : 0 ≤ eps * Cc := mul_nonneg heps0.le hCc0
  have hKlE : 0 ≤ (K : ℝ) * log E := mul_nonneg (Nat.cast_nonneg _) hlE
  have heh : 0 ≤ eps * h := mul_nonneg heps0.le hh0.le
  by_cases h0T : a0 ∈ T
  · -- the first anchor is present
    have hb := hbound a0 h0T
    rw [hdinv, hN1abs] at hb
    have ha0e : a0 ∈ T.erase a1 := mem_erase.mpr ⟨by rw [ha0, ha1]; simp, h0T⟩
    have hsplit : ∏ a ∈ T.erase a1, nuS S (x a)
        = nuS S (x a0) * ∏ a ∈ (T.erase a1).erase a0, nuS S (x a) :=
      (mul_prod_erase _ _ ha0e).symm
    have hnua0 : nuS S (x a0) ≤ |(N0 : ℝ)| := by
      rw [xa0]; exact nuS_attach hS hup huq _ _ _
    have hrest : ∏ a ∈ (T.erase a1).erase a0, nuS S (x a) ≤ E ^ K :=
      hprodD _ (erase_subset _ _) (notMem_erase _ _)
    have hrest0 : 0 ≤ ∏ a ∈ (T.erase a1).erase a0, nuS S (x a) :=
      prod_nonneg (fun a ha => hnu0 a (mem_of_mem_erase (mem_of_mem_erase ha)))
    have hP : ∏ a ∈ T.erase a1, nuS S (x a) ≤ |(N0 : ℝ)| * E ^ K := by
      rw [hsplit]
      exact mul_le_mul hnua0 hrest hrest0 (abs_nonneg _)
    have hP0 : 0 ≤ ∏ a ∈ T.erase a1, nuS S (x a) :=
      prod_nonneg (fun a ha => hnu0 a (mem_of_mem_erase ha))
    have hb2 : |(x a0 : ℝ)| ≤ C * (|(N1 : ℝ)| * |(N0 : ℝ)| * E ^ K) ^ (1 + eps) := by
      refine le_trans hb (mul_le_mul_of_nonneg_left ?_ hC0.le)
      refine rpow_le_rpow (mul_nonneg (abs_nonneg _) hP0) ?_ (by linarith)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hP (abs_nonneg _)
    rw [hexp _ (mul_pos hN1pos hN0pos), log_mul hN1pos.ne' hN0pos.ne'] at hb2
    have hxa0 : |(x a0 : ℝ)|
        = exp (log |(N0 : ℝ)| + ((n1 - n0 : ℕ) : ℝ) * log p + ((m1 - m0 : ℕ) : ℝ) * log q) := by
      have pp : (0 : ℝ) < p := by linarith
      have qp : (0 : ℝ) < q := by linarith
      rw [exp_add, exp_add, exp_log hN0pos, ← log_pow, ← log_pow,
        exp_log (pow_pos pp _), exp_log (pow_pos qp _), xa0]
      push_cast
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ (n1 - n0)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ (m1 - m0))]
    rw [hxa0, ← exp_log hC0, ← exp_add, exp_le_exp] at hb2
    have hn1l := (floor_pos_bounds hp c10).2.1
    have hn0l := (floor_pos_bounds hp c00).1
    have hm1l := (floor_pos_bounds hq c10).2.1
    have hm0l := (floor_pos_bounds hq c00).1
    rw [← hn1] at hn1l
    rw [← hn0] at hn0l
    rw [← hm1] at hm1l
    rw [← hm0] at hm0l
    rw [Nat.cast_sub hn01, Nat.cast_sub hm01] at hb2
    have u0 : eps * log |(N0 : ℝ)| ≤ eps * (Cc + c0 - h) :=
      mul_le_mul_of_nonneg_left hN0l heps0.le
    have u1 : (1 + eps) * log |(N1 : ℝ)| ≤ (1 + eps) * (Cc + c1 - h) :=
      mul_le_mul_of_nonneg_left hN1l (by linarith)
    have uc : eps * (c0 + c1) ≤ 1 / 26 * (c0 + c1) :=
      mul_le_mul_of_nonneg_right heps26 (by linarith)
    have hAY : 8 * (A + 1) ≤ Y := by
      have : 8 * 1 * (A + 1) ≤ 8 * ((K : ℝ) + 1) * (A + 1) := by
        have : (0 : ℝ) ≤ K := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith
    have final : c1 - 2 * c0 + h ≤ A + eps * (c0 + c1) := by
      rw [hA]
      nlinarith [hb2, hn1l, hn0l, hm1l, hm0l, u0, u1, heh]
    have c0hi' : c0 ≤ 5 / 4 * Y := by linarith
    have c1hi' : c1 ≤ 13 / 4 * Y := by linarith
    linarith [final, uc, hh0]
  · -- only digit terms besides the second anchor
    obtain ⟨b, hb1, hbT⟩ : ∃ b ∈ T, b ≠ a1 := by
      obtain ⟨b, hb, hne⟩ := exists_mem_ne (by omega : 1 < T.card) a1
      exact ⟨b, hb, hne⟩
    have hb0 : b ≠ a0 := fun e => h0T (e ▸ hb1)
    have hd' := (hdig b (hTsub hb1) hb0 hbT).2.2
    have hbd := hbound b hb1
    rw [hdinv, hN1abs] at hbd
    have hP : ∏ a ∈ T.erase a1, nuS S (x a) ≤ E ^ K :=
      hprodD _ subset_rfl (fun h => h0T (mem_of_mem_erase h))
    have hP0 : 0 ≤ ∏ a ∈ T.erase a1, nuS S (x a) :=
      prod_nonneg (fun a ha => hnu0 a (mem_of_mem_erase ha))
    have hb2 : |(x b : ℝ)| ≤ C * (|(N1 : ℝ)| * E ^ K) ^ (1 + eps) := by
      refine le_trans hbd (mul_le_mul_of_nonneg_left ?_ hC0.le)
      exact rpow_le_rpow (mul_nonneg (abs_nonneg _) hP0)
        (mul_le_mul_of_nonneg_left hP (abs_nonneg _)) (by linarith)
    rw [hexp _ hN1pos, ← exp_log hC0, ← exp_add] at hb2
    have main : ∀ l : ℕ, 2 ≤ l → log (l : ℝ) ≤ log p + log q → exp c1 / l ≤ |(x b : ℝ)| → False := by
      intro l hl hll hle
      have lp : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
      have h1 : exp (c1 - log l) ≤ exp (log C + (1 + eps) * (log |(N1 : ℝ)| + K * log E)) := by
        rw [exp_sub, exp_log lp]
        exact le_trans hle hb2
      rw [exp_le_exp] at h1
      have u1 : (1 + eps) * log |(N1 : ℝ)| ≤ (1 + eps) * (Cc + c1 - h) :=
        mul_le_mul_of_nonneg_left hN1l (by linarith)
      have uc : eps * c1 ≤ h / 2 := by
        have h2 : c1 ≤ 13 / 4 * Y := by linarith
        have h3 : eps * c1 ≤ eps * (13 / 4 * Y) := mul_le_mul_of_nonneg_left h2 heps0.le
        have e : eps * (13 / 4 * Y) = h / 2 := by
          rw [heps, hh]; field_simp; ring
        linarith
      have final : h ≤ A + eps * c1 := by
        have hlp0 : 0 ≤ log (p : ℝ) := hLp.le
        have hlq0 : 0 ≤ log (q : ℝ) := hLq.le
        have hcc : 0 ≤ eps * Cc := hAeps
        rw [hA]
        nlinarith [h1, u1, hll, heh]
      have hhA : A + 1 ≤ h / 2 := by
        rw [hh, div_div, le_div_iff₀ (by positivity)]
        linarith
      linarith
    rcases hd' with h | h
    · exact main p hp hlogp h
    · exact main q hq hlogq h

/-! ## The number of marks is not `O(log n)` -/

lemma sum_windows {l : ℕ} (hl : 2 ≤ l) (α : ℕ → ℚ) {Y1 : ℝ} (hY : 0 < Y1) {X : ℝ} (T : ℕ)
    (hT : Y1 * (13 / 4) ^ T ≤ X) :
    ∑ i ∈ range T, (marksIn l α (Y1 * (13 / 4) ^ i) (13 / 4 * (Y1 * (13 / 4) ^ i))).card
      ≤ (marks α ⌊X / log l⌋₊).card := by
  have hX : 0 ≤ X := le_trans (by positivity) hT
  have e : ∀ i : ℕ, 13 / 4 * (Y1 * (13 / 4) ^ i) = Y1 * (13 / 4) ^ (i + 1) := by
    intro i; rw [pow_succ]; ring
  have mono : ∀ i j : ℕ, i ≤ j → Y1 * (13 / 4 : ℝ) ^ i ≤ Y1 * (13 / 4) ^ j := fun i j h =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h) hY.le
  have hb : ∀ i : ℕ, 0 ≤ 13 / 4 * (Y1 * (13 / 4 : ℝ) ^ i) := fun i => by positivity
  rw [← card_biUnion]
  · refine card_le_card (fun j hj => ?_)
    rw [mem_biUnion] at hj
    obtain ⟨i, hi, hj⟩ := hj
    rw [mem_range] at hi
    rw [mem_marksIn hl (hb i)] at hj
    have hL : 0 < log (l : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < l))
    have hle : (j : ℝ) * log l ≤ X := le_trans hj.2.2.2 (by
      rw [e]; exact le_trans (mono _ _ (by omega)) hT)
    unfold marks
    rw [mem_filter, mem_Icc]
    refine ⟨⟨hj.1, ?_⟩, hj.2.1⟩
    rw [Nat.le_floor_iff (div_nonneg hX hL.le), le_div_iff₀ hL]
    exact hle
  · intro i _ k _ hik
    rw [Function.onFun, Finset.disjoint_left]
    intro j h1 h2
    rw [mem_marksIn hl (hb i)] at h1
    rw [mem_marksIn hl (hb k)] at h2
    rcases Nat.lt_or_gt_of_ne hik with h | h
    · have := mono (i + 1) k h
      rw [e] at h1
      linarith [h1.2.2.2, h2.2.2.1]
    · have := mono (k + 1) i h
      rw [e] at h2
      linarith [h2.2.2.2, h1.2.2.1]

/-- **The marks of two coprime bases are not `O(log n)`.** -/
theorem tendsto_marks {p q : ℕ} (hp : 2 ≤ p) (hpq' : p < q) (hpq : Nat.Coprime p q)
    (hE : EvertseCor1 (p * q).primeFactors) {ξ : ℝ} (hξ : Irrational ξ)
    {α β : ℕ → ℚ} (hα : Approx p ξ α) (hβ : Approx q ξ β) (L : ℝ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → L * log n ≤ ((marks α n).card + (marks β n).card : ℝ) := by
  have hq : 2 ≤ q := by omega
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hLp : 0 < log (p : ℝ) := log_pos (by linarith)
  have hW : 0 < log (13 / 4 : ℝ) := log_pos (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_ge (2 * |L| * log (13 / 4 : ℝ))
  obtain ⟨Y1, hY1, hwin⟩ := window_marks hp hq hpq hE hξ hα hβ K
  set c : ℝ := log (Y1 / log p) with hc
  have hev : ∀ᶠ n : ℕ in Filter.atTop, 2 * (|c| + log (13 / 4 : ℝ)) + 1 ≤ log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  rw [Filter.eventually_atTop] at hev
  obtain ⟨n0, hn0⟩ := hev
  refine ⟨max n0 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hlog := hn0 n (le_trans (le_max_left _ _) hn)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  set X : ℝ := n * log p with hX
  have hX0 : 0 < X := mul_pos hnr hLp
  set t : ℝ := (log n - c) / log (13 / 4 : ℝ) with ht
  have hc1 : c ≤ |c| := le_abs_self c
  have ht0 : 0 ≤ t := div_nonneg (by linarith [abs_nonneg c, hW]) hW.le
  set T : ℕ := ⌊t⌋₊ with hT
  have hTt : (T : ℝ) ≤ t := Nat.floor_le ht0
  have htT : t < T + 1 := Nat.lt_floor_add_one t
  have hfit : Y1 * (13 / 4) ^ T ≤ X := by
    have h1 : (T : ℝ) * log (13 / 4 : ℝ) ≤ log n - c := by
      rw [ht, le_div_iff₀ hW] at hTt
      exact hTt
    have h2 : (13 / 4 : ℝ) ^ T ≤ exp (log n - c) := by
      rw [← exp_log (pow_pos (by norm_num : (0 : ℝ) < 13 / 4) T), log_pow]
      exact exp_le_exp.mpr h1
    have h3 : exp (log n - c) = n * log p / Y1 := by
      rw [exp_sub, exp_log hnr, hc, exp_log (div_pos hY1 hLp)]
      field_simp
    rw [h3, le_div_iff₀ hY1, mul_comm] at h2
    exact h2
  have hcount : ∀ i ∈ range T, K + 1 ≤
      (marksIn p α (Y1 * (13 / 4) ^ i) (13 / 4 * (Y1 * (13 / 4) ^ i))).card
        + (marksIn q β (Y1 * (13 / 4) ^ i) (13 / 4 * (Y1 * (13 / 4) ^ i))).card := by
    intro i _
    exact hwin _ (le_mul_of_one_le_right hY1.le (one_le_pow₀ (by norm_num)))
  have htot := sum_le_sum hcount
  rw [sum_const, card_range, smul_eq_mul, sum_add_distrib] at htot
  have sp := sum_windows hp α hY1 T hfit
  have sq' := sum_windows hq β hY1 T hfit
  have ep : ⌊X / log p⌋₊ = n := by
    rw [hX, mul_div_assoc, div_self hLp.ne', mul_one, Nat.floor_natCast]
  have eq' : ⌊X / log q⌋₊ ≤ n := by
    have hLq : 0 < log (q : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < q))
    have hle : log (p : ℝ) ≤ log q := log_le_log (by linarith) (by exact_mod_cast hpq'.le)
    have : X / log q ≤ n := by
      rw [div_le_iff₀ hLq, hX]
      exact mul_le_mul_of_nonneg_left hle hnr.le
    exact le_trans (Nat.floor_mono this) (le_of_eq (Nat.floor_natCast n))
  rw [ep] at sp
  have hmono : (marks β ⌊X / log q⌋₊).card ≤ (marks β n).card := by
    refine card_le_card (filter_subset_filter _ (Icc_subset_Icc_right eq'))
  have hfinal : T * (K + 1) ≤ (marks α n).card + (marks β n).card :=
    le_trans htot (add_le_add sp (le_trans sq' hmono))
  have hfr : (T : ℝ) * ((K : ℝ) + 1) ≤ ((marks α n).card + (marks β n).card : ℝ) := by
    exact_mod_cast hfinal
  refine le_trans ?_ hfr
  have hT2 : log n / (2 * log (13 / 4 : ℝ)) ≤ T := by
    have h1 : log n / (2 * log (13 / 4 : ℝ)) ≤ t - 1 := by
      rw [ht, div_sub_one hW.ne', div_le_div_iff₀ (by positivity) hW]
      have h2 : log n ≤ 2 * (log n - c - log (13 / 4 : ℝ)) := by linarith
      have h3 := mul_le_mul_of_nonneg_right h2 hW.le
      linarith
    linarith
  have hlog0 : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn1)
  have h4 : |L| * log n ≤ (T : ℝ) * ((K : ℝ) + 1) := by
    have h5 : log n / (2 * log (13 / 4 : ℝ)) * (2 * |L| * log (13 / 4 : ℝ)) = |L| * log n := by
      field_simp
    rw [← h5]
    exact mul_le_mul hT2 (le_trans hK (by linarith)) (by positivity) (Nat.cast_nonneg _)
  exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self L) hlog0) h4

/-! ## Digit changes and non-zero digits -/

/-- The number of `k ≤ n` with `a_k ≠ a_{k+1}`. -/
noncomputable def DC (l : ℕ) (ξ : ℝ) (n : ℕ) : ℕ :=
  ((Icc 1 n).filter (fun k => digit l ξ k ≠ digit l ξ (k + 1))).card

/-- The number of `k ≤ n` with `a_k ≠ 0`. -/
noncomputable def NZ (l : ℕ) (ξ : ℝ) (n : ℕ) : ℕ :=
  ((Icc 1 n).filter (fun k => digit l ξ k ≠ 0)).card

lemma card_marks_DC {l : ℕ} (hl : 2 ≤ l) (ξ : ℝ) (n : ℕ) :
    (marks (alphaDC l ξ) n).card = DC l ξ n := by
  unfold marks DC
  congr 1
  refine filter_congr (fun j hj => ?_)
  rw [mem_Icc] at hj
  have h := alphaDC_sub hl ξ hj.1
  have hden : (((l : ℚ) - 1) * (l : ℚ) ^ j) ≠ 0 := by
    have a : (2 : ℚ) ≤ l := by exact_mod_cast hl
    have b : (0 : ℚ) < (l : ℚ) - 1 := by linarith
    have c : (0 : ℚ) < l := by linarith
    exact (by positivity : (0 : ℚ) < _).ne'
  rw [ne_eq, ne_eq, ← sub_eq_zero, h, div_eq_zero_iff, or_iff_left hden, Int.cast_eq_zero,
    sub_eq_zero, eq_comm]

lemma card_marks_NZ {l : ℕ} (hl : 2 ≤ l) (ξ : ℝ) (n : ℕ) :
    (marks (alphaNZ l ξ) n).card = NZ l ξ n := by
  unfold marks NZ
  congr 1
  refine filter_congr (fun j hj => ?_)
  rw [mem_Icc] at hj
  have h := alphaNZ_sub hl ξ hj.1
  have hden : ((l : ℚ) ^ j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : l ≠ 0))
  rw [ne_eq, ne_eq, ← sub_eq_zero, h, div_eq_zero_iff, or_iff_left hden, Int.cast_eq_zero]

/-- **Digit changes** in two coprime bases are not `O(log n)`. -/
theorem digit_changes {p q : ℕ} (hp : 2 ≤ p) (hpq' : p < q) (hpq : Nat.Coprime p q)
    (hE : EvertseCor1 (p * q).primeFactors) {ξ : ℝ} (hξ : Irrational ξ) (L : ℝ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → L * log n ≤ ((DC p ξ n : ℝ) + DC q ξ n) := by
  have hq : 2 ≤ q := by omega
  obtain ⟨n0, h⟩ := tendsto_marks hp hpq' hpq hE hξ (approxDC hp ξ) (approxDC hq ξ) L
  refine ⟨n0, fun n hn => ?_⟩
  have := h n hn
  rwa [card_marks_DC hp, card_marks_DC hq] at this

/-- **Non-zero digits** in two coprime bases are not `O(log n)`. -/
theorem nonzero_digits {p q : ℕ} (hp : 2 ≤ p) (hpq' : p < q) (hpq : Nat.Coprime p q)
    (hE : EvertseCor1 (p * q).primeFactors) {ξ : ℝ} (hξ : Irrational ξ) (L : ℝ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → L * log n ≤ ((NZ p ξ n : ℝ) + NZ q ξ n) := by
  have hq : 2 ≤ q := by omega
  obtain ⟨n0, h⟩ := tendsto_marks hp hpq' hpq hE hξ (approxNZ hp ξ) (approxNZ hq ξ) L
  refine ⟨n0, fun n hn => ?_⟩
  have := h n hn
  rwa [card_marks_NZ hp, card_marks_NZ hq] at this

/-- The effective bound for digit changes and for non-zero digits. -/
theorem golden_digits {p q : ℕ} (hp : 2 ≤ p) (hpq' : p < q) (hpq : Nat.Coprime p q) {ξ x0 C : ℝ}
    (hC : C = log (((p : ℝ) + q) * (((p : ℝ) - 1) * ((q : ℝ) - 1)))) (hx0 : 0 ≤ x0)
    (hdist : ∀ z : ℤ, (q : ℝ) * exp (-x0) ≤ |ξ - z / (((p : ℝ) - 1) * ((q : ℝ) - 1))|)
    {B n : ℕ} (hn : ww C x0 (B + 2) ≤ n * log p) :
    B + 1 ≤ DC p ξ n + DC q ξ n ∧ B + 1 ≤ NZ p ξ n + NZ q ξ n := by
  have hq : 2 ≤ q := by omega
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hLp : 0 < log (p : ℝ) := log_pos (by linarith)
  have hLq : 0 < log (q : ℝ) := log_pos (by linarith)
  have hle : log (p : ℝ) ≤ log q := log_le_log (by linarith) (by exact_mod_cast hpq'.le)
  have count : ∀ (α β : ℕ → ℚ), Approx p ξ α → Approx q ξ β →
      B + 1 ≤ (marks α n).card + (marks β n).card := by
    intro α β hα hβ
    refine le_trans (golden_marks hp hpq' hpq hα hβ hC hx0 hdist B) (add_le_add ?_ ?_)
    · refine card_le_card ((filter_subset _ _).trans
        (filter_subset_filter _ (Icc_subset_Icc_right ?_)))
      refine le_trans (Nat.floor_mono (div_le_div_of_nonneg_right hn hLp.le)) ?_
      rw [mul_div_assoc, div_self hLp.ne', mul_one, Nat.floor_natCast]
    · refine card_le_card ((filter_subset _ _).trans
        (filter_subset_filter _ (Icc_subset_Icc_right ?_)))
      have h1 : ww C x0 (B + 2) / log q ≤ n := by
        rw [div_le_iff₀ hLq]
        exact le_trans hn (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _))
      exact le_trans (Nat.floor_mono h1) (le_of_eq (Nat.floor_natCast n))
  constructor
  · have := count _ _ (approxDC hp ξ) (approxDC hq ξ)
    rwa [card_marks_DC hp, card_marks_DC hq] at this
  · have := count _ _ (approxNZ hp ξ) (approxNZ hq ξ)
    rwa [card_marks_NZ hp, card_marks_NZ hq] at this

end TwoPrimesDigits
