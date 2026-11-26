import Mathlib
import LeanCheck.TwoPrimesBasis

/-!
# The dual side of the 124-dimensional certificate

The first 123 rows of the matrix are exact relations `Σ B i j * w j = 0` between the digit weights,
and the last row gives `3^6400`.  Consequently:

* `phase`: for every real `θ`, if `J j * ‖w j θ‖ < 90` at all 124 digits then `‖θ‖ < 1/10`;
  that is, `‖θ‖ > 1/10` forces `max J j ‖w j θ‖ ≥ 90`;
* `dual_gap`: for every `b` not divisible by `u = 3^6400` some digit has `N j ‖b w j / u‖ > 140`,
  and the sum of the squares of `N j ‖b w j / u‖` exceeds `336²`.

Here `J j = ⌊ℓ^(2m-1) / 10^15⌋` and `N j = 2 J j + 1`.  The results are due to ChatGPT (the proofs
by pairing with a single row); the checks on the matrix are made by the kernel.
-/

namespace TwoPrimesDualGap

open Finset Matrix TwoPrimesBasisData TwoPrimesBasis

def J (j : Fin 124) : ℕ := base j ^ (2 * dig j - 1) / 10 ^ 15

def N (j : Fin 124) : ℕ := 2 * J j + 1

def scale : ℕ := 10 ^ 60

/-- An upper bound for `scale * Σ |B i j| / J j`. -/
def rowJ (r : List ℤ) : ℕ :=
  ((List.zipWith (fun (a : ℤ) (q : ℕ) => (a.natAbs * scale) / q + 1) r (List.ofFn J))).sum

def rowN (r : List ℤ) : ℕ :=
  ((List.zipWith (fun (a : ℤ) (q : ℕ) => (a.natAbs * scale) / q + 1) r (List.ofFn N))).sum

def rowN2 (r : List ℤ) : ℕ :=
  ((List.zipWith (fun (a : ℤ) (q : ℕ) => (a.natAbs ^ 2 * scale) / q ^ 2 + 1) r (List.ofFn N))).sum

lemma check_J : (List.finRange 124).all (fun j => decide (0 < J j)) = true := by decide +kernel

lemma check_exact :
    (rows.take 123).all (fun r => (List.zipWith (fun a (b : ℕ) => a * (b : ℤ)) r (List.ofFn wN)).sum
      == 0) = true := by decide +kernel

lemma check_rowJ : (rows.take 123).all (fun r => decide (90 * rowJ r < scale)) = true := by
  decide +kernel

lemma check_rowN : rows.all (fun r => decide (140 * rowN r < scale)) = true := by decide +kernel

lemma check_rowN2 : rows.all (fun r => decide (336 ^ 2 * rowN2 r < scale)) = true := by
  decide +kernel

lemma check_big : base 65 = 2 ∧ dig 65 = 101 ∧ base 66 = 3 ∧ dig 66 = 23 := by decide +kernel

lemma J_pos (j : Fin 124) : (0 : ℝ) < J j := by
  have h := List.all_eq_true.mp check_J j (List.mem_finRange j)
  exact_mod_cast of_decide_eq_true h

lemma N_pos (j : Fin 124) : (0 : ℝ) < N j := by
  have : 0 < N j := by unfold N; omega
  exact_mod_cast this

lemma row_mem_take (i : Fin 124) (hi : (i : ℕ) < 123) : rows.getD i [] ∈ rows.take 123 := by
  have h1 : (i : ℕ) < rows.length := by rw [rows_length]; exact i.isLt
  have h2 : (i : ℕ) < (rows.take 123).length := by
    rw [List.length_take, rows_length]
    omega
  have e : rows.getD i [] = (rows.take 123)[(i : ℕ)] := by
    rw [List.getElem_take, getD_get _ _ _ h1]
  rw [e]
  exact List.getElem_mem h2

lemma getD_ofFn (f : Fin 124 → ℕ) (j : Fin 124) : (List.ofFn f).getD j 0 = f j := by
  have hj : (j : ℕ) < (List.ofFn f).length := by rw [List.length_ofFn]; exact j.isLt
  rw [getD_get _ _ _ hj, List.getElem_ofFn]

lemma sum_zip (g : ℤ → ℕ → ℕ) (i : Fin 124) (f : Fin 124 → ℕ) :
    (List.zipWith g (rows.getD i []) (List.ofFn f)).sum = ∑ j, g (B i j) (f j) := by
  rw [zipWith_eq_ofFn g _ _ 0 0 124 (row_length i) List.length_ofFn, List.sum_ofFn]
  exact sum_congr rfl fun j _ => by rw [getD_ofFn]; rfl

/-- The first 123 rows are exact relations. -/
lemma exact_rows (i : Fin 124) (hi : (i : ℕ) < 123) : ∑ j, B i j * (wN j : ℤ) = 0 := by
  have h := List.all_eq_true.mp check_exact _ (row_mem_take i hi)
  rw [beq_iff_eq] at h
  have e := zipWith_sum_eq (fun a (b : ℕ) => a * (b : ℤ)) (rows.getD i []) (List.ofFn wN) 0 0
    124 (row_length i) (List.length_ofFn)
  rw [e] at h
  simp only [getD_ofFn] at h
  exact h

/-- A sum bounded through the integer upper bound of the ratios. -/
lemma ratio_le (a q : ℕ) (hq : 0 < q) :
    (a : ℝ) / q ≤ (((a * scale) / q + 1 : ℕ) : ℝ) / scale := by
  have hs : (0 : ℝ) < scale := by
    have : 0 < scale := pow_pos (by norm_num) _
    exact_mod_cast this
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_div_iff₀ hqr hs]
  have h := Nat.lt_div_mul_add (a := a * scale) hq
  have h' : a * scale ≤ ((a * scale) / q + 1) * q := by
    rw [add_mul, one_mul]
    exact h.le
  exact_mod_cast h'

lemma scale_pos : (0 : ℝ) < scale := by
  have : 0 < scale := pow_pos (by norm_num) _
  exact_mod_cast this

/-! ## The conclusions -/

lemma bezout : ∃ α β : ℤ, α * (wN 0 : ℤ) + β * (wN 66 : ℤ) = 1 := by
  have h : Nat.Coprime (wN 0) (wN 66) := by
    unfold wN
    rw [check_first.1, check_big.2.2.1]
    exact Nat.Coprime.pow _ _ (by norm_num)
  exact Nat.Coprime.isCoprime h

lemma w_pos (j : Fin 124) : 0 < wN j := by
  unfold wN
  refine pow_pos ?_ _
  rcases (shape j).2.2.1 with h | h <;> omega

/-- `‖θ‖ < 1/10` whenever all 124 digits see `θ` below the threshold `90`. -/
theorem phase (θ : ℝ) (h : ∀ j : Fin 124,
    (J j : ℝ) * |(wN j : ℝ) * θ - round ((wN j : ℝ) * θ)| < 90) :
    |θ - round θ| < 1 / 10 := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 124 → ℤ, ∀ j, k j = round ((wN j : ℝ) * θ) := ⟨_, fun _ => rfl⟩
  obtain ⟨ev, hev⟩ : ∃ ev : Fin 124 → ℝ, ∀ j, ev j = (wN j : ℝ) * θ - k j := ⟨_, fun _ => rfl⟩
  have hev90 : ∀ j, |ev j| ≤ 90 / J j := by
    intro j
    rw [le_div_iff₀ (J_pos j), mul_comm, hev, hk]
    exact (h j).le
  -- the nearest integers satisfy the exact relations
  have hrel : ∀ i : Fin 124, (i : ℕ) < 123 → ∑ j, B i j * k j = 0 := by
    intro i hi
    have e : ((∑ j, B i j * k j : ℤ) : ℝ) = -∑ j, (B i j : ℝ) * ev j := by
      have h0 : ∑ j, (B i j : ℝ) * (wN j : ℝ) = 0 := by
        have := congrArg (fun n : ℤ => (n : ℝ)) (exact_rows i hi)
        simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero] using this
      have h1 : ∑ j, (B i j : ℝ) * ev j
          = (∑ j, (B i j : ℝ) * (wN j : ℝ)) * θ - ∑ j, (B i j : ℝ) * (k j : ℝ) := by
        rw [sum_mul, ← sum_sub_distrib]
        exact sum_congr rfl fun j _ => by rw [hev]; ring
      rw [h1, h0, zero_mul, zero_sub, neg_neg, Int.cast_sum]
      exact sum_congr rfl fun j _ => Int.cast_mul _ _
    have hsmall : |((∑ j, B i j * k j : ℤ) : ℝ)| < 1 := by
      rw [e, abs_neg]
      have h2 : |∑ j, (B i j : ℝ) * ev j| ≤ 90 * ∑ j, ((B i j).natAbs : ℝ) / J j := by
        refine le_trans (abs_sum_le_sum_abs _ _) ?_
        rw [mul_sum]
        refine sum_le_sum fun j _ => ?_
        rw [abs_mul]
        have h3 : |(B i j : ℝ)| = ((B i j).natAbs : ℝ) := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        rw [h3]
        refine le_trans (mul_le_mul_of_nonneg_left (hev90 j) (Nat.cast_nonneg _)) (le_of_eq ?_)
        ring
      have h4 : ∑ j, ((B i j).natAbs : ℝ) / J j ≤ (rowJ (rows.getD i []) : ℝ) / scale := by
        have e2 : rowJ (rows.getD i []) = ∑ j, (((B i j).natAbs * scale) / J j + 1) :=
          sum_zip (fun (a : ℤ) (q : ℕ) => (a.natAbs * scale) / q + 1) i J
        rw [e2, Nat.cast_sum, sum_div]
        refine sum_le_sum fun j _ => ratio_le _ _ ?_
        exact_mod_cast J_pos j
      have h5 : 90 * rowJ (rows.getD i []) < scale :=
        of_decide_eq_true (List.all_eq_true.mp check_rowJ _ (row_mem_take i hi))
      have h6 : 90 * ((rowJ (rows.getD i []) : ℝ) / scale) < 1 := by
        rw [mul_div_assoc', div_lt_one scale_pos]
        exact_mod_cast h5
      exact lt_of_le_of_lt (le_trans h2 (mul_le_mul_of_nonneg_left h4 (by norm_num))) h6
    have h7 : |∑ j, B i j * k j| < 1 := by exact_mod_cast hsmall
    exact Int.abs_lt_one_iff.mp h7
  -- hence `k` is an integer multiple of the weights
  obtain ⟨z, hz⟩ : ∃ z : ℤ, ∀ j, k j = z * (wN j : ℤ) := by
    set last : Fin 124 := ⟨123, by norm_num⟩ with hlast
    obtain ⟨W, hW⟩ : ∃ W : ℤ, W = ∑ j, B last j * (wN j : ℤ) := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : ℤ, t = ∑ j, B last j * k j := ⟨_, rfl⟩
    have hlasti : ∀ i : Fin 124, ¬ (i : ℕ) < 123 → i = last := fun i hi =>
      Fin.ext (by rw [hlast]; simp only; omega)
    have hW0 : W ≠ 0 := by
      intro h0
      have hker : B *ᵥ (fun j => (wN j : ℤ)) = 0 := by
        funext i
        show ∑ j, B i j * (wN j : ℤ) = 0
        by_cases hi : (i : ℕ) < 123
        · exact exact_rows i hi
        · rw [hlasti i hi, ← hW, h0]
      have := congrFun (eq_zero_of_mulVec_eq_zero det_ne_zero hker) 0
      have h1 := w_pos 0
      simp only [Pi.zero_apply] at this
      omega
    have hker : B *ᵥ (fun j => W * k j - t * (wN j : ℤ)) = 0 := by
      funext i
      have e : (B *ᵥ fun j => W * k j - t * (wN j : ℤ)) i
          = W * (∑ j, B i j * k j) - t * ∑ j, B i j * (wN j : ℤ) := by
        show ∑ j, B i j * (W * k j - t * (wN j : ℤ)) = _
        rw [mul_sum, mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun j _ => by ring
      rw [e, Pi.zero_apply]
      by_cases hi : (i : ℕ) < 123
      · rw [hrel i hi, exact_rows i hi, mul_zero, mul_zero, sub_zero]
      · rw [hlasti i hi, ← ht, ← hW]
        ring
    have hprop : ∀ j, W * k j = t * (wN j : ℤ) := by
      intro j
      have := congrFun (eq_zero_of_mulVec_eq_zero det_ne_zero hker) j
      simp only [Pi.zero_apply] at this
      omega
    obtain ⟨α, β, hab⟩ := bezout
    refine ⟨α * k 0 + β * k 66, fun j => ?_⟩
    have htz : t = W * (α * k 0 + β * k 66) := by
      linear_combination (-t) * hab - α * hprop 0 - β * hprop 66
    refine mul_left_cancel₀ hW0 ?_
    rw [hprop j, htz]
    ring
  -- conclude with a large weight
  have hbig := h 65
  have hw65 : (wN 65 : ℝ) * (θ - z) = (wN 65 : ℝ) * θ - round ((wN 65 : ℝ) * θ) := by
    have e : round ((wN 65 : ℝ) * θ) = z * (wN 65 : ℤ) := by rw [← hk]; exact hz 65
    rw [e, Int.cast_mul, Int.cast_natCast]
    ring
  rw [← hw65, abs_mul, Nat.abs_cast] at hbig
  have h900 : (900 : ℝ) ≤ (J 65 : ℝ) * wN 65 := by
    have h1 : 0 < J 65 := by exact_mod_cast J_pos 65
    have h2 : 900 ≤ wN 65 := by
      unfold wN
      rw [check_big.1, check_big.2.1]
      exact le_trans (by norm_num : 900 ≤ 2 ^ 10) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    have h3 : 900 ≤ J 65 * wN 65 := le_trans h2 (Nat.le_mul_of_pos_left _ h1)
    exact_mod_cast h3
  have hlt : |θ - z| < 1 / 10 := by
    by_contra hc
    push Not at hc
    have h1 := mul_le_mul h900 hc (by norm_num) (by positivity)
    rw [mul_assoc] at h1
    linarith
  exact lt_of_le_of_lt (round_le θ z) hlt

/-- The dual gaps modulo `u`: in the maximum norm above `140`, in the Euclidean norm above `336`. -/
theorem dual_gap (b : ℤ) (hb : ¬ (u : ℤ) ∣ b) :
    (∃ j : Fin 124, (140 : ℝ) < N j * |(b : ℝ) * wN j / u - round ((b : ℝ) * wN j / u)|) ∧
      (336 : ℝ) ^ 2 < ∑ j : Fin 124,
        ((N j : ℝ) * |(b : ℝ) * wN j / u - round ((b : ℝ) * wN j / u)|) ^ 2 := by
  have hu0 : 0 < u := by unfold u; exact pow_pos (by norm_num) _
  have hur : (u : ℝ) ≠ 0 := by exact_mod_cast hu0.ne'
  obtain ⟨k, hk⟩ : ∃ k : Fin 124 → ℤ, ∀ j, k j = round ((b : ℝ) * wN j / u) := ⟨_, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin 124 → ℝ, ∀ j, y j = (b : ℝ) * wN j / u - k j := ⟨_, fun _ => rfl⟩
  have hyr : ∀ j, |(b : ℝ) * wN j / u - round ((b : ℝ) * wN j / u)| = |y j| := by
    intro j
    rw [hy, hk]
  simp only [hyr]
  -- some row has a nonzero integer pairing with `y`
  have hint : ∀ i : Fin 124, ∃ m : ℤ, ∑ j, (B i j : ℝ) * y j = m := by
    intro i
    obtain ⟨q, hq⟩ := row_dvd i
    refine ⟨b * q - ∑ j, B i j * k j, ?_⟩
    have h1 : ∑ j, (B i j : ℝ) * (wN j : ℝ) = (u : ℝ) * q := by
      have := congrArg (fun n : ℤ => (n : ℝ)) hq
      simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] using this
    have h2 : ∑ j, (B i j : ℝ) * y j
        = (b : ℝ) / u * (∑ j, (B i j : ℝ) * (wN j : ℝ)) - ∑ j, (B i j : ℝ) * (k j : ℝ) := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun j _ => by rw [hy]; ring
    rw [h2, h1, Int.cast_sub, Int.cast_mul, Int.cast_sum]
    congr 1
    · field_simp
    · exact sum_congr rfl fun j _ => (Int.cast_mul _ _).symm
  have hne : ∃ i : Fin 124, ∑ j, (B i j : ℝ) * y j ≠ 0 := by
    by_contra hc
    push Not at hc
    have hdetR : (B.map (Int.castRingHom ℝ)).det ≠ 0 := by
      have e : (B.map (Int.castRingHom ℝ)).det = ((B.det : ℤ) : ℝ) :=
        ((Int.castRingHom ℝ).map_det B).symm
      rw [e]
      exact_mod_cast det_ne_zero
    have hker : (B.map (Int.castRingHom ℝ)) *ᵥ y = 0 := by
      funext i
      show ∑ j, (B i j : ℝ) * y j = 0
      exact hc i
    have hy0 := eq_zero_of_mulVec_eq_zero hdetR hker
    have h0 := congrFun hy0 0
    rw [hy, Pi.zero_apply, sub_eq_zero, div_eq_iff hur] at h0
    have h1 : b * (wN 0 : ℤ) = k 0 * (u : ℤ) := by exact_mod_cast h0
    have h2 : (u : ℤ) ∣ b * (wN 0 : ℤ) := ⟨k 0, by rw [h1, mul_comm]⟩
    have hco : IsCoprime (u : ℤ) (wN 0 : ℤ) := by
      have h : Nat.Coprime u (wN 0) := by
        unfold u wN
        rw [check_first.1]
        exact Nat.Coprime.pow _ _ (by norm_num)
      exact Nat.Coprime.isCoprime h
    exact hb (hco.dvd_of_dvd_mul_right h2)
  obtain ⟨i, hi⟩ := hne
  have h1 : 1 ≤ |∑ j, (B i j : ℝ) * y j| := by
    obtain ⟨m, hm⟩ := hint i
    rw [hm] at hi ⊢
    have hm0 : m ≠ 0 := by exact_mod_cast hi
    exact_mod_cast Int.one_le_abs hm0
  have hrow : rows.getD i [] ∈ rows := row_mem i
  have habs : ∀ j, |(B i j : ℝ)| = ((B i j).natAbs : ℝ) := fun j => by
    rw [Nat.cast_natAbs, Int.cast_abs]
  constructor
  · by_contra hc
    push Not at hc
    have h2 : |∑ j, (B i j : ℝ) * y j| ≤ 140 * ∑ j, ((B i j).natAbs : ℝ) / N j := by
      refine le_trans (abs_sum_le_sum_abs _ _) ?_
      rw [mul_sum]
      refine sum_le_sum fun j _ => ?_
      rw [abs_mul, habs]
      have h3 : |y j| ≤ 140 / N j := by
        rw [le_div_iff₀ (N_pos j), mul_comm]
        exact hc j
      refine le_trans (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)) (le_of_eq ?_)
      ring
    have h4 : ∑ j, ((B i j).natAbs : ℝ) / N j ≤ (rowN (rows.getD i []) : ℝ) / scale := by
      have e2 : rowN (rows.getD i []) = ∑ j, (((B i j).natAbs * scale) / N j + 1) :=
        sum_zip (fun (a : ℤ) (q : ℕ) => (a.natAbs * scale) / q + 1) i N
      rw [e2, Nat.cast_sum, sum_div]
      refine sum_le_sum fun j _ => ratio_le _ _ ?_
      exact_mod_cast N_pos j
    have h5 : 140 * rowN (rows.getD i []) < scale :=
      of_decide_eq_true (List.all_eq_true.mp check_rowN _ hrow)
    have h6 : 140 * ((rowN (rows.getD i []) : ℝ) / scale) < 1 := by
      rw [mul_div_assoc', div_lt_one scale_pos]
      exact_mod_cast h5
    have h7 := le_trans h2 (mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 140))
    linarith
  · obtain ⟨S2, hS2⟩ : ∃ S2 : ℝ, S2 = ∑ j, (((B i j).natAbs : ℝ) / N j) ^ 2 := ⟨_, rfl⟩
    have hS20 : 0 ≤ S2 := by rw [hS2]; exact sum_nonneg fun j _ => sq_nonneg _
    have hcs : (∑ j, (B i j : ℝ) * y j) ^ 2 ≤ S2 * ∑ j, ((N j : ℝ) * |y j|) ^ 2 := by
      have e : ∑ j, (B i j : ℝ) * y j = ∑ j, ((B i j : ℝ) / N j) * ((N j : ℝ) * y j) :=
        sum_congr rfl fun j _ => by
          have := (N_pos j).ne'
          field_simp
      have e1 : S2 = ∑ j, ((B i j : ℝ) / N j) ^ 2 := by
        rw [hS2]
        exact sum_congr rfl fun j _ => by rw [← habs, div_pow, div_pow, sq_abs]
      have e2 : ∑ j, ((N j : ℝ) * |y j|) ^ 2 = ∑ j, ((N j : ℝ) * y j) ^ 2 :=
        sum_congr rfl fun j _ => by rw [mul_pow, mul_pow, sq_abs]
      rw [e, e1, e2]
      exact sum_mul_sq_le_sq_mul_sq _ _ _
    have h4 : S2 ≤ (rowN2 (rows.getD i []) : ℝ) / scale := by
      have e2 : rowN2 (rows.getD i []) = ∑ j, (((B i j).natAbs ^ 2 * scale) / N j ^ 2 + 1) :=
        sum_zip (fun (a : ℤ) (q : ℕ) => (a.natAbs ^ 2 * scale) / q ^ 2 + 1) i N
      rw [hS2, e2, Nat.cast_sum, sum_div]
      refine sum_le_sum fun j _ => ?_
      have hNn : 0 < N j := by exact_mod_cast N_pos j
      have := ratio_le ((B i j).natAbs ^ 2) (N j ^ 2) (pow_pos hNn 2)
      rwa [Nat.cast_pow, Nat.cast_pow, ← div_pow] at this
    have h5 : 336 ^ 2 * rowN2 (rows.getD i []) < scale :=
      of_decide_eq_true (List.all_eq_true.mp check_rowN2 _ hrow)
    have h6 : (336 : ℝ) ^ 2 * ((rowN2 (rows.getD i []) : ℝ) / scale) < 1 := by
      rw [mul_div_assoc', div_lt_one scale_pos]
      exact_mod_cast h5
    have h7 : (1 : ℝ) ≤ (∑ j, (B i j : ℝ) * y j) ^ 2 := by
      have := mul_le_mul h1 h1 zero_le_one (abs_nonneg _)
      rw [abs_mul_abs_self, one_mul] at this
      rwa [sq]
    have h8 : S2 * 336 ^ 2 < 1 := by
      refine lt_of_le_of_lt ?_ h6
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have h10 := le_trans h7 hcs
    by_contra hc
    push Not at hc
    have h11 : S2 * ∑ j, ((N j : ℝ) * |y j|) ^ 2 ≤ S2 * 336 ^ 2 :=
      mul_le_mul_of_nonneg_left hc hS20
    linarith

end TwoPrimesDualGap
