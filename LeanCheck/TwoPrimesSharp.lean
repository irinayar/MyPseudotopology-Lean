import LeanCheck.TwoPrimesDigits
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# The ratio 2 cannot be lowered

For coprime bases `p`, `q` the position of the index `k` of the base `l` is `k log l`.

* `one_mark`: for `R > 2` and irrational `ξ` every late window `(Y, RY]` contains a mark
  (elementary).
* `free_windows`: for `1 < R < 2` and any interval there are, for all large `Y`, subintervals of
  numbers with no non-zero digit, in either base, with position in `(Y, RY]`.  Here `EvertseCor1`
  (Corollary 1 of J.-H. Evertse, Compositio Math. 53 (1984)) is a **hypothesis**.
* `generic_free_windows`: hence a generic real number (in the sense of Baire) is irrational and has
  arbitrarily late windows `(Y, RY]` free of non-zero digits and of digit changes.
-/

namespace TwoPrimesSharp

open Finset Real Set Filter TwoPrimesSUnit TwoPrimesDigits

/-! ## Above 2: there is always a mark -/

/-- **One mark in every late window** `(Y, RY]` for `R > 2`. -/
theorem one_mark {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q) {ξ : ℝ}
    (hξ : Irrational ξ) {α β : ℕ → ℚ} (hα : Approx p ξ α) (hβ : Approx q ξ β) {R : ℝ}
    (hR : 2 < R) :
    ∃ Y1 : ℝ, 0 < Y1 ∧ ∀ Y, Y1 ≤ Y →
      1 ≤ (marksIn p α Y (R * Y)).card + (marksIn q β Y (R * Y)).card := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set G : ℝ := ((p : ℝ) - 1) * ((q : ℝ) - 1) with hG
  have hG1 : 1 ≤ G := by
    have h1 : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have h2 : (1 : ℝ) ≤ (q : ℝ) - 1 := by linarith
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hG0 : 0 < G := by linarith
  obtain ⟨δ, hδ, hdist⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℤ, δ ≤ |ξ - z / G| := by
    set k : ℕ := (p - 1) * (q - 1) with hk
    have hkG : (k : ℝ) = G := by
      rw [hk, hG]
      push_cast [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_sub (show 1 ≤ q by omega)]
      ring
    have hk0 : k ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have hirr : Irrational (ξ * k) := hξ.mul_natCast hk0
    have hpos : 0 < |ξ * k - round (ξ * k)| :=
      abs_pos.mpr (sub_ne_zero.mpr (hirr.ne_int _))
    refine ⟨|ξ * k - round (ξ * k)| / G, div_pos hpos hG0, fun z => ?_⟩
    have e : ξ - z / G = (ξ * k - z) / G := by rw [hkG]; field_simp
    rw [e, abs_div, abs_of_pos hG0]
    exact div_le_div_of_nonneg_right (round_le _ _) hG0.le
  set qq : ℝ := (p : ℝ) + q with hqq
  have hqq0 : 0 < qq := by positivity
  have hR2 : 0 < R - 2 := by linarith
  set A : ℝ := log (G * qq) with hA
  set B : ℝ := log (qq / δ) with hB
  set Y1 : ℝ := 1 + |A| / (R - 2) + |B| with hY1
  have hfrac : 0 ≤ |A| / (R - 2) := div_nonneg (abs_nonneg _) hR2.le
  have hY1pos : 0 < Y1 := by
    have := abs_nonneg B
    linarith
  refine ⟨Y1, hY1pos, fun Y hY => ?_⟩
  have hY0 : 0 < Y := lt_of_lt_of_le hY1pos hY
  have hAY : |A| < (R - 2) * Y := by
    have h1 : |A| / (R - 2) < Y := by
      have := abs_nonneg B
      linarith
    rw [div_lt_iff₀ hR2] at h1
    linarith
  have hBY : |B| < Y := by linarith
  by_contra hcon
  rw [not_le, Nat.lt_one_iff, Nat.add_eq_zero_iff, card_eq_zero, card_eq_zero] at hcon
  have hRY : Y ≤ R * Y := le_mul_of_one_le_left hY0.le (by linarith)
  have hX0 : 0 ≤ R * Y := le_trans hY0.le hRY
  have free : ∀ (l : ℕ) (hl : 2 ≤ l) (γ : ℕ → ℚ) (hγ : Approx l ξ γ),
      marksIn l γ Y (R * Y) = ∅ → |ξ - (γ ⌊Y / log l⌋₊ : ℝ)| < l * exp (-(R * Y)) := by
    intro l hl γ hγ hem
    refine free_close hl hγ hY0.le hRY (fun n hn h1 h2 => ?_)
    by_contra hne
    have : n ∈ marksIn l γ Y (R * Y) := (mem_marksIn hl hX0).mpr ⟨hn, hne, h1, h2⟩
    rw [hem] at this
    exact absurd this (notMem_empty n)
  have e1 := free p hp α hα hcon.1
  have e2 := free q hq β hβ hcon.2
  set n := ⌊Y / log p⌋₊ with hn
  set m := ⌊Y / log q⌋₊ with hm
  have pn : (p : ℝ) ^ n ≤ exp Y := (floor_pos_bounds hp hY0.le).2.2
  have qm : (q : ℝ) ^ m ≤ exp Y := (floor_pos_bounds hq hY0.le).2.2
  obtain ⟨r, hr⟩ := hα.num n
  obtain ⟨s, hs⟩ := hβ.num m
  obtain ⟨N, hN⟩ := anchor_int hp hq hr hs
  have hNr : (N : ℝ) = G * (p : ℝ) ^ n * (q : ℝ) ^ m * ((α n : ℝ) - (β m : ℝ)) := by
    have := congrArg (fun t : ℚ => (t : ℝ)) hN
    push_cast at this
    rw [this, hG]
  have hdiff : |(α n : ℝ) - (β m : ℝ)| < qq * exp (-(R * Y)) := by
    have : (α n : ℝ) - (β m : ℝ) = (ξ - (β m : ℝ)) - (ξ - (α n : ℝ)) := by ring
    rw [this]
    refine lt_of_le_of_lt (abs_sub _ _) ?_
    rw [hqq]
    linarith
  have hN0 : N = 0 := by
    have hlt : |(N : ℝ)| < 1 := by
      have hGpq : 0 < G * (p : ℝ) ^ n * (q : ℝ) ^ m := by positivity
      rw [hNr, abs_mul, abs_of_pos hGpq]
      have h1 : G * (p : ℝ) ^ n * (q : ℝ) ^ m ≤ G * exp Y * exp Y := by gcongr
      have h2 : G * exp Y * exp Y * (qq * exp (-(R * Y))) ≤ 1 := by
        have e : G * exp Y * exp Y * (qq * exp (-(R * Y))) = exp (A + (Y + Y + -(R * Y))) := by
          rw [exp_add, exp_add, exp_add, hA, exp_log (mul_pos hG0 hqq0)]
          ring
        rw [e, ← exp_zero]
        refine exp_le_exp.mpr ?_
        have := le_abs_self A
        linarith
      calc G * (p : ℝ) ^ n * (q : ℝ) ^ m * |(α n : ℝ) - (β m : ℝ)|
          ≤ G * exp Y * exp Y * |(α n : ℝ) - (β m : ℝ)| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ < G * exp Y * exp Y * (qq * exp (-(R * Y))) :=
            mul_lt_mul_of_pos_left hdiff (by positivity)
        _ ≤ 1 := h2
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
  have h2 : (p : ℝ) * exp (-(R * Y)) < δ := by
    have h3 : B < R * Y := lt_of_le_of_lt (le_abs_self _) (lt_of_lt_of_le hBY hRY)
    have h4 : qq / δ < exp (R * Y) := by
      rw [← exp_log (div_pos hqq0 hδ), ← hB]
      exact exp_lt_exp.mpr h3
    have h5 : (p : ℝ) < δ * exp (R * Y) := by
      rw [div_lt_iff₀ hδ, mul_comm] at h4
      have : (p : ℝ) ≤ qq := by
        rw [hqq]
        have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
        linarith
      linarith
    rw [exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (exp_pos _)]
    exact h5
  linarith

/-! ## Below 2: two close rationals, one with a `p`-power and one with a `q`-power denominator -/

set_option maxHeartbeats 1000000 in
/-- No short vector with a bounded second coordinate. -/
lemma no_short {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hE : EvertseCor1 (p * q).primeFactors) {R : ℝ} (hR1 : 1 < R) (hR2 : R < 2)
    (C C0 : ℝ) (hC : 1 ≤ C) (hC0 : 1 ≤ C0) :
    ∃ Y1 : ℝ, ∀ Y, Y1 ≤ Y → ∀ r t s : ℤ, 0 < r → (r : ℝ) ≤ C * exp ((R - 1) * Y) →
      |(t : ℝ)| ≤ C0 →
      (q : ℤ) ^ ⌊Y / log q⌋₊ * r - (p : ℤ) ^ ⌊Y / log p⌋₊ * s = t → False := by
  classical
  set S := (p * q).primeFactors with hSdef
  have hS : ∀ r ∈ S, Nat.Prime r := fun r hr => Nat.prime_of_mem_primeFactors hr
  have hpq0 : p * q ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hup : nuS S (p : ℤ) = 1 :=
    nuS_unit hS (by omega) (Nat.primeFactors_mono (dvd_mul_right p q) hpq0)
  have huq : nuS S (q : ℤ) = 1 :=
    nuS_unit hS (by omega) (Nat.primeFactors_mono (dvd_mul_left q p) hpq0)
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set eps : ℝ := (2 - R) / (4 * (R - 1)) with heps
  have hR10 : 0 < R - 1 := by linarith
  have heps0 : 0 < eps := div_pos (by linarith) (by linarith)
  have hkey : (R - 1) * (1 + 2 * eps) = R / 2 := by
    rw [heps]; field_simp; ring
  set d : ℝ := 1 / (1 + eps) with hd
  have hd0 : 0 < d := by positivity
  have hd1 : d < 1 := by rw [hd, div_lt_one (by positivity)]; linarith
  have hdinv : 1 / d = 1 + eps := by rw [hd, one_div_one_div]
  obtain ⟨C1, hC1, hsb⟩ := sum_bound hS hE 3 hd0 hd1
  set C2 : ℝ := C0 * ((p : ℝ) + C0) with hC2
  have hC2pos : 0 < C2 := mul_pos (by linarith) (by linarith)
  set K : ℝ := log q + log C1 + (1 + eps) * log C2 + (1 + 2 * eps) * log C with hK
  set Y1 : ℝ := |K| / (1 - R / 2) + |log (C0 * q)| + |log (C * p)| / (2 - R) + 1 with hY1
  have hR20 : 0 < 1 - R / 2 := by linarith
  have h2R : 0 < 2 - R := by linarith
  refine ⟨Y1, fun Y hY r t s hr0 hr ht heq => ?_⟩
  have f1 : 0 ≤ |K| / (1 - R / 2) := div_nonneg (abs_nonneg _) hR20.le
  have f2 : 0 ≤ |log (C * p)| / (2 - R) := div_nonneg (abs_nonneg _) h2R.le
  have f3 := abs_nonneg (log (C0 * q))
  have hY0 : 0 < Y := by linarith
  have hKY : |K| < (1 - R / 2) * Y := by
    have h1 : |K| / (1 - R / 2) < Y := by linarith
    rw [div_lt_iff₀ hR20] at h1; linarith
  have hCqY : |log (C0 * q)| < Y := by linarith
  have hCpY : |log (C * p)| < (2 - R) * Y := by
    have h1 : |log (C * p)| / (2 - R) < Y := by linarith
    rw [div_lt_iff₀ h2R] at h1; linarith
  set n := ⌊Y / log p⌋₊ with hn
  set m := ⌊Y / log q⌋₊ with hm
  have pn : (p : ℝ) ^ n ≤ exp Y := (floor_pos_bounds hp hY0.le).2.2
  have qm : (q : ℝ) ^ m ≤ exp Y := (floor_pos_bounds hq hY0.le).2.2
  have big : ∀ (l : ℕ), 2 ≤ l → exp Y < (l : ℝ) ^ ⌊Y / log l⌋₊ * l := by
    intro l hl
    have h := (floor_pos_bounds hl hY0.le).2.1
    have l0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
    have e : (l : ℝ) ^ ⌊Y / log l⌋₊ * l = exp (((⌊Y / log l⌋₊ : ℝ) + 1) * log l) := by
      rw [← pow_succ, ← exp_log (pow_pos l0 (⌊Y / log l⌋₊ + 1)), log_pow]
      push_cast; ring_nf
    rw [e]
    exact exp_lt_exp.mpr h
  have pnb := big p hp
  have qmb := big q hq
  rw [← hn] at pnb
  rw [← hm] at qmb
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr0
  -- `t` and `s` do not vanish
  have ht0 : t ≠ 0 := by
    intro h0
    have h1 : (p : ℤ) ^ n ∣ (q : ℤ) ^ m * r := ⟨s, by rw [h0] at heq; linarith⟩
    have hco : IsCoprime ((p : ℤ) ^ n) ((q : ℤ) ^ m) :=
      (Nat.isCoprime_iff_coprime.mpr hpq).pow
    have h2 : (p : ℤ) ^ n ∣ r := hco.dvd_of_dvd_mul_left h1
    have h3 : (p : ℤ) ^ n ≤ r := Int.le_of_dvd hr0 h2
    have h4 : (p : ℝ) ^ n ≤ r := by exact_mod_cast h3
    have h5 : exp Y < C * exp ((R - 1) * Y) * p :=
      lt_of_lt_of_le pnb (mul_le_mul_of_nonneg_right (le_trans h4 hr) (by positivity))
    have h6 : C * exp ((R - 1) * Y) * p = exp (log (C * p) + (R - 1) * Y) := by
      rw [exp_add, exp_log (mul_pos (by linarith) (by linarith : (0 : ℝ) < p))]; ring
    rw [h6, exp_lt_exp] at h5
    have := le_abs_self (log (C * p))
    linarith
  have hqbig : C0 < (q : ℝ) ^ m := by
    have h1 : C0 * q < exp Y := by
      have h2 : log (C0 * q) < Y := lt_of_le_of_lt (le_abs_self _) hCqY
      rw [← exp_log (mul_pos (by linarith) (by linarith : (0 : ℝ) < q))]
      exact exp_lt_exp.mpr h2
    have h3 := lt_trans h1 qmb
    exact lt_of_mul_lt_mul_right h3 (by positivity)
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero, sub_zero] at heq
    have h1 : (q : ℝ) ^ m * r = t := by exact_mod_cast heq
    have h2 : (q : ℝ) ^ m ≤ |(t : ℝ)| := by
      rw [← h1, abs_of_pos (mul_pos (pow_pos (by linarith) _) hrr)]
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr0
      exact le_mul_of_one_le_right (by positivity) this
    linarith
  -- the three terms
  set x : Fin 3 → ℤ := ![(q : ℤ) ^ m * r, -((p : ℤ) ^ n * s), -t] with hx
  have x0 : x 0 = (q : ℤ) ^ m * r := rfl
  have x1 : x 1 = -((p : ℤ) ^ n * s) := rfl
  have x2 : x 2 = -t := rfl
  have xne : ∀ i, x i ≠ 0 := by
    intro i
    fin_cases i
    · exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))) hr0.ne'
    · exact neg_ne_zero.mpr
        (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (by omega : p ≠ 0))) hs0)
    · exact neg_ne_zero.mpr ht0
  have xsum : ∑ i, x i = 0 := by
    rw [Fin.sum_univ_three, x0, x1, x2, ← heq]; ring
  have xnd : ∀ U ⊆ (Finset.univ : Finset (Fin 3)), U.Nonempty → U ≠ Finset.univ → ∑ i ∈ U, x i ≠ 0 := by
    intro U _ hU hUne h0
    have hc : U.card < 3 := by
      have := card_lt_card (ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ U, hUne⟩)
      simpa using this
    have hc0 : 0 < U.card := hU.card_pos
    have h12 : U.card = 1 ∨ U.card = 2 := by omega
    rcases h12 with h | h
    · obtain ⟨a, ha⟩ := card_eq_one.mp h
      rw [ha, sum_singleton] at h0
      exact xne a h0
    · have h' : (Finset.univ \ U).card = 1 := by
        rw [card_sdiff_of_subset (Finset.subset_univ U)]
        simp [h]
      obtain ⟨a, ha⟩ := card_eq_one.mp h'
      have := sum_sdiff (f := x) (Finset.subset_univ U)
      rw [ha, sum_singleton, h0, add_zero, xsum] at this
      exact xne a this
  have hb := hsb (Finset.univ : Finset (Fin 3)) x 2 (mem_univ _) (by simp) (by simp) xsum xnd 0
    (mem_univ _)
  have herase : (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  rw [hdinv, herase, prod_pair (by decide : (0 : Fin 3) ≠ 1)] at hb
  -- sizes
  have nu0 : nuS S (x 0) ≤ r := by
    have e : x 0 = r * (p : ℤ) ^ 0 * (q : ℤ) ^ m := by rw [x0]; ring
    rw [e]
    refine le_trans (nuS_attach hS hup huq _ _ _) (le_of_eq ?_)
    exact abs_of_pos hrr
  have nu1 : nuS S (x 1) ≤ |(s : ℝ)| := by
    have e : x 1 = (-s) * (p : ℤ) ^ n * (q : ℤ) ^ 0 := by rw [x1]; ring
    rw [e]
    refine le_trans (nuS_attach hS hup huq _ _ _) (le_of_eq ?_)
    push_cast
    rw [abs_neg]
  have nu0' : 0 ≤ nuS S (x 0) := le_trans zero_le_one (one_le_nuS hS (xne 0))
  have nu1' : 0 ≤ nuS S (x 1) := le_trans zero_le_one (one_le_nuS hS (xne 1))
  have hsb' : |(s : ℝ)| ≤ ((p : ℝ) + C0) * r := by
    have h1 : (p : ℝ) ^ n * s = (q : ℝ) ^ m * r - t := by
      have : (q : ℝ) ^ m * r - (p : ℝ) ^ n * s = t := by exact_mod_cast heq
      linarith
    have pn0 : (0 : ℝ) < (p : ℝ) ^ n := pow_pos (by linarith) _
    have pn1 : (1 : ℝ) ≤ (p : ℝ) ^ n := one_le_pow₀ (by linarith)
    have hq_le : (q : ℝ) ^ m ≤ (p : ℝ) ^ n * p := le_trans qm pnb.le
    have h2 : (p : ℝ) ^ n * |(s : ℝ)| ≤ (p : ℝ) ^ n * (((p : ℝ) + C0) * r) := by
      have h3 : (p : ℝ) ^ n * |(s : ℝ)| = |(q : ℝ) ^ m * r - t| := by
        rw [← h1, abs_mul, abs_of_pos pn0]
      rw [h3]
      refine le_trans (abs_sub _ _) ?_
      rw [abs_of_pos (mul_pos (pow_pos (by linarith) _) hrr)]
      have h4 : (q : ℝ) ^ m * r ≤ (p : ℝ) ^ n * p * r := mul_le_mul_of_nonneg_right hq_le hrr.le
      have h5 : |(t : ℝ)| ≤ (p : ℝ) ^ n * C0 * r := by
        have r1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
        refine le_trans ht ?_
        have : C0 ≤ (p : ℝ) ^ n * C0 := le_mul_of_one_le_left (by linarith) pn1
        exact le_trans this (le_mul_of_one_le_right (by positivity) r1)
      nlinarith
    exact le_of_mul_le_mul_left h2 pn0
  have hprod : |(x 2 : ℝ)| * (nuS S (x 0) * nuS S (x 1)) ≤ C2 * (r : ℝ) ^ 2 := by
    have h2 : |(x 2 : ℝ)| ≤ C0 := by rw [x2]; push_cast; rw [abs_neg]; exact ht
    have h3 : nuS S (x 0) * nuS S (x 1) ≤ r * (((p : ℝ) + C0) * r) :=
      mul_le_mul nu0 (le_trans nu1 hsb') nu1' hrr.le
    refine le_trans (mul_le_mul h2 h3 (mul_nonneg nu0' nu1') (by linarith)) (le_of_eq ?_)
    rw [hC2]; ring
  have hb2 : |(x 0 : ℝ)| ≤ C1 * (C2 * (r : ℝ) ^ 2) ^ (1 + eps) :=
    le_trans hb (mul_le_mul_of_nonneg_left
      (rpow_le_rpow (mul_nonneg (abs_nonneg _) (mul_nonneg nu0' nu1')) hprod (by linarith))
      (by linarith))
  have hx0abs : |(x 0 : ℝ)| = (q : ℝ) ^ m * r := by
    rw [x0]; push_cast
    exact abs_of_pos (mul_pos (pow_pos (by linarith) _) hrr)
  have hC10 : 0 < C1 := by linarith
  have hqm0 : (0 : ℝ) < (q : ℝ) ^ m := pow_pos (by linarith) _
  rw [hx0abs] at hb2
  have hlog := log_le_log (mul_pos hqm0 hrr) hb2
  have hbase : 0 < C2 * (r : ℝ) ^ 2 := mul_pos hC2pos (pow_pos hrr 2)
  rw [log_mul hqm0.ne' hrr.ne', log_mul hC10.ne' (rpow_pos_of_pos hbase _).ne',
    log_rpow hbase, log_mul hC2pos.ne' (pow_pos hrr 2).ne', log_pow (r : ℝ) 2] at hlog
  push_cast at hlog
  have hlr : log (r : ℝ) ≤ log C + (R - 1) * Y := by
    have h1 := log_le_log hrr hr
    rwa [log_mul (by linarith : C ≠ 0) (exp_ne_zero _), log_exp] at h1
  have hlq : Y - log q ≤ log ((q : ℝ) ^ m) := by
    have h1 := log_le_log (exp_pos _) qmb.le
    rw [log_exp, log_mul hqm0.ne' (by positivity)] at h1
    linarith
  have h3 : (1 + 2 * eps) * log (r : ℝ) ≤ (1 + 2 * eps) * (log C + (R - 1) * Y) :=
    mul_le_mul_of_nonneg_left hlr (by linarith)
  have h4 : (1 + 2 * eps) * ((R - 1) * Y) = R / 2 * Y := by
    rw [← hkey]; ring
  have h5 : (1 - R / 2) * Y ≤ K := by
    rw [hK]
    nlinarith [hlog, hlq, h3, h4]
  have := le_abs_self K
  linarith

set_option maxHeartbeats 1000000 in
/-- Two rationals `r/p^n ≥ s/q^m`, `n = ⌊Y/log p⌋`, `m = ⌊Y/log q⌋`, closer than
`exp(-RY)/(2q)`, with the first in a given interval. -/
lemma close_pair {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hE : EvertseCor1 (p * q).primeFactors) {R : ℝ} (hR1 : 1 < R) (hR2 : R < 2)
    (j0 j1 : ℝ) (hj : j0 < j1) :
    ∃ Y1 : ℝ, ∀ Y, Y1 ≤ Y → ∃ r s : ℤ,
      let P : ℝ := (p : ℝ) ^ ⌊Y / log p⌋₊
      let Q : ℝ := (q : ℝ) ^ ⌊Y / log q⌋₊
      |(r : ℝ) / P - (j0 + j1) / 2| ≤ (j1 - j0) / 4 ∧
      0 ≤ (r : ℝ) / P - s / Q ∧ (r : ℝ) / P - s / Q ≤ exp (-(R * Y)) / (2 * q) := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hw : 0 < j1 - j0 := by linarith
  set w : ℝ := j1 - j0 with hwdef
  set C : ℝ := 4 * (q : ℝ) ^ 2 + 1 with hCdef
  set C0 : ℝ := 8 / w + 1 with hC0def
  have hC : 1 ≤ C := by
    have : (0 : ℝ) ≤ 4 * (q : ℝ) ^ 2 := by positivity
    linarith
  have h8w : 0 ≤ 8 / w := div_nonneg (by norm_num) hw.le
  have hC0 : 1 ≤ C0 := by linarith
  obtain ⟨Y2, hns⟩ := no_short hp hq hpq hE hR1 hR2 C C0 hC hC0
  have h2R : 0 < 2 - R := by linarith
  set L1 : ℝ := log (4 * C0 * p * (q : ℝ) ^ 2) with hL1
  set L2 : ℝ := log (4 * p / w) with hL2
  set Y1 : ℝ := |Y2| + |L1| / (2 - R) + |L2| + 1 with hY1
  refine ⟨Y1, fun Y hY => ?_⟩
  have f1 : 0 ≤ |L1| / (2 - R) := div_nonneg (abs_nonneg _) h2R.le
  have f2 := abs_nonneg Y2
  have f3 := abs_nonneg L2
  have hY0 : 0 < Y := by linarith
  have hY2 : Y2 ≤ Y := le_trans (le_abs_self _) (by linarith)
  have hL1Y : |L1| < (2 - R) * Y := by
    have h1 : |L1| / (2 - R) < Y := by linarith
    rw [div_lt_iff₀ h2R] at h1; linarith
  have hL2Y : |L2| < Y := by linarith
  set n := ⌊Y / log p⌋₊ with hn
  set m := ⌊Y / log q⌋₊ with hm
  have pn : (p : ℝ) ^ n ≤ exp Y := (floor_pos_bounds hp hY0.le).2.2
  have qm : (q : ℝ) ^ m ≤ exp Y := (floor_pos_bounds hq hY0.le).2.2
  have big : ∀ (l : ℕ), 2 ≤ l → exp Y < (l : ℝ) ^ ⌊Y / log l⌋₊ * l := by
    intro l hl
    have h := (floor_pos_bounds hl hY0.le).2.1
    have l0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
    have e : (l : ℝ) ^ ⌊Y / log l⌋₊ * l = exp (((⌊Y / log l⌋₊ : ℝ) + 1) * log l) := by
      rw [← pow_succ, ← exp_log (pow_pos l0 (⌊Y / log l⌋₊ + 1)), log_pow]
      push_cast; ring_nf
    rw [e]
    exact exp_lt_exp.mpr h
  have pnb := big p hp
  have qmb := big q hq
  rw [← hn] at pnb
  rw [← hm] at qmb
  set P : ℝ := (p : ℝ) ^ n with hP
  set Q : ℝ := (q : ℝ) ^ m with hQ
  have P0 : 0 < P := pow_pos (by linarith) _
  have Q0 : 0 < Q := pow_pos (by linarith) _
  set T : ℝ := P * Q * exp (-(R * Y)) / (2 * q) with hTdef
  have T0 : 0 < T := div_pos (mul_pos (mul_pos P0 Q0) (exp_pos _)) (by linarith)
  set A : ℝ := w * P / 4 with hAdef
  have A0 : 0 < A := div_pos (mul_pos hw P0) (by norm_num)
  -- `T` is large and `P` is large
  have hPY : exp Y / p < P := by rw [div_lt_iff₀ (by linarith)]; exact pnb
  have hQY : exp Y / q < Q := by rw [div_lt_iff₀ (by linarith)]; exact qmb
  have hTbig : 2 * C0 ≤ T := by
    have h1 : exp Y / p * (exp Y / q) ≤ P * Q :=
      mul_le_mul hPY.le hQY.le (div_nonneg (exp_pos _).le (by linarith)) P0.le
    have h2 : exp ((2 - R) * Y) / (2 * p * (q : ℝ) ^ 2) ≤ T := by
      have e : exp ((2 - R) * Y) / (2 * p * (q : ℝ) ^ 2)
          = exp Y / p * (exp Y / q) * exp (-(R * Y)) / (2 * q) := by
        have : exp ((2 - R) * Y) = exp Y * exp Y * exp (-(R * Y)) := by
          rw [← exp_add, ← exp_add]; ring_nf
        rw [this]; field_simp
      rw [e, hTdef]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (exp_pos _).le)
        (by linarith)
    have h3 : 4 * C0 * p * (q : ℝ) ^ 2 ≤ exp ((2 - R) * Y) := by
      have hpos : 0 < 4 * C0 * p * (q : ℝ) ^ 2 := by
        have : (0 : ℝ) < C0 := by linarith
        positivity
      rw [← exp_log hpos, ← hL1]
      exact exp_le_exp.mpr (le_trans (le_abs_self _) hL1Y.le)
    refine le_trans ?_ h2
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hAbig : 1 ≤ A := by
    have h1 : 4 * p / w ≤ exp Y := by
      have hpos : 0 < 4 * (p : ℝ) / w := div_pos (by linarith) hw
      rw [← exp_log hpos, ← hL2]
      exact exp_le_exp.mpr (le_trans (le_abs_self _) hL2Y.le)
    rw [div_le_iff₀ hw] at h1
    have h2 : exp Y < P * p := pnb
    have h3 : 4 * (p : ℝ) ≤ w * P * p := by
      have := mul_le_mul_of_nonneg_right h2.le hw.le
      nlinarith
    have h4 : 4 ≤ w * P := le_of_mul_le_mul_right h3 (by linarith)
    rw [hAdef]; linarith
  -- two short independent vectors
  set P' : ℕ := p ^ n with hP'
  set a : ℕ := q ^ m with ha
  have hPP : (P' : ℝ) = P := by rw [hP', hP]; push_cast; rfl
  have hQQ : (a : ℝ) = Q := by rw [ha, hQ]; push_cast; rfl
  have dir : ∀ N : ℕ, 0 < N → ∃ r t s : ℤ, 0 < r ∧ r ≤ N ∧
      (a : ℤ) * r - (P' : ℤ) * s = t ∧ |(t : ℝ)| ≤ P / (N + 1) := by
    intro N hN
    obtain ⟨j, k, hk0, hkN, h⟩ := Real.exists_int_int_abs_mul_sub_le ((a : ℝ) / P) hN
    refine ⟨k, (a : ℤ) * k - (P' : ℤ) * j, j, hk0, hkN, rfl, ?_⟩
    have e : (((a : ℤ) * k - (P' : ℤ) * j : ℤ) : ℝ) = P * ((k : ℝ) * ((a : ℝ) / P) - j) := by
      push_cast [hPP]
      field_simp
    rw [e, abs_mul, abs_of_pos P0]
    have := mul_le_mul_of_nonneg_left h P0.le
    rwa [mul_one_div] at this
  set N1 : ℕ := ⌈2 * P / T⌉₊ with hN1
  have h2PT : 0 < 2 * P / T := div_pos (by linarith) T0
  have N10 : 0 < N1 := Nat.ceil_pos.mpr h2PT
  have N1lo : 2 * P / T ≤ N1 := Nat.le_ceil _
  have N1hi : (N1 : ℝ) ≤ C * exp ((R - 1) * Y) := by
    have h1 : (N1 : ℝ) < 2 * P / T + 1 := Nat.ceil_lt_add_one h2PT.le
    have h2 : 2 * P / T = 4 * q * exp (R * Y) / Q := by
      rw [hTdef, exp_neg]
      field_simp
      ring
    have h3 : 4 * q * exp (R * Y) / Q ≤ 4 * (q : ℝ) ^ 2 * exp ((R - 1) * Y) := by
      rw [div_le_iff₀ Q0]
      have h4 : exp (R * Y) = exp ((R - 1) * Y) * exp Y := by rw [← exp_add]; ring_nf
      rw [h4]
      have h5 := mul_le_mul_of_nonneg_left qmb.le
        (show (0 : ℝ) ≤ 4 * q * exp ((R - 1) * Y) by positivity)
      nlinarith
    have h6 : 1 ≤ exp ((R - 1) * Y) := one_le_exp (mul_nonneg (by linarith) hY0.le)
    rw [hCdef]
    linarith
  set N2 : ℕ := ⌊A⌋₊ with hN2
  have N20 : 0 < N2 := Nat.floor_pos.mpr hAbig
  obtain ⟨r1, t1, s1, r10, r1N, e1, b1⟩ := dir N1 N10
  obtain ⟨r2, t2, s2, r20, r2N, e2, b2⟩ := dir N2 N20
  have b1' : |(t1 : ℝ)| ≤ T / 2 := by
    refine le_trans b1 ?_
    have h1 : 2 * P / T ≤ (N1 : ℝ) + 1 := by linarith
    rw [div_le_iff₀ T0] at h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have b2' : |(t2 : ℝ)| ≤ C0 := by
    refine le_trans b2 ?_
    have h1 : A ≤ (N2 : ℝ) + 1 := (Nat.lt_floor_add_one A).le
    have h2 : P / ((N2 : ℝ) + 1) ≤ P / A := div_le_div_of_nonneg_left P0.le A0 h1
    have h3 : P / A = 4 / w := by rw [hAdef]; field_simp
    have h4 : 4 / w ≤ 8 / w := div_le_div_of_nonneg_right (by norm_num) hw.le
    linarith
  have r2A : (r2 : ℝ) ≤ A := by
    have h1 : (r2 : ℝ) ≤ N2 := by exact_mod_cast r2N
    exact le_trans h1 (Nat.floor_le A0.le)
  have r1N' : (r1 : ℝ) ≤ N1 := by exact_mod_cast r1N
  have t1big : C0 < |(t1 : ℝ)| := by
    by_contra h
    exact hns Y hY2 r1 t1 s1 r10 (le_trans r1N' N1hi) (not_lt.mp h)
      (by rw [← hn, ← hm]; rw [ha, hP'] at e1; exact_mod_cast e1)
  have r2big : (N1 : ℝ) < r2 := by
    by_contra h
    exact hns Y hY2 r2 t2 s2 r20 (le_trans (not_lt.mp h) N1hi) b2'
      (by rw [← hn, ← hm]; rw [ha, hP'] at e2; exact_mod_cast e2)
  have r10' : (0 : ℝ) < r1 := by exact_mod_cast r10
  have r20' : (0 : ℝ) < r2 := by exact_mod_cast r20
  set det : ℝ := (r1 : ℝ) * t2 - r2 * t1 with hdet
  have det0 : det ≠ 0 := by
    intro h
    have h1 : (r1 : ℝ) * t2 = r2 * t1 := by rw [hdet] at h; linarith
    have h2 := congrArg abs h1
    rw [abs_mul, abs_mul, abs_of_pos r10', abs_of_pos r20'] at h2
    have h3 : (r1 : ℝ) * |(t2 : ℝ)| ≤ N1 * C0 :=
      mul_le_mul r1N' b2' (abs_nonneg _) (Nat.cast_nonneg _)
    have h4 : (N1 : ℝ) * C0 < r2 * |(t1 : ℝ)| := by
      have hN1' : (0 : ℝ) ≤ N1 := Nat.cast_nonneg _
      exact mul_lt_mul'' r2big t1big hN1' (by linarith)
    linarith
  -- a lattice point near the centre
  set zr : ℝ := P * ((j0 + j1) / 2) with hzr
  set zt : ℝ := T / 2 with hzt
  set x : ℝ := (zr * t2 - r2 * zt) / det with hx
  set y : ℝ := (r1 * zt - t1 * zr) / det with hy
  have solr : x * r1 + y * r2 = zr := by
    rw [hx, hy]; field_simp; rw [hdet]; ring
  have solt : x * t1 + y * t2 = zt := by
    rw [hx, hy]; field_simp; rw [hdet]; ring
  set k : ℤ := round x with hk
  set l : ℤ := round y with hl
  have hxk : |(k : ℝ) - x| ≤ 1 / 2 := by rw [abs_sub_comm]; exact abs_sub_round x
  have hyl : |(l : ℝ) - y| ≤ 1 / 2 := by rw [abs_sub_comm]; exact abs_sub_round y
  set r : ℤ := k * r1 + l * r2 with hr
  set t : ℤ := k * t1 + l * t2 with ht
  set s : ℤ := k * s1 + l * s2 with hs
  have comb : (a : ℤ) * r - (P' : ℤ) * s = t := by
    rw [hr, hs, ht, ← e1, ← e2]; ring
  have r12 : (r1 : ℝ) ≤ r2 := le_of_lt (lt_of_le_of_lt r1N' r2big)
  have near : ∀ (u v z : ℝ), x * u + y * v = z →
      |(k : ℝ) * u + l * v - z| ≤ (|u| + |v|) / 2 := by
    intro u v z h
    have e : (k : ℝ) * u + l * v - z = ((k : ℝ) - x) * u + ((l : ℝ) - y) * v := by
      rw [← h]; ring
    rw [e]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul]
    have := mul_le_mul_of_nonneg_right hxk (abs_nonneg u)
    have := mul_le_mul_of_nonneg_right hyl (abs_nonneg v)
    linarith
  have hr_near : |(r : ℝ) - zr| ≤ A := by
    have h := near r1 r2 zr solr
    rw [abs_of_pos r10', abs_of_pos r20'] at h
    have e : (r : ℝ) = (k : ℝ) * r1 + l * r2 := by rw [hr]; push_cast; ring
    rw [e]; linarith
  have ht_near : |(t : ℝ) - zt| ≤ T / 2 := by
    have h := near t1 t2 zt solt
    have e : (t : ℝ) = (k : ℝ) * t1 + l * t2 := by rw [ht]; push_cast; ring
    rw [e]; linarith
  refine ⟨r, s, ?_⟩
  intro P1 Q1
  have eP : P1 = P := rfl
  have eQ : Q1 = Q := rfl
  rw [eP, eQ]
  have hdiff : (r : ℝ) / P - s / Q = t / (P * Q) := by
    have h : Q * r - P * s = t := by
      have := congrArg (fun z : ℤ => (z : ℝ)) comb
      push_cast [hPP, hQQ] at this
      exact this
    rw [← h]; field_simp
  have ht0 : (0 : ℝ) ≤ t := by
    have := (abs_le.mp ht_near).1
    rw [hzt] at this; linarith
  have htT : (t : ℝ) ≤ T := by
    have := (abs_le.mp ht_near).2
    rw [hzt] at this; linarith
  refine ⟨?_, ?_, ?_⟩
  · have e : (r : ℝ) / P - (j0 + j1) / 2 = ((r : ℝ) - zr) / P := by
      rw [hzr]; field_simp
    rw [e, abs_div, abs_of_pos P0, div_le_iff₀ P0]
    refine le_trans hr_near (le_of_eq ?_)
    rw [hAdef]; ring
  · rw [hdiff]; exact div_nonneg ht0 (mul_pos P0 Q0).le
  · rw [hdiff, div_le_iff₀ (mul_pos P0 Q0)]
    refine le_trans htT (le_of_eq ?_)
    rw [hTdef]; ring

/-! ## Free windows -/

lemma digit_zero {l n M : ℕ} (hl : 2 ≤ l) {ξ : ℝ} {r : ℤ} (h1 : (r : ℝ) / (l : ℝ) ^ n ≤ ξ)
    (h2 : ξ < r / (l : ℝ) ^ n + 1 / (l : ℝ) ^ M) {k : ℕ} (hk1 : n < k) (hk2 : k ≤ M) :
    digit l ξ k = 0 := by
  have l0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have l1 : (1 : ℝ) ≤ l := by exact_mod_cast (by omega : 1 ≤ l)
  have fl : ∀ j, n ≤ j → j ≤ M → ⌊ξ * (l : ℝ) ^ j⌋ = r * (l : ℤ) ^ (j - n) := by
    intro j hnj hjM
    have ej : (l : ℝ) ^ j = (l : ℝ) ^ n * (l : ℝ) ^ (j - n) := by
      rw [← pow_add]; congr 1; omega
    have pj : (0 : ℝ) < (l : ℝ) ^ j := pow_pos l0 _
    have e : (r : ℝ) / (l : ℝ) ^ n * (l : ℝ) ^ j = r * (l : ℝ) ^ (j - n) := by
      rw [ej]
      have : (l : ℝ) ^ n ≠ 0 := (pow_pos l0 _).ne'
      field_simp
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · rw [← e]; exact mul_le_mul_of_nonneg_right h1 pj.le
    · have h3 := mul_lt_mul_of_pos_right h2 pj
      rw [add_mul, e] at h3
      have h4 : 1 / (l : ℝ) ^ M * (l : ℝ) ^ j ≤ 1 := by
        rw [one_div_mul_eq_div, div_le_one (pow_pos l0 _)]
        exact pow_le_pow_right₀ l1 hjM
      linarith
  unfold digit
  rw [fl k (by omega) hk2, fl (k - 1) (by omega) (by omega)]
  have : (l : ℤ) ^ (k - n) = (l : ℤ) * (l : ℤ) ^ (k - 1 - n) := by
    rw [← pow_succ']; congr 1; omega
  rw [this]; ring

/-- No non-zero digit and no digit change of the base `l` with position in `(Y, RY]`. -/
def Free (l : ℕ) (ξ R Y : ℝ) : Prop :=
  ∀ k : ℕ, Y < (k : ℝ) * log l → (k : ℝ) * log l ≤ R * Y → digit l ξ k = 0 ∧ digit l ξ (k + 1) = 0

/-- **Free windows in both bases** for `1 < R < 2`, on a subinterval of any interval. -/
theorem free_windows {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hE : EvertseCor1 (p * q).primeFactors) {R : ℝ} (hR1 : 1 < R) (hR2 : R < 2)
    (j0 j1 : ℝ) (hj : j0 < j1) :
    ∃ Y1 : ℝ, ∀ Y, Y1 ≤ Y → ∃ a b : ℝ, j0 < a ∧ a < b ∧ b < j1 ∧
      ∀ ξ ∈ Ioo a b, Free p ξ R Y ∧ Free q ξ R Y := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hw : 0 < j1 - j0 := by linarith
  obtain ⟨Y2, hcp⟩ := close_pair hp hq hpq hE hR1 hR2 j0 j1 hj
  set L : ℝ := log (4 / (j1 - j0)) with hL
  refine ⟨|Y2| + |L| + 1, fun Y hY => ?_⟩
  have f2 := abs_nonneg Y2
  have f3 := abs_nonneg L
  have hY0 : 0 < Y := by linarith
  obtain ⟨r, s, h1, h2, h3⟩ := hcp Y (le_trans (le_abs_self _) (by linarith))
  set n := ⌊Y / log p⌋₊ with hn
  set m := ⌊Y / log q⌋₊ with hm
  set mx : ℝ := max (p : ℝ) q with hmx
  have mx0 : 0 < mx := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  set len : ℝ := exp (-(R * Y)) / (2 * mx) with hlen
  have len0 : 0 < len := div_pos (exp_pos _) (by linarith)
  set a : ℝ := (r : ℝ) / (p : ℝ) ^ n with ha
  have hlenw : len < (j1 - j0) / 4 := by
    have h4 : len ≤ exp (-(R * Y)) := by
      rw [hlen]
      refine div_le_self (exp_pos _).le ?_
      have : (p : ℝ) ≤ mx := le_max_left _ _
      linarith
    have h5 : exp (-(R * Y)) < (j1 - j0) / 4 := by
      have h6 : L < R * Y := by
        have hRY : Y ≤ R * Y := le_mul_of_one_le_left hY0.le hR1.le
        exact lt_of_le_of_lt (le_abs_self _) (by linarith)
      have h7 : 4 / (j1 - j0) < exp (R * Y) := by
        rw [← exp_log (div_pos (by norm_num : (0 : ℝ) < 4) hw), ← hL]
        exact exp_lt_exp.mpr h6
      rw [exp_neg, inv_lt_comm₀ (exp_pos _) (by positivity), inv_div]
      exact h7
    linarith
  have habs := abs_le.mp h1
  refine ⟨a, a + len, by linarith [habs.1], by linarith, by linarith [habs.2], ?_⟩
  intro ξ hξ
  -- common bound on the length of the cylinder
  have cyl : ∀ (l : ℕ), 2 ≤ l → exp (-(R * Y)) / l ≤ 1 / (l : ℝ) ^ (⌊R * Y / log l⌋₊ + 1) := by
    intro l hl
    have l0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
    have hRY0 : 0 ≤ R * Y := mul_nonneg (by linarith) hY0.le
    have h4 := (floor_pos_bounds hl hRY0).2.2
    rw [exp_neg, pow_succ, div_le_div_iff₀ l0 (mul_pos (pow_pos l0 _) l0), one_mul,
      ← mul_assoc]
    refine mul_le_of_le_one_left l0.le ?_
    rw [inv_mul_le_iff₀ (exp_pos _), mul_one]
    exact h4
  have zero : ∀ (l : ℕ), 2 ≤ l → ∀ t : ℤ, (t : ℝ) / (l : ℝ) ^ ⌊Y / log l⌋₊ ≤ ξ →
      ξ < t / (l : ℝ) ^ ⌊Y / log l⌋₊ + exp (-(R * Y)) / l → Free l ξ R Y := by
    intro l hl t g1 g2 k k1 k2
    have hL0 : 0 < log (l : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < l))
    have g3 : ξ < t / (l : ℝ) ^ ⌊Y / log l⌋₊ + 1 / (l : ℝ) ^ (⌊R * Y / log l⌋₊ + 1) :=
      lt_of_lt_of_le g2 (add_le_add_right (cyl l hl) _)
    have hk1 : ⌊Y / log l⌋₊ < k := by
      rw [Nat.floor_lt (div_nonneg hY0.le hL0.le), div_lt_iff₀ hL0]
      exact k1
    have hk2 : k ≤ ⌊R * Y / log l⌋₊ := by
      have hRY0 : 0 ≤ R * Y := mul_nonneg (by linarith) hY0.le
      rw [Nat.le_floor_iff (div_nonneg hRY0 hL0.le), le_div_iff₀ hL0]
      exact k2
    exact ⟨digit_zero hl g1 g3 hk1 (by omega), digit_zero hl g1 g3 (by omega) (by omega)⟩
  have plen : len ≤ exp (-(R * Y)) / (2 * p) :=
    div_le_div_of_nonneg_left (exp_pos _).le (by linarith)
      (by have : (p : ℝ) ≤ mx := le_max_left _ _; linarith)
  have qlen : len ≤ exp (-(R * Y)) / (2 * q) :=
    div_le_div_of_nonneg_left (exp_pos _).le (by linarith)
      (by have : (q : ℝ) ≤ mx := le_max_right _ _; linarith)
  have half : ∀ l : ℝ, 2 ≤ l → exp (-(R * Y)) / (2 * l) + exp (-(R * Y)) / (2 * l)
      = exp (-(R * Y)) / l := by
    intro l hl
    have : l ≠ 0 := by linarith
    field_simp
    ring
  constructor
  · refine zero p hp r (by rw [← hn, ← ha]; exact hξ.1.le) ?_
    rw [← hn, ← ha]
    have h4 : exp (-(R * Y)) / (2 * p) ≤ exp (-(R * Y)) / p := by
      rw [← half p hpr]
      have : 0 ≤ exp (-(R * Y)) / (2 * p) := div_nonneg (exp_pos _).le (by linarith)
      linarith
    exact lt_of_lt_of_le hξ.2 (add_le_add_right (le_trans plen h4) _)
  · have hb : (s : ℝ) / (q : ℝ) ^ m ≤ a := by linarith
    refine zero q hq s (by rw [← hm]; linarith [hξ.1]) ?_
    rw [← hm, ← half q hqr]
    have h4 : ξ < a + exp (-(R * Y)) / (2 * q) := lt_of_lt_of_le hξ.2 (add_le_add_right qlen _)
    linarith

/-- **A generic real number** has arbitrarily late free windows in both bases. -/
theorem generic_free_windows {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hE : EvertseCor1 (p * q).primeFactors) {R : ℝ} (hR1 : 1 < R) (hR2 : R < 2) :
    ∀ᶠ ξ in residual ℝ, Irrational ξ ∧ ∀ N : ℕ, ∃ Y : ℝ, (N : ℝ) ≤ Y ∧
      Free p ξ R Y ∧ Free q ξ R Y := by
  have main : ∀ N : ℕ, ∀ᶠ ξ in residual ℝ, ∃ Y : ℝ, (N : ℝ) ≤ Y ∧
      Free p ξ R Y ∧ Free q ξ R Y := by
    intro N
    set U : Set ℝ := ⋃₀ {I : Set ℝ | IsOpen I ∧ ∃ Y : ℝ, (N : ℝ) ≤ Y ∧
      ∀ ξ ∈ I, Free p ξ R Y ∧ Free q ξ R Y} with hU
    have hopen : IsOpen U := isOpen_sUnion (fun I hI => hI.1)
    have hdense : Dense U := by
      rw [dense_iff_inter_open]
      intro V hV hne
      obtain ⟨v, hv⟩ := hne
      obtain ⟨j0, j1, hvj, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hV.mem_nhds hv)
      obtain ⟨Y1, h⟩ := free_windows hp hq hpq hE hR1 hR2 j0 j1 (lt_trans hvj.1 hvj.2)
      set Y := max Y1 N with hY
      obtain ⟨a, b, ha, hab, hb, hfree⟩ := h Y (le_max_left _ _)
      refine ⟨(a + b) / 2, hsub ⟨by linarith, by linarith⟩, ?_⟩
      refine mem_sUnion.mpr ⟨Ioo a b, ⟨isOpen_Ioo, Y, le_max_right _ _, hfree⟩, ?_⟩
      exact ⟨by linarith, by linarith⟩
    filter_upwards [residual_of_dense_open hopen hdense] with ξ hξ
    obtain ⟨I, ⟨_, Y, hY, hfree⟩, hξI⟩ := mem_sUnion.mp hξ
    exact ⟨Y, hY, hfree ξ hξI⟩
  filter_upwards [eventually_residual_irrational, eventually_countable_forall.mpr main] with ξ h1 h2
  exact ⟨h1, h2⟩

end TwoPrimesSharp
