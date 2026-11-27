import LeanCheck.TwoPrimesSUnit

/-!
# Witnesses cannot be small: lower bounds

For two primes `p < q` and some targets `t` every witness is large.

* `lower_one_level`: `t = (q^(m²) - 1)/2` forces `|k| > (1-2ε) t - ε`.  So no exponent below one
  is possible in an upper bound for witnesses.
* `lower_close_levels`: if moreover `p^(n²)` is close to `q^(m²)`, then `|k|` is large.
* `exists_close_levels`: infinitely many pairs have `|m² ln q - n² ln p| ≤ 3 √(ln p ln q)`.
* `lower_linear`: for small `ε` there are arbitrarily large `t` all of whose witnesses satisfy
  `|k| ≥ t / (32 R (1+R) ε)`, where `R = exp (3 √(ln p ln q))`.
* `no_linear_bound`: if `m² ln q - n² ln p` comes arbitrarily close to zero, then no bound
  `|k| ≤ C |t|` holds at any radius below `1/4`.
-/

namespace TwoPrimesLower

open Finset Real TwoPrimesEffective

/-- The distance from the nearest integer. -/
noncomputable def dist1 (x : ℝ) : ℝ := |x - round x|

lemma dist1_le (x : ℝ) (z : ℤ) : dist1 x ≤ |x - z| := round_le x z

lemma dist1_add_le (x y : ℝ) : dist1 (x + y) ≤ dist1 x + |y| := by
  refine le_trans (dist1_le _ (round x)) ?_
  have e : x + y - round x = (x - round x) + y := by ring
  rw [e]
  exact abs_add_le _ _

lemma dist1_add_int (x : ℝ) (z : ℤ) : dist1 (x + z) = dist1 x := by
  unfold dist1
  rw [round_add_intCast]
  push_cast
  congr 1; ring

lemma dist1_neg_le (x : ℝ) : dist1 (-x) ≤ dist1 x := by
  refine le_trans (dist1_le _ (-round x)) ?_
  have e : -x - ((-round x : ℤ) : ℝ) = -(x - round x) := by push_cast; ring
  rw [e, abs_neg]
  rfl

lemma dist1_sub_le (x y : ℝ) : dist1 (x - y) ≤ dist1 x + dist1 y := by
  refine le_trans (dist1_le _ (round x - round y)) ?_
  have e : x - y - ((round x - round y : ℤ) : ℝ) = (x - round x) - (y - round y) := by
    push_cast; ring
  rw [e]
  exact abs_sub _ _

lemma small_dist {p : ℕ} {ε : ℝ} {k : ℤ} (h : Small p ε k) (n : ℕ) :
    dist1 ((k : ℝ) / (p : ℝ) ^ (n ^ 2)) < ε := h n

/-- For `Q = 2t+1` the number `t/Q` is far from the integers. -/
lemma dist1_half {t Q : ℕ} (hQ : Q = 2 * t + 1) :
    (1 : ℝ) / 2 - 1 / (2 * Q) ≤ dist1 ((t : ℝ) / Q) := by
  have hQ0 : (0 : ℝ) < Q := by
    have : 0 < Q := by omega
    exact_mod_cast this
  have hQr : (Q : ℝ) = 2 * t + 1 := by exact_mod_cast hQ
  have e : (t : ℝ) / Q = 1 / 2 - 1 / (2 * Q) := by
    field_simp
    linarith
  have h2 : 1 / (2 * (Q : ℝ)) ≤ 1 / 2 := by
    refine one_div_le_one_div_of_le two_pos ?_
    have : (1 : ℝ) ≤ Q := by
      have : 1 ≤ Q := by omega
      exact_mod_cast this
    linarith
  have h3 : 0 ≤ 1 / (2 * (Q : ℝ)) := by positivity
  unfold dist1
  rw [e]
  set u : ℝ := 1 / (2 * (Q : ℝ)) with hu
  rcases le_or_gt (round ((1 : ℝ) / 2 - u)) 0 with h | h
  · have : ((round ((1 : ℝ) / 2 - u) : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
    exact le_trans (by linarith) (le_abs_self _)
  · have : (1 : ℝ) ≤ ((round ((1 : ℝ) / 2 - u) : ℤ) : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ round ((1 : ℝ) / 2 - u) by omega)
    exact le_trans (by linarith) (neg_le_abs _)

lemma far_from_half {q m t : ℕ} (hQ : q ^ (m ^ 2) = 2 * t + 1) {ε : ℝ} {k : ℤ}
    (hk : Small q ε (k - t)) :
    (1 : ℝ) / 2 - 1 / (2 * (q : ℝ) ^ (m ^ 2)) - ε < dist1 ((k : ℝ) / (q : ℝ) ^ (m ^ 2)) := by
  set Q : ℕ := q ^ (m ^ 2) with hQd
  have hQc : (Q : ℝ) = (q : ℝ) ^ (m ^ 2) := by rw [hQd]; push_cast; rfl
  have h1 := dist1_half (t := t) (Q := Q) hQ
  rw [hQc] at h1
  have h2 := small_dist hk m
  have h3 := dist1_sub_le ((k : ℝ) / (q : ℝ) ^ (m ^ 2))
    (((k - t : ℤ) : ℝ) / (q : ℝ) ^ (m ^ 2))
  have e : (k : ℝ) / (q : ℝ) ^ (m ^ 2) - ((k - t : ℤ) : ℝ) / (q : ℝ) ^ (m ^ 2)
      = (t : ℝ) / (q : ℝ) ^ (m ^ 2) := by
    push_cast; ring
  rw [e] at h3
  linarith

/-- **The exponent cannot be below one.** -/
theorem lower_one_level {q m t : ℕ} (hQ : q ^ (m ^ 2) = 2 * t + 1) {ε : ℝ} {k : ℤ}
    (hk : Small q ε (k - t)) : (1 - 2 * ε) * t - ε < |(k : ℝ)| := by
  have hQr : (q : ℝ) ^ (m ^ 2) = 2 * t + 1 := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (q : ℝ) ^ (m ^ 2) := by rw [hQr]; positivity
  have h1 := far_from_half hQ hk
  have h2 : dist1 ((k : ℝ) / (q : ℝ) ^ (m ^ 2)) ≤ |(k : ℝ)| / (q : ℝ) ^ (m ^ 2) := by
    refine le_trans (dist1_le _ 0) (le_of_eq ?_)
    rw [Int.cast_zero, sub_zero, abs_div, abs_of_pos hQ0]
  have h3 := lt_of_lt_of_le h1 h2
  rw [lt_div_iff₀ hQ0] at h3
  have e : (1 / 2 - 1 / (2 * (q : ℝ) ^ (m ^ 2)) - ε) * (q : ℝ) ^ (m ^ 2)
      = (1 / 2 - ε) * (q : ℝ) ^ (m ^ 2) - 1 / 2 := by
    field_simp
    ring
  rw [e, hQr] at h3
  linarith

/-- With a level of the other base close by, the witness is far larger. -/
theorem lower_close_levels {p q m n t : ℕ} (hp : 0 < p) (hQ : q ^ (m ^ 2) = 2 * t + 1) {ε : ℝ}
    {k : ℤ} (hkp : Small p ε k) (hkq : Small q ε (k - t)) :
    (1 - 4 * ε) * t - 2 * ε < |(k : ℝ)| * |(q : ℝ) ^ (m ^ 2) / (p : ℝ) ^ (n ^ 2) - 1| := by
  have hQr : (q : ℝ) ^ (m ^ 2) = 2 * t + 1 := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (q : ℝ) ^ (m ^ 2) := by rw [hQr]; positivity
  have hP0 : (0 : ℝ) < (p : ℝ) ^ (n ^ 2) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp
    positivity
  have h1 := far_from_half hQ hkq
  have h2 := small_dist hkp n
  have h3 := dist1_add_le ((k : ℝ) / (p : ℝ) ^ (n ^ 2))
    ((k : ℝ) / (q : ℝ) ^ (m ^ 2) - (k : ℝ) / (p : ℝ) ^ (n ^ 2))
  rw [add_sub_cancel] at h3
  have e : (k : ℝ) / (q : ℝ) ^ (m ^ 2) - (k : ℝ) / (p : ℝ) ^ (n ^ 2)
      = -((k : ℝ) * ((q : ℝ) ^ (m ^ 2) / (p : ℝ) ^ (n ^ 2) - 1) / (q : ℝ) ^ (m ^ 2)) := by
    field_simp
    ring
  rw [e, abs_neg, abs_div, abs_mul, abs_of_pos hQ0] at h3
  have h4 : (1 : ℝ) / 2 - 1 / (2 * (q : ℝ) ^ (m ^ 2)) - 2 * ε
      < |(k : ℝ)| * |(q : ℝ) ^ (m ^ 2) / (p : ℝ) ^ (n ^ 2) - 1| / (q : ℝ) ^ (m ^ 2) := by
    linarith
  rw [lt_div_iff₀ hQ0] at h4
  have e2 : (1 / 2 - 1 / (2 * (q : ℝ) ^ (m ^ 2)) - 2 * ε) * (q : ℝ) ^ (m ^ 2)
      = (1 / 2 - 2 * ε) * (q : ℝ) ^ (m ^ 2) - 1 / 2 := by
    field_simp
    ring
  rw [e2, hQr] at h4
  rw [hQr]
  linarith

/-! ## Close levels -/

lemma irrational_beta {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Irrational (sqrt (log q) / sqrt (log p)) := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < log (q : ℝ) := log_pos (by exact_mod_cast hq.one_lt)
  rintro ⟨r, hr⟩
  have hr0 : 0 < (r : ℝ) := by
    rw [hr]
    exact div_pos (sqrt_pos.mpr hlq) (sqrt_pos.mpr hlp)
  set b : ℕ := r.den with hb
  set a : ℕ := r.num.natAbs with ha
  have hrpos : 0 < r := by exact_mod_cast hr0
  have hnum : (a : ℤ) = r.num := by
    rw [ha]; exact Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hrpos.le)
  have hrab : (r : ℝ) = (a : ℝ) / b := by
    rw [Rat.cast_def, ← hnum, Int.cast_natCast]
  have hb0 : (0 : ℝ) < b := by
    have : 0 < b := r.den_pos
    exact_mod_cast this
  have h2 : (r : ℝ) ^ 2 = log q / log p := by
    rw [hr, div_pow, sq_sqrt hlq.le, sq_sqrt hlp.le]
  rw [hrab, div_pow, div_eq_div_iff (pow_ne_zero _ hb0.ne') hlp.ne'] at h2
  have h3 : log ((p : ℝ) ^ (a ^ 2)) = log ((q : ℝ) ^ (b ^ 2)) := by
    rw [log_pow, log_pow]
    push_cast
    linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have h4 := log_injOn_pos (Set.mem_Ioi.mpr (pow_pos hp0 _)) (Set.mem_Ioi.mpr (pow_pos hq0 _)) h3
  have h5 : p ^ (a ^ 2) = q ^ (b ^ 2) := by exact_mod_cast h4
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero _ r.den_pos.ne'
  have h6 : q ∣ p ^ (a ^ 2) := h5 ▸ dvd_pow_self q hb2
  have h7 := hq.dvd_of_dvd_pow h6
  exact hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp h7).symm

/-- **Infinitely many pairs of levels are close.** -/
theorem exists_close_levels {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q) (N : ℕ) :
    ∃ m n : ℕ, N ≤ m ∧ 1 ≤ m ∧ 1 ≤ n ∧
      |((m ^ 2 : ℕ) : ℝ) * log q - ((n ^ 2 : ℕ) : ℝ) * log p| ≤ 3 * sqrt (log p * log q) := by
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < log (q : ℝ) := log_pos (by exact_mod_cast hq.one_lt)
  set sp : ℝ := sqrt (log p) with hsp
  set sq : ℝ := sqrt (log q) with hsq
  have hsp0 : 0 < sp := sqrt_pos.mpr hlp
  have hsq0 : 0 < sq := sqrt_pos.mpr hlq
  have hsp2 : sp ^ 2 = log p := sq_sqrt hlp.le
  have hsq2 : sq ^ 2 = log q := sq_sqrt hlq.le
  set β : ℝ := sq / sp with hβ
  have hβ1 : 1 ≤ β := by
    rw [hβ, le_div_iff₀ hsp0, one_mul]
    refine sqrt_le_sqrt (log_le_log (by exact_mod_cast hp.pos) ?_)
    exact_mod_cast hlt.le
  have hirr : Irrational β := irrational_beta hp hq (Nat.ne_of_lt hlt)
  have hinf := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hirr
  have hden : ∃ r : ℚ, |β - r| < 1 / (r.den : ℝ) ^ 2 ∧ N + 1 ≤ r.den := by
    by_contra hcon
    push Not at hcon
    refine hinf (Set.Finite.subset
      (s := (fun w : ℤ × ℕ => (w.1 : ℚ) / w.2) ''
        (Set.Icc (-(⌈(β + 1) * (N + 1)⌉)) (⌈(β + 1) * (N + 1)⌉) ×ˢ Set.Iic (N + 1)))
      (((Set.finite_Icc _ _).prod (Set.finite_Iic _)).image _) ?_)
    intro r hr
    have hr' : |β - r| < 1 / (r.den : ℝ) ^ 2 := hr
    have hd := hcon r hr'
    have hd0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
    have hd1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
    refine ⟨(r.num, r.den), ⟨?_, Set.mem_Iic.mpr (by omega)⟩, Rat.num_div_den r⟩
    have h1 : |(r : ℝ)| ≤ β + 1 := by
      have h2 : 1 / (r.den : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ hd1
      have h3 := abs_sub_abs_le_abs_sub (r : ℝ) β
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ β)] at h3
      linarith
    have h4 : |(r.num : ℝ)| ≤ (β + 1) * (N + 1) := by
      have e : (r.num : ℝ) = (r : ℝ) * r.den := by
        rw [Rat.cast_def]; field_simp
      rw [e, abs_mul, abs_of_pos hd0]
      refine mul_le_mul h1 ?_ hd0.le (by linarith)
      exact_mod_cast (show r.den ≤ N + 1 by omega)
    have h5 : |r.num| ≤ ⌈(β + 1) * (N + 1)⌉ := by
      have h6 := le_trans h4 (Int.le_ceil _)
      exact_mod_cast h6
    exact Set.mem_Icc.mpr (abs_le.mp h5)
  obtain ⟨r, hr, hN⟩ := hden
  set m : ℕ := r.den with hm
  have hm1 : 1 ≤ m := r.den_pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast r.den_pos
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast r.den_pos
  have happ : |(m : ℝ) * β - r.num| < 1 / m := by
    have e : (m : ℝ) * β - r.num = (m : ℝ) * (β - r) := by
      rw [Rat.cast_def, ← hm]; field_simp
    rw [e, abs_mul, abs_of_pos hm0]
    have h1 := mul_lt_mul_of_pos_left hr hm0
    have e2 : (m : ℝ) * (1 / (m : ℝ) ^ 2) = 1 / m := by field_simp
    rwa [e2] at h1
  have hnum : 1 ≤ r.num := by
    have h1 : (0 : ℝ) < r.num := by
      have h2 := (abs_lt.mp happ).2
      have h3 : 1 / (m : ℝ) ≤ 1 := by rw [div_le_one hm0]; exact hmR
      have h4 : (1 : ℝ) ≤ (m : ℝ) * β := one_le_mul_of_one_le_of_one_le hmR hβ1
      have h5 : (m : ℝ) * β - 1 / m ≠ 0 := by
        intro h0
        have h6 : (m : ℝ) * β = 1 / m := by linarith
        have h7 : β = ((1 / (m : ℚ) ^ 2 : ℚ) : ℝ) := by
          push_cast
          field_simp at h6 ⊢
          linarith
        exact hirr ⟨_, h7.symm⟩
      have h8 : 0 ≤ (m : ℝ) * β - 1 / m := by linarith
      have h9 := lt_of_le_of_ne h8 (Ne.symm h5)
      linarith
    exact_mod_cast h1
  set n : ℕ := r.num.toNat with hn
  have hnc : (n : ℝ) = r.num := by
    have : (n : ℤ) = r.num := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have hn1 : 1 ≤ n := by omega
  refine ⟨m, n, by omega, hm1, hn1, ?_⟩
  rw [← hnc] at happ
  have hsum : (m : ℝ) * β + n ≤ 2 * (m : ℝ) * β + 1 / m := by
    have h1 := (abs_lt.mp happ).1
    linarith
  have hsum0 : (0 : ℝ) ≤ (m : ℝ) * β + n := by
    have : (0 : ℝ) ≤ (m : ℝ) * β := mul_nonneg hm0.le (by linarith)
    positivity
  have hprod : |((m : ℝ) * β - n) * ((m : ℝ) * β + n)| ≤ 3 * β := by
    rw [abs_mul, abs_of_nonneg hsum0]
    refine le_trans (mul_le_mul happ.le hsum hsum0 (by positivity)) ?_
    have e : 1 / (m : ℝ) * (2 * m * β + 1 / m) = 2 * β + 1 / (m : ℝ) ^ 2 := by field_simp
    rw [e]
    have h1 : 1 / (m : ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ hmR
    linarith
  have e1 : ((m ^ 2 : ℕ) : ℝ) * log q - ((n ^ 2 : ℕ) : ℝ) * log p
      = log p * (((m : ℝ) * β - n) * ((m : ℝ) * β + n)) := by
    have h1 : log (q : ℝ) = β ^ 2 * log p := by
      rw [hβ, div_pow, hsq2, hsp2]; field_simp
    rw [h1]; push_cast; ring
  have e2 : log (p : ℝ) * (3 * β) = 3 * sqrt (log p * log q) := by
    rw [sqrt_mul hlp.le, ← hsp, ← hsq, ← hsp2, hβ]; field_simp
  rw [e1, abs_mul, abs_of_pos hlp, ← e2]
  exact mul_le_mul_of_nonneg_left hprod hlp.le

/-! ## The linear lower bound -/

/-- Among `N+1` equally spaced points one is far from `N` given points modulo `1`. -/
lemma exists_far {ι : Type} (s : Finset ι) (x : ι → ℝ) :
    ∃ r ∈ range (s.card + 1), ∀ i ∈ s,
      1 / (2 * (s.card + 1 : ℝ)) ≤ dist1 ((r : ℝ) / (s.card + 1) + x i) := by
  classical
  set N : ℕ := s.card with hN
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  by_contra hcon
  push Not at hcon
  have h : ∀ r ∈ range (N + 1), ∃ i ∈ s, dist1 ((r : ℝ) / (N + 1) + x i)
      < 1 / (2 * (N + 1 : ℝ)) := hcon
  obtain ⟨i0, _, _⟩ := h 0 (mem_range.mpr (Nat.succ_pos _))
  haveI : Nonempty ι := ⟨i0⟩
  choose! f hf hlt using h
  have hinj : Set.InjOn f ((range (N + 1) : Finset ℕ) : Set ℕ) := by
    intro a ha b hb hab
    rw [mem_coe] at ha hb
    by_contra hne
    have h1 := hlt a ha
    have h2 := hlt b hb
    rw [← hab] at h2
    have h3 := dist1_sub_le ((a : ℝ) / (N + 1) + x (f a)) ((b : ℝ) / (N + 1) + x (f a))
    have e : (a : ℝ) / (N + 1) + x (f a) - ((b : ℝ) / (N + 1) + x (f a))
        = ((a : ℝ) - b) / (N + 1) := by ring
    rw [e] at h3
    have h4 : dist1 (((a : ℝ) - b) / (N + 1)) < 1 / (N + 1 : ℝ) := by
      have e2 : 1 / (2 * (N + 1 : ℝ)) + 1 / (2 * (N + 1 : ℝ)) = 1 / (N + 1 : ℝ) := by
        field_simp; ring
      linarith
    rw [mem_range] at ha hb
    set z : ℤ := round (((a : ℝ) - b) / (N + 1)) with hz
    unfold dist1 at h4
    rw [← hz] at h4
    have h5 : |((a : ℝ) - b) - z * (N + 1)| < 1 := by
      have e3 : ((a : ℝ) - b) - z * (N + 1) = (((a : ℝ) - b) / (N + 1) - z) * (N + 1) := by
        field_simp
      rw [e3, abs_mul, abs_of_pos hN0]
      have := mul_lt_mul_of_pos_right h4 hN0
      rwa [one_div_mul_cancel hN0.ne'] at this
    have h6 : |((a : ℤ) - b) - z * (N + 1)| < 1 := by exact_mod_cast h5
    have h7 := Int.abs_lt_one_iff.mp h6
    have h8 : (a : ℤ) - b = z * (N + 1) := by omega
    have h9 : z = 0 := by
      by_contra hz0
      have h10 : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
      have h11 : |(a : ℤ) - b| = |z| * (N + 1) := by
        rw [h8, abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ (N : ℤ) + 1)]
      have h12 : |(a : ℤ) - b| < (N : ℤ) + 1 := abs_lt.mpr ⟨by omega, by omega⟩
      have h13 := le_mul_of_one_le_left (by omega : (0 : ℤ) ≤ (N : ℤ) + 1) h10
      omega
    rw [h9, zero_mul] at h8
    exact hne (by omega)
  have hcard := card_le_card_of_injOn f (fun r hr => hf r hr) hinj
  rw [card_range] at hcard
  omega

/-- **For infinitely many targets every witness is at least `c |t| / ε`.** -/
theorem lower_linear {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q) {R ε : ℝ}
    (hR : R = exp (3 * sqrt (log p * log q))) (hε : 0 < ε)
    (hεs : ε ≤ 1 / (64 * R * (1 + R))) (T : ℝ) :
    ∃ t : ℤ, T ≤ t ∧ ∀ k : ℤ, Small p ε k → Small q ε (k - t) →
      (t : ℝ) / (32 * R * (1 + R) * ε) ≤ |(k : ℝ)| := by
  classical
  have hR1 : 1 ≤ R := by
    rw [hR]; exact one_le_exp (by positivity)
  have hR0 : 0 < R := by linarith
  have hRR : 0 < 1 + R := by linarith
  have hRRR : 1 ≤ R * (1 + R) := one_le_mul_of_one_le_of_one_le hR1 (by linarith)
  have hε1 : ε ≤ 1 / 64 := by
    refine le_trans hεs (one_div_le_one_div_of_le (by norm_num) ?_)
    rw [mul_assoc]; linarith
  set X : ℝ := 1 / (8 * (1 + R) * ε) with hX
  have hεX : 64 * R * (1 + R) * ε ≤ 1 := by
    have := hεs
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hX1 : 1 ≤ X := by
    rw [hX, le_div_iff₀ (by positivity), one_mul]
    have h1 : 8 * (1 + R) * ε ≤ 64 * R * (1 + R) * ε := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hRR.le) hε.le
      linarith
    linarith
  set M : ℕ := ⌊X⌋₊ with hM
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hX1)
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMX : (M : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hXM : X ≤ 2 * (M : ℝ) := by
    have := Nat.lt_floor_add_one X
    rw [← hM] at this
    linarith
  set J : ℕ := M - 1 with hJ
  have hJM : (J : ℝ) + 1 = M := by
    have : J + 1 = M := by omega
    exact_mod_cast this
  -- a far level
  have hp2 : 2 ≤ p := hp.two_le
  set A : ℝ := 8 * M + 4 * |T| * (4 * M) + 4 with hA
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (R * A) (show (1 : ℝ) < 2 by norm_num)
  obtain ⟨m, n, hmN, hm1, hn1, hclose⟩ := exists_close_levels hp hq hlt N
  set P : ℝ := (p : ℝ) ^ (n ^ 2) with hP
  set Q : ℝ := (q : ℝ) ^ (m ^ 2) with hQ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hP0 : 0 < P := pow_pos hp0 _
  have hQ0 : 0 < Q := pow_pos hq0 _
  have hPQ : P ≤ R * Q ∧ Q ≤ R * P := by
    have h1 : log Q - log P = ((m ^ 2 : ℕ) : ℝ) * log q - ((n ^ 2 : ℕ) : ℝ) * log p := by
      rw [hQ, hP, log_pow, log_pow]
    rw [← h1] at hclose
    obtain ⟨c1, c2⟩ := abs_le.mp hclose
    constructor
    · rw [← exp_log hP0, ← exp_log hQ0, hR, ← exp_add]
      exact exp_le_exp.mpr (by linarith)
    · rw [← exp_log hP0, ← exp_log hQ0, hR, ← exp_add]
      exact exp_le_exp.mpr (by linarith)
  have hQbig : R * A ≤ Q := by
    have h1 : (2 : ℝ) ^ N ≤ Q := by
      have h2 : (2 : ℝ) ^ N ≤ (q : ℝ) ^ N :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq.two_le) N
      have h3 : N ≤ m ^ 2 := le_trans hmN (Nat.le_self_pow two_ne_zero m)
      exact le_trans h2 (pow_le_pow_right₀ (by exact_mod_cast hq.one_lt.le) h3)
    exact le_trans hN.le h1
  have hPbig : A ≤ P := by
    have h1 := le_trans hQbig hPQ.2
    exact le_of_mul_le_mul_left h1 hR0
  -- the target
  set s : Finset ℤ := Icc (-(J : ℤ)) J with hs
  have hscard : s.card = 2 * J + 1 := by
    rw [hs, Int.card_Icc]; omega
  obtain ⟨r, hr, hfar⟩ := exists_far s (fun j => (j : ℝ) * Q / P)
  rw [mem_range] at hr
  set K : ℝ := (s.card : ℝ) + 1 with hK
  have hK2 : K = 2 * M := by
    rw [hK, hscard]
    have : ((2 * J + 1 : ℕ) : ℝ) = 2 * J + 1 := by push_cast; ring
    rw [this]; linarith
  have hK0 : 0 < K := by rw [hK2]; linarith
  set y : ℝ := (r : ℝ) / K with hy
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg _) hK0.le
  have hy1 : y < 1 := by
    rw [hy, div_lt_one hK0, hK]; exact_mod_cast hr
  set t : ℤ := round (y * P) with ht
  have hterr : |y * P - t| ≤ 1 / 2 := abs_sub_round _
  have h0s : (0 : ℤ) ∈ s := by rw [hs, mem_Icc]; omega
  have hybound : 1 / (2 * K) ≤ y := by
    have h1 := hfar 0 h0s
    simp only [Int.cast_zero, zero_mul, zero_div, add_zero] at h1
    refine le_trans h1 (le_trans (dist1_le _ 0) (le_of_eq ?_))
    rw [Int.cast_zero, sub_zero, abs_of_nonneg hy0]
  have htlow : P / (4 * M) - 1 / 2 ≤ t := by
    have h1 : P / (4 * M) ≤ y * P := by
      have h2 := mul_le_mul_of_nonneg_right hybound hP0.le
      have e : 1 / (2 * K) * P = P / (4 * M) := by rw [hK2]; field_simp; ring
      rwa [e] at h2
    have := (abs_le.mp hterr).2
    linarith
  have htT : T ≤ t := by
    have h1 : 4 * |T| * (4 * M) ≤ P := by
      have h2 : 4 * |T| * (4 * M) ≤ A := by
        rw [hA]
        have : (0 : ℝ) ≤ 8 * M := by positivity
        linarith
      linarith
    have h3 : 4 * |T| ≤ P / (4 * M) := by
      rw [le_div_iff₀ (by positivity)]; exact h1
    have h4 : (2 : ℝ) ≤ P / (4 * M) := by
      rw [le_div_iff₀ (by positivity)]
      have : 8 * (M : ℝ) ≤ A := by
        rw [hA]
        have : (0 : ℝ) ≤ 4 * |T| * (4 * M) := by positivity
        linarith
      linarith
    have := le_abs_self T
    have := abs_nonneg T
    linarith
  have htP : (t : ℝ) ≤ P := by
    have h1 : y * P ≤ (1 - 1 / K) * P := by
      refine mul_le_mul_of_nonneg_right ?_ hP0.le
      have h2 : (r : ℝ) + 1 ≤ K := by
        rw [hK]; exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt_succ hr)
      rw [hy, div_le_iff₀ hK0]
      have e : (1 - 1 / K) * K = K - 1 := by field_simp
      rw [e]; linarith
    have h3 : (1 : ℝ) / 2 ≤ P / K := by
      rw [le_div_iff₀ hK0, hK2]
      have : 8 * (M : ℝ) ≤ A := by
        rw [hA]
        have : (0 : ℝ) ≤ 4 * |T| * (4 * M) := by positivity
        linarith
      linarith
    have e : (1 - 1 / K) * P = P - P / K := by field_simp
    have := (abs_le.mp hterr).1
    linarith
  refine ⟨t, htT, fun k hkp hkq => ?_⟩
  -- write `k - t` near a multiple of `Q`
  set j : ℤ := round (((k - t : ℤ) : ℝ) / Q) with hj
  set u : ℝ := ((k - t : ℤ) : ℝ) - j * Q with hu
  have huQ : |u| < ε * Q := by
    have h1 := small_dist hkq m
    have e : u = (((k - t : ℤ) : ℝ) / Q - j) * Q := by rw [hu]; field_simp
    rw [e, abs_mul, abs_of_pos hQ0]
    exact mul_lt_mul_of_pos_right h1 hQ0
  have hjbig : (J : ℤ) < |j| := by
    by_contra hcon
    rw [not_lt] at hcon
    have hjs : j ∈ s := by
      rw [hs, mem_Icc]; exact abs_le.mp hcon
    have h1 := hfar j hjs
    have h2 := small_dist hkp n
    rw [← hP] at h2
    have e : y + (j : ℝ) * Q / P = (k : ℝ) / P + ((y * P - t) / P - u / P) := by
      rw [hu]; push_cast; field_simp; ring
    rw [e] at h1
    have h3 := le_trans h1 (dist1_add_le _ _)
    have h4 : |(y * P - t) / P - u / P| ≤ 1 / (2 * P) + ε * R := by
      refine le_trans (abs_sub _ _) (add_le_add ?_ ?_)
      · rw [abs_div, abs_of_pos hP0, div_le_iff₀ hP0]
        have e2 : 1 / (2 * P) * P = 1 / 2 := by field_simp
        rw [e2]; exact hterr
      · rw [abs_div, abs_of_pos hP0, div_le_iff₀ hP0]
        refine le_trans huQ.le ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hPQ.2 hε.le
    have h5 : ε * (1 + R) ≤ 1 / (8 * M) := by
      have h6 : (M : ℝ) * (8 * (1 + R) * ε) ≤ 1 := by
        have := hMX
        rw [hX, le_div_iff₀ (by positivity)] at this
        linarith
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h7 : 1 / (2 * P) ≤ 1 / (16 * M) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have : 8 * (M : ℝ) ≤ A := by
        rw [hA]
        have : (0 : ℝ) ≤ 4 * |T| * (4 * M) := by positivity
        linarith
      linarith
    have h8 : 1 / (2 * K) = 1 / (4 * M) := by rw [hK2]; ring
    have e3 : (1 : ℝ) / (4 * M) = 1 / (8 * M) + 1 / (16 * M) + 1 / (16 * M) := by
      field_simp; ring
    have e4 : ε * (1 + R) = ε + ε * R := by ring
    have h9 : (0 : ℝ) < 1 / (16 * M) := by positivity
    rw [h8] at h3
    linarith
  have hjR : (M : ℝ) ≤ |(j : ℝ)| := by
    have : (M : ℤ) ≤ |j| := by omega
    exact_mod_cast this
  have ht0 : (0 : ℝ) ≤ t := by
    have : (0 : ℝ) ≤ |T| := abs_nonneg _
    have h1 : (2 : ℝ) ≤ P / (4 * M) := by
      rw [le_div_iff₀ (by positivity)]
      have : 8 * (M : ℝ) ≤ A := by
        rw [hA]
        have : (0 : ℝ) ≤ 4 * |T| * (4 * M) := by positivity
        linarith
      linarith
    linarith
  have hk1 : (M : ℝ) * Q - ε * Q - t ≤ |(k : ℝ)| := by
    have e : (j : ℝ) * Q = (k : ℝ) - t - u := by rw [hu]; push_cast; ring
    have h1 : (M : ℝ) * Q ≤ |(j : ℝ) * Q| := by
      rw [abs_mul, abs_of_pos hQ0]; exact mul_le_mul_of_nonneg_right hjR hQ0.le
    rw [e] at h1
    have h2 : |(k : ℝ) - t - u| ≤ |(k : ℝ)| + |(t : ℝ)| + |u| :=
      le_trans (abs_sub _ _) (add_le_add (abs_sub _ _) le_rfl)
    rw [abs_of_nonneg ht0] at h2
    linarith
  have htQ : (t : ℝ) ≤ R * Q := le_trans htP hPQ.1
  -- the constant
  have hMlow : 1 / (16 * (1 + R) * ε) ≤ (M : ℝ) := by
    have e : 1 / (16 * (1 + R) * ε) = X / 2 := by rw [hX]; field_simp; ring
    rw [e]; linarith
  set c : ℝ := 1 / (32 * R * (1 + R) * ε) with hc
  have hc2 : 2 ≤ c := by
    rw [hc, le_div_iff₀ (by positivity)]
    linarith
  have hMc : 2 * c * R ≤ (M : ℝ) := by
    have e : 2 * c * R = 1 / (16 * (1 + R) * ε) := by rw [hc]; field_simp; ring
    rw [e]; exact hMlow
  have hgoal : c * t ≤ |(k : ℝ)| := by
    have h1 : c * t ≤ c * (R * Q) := mul_le_mul_of_nonneg_left htQ (by linarith)
    have h2 : (2 * c * R) * Q ≤ (M : ℝ) * Q := mul_le_mul_of_nonneg_right hMc hQ0.le
    have h3 : ε * Q + R * Q ≤ c * (R * Q) := by
      have h4 : ε + R ≤ c * R := by
        have h5 : 2 * R ≤ c * R := mul_le_mul_of_nonneg_right hc2 hR0.le
        linarith
      have := mul_le_mul_of_nonneg_right h4 hQ0.le
      linarith
    have e : (2 * c * R) * Q = 2 * (c * (R * Q)) := by ring
    linarith
  have e : (t : ℝ) / (32 * R * (1 + R) * ε) = c * t := by rw [hc]; ring
  rw [e]; exact hgoal

/-- **If the two kinds of levels come arbitrarily close, no linear bound holds.** -/
theorem no_linear_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q)
    (hacc : ∀ η : ℝ, 0 < η → ∀ N : ℕ, ∃ m n : ℕ, N ≤ m ∧
      |((m ^ 2 : ℕ) : ℝ) * log q - ((n ^ 2 : ℕ) : ℝ) * log p| < η)
    {ε : ℝ} (hε : ε < 1 / 4) (hε0 : 0 < ε) (C : ℝ) (T : ℕ) :
    ∃ t : ℕ, T ≤ t ∧ ∀ k : ℤ, Small p ε k → Small q ε (k - t) → C * t < |(k : ℝ)| := by
  set C' : ℝ := max C 1 with hC'
  have hC1 : 1 ≤ C' := le_max_right _ _
  have hC0 : 0 < C' := by linarith
  set g : ℝ := 1 - 4 * ε with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set η : ℝ := min (g / (4 * C')) 1 with hη
  have hη0 : 0 < η := lt_min (div_pos hg0 (by linarith)) one_pos
  set A : ℕ := ⌈2 / g⌉₊ + T + 1 with hA
  obtain ⟨m, n, hmN, hclose⟩ := hacc (η / 2) (by linarith) (2 * A + 1)
  have hq3 : 3 ≤ q := by
    have := hp.two_le
    omega
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hQodd : Odd (q ^ (m ^ 2)) := hqodd.pow
  obtain ⟨t, ht⟩ := hQodd
  have htA : A ≤ t := by
    have h1 : m < q ^ (m ^ 2) := by
      have h2 : m < 2 ^ m := Nat.lt_two_pow_self
      have h3 : 2 ^ m ≤ q ^ m := Nat.pow_le_pow_left (by omega) _
      have h4 : q ^ m ≤ q ^ (m ^ 2) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_self_pow two_ne_zero m)
      omega
    omega
  refine ⟨t, by omega, fun k hkp hkq => ?_⟩
  have hbase := lower_close_levels (p := p) (n := n) hp.pos ht hkp hkq
  set Q : ℝ := (q : ℝ) ^ (m ^ 2) with hQ
  set P : ℝ := (p : ℝ) ^ (n ^ 2) with hP
  have hQ0 : 0 < Q := by
    have : (0 : ℝ) < q := by exact_mod_cast hq.pos
    positivity
  have hP0 : 0 < P := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  have hratio : |Q / P - 1| ≤ η := by
    set w : ℝ := log Q - log P with hw
    have h1 : |w| < η / 2 := by
      rw [hw, hQ, hP, log_pow, log_pow]; exact hclose
    have h2 : Q / P = exp w := by
      rw [hw, exp_sub, exp_log hQ0, exp_log hP0]
    have h3 : |w| ≤ 1 := by
      have : η ≤ 1 := min_le_right _ _
      linarith
    rw [h2]
    have := Real.abs_exp_sub_one_le h3
    linarith
  have htT : (2 : ℝ) / g ≤ t := by
    have h1 : (2 : ℝ) / g ≤ (⌈2 / g⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 / g⌉₊ : ℝ) ≤ t := by exact_mod_cast (show ⌈2 / g⌉₊ ≤ t by omega)
    linarith
  have hgt : 2 ≤ g * t := by
    rw [div_le_iff₀ hg0] at htT; linarith
  have h1 : g * t / 2 ≤ g * t - 2 * ε := by linarith
  have h2 : g * t - 2 * ε < |(k : ℝ)| * η :=
    lt_of_lt_of_le hbase (mul_le_mul_of_nonneg_left hratio (abs_nonneg _))
  have h3 : |(k : ℝ)| * η ≤ |(k : ℝ)| * (g / (4 * C')) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg _)
  have h4 : g * t / 2 < |(k : ℝ)| * (g / (4 * C')) := by linarith
  have h5 : 2 * C' * t < |(k : ℝ)| := by
    have h6 := mul_lt_mul_of_pos_right h4 (show (0 : ℝ) < 4 * C' / g by positivity)
    have e1 : g * t / 2 * (4 * C' / g) = 2 * C' * t := by field_simp; ring
    have e2 : |(k : ℝ)| * (g / (4 * C')) * (4 * C' / g) = |(k : ℝ)| := by field_simp
    rwa [e1, e2] at h6
  have h7 : C * t ≤ 2 * C' * t := by
    have : C ≤ 2 * C' := le_trans (le_max_left _ _) (by linarith)
    exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
  linarith

end TwoPrimesLower
