import LeanCheck.TwoPrimesSmoothing

/-!
# Staggered windows: the golden ratio instead of `2`

The two bases need not start their quiet stretches at the same place.  Positions are
`n * sqrt (log base)` and `w k = r^k (x0 + 4c) - 4c` with `r² = (1+√5)/2`.

* `exists_stagger`: if the two bases have at most `B` marked levels together, then for some
  `k ≤ B` one base has none in positions `(w (k+1), w (k+2)]` and the other none in
  `(w k, w (k+2)]`.
* `w_rec`: `w (k+2)² > (w (k+1) + c)² + (w k + c)² + 1`.
* `rigidity_golden`: hence rigidity at the height `w (B+2)`.
* `witness_of_density_golden`, `witness_of_critical_density_golden`,
  `witness_of_free_heights_golden`: height `64 exp(Λ)` with `Λ = φ^(B+2) (x0+4c)²`.

The densities are hypotheses.
-/

namespace TwoPrimesGolden

open Finset Real TwoPrimesEffective TwoPrimesWindows TwoPrimesFreeHeight TwoPrimesAdaptive
  TwoPrimesSharpFactor TwoPrimesSmoothing

/-- The square root of the golden ratio. -/
noncomputable def rr : ℝ := sqrt ((1 + sqrt 5) / 2)

lemma sqrt5_bounds : (2.236 : ℝ) < sqrt 5 ∧ sqrt 5 < 2.2361 := by
  constructor
  · rw [lt_sqrt (by norm_num)]; norm_num
  · rw [sqrt_lt' (by norm_num)]; norm_num

lemma rr_sq : rr ^ 2 = (1 + sqrt 5) / 2 := by
  unfold rr
  rw [sq_sqrt]
  have := sqrt_nonneg (5 : ℝ)
  linarith

lemma rr_four : rr ^ 4 = rr ^ 2 + 1 := by
  have e : rr ^ 4 = (rr ^ 2) ^ 2 := by ring
  have h5 : sqrt 5 ^ 2 = 5 := sq_sqrt (by norm_num)
  rw [e, rr_sq]
  have e2 : ((1 + sqrt 5) / 2) ^ 2 = (1 + 2 * sqrt 5 + sqrt 5 ^ 2) / 4 := by ring
  rw [e2, h5]; ring

lemma rr_bounds : (1.272 : ℝ) < rr ∧ rr < 1.2721 := by
  have h := sqrt5_bounds
  have h0 : 0 ≤ rr := sqrt_nonneg _
  have e := rr_sq
  constructor
  · refine (pow_lt_pow_iff_left₀ (by norm_num) h0 two_ne_zero).mp ?_
    rw [e]
    have : (1.272 : ℝ) ^ 2 < 1.618 := by norm_num
    linarith [h.1]
  · refine (pow_lt_pow_iff_left₀ h0 (by norm_num) two_ne_zero).mp ?_
    rw [e]
    have : (1.61806 : ℝ) < 1.2721 ^ 2 := by norm_num
    linarith [h.2]

/-- The window ends. -/
noncomputable def w (c x0 : ℝ) (k : ℕ) : ℝ := rr ^ k * (x0 + 4 * c) - 4 * c

lemma w_zero (c x0 : ℝ) : w c x0 0 = x0 := by
  unfold w; ring

lemma w_step {c x0 : ℝ} (hc : 0 < c) (hx : 50 * c ≤ x0) (k : ℕ) :
    x0 ≤ w c x0 k ∧ w c x0 k + c ≤ w c x0 (k + 1) := by
  have hr := rr_bounds.1
  have hA : 0 < x0 + 4 * c := by linarith
  have h1 : (1 : ℝ) ≤ rr ^ k := one_le_pow₀ (by linarith)
  have hm : x0 + 4 * c ≤ rr ^ k * (x0 + 4 * c) := le_mul_of_one_le_left hA.le h1
  constructor
  · unfold w; linarith
  · have e : w c x0 (k + 1) - w c x0 k = (rr - 1) * (rr ^ k * (x0 + 4 * c)) := by
      unfold w; rw [pow_succ]; ring
    have h2 : 0.272 * (x0 + 4 * c) ≤ (rr - 1) * (rr ^ k * (x0 + 4 * c)) :=
      mul_le_mul (by linarith) hm hA.le (by linarith)
    linarith

lemma w_mono {c x0 : ℝ} (hc : 0 < c) (hx : 50 * c ≤ x0) {i j : ℕ} (h : i ≤ j) :
    w c x0 i ≤ w c x0 j := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih =>
    have := (w_step hc hx m).2
    exact le_trans ih (by linarith)

/-- The recursion which the coprimality step needs. -/
lemma w_rec {c x0 : ℝ} (hc : 0 < c) (hc2 : 0.69 ≤ c ^ 2) (hx : 50 * c ≤ x0) (k : ℕ) :
    (w c x0 (k + 1) + c) ^ 2 + (w c x0 k + c) ^ 2 + 1 < w c x0 (k + 2) ^ 2 := by
  have hr := rr_bounds
  have hr4 := rr_four
  set A : ℝ := x0 + 4 * c with hA
  set m : ℝ := rr ^ k with hm
  have hm1 : 1 ≤ m := one_le_pow₀ (by linarith [hr.1])
  have hAc : 50 * c ≤ A := by rw [hA]; linarith
  have hA0 : 0 < A := by linarith
  have e0 : w c x0 k = m * A - 4 * c := by unfold w; rw [hm]
  have e1 : w c x0 (k + 1) = rr * (m * A) - 4 * c := by
    unfold w; rw [hm, hA, pow_succ]; ring
  have e2 : w c x0 (k + 2) = rr ^ 2 * (m * A) - 4 * c := by
    unfold w; rw [hm, hA, pow_add]; ring
  rw [e0, e1, e2]
  set u : ℝ := m * A with hu
  have huA : A ≤ u := le_mul_of_one_le_left hA0.le hm1
  have key : (rr ^ 2 * u - 4 * c) ^ 2 - ((rr * u - 4 * c + c) ^ 2 + (u - 4 * c + c) ^ 2)
      = 2 * u * c * (3 * (rr + 1) - 4 * rr ^ 2) - 2 * c ^ 2 := by
    have e : (rr ^ 2 * u - 4 * c) ^ 2 = rr ^ 4 * u ^ 2 - 8 * rr ^ 2 * u * c + 16 * c ^ 2 := by
      ring
    rw [e, hr4]; ring
  have hcoef : 0.34 ≤ 3 * (rr + 1) - 4 * rr ^ 2 := by
    rw [rr_sq]
    have := sqrt5_bounds.2
    linarith [hr.1]
  have huc : 50 * c ^ 2 ≤ u * c := by
    have : 50 * c ≤ u := le_trans hAc huA
    have := mul_le_mul_of_nonneg_right this hc.le
    nlinarith
  have h3 : 2 * (50 * c ^ 2) * 0.34 ≤ 2 * u * c * (3 * (rr + 1) - 4 * rr ^ 2) := by
    have h4 : 2 * (50 * c ^ 2) ≤ 2 * u * c := by nlinarith
    exact mul_le_mul h4 hcoef (by norm_num) (by nlinarith)
  linarith

/-- **The staggered pigeonhole.** -/
lemma exists_stagger (w : ℕ → ℝ) (hw : ∀ i j, i ≤ j → w i ≤ w j) (sp sq : ℝ) (Mp Mq : Finset ℕ)
    (B : ℕ) (hsum : Mp.card + Mq.card ≤ B) :
    ∃ k ≤ B, ∃ i j : ℕ, (i = k ∧ j = k + 1 ∨ i = k + 1 ∧ j = k) ∧
      (∀ n ∈ Mp, ¬ (w i < (n : ℝ) * sp ∧ (n : ℝ) * sp ≤ w (k + 2))) ∧
      (∀ n ∈ Mq, ¬ (w j < (n : ℝ) * sq ∧ (n : ℝ) * sq ≤ w (k + 2))) := by
  classical
  set F : Finset ℕ → ℝ → ℝ → ℝ → Finset ℕ := fun M s a b =>
    M.filter (fun n => a < (n : ℝ) * s ∧ (n : ℝ) * s ≤ b) with hF
  set N : ℕ → ℕ := fun k => (F Mp sp (w 0) (w (k + 2))).card + (F Mq sq (w 0) (w (k + 2))).card
    with hN
  have hex : ∃ k, N k ≤ k := by
    refine ⟨B, le_trans (add_le_add ?_ ?_) hsum⟩
    · exact card_le_card (filter_subset _ _)
    · exact card_le_card (filter_subset _ _)
  set k := Nat.find hex with hk
  have hkN : N k ≤ k := Nat.find_spec hex
  have hmin : ∀ j < k, j + 1 ≤ N j := by
    intro j hj
    have := Nat.find_min hex hj
    omega
  have hkB : k ≤ B := Nat.find_min' hex (le_trans (add_le_add
    (card_le_card (filter_subset _ _)) (card_le_card (filter_subset _ _))) hsum)
  -- splitting a count at an intermediate point
  have split : ∀ (M : Finset ℕ) (s a b c : ℝ), a ≤ b → b ≤ c →
      (F M s a c).card = (F M s a b).card + (F M s b c).card := by
    intro M s a b c hab hbc
    have e : F M s a c = F M s a b ∪ F M s b c := by
      ext n
      simp only [hF, mem_union, mem_filter]
      constructor
      · rintro ⟨hn, h1, h2⟩
        rcases le_or_gt ((n : ℝ) * s) b with h | h
        · exact Or.inl ⟨hn, h1, h⟩
        · exact Or.inr ⟨hn, h, h2⟩
      · rintro (⟨hn, h1, h2⟩ | ⟨hn, h1, h2⟩)
        · exact ⟨hn, h1, le_trans h2 hbc⟩
        · exact ⟨hn, lt_of_le_of_lt hab h1, h2⟩
    have d : Disjoint (F M s a b) (F M s b c) := by
      rw [Finset.disjoint_left]
      intro n h1 h2
      simp only [hF, mem_filter] at h1 h2
      exact absurd h2.2.1 (not_lt.mpr h1.2.2)
    rw [e, card_union_of_disjoint d]
  have h0 : ∀ i, w 0 ≤ w i := fun i => hw 0 i (Nat.zero_le i)
  -- nothing in the last stretch
  have hlast : (F Mp sp (w (k + 1)) (w (k + 2))).card = 0 ∧
      (F Mq sq (w (k + 1)) (w (k + 2))).card = 0 := by
    have s1 := split Mp sp (w 0) (w (k + 1)) (w (k + 2)) (h0 _) (hw _ _ (by omega))
    have s2 := split Mq sq (w 0) (w (k + 1)) (w (k + 2)) (h0 _) (hw _ _ (by omega))
    have hNk : N k = (F Mp sp (w 0) (w (k + 2))).card + (F Mq sq (w 0) (w (k + 2))).card := rfl
    rcases Nat.eq_zero_or_pos k with hz | hz
    · have : N k = 0 := by omega
      omega
    · have hprev := hmin (k - 1) (by omega)
      have hNp : N (k - 1)
          = (F Mp sp (w 0) (w (k + 1))).card + (F Mq sq (w 0) (w (k + 1))).card := by
        have e : k - 1 + 2 = k + 1 := by omega
        simp only [hN, e]
      omega
  -- at most one in the last two stretches
  have htwo : (F Mp sp (w k) (w (k + 2))).card + (F Mq sq (w k) (w (k + 2))).card ≤ 1 := by
    have s1 := split Mp sp (w 0) (w k) (w (k + 2)) (h0 _) (hw _ _ (by omega))
    have s2 := split Mq sq (w 0) (w k) (w (k + 2)) (h0 _) (hw _ _ (by omega))
    have hNk : N k = (F Mp sp (w 0) (w (k + 2))).card + (F Mq sq (w 0) (w (k + 2))).card := rfl
    rcases Nat.lt_or_ge k 2 with h | h
    · omega
    · have hprev := hmin (k - 2) (by omega)
      have hNp : N (k - 2) = (F Mp sp (w 0) (w k)).card + (F Mq sq (w 0) (w k)).card := by
        have e : k - 2 + 2 = k := by omega
        simp only [hN, e]
      omega
  have none : ∀ (M : Finset ℕ) (s a : ℝ), (F M s a (w (k + 2))).card = 0 →
      ∀ n ∈ M, ¬ (a < (n : ℝ) * s ∧ (n : ℝ) * s ≤ w (k + 2)) := by
    intro M s a h n hn hc
    have : n ∈ F M s a (w (k + 2)) := by
      simp only [hF, mem_filter]; exact ⟨hn, hc⟩
    rw [card_eq_zero] at h
    rw [h] at this
    exact absurd this (notMem_empty n)
  refine ⟨k, hkB, ?_⟩
  by_cases hp : (F Mp sp (w k) (w (k + 2))).card = 0
  · exact ⟨k, k + 1, Or.inl ⟨rfl, rfl⟩, none Mp sp (w k) hp,
      none Mq sq (w (k + 1)) hlast.2⟩
  · have hq : (F Mq sq (w k) (w (k + 2))).card = 0 := by omega
    exact ⟨k + 1, k, Or.inr ⟨rfl, rfl⟩, none Mp sp (w (k + 1)) hlast.1,
      none Mq sq (w k) hq⟩

/-- **Rigidity with staggered windows.** -/
theorem rigidity_golden {p q D B Np Nq : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 12 ≤ D) {η c x0 θ : ℝ} (hη : 0 < η) (hB : (D : ℝ) ^ 2 / 4 * (-log η) < B + 1)
    (hcp : sqrt (log p) ≤ c) (hcq : sqrt (log q) ≤ c) (hx : 50 * c ≤ x0)
    (hDp : log (50 * D) ^ 2 ≤ 4 * log p * x0 ^ 2) (hDq : log (50 * D) ^ 2 ≤ 4 * log q * x0 ^ 2)
    (hNp : ⌊w c x0 (B + 2) / sqrt (log p)⌋₊ + 1 ≤ Np)
    (hNq : ⌊w c x0 (B + 2) / sqrt (log q)⌋₊ + 1 ≤ Nq)
    (h12 : η ≤ |prodPhi p D Np θ| * |prodPhi q D Nq θ|) :
    ∃ z : ℤ, |θ - z| ≤ exp (-(2 * x0 ^ 2)) / 2 := by
  classical
  have hc0 : 0 < c := lt_of_lt_of_le (sqrt_log_pos hp) hcp
  have hx0 : 0 ≤ x0 := by linarith
  have hlog2 : (0.69 : ℝ) < log 2 := lt_trans (by norm_num) log_two_gt_d9
  have hc2 : 0.69 ≤ c ^ 2 := by
    have h1 : log 2 ≤ log (p : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hp)
    have h2 := pow_le_pow_left₀ (sqrt_nonneg _) hcp 2
    rw [sq_sqrt (TwoPrimesEffective.log_pos' hp).le] at h2
    linarith
  set Mp := marked'' p D Np θ with hMp
  set Mq := marked'' q D Nq θ with hMq
  have hsum : Mp.card + Mq.card ≤ B := by
    have h := lt_of_le_of_lt (card_marked_joint'' hD hη h12) hB
    have : Mp.card + Mq.card < B + 1 := by exact_mod_cast h
    omega
  obtain ⟨k, hkB, i, j, hij, hfp, hfq⟩ := exists_stagger (w c x0)
    (fun _ _ h => w_mono hc0 hx h) (sqrt (log p)) (sqrt (log q)) Mp Mq B hsum
  set b : ℝ := w c x0 (k + 2) with hb
  have hbB : b ≤ w c x0 (B + 2) := w_mono hc0 hx (by omega)
  have hxw : ∀ m, x0 ≤ w c x0 m := fun m => (w_step hc0 hx m).1
  have hstart : ∀ m, m = k ∨ m = k + 1 → x0 ≤ w c x0 m ∧ w c x0 m + c ≤ b := by
    intro m hm
    refine ⟨hxw m, ?_⟩
    rcases hm with h | h
    · rw [h]
      exact le_trans (w_step hc0 hx k).2 (w_mono hc0 hx (by omega))
    · rw [h]
      exact (w_step hc0 hx (k + 1)).2
  have hi : i = k ∨ i = k + 1 := by omega
  have hj : j = k ∨ j = k + 1 := by omega
  -- the quiet stretch of one base
  have chain : ∀ (r N : ℕ) (a : ℝ), 2 ≤ r → sqrt (log r) ≤ c →
      log (50 * D) ^ 2 ≤ 4 * log r * x0 ^ 2 → ⌊w c x0 (B + 2) / sqrt (log r)⌋₊ + 1 ≤ N →
      x0 ≤ a → a + c ≤ b →
      (∀ n ∈ marked'' r D N θ, ¬ (a < (n : ℝ) * sqrt (log r) ∧ (n : ℝ) * sqrt (log r) ≤ b)) →
      ∃ (n1 : ℕ) (z : ℤ), (r : ℝ) ^ (n1 ^ 2) ≤ exp ((a + c) ^ 2) ∧
        |θ - z / (r : ℝ) ^ (n1 ^ 2)| ≤ exp (-(b ^ 2)) := by
    intro r N a hr hcr hDr hN hxa hac hfr
    set s : ℝ := sqrt (log r) with hs
    have hs0 : 0 < s := sqrt_log_pos hr
    have hs2 : s ^ 2 = log r := sq_sqrt (TwoPrimesEffective.log_pos' hr).le
    have ha0 : 0 ≤ a := le_trans hx0 hxa
    have hb0 : 0 ≤ b := by linarith
    set n1 : ℕ := ⌊a / s⌋₊ + 1 with hn1
    set n2 : ℕ := ⌊b / s⌋₊ + 1 with hn2
    have h1a : a < (n1 : ℝ) * s := by
      have := Nat.lt_floor_add_one (a / s)
      rw [div_lt_iff₀ hs0] at this
      rw [hn1]; push_cast; exact this
    have h1b : (n1 : ℝ) * s ≤ a + c := by
      have h := Nat.floor_le (div_nonneg ha0 hs0.le)
      rw [le_div_iff₀ hs0] at h
      rw [hn1]; push_cast; linarith
    have h2a : b < (n2 : ℝ) * s := by
      have := Nat.lt_floor_add_one (b / s)
      rw [div_lt_iff₀ hs0] at this
      rw [hn2]; push_cast; exact this
    have h12' : n1 < n2 := by
      have h : (a / s) + 1 ≤ b / s := by
        rw [le_div_iff₀ hs0, add_mul, div_mul_cancel₀ _ hs0.ne', one_mul]; linarith
      have := Nat.floor_le_floor h
      rw [Nat.floor_add_one (div_nonneg ha0 hs0.le)] at this
      omega
    have hn2N : n2 ≤ N := by
      refine le_trans ?_ hN
      exact Nat.add_le_add_right (Nat.floor_le_floor (div_le_div_of_nonneg_right hbB hs0.le)) 1
    have hin : ∀ n, n1 ≤ n → n < n2 → a < (n : ℝ) * s ∧ (n : ℝ) * s ≤ b := by
      intro n hn hlt
      constructor
      · exact lt_of_lt_of_le h1a (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hs0.le)
      · have h3 : n ≤ ⌊b / s⌋₊ := by omega
        have h4 := le_trans (Nat.cast_le.mpr h3 : (n : ℝ) ≤ _)
          (Nat.floor_le (div_nonneg hb0 hs0.le))
        rwa [le_div_iff₀ hs0] at h4
    have hJ : ∀ n, n1 ≤ n → n < n2 → 50 ≤ range' r D n := by
      intro n hn hlt
      refine range_fifty hr (le_trans (by norm_num) hD) hcr hx hDr (k := 0) ?_
      have h5 : x0 / s ≤ (n : ℝ) := by
        rw [div_le_iff₀ hs0]
        have := (hin n hn hlt).1
        linarith
      unfold loA
      exact Nat.ceil_le.mpr h5
    obtain ⟨z, hz⟩ := run_smooth (p := r) (θ := θ) hD h12' hJ (fun n hn hlt => by
      by_contra hcon
      refine hfr n ?_ (hin n hn hlt)
      rw [marked'', mem_filter, Finset.mem_range]
      exact ⟨lt_of_lt_of_le hlt hn2N, le_trans (by norm_num) (hJ n hn hlt), not_lt.mp hcon⟩)
      (by omega)
    refine ⟨n1, z, ?_, le_trans hz ?_⟩
    · rw [pow_eq_exp hr, ← hs2]
      apply exp_le_exp.mpr
      push_cast
      have := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg n1) hs0.le) h1b 2
      rwa [mul_pow] at this
    · have h6 : exp (b ^ 2) ≤ (r : ℝ) ^ (n2 ^ 2) := by
        rw [pow_eq_exp hr, ← hs2]
        apply exp_le_exp.mpr
        push_cast
        have := pow_le_pow_left₀ hb0 h2a.le 2
        rwa [mul_pow] at this
      rw [exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (exp_pos _) h6
  obtain ⟨n1, z1, hP, hε1⟩ := chain p Np (w c x0 i) hp hcp hDp hNp (hstart i hi).1
    (hstart i hi).2 hfp
  obtain ⟨m1, z2, hQ, hε2⟩ := chain q Nq (w c x0 j) hq hcq hDq hNq (hstart j hj).1
    (hstart j hj).2 hfq
  set P : ℕ := p ^ (n1 ^ 2) with hPd
  set Q : ℕ := q ^ (m1 ^ 2) with hQd
  have hPr : (p : ℝ) ^ (n1 ^ 2) = (P : ℝ) := by rw [hPd]; push_cast; rfl
  have hQr : (q : ℝ) ^ (m1 ^ 2) = (Q : ℝ) := by rw [hQd]; push_cast; rfl
  have hPpos : (0 : ℝ) < P := by
    rw [← hPr]; exact pow_pos (by exact_mod_cast (show 0 < p by omega)) _
  have hQpos : (0 : ℝ) < Q := by
    rw [← hQr]; exact pow_pos (by exact_mod_cast (show 0 < q by omega)) _
  rw [hPr] at hP hε1
  rw [hQr] at hQ hε2
  have hrec := w_rec hc0 hc2 hx k
  have hgap : (w c x0 i + c) ^ 2 + (w c x0 j + c) ^ 2 + 1 < b ^ 2 := by
    rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hb]; linarith
    · rw [h1, h2, hb]; linarith
  have htwo : (2 : ℝ) < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  have hzero : z1 * (Q : ℤ) - z2 * (P : ℤ) = 0 := by
    have hdiff : |(z1 : ℝ) / P - z2 / Q| ≤ 2 * exp (-(b ^ 2)) := by
      have t := abs_sub_le ((z1 : ℝ) / P) θ (z2 / Q)
      rw [abs_sub_comm ((z1 : ℝ) / P) θ] at t
      linarith
    have e : (z1 : ℝ) / P - z2 / Q = ((z1 * (Q : ℤ) - z2 * (P : ℤ) : ℤ) : ℝ) / (P * Q) := by
      push_cast; field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hPpos hQpos), div_le_iff₀ (mul_pos hPpos hQpos)] at hdiff
    have h3 : 2 * exp (-(b ^ 2)) * (P * Q) < 1 := by
      have h4 : (P : ℝ) * Q ≤ exp ((w c x0 i + c) ^ 2) * exp ((w c x0 j + c) ^ 2) :=
        mul_le_mul hP hQ hQpos.le (exp_pos _).le
      have h5 := mul_le_mul_of_nonneg_left h4
        (show (0 : ℝ) ≤ 2 * exp (-(b ^ 2)) by have := exp_pos (-(b ^ 2)); linarith)
      refine lt_of_le_of_lt h5 ?_
      have h7 : 2 * exp (-(b ^ 2)) * (exp ((w c x0 i + c) ^ 2) * exp ((w c x0 j + c) ^ 2))
          ≤ exp 1 * (exp (-(b ^ 2))
            * (exp ((w c x0 i + c) ^ 2) * exp ((w c x0 j + c) ^ 2))) := by
        have h8 : 0 ≤ exp (-(b ^ 2))
            * (exp ((w c x0 i + c) ^ 2) * exp ((w c x0 j + c) ^ 2)) := by positivity
        have := mul_le_mul_of_nonneg_right htwo.le h8
        linarith
      refine lt_of_le_of_lt h7 ?_
      rw [← exp_add, ← exp_add, ← exp_add, exp_lt_one_iff]
      linarith
    have h9 : |((z1 * (Q : ℤ) - z2 * (P : ℤ) : ℤ) : ℝ)| < 1 := lt_of_le_of_lt hdiff h3
    have h10 : |z1 * (Q : ℤ) - z2 * (P : ℤ)| < 1 := by exact_mod_cast h9
    exact Int.abs_lt_one_iff.mp h10
  have hdvd : (P : ℤ) ∣ z1 := by
    have hcop : IsCoprime (P : ℤ) (Q : ℤ) := by
      apply Nat.Coprime.isCoprime
      exact Nat.Coprime.pow _ _ hpq
    have : (P : ℤ) ∣ z1 * (Q : ℤ) := ⟨z2, by linear_combination hzero⟩
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨z, hz⟩ := hdvd
  refine ⟨z, ?_⟩
  have e : (z1 : ℝ) / P = z := by
    rw [hz]; push_cast; field_simp
  rw [e] at hε1
  refine le_trans hε1 ?_
  have hbig : 2 * x0 ^ 2 + 1 ≤ b ^ 2 := by
    have h1 : rr ^ 2 * x0 ≤ w c x0 2 := by
      have h2 : (1 : ℝ) ≤ rr ^ 2 := one_le_pow₀ (by linarith [rr_bounds.1])
      have e2 : w c x0 2 = rr ^ 2 * x0 + (rr ^ 2 - 1) * (4 * c) := by unfold w; ring
      have h3 : 0 ≤ (rr ^ 2 - 1) * (4 * c) := mul_nonneg (by linarith) (by linarith)
      rw [e2]; linarith
    have h4 : w c x0 2 ≤ b := w_mono hc0 hx (by omega)
    have h5 : 1.618 * x0 ≤ b := by
      have h6 : 1.618 * x0 ≤ rr ^ 2 * x0 := by
        refine mul_le_mul_of_nonneg_right ?_ hx0
        rw [rr_sq]; linarith [sqrt5_bounds.1]
      linarith
    have h7 := pow_le_pow_left₀ (by positivity) h5 2
    have h8 : 1000 ≤ x0 ^ 2 := by
      have h9 : (50 * c) ^ 2 ≤ x0 ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
      rw [mul_pow] at h9
      linarith
    rw [mul_pow] at h7
    have : (2.6 : ℝ) ≤ 1.618 ^ 2 := by norm_num
    nlinarith
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have h1 : exp (-(b ^ 2)) * exp 1 ≤ exp (-(2 * x0 ^ 2)) := by
    rw [← exp_add]; apply exp_le_exp.mpr; linarith
  have h2 := mul_le_mul_of_nonneg_left htwo.le (exp_pos (-(b ^ 2))).le
  linarith

/-- The height of the theorem. -/
noncomputable def Lam (c x0 : ℝ) (B : ℕ) : ℝ := ((1 + sqrt 5) / 2) ^ (B + 2) * (x0 + 4 * c) ^ 2

lemma Lam_eq (c x0 : ℝ) (B : ℕ) : Lam c x0 B = (rr ^ (B + 2) * (x0 + 4 * c)) ^ 2 := by
  unfold Lam
  rw [← rr_sq, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (B + 2)]

/-- All the levels used fit below `exp (Lam)`. -/
lemma top_le {r : ℕ} (hr : 2 ≤ r) {c x0 : ℝ} (hcr : sqrt (log r) ≤ c) (hx : 50 * c ≤ x0)
    (B : ℕ) : (r : ℝ) ^ ((⌊w c x0 (B + 2) / sqrt (log r)⌋₊ + 1) ^ 2) ≤ exp (Lam c x0 B) := by
  set s : ℝ := sqrt (log r) with hs
  have hs0 : 0 < s := sqrt_log_pos hr
  have hs2 : s ^ 2 = log r := sq_sqrt (TwoPrimesEffective.log_pos' hr).le
  have hc0 : 0 < c := lt_of_lt_of_le hs0 hcr
  have hw0 : 0 ≤ w c x0 (B + 2) := by
    have := (w_step hc0 hx (B + 2)).1
    linarith
  set N : ℕ := ⌊w c x0 (B + 2) / s⌋₊ + 1 with hN
  have h1 : (N : ℝ) * s ≤ w c x0 (B + 2) + c := by
    have h := Nat.floor_le (div_nonneg hw0 hs0.le)
    rw [le_div_iff₀ hs0] at h
    rw [hN]; push_cast; linarith
  have h2 : (N : ℝ) * s ≤ rr ^ (B + 2) * (x0 + 4 * c) := by
    refine le_trans h1 ?_
    unfold w; linarith
  rw [pow_eq_exp hr, ← hs2, Lam_eq]
  apply exp_le_exp.mpr
  push_cast
  have := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg N) hs0.le) h2 2
  rwa [mul_pow] at this

/-- **Density to witnesses** at the height `64 exp (φ^(B+2) (x0+4c)^2)`. -/
theorem witness_of_density_golden {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD12 : 12 ≤ D) {K c x0 s : ℝ} (hK : 1 ≤ K)
    (hcp : sqrt (log p) ≤ c) (hcq : sqrt (log q) ≤ c) (hx : 50 * c ≤ x0)
    (hDp : log (50 * D) ^ 2 ≤ 4 * log p * x0 ^ 2) (hDq : log (50 * D) ^ 2 ≤ 4 * log q * x0 ^ 2)
    {B : ℕ} (hB : B = ⌊(D : ℝ) ^ 2 * log (17 * K) / 8⌋₊)
    {X : ℕ} (hX : 64 * exp (Lam c x0 B) ≤ X) (hX100 : 100 ≤ X)
    (V : Finset ℤ) (hV : (X : ℝ) ≤ K * V.card) (a b : ℤ → ℤ)
    (hdiff : ∀ v ∈ V, v = a v - b v)
    (haX : ∀ v ∈ V, |a v| ≤ (X : ℤ)) (hbX : ∀ v ∈ V, |b v| ≤ (X : ℤ))
    (ha : ∀ v ∈ V, Small p s (a v)) (hb : ∀ v ∈ V, Small q s (b v))
    (t : ℤ) (ht : |(t : ℝ)| ≤ exp (2 * x0 ^ 2) / 32) :
    ∃ k : ℤ, |k| ≤ 8 * (X : ℤ) ∧ Small p (4 * (s + 1 / D)) k
      ∧ Small q (4 * (s + 1 / D)) (k - t) := by
  classical
  have hD : 1 ≤ D := le_trans (by norm_num) hD12
  have hc0 : 0 < c := lt_of_lt_of_le (sqrt_log_pos hp) hcp
  have hx00 : 0 ≤ x0 := by linarith
  have hKpos : (0 : ℝ) < K := by linarith
  have hX100r : (100 : ℝ) ≤ X := by exact_mod_cast hX100
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hVpos : (0 : ℝ) < V.card := by
    by_contra h
    have h0 : (V.card : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [h0, mul_zero] at hV
    linarith
  set Np := ⌊w c x0 (B + 2) / sqrt (log p)⌋₊ + 1 with hNp
  set Nq := ⌊w c x0 (B + 2) / sqrt (log q)⌋₊ + 1 with hNq
  -- the digit sets are short
  have hfit : ∀ r : ℕ, 2 ≤ r → sqrt (log r) ≤ c →
      (r : ℝ) ^ ((⌊w c x0 (B + 2) / sqrt (log r)⌋₊ + 1) ^ 2) ≤ X / 64 := by
    intro r hr hcr
    exact le_trans (top_le hr hcr hx B) (by linarith)
  set I' : Finset (ℤ × Idx p D Np × Idx q D Nq) :=
    V ×ˢ (idx p D Np ×ˢ idx q D Nq) with hI'
  set g : ℤ × Idx p D Np × Idx q D Nq → ℤ :=
    fun i => i.1 + val' p i.2.1 - val' q i.2.2 with hg
  have hVne : V.Nonempty := card_pos.mp (by exact_mod_cast hVpos)
  have hIne : I'.Nonempty :=
    hVne.product ((idx_nonempty p D Np).product (idx_nonempty q D Nq))
  have hcard : (I'.card : ℝ)
      = V.card * ((idx p D Np).card * (idx q D Nq).card) := by
    rw [hI', card_product, card_product]; push_cast; ring
  have hmem : ∀ i ∈ I', i.1 ∈ V ∧ i.2.1 ∈ idx p D Np ∧ i.2.2 ∈ idx q D Nq := by
    intro i hi'
    rw [hI', mem_product, mem_product] at hi'
    exact ⟨hi'.1, hi'.2.1, hi'.2.2⟩
  have svp : ∀ j ∈ idx p D Np, 64 * |val' p j| ≤ (X : ℤ) := by
    intro j hj
    have h1 := le_trans (abs_val'_le hp hD hj) (hfit p hp hcp)
    have h2 : 64 * |(val' p j : ℝ)| ≤ X := by linarith
    exact_mod_cast h2
  have svq : ∀ j ∈ idx q D Nq, 64 * |val' q j| ≤ (X : ℤ) := by
    intro j hj
    have h1 := le_trans (abs_val'_le hq hD hj) (hfit q hq hcq)
    have h2 : 64 * |(val' q j : ℝ)| ≤ X := by linarith
    exact_mod_cast h2
  have hvp : ∀ j ∈ idx p D Np, |val' p j| ≤ (X : ℤ) := by
    intro j hj
    have := svp j hj
    have := abs_nonneg (val' p j)
    omega
  have hvq : ∀ j ∈ idx q D Nq, |val' q j| ≤ (X : ℤ) := by
    intro j hj
    have := svq j hj
    have := abs_nonneg (val' q j)
    omega
  set M : ℕ := 2 * X + X / 32 with hM
  have hR : ∀ i ∈ I', |g i| ≤ ((M : ℕ) : ℤ) := by
    intro i hi'
    obtain ⟨h1, h2, h3⟩ := hmem i hi'
    have e1 := hdiff _ h1
    have a1 := haX _ h1
    have a2 := hbX _ h1
    have a3 := svp _ h2
    have a4 := svq _ h3
    have a5 : |val' p i.2.1| + |val' q i.2.2| ≤ ((X / 32 : ℕ) : ℤ) := by
      have := abs_nonneg (val' p i.2.1)
      have := abs_nonneg (val' q i.2.2)
      omega
    have a6 := le_abs_self (val' p i.2.1)
    have a7 := neg_le_abs (val' p i.2.1)
    have a8 := le_abs_self (val' q i.2.2)
    have a9 := neg_le_abs (val' q i.2.2)
    rw [abs_le] at a1 a2
    rw [abs_le]; simp only [hg, hM]; push_cast at a5 ⊢; omega
  -- collisions
  have hcoll : (((I' ×ˢ I').filter (fun x => g x.1 - g x.2 = 0)).card : ℝ)
      ≤ (1 / V.card) * (I'.card : ℝ) ^ 2 := by
    set W := idx p D Np ×ˢ idx q D Nq with hW
    have h1 : ((I' ×ˢ I').filter (fun x => g x.1 - g x.2 = 0)).card ≤ (I' ×ˢ W).card := by
      refine card_le_card_of_injOn (fun x => (x.1, x.2.2)) ?_ ?_
      · intro x hx
        rw [mem_coe, mem_filter, mem_product] at hx
        rw [mem_coe, mem_product]
        refine ⟨hx.1.1, ?_⟩
        have := hx.1.2
        rw [hI', mem_product] at this
        exact this.2
      · intro x hx y hy hxy
        rw [mem_coe, mem_filter] at hx hy
        simp only [Prod.mk.injEq] at hxy
        obtain ⟨e1, e2⟩ := hxy
        have e3 : x.2.1 = y.2.1 := by
          have gx := hx.2
          have gy := hy.2
          have e4 : g x.2 = g y.2 := by rw [e1] at gx; omega
          simp only [hg, e2] at e4
          omega
        exact Prod.ext e1 (Prod.ext e3 e2)
    have h2 : (((I' ×ˢ I').filter (fun x => g x.1 - g x.2 = 0)).card : ℝ)
        ≤ (I'.card : ℝ) * ((idx p D Np).card * (idx q D Nq).card) := by
      have h3 : (I' ×ˢ W).card = I'.card * ((idx p D Np).card * (idx q D Nq).card) := by
        rw [card_product I' W, hW, card_product (idx p D Np)]
      exact_mod_cast le_trans h1 (le_of_eq h3)
    refine le_trans h2 (le_of_eq ?_)
    rw [hcard]; field_simp
  have hsupp : ((I' ×ˢ I').image (fun x => g x.1 - g x.2)).card ≤ 4 * M + 1 := by
    have hsub : (I' ×ˢ I').image (fun x => g x.1 - g x.2)
        ⊆ Icc (-(2 * (M : ℤ))) (2 * (M : ℤ)) := by
      intro y hy
      rw [mem_image] at hy
      obtain ⟨x, hx', rfl⟩ := hy
      rw [mem_product] at hx'
      have a1 := hR _ hx'.1
      have a2 := hR _ hx'.2
      rw [abs_le] at a1 a2
      rw [mem_Icc]; omega
    refine le_trans (card_le_card hsub) ?_
    rw [Int.card_Icc]; omega
  -- the large values of the exponential sum
  set η : ℝ := sqrt (1 / (17 * K)) with hη
  have hηpos : 0 < η := sqrt_pos.mpr (by positivity)
  have hη2 : η ^ 2 = 1 / (17 * K) := sq_sqrt (by positivity)
  have hlogη : -log η = log (17 * K) / 2 := by
    rw [hη, log_sqrt (by positivity), one_div, log_inv]; ring
  have hBlt : (D : ℝ) ^ 2 / 4 * (-log η) < B + 1 := by
    have h := Nat.lt_floor_add_one ((D : ℝ) ^ 2 * log (17 * K) / 8)
    rw [← hB] at h
    rw [hlogη]
    linarith
  have hfactor : ∀ θ : ℝ, S I' g θ = (∑ v ∈ V, e ((v : ℝ) * θ))
      * ((∑ j ∈ idx p D Np, e ((val' p j : ℝ) * θ))
        * (∑ j ∈ idx q D Nq, e ((val' q j : ℝ) * (-θ)))) := by
    intro θ
    rw [S, hI', sum_product, sum_mul]
    refine sum_congr rfl (fun v _ => ?_)
    rw [sum_product, sum_mul_sum, mul_sum]
    refine sum_congr rfl (fun j _ => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun l _ => ?_)
    rw [← e_add, ← e_add]
    congr 1; simp only [hg]; push_cast; ring
  have heven : ∀ θ : ℝ, prodPhi q D Nq (-θ) = prodPhi q D Nq θ := by
    intro θ
    unfold prodPhi
    refine prod_congr rfl (fun n _ => ?_)
    rw [mul_neg, phi_neg]
  have hle1 : ∀ (r N : ℕ) (θ : ℝ), |prodPhi r D N θ| ≤ 1 := by
    intro r N θ
    unfold prodPhi
    rw [abs_prod]
    exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_phi_le_one _ _)
  have hspec : ∀ θ : ℝ, η * I'.card ≤ ‖S I' g θ‖ → 99 / 100 ≤ Real.cos (2 * π * (t * θ)) := by
    intro θ hθ
    have hnorm : ‖S I' g θ‖ ≤ (I'.card : ℝ)
        * (|prodPhi p D Np θ| * |prodPhi q D Nq θ|) := by
      rw [hfactor, norm_mul, norm_mul, sum_idx, sum_idx, heven,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
      have hVs : ‖∑ v ∈ V, e ((v : ℝ) * θ)‖ ≤ (V.card : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have : ∀ v ∈ V, ‖e ((v : ℝ) * θ)‖ = 1 := by
          intro v _
          unfold e
          exact Complex.norm_exp_ofReal_mul_I _
        rw [sum_congr rfl this]; simp
      refine le_trans (mul_le_mul_of_nonneg_right hVs (by positivity)) (le_of_eq ?_)
      rw [hcard]; ring
    have hIpos : (0 : ℝ) < I'.card := by exact_mod_cast card_pos.mpr hIne
    have hboth : η ≤ |prodPhi p D Np θ| * |prodPhi q D Nq θ| := by
      have := le_trans hθ hnorm
      rw [mul_comm η] at this
      exact le_of_mul_le_mul_left this hIpos
    obtain ⟨z, hz⟩ := rigidity_golden hp hq hpq hD12 hηpos hBlt hcp hcq hx hDp hDq (le_of_eq hNp.symm)
      (le_of_eq hNq.symm) hboth
    set y : ℝ := t * (θ - z) with hy
    have hyabs : |y| ≤ 1 / 64 := by
      rw [hy, abs_mul]
      have h3 := mul_le_mul ht hz (abs_nonneg _) (by positivity)
      refine le_trans h3 (le_of_eq ?_)
      have e1 : exp (2 * x0 ^ 2) * exp (-(2 * x0 ^ 2)) = 1 := by
        rw [← exp_add, add_neg_cancel, exp_zero]
      rw [div_mul_div_comm, e1]; norm_num
    have hcos : Real.cos (2 * π * (t * θ)) = Real.cos (2 * π * y) := by
      have : 2 * π * ((t : ℝ) * θ) = 2 * π * y + ((t * z : ℤ) : ℝ) * (2 * π) := by
        rw [hy]; push_cast; ring
      rw [this, Real.cos_add_int_mul_two_pi]
    rw [hcos]
    refine le_trans ?_ (Real.one_sub_sq_div_two_le_cos)
    have h6 : |2 * π * y| ≤ 1 / 8 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have := mul_le_mul_of_nonneg_left hyabs (show (0 : ℝ) ≤ 2 * π by positivity)
      have hpi : π < 4 := pi_lt_four
      linarith
    have h7 : (2 * π * y) ^ 2 ≤ (1 / 8) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h6 2
    linarith [show ((1 : ℝ) / 8) ^ 2 = 1 / 64 by norm_num]
  have hnum : (1 + 99 / 100) * η ^ 2 * (1 / (V.card : ℝ))
      < (99 / 100) / ((4 * M + 1 : ℕ) : ℝ) := by
    rw [hη2]
    have h1 : 1 / (V.card : ℝ) ≤ K / X := by
      rw [div_le_div_iff₀ hVpos hXpos]; linarith
    have h2 : (1 + 99 / 100) * (1 / (17 * K)) * (1 / (V.card : ℝ))
        ≤ (1 + 99 / 100) * (1 / (17 * K)) * (K / X) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (1 + 99 / 100) * (1 / (17 * K)) * (K / X) = (199 / 1700) / X := by
      field_simp; ring
    have h4 : ((4 * M + 1 : ℕ) : ℝ) ≤ 1627 / 200 * X := by
      have h5 : ((X / 32 : ℕ) : ℝ) ≤ (X : ℝ) / 32 := Nat.cast_div_le
      have h6 : ((4 * M + 1 : ℕ) : ℝ) = 8 * X + 4 * ((X / 32 : ℕ) : ℝ) + 1 := by
        rw [hM]; push_cast; ring
      rw [h6]; linarith
    refine lt_of_le_of_lt (le_trans h2 (le_of_eq h3)) ?_
    have h7 : (0 : ℝ) < ((4 * M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (4 * M)
    rw [div_lt_div_iff₀ hXpos h7]
    linarith
  obtain ⟨i1, m1, i2, m2, i3, m3, i4, m4, hsum⟩ :=
    exists_four' I' g t M (4 * M + 1) η (1 / V.card) (99 / 100) (by norm_num) hIne hR hcoll
      hsupp hspec hnum
  obtain ⟨v1, x1, y1⟩ := hmem i1 m1
  obtain ⟨v2, x2, y2⟩ := hmem i2 m2
  obtain ⟨v3, x3, y3⟩ := hmem i3 m3
  obtain ⟨v4, x4, y4⟩ := hmem i4 m4
  set P : ℤ × Idx p D Np × Idx q D Nq → ℤ := fun i => a i.1 + val' p i.2.1 with hP
  set Q : ℤ × Idx p D Np × Idx q D Nq → ℤ := fun i => b i.1 + val' q i.2.2 with hQ
  have hPQ : ∀ i ∈ I', g i = P i - Q i := by
    intro i hi'
    have := hdiff _ (hmem i hi').1
    simp only [hg, hP, hQ]; omega
  set k := (P i1 - P i2) + (P i3 - P i4) with hk
  have hkt : k - t = (Q i1 - Q i2) + (Q i3 - Q i4) := by
    rw [hPQ _ m1, hPQ _ m2, hPQ _ m3, hPQ _ m4] at hsum
    omega
  have sP : ∀ i ∈ I', Small p (s + 1 / D) (P i) := fun i hi' =>
    (ha _ (hmem i hi').1).add (small_val' hp hD (hmem i hi').2.1)
  have sQ : ∀ i ∈ I', Small q (s + 1 / D) (Q i) := fun i hi' =>
    (hb _ (hmem i hi').1).add (small_val' hq hD (hmem i hi').2.2)
  have e4 : 4 * (s + 1 / (D : ℝ))
      = ((s + 1 / D) + (s + 1 / D)) + ((s + 1 / D) + (s + 1 / D)) := by ring
  refine ⟨k, ?_, ?_, ?_⟩
  · have bound : ∀ i ∈ I', |P i| ≤ 2 * (X : ℤ) := by
      intro i hi'
      have h1 := haX _ (hmem i hi').1
      have h2 := hvp _ (hmem i hi').2.1
      have := abs_add_le (a i.1) (val' p i.2.1)
      simp only [hP]; omega
    have b1 := bound _ m1
    have b2 := bound _ m2
    have b3 := bound _ m3
    have b4 := bound _ m4
    rw [abs_le] at b1 b2 b3 b4
    rw [abs_le, hk]; omega
  · rw [e4, hk]
    exact ((sP _ m1).sub (sP _ m2)).add ((sP _ m3).sub (sP _ m4))
  · rw [e4, hkt]
    exact ((sQ _ m1).sub (sQ _ m2)).add ((sQ _ m3).sub (sQ _ m4))

/-- **The critical density** with `a = D² log φ / 8`. -/
theorem witness_of_critical_density_golden {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD12 : 12 ≤ D) {s : ℝ} (t : ℤ)
    (dens : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧ ∃ K : ℝ, 1 ≤ K ∧
      K ≤ ε * (log X) ^ (1 / ((D : ℝ) ^ 2 * log ((1 + sqrt 5) / 2) / 8)) ∧
      ∃ V : Finset ℤ, ∃ a b : ℤ → ℤ, (X : ℝ) ≤ K * V.card ∧ (∀ v ∈ V, v = a v - b v) ∧
        (∀ v ∈ V, |a v| ≤ (X : ℤ)) ∧ (∀ v ∈ V, |b v| ≤ (X : ℤ)) ∧
        (∀ v ∈ V, Small p s (a v)) ∧ (∀ v ∈ V, Small q s (b v))) :
    ∃ k : ℤ, Small p (4 * (s + 1 / D)) k ∧ Small q (4 * (s + 1 / D)) (k - t) := by
  classical
  have hD : 1 ≤ D := le_trans (by norm_num) hD12
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set e : ℝ := (D : ℝ) ^ 2 * log ((1 + sqrt 5) / 2) / 8 with he
  set g : ℝ := (1 + sqrt 5) / 2 with hg
  have hg1 : 1 < g := by
    have := sqrt5_bounds.1
    rw [hg]; linarith
  have hg0 : 0 < g := by linarith
  have he0 : 0 < e := by
    have h2 : 0 < log g := log_pos hg1
    have : (0 : ℝ) < (D : ℝ) ^ 2 := pow_pos (by linarith) 2
    exact div_pos (mul_pos this h2) (by norm_num)
  set c : ℝ := max (sqrt (log p)) (sqrt (log q)) with hc
  have hcp : sqrt (log p) ≤ c := le_max_left _ _
  have hcq : sqrt (log q) ≤ c := le_max_right _ _
  have hc0 : 0 < c := lt_of_lt_of_le (sqrt_log_pos hp) hcp
  set x0 : ℝ := max (50 * c) (max (log (50 * D) / (2 * sqrt (log p)))
    (max (log (50 * D) / (2 * sqrt (log q))) (sqrt (log (32 * (1 + |(t : ℝ)|)) / 2)))) with hx0
  have hx : 50 * c ≤ x0 := le_max_left _ _
  have hx00 : 0 ≤ x0 := le_trans (by positivity) hx
  have hx1 : log (50 * D) / (2 * sqrt (log p)) ≤ x0 :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hx2 : log (50 * D) / (2 * sqrt (log q)) ≤ x0 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hx3 : sqrt (log (32 * (1 + |(t : ℝ)|)) / 2) ≤ x0 :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hrange : ∀ r : ℕ, 2 ≤ r → log (50 * D) / (2 * sqrt (log r)) ≤ x0 →
      log (50 * D) ^ 2 ≤ 4 * log r * x0 ^ 2 := by
    intro r hr h
    have hs : 0 < sqrt (log (r : ℝ)) := sqrt_log_pos hr
    rw [div_le_iff₀ (by positivity)] at h
    have h0 : 0 ≤ log (50 * (D : ℝ)) := log_nonneg (by linarith)
    have h1 := pow_le_pow_left₀ h0 h 2
    have e1 : (x0 * (2 * sqrt (log r))) ^ 2 = 4 * log r * x0 ^ 2 := by
      rw [mul_pow, mul_pow, sq_sqrt (TwoPrimesEffective.log_pos' hr).le]; ring
    rwa [e1] at h1
  set M : ℝ := g ^ 2 * (x0 + 4 * c) ^ 2 with hM
  have hM0 : 0 < M := by
    have : 0 < x0 + 4 * c := by linarith
    exact mul_pos (pow_pos hg0 2) (pow_pos this 2)
  have h17 : (0 : ℝ) < 17 ^ e := rpow_pos_of_pos (by norm_num) _
  have hbase : (0 : ℝ) < 1 / (4 * 17 ^ e * M) :=
    div_pos one_pos (mul_pos (mul_pos (by norm_num) h17) hM0)
  set ε : ℝ := (1 / (4 * 17 ^ e * M)) ^ (1 / e) with hε
  have hε0 : 0 < ε := rpow_pos_of_pos hbase _
  obtain ⟨X, hX, K, hK, hKX, V, a, b, hV, hdiff, haX, hbX, ha, hb⟩ := dens ε hε0 4096
  have hXr : (4096 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hlX : 0 ≤ log (X : ℝ) := log_nonneg (by linarith)
  set B : ℕ := ⌊(D : ℝ) ^ 2 * log (17 * K) / 8⌋₊ with hB
  have hK0 : 0 < K := by linarith
  have h17K : (0 : ℝ) < 17 * K := by linarith
  have h2B : g ^ B ≤ (17 * K) ^ e := by
    have h1 : (B : ℝ) ≤ (D : ℝ) ^ 2 * log (17 * K) / 8 :=
      Nat.floor_le (div_nonneg (mul_nonneg (by positivity) (log_nonneg (by linarith)))
        (by norm_num))
    have e2 : g ^ B = exp (B * log g) := by
      rw [exp_nat_mul, exp_log hg0]
    rw [e2, rpow_def_of_pos h17K]
    apply exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right h1 (log_pos hg1).le
    refine le_trans this (le_of_eq ?_)
    rw [he]; ring
  have hKe : K ^ e ≤ (1 / (4 * 17 ^ e * M)) * log X := by
    have h1 := rpow_le_rpow hK0.le hKX he0.le
    have e1 : (ε * (log X) ^ (1 / e)) ^ e = (1 / (4 * 17 ^ e * M)) * log X := by
      rw [mul_rpow hε0.le (rpow_nonneg hlX _), hε, ← rpow_mul hbase.le, ← rpow_mul hlX,
        one_div_mul_cancel he0.ne', rpow_one, rpow_one]
    rwa [e1] at h1
  have hΛ : Lam c x0 B ≤ log X / 2 := by
    have h1 : Lam c x0 B = g ^ B * M := by
      unfold Lam
      rw [← hg, hM, pow_add]; ring
    have h2 : g ^ B ≤ 17 ^ e * ((1 / (4 * 17 ^ e * M)) * log X) := by
      refine le_trans h2B ?_
      rw [mul_rpow (by norm_num) hK0.le]
      exact mul_le_mul_of_nonneg_left hKe h17.le
    have e3 : 17 ^ e * ((1 / (4 * 17 ^ e * M)) * log X) = log X / (4 * M) := by
      field_simp
    rw [e3] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 hM0.le
    have e4 : log (X : ℝ) / (4 * M) * M = log X / 4 := by
      field_simp
    rw [h1]
    rw [e4] at h3
    linarith
  have hXbig : 64 * exp (Lam c x0 B) ≤ X := by
    set r : ℝ := exp (log X / 2) with hr
    have hr2 : r ^ 2 = X := by
      rw [sq, hr, ← exp_add, add_halves, exp_log hXpos]
    have hr0 : 0 < r := exp_pos _
    have hr64 : 64 ≤ r := by
      have h1 : (64 : ℝ) ^ 2 ≤ r ^ 2 := by rw [hr2]; linarith
      exact (pow_le_pow_iff_left₀ (by norm_num) hr0.le two_ne_zero).mp h1
    have h2 : exp (Lam c x0 B) ≤ r := exp_le_exp.mpr hΛ
    have h3 := mul_le_mul_of_nonneg_right hr64 hr0.le
    nlinarith
  have htx : |(t : ℝ)| ≤ exp (2 * x0 ^ 2) / 32 := by
    have ht1 : (1 : ℝ) ≤ 32 * (1 + |(t : ℝ)|) := by
      have := abs_nonneg (t : ℝ); linarith
    have hl : 0 ≤ log (32 * (1 + |(t : ℝ)|)) := log_nonneg ht1
    have h1 := pow_le_pow_left₀ (sqrt_nonneg _) hx3 2
    rw [sq_sqrt (by linarith)] at h1
    have h2 : 32 * (1 + |(t : ℝ)|) ≤ exp (2 * x0 ^ 2) := by
      have := exp_le_exp.mpr (show log (32 * (1 + |(t : ℝ)|)) ≤ 2 * x0 ^ 2 by linarith)
      rwa [exp_log (by linarith)] at this
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
    linarith
  have hX100 : 100 ≤ X := le_trans (by norm_num) hX
  obtain ⟨k, _, hkp, hkq⟩ := witness_of_density_golden hp hq hpq hD12 (s := s) hK hcp hcq hx
    (hrange p hp hx1) (hrange q hq hx2) hB (X := X) hXbig hX100 V hV a b hdiff haX hbX ha hb
    t htx
  exact ⟨k, hkp, hkq⟩




/-- **Fixed radius** with the exponent `φ^(B+2)/2`. -/
theorem witness_of_free_heights_golden {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : Nat.Coprime p q) (hD12 : 12 ≤ D) {K A0 XD β H c g : ℝ} (hK : 1 ≤ K)
    (hcp : sqrt (log p) ≤ c) (hcq : sqrt (log q) ≤ c)
    (hA0 : (50 * c) ^ 2 ≤ A0)
    (hDp : log (50 * D) ^ 2 ≤ 4 * log p * A0) (hDq : log (50 * D) ^ 2 ≤ 4 * log q * A0)
    (h32 : log 32 ≤ 2 * A0)
    {B : ℕ} (hB : B = ⌊(D : ℝ) ^ 2 * log (17 * K) / 8⌋₊)
    (hH : H = 2 * log (8 * D) + 1) (hg : g = (1 + sqrt 5) / 2)
    (hβ : 0 < β) (hβp : β ≤ log p) (hβq : β ≤ log q)
    (hR0 : 8 * exp ((H + log (8 * D)) ^ 2 / (4 * β)) ≤ exp A0)
    (h100 : 100 ≤ exp A0) (hXD : XD ≤ exp A0)
    (dens : ∀ X : ℕ, Free {p, q} D X → XD ≤ X → ∃ V : Finset ℤ, ∃ a b : ℤ → ℤ,
      (X : ℝ) ≤ K * V.card ∧ (∀ v ∈ V, v = a v - b v) ∧
      (∀ v ∈ V, |a v| ≤ (X : ℤ)) ∧ (∀ v ∈ V, |b v| ≤ (X : ℤ)) ∧
      (∀ v ∈ V, Small p (2 / D) (a v)) ∧ (∀ v ∈ V, Small q (2 / D) (b v)))
    (t : ℤ) :
    ∃ k : ℤ, |(k : ℝ)| ≤ 1024 * exp (H + g ^ (B + 2) * (sqrt A0 + 4 * c) ^ 2)
          * (1 + |(t : ℝ)|) ^ (g ^ (B + 2) / 2)
          * exp (g ^ (B + 2) * (8 * c) / sqrt 2 * sqrt (log (1 + |(t : ℝ)|)))
      ∧ Small p (12 / D) k ∧ Small q (12 / D) (k - t) := by
  classical
  have hD : 1 ≤ D := le_trans (by norm_num) hD12
  have hne : p ≠ q := by
    intro h
    rw [← h, Nat.coprime_self] at hpq
    omega
  have hcard : ({p, q} : Finset ℕ).card = 2 := card_pair hne
  have hc0 : 0 < c := lt_of_lt_of_le (sqrt_log_pos hp) hcp
  have hA00 : 0 ≤ A0 := le_trans (sq_nonneg _) hA0
  have ht1 : (1 : ℝ) ≤ 1 + |(t : ℝ)| := by
    have := abs_nonneg (t : ℝ); linarith
  have ht0 : (0 : ℝ) < 1 + |(t : ℝ)| := by linarith
  set T : ℝ := log (1 + |(t : ℝ)|) with hT
  have hT0 : 0 ≤ T := log_nonneg ht1
  set x0 : ℝ := sqrt (A0 + T / 2) with hx0def
  have hx0sq : x0 ^ 2 = A0 + T / 2 := sq_sqrt (by linarith)
  have hx00 : 0 ≤ x0 := sqrt_nonneg _
  have hx : 50 * c ≤ x0 := by
    have h1 : (50 * c) ^ 2 ≤ x0 ^ 2 := by rw [hx0sq]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hx00 two_ne_zero).mp h1
  have hAx : A0 ≤ x0 ^ 2 := by rw [hx0sq]; linarith
  set Λ : ℝ := Lam c x0 B with hΛ
  have hg1 : 1 ≤ g := by
    have := sqrt5_bounds.1
    rw [hg]; linarith
  have hAΛ : A0 ≤ Λ := by
    refine le_trans hAx ?_
    have h1 : x0 ^ 2 ≤ (x0 + 4 * c) ^ 2 := pow_le_pow_left₀ hx00 (by linarith) 2
    refine le_trans h1 ?_
    rw [hΛ]
    unfold Lam
    rw [← hg]
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hg1)
  have heA : exp A0 ≤ 64 * exp Λ := by
    have h1 := exp_le_exp.mpr hAΛ
    have := exp_pos Λ
    linarith
  have hS : ∀ l ∈ ({p, q} : Finset ℕ), 2 ≤ l := by
    intro l hl
    rcases mem_insert.mp hl with h | h
    · omega
    · rw [mem_singleton] at h; omega
  have hlog : ∀ l ∈ ({p, q} : Finset ℕ), β ≤ log l := by
    intro l hl
    rcases mem_insert.mp hl with h | h
    · rw [h]; exact hβp
    · rw [mem_singleton] at h; rw [h]; exact hβq
  have hH2 : (({p, q} : Finset ℕ).card : ℝ) * log (8 * D) + 1 = H := by
    rw [hcard, hH]; push_cast; ring
  obtain ⟨X, hX1, hX2, hXfree⟩ := exists_free {p, q} hS hD (R := 64 * exp Λ) hβ hlog
    (by rw [hH2]; exact le_trans hR0 heA)
  rw [hH2] at hX2
  obtain ⟨V, a, b, hV, hdiff, haX, hbX, ha, hb⟩ :=
    dens X hXfree (le_trans hXD (le_trans heA hX1))
  have hX100 : 100 ≤ X := by
    have : (100 : ℝ) ≤ X := le_trans h100 (le_trans heA hX1)
    exact_mod_cast this
  have htx : |(t : ℝ)| ≤ exp (2 * x0 ^ 2) / 32 := by
    have e : exp (2 * x0 ^ 2) = exp (2 * A0) * (1 + |(t : ℝ)|) := by
      have e2 : 2 * x0 ^ 2 = 2 * A0 + T := by rw [hx0sq]; ring
      rw [e2, exp_add, hT, exp_log ht0]
    have h5 : (32 : ℝ) ≤ exp (2 * A0) := by
      have := exp_le_exp.mpr h32
      rwa [exp_log (by norm_num : (0 : ℝ) < 32)] at this
    have h6 := mul_le_mul_of_nonneg_right h5 ht0.le
    rw [e, le_div_iff₀ (by norm_num : (0 : ℝ) < 32)]
    linarith
  obtain ⟨k, hk, hkp, hkq⟩ := witness_of_density_golden hp hq hpq hD12 (s := 2 / D) hK
    hcp hcq hx
    (le_trans hDp (mul_le_mul_of_nonneg_left hAx
      (mul_nonneg (by norm_num) (log_pos' hp).le)))
    (le_trans hDq (mul_le_mul_of_nonneg_left hAx
      (mul_nonneg (by norm_num) (log_pos' hq).le)))
    hB (X := X) hX1 hX100 V hV a b hdiff haX hbX ha hb t htx
  have er : 4 * (2 / (D : ℝ) + 1 / D) = 12 / D := by ring
  rw [er] at hkp hkq
  refine ⟨k, ?_, hkp, hkq⟩
  have h1 : |(k : ℝ)| ≤ 8 * (X : ℝ) := by exact_mod_cast hk
  have hsq2 : (0 : ℝ) < sqrt 2 := sqrt_pos.mpr (by norm_num)
  have hg0 : 0 < g := by linarith
  have hgB : 0 ≤ g ^ (B + 2) := (pow_pos hg0 _).le
  -- the size of the last window
  have hΛle : Λ ≤ g ^ (B + 2) * (sqrt A0 + 4 * c) ^ 2 + g ^ (B + 2) / 2 * T
      + g ^ (B + 2) * (8 * c) / sqrt 2 * sqrt T := by
    have hx0le : x0 ≤ sqrt A0 + sqrt T / sqrt 2 := by
      have e1 : sqrt T / sqrt 2 = sqrt (T / 2) := (sqrt_div hT0 2).symm
      rw [e1]
      have hu := sqrt_nonneg A0
      have hv := sqrt_nonneg (T / 2)
      have e3 : x0 ^ 2 ≤ (sqrt A0 + sqrt (T / 2)) ^ 2 := by
        rw [hx0sq, add_sq, sq_sqrt hA00, sq_sqrt (by linarith : (0 : ℝ) ≤ T / 2)]
        have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu) hv
        linarith
      exact (pow_le_pow_iff_left₀ hx00 (add_nonneg hu hv) two_ne_zero).mp e3
    have h3 : (x0 + 4 * c) ^ 2
        ≤ (sqrt A0 + 4 * c) ^ 2 + T / 2 + 8 * c * (sqrt T / sqrt 2) := by
      have e : (x0 + 4 * c) ^ 2 = x0 ^ 2 + 8 * c * x0 + (4 * c) ^ 2 := by ring
      have e2 : (sqrt A0 + 4 * c) ^ 2 = A0 + 8 * c * sqrt A0 + (4 * c) ^ 2 := by
        rw [add_sq, sq_sqrt hA00]; ring
      have h4 := mul_le_mul_of_nonneg_left hx0le (show (0 : ℝ) ≤ 8 * c by linarith)
      rw [e, e2, hx0sq]; nlinarith
    have h5 : Λ = g ^ (B + 2) * (x0 + 4 * c) ^ 2 := by
      rw [hΛ]; unfold Lam; rw [← hg]
    rw [h5]
    refine le_trans (mul_le_mul_of_nonneg_left h3 hgB) (le_of_eq ?_)
    ring
  have epow : (1 + |(t : ℝ)|) ^ (g ^ (B + 2) / 2) = exp (g ^ (B + 2) / 2 * T) := by
    rw [rpow_def_of_pos ht0, ← hT, mul_comm]
  calc |(k : ℝ)| ≤ 8 * (X : ℝ) := h1
    _ ≤ 8 * (2 * exp H * (64 * exp Λ)) := by linarith
    _ = 1024 * exp (H + Λ) := by rw [exp_add]; ring
    _ ≤ 1024 * exp (H + (g ^ (B + 2) * (sqrt A0 + 4 * c) ^ 2 + g ^ (B + 2) / 2 * T
          + g ^ (B + 2) * (8 * c) / sqrt 2 * sqrt T)) := by
        refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
        linarith
    _ = _ := by
        rw [epow]
        simp only [exp_add]
        ring

end TwoPrimesGolden
