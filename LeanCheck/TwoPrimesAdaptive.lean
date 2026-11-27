import LeanCheck.TwoPrimesFreeHeight

/-!
# Windows with an additive allowance for rounding

The windows `[x_j, x_{j+1})` in the variable `n * sqrt (log base)` follow
`x_{j+1} = sqrt 2 * x_j + 4 c`, `c ≥ sqrt (log base)`.

* `rigidity_adaptive`: if the product of the two digit products at `θ` is at least `η`, then `θ`
  is within `exp(-2 x0^2)/2` of an integer.
* `exists_four'`: the positivity criterion with the phase threshold `α` as a parameter.
* `witness_of_density_adaptive`: height `64 exp(x_{B+1}^2)`, `B = ⌊12 D² log(17K)⌋`, targets
  `|t| ≤ exp(2 x0^2)/32`.
* `xs_closed`: hence `x_{B+1}^2 ≤ 2^(B+1) (x0 + C)^2`, `C = 4c/(sqrt 2 - 1)`.
* `witness_of_free_heights_adaptive`: at a fixed radius
  `|k| ≤ C0 (1+|t|)^(2^B) exp(C1 sqrt (log (1+|t|)))`.  The density is a hypothesis.

The windows, the constant `17` and the resulting bounds are due to ChatGPT.
-/

namespace TwoPrimesAdaptive

open Finset Real TwoPrimesEffective TwoPrimesWindows TwoPrimesFreeHeight

/-- The window ends. -/
noncomputable def xs (c x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | j + 1 => sqrt 2 * xs c x0 j + 4 * c

lemma sqrt2_bounds : (1.4 : ℝ) < sqrt 2 ∧ sqrt 2 < 1.5 := by
  constructor
  · rw [lt_sqrt (by norm_num)]; norm_num
  · rw [sqrt_lt' (by norm_num)]; norm_num

lemma xs_mono {c x0 : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x0) (j : ℕ) :
    x0 ≤ xs c x0 j ∧ xs c x0 j + 4 * c ≤ xs c x0 (j + 1) := by
  have h2 := sqrt2_bounds.1
  have step : ∀ y : ℝ, 0 ≤ y → y ≤ sqrt 2 * y := fun y hy =>
    le_mul_of_one_le_left hy (by linarith)
  have low : ∀ j, x0 ≤ xs c x0 j := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      have h := step (xs c x0 j) (le_trans hx ih)
      change x0 ≤ sqrt 2 * xs c x0 j + 4 * c
      linarith
  refine ⟨low j, ?_⟩
  have h := step (xs c x0 j) (le_trans hx (low j))
  change xs c x0 j + 4 * c ≤ sqrt 2 * xs c x0 j + 4 * c
  linarith

lemma xs_le {c x0 : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x0) {i j : ℕ} (h : i ≤ j) :
    xs c x0 i ≤ xs c x0 j := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih =>
    have := (xs_mono hc hx m).2
    exact le_trans ih (by linarith)

/-- The closed form of the recursion. -/
lemma xs_closed (c x0 : ℝ) (j : ℕ) :
    xs c x0 j + 4 * c / (sqrt 2 - 1)
      = sqrt 2 ^ j * (x0 + 4 * c / (sqrt 2 - 1)) := by
  have h2 := sqrt2_bounds.1
  have hne : sqrt 2 - 1 ≠ 0 := by
    intro h; linarith
  induction j with
  | zero => simp [xs]
  | succ j ih =>
    have e : xs c x0 (j + 1) + 4 * c / (sqrt 2 - 1)
        = sqrt 2 * (xs c x0 j + 4 * c / (sqrt 2 - 1)) := by
      change sqrt 2 * xs c x0 j + 4 * c + 4 * c / (sqrt 2 - 1) = _
      have e1 : 4 * c + 4 * c / (sqrt 2 - 1) = sqrt 2 * (4 * c / (sqrt 2 - 1)) := by
        field_simp; ring
      rw [add_assoc, e1, ← mul_add]
    rw [e, ih, pow_succ]; ring

lemma xs_sq_le {c x0 : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x0) (j : ℕ) :
    xs c x0 j ^ 2 ≤ 2 ^ j * (x0 + 4 * c / (sqrt 2 - 1)) ^ 2 := by
  have h2 := sqrt2_bounds.1
  have hC : 0 ≤ 4 * c / (sqrt 2 - 1) := div_nonneg (by linarith) (by linarith)
  have h0 : 0 ≤ xs c x0 j := le_trans hx (xs_mono hc hx j).1
  have h1 : xs c x0 j ≤ sqrt 2 ^ j * (x0 + 4 * c / (sqrt 2 - 1)) := by
    rw [← xs_closed]; linarith
  have h3 := pow_le_pow_left₀ h0 h1 2
  have e : (sqrt 2 ^ j) ^ 2 = 2 ^ j := by
    rw [← pow_mul, mul_comm, pow_mul, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rwa [mul_pow, e] at h3

/-- First level of the window `j` of the base `p`. -/
noncomputable def loA (p : ℕ) (c x0 : ℝ) (j : ℕ) : ℕ := ⌈xs c x0 j / sqrt (log p)⌉₊

/-- Last level of the window `j` of the base `p`. -/
noncomputable def hiA (p : ℕ) (c x0 : ℝ) (j : ℕ) : ℕ := ⌊xs c x0 (j + 1) / sqrt (log p)⌋₊

lemma sqrt_log_pos {p : ℕ} (hp : 2 ≤ p) : 0 < sqrt (log (p : ℝ)) := sqrt_pos.mpr (log_pos' hp)

lemma windowA {p : ℕ} (hp : 2 ≤ p) {c x0 : ℝ} (hc : sqrt (log p) ≤ c) (hx : 50 * c ≤ x0)
    (j : ℕ) :
    loA p c x0 j ≤ hiA p c x0 j ∧ hiA p c x0 j ≤ loA p c x0 (j + 1) ∧
    ((loA p c x0 j : ℝ) ^ 2) * log p ≤ (xs c x0 j + c) ^ 2 ∧
    (sqrt 2 * xs c x0 j + 3 * c) ^ 2 ≤ ((hiA p c x0 j : ℝ) ^ 2) * log p ∧
    ((hiA p c x0 j : ℝ) ^ 2) * log p ≤ xs c x0 (j + 1) ^ 2 := by
  set s := sqrt (log (p : ℝ)) with hs
  have hs0 : 0 < s := sqrt_log_pos hp
  have hc0 : 0 ≤ c := le_trans hs0.le hc
  have hx0 : 0 ≤ x0 := by linarith
  have hlog : s ^ 2 = log p := sq_sqrt (log_pos' hp).le
  have hxj0 : 0 ≤ xs c x0 j := le_trans hx0 (xs_mono hc0 hx0 j).1
  have hstep := (xs_mono hc0 hx0 j (c := c) (x0 := x0)).2
  have hdef : xs c x0 (j + 1) = sqrt 2 * xs c x0 j + 4 * c := rfl
  have hxj1 : 0 ≤ xs c x0 (j + 1) := by linarith
  have lo1 : xs c x0 j / s ≤ (loA p c x0 j : ℝ) := Nat.le_ceil _
  have lo2 : (loA p c x0 j : ℝ) < xs c x0 j / s + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hxj0 hs0.le)
  have hi1 : (hiA p c x0 j : ℝ) ≤ xs c x0 (j + 1) / s :=
    Nat.floor_le (div_nonneg hxj1 hs0.le)
  have hi2 : xs c x0 (j + 1) / s - 1 < (hiA p c x0 j : ℝ) := Nat.sub_one_lt_floor _
  have lom : (loA p c x0 j : ℝ) * s ≤ xs c x0 j + c := by
    have := mul_le_mul_of_nonneg_right lo2.le hs0.le
    rw [add_mul, one_mul, div_mul_cancel₀ _ hs0.ne'] at this
    linarith
  have him : sqrt 2 * xs c x0 j + 3 * c ≤ (hiA p c x0 j : ℝ) * s := by
    have := mul_le_mul_of_nonneg_right hi2.le hs0.le
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hs0.ne'] at this
    linarith
  have him2 : (hiA p c x0 j : ℝ) * s ≤ xs c x0 (j + 1) := by
    have := mul_le_mul_of_nonneg_right hi1 hs0.le
    rwa [div_mul_cancel₀ _ hs0.ne'] at this
  have esq : ∀ n : ℝ, n ^ 2 * log p = (n * s) ^ 2 := by
    intro n; rw [mul_pow, hlog]
  have h3 : 0 ≤ sqrt 2 * xs c x0 j + 3 * c := by
    have := mul_nonneg (sqrt_nonneg 2) hxj0
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h : (loA p c x0 j : ℝ) * s ≤ (hiA p c x0 j : ℝ) * s := by
      refine le_trans lom (le_trans ?_ him)
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ sqrt 2 by
        have := sqrt2_bounds.1; linarith) hxj0
      linarith
    exact_mod_cast le_of_mul_le_mul_right h hs0
  · have h : (hiA p c x0 j : ℝ) ≤ (loA p c x0 (j + 1) : ℝ) := le_trans hi1 (Nat.le_ceil _)
    exact_mod_cast h
  · rw [esq]; exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hs0.le) lom 2
  · rw [esq]; exact pow_le_pow_left₀ h3 him 2
  · rw [esq]; exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hs0.le) him2 2

lemma loA_mono {p : ℕ} (_hp : 2 ≤ p) {c x0 : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x0) {i j : ℕ}
    (h : i ≤ j) : loA p c x0 i ≤ loA p c x0 j :=
  Nat.ceil_le_ceil (div_le_div_of_nonneg_right (xs_le hc hx h) (sqrt_nonneg _))

lemma hiA_mono {p : ℕ} {c x0 : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x0) {i j : ℕ}
    (h : i ≤ j) : hiA p c x0 i ≤ hiA p c x0 j :=
  Nat.floor_le_floor (div_le_div_of_nonneg_right (xs_le hc hx (by omega)) (sqrt_nonneg _))

/-- **Rigidity with additive allowances.** -/
theorem rigidity_adaptive {p q D B Np Nq : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) {η c x0 θ : ℝ} (hη : 0 < η) (hB : 24 * (D : ℝ) ^ 2 * (-log η) < B + 1)
    (hcp : sqrt (log p) ≤ c) (hcq : sqrt (log q) ≤ c) (hx : 50 * c ≤ x0)
    (hDp : log (2 * D) ^ 2 ≤ 4 * log p * x0 ^ 2) (hDq : log (2 * D) ^ 2 ≤ 4 * log q * x0 ^ 2)
    (hNp : hiA p c x0 B ≤ Np) (hNq : hiA q c x0 B ≤ Nq)
    (h12 : η ≤ |prodDigit p D Np θ| * |prodDigit q D Nq θ|) :
    ∃ z : ℤ, |θ - z| ≤ exp (-(2 * x0 ^ 2)) / 2 := by
  classical
  have hc0 : 0 < c := lt_of_lt_of_le (sqrt_log_pos hp) hcp
  have hx0 : 0 ≤ x0 := by linarith
  set Mp := marked p D Np θ with hMp
  set Mq := marked q D Nq θ with hMq
  have hsum : Mp.card + Mq.card ≤ B := by
    have h := lt_of_le_of_lt (card_marked_joint hD hη h12) hB
    have : Mp.card + Mq.card < B + 1 := by exact_mod_cast h
    omega
  have hord : ∀ r : ℕ, 2 ≤ r → sqrt (log r) ≤ c → ∀ j k, j < k → hiA r c x0 j ≤ loA r c x0 k := by
    intro r hr hcr j k hjk
    exact le_trans (windowA hr hcr hx j).2.1
      (loA_mono hr hc0.le hx0 (show j + 1 ≤ k by omega))
  have hfree : ∃ k ∈ Finset.range (B + 1),
      (¬ ∃ n ∈ Mp, loA p c x0 k ≤ n ∧ n < hiA p c x0 k) ∧
      (¬ ∃ n ∈ Mq, loA q c x0 k ≤ n ∧ n < hiA q c x0 k) := by
    by_contra hcon
    have hsub : Finset.range (B + 1)
        ⊆ (Finset.range (B + 1)).filter (fun k => ∃ n ∈ Mp, loA p c x0 k ≤ n ∧ n < hiA p c x0 k)
          ∪ (Finset.range (B + 1)).filter
              (fun k => ∃ n ∈ Mq, loA q c x0 k ≤ n ∧ n < hiA q c x0 k) := by
      intro k hk
      rw [mem_union, mem_filter, mem_filter]
      by_cases hP : ∃ n ∈ Mp, loA p c x0 k ≤ n ∧ n < hiA p c x0 k
      · exact Or.inl ⟨hk, hP⟩
      by_cases hQ : ∃ n ∈ Mq, loA q c x0 k ≤ n ∧ n < hiA q c x0 k
      · exact Or.inr ⟨hk, hQ⟩
      exact absurd ⟨k, hk, hP, hQ⟩ hcon
    have h3 := le_trans (card_le_card hsub) (card_union_le _ _)
    have h4 := card_hit (loA p c x0) (hiA p c x0) (hord p hp hcp) Mp (B + 1)
    have h5 := card_hit (loA q c x0) (hiA q c x0) (hord q hq hcq) Mq (B + 1)
    rw [Finset.card_range] at h3
    omega
  obtain ⟨k, hk, hfp, hfq⟩ := hfree
  have hk' : k ≤ B := by rw [Finset.mem_range] at hk; omega
  have chain : ∀ (r N : ℕ), 2 ≤ r → sqrt (log r) ≤ c →
      log (2 * D) ^ 2 ≤ 4 * log r * x0 ^ 2 →
      hiA r c x0 B ≤ N → (¬ ∃ n ∈ marked r D N θ, loA r c x0 k ≤ n ∧ n < hiA r c x0 k) →
      ∃ a : ℤ, |θ - a / (r : ℝ) ^ ((loA r c x0 k) ^ 2)|
        ≤ 1 / (2 * (r : ℝ) ^ ((hiA r c x0 k) ^ 2)) := by
    intro r N hr hcr hDr hN hfr
    have hhiN : hiA r c x0 k ≤ N := le_trans (hiA_mono hc0.le hx0 hk') hN
    have hlog : sqrt (log r) ^ 2 = log r := sq_sqrt (log_pos' hr).le
    have hs0 := sqrt_log_pos hr
    have h50 : 50 * sqrt (log r) ≤ x0 := le_trans (by linarith) hx
    have h100 : 100 * log r ≤ x0 ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h50 2
      rw [mul_pow, hlog] at this
      have := (log_pos' hr).le
      linarith
    have hlo0 : lo r (x0 ^ 2) 0 = loA r c x0 0 := by
      have e : sqrt (x0 ^ 2 / log r) = x0 / sqrt (log r) := by
        rw [sqrt_div (sq_nonneg _), sqrt_sq hx0]
      unfold lo loA
      rw [e]; simp [xs]
    have hJ : ∀ n, loA r c x0 k ≤ n → 1 ≤ range' r D n := by
      intro n hn
      refine range_pos hr hD h100 hDr (k := 0) (le_trans ?_ hn)
      rw [hlo0]
      exact loA_mono hr hc0.le hx0 (Nat.zero_le k)
    refine run hD (windowA hr hcr hx k).1 (fun n hn _ => hJ n hn) (fun n hn hlt => ?_) (by omega)
    by_contra hcon
    refine hfr ⟨n, ?_, hn, hlt⟩
    rw [marked, mem_filter, Finset.mem_range]
    exact ⟨lt_of_lt_of_le hlt hhiN, hJ n hn, not_lt.mp hcon⟩
  obtain ⟨a, ha⟩ := chain p Np hp hcp hDp hNp hfp
  obtain ⟨a', ha'⟩ := chain q Nq hq hcq hDq hNq hfq
  have wp := windowA hp hcp hx k
  have wq := windowA hq hcq hx k
  set y : ℝ := xs c x0 k with hy
  have hyx : x0 ≤ y := (xs_mono hc0.le hx0 k).1
  have hy0 : 0 ≤ y := le_trans hx0 hyx
  set W : ℝ := (sqrt 2 * y + 3 * c) ^ 2 with hW
  set V : ℝ := (y + c) ^ 2 with hV
  set P : ℕ := p ^ ((loA p c x0 k) ^ 2) with hP
  set Q : ℕ := q ^ ((loA q c x0 k) ^ 2) with hQ
  have hPr : (p : ℝ) ^ ((loA p c x0 k) ^ 2) = (P : ℝ) := by rw [hP]; push_cast; rfl
  have hQr : (q : ℝ) ^ ((loA q c x0 k) ^ 2) = (Q : ℝ) := by rw [hQ]; push_cast; rfl
  have hPpos : (0 : ℝ) < P := by
    rw [← hPr]; exact pow_pos (by exact_mod_cast (show 0 < p by omega)) _
  have hQpos : (0 : ℝ) < Q := by
    rw [← hQr]; exact pow_pos (by exact_mod_cast (show 0 < q by omega)) _
  have hPle : (P : ℝ) ≤ exp V := by
    rw [← hPr, pow_eq_exp hp]; apply exp_le_exp.mpr; push_cast; exact wp.2.2.1
  have hQle : (Q : ℝ) ≤ exp V := by
    rw [← hQr, pow_eq_exp hq]; apply exp_le_exp.mpr; push_cast; exact wq.2.2.1
  have hbig : ∀ (r : ℕ), 2 ≤ r → W ≤ ((hiA r c x0 k : ℝ) ^ 2) * log r →
      1 / (2 * (r : ℝ) ^ ((hiA r c x0 k) ^ 2)) ≤ exp (-W) / 2 := by
    intro r hr hw
    have h1 : exp W ≤ (r : ℝ) ^ ((hiA r c x0 k) ^ 2) := by
      rw [pow_eq_exp hr]; apply exp_le_exp.mpr; push_cast; exact hw
    have e : exp (-W) / 2 = 1 / (2 * exp W) := by
      rw [exp_neg]; field_simp
    rw [e]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hε1 : |θ - a / (P : ℝ)| ≤ exp (-W) / 2 := by
    rw [← hPr]; exact le_trans ha (hbig p hp wp.2.2.2.1)
  have hε2 : |θ - a' / (Q : ℝ)| ≤ exp (-W) / 2 := by
    rw [← hQr]; exact le_trans ha' (hbig q hq wq.2.2.2.1)
  have h2b := sqrt2_bounds
  have h22 : sqrt 2 ^ 2 = 2 := sq_sqrt (by norm_num)
  have hgap : 2 * V < W := by
    have e : W = 2 * y ^ 2 + 6 * sqrt 2 * y * c + 9 * c ^ 2 := by
      rw [hW]
      have : (sqrt 2 * y + 3 * c) ^ 2 = sqrt 2 ^ 2 * y ^ 2 + 6 * sqrt 2 * y * c + 9 * c ^ 2 := by
        ring
      rw [this, h22]
    have e2 : 2 * V = 2 * y ^ 2 + 4 * y * c + 2 * c ^ 2 := by rw [hV]; ring
    have h6 : 4 * (y * c) ≤ 6 * sqrt 2 * (y * c) :=
      mul_le_mul_of_nonneg_right (by linarith [h2b.1]) (mul_nonneg hy0 hc0.le)
    have h7 : 0 < c ^ 2 := pow_pos hc0 2
    rw [e, e2]; nlinarith
  have hW0 : 2 * x0 ^ 2 ≤ W := by
    have h1 : y ^ 2 * 2 ≤ W := by
      have h2 : sqrt 2 * y ≤ sqrt 2 * y + 3 * c := by linarith
      have := pow_le_pow_left₀ (mul_nonneg (sqrt_nonneg 2) hy0) h2 2
      rw [mul_pow, h22] at this
      rw [hW]; linarith
    have := pow_le_pow_left₀ hx0 hyx 2
    linarith
  have hzero : a * (Q : ℤ) - a' * (P : ℤ) = 0 := by
    have hdiff : |(a : ℝ) / P - a' / Q| ≤ exp (-W) := by
      have t := abs_sub_le ((a : ℝ) / P) θ (a' / Q)
      rw [abs_sub_comm ((a : ℝ) / P) θ] at t
      linarith
    have e : (a : ℝ) / P - a' / Q = ((a * (Q : ℤ) - a' * (P : ℤ) : ℤ) : ℝ) / (P * Q) := by
      push_cast; field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hPpos hQpos), div_le_iff₀ (mul_pos hPpos hQpos)] at hdiff
    have h3 : exp (-W) * (P * Q) < 1 := by
      have h4 : (P : ℝ) * Q ≤ exp V * exp V := mul_le_mul hPle hQle hQpos.le (exp_pos _).le
      have h5 := mul_le_mul_of_nonneg_left h4 (exp_pos (-W)).le
      refine lt_of_le_of_lt h5 ?_
      rw [← exp_add, ← exp_add, exp_lt_one_iff]
      linarith
    have h6 : |((a * (Q : ℤ) - a' * (P : ℤ) : ℤ) : ℝ)| < 1 := lt_of_le_of_lt hdiff h3
    have h7 : |a * (Q : ℤ) - a' * (P : ℤ)| < 1 := by exact_mod_cast h6
    exact Int.abs_lt_one_iff.mp h7
  have hdvd : (P : ℤ) ∣ a := by
    have hcop : IsCoprime (P : ℤ) (Q : ℤ) := by
      apply Nat.Coprime.isCoprime
      exact Nat.Coprime.pow _ _ hpq
    have : (P : ℤ) ∣ a * (Q : ℤ) := ⟨a', by linear_combination hzero⟩
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨z, hz⟩ := hdvd
  refine ⟨z, ?_⟩
  have e : (a : ℝ) / P = z := by
    rw [hz]; push_cast; field_simp
  rw [e] at hε1
  refine le_trans hε1 (div_le_div_of_nonneg_right (exp_le_exp.mpr ?_) (by norm_num))
  linarith

section Fourier

open Complex

variable {ι : Type*} (I' : Finset ι) (g : ι → ℤ)

/-- Positivity with the phase threshold `α`. -/
theorem exists_four' (t : ℤ) (R L : ℕ) (η E0 α : ℝ) (hα : 0 ≤ α) (hI : I'.Nonempty)
    (hR : ∀ i ∈ I', |g i| ≤ R)
    (hcoll : (((I' ×ˢ I').filter (fun p => g p.1 - g p.2 = 0)).card : ℝ)
      ≤ E0 * (I'.card : ℝ) ^ 2)
    (hsupp : ((I' ×ˢ I').image (fun p => g p.1 - g p.2)).card ≤ L)
    (hspec : ∀ θ : ℝ, η * I'.card ≤ ‖S I' g θ‖ → α ≤ Real.cos (2 * π * (t * θ)))
    (hnum : (1 + α) * η ^ 2 * E0 < α / L) :
    ∃ i1 ∈ I', ∃ i2 ∈ I', ∃ i3 ∈ I', ∃ i4 ∈ I', (g i1 - g i2) + (g i3 - g i4) = t := by
  classical
  set J := (I' ×ˢ I') ×ˢ (I' ×ˢ I') with hJ
  set h4 : (ι × ι) × (ι × ι) → ℤ := fun p => (g p.1.1 - g p.1.2) + (g p.2.1 - g p.2.2) with hh4
  set N : ℕ := 4 * R + t.natAbs + 1 with hNdef
  have hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb4 : ∀ x ∈ J, |h4 x| ≤ 4 * (R : ℤ) := by
    intro x hx
    rw [hJ, mem_product, mem_product, mem_product] at hx
    have a := hR _ hx.1.1
    have b := hR _ hx.1.2
    have c := hR _ hx.2.1
    have d := hR _ hx.2.2
    rw [abs_le] at a b c d
    rw [abs_le]; simp only [hh4]; omega
  have hbt : ∀ x ∈ J, |h4 x - t| < N := by
    intro x hx
    have := hb4 x hx
    rw [abs_le] at this
    rw [abs_lt]; omega
  have hb0 : ∀ x ∈ J, |h4 x - 0| < N := by
    intro x hx
    have := hb4 x hx
    rw [abs_le] at this
    rw [abs_lt]; omega
  set F : ℕ → ℝ := fun r => ‖S I' g ((r : ℝ) / N)‖ with hF
  set Ct := (J.filter (fun x => h4 x = t)).card with hCt
  set C0 := (J.filter (fun x => h4 x = 0)).card with hC0
  set C2 := ((I' ×ˢ I').filter (fun p => g p.1 - g p.2 = 0)).card with hC2
  -- the three counting identities
  have idt : ∑ r ∈ Finset.range N, F r ^ 4 * Real.cos (2 * π * (t * ((r : ℝ) / N)))
      = N * Ct := by
    have hc := count_eq J h4 t hN hbt
    have : ∀ r : ℕ, ∑ x ∈ J, e (((h4 x - t : ℤ) : ℝ) * ((r : ℝ) / N))
        = (((F r ^ 4 : ℝ)) : ℂ) * e (-(t * ((r : ℝ) / N))) := by
      intro r
      simp only [hF]
      rw [norm_four_S, sum_mul]
      refine sum_congr rfl (fun x _ => ?_)
      rw [← e_add]; congr 1; simp only [hh4]; push_cast; ring
    simp_rw [this] at hc
    have := congrArg Complex.re hc
    rw [Complex.re_sum] at this
    simp only [Complex.re_ofReal_mul, e_re] at this
    have e2 : ((N : ℂ) * (Ct : ℂ)).re = (N : ℝ) * Ct := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    rw [← hCt, e2] at this
    rw [← this]
    refine sum_congr rfl (fun r _ => ?_)
    rw [mul_neg, Real.cos_neg]
  have id0 : ∑ r ∈ Finset.range N, F r ^ 4 = N * C0 := by
    have hc := count_eq J h4 0 hN hb0
    have : ∀ r : ℕ, ∑ x ∈ J, e (((h4 x - 0 : ℤ) : ℝ) * ((r : ℝ) / N))
        = (((F r ^ 4 : ℝ)) : ℂ) := by
      intro r
      simp only [hF, sub_zero]
      rw [norm_four_S]
    simp_rw [this] at hc
    rw [← hC0] at hc
    exact_mod_cast hc
  have id2 : ∑ r ∈ Finset.range N, F r ^ 2 = N * C2 := by
    have hb2 : ∀ x ∈ I' ×ˢ I', |(g x.1 - g x.2) - 0| < N := by
      intro x hx
      rw [mem_product] at hx
      have a := hR _ hx.1
      have b := hR _ hx.2
      rw [abs_le] at a b
      rw [abs_lt]; omega
    have hc := count_eq (I' ×ˢ I') (fun p => g p.1 - g p.2) 0 hN hb2
    have : ∀ r : ℕ, ∑ x ∈ I' ×ˢ I', e (((g x.1 - g x.2 - 0 : ℤ) : ℝ) * ((r : ℝ) / N))
        = (((F r ^ 2 : ℝ)) : ℂ) := by
      intro r
      simp only [hF, sub_zero]
      rw [norm_sq_S]
    simp_rw [this] at hc
    rw [← hC2] at hc
    exact_mod_cast hc
  -- the pointwise inequality
  have hpt : ∀ r ∈ Finset.range N,
      α * F r ^ 4 - (1 + α) * η ^ 2 * (I'.card : ℝ) ^ 2 * F r ^ 2
        ≤ F r ^ 4 * Real.cos (2 * π * (t * ((r : ℝ) / N))) := by
    intro r _
    have hF0 : 0 ≤ F r := norm_nonneg _
    by_cases h : η * I'.card ≤ F r
    · have hc := hspec _ h
      have h1 := mul_le_mul_of_nonneg_left hc (pow_nonneg hF0 4)
      have h2 : 0 ≤ (1 + α) * η ^ 2 * (I'.card : ℝ) ^ 2 * F r ^ 2 := by
        have : (0 : ℝ) ≤ 1 + α := by linarith
        positivity
      linarith
    · have h' : F r < η * I'.card := not_le.mp h
      have h1 : F r ^ 2 ≤ (η * I'.card) ^ 2 := pow_le_pow_left₀ hF0 h'.le 2
      have h2 := Real.neg_one_le_cos (2 * π * (t * ((r : ℝ) / N)))
      have h3 := mul_le_mul_of_nonneg_left h2 (pow_nonneg hF0 4)
      have h4' := mul_le_mul_of_nonneg_right h1 (sq_nonneg (F r))
      have h6 := mul_le_mul_of_nonneg_left h4' (show (0 : ℝ) ≤ 1 + α by linarith)
      have e1 : (1 + α) * (F r ^ 2 * F r ^ 2) = F r ^ 4 + α * F r ^ 4 := by ring
      have e2 : (1 + α) * ((η * (I'.card : ℝ)) ^ 2 * F r ^ 2)
          = (1 + α) * η ^ 2 * (I'.card : ℝ) ^ 2 * F r ^ 2 := by ring
      rw [e1, e2] at h6
      linarith
  have hsum := sum_le_sum hpt
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, id0, id2, idt] at hsum
  have hmain : α * (C0 : ℝ) - (1 + α) * η ^ 2 * (I'.card : ℝ) ^ 2 * C2 ≤ Ct := by
    have : (N : ℝ) * (α * (C0 : ℝ) - (1 + α) * η ^ 2 * (I'.card : ℝ) ^ 2 * C2)
        ≤ N * Ct := by
      calc (N : ℝ) * (α * (C0 : ℝ) - (1 + α) * η ^ 2 * (I'.card : ℝ) ^ 2 * C2)
          = α * (N * C0) - (1 + α) * η ^ 2 * (I'.card : ℝ) ^ 2 * (N * C2) := by ring
        _ ≤ _ := hsum
    exact le_of_mul_le_mul_left this hNr
  -- Cauchy-Schwarz for the zero count
  set d : ι × ι → ℤ := fun p => g p.1 - g p.2 with hd
  set T := (I' ×ˢ I').image d with hT
  set rep : ℤ → ℕ := fun x => ((I' ×ˢ I').filter (fun p => d p = x)).card with hrep
  have htot : ∑ x ∈ T, rep x = (I'.card) ^ 2 := by
    rw [sq, ← card_product]
    exact (card_eq_sum_card_image d (I' ×ˢ I')).symm
  have hneg : ∀ x, ((I' ×ˢ I').filter (fun p => d p = -x)).card = rep x := by
    intro x
    refine card_bij' (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_filter, mem_product, hd, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, by omega⟩
    · intro p hp
      simp only [mem_filter, mem_product, hd, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, by omega⟩
    · intro p _; simp
    · intro p _; simp
  have hC0eq : ∑ x ∈ T, rep x ^ 2 = C0 := by
    have hmaps : ∀ p ∈ J.filter (fun x => h4 x = 0), p.1 ∈ I' ×ˢ I' := by
      intro p hp
      rw [mem_filter, hJ, mem_product] at hp
      exact hp.1.1
    have h1 : C0 = ∑ a ∈ I' ×ˢ I', rep (d a) := by
      rw [hC0, card_eq_sum_card_fiberwise (f := fun p => p.1) (t := I' ×ˢ I')
        (fun p hp => hmaps p hp)]
      refine sum_congr rfl (fun a ha => ?_)
      rw [← hneg (d a)]
      refine card_bij' (fun p _ => p.2) (fun b _ => (a, b)) ?_ ?_ ?_ ?_
      · intro p hp
        rw [mem_filter, mem_filter, hJ, mem_product] at hp
        obtain ⟨⟨⟨_, hp2⟩, hz⟩, hpa⟩ := hp
        rw [mem_filter]
        refine ⟨hp2, ?_⟩
        simp only [hh4] at hz
        simp only [hd, ← hpa]
        omega
      · intro b hb
        rw [mem_filter] at hb
        rw [mem_filter, mem_filter, hJ, mem_product]
        refine ⟨⟨⟨ha, hb.1⟩, ?_⟩, rfl⟩
        have := hb.2
        simp only [hd] at this
        simp only [hh4]; omega
      · intro p hp
        rw [mem_filter] at hp
        exact Prod.ext hp.2.symm rfl
      · intro b _; rfl
    rw [h1, ← sum_fiberwise_of_maps_to (g := d) (t := T)
      (fun a ha => mem_image_of_mem d ha) (fun a => rep (d a))]
    refine sum_congr rfl (fun x _ => ?_)
    have : ∑ a ∈ (I' ×ˢ I').filter (fun a => d a = x), rep (d a)
        = ∑ _a ∈ (I' ×ˢ I').filter (fun a => d a = x), rep x :=
      sum_congr rfl (fun a ha => by rw [(mem_filter.mp ha).2])
    rw [this, sum_const, smul_eq_mul, sq]
  have hCS : ((I'.card : ℝ) ^ 2) ^ 2 ≤ L * C0 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := T) (f := fun x => (rep x : ℝ))
    have h2 : ∑ x ∈ T, (rep x : ℝ) = (I'.card : ℝ) ^ 2 := by exact_mod_cast htot
    have h3 : ∑ x ∈ T, (rep x : ℝ) ^ 2 = (C0 : ℝ) := by exact_mod_cast hC0eq
    rw [h2, h3] at h1
    refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    exact_mod_cast hsupp
  have hIpos : (0 : ℝ) < I'.card := by exact_mod_cast card_pos.mpr hI
  have hLpos : (0 : ℝ) < L := by
    have : 0 < T.card := by
      rw [hT]; exact card_pos.mpr ((hI.product hI).image d)
    exact_mod_cast lt_of_lt_of_le this hsupp
  have hpos : (0 : ℝ) < Ct := by
    have h1 : ((I'.card : ℝ) ^ 2) ^ 2 / L ≤ C0 := by
      rw [div_le_iff₀ hLpos]; linarith
    have h2 : (1 + α) * η ^ 2 * (I'.card : ℝ) ^ 2 * C2
        ≤ (1 + α) * η ^ 2 * (I'.card : ℝ) ^ 2 * (E0 * (I'.card : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hcoll (by
        have : (0 : ℝ) ≤ 1 + α := by linarith
        positivity)
    have h3 : 0 < ((I'.card : ℝ) ^ 2) ^ 2 * (α / L - (1 + α) * η ^ 2 * E0) :=
      mul_pos (by positivity) (by linarith)
    have e : ((I'.card : ℝ) ^ 2) ^ 2 * (α / L - (1 + α) * η ^ 2 * E0)
        = α * (((I'.card : ℝ) ^ 2) ^ 2 / L)
          - (1 + α) * η ^ 2 * (I'.card : ℝ) ^ 2 * (E0 * (I'.card : ℝ) ^ 2) := by ring
    rw [e] at h3
    have h1' := mul_le_mul_of_nonneg_left h1 hα
    linarith
  have hpos' : 0 < Ct := by exact_mod_cast hpos
  obtain ⟨x, hx⟩ := card_pos.mp hpos'
  rw [mem_filter, hJ, mem_product, mem_product, mem_product] at hx
  exact ⟨x.1.1, hx.1.1.1, x.1.2, hx.1.1.2, x.2.1, hx.1.2.1, x.2.2, hx.1.2.2, hx.2⟩

end Fourier

/-- **Density to witnesses**, with the adaptive windows. -/
theorem witness_of_density_adaptive {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) {K c x0 s : ℝ} (hK : 1 ≤ K)
    (hcp : sqrt (log p) ≤ c) (hcq : sqrt (log q) ≤ c) (hx : 50 * c ≤ x0)
    (hDp : log (2 * D) ^ 2 ≤ 4 * log p * x0 ^ 2) (hDq : log (2 * D) ^ 2 ≤ 4 * log q * x0 ^ 2)
    {B : ℕ} (hB : B = ⌊12 * (D : ℝ) ^ 2 * log (17 * K)⌋₊)
    {X : ℕ} (hX : 64 * exp (xs c x0 (B + 1) ^ 2) ≤ X) (hX100 : 100 ≤ X)
    (V : Finset ℤ) (hV : (X : ℝ) ≤ K * V.card) (a b : ℤ → ℤ)
    (hdiff : ∀ v ∈ V, v = a v - b v)
    (haX : ∀ v ∈ V, |a v| ≤ (X : ℤ)) (hbX : ∀ v ∈ V, |b v| ≤ (X : ℤ))
    (ha : ∀ v ∈ V, Small p s (a v)) (hb : ∀ v ∈ V, Small q s (b v))
    (t : ℤ) (ht : |(t : ℝ)| ≤ exp (2 * x0 ^ 2) / 32) :
    ∃ k : ℤ, |k| ≤ 8 * (X : ℤ) ∧ Small p (4 * (s + 1 / D)) k
      ∧ Small q (4 * (s + 1 / D)) (k - t) := by
  classical
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
  set Np := hiA p c x0 B with hNp
  set Nq := hiA q c x0 B with hNq
  -- the digit sets are short
  have hfit : ∀ r : ℕ, 2 ≤ r → sqrt (log r) ≤ c → (r : ℝ) ^ ((hiA r c x0 B) ^ 2) ≤ X / 64 := by
    intro r hr hcr
    have h1 : (r : ℝ) ^ ((hiA r c x0 B) ^ 2) ≤ exp (xs c x0 (B + 1) ^ 2) := by
      rw [pow_eq_exp hr]
      apply exp_le_exp.mpr
      push_cast
      exact (windowA hr hcr hx B).2.2.2.2
    exact le_trans h1 (by linarith)
  set I' : Finset (ℤ × (Fin Np → ℤ) × (Fin Nq → ℤ)) :=
    V ×ˢ (vectors p D Np ×ˢ vectors q D Nq) with hI'
  set g : ℤ × (Fin Np → ℤ) × (Fin Nq → ℤ) → ℤ :=
    fun i => i.1 + value p i.2.1 - value q i.2.2 with hg
  have hVne : V.Nonempty := card_pos.mp (by exact_mod_cast hVpos)
  have hIne : I'.Nonempty :=
    hVne.product ((vectors_nonempty p D Np).product (vectors_nonempty q D Nq))
  have hcard : (I'.card : ℝ)
      = V.card * ((vectors p D Np).card * (vectors q D Nq).card) := by
    rw [hI', card_product, card_product]; push_cast; ring
  have hmem : ∀ i ∈ I', i.1 ∈ V ∧ i.2.1 ∈ vectors p D Np ∧ i.2.2 ∈ vectors q D Nq := by
    intro i hi'
    rw [hI', mem_product, mem_product] at hi'
    exact ⟨hi'.1, hi'.2.1, hi'.2.2⟩
  have svp : ∀ j ∈ vectors p D Np, 64 * |value p j| ≤ (X : ℤ) := by
    intro j hj
    have h1 := le_trans (abs_value_le hp hD hj) (hfit p hp hcp)
    have h2 : 64 * |(value p j : ℝ)| ≤ X := by linarith
    exact_mod_cast h2
  have svq : ∀ j ∈ vectors q D Nq, 64 * |value q j| ≤ (X : ℤ) := by
    intro j hj
    have h1 := le_trans (abs_value_le hq hD hj) (hfit q hq hcq)
    have h2 : 64 * |(value q j : ℝ)| ≤ X := by linarith
    exact_mod_cast h2
  have hvp : ∀ j ∈ vectors p D Np, |value p j| ≤ (X : ℤ) := by
    intro j hj
    have := svp j hj
    have := abs_nonneg (value p j)
    omega
  have hvq : ∀ j ∈ vectors q D Nq, |value q j| ≤ (X : ℤ) := by
    intro j hj
    have := svq j hj
    have := abs_nonneg (value q j)
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
    have a5 : |value p i.2.1| + |value q i.2.2| ≤ ((X / 32 : ℕ) : ℤ) := by
      have := abs_nonneg (value p i.2.1)
      have := abs_nonneg (value q i.2.2)
      omega
    have a6 := le_abs_self (value p i.2.1)
    have a7 := neg_le_abs (value p i.2.1)
    have a8 := le_abs_self (value q i.2.2)
    have a9 := neg_le_abs (value q i.2.2)
    rw [abs_le] at a1 a2
    rw [abs_le]; simp only [hg, hM]; push_cast at a5 ⊢; omega
  -- collisions
  have hcoll : (((I' ×ˢ I').filter (fun x => g x.1 - g x.2 = 0)).card : ℝ)
      ≤ (1 / V.card) * (I'.card : ℝ) ^ 2 := by
    set W := vectors p D Np ×ˢ vectors q D Nq with hW
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
        ≤ (I'.card : ℝ) * ((vectors p D Np).card * (vectors q D Nq).card) := by
      have h3 : (I' ×ˢ W).card = I'.card * ((vectors p D Np).card * (vectors q D Nq).card) := by
        rw [card_product I' W, hW, card_product (vectors p D Np)]
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
  have hBlt : 24 * (D : ℝ) ^ 2 * (-log η) < B + 1 := by
    have h := Nat.lt_floor_add_one (12 * (D : ℝ) ^ 2 * log (17 * K))
    rw [← hB] at h
    rw [hlogη]
    linarith
  have hfactor : ∀ θ : ℝ, S I' g θ = (∑ v ∈ V, e ((v : ℝ) * θ))
      * ((∑ j ∈ vectors p D Np, e ((value p j : ℝ) * θ))
        * (∑ j ∈ vectors q D Nq, e ((value q j : ℝ) * (-θ)))) := by
    intro θ
    rw [S, hI', sum_product, sum_mul]
    refine sum_congr rfl (fun v _ => ?_)
    rw [sum_product, sum_mul_sum, mul_sum]
    refine sum_congr rfl (fun j _ => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun l _ => ?_)
    rw [← e_add, ← e_add]
    congr 1; simp only [hg]; push_cast; ring
  have heven : ∀ θ : ℝ, prodDigit q D Nq (-θ) = prodDigit q D Nq θ := by
    intro θ
    unfold prodDigit
    refine prod_congr rfl (fun n _ => ?_)
    rw [mul_neg, digit_neg]
  have hle1 : ∀ (r N : ℕ) (θ : ℝ), |prodDigit r D N θ| ≤ 1 := by
    intro r N θ
    unfold prodDigit
    rw [abs_prod]
    exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_digit_le_one _ _)
  have hspec : ∀ θ : ℝ, η * I'.card ≤ ‖S I' g θ‖ → 99 / 100 ≤ Real.cos (2 * π * (t * θ)) := by
    intro θ hθ
    have hnorm : ‖S I' g θ‖ ≤ (I'.card : ℝ)
        * (|prodDigit p D Np θ| * |prodDigit q D Nq θ|) := by
      rw [hfactor, norm_mul, norm_mul, sum_vectors, sum_vectors, heven,
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
    have hboth : η ≤ |prodDigit p D Np θ| * |prodDigit q D Nq θ| := by
      have := le_trans hθ hnorm
      rw [mul_comm η] at this
      exact le_of_mul_le_mul_left this hIpos
    obtain ⟨z, hz⟩ := rigidity_adaptive hp hq hpq hD hηpos hBlt hcp hcq hx hDp hDq (le_of_eq hNp.symm)
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
  set P : ℤ × (Fin Np → ℤ) × (Fin Nq → ℤ) → ℤ := fun i => a i.1 + value p i.2.1 with hP
  set Q : ℤ × (Fin Np → ℤ) × (Fin Nq → ℤ) → ℤ := fun i => b i.1 + value q i.2.2 with hQ
  have hPQ : ∀ i ∈ I', g i = P i - Q i := by
    intro i hi'
    have := hdiff _ (hmem i hi').1
    simp only [hg, hP, hQ]; omega
  set k := (P i1 - P i2) + (P i3 - P i4) with hk
  have hkt : k - t = (Q i1 - Q i2) + (Q i3 - Q i4) := by
    rw [hPQ _ m1, hPQ _ m2, hPQ _ m3, hPQ _ m4] at hsum
    omega
  have sP : ∀ i ∈ I', Small p (s + 1 / D) (P i) := fun i hi' =>
    (ha _ (hmem i hi').1).add (small_value hp hD (hmem i hi').2.1)
  have sQ : ∀ i ∈ I', Small q (s + 1 / D) (Q i) := fun i hi' =>
    (hb _ (hmem i hi').1).add (small_value hq hD (hmem i hi').2.2)
  have e4 : 4 * (s + 1 / (D : ℝ))
      = ((s + 1 / D) + (s + 1 / D)) + ((s + 1 / D) + (s + 1 / D)) := by ring
  refine ⟨k, ?_, ?_, ?_⟩
  · have bound : ∀ i ∈ I', |P i| ≤ 2 * (X : ℤ) := by
      intro i hi'
      have h1 := haX _ (hmem i hi').1
      have h2 := hvp _ (hmem i hi').2.1
      have := abs_add_le (a i.1) (value p i.2.1)
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

/-- **Fixed radius, every target.**  The exponent is `2^B`, up to a factor which grows more
slowly than every power. -/
theorem witness_of_free_heights_adaptive {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : Nat.Coprime p q) (hD : 1 ≤ D) {K A0 XD β H c C : ℝ} (hK : 1 ≤ K)
    (hcp : sqrt (log p) ≤ c) (hcq : sqrt (log q) ≤ c)
    (hA0 : (50 * c) ^ 2 ≤ A0)
    (hDp : log (2 * D) ^ 2 ≤ 4 * log p * A0) (hDq : log (2 * D) ^ 2 ≤ 4 * log q * A0)
    (h32 : log 32 ≤ 2 * A0)
    {B : ℕ} (hB : B = ⌊12 * (D : ℝ) ^ 2 * log (17 * K)⌋₊)
    (hH : H = 2 * log (8 * D) + 1) (hC : C = 4 * c / (sqrt 2 - 1))
    (hβ : 0 < β) (hβp : β ≤ log p) (hβq : β ≤ log q)
    (hR0 : 8 * exp ((H + log (8 * D)) ^ 2 / (4 * β)) ≤ exp A0)
    (h100 : 100 ≤ exp A0) (hXD : XD ≤ exp A0)
    (dens : ∀ X : ℕ, Free {p, q} D X → XD ≤ X → ∃ V : Finset ℤ, ∃ a b : ℤ → ℤ,
      (X : ℝ) ≤ K * V.card ∧ (∀ v ∈ V, v = a v - b v) ∧
      (∀ v ∈ V, |a v| ≤ (X : ℤ)) ∧ (∀ v ∈ V, |b v| ≤ (X : ℤ)) ∧
      (∀ v ∈ V, Small p (2 / D) (a v)) ∧ (∀ v ∈ V, Small q (2 / D) (b v)))
    (t : ℤ) :
    ∃ k : ℤ, |(k : ℝ)| ≤ 1024 * exp (H + 2 ^ (B + 1) * (sqrt A0 + C) ^ 2)
          * (1 + |(t : ℝ)|) ^ (2 ^ B)
          * exp (2 ^ (B + 2) * C / sqrt 2 * sqrt (log (1 + |(t : ℝ)|)))
      ∧ Small p (12 / D) k ∧ Small q (12 / D) (k - t) := by
  classical
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
  set Λ : ℝ := xs c x0 (B + 1) ^ 2 with hΛ
  have hAΛ : A0 ≤ Λ := by
    refine le_trans hAx ?_
    exact pow_le_pow_left₀ hx00 (xs_mono hc0.le hx00 (B + 1)).1 2
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
  obtain ⟨k, hk, hkp, hkq⟩ := witness_of_density_adaptive hp hq hpq hD (s := 2 / D) hK
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
  have hC0 : 0 ≤ C := by
    rw [hC]; exact div_nonneg (by linarith) (by linarith [sqrt2_bounds.1])
  have hsq2 : (0 : ℝ) < sqrt 2 := sqrt_pos.mpr (by norm_num)
  -- the size of the last window
  have hΛle : Λ ≤ 2 ^ (B + 1) * (sqrt A0 + C) ^ 2 + 2 ^ B * T
      + 2 ^ (B + 2) * C / sqrt 2 * sqrt T := by
    have h2 : Λ ≤ 2 ^ (B + 1) * (x0 + C) ^ 2 := by
      rw [hC]; exact xs_sq_le hc0.le hx00 (B + 1)
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
    have h3 : (x0 + C) ^ 2 ≤ (sqrt A0 + C) ^ 2 + T / 2 + 2 * C * (sqrt T / sqrt 2) := by
      have e : (x0 + C) ^ 2 = x0 ^ 2 + 2 * C * x0 + C ^ 2 := by ring
      have e2 : (sqrt A0 + C) ^ 2 = A0 + 2 * C * sqrt A0 + C ^ 2 := by
        rw [add_sq, sq_sqrt hA00]; ring
      have h4 := mul_le_mul_of_nonneg_left hx0le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0)
      rw [e, e2, hx0sq]; nlinarith
    refine le_trans h2 (le_trans (mul_le_mul_of_nonneg_left h3 (by positivity)) (le_of_eq ?_))
    have e4 : (2 : ℝ) ^ (B + 2) = 2 * 2 ^ (B + 1) := by rw [pow_succ]; ring
    have e5 : (2 : ℝ) ^ (B + 1) = 2 * 2 ^ B := by rw [pow_succ]; ring
    rw [e4, e5]; ring
  have epow : (1 + |(t : ℝ)|) ^ (2 ^ B) = exp (2 ^ B * T) := by
    have : (2 : ℝ) ^ B * T = ((2 ^ B : ℕ) : ℝ) * T := by push_cast; ring
    rw [this, exp_nat_mul, hT, exp_log ht0]
  calc |(k : ℝ)| ≤ 8 * (X : ℝ) := h1
    _ ≤ 8 * (2 * exp H * (64 * exp Λ)) := by linarith
    _ = 1024 * exp (H + Λ) := by rw [exp_add]; ring
    _ ≤ 1024 * exp (H + (2 ^ (B + 1) * (sqrt A0 + C) ^ 2 + 2 ^ B * T
          + 2 ^ (B + 2) * C / sqrt 2 * sqrt T)) := by
        refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
        linarith
    _ = _ := by
        rw [epow]
        simp only [exp_add]
        ring

end TwoPrimesAdaptive
