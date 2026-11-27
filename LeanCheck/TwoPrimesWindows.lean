import LeanCheck.TwoPrimesEffective

/-!
# Witnesses from a density of differences: one budget for both bases, narrower windows

This sharpens `TwoPrimesEffective.witness_of_density`.

* `rigidity_joint`: it is enough that the **product** of the two digit products at `θ` has modulus
  at least `η`.  The visible levels of both bases together are then at most `⌊24 D² log(1/η)⌋`, so
  one common budget of windows suffices; and the windows may have ratio `3/2` instead of `2`.
* `witness_of_density_sharp`: the height `exp(4^(2B+1) A₀)` is replaced by `exp((9/4)^(B+1) A₀)`,
  with the same `B = ⌊12 D² log(50K)⌋`, the same witness radius and the same bound `|k| ≤ 8X`.
  The price is `2500 log` (base) `≤ A₀` and targets `|t| ≤ exp(2 A₀)`.

One budget for all bases is also used, with windows of ratio `m + 1`, in `ThreePrimesDensityM13`.
Its use here and the narrower windows were proposed by ChatGPT.
-/

namespace TwoPrimesWindows

open Finset Real TwoPrimesEffective

/-- First level of the window `k`. -/
noncomputable def lo' (p : ℕ) (A0 : ℝ) (k : ℕ) : ℕ := ⌈(3 / 2 : ℝ) ^ k * sqrt (A0 / log p)⌉₊

/-- Last level of the window `k`. -/
noncomputable def hi' (p : ℕ) (A0 : ℝ) (k : ℕ) : ℕ := ⌊(3 / 2 : ℝ) ^ (k + 1) * sqrt (A0 / log p)⌋₊

/-- Facts about the levels of one window. -/
lemma window' {p : ℕ} (hp : 2 ≤ p) {A0 : ℝ} (h : 2500 * log p ≤ A0) (k : ℕ) :
    lo' p A0 k ≤ hi' p A0 k ∧ hi' p A0 k ≤ lo' p A0 (k + 1) ∧
    ((lo' p A0 k : ℝ) ^ 2) * log p ≤ 2601 / 2500 * ((9 / 4) ^ k * A0) ∧
    1369 / 625 * ((9 / 4) ^ k * A0) ≤ ((hi' p A0 k : ℝ) ^ 2) * log p ∧
    ((hi' p A0 k : ℝ) ^ 2) * log p ≤ (9 / 4) ^ (k + 1) * A0 := by
  have hl := log_pos' hp
  have hA : 0 ≤ A0 := le_trans (by positivity) h
  set s0 := sqrt (A0 / log p) with hs0
  have h50 : 50 ≤ s0 := by
    have : (50 : ℝ) ^ 2 ≤ A0 / log p := by
      rw [le_div_iff₀ hl]; linarith
    calc (50 : ℝ) = sqrt (50 ^ 2) := (sqrt_sq (by norm_num)).symm
      _ ≤ _ := sqrt_le_sqrt this
  have h2k : (1 : ℝ) ≤ (3 / 2) ^ k := one_le_pow₀ (by norm_num)
  set s := (3 / 2 : ℝ) ^ k * s0 with hs
  have hs50 : 50 ≤ s := le_trans h50 (le_mul_of_one_le_left (by linarith) h2k)
  have hsq : s ^ 2 * log p = (9 / 4) ^ k * A0 := by
    have e : s0 ^ 2 = A0 / log p := sq_sqrt (div_nonneg hA hl.le)
    have e4 : ((3 / 2 : ℝ) ^ k) ^ 2 = (9 / 4) ^ k := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [hs, mul_pow, e, e4]; field_simp
  have hlo1 : s ≤ (lo' p A0 k : ℝ) := Nat.le_ceil _
  have hlo2 : (lo' p A0 k : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith)
  have hs2 : (3 / 2 : ℝ) ^ (k + 1) * s0 = 3 / 2 * s := by rw [hs, pow_succ]; ring
  have hhi1 : (hi' p A0 k : ℝ) ≤ 3 / 2 * s := by
    unfold hi'; rw [← hs0, hs2]; exact Nat.floor_le (by linarith)
  have hhi2 : 3 / 2 * s - 1 < (hi' p A0 k : ℝ) := by
    unfold hi'; rw [← hs0, hs2]; exact Nat.sub_one_lt_floor _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (lo' p A0 k : ℝ) ≤ hi' p A0 k := by linarith
    exact_mod_cast this
  · have h1 : 3 / 2 * s ≤ (lo' p A0 (k + 1) : ℝ) := by
      unfold lo'; rw [← hs0, hs2]; exact Nat.le_ceil _
    have : (hi' p A0 k : ℝ) ≤ lo' p A0 (k + 1) := le_trans hhi1 h1
    exact_mod_cast this
  · have h1 : (lo' p A0 k : ℝ) ≤ 51 / 50 * s := by linarith
    have h2 : (lo' p A0 k : ℝ) ^ 2 ≤ (51 / 50 * s) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
    have := mul_le_mul_of_nonneg_right h2 hl.le
    nlinarith
  · have h1 : 37 / 25 * s ≤ (hi' p A0 k : ℝ) := by linarith
    have h2 : (37 / 25 * s) ^ 2 ≤ (hi' p A0 k : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h1 2
    have := mul_le_mul_of_nonneg_right h2 hl.le
    nlinarith
  · have h2 : (hi' p A0 k : ℝ) ^ 2 ≤ (3 / 2 * s) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hhi1 2
    have := mul_le_mul_of_nonneg_right h2 hl.le
    have e4 : (9 / 4 : ℝ) ^ (k + 1) * A0 = 9 / 4 * ((9 / 4) ^ k * A0) := by ring
    nlinarith

lemma lo'_mono {p : ℕ} {A0 : ℝ} {j k : ℕ} (h : j ≤ k) : lo' p A0 j ≤ lo' p A0 k :=
  Nat.ceil_le_ceil (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) h) (sqrt_nonneg _))

/-- Disjoint windows in increasing order: `S` meets at most `S.card` of them. -/
lemma card_hit (l h : ℕ → ℕ) (hlh : ∀ j k, j < k → h j ≤ l k) (S : Finset ℕ) (K : ℕ) :
    ((Finset.range K).filter (fun k => ∃ n ∈ S, l k ≤ n ∧ n < h k)).card ≤ S.card := by
  classical
  set T := (Finset.range K).filter (fun k => ∃ n ∈ S, l k ≤ n ∧ n < h k) with hT
  have hex : ∀ k ∈ T, ∃ n ∈ S, l k ≤ n ∧ n < h k := by
    intro k hk; rw [hT, mem_filter] at hk; exact hk.2
  choose f hfS hf1 hf2 using hex
  have key : ∀ j k (hj : j ∈ T) (hk : k ∈ T), j < k → f j hj < f k hk := by
    intro j k hj hk hlt
    exact lt_of_lt_of_le (hf2 j hj) (le_trans (hlh j k hlt) (hf1 k hk))
  have hinj : Set.InjOn (fun k : {x // x ∈ T} => f k.1 k.2) (T.attach : Set {x // x ∈ T}) := by
    intro x _ y _ hxy
    rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
    · exact absurd hxy (ne_of_lt (key _ _ x.2 y.2 hlt))
    · exact Subtype.ext heq
    · exact absurd hxy.symm (ne_of_lt (key _ _ y.2 x.2 hgt))
  have := card_le_card_of_injOn (s := T.attach) (t := S)
    (fun k : {x // x ∈ T} => f k.1 k.2) (fun k _ => hfS k.1 k.2) hinj
  rwa [card_attach] at this

/-- The visible levels of both bases together are controlled by the product of the two digit
products. -/
lemma card_marked_joint {p q D Np Nq : ℕ} {θ η : ℝ} (hD : 1 ≤ D) (hη : 0 < η)
    (h : η ≤ |prodDigit p D Np θ| * |prodDigit q D Nq θ|) :
    ((marked p D Np θ).card : ℝ) + ((marked q D Nq θ).card : ℝ) ≤ 24 * D ^ 2 * (-log η) := by
  have h0 : 0 < |prodDigit p D Np θ| * |prodDigit q D Nq θ| := lt_of_lt_of_le hη h
  have h1 : 0 < |prodDigit p D Np θ| := by
    refine lt_of_le_of_ne (abs_nonneg _) (fun e => ?_)
    rw [← e, zero_mul] at h0
    exact lt_irrefl 0 h0
  have h2 : 0 < |prodDigit q D Nq θ| := by
    refine lt_of_le_of_ne (abs_nonneg _) (fun e => ?_)
    rw [← e, mul_zero] at h0
    exact lt_irrefl 0 h0
  have c1 := card_marked_le (p := p) (N := Np) (θ := θ) hD h1 le_rfl
  have c2 := card_marked_le (p := q) (N := Nq) (θ := θ) hD h2 le_rfl
  have hlog := log_le_log hη h
  rw [log_mul h1.ne' h2.ne'] at hlog
  have h24 : (0 : ℝ) ≤ 24 * (D : ℝ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (neg_le_neg hlog) h24
  nlinarith

/-- **Rigidity, joint form.** If the product of the two digit products at `θ` has modulus at least
`η`, then `θ` is extremely close to an integer. -/
theorem rigidity_joint {p q D B Np Nq : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) {η A0 θ : ℝ} (hη : 0 < η) (hB : 24 * (D : ℝ) ^ 2 * (-log η) < B + 1)
    (hAp : 2500 * log p ≤ A0) (hAq : 2500 * log q ≤ A0)
    (hDp : log (2 * D) ^ 2 ≤ 4 * log p * A0) (hDq : log (2 * D) ^ 2 ≤ 4 * log q * A0)
    (hNp : hi' p A0 B ≤ Np) (hNq : hi' q A0 B ≤ Nq)
    (h12 : η ≤ |prodDigit p D Np θ| * |prodDigit q D Nq θ|) :
    ∃ z : ℤ, |θ - z| ≤ exp (-(219 / 100) * A0) / 2 := by
  classical
  have hA : 0 ≤ A0 := le_trans (mul_nonneg (by norm_num) (log_pos' hp).le) hAp
  have hAp1 : 100 * log p ≤ A0 := by
    have := log_pos' hp; linarith
  have hAq1 : 100 * log q ≤ A0 := by
    have := log_pos' hq; linarith
  set Mp := marked p D Np θ with hMp
  set Mq := marked q D Nq θ with hMq
  have hsum : Mp.card + Mq.card ≤ B := by
    have h := lt_of_le_of_lt (card_marked_joint hD hη h12) hB
    have : Mp.card + Mq.card < B + 1 := by exact_mod_cast h
    omega
  have hord : ∀ r : ℕ, 2 ≤ r → 2500 * log r ≤ A0 → ∀ j k, j < k → hi' r A0 j ≤ lo' r A0 k := by
    intro r hr hAr j k hjk
    exact le_trans (window' hr hAr j).2.1 (lo'_mono (show j + 1 ≤ k by omega))
  -- a window without marked levels of either chain
  have hfree : ∃ k ∈ Finset.range (B + 1),
      (¬ ∃ n ∈ Mp, lo' p A0 k ≤ n ∧ n < hi' p A0 k) ∧
      (¬ ∃ n ∈ Mq, lo' q A0 k ≤ n ∧ n < hi' q A0 k) := by
    by_contra hcon
    have hsub : Finset.range (B + 1)
        ⊆ (Finset.range (B + 1)).filter (fun k => ∃ n ∈ Mp, lo' p A0 k ≤ n ∧ n < hi' p A0 k)
          ∪ (Finset.range (B + 1)).filter
              (fun k => ∃ n ∈ Mq, lo' q A0 k ≤ n ∧ n < hi' q A0 k) := by
      intro k hk
      rw [mem_union, mem_filter, mem_filter]
      by_cases hP : ∃ n ∈ Mp, lo' p A0 k ≤ n ∧ n < hi' p A0 k
      · exact Or.inl ⟨hk, hP⟩
      by_cases hQ : ∃ n ∈ Mq, lo' q A0 k ≤ n ∧ n < hi' q A0 k
      · exact Or.inr ⟨hk, hQ⟩
      exact absurd ⟨k, hk, hP, hQ⟩ hcon
    have h3 := le_trans (card_le_card hsub) (card_union_le _ _)
    have h4 := card_hit (lo' p A0) (hi' p A0) (hord p hp hAp) Mp (B + 1)
    have h5 := card_hit (lo' q A0) (hi' q A0) (hord q hq hAq) Mq (B + 1)
    rw [Finset.card_range] at h3
    omega
  obtain ⟨k, hk, hfp, hfq⟩ := hfree
  have hk' : k ≤ B := by rw [Finset.mem_range] at hk; omega
  -- the run for one chain
  have chain : ∀ (r N : ℕ), 2 ≤ r → 2500 * log r ≤ A0 → 100 * log r ≤ A0 →
      log (2 * D) ^ 2 ≤ 4 * log r * A0 →
      hi' r A0 B ≤ N → (¬ ∃ n ∈ marked r D N θ, lo' r A0 k ≤ n ∧ n < hi' r A0 k) →
      ∃ a : ℤ, |θ - a / (r : ℝ) ^ ((lo' r A0 k) ^ 2)|
        ≤ 1 / (2 * (r : ℝ) ^ ((hi' r A0 k) ^ 2)) := by
    intro r N hr hAr hAr1 hDr hN hfr
    have hhiN : hi' r A0 k ≤ N := by
      refine le_trans ?_ hN
      exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by omega)) (sqrt_nonneg _))
    have hJ : ∀ n, lo' r A0 k ≤ n → 1 ≤ range' r D n := by
      intro n hn
      refine range_pos hr hD hAr1 hDr (k := 0) (le_trans ?_ hn)
      have e0 : lo r A0 0 = lo' r A0 0 := by simp [lo, lo']
      rw [e0]
      exact lo'_mono (Nat.zero_le k)
    refine run hD (window' hr hAr k).1 (fun n hn _ => hJ n hn) (fun n hn hlt => ?_) (by omega)
    by_contra hcon
    refine hfr ⟨n, ?_, hn, hlt⟩
    rw [marked, mem_filter, Finset.mem_range]
    exact ⟨lt_of_lt_of_le hlt hhiN, hJ n hn, not_lt.mp hcon⟩
  obtain ⟨a, ha⟩ := chain p Np hp hAp hAp1 hDp hNp hfp
  obtain ⟨a', ha'⟩ := chain q Nq hq hAq hAq1 hDq hNq hfq
  have wp := window' hp hAp k
  have wq := window' hq hAq k
  set A : ℝ := (9 / 4) ^ k * A0 with hAdef
  have hAA0 : A0 ≤ A := le_mul_of_one_le_left hA (one_le_pow₀ (by norm_num))
  have hApos : 0 < A := by
    have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have : log 2 ≤ log (p : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hp)
    linarith
  set P : ℕ := p ^ ((lo' p A0 k) ^ 2) with hP
  set Q : ℕ := q ^ ((lo' q A0 k) ^ 2) with hQ
  have hPr : (p : ℝ) ^ ((lo' p A0 k) ^ 2) = (P : ℝ) := by rw [hP]; push_cast; rfl
  have hQr : (q : ℝ) ^ ((lo' q A0 k) ^ 2) = (Q : ℝ) := by rw [hQ]; push_cast; rfl
  have hPpos : (0 : ℝ) < P := by
    rw [← hPr]; exact pow_pos (by exact_mod_cast (show 0 < p by omega)) _
  have hQpos : (0 : ℝ) < Q := by
    rw [← hQr]; exact pow_pos (by exact_mod_cast (show 0 < q by omega)) _
  have hPle : (P : ℝ) ≤ exp (2601 / 2500 * A) := by
    rw [← hPr, pow_eq_exp hp]; apply exp_le_exp.mpr; push_cast; exact wp.2.2.1
  have hQle : (Q : ℝ) ≤ exp (2601 / 2500 * A) := by
    rw [← hQr, pow_eq_exp hq]; apply exp_le_exp.mpr; push_cast; exact wq.2.2.1
  have hbig : ∀ (r : ℕ), 2 ≤ r →
      1369 / 625 * A ≤ ((hi' r A0 k : ℝ) ^ 2) * log r →
      1 / (2 * (r : ℝ) ^ ((hi' r A0 k) ^ 2)) ≤ exp (-(1369 / 625) * A) / 2 := by
    intro r hr hw
    have h1 : exp (1369 / 625 * A) ≤ (r : ℝ) ^ ((hi' r A0 k) ^ 2) := by
      rw [pow_eq_exp hr]; apply exp_le_exp.mpr; push_cast; exact hw
    have e : exp (-(1369 / 625) * A) / 2 = 1 / (2 * exp (1369 / 625 * A)) := by
      rw [neg_mul, exp_neg]; field_simp
    rw [e]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hε1 : |θ - a / (P : ℝ)| ≤ exp (-(1369 / 625) * A) / 2 := by
    rw [← hPr]; exact le_trans ha (hbig p hp wp.2.2.2.1)
  have hε2 : |θ - a' / (Q : ℝ)| ≤ exp (-(1369 / 625) * A) / 2 := by
    rw [← hQr]; exact le_trans ha' (hbig q hq wq.2.2.2.1)
  have hzero : a * (Q : ℤ) - a' * (P : ℤ) = 0 := by
    have hdiff : |(a : ℝ) / P - a' / Q| ≤ exp (-(1369 / 625) * A) := by
      have t := abs_sub_le ((a : ℝ) / P) θ (a' / Q)
      rw [abs_sub_comm ((a : ℝ) / P) θ] at t
      linarith
    have e : (a : ℝ) / P - a' / Q = ((a * (Q : ℤ) - a' * (P : ℤ) : ℤ) : ℝ) / (P * Q) := by
      push_cast; field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hPpos hQpos), div_le_iff₀ (mul_pos hPpos hQpos)] at hdiff
    have h3 : exp (-(1369 / 625) * A) * (P * Q) < 1 := by
      have h4 : (P : ℝ) * Q ≤ exp (2601 / 2500 * A) * exp (2601 / 2500 * A) :=
        mul_le_mul hPle hQle hQpos.le (exp_pos _).le
      have h5 := mul_le_mul_of_nonneg_left h4 (exp_pos (-(1369 / 625) * A)).le
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

theorem witness_of_density_sharp {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) {K A0 s : ℝ} (hK : 1 ≤ K)
    (hAp : 2500 * log p ≤ A0) (hAq : 2500 * log q ≤ A0)
    (hDp : log (2 * D) ^ 2 ≤ 4 * log p * A0) (hDq : log (2 * D) ^ 2 ≤ 4 * log q * A0)
    {B : ℕ} (hB : B = ⌊12 * (D : ℝ) ^ 2 * log (50 * K)⌋₊)
    {X : ℕ} (hX : exp ((9 / 4) ^ (B + 1) * A0) ≤ X)
    (V : Finset ℤ) (hV : (X : ℝ) ≤ K * V.card) (a b : ℤ → ℤ)
    (hdiff : ∀ v ∈ V, v = a v - b v)
    (haX : ∀ v ∈ V, |a v| ≤ (X : ℤ)) (hbX : ∀ v ∈ V, |b v| ≤ (X : ℤ))
    (ha : ∀ v ∈ V, Small p s (a v)) (hb : ∀ v ∈ V, Small q s (b v))
    (t : ℤ) (ht : |(t : ℝ)| ≤ exp (2 * A0)) :
    ∃ k : ℤ, |k| ≤ 8 * (X : ℤ) ∧ Small p (4 * (s + 1 / D)) k
      ∧ Small q (4 * (s + 1 / D)) (k - t) := by
  classical
  have hA : 0 ≤ A0 := le_trans (mul_nonneg (by norm_num) (log_pos' hp).le) hAp
  have hKpos : (0 : ℝ) < K := by linarith
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (exp_pos _) hX
  have hX1 : (1 : ℝ) ≤ X := by
    have : 0 < X := by exact_mod_cast hXpos
    exact_mod_cast this
  have hVpos : (0 : ℝ) < V.card := by
    by_contra h
    have h0 : (V.card : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [h0, mul_zero] at hV
    linarith
  set Np := hi' p A0 B with hNp
  set Nq := hi' q A0 B with hNq
  -- the digit sets fit below `X`
  have hfit : ∀ r : ℕ, 2 ≤ r → 2500 * log r ≤ A0 → (r : ℝ) ^ ((hi' r A0 B) ^ 2) ≤ X := by
    intro r hr hAr
    refine le_trans ?_ hX
    rw [pow_eq_exp hr]
    apply exp_le_exp.mpr
    push_cast
    exact (window' hr hAr B).2.2.2.2
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
  have hvp : ∀ j ∈ vectors p D Np, |value p j| ≤ (X : ℤ) := by
    intro j hj
    have := le_trans (abs_value_le hp hD hj) (hfit p hp hAp)
    exact_mod_cast this
  have hvq : ∀ j ∈ vectors q D Nq, |value q j| ≤ (X : ℤ) := by
    intro j hj
    have := le_trans (abs_value_le hq hD hj) (hfit q hq hAq)
    exact_mod_cast this
  have hR : ∀ i ∈ I', |g i| ≤ ((4 * X : ℕ) : ℤ) := by
    intro i hi'
    obtain ⟨h1, h2, h3⟩ := hmem i hi'
    have e1 := hdiff _ h1
    have a1 := haX _ h1
    have a2 := hbX _ h1
    have a3 := hvp _ h2
    have a4 := hvq _ h3
    rw [abs_le] at a1 a2 a3 a4
    rw [abs_le]; simp only [hg]; push_cast; omega
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
  have hsupp : ((I' ×ˢ I').image (fun x => g x.1 - g x.2)).card ≤ 16 * X + 1 := by
    have hsub : (I' ×ˢ I').image (fun x => g x.1 - g x.2)
        ⊆ Icc (-(8 * (X : ℤ))) (8 * (X : ℤ)) := by
      intro y hy
      rw [mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [mem_product] at hx
      have a1 := hR _ hx.1
      have a2 := hR _ hx.2
      rw [abs_le] at a1 a2
      push_cast at a1 a2
      rw [mem_Icc]; omega
    refine le_trans (card_le_card hsub) ?_
    rw [Int.card_Icc]; omega
  -- the large values of the exponential sum
  set η : ℝ := sqrt (1 / (50 * K)) with hη
  have hηpos : 0 < η := sqrt_pos.mpr (by positivity)
  have hη2 : η ^ 2 = 1 / (50 * K) := sq_sqrt (by positivity)
  have hlogη : -log η = log (50 * K) / 2 := by
    rw [hη, log_sqrt (by positivity), one_div, log_inv]; ring
  have hBlt : 24 * (D : ℝ) ^ 2 * (-log η) < B + 1 := by
    have h := Nat.lt_floor_add_one (12 * (D : ℝ) ^ 2 * log (50 * K))
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
  have hspec : ∀ θ : ℝ, η * I'.card ≤ ‖S I' g θ‖ → 4 / 5 ≤ Real.cos (2 * π * (t * θ)) := by
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
    obtain ⟨z, hz⟩ := rigidity_joint hp hq hpq hD hηpos hBlt hAp hAq hDp hDq (le_of_eq hNp.symm)
      (le_of_eq hNq.symm) hboth
    set y : ℝ := t * (θ - z) with hy
    have hyabs : |y| ≤ 1 / 10 := by
      rw [hy, abs_mul]
      have h3 := mul_le_mul ht hz (abs_nonneg _) (exp_pos _).le
      refine le_trans h3 ?_
      have e1 : exp (2 * A0) * (exp (-(219 / 100) * A0) / 2) = exp (-(19 / 100) * A0) / 2 := by
        rw [mul_div_assoc', ← exp_add]; congr 2; ring
      rw [e1]
      have h4 : exp (-(19 / 100) * A0) ≤ 1 / 5 := by
        have hl2 : (0.69 : ℝ) < log 2 := lt_trans (by norm_num) log_two_gt_d9
        have hA60 : 1000 ≤ A0 := by
          have : log 2 ≤ log (p : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hp)
          linarith
        rw [neg_mul, exp_neg]
        have h5 : (5 : ℝ) ≤ exp (19 / 100 * A0) :=
          le_trans (by linarith) (add_one_le_exp _)
        rw [one_div]
        exact inv_anti₀ (by norm_num) h5
      linarith
    have hcos : Real.cos (2 * π * (t * θ)) = Real.cos (2 * π * y) := by
      have : 2 * π * ((t : ℝ) * θ) = 2 * π * y + ((t * z : ℤ) : ℝ) * (2 * π) := by
        rw [hy]; push_cast; ring
      rw [this, Real.cos_add_int_mul_two_pi]
    rw [hcos]
    refine le_trans ?_ (Real.one_sub_sq_div_two_le_cos)
    have h6 : |2 * π * y| ≤ 0.63 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have := mul_le_mul_of_nonneg_left hyabs (show (0 : ℝ) ≤ 2 * π by positivity)
      have hpi : π < 3.15 := pi_lt_d2
      linarith
    have h7 : (2 * π * y) ^ 2 ≤ 0.63 ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h6 2
    linarith [show (0.63 : ℝ) ^ 2 ≤ 0.4 by norm_num]
  have hnum : 2 * η ^ 2 * (1 / (V.card : ℝ)) < (4 / 5) / ((16 * X + 1 : ℕ) : ℝ) := by
    rw [hη2]
    have h1 : 1 / (V.card : ℝ) ≤ K / X := by
      rw [div_le_div_iff₀ hVpos hXpos]; linarith
    have h2 : 2 * (1 / (50 * K)) * (1 / (V.card : ℝ)) ≤ 2 * (1 / (50 * K)) * (K / X) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * (1 / (50 * K)) * (K / X) = 1 / (25 * X) := by field_simp; ring
    refine lt_of_le_of_lt (le_trans h2 (le_of_eq h3)) ?_
    push_cast
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  obtain ⟨i1, m1, i2, m2, i3, m3, i4, m4, hsum⟩ :=
    exists_four I' g t (4 * X) (16 * X + 1) η (1 / V.card) hIne hR hcoll hsupp hspec hnum
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

end TwoPrimesWindows
