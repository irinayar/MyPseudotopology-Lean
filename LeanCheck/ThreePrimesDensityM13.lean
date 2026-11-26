import LeanCheck.TwoPrimesEffective

/-!
# ThreePrimesDensityM13: witnesses and diagonal density from a sparse set of shifts

`m + 1` prime-square chains with pairwise coprime bases `p 0, …, p m`; chain `0` is the anchor and
chain `i.succ` receives the shift `w i`.  `Small p s k` says that `k` is within `s` of `0` at every
level of the base `p`.

* `witness_of_density_M13`: if at one height `X ≥ exp ((m+1)^(2(V+1)) A₀)`, where
  `V = ⌊12 D² log (5·17^m·K)⌋`, at least `X^m / K` shifts `w` are reached with witnesses `|u| ≤ X`
  and errors `< r`, then every small target `t` has a witness `|k| ≤ 8X` with errors
  `< 4 (r + 1/D)`.  The radius does not depend on the density; only the height does.
* `diagonal_of_sparse_M13`: if for every `D` such sets exist at arbitrarily large heights with
  `K ≤ (log X)^γ`, `γ · 24 D² log (m+1) < 1`, then the diagonal is dense: all integer targets are
  approximated simultaneously.

The existence of the sets is a hypothesis.  The digit products, the one-chain lemmas and the
four-copies positivity are those of `TwoPrimesEffective`; the several targets are encoded as one
integer in base `M`.
-/

namespace ThreePrimesDensityM13

open Finset Real TwoPrimesEffective

/-! ## Windows with ratio `ρ` -/

noncomputable def loM (ρ p : ℕ) (A0 : ℝ) (k : ℕ) : ℕ := ⌈(ρ : ℝ) ^ k * sqrt (A0 / log p)⌉₊

noncomputable def hiM (ρ p : ℕ) (A0 : ℝ) (k : ℕ) : ℕ := ⌊(ρ : ℝ) ^ (k + 1) * sqrt (A0 / log p)⌋₊

lemma windowM13 {ρ p : ℕ} (hρ : 2 ≤ ρ) (hp : 2 ≤ p) {A0 : ℝ} (h : 100 * log p ≤ A0) (k : ℕ) :
    loM ρ p A0 k ≤ hiM ρ p A0 k ∧ hiM ρ p A0 k ≤ loM ρ p A0 (k + 1) ∧
    ((loM ρ p A0 k : ℝ) ^ 2) * log p ≤ 121 / 100 * ((ρ : ℝ) ^ (2 * k) * A0) ∧
    ((ρ : ℝ) - 1 / 10) ^ 2 * ((ρ : ℝ) ^ (2 * k) * A0) ≤ ((hiM ρ p A0 k : ℝ) ^ 2) * log p ∧
    ((hiM ρ p A0 k : ℝ) ^ 2) * log p ≤ (ρ : ℝ) ^ (2 * (k + 1)) * A0 := by
  have hl := log_pos' hp
  have hA : 0 ≤ A0 := le_trans (by positivity) h
  have hρ' : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ
  set s0 := sqrt (A0 / log p) with hs0
  have h10 : 10 ≤ s0 := ten_le_sqrt hp h
  have h1ρ : (1 : ℝ) ≤ (ρ : ℝ) ^ k := one_le_pow₀ (by linarith)
  set s := (ρ : ℝ) ^ k * s0 with hs
  have hs10 : 10 ≤ s := le_trans h10 (le_mul_of_one_le_left (by linarith) h1ρ)
  have hsq : s ^ 2 * log p = (ρ : ℝ) ^ (2 * k) * A0 := by
    have e : s0 ^ 2 = A0 / log p := sq_sqrt (div_nonneg hA hl.le)
    have e4 : ((ρ : ℝ) ^ k) ^ 2 = (ρ : ℝ) ^ (2 * k) := by rw [← pow_mul, mul_comm]
    rw [hs, mul_pow, e, e4]; field_simp
  have hlo1 : s ≤ (loM ρ p A0 k : ℝ) := Nat.le_ceil _
  have hlo2 : (loM ρ p A0 k : ℝ) < s + 1 := Nat.ceil_lt_add_one (by linarith)
  have hs2 : (ρ : ℝ) ^ (k + 1) * s0 = ρ * s := by rw [hs, pow_succ]; ring
  have hhi1 : (hiM ρ p A0 k : ℝ) ≤ ρ * s := by
    unfold hiM; rw [← hs0, hs2]; exact Nat.floor_le (by positivity)
  have hhi2 : (ρ : ℝ) * s - 1 < (hiM ρ p A0 k : ℝ) := by
    unfold hiM; rw [← hs0, hs2]; exact Nat.sub_one_lt_floor _
  have hlow : ((ρ : ℝ) - 1 / 10) * s ≤ (hiM ρ p A0 k : ℝ) := by
    have e : ((ρ : ℝ) - 1 / 10) * s = ρ * s - s / 10 := by ring
    rw [e]; linarith
  have hlow0 : 0 ≤ ((ρ : ℝ) - 1 / 10) * s := mul_nonneg (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h2s : 2 * s ≤ (ρ : ℝ) * s := mul_le_mul_of_nonneg_right hρ' (by linarith)
    have : (loM ρ p A0 k : ℝ) ≤ hiM ρ p A0 k := by linarith
    exact_mod_cast this
  · have h1 : (ρ : ℝ) * s ≤ (loM ρ p A0 (k + 1) : ℝ) := by
      unfold loM; rw [← hs0, hs2]; exact Nat.le_ceil _
    have : (hiM ρ p A0 k : ℝ) ≤ loM ρ p A0 (k + 1) := le_trans hhi1 h1
    exact_mod_cast this
  · have h1 : (loM ρ p A0 k : ℝ) ≤ 11 / 10 * s := by linarith
    have h2 : (loM ρ p A0 k : ℝ) ^ 2 ≤ (11 / 10 * s) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
    have h3 := mul_le_mul_of_nonneg_right h2 hl.le
    have e : (11 / 10 * s) ^ 2 * log p = 121 / 100 * ((ρ : ℝ) ^ (2 * k) * A0) := by
      rw [← hsq]; ring
    linarith
  · have h2 : (((ρ : ℝ) - 1 / 10) * s) ^ 2 ≤ (hiM ρ p A0 k : ℝ) ^ 2 :=
      pow_le_pow_left₀ hlow0 hlow 2
    have h3 := mul_le_mul_of_nonneg_right h2 hl.le
    have e : (((ρ : ℝ) - 1 / 10) * s) ^ 2 * log p
        = ((ρ : ℝ) - 1 / 10) ^ 2 * ((ρ : ℝ) ^ (2 * k) * A0) := by
      rw [← hsq]; ring
    linarith
  · have h2 : (hiM ρ p A0 k : ℝ) ^ 2 ≤ (ρ * s) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hhi1 2
    have h3 := mul_le_mul_of_nonneg_right h2 hl.le
    have e : ((ρ : ℝ) * s) ^ 2 * log p = (ρ : ℝ) ^ (2 * (k + 1)) * A0 := by
      have e2 : (ρ : ℝ) ^ (2 * (k + 1)) = (ρ : ℝ) ^ 2 * (ρ : ℝ) ^ (2 * k) := by
        rw [← pow_add]; congr 1; ring
      rw [e2, mul_assoc, ← hsq]; ring
    linarith

lemma loM_mono {ρ p : ℕ} (hρ : 2 ≤ ρ) {A0 : ℝ} {j k : ℕ} (h : j ≤ k) :
    loM ρ p A0 j ≤ loM ρ p A0 k :=
  Nat.ceil_le_ceil (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ ρ by omega)) h) (sqrt_nonneg _))

lemma range_posM13 {ρ p D : ℕ} (hρ : 2 ≤ ρ) (hp : 2 ≤ p) (hD : 1 ≤ D) {A0 : ℝ}
    (h : 100 * log p ≤ A0) (hD2 : log (2 * D) ^ 2 ≤ 4 * log p * A0) {k n : ℕ}
    (hn : loM ρ p A0 k ≤ n) : 1 ≤ range' p D n := by
  have hl := log_pos' hp
  have hA : 0 ≤ A0 := le_trans (by positivity) h
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h0 : sqrt (A0 / log p) ≤ (n : ℝ) := by
    have h1 : sqrt (A0 / log p) ≤ (loM ρ p A0 0 : ℝ) := by
      unfold loM; simp only [pow_zero, one_mul]; exact Nat.le_ceil _
    have h2 : loM ρ p A0 0 ≤ n := le_trans (loM_mono hρ (Nat.zero_le k)) hn
    exact le_trans h1 (by exact_mod_cast h2)
  have h1 : A0 ≤ (n : ℝ) ^ 2 * log p := by
    have := pow_le_pow_left₀ (sqrt_nonneg _) h0 2
    rw [sq_sqrt (div_nonneg hA hl.le), div_le_iff₀ hl] at this
    exact this
  have h2 : log (2 * D) ≤ 2 * n * log p := by
    have h3 : log (2 * (D : ℝ)) ^ 2 ≤ (2 * n * log p) ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 4 * log p by positivity)
      nlinarith
    have h4 : 0 ≤ log (2 * (D : ℝ)) := log_nonneg (by linarith)
    exact (pow_le_pow_iff_left₀ h4 (by positivity) two_ne_zero).mp h3
  have h5 : (2 * D : ℝ) ≤ (p : ℝ) ^ (2 * n + 1) := by
    rw [pow_eq_exp hp, ← exp_log (show (0 : ℝ) < 2 * D by positivity)]
    apply exp_le_exp.mpr
    push_cast
    nlinarith
  have h6 : 2 * D ≤ p ^ (2 * n + 1) := by exact_mod_cast h5
  exact (Nat.one_le_div_iff (by omega)).mpr h6

lemma card_badM13 {ρ p : ℕ} (hρ : 2 ≤ ρ) {A0 : ℝ} (hp : 2 ≤ p) (h : 100 * log p ≤ A0)
    (S : Finset ℕ) (K : ℕ) :
    ((Finset.range K).filter (fun k => ∃ n ∈ S, loM ρ p A0 k ≤ n ∧ n < hiM ρ p A0 k)).card
      ≤ S.card := by
  classical
  set T := (Finset.range K).filter (fun k => ∃ n ∈ S, loM ρ p A0 k ≤ n ∧ n < hiM ρ p A0 k) with hT
  have hex : ∀ k ∈ T, ∃ n ∈ S, loM ρ p A0 k ≤ n ∧ n < hiM ρ p A0 k := by
    intro k hk; rw [hT, mem_filter] at hk; exact hk.2
  choose f hfS hf1 hf2 using hex
  have key : ∀ j k (hj : j ∈ T) (hk : k ∈ T), j < k → f j hj < f k hk := by
    intro j k hj hk hlt
    have h1 : hiM ρ p A0 j ≤ loM ρ p A0 k :=
      le_trans (windowM13 hρ hp h j).2.1 (loM_mono hρ (show j + 1 ≤ k by omega))
    exact lt_of_lt_of_le (hf2 j hj) (le_trans h1 (hf1 k hk))
  have hinj : Set.InjOn (fun k : {x // x ∈ T} => f k.1 k.2) (T.attach : Set {x // x ∈ T}) := by
    intro x _ y _ hxy
    rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
    · exact absurd hxy (ne_of_lt (key _ _ x.2 y.2 hlt))
    · exact Subtype.ext heq
    · exact absurd hxy.symm (ne_of_lt (key _ _ y.2 x.2 hgt))
  have := card_le_card_of_injOn (s := T.attach) (t := S)
    (fun k : {x // x ∈ T} => f k.1 k.2) (fun k _ => hfS k.1 k.2) hinj
  rwa [card_attach] at this

/-! ## Joint count of the marked levels and rigidity -/

lemma abs_prodDigit_le_one (p D N : ℕ) (θ : ℝ) : |prodDigit p D N θ| ≤ 1 := by
  unfold prodDigit
  rw [abs_prod]
  exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_digit_le_one _ _)

/-- The marked levels of all chains together are bounded by one common count. -/
lemma card_marked_joint {n D : ℕ} (p N : Fin n → ℕ) (θ : Fin n → ℝ) {η : ℝ} (hD : 1 ≤ D)
    (hη : 0 < η) (h : η ≤ ∏ j, |prodDigit (p j) D (N j) (θ j)|) :
    ((∑ j, (marked (p j) D (N j) (θ j)).card : ℕ) : ℝ) ≤ 24 * D ^ 2 * (-log η) := by
  have hpos : ∀ j, 0 < |prodDigit (p j) D (N j) (θ j)| := by
    intro j
    refine lt_of_le_of_ne (abs_nonneg _) (fun h0 => ?_)
    have : (∏ j, |prodDigit (p j) D (N j) (θ j)|) = 0 := prod_eq_zero (mem_univ j) h0.symm
    linarith
  have hone : ∀ j, ((marked (p j) D (N j) (θ j)).card : ℝ)
      ≤ 24 * D ^ 2 * (-log |prodDigit (p j) D (N j) (θ j)|) :=
    fun j => card_marked_le hD (hpos j) le_rfl
  have hlog : log η ≤ ∑ j, log |prodDigit (p j) D (N j) (θ j)| := by
    have := log_le_log hη h
    rwa [log_prod (fun j _ => (hpos j).ne')] at this
  push_cast
  refine le_trans (sum_le_sum (fun j _ => hone j)) ?_
  rw [← mul_sum, sum_neg_distrib]
  exact mul_le_mul_of_nonneg_left (neg_le_neg hlog) (by positivity)

/-- **Rigidity for several chains.** If the product of all digit products is at least `η`, where the
anchor is evaluated at the sum of the other arguments, then every argument is extremely close to an
integer. -/
theorem rigidity_M13 {m D V : ℕ} (hm : 1 ≤ m) (p N : Fin (m + 1) → ℕ) (hp : ∀ j, 2 ≤ p j)
    (hco : ∀ i j, i ≠ j → Nat.Coprime (p i) (p j)) (hD : 1 ≤ D) {η A0 : ℝ}
    (θ : Fin (m + 1) → ℝ) (hθ : θ 0 = ∑ i : Fin m, θ i.succ) (hη : 0 < η)
    (hV : 24 * (D : ℝ) ^ 2 * (-log η) < V + 1)
    (hA : ∀ j, 100 * log (p j) ≤ A0) (hDA : ∀ j, log (2 * D) ^ 2 ≤ 4 * log (p j) * A0)
    (hN : ∀ j, hiM (m + 1) (p j) A0 V ≤ N j)
    (h : η ≤ ∏ j, |prodDigit (p j) D (N j) (θ j)|) (i : Fin m) :
    ∃ z : ℤ, |θ i.succ - z| ≤ exp (-(36 / 10) * A0) / 2 := by
  classical
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℕ, ρ = m + 1 := ⟨_, rfl⟩
  have hN' : ∀ j : Fin (m + 1), hiM ρ (p j) A0 V ≤ N j := by
    intro j; rw [hρdef]; exact hN j
  have hρ : 2 ≤ ρ := by omega
  have hρ' : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hA0 : 0 ≤ A0 := le_trans (mul_nonneg (by norm_num) (log_pos' (hp 0)).le) (hA 0)
  set Mk : Fin (m + 1) → Finset ℕ := fun j => marked (p j) D (N j) (θ j) with hMk
  have htot : (∑ j, (Mk j).card) ≤ V := by
    have h1 := lt_of_le_of_lt (card_marked_joint p N θ hD hη h) hV
    have : (∑ j, (Mk j).card) < V + 1 := by exact_mod_cast h1
    omega
  -- a window without marked levels of any chain
  set bad : Fin (m + 1) → Finset ℕ := fun j => (Finset.range (V + 1)).filter
    (fun k => ∃ n ∈ Mk j, loM ρ (p j) A0 k ≤ n ∧ n < hiM ρ (p j) A0 k) with hbad
  have hfree : ∃ k ∈ Finset.range (V + 1), ∀ j,
      ¬ ∃ n ∈ Mk j, loM ρ (p j) A0 k ≤ n ∧ n < hiM ρ (p j) A0 k := by
    by_contra hcon
    have hsub : Finset.range (V + 1) ⊆ univ.biUnion bad := by
      intro k hk
      by_contra hk'
      refine hcon ⟨k, hk, fun j hj => hk' ?_⟩
      rw [mem_biUnion]
      exact ⟨j, mem_univ j, mem_filter.mpr ⟨hk, hj⟩⟩
    have h3 := le_trans (card_le_card hsub) card_biUnion_le
    have h4 : ∑ j, (bad j).card ≤ ∑ j, (Mk j).card :=
      sum_le_sum (fun j _ => card_badM13 hρ (hp j) (hA j) (Mk j) (V + 1))
    rw [Finset.card_range] at h3
    omega
  obtain ⟨k, hk, hf⟩ := hfree
  have hk' : k ≤ V := by rw [Finset.mem_range] at hk; omega
  have chain : ∀ j, ∃ a : ℤ, |θ j - a / (p j : ℝ) ^ ((loM ρ (p j) A0 k) ^ 2)|
      ≤ 1 / (2 * (p j : ℝ) ^ ((hiM ρ (p j) A0 k) ^ 2)) := by
    intro j
    have hhiN : hiM ρ (p j) A0 k ≤ N j := by
      refine le_trans ?_ (hN' j)
      exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by linarith) (by omega)) (sqrt_nonneg _))
    refine run hD (windowM13 hρ (hp j) (hA j) k).1
      (fun n hn _ => range_posM13 hρ (hp j) hD (hA j) (hDA j) hn)
      (fun n hn hlt => ?_) (by have := hp j; omega)
    by_contra hcon
    refine hf j ⟨n, ?_, hn, hlt⟩
    simp only [hMk, marked, mem_filter, Finset.mem_range]
    exact ⟨lt_of_lt_of_le hlt hhiN, range_posM13 hρ (hp j) hD (hA j) (hDA j) hn,
      not_lt.mp hcon⟩
  choose a ha using chain
  set A : ℝ := (ρ : ℝ) ^ (2 * k) * A0 with hAdef
  have hAA0 : A0 ≤ A := le_mul_of_one_le_left hA0 (one_le_pow₀ (by linarith))
  have hA60 : 60 ≤ A := by
    have h1 : log 2 ≤ log (p 0 : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hp 0)
    have h2 : (0.69 : ℝ) < log 2 := lt_trans (by norm_num) log_two_gt_d9
    have := hA 0
    linarith
  set P : Fin (m + 1) → ℕ := fun j => p j ^ ((loM ρ (p j) A0 k) ^ 2) with hP
  have hPr : ∀ j, (p j : ℝ) ^ ((loM ρ (p j) A0 k) ^ 2) = (P j : ℝ) := by
    intro j; simp only [hP]; push_cast; rfl
  have hPpos : ∀ j, (0 : ℝ) < P j := by
    intro j
    rw [← hPr j]
    exact pow_pos (by exact_mod_cast (show 0 < p j by have := hp j; omega)) _
  have hPle : ∀ j, (P j : ℝ) ≤ exp (121 / 100 * A) := by
    intro j
    rw [← hPr j, pow_eq_exp (hp j)]
    apply exp_le_exp.mpr
    push_cast
    exact (windowM13 hρ (hp j) (hA j) k).2.2.1
  set c : ℝ := ((ρ : ℝ) - 1 / 10) ^ 2 with hc
  have herr : ∀ j, |θ j - a j / (P j : ℝ)| ≤ exp (-c * A) / 2 := by
    intro j
    have h1 : exp (c * A) ≤ (p j : ℝ) ^ ((hiM ρ (p j) A0 k) ^ 2) := by
      rw [pow_eq_exp (hp j)]
      apply exp_le_exp.mpr
      push_cast
      exact (windowM13 hρ (hp j) (hA j) k).2.2.2.1
    have e : exp (-c * A) / 2 = 1 / (2 * exp (c * A)) := by
      rw [neg_mul, exp_neg]; field_simp
    rw [← hPr j, e]
    exact le_trans (ha j) (one_div_le_one_div_of_le (by positivity) (by linarith))
  set Pall : ℝ := ∏ j, (P j : ℝ) with hPall
  have hPallpos : 0 < Pall := prod_pos (fun j _ => hPpos j)
  have hPallle : Pall ≤ exp ((ρ : ℝ) * (121 / 100 * A)) := by
    have h1 : Pall ≤ ∏ _j : Fin (m + 1), exp (121 / 100 * A) :=
      prod_le_prod₀ (fun j _ => (hPpos j).le) (fun j _ => hPle j)
    rw [prod_const, card_univ, Fintype.card_fin, ← exp_nat_mul, ← hρdef] at h1
    exact h1
  -- the integer combination
  set Z : ℤ := a 0 * (∏ i' : Fin m, (P i'.succ : ℤ))
    - ∑ i' : Fin m, a i'.succ * ∏ l ∈ univ.erase i'.succ, (P l : ℤ) with hZ
  have hZr : (Z : ℝ) = Pall * ((a 0 : ℝ) / P 0 - ∑ i' : Fin m, (a i'.succ : ℝ) / P i'.succ) := by
    rw [hZ]
    push_cast
    rw [mul_sub, mul_sum]
    congr 1
    · have e : Pall = (P 0 : ℝ) * ∏ i' : Fin m, (P i'.succ : ℝ) := Fin.prod_univ_succ _
      rw [e]
      have := (hPpos 0).ne'
      field_simp
    · refine sum_congr rfl (fun i' _ => ?_)
      have e : Pall = (P i'.succ : ℝ) * ∏ l ∈ univ.erase i'.succ, (P l : ℝ) :=
        (mul_prod_erase univ (fun l => (P l : ℝ)) (mem_univ i'.succ)).symm
      rw [e]
      have := (hPpos i'.succ).ne'
      field_simp
  have hcomb : |(a 0 : ℝ) / P 0 - ∑ i' : Fin m, (a i'.succ : ℝ) / P i'.succ|
      ≤ (ρ : ℝ) * (exp (-c * A) / 2) := by
    have e : (a 0 : ℝ) / P 0 - ∑ i' : Fin m, (a i'.succ : ℝ) / P i'.succ
        = -(θ 0 - a 0 / P 0) + ∑ i' : Fin m, (θ i'.succ - a i'.succ / P i'.succ) := by
      rw [sum_sub_distrib, ← hθ]; ring
    rw [e]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_neg]
    have h1 : |∑ i' : Fin m, (θ i'.succ - a i'.succ / P i'.succ)|
        ≤ (m : ℝ) * (exp (-c * A) / 2) := by
      refine le_trans (abs_sum_le_sum_abs _ _) ?_
      refine le_trans (sum_le_sum (fun i' _ => herr i'.succ)) (le_of_eq ?_)
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e2 : (ρ : ℝ) * (exp (-c * A) / 2) = exp (-c * A) / 2 + (m : ℝ) * (exp (-c * A) / 2) := by
      rw [hρdef]; push_cast; ring
    rw [e2]
    exact add_le_add (herr 0) h1
  have hZ0 : Z = 0 := by
    have h1 : |(Z : ℝ)| < 1 := by
      rw [hZr, abs_mul, abs_of_pos hPallpos]
      have h2 := mul_le_mul hPallle hcomb (abs_nonneg _) (exp_pos _).le
      refine lt_of_le_of_lt h2 ?_
      have e : exp ((ρ : ℝ) * (121 / 100 * A)) * ((ρ : ℝ) * (exp (-c * A) / 2))
          = (ρ : ℝ) / 2 * exp ((ρ : ℝ) * (121 / 100 * A) + -c * A) := by
        rw [exp_add]; ring
      rw [e]
      have h3 : (ρ : ℝ) * (121 / 100 * A) + -c * A ≤ -(ρ : ℝ) := by
        have h4 : (ρ : ℝ) * (121 / 100) - c ≤ -(ρ : ℝ) / 2 := by
          rw [hc]; nlinarith
        have h5 := mul_le_mul_of_nonneg_right h4 (show (0 : ℝ) ≤ A by linarith)
        have h6 : (ρ : ℝ) * 60 ≤ (ρ : ℝ) * A := mul_le_mul_of_nonneg_left hA60 (by linarith)
        nlinarith
      have h7 : (ρ : ℝ) / 2 * exp ((ρ : ℝ) * (121 / 100 * A) + -c * A)
          ≤ (ρ : ℝ) / 2 * exp (-(ρ : ℝ)) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr h3) (by positivity)
      refine lt_of_le_of_lt h7 ?_
      rw [exp_neg, ← div_eq_mul_inv, div_lt_one (exp_pos _)]
      have := add_one_le_exp (ρ : ℝ)
      linarith
    have h8 : |Z| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.mp h8
  have hdvd : (P i.succ : ℤ) ∣ a i.succ := by
    have hsum : a 0 * (∏ i' : Fin m, (P i'.succ : ℤ))
        = ∑ i' : Fin m, a i'.succ * ∏ l ∈ univ.erase i'.succ, (P l : ℤ) := by
      have := hZ0; rw [hZ] at this; omega
    have hL : (P i.succ : ℤ) ∣ a 0 * (∏ i' : Fin m, (P i'.succ : ℤ)) :=
      Dvd.dvd.mul_left (dvd_prod_of_mem (fun i' : Fin m => (P i'.succ : ℤ)) (mem_univ i)) _
    rw [hsum, ← add_sum_erase univ _ (mem_univ i)] at hL
    have hrest : (P i.succ : ℤ) ∣ ∑ i' ∈ univ.erase i,
        a i'.succ * ∏ l ∈ univ.erase i'.succ, (P l : ℤ) := by
      refine dvd_sum (fun i' hi' => Dvd.dvd.mul_left ?_ _)
      refine dvd_prod_of_mem (fun l => (P l : ℤ)) (mem_erase.mpr ⟨?_, mem_univ _⟩)
      intro e
      exact (mem_erase.mp hi').1 (Fin.succ_injective _ e).symm
    have hterm := (dvd_add_left hrest).mp hL
    have hcop : IsCoprime (P i.succ : ℤ) (∏ l ∈ univ.erase i.succ, (P l : ℤ)) := by
      have h1 : Nat.Coprime (P i.succ) (∏ l ∈ univ.erase i.succ, P l) := by
        refine Nat.Coprime.prod_right (fun l hl => ?_)
        exact Nat.Coprime.pow _ _ (hco _ _ (mem_erase.mp hl).1.symm)
      have h2 := Nat.Coprime.isCoprime h1
      push_cast at h2
      exact h2
    exact hcop.dvd_of_dvd_mul_right hterm
  obtain ⟨z, hz⟩ := hdvd
  refine ⟨z, ?_⟩
  have e : (a i.succ : ℝ) / P i.succ = z := by
    have := (hPpos i.succ).ne'
    rw [hz]; push_cast; field_simp
  have h1 := herr i.succ
  rw [e] at h1
  refine le_trans h1 (div_le_div_of_nonneg_right (exp_le_exp.mpr ?_) (by norm_num))
  have hc36 : 36 / 10 ≤ c := by rw [hc]; nlinarith
  have h2 := mul_le_mul hc36 hAA0 hA0 (le_trans (by norm_num) hc36)
  linarith

/-! ## Several targets as one integer -/

/-- The vector `v` read as digits in base `M`. -/
def enc (M : ℤ) {m : ℕ} (v : Fin m → ℤ) : ℤ := ∑ i : Fin m, v i * M ^ (i : ℕ)

lemma enc_sub (M : ℤ) {m : ℕ} (v w : Fin m → ℤ) : enc M (v - w) = enc M v - enc M w := by
  unfold enc
  rw [← sum_sub_distrib]
  exact sum_congr rfl (fun i _ => by rw [Pi.sub_apply, sub_mul])

lemma enc_add (M : ℤ) {m : ℕ} (v w : Fin m → ℤ) : enc M (v + w) = enc M v + enc M w := by
  unfold enc
  rw [← sum_add_distrib]
  exact sum_congr rfl (fun i _ => by rw [Pi.add_apply, add_mul])

lemma enc_eq_zero {M : ℤ} : ∀ {m : ℕ} (v : Fin m → ℤ), (∀ i, |v i| < M) → enc M v = 0 → v = 0 := by
  intro m
  induction m with
  | zero => intro v _ _; funext i; exact i.elim0
  | succ m ih =>
    intro v hv h
    have hM : 0 < M := lt_of_le_of_lt (abs_nonneg _) (hv 0)
    have e : enc M v = v 0 + M * enc M (fun i : Fin m => v i.succ) := by
      unfold enc
      rw [Fin.sum_univ_succ, mul_sum]
      congr 1
      · simp
      · refine sum_congr rfl (fun i _ => ?_)
        rw [Fin.val_succ, pow_succ]; ring
    rw [e] at h
    have h0 : v 0 = 0 := by
      have hd : M ∣ v 0 :=
        ⟨-enc M (fun i : Fin m => v i.succ), by rw [mul_neg]; omega⟩
      exact Int.eq_zero_of_abs_lt_dvd hd (hv 0)
    have ht : enc M (fun i : Fin m => v i.succ) = 0 := by
      rw [h0, zero_add] at h
      rcases mul_eq_zero.mp h with h1 | h1
      · omega
      · exact h1
    have := ih (fun i : Fin m => v i.succ) (fun i => hv i.succ) ht
    funext i
    refine Fin.cases h0 (fun j => ?_) i
    exact congrFun this j

/-! ## The theorem -/

/-- **Witnesses from a sparse set of shifts**, for `m + 1` chains. -/
theorem witness_of_density_M13 {m D : ℕ} (hm : 1 ≤ m) (p : Fin (m + 1) → ℕ) (hp : ∀ j, 2 ≤ p j)
    (hco : ∀ i j, i ≠ j → Nat.Coprime (p i) (p j)) (hD : 1 ≤ D) {K A0 r : ℝ} (hK : 1 ≤ K)
    (hA : ∀ j, 100 * log (p j) ≤ A0) (hDA : ∀ j, log (2 * D) ^ 2 ≤ 4 * log (p j) * A0)
    {V : ℕ} (hV : V = ⌊12 * (D : ℝ) ^ 2 * log (5 * 17 ^ m * K)⌋₊)
    {X : ℕ} (hX : exp (((m + 1 : ℕ) : ℝ) ^ (2 * (V + 1)) * A0) ≤ X)
    (W : Finset (Fin m → ℤ)) (hW : (X : ℝ) ^ m ≤ K * W.card)
    (hbox : ∀ w ∈ W, ∀ i, |w i| ≤ 2 * (X : ℤ))
    (u : (Fin m → ℤ) → ℤ) (huX : ∀ w ∈ W, |u w| ≤ (X : ℤ))
    (h0 : ∀ w ∈ W, Small (p 0) r (u w)) (h1 : ∀ w ∈ W, ∀ i : Fin m, Small (p i.succ) r (u w - w i))
    (t : Fin m → ℤ) (ht : ∑ i, |(t i : ℝ)| ≤ exp (3 * A0)) :
    ∃ k : ℤ, |k| ≤ 8 * (X : ℤ) ∧ Small (p 0) (4 * (r + 1 / D)) k
      ∧ ∀ i : Fin m, Small (p i.succ) (4 * (r + 1 / D)) (k - t i) := by
  classical
  have hA0 : 0 ≤ A0 := le_trans (mul_nonneg (by norm_num) (log_pos' (hp 0)).le) (hA 0)
  have hKpos : (0 : ℝ) < K := by linarith
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (exp_pos _) hX
  have hX1 : 1 ≤ X := by
    have : 0 < X := by exact_mod_cast hXpos
    omega
  have hWpos : (0 : ℝ) < W.card := by
    by_contra hcon
    have h00 : (W.card : ℝ) = 0 := le_antisymm (not_lt.mp hcon) (Nat.cast_nonneg _)
    rw [h00, mul_zero] at hW
    exact absurd hW (not_le.mpr (pow_pos hXpos m))
  have hρ : 2 ≤ m + 1 := by omega
  set N : Fin (m + 1) → ℕ := fun j => hiM (m + 1) (p j) A0 V with hNdef
  have hfit : ∀ j, (p j : ℝ) ^ ((N j) ^ 2) ≤ X := by
    intro j
    refine le_trans ?_ hX
    rw [pow_eq_exp (hp j)]
    apply exp_le_exp.mpr
    push_cast
    have := (windowM13 hρ (hp j) (hA j) V).2.2.2.2
    push_cast at this
    exact this
  set Y := Fintype.piFinset (fun j : Fin (m + 1) => vectors (p j) D (N j)) with hY
  set I' := W ×ˢ Y with hI'
  set g : (Fin m → ℤ) × ((j : Fin (m + 1)) → Fin (N j) → ℤ) → (Fin m → ℤ) :=
    fun x l => x.1 l + value (p 0) (x.2 0) - value (p l.succ) (x.2 l.succ) with hg
  set M : ℤ := 16 * (X : ℤ) + 1 + ∑ l : Fin m, |t l| with hM
  have htsum : 0 ≤ ∑ l : Fin m, |t l| := sum_nonneg (fun _ _ => abs_nonneg _)
  have htle : ∀ l, |t l| ≤ ∑ l : Fin m, |t l| :=
    fun l => single_le_sum (f := fun l => |t l|) (fun _ _ => abs_nonneg _) (mem_univ l)
  set G : (Fin m → ℤ) × ((j : Fin (m + 1)) → Fin (N j) → ℤ) → ℤ := fun x => enc M (g x) with hG
  have hYne : Y.Nonempty := by
    rw [hY, Fintype.piFinset_nonempty]
    exact fun j => vectors_nonempty _ _ _
  have hWne : W.Nonempty := card_pos.mp (by exact_mod_cast hWpos)
  have hIne : I'.Nonempty := hWne.product hYne
  have hcard : (I'.card : ℝ) = W.card * Y.card := by rw [hI', card_product]; push_cast; ring
  have hmem : ∀ x ∈ I', x.1 ∈ W ∧ ∀ j, x.2 j ∈ vectors (p j) D (N j) := by
    intro x hx
    rw [hI', mem_product, hY, Fintype.mem_piFinset] at hx
    exact hx
  have hv : ∀ j, ∀ y ∈ vectors (p j) D (N j), |value (p j) y| ≤ (X : ℤ) := by
    intro j y hy
    have := le_trans (abs_value_le (hp j) hD hy) (hfit j)
    exact_mod_cast this
  have hgbox : ∀ x ∈ I', ∀ l, |g x l| ≤ 4 * (X : ℤ) := by
    intro x hx l
    obtain ⟨hw, hy⟩ := hmem x hx
    have a1 := hbox _ hw l
    have a2 := hv 0 _ (hy 0)
    have a3 := hv l.succ _ (hy l.succ)
    rw [abs_le] at a1 a2 a3
    rw [abs_le]; simp only [hg]; omega
  have hdiffbox : ∀ x ∈ I', ∀ y ∈ I', ∀ l, |(g x - g y) l| ≤ 8 * (X : ℤ) := by
    intro x hx y hy l
    have a := hgbox x hx l
    have b := hgbox y hy l
    rw [abs_le] at a b
    rw [abs_le, Pi.sub_apply]; omega
  set R : ℕ := ∑ l : Fin m, 4 * X * M.natAbs ^ (l : ℕ) with hRdef
  have hR : ∀ x ∈ I', |G x| ≤ (R : ℤ) := by
    intro x hx
    simp only [hG, enc]
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    rw [hRdef]
    push_cast
    refine sum_le_sum (fun l _ => ?_)
    rw [abs_mul, abs_pow]
    exact mul_le_mul (hgbox x hx l) le_rfl (by positivity) (by positivity)
  -- collisions
  have hcoll : (((I' ×ˢ I').filter (fun x => G x.1 - G x.2 = 0)).card : ℝ)
      ≤ (1 / W.card) * (I'.card : ℝ) ^ 2 := by
    have c1 : ((I' ×ˢ I').filter (fun x => G x.1 - G x.2 = 0)).card ≤ (I' ×ˢ Y).card := by
      refine card_le_card_of_injOn (fun x => (x.1, x.2.2)) ?_ ?_
      · intro x hx
        rw [mem_coe, mem_filter, mem_product] at hx
        rw [mem_coe, mem_product]
        refine ⟨hx.1.1, ?_⟩
        have := hx.1.2
        rw [hI', mem_product] at this
        exact this.2
      · intro x hx y hy hxy
        rw [mem_coe, mem_filter, mem_product] at hx hy
        simp only [Prod.mk.injEq] at hxy
        obtain ⟨e1, e2⟩ := hxy
        have geq : ∀ z : ((Fin m → ℤ) × ((j : Fin (m + 1)) → Fin (N j) → ℤ))
              × ((Fin m → ℤ) × ((j : Fin (m + 1)) → Fin (N j) → ℤ)),
            z.1 ∈ I' → z.2 ∈ I' → G z.1 - G z.2 = 0 → g z.1 = g z.2 := by
          intro z hz1 hz2 hz
          have h2 : enc M (g z.1 - g z.2) = 0 := by rw [enc_sub]; exact hz
          have h3 := enc_eq_zero (g z.1 - g z.2) (fun l => by
            have := hdiffbox _ hz1 _ hz2 l
            omega) h2
          exact sub_eq_zero.mp h3
        have gx := geq x hx.1.1 hx.1.2 hx.2
        have gy := geq y hy.1.1 hy.1.2 hy.2
        have e4 : g x.2 = g y.2 := by rw [← gx, ← gy, e1]
        have e3 : x.2.1 = y.2.1 := by
          funext l
          have := congrFun e4 l
          simp only [hg, e2] at this
          omega
        exact Prod.ext e1 (Prod.ext e3 e2)
    have c2 : (((I' ×ˢ I').filter (fun x => G x.1 - G x.2 = 0)).card : ℝ)
        ≤ (I'.card : ℝ) * Y.card := by
      rw [card_product I' Y] at c1
      exact_mod_cast c1
    refine le_trans c2 (le_of_eq ?_)
    rw [hcard]; field_simp
  have hsupp : ((I' ×ˢ I').image (fun x => G x.1 - G x.2)).card ≤ (16 * X + 1) ^ m := by
    set Box : Finset (Fin m → ℤ) :=
      Fintype.piFinset (fun _ : Fin m => Icc (-(8 * (X : ℤ))) (8 * (X : ℤ))) with hBox
    have hsub : (I' ×ˢ I').image (fun x => G x.1 - G x.2) ⊆ Box.image (enc M) := by
      intro y hy
      rw [mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [mem_product] at hx
      rw [mem_image]
      refine ⟨g x.1 - g x.2, ?_, enc_sub _ _ _⟩
      rw [hBox, Fintype.mem_piFinset]
      intro l
      have := hdiffbox _ hx.1 _ hx.2 l
      rw [abs_le] at this
      exact mem_Icc.mpr this
    refine le_trans (card_le_card hsub) (le_trans card_image_le (le_of_eq ?_))
    have hc : (Icc (-(8 * (X : ℤ))) (8 * (X : ℤ))).card = 16 * X + 1 := by
      rw [Int.card_Icc]; omega
    rw [hBox, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, hc]
  -- the large values of the exponential sum
  set η : ℝ := sqrt (1 / (5 * 17 ^ m * K)) with hη
  have hbase : (0 : ℝ) < 5 * 17 ^ m * K := by positivity
  have hηpos : 0 < η := sqrt_pos.mpr (by positivity)
  have hη2 : η ^ 2 = 1 / (5 * 17 ^ m * K) := sq_sqrt (by positivity)
  have hlogη : -log η = log (5 * 17 ^ m * K) / 2 := by
    rw [hη, log_sqrt (by positivity), one_div, log_inv]; ring
  have hVlt : 24 * (D : ℝ) ^ 2 * (-log η) < V + 1 := by
    have h := Nat.lt_floor_add_one (12 * (D : ℝ) ^ 2 * log (5 * 17 ^ m * K))
    rw [← hV] at h
    rw [hlogη]
    linarith
  set Θ : ℝ → Fin (m + 1) → ℝ := fun θ =>
    Fin.cons (∑ l : Fin m, (M : ℝ) ^ (l : ℕ) * θ) (fun l : Fin m => (M : ℝ) ^ (l : ℕ) * θ)
    with hΘ
  set φ : ℝ → Fin (m + 1) → ℝ := fun θ =>
    Fin.cons (∑ l : Fin m, (M : ℝ) ^ (l : ℕ) * θ) (fun l : Fin m => -((M : ℝ) ^ (l : ℕ) * θ))
    with hφ
  have hfactor : ∀ θ : ℝ, TwoPrimesEffective.S I' G θ
      = (∑ w ∈ W, e ((enc M w : ℝ) * θ))
        * ∏ j : Fin (m + 1), ∑ y ∈ vectors (p j) D (N j), e ((value (p j) y : ℝ) * φ θ j) := by
    intro θ
    rw [TwoPrimesEffective.S, hI', sum_product, sum_mul]
    refine sum_congr rfl (fun w _ => ?_)
    rw [prod_univ_sum, ← hY, mul_sum]
    refine sum_congr rfl (fun y _ => ?_)
    have hexp : ∀ (n : ℕ) (f : Fin n → ℝ), ∏ j, e (f j) = e (∑ j, f j) := by
      intro n f
      unfold e
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [mul_sum, sum_mul]
    rw [hexp, ← e_add]
    congr 1
    rw [Fin.sum_univ_succ]
    simp only [hφ, Fin.cons_zero, Fin.cons_succ, hG, hg, enc]
    push_cast
    simp only [sum_mul, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl (fun l _ => by ring)
  have heven : ∀ (θ : ℝ) (j : Fin (m + 1)),
      |prodDigit (p j) D (N j) (φ θ j)| = |prodDigit (p j) D (N j) (Θ θ j)| := by
    intro θ j
    refine Fin.cases ?_ (fun l => ?_) j
    · simp only [hφ, hΘ, Fin.cons_zero]
    · simp only [hφ, hΘ, Fin.cons_succ]
      have : prodDigit (p l.succ) D (N l.succ) (-((M : ℝ) ^ (l : ℕ) * θ))
          = prodDigit (p l.succ) D (N l.succ) ((M : ℝ) ^ (l : ℕ) * θ) := by
        unfold prodDigit
        exact prod_congr rfl (fun n _ => by rw [mul_neg, digit_neg])
      rw [this]
  have hspec : ∀ θ : ℝ, η * I'.card ≤ ‖TwoPrimesEffective.S I' G θ‖
      → 4 / 5 ≤ Real.cos (2 * π * ((enc M t : ℤ) * θ)) := by
    intro θ hθ
    have hIpos : (0 : ℝ) < I'.card := by exact_mod_cast card_pos.mpr hIne
    have hWs : ‖∑ w ∈ W, e ((enc M w : ℝ) * θ)‖ ≤ (W.card : ℝ) := by
      refine le_trans (norm_sum_le _ _) ?_
      have : ∀ w ∈ W, ‖e ((enc M w : ℝ) * θ)‖ = 1 := by
        intro w _
        unfold e
        exact Complex.norm_exp_ofReal_mul_I _
      rw [sum_congr rfl this]; simp
    have hprodn : ‖∏ j : Fin (m + 1),
          ∑ y ∈ vectors (p j) D (N j), e ((value (p j) y : ℝ) * φ θ j)‖
        = (Y.card : ℝ) * ∏ j, |prodDigit (p j) D (N j) (Θ θ j)| := by
      rw [norm_prod, hY, Fintype.card_piFinset, Nat.cast_prod, ← prod_mul_distrib]
      refine prod_congr rfl (fun j _ => ?_)
      rw [sum_vectors, Complex.norm_real, Real.norm_eq_abs, abs_mul, Nat.abs_cast, heven]
    have hnorm : ‖TwoPrimesEffective.S I' G θ‖
        ≤ (I'.card : ℝ) * ∏ j, |prodDigit (p j) D (N j) (Θ θ j)| := by
      rw [hfactor, norm_mul, hprodn, hcard, mul_assoc]
      exact mul_le_mul_of_nonneg_right hWs (by positivity)
    have hbig : η ≤ ∏ j, |prodDigit (p j) D (N j) (Θ θ j)| := by
      have := le_trans hθ hnorm
      rw [mul_comm η] at this
      exact le_of_mul_le_mul_left this hIpos
    have hΘ0 : Θ θ 0 = ∑ i : Fin m, Θ θ i.succ := by
      simp only [hΘ, Fin.cons_zero, Fin.cons_succ]
    have hrig : ∀ l : Fin m, ∃ z : ℤ, |(M : ℝ) ^ (l : ℕ) * θ - z|
        ≤ exp (-(36 / 10) * A0) / 2 := by
      intro l
      have := rigidity_M13 hm p N hp hco hD (Θ θ) hΘ0 hηpos hVlt hA hDA (fun j => le_rfl) hbig l
      simpa only [hΘ, Fin.cons_succ] using this
    choose z hz using hrig
    set y : ℝ := ∑ l : Fin m, (t l : ℝ) * ((M : ℝ) ^ (l : ℕ) * θ - z l) with hy
    have hyabs : |y| ≤ 1 / 10 := by
      have h2 : |y| ≤ (∑ l : Fin m, |(t l : ℝ)|) * (exp (-(36 / 10) * A0) / 2) := by
        rw [hy, sum_mul]
        refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum (fun l _ => ?_))
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hz l) (abs_nonneg _)
      have h3 := le_trans h2 (mul_le_mul_of_nonneg_right ht (by positivity))
      refine le_trans h3 ?_
      have e1 : exp (3 * A0) * (exp (-(36 / 10) * A0) / 2) = exp (-(6 / 10) * A0) / 2 := by
        rw [mul_div_assoc', ← exp_add]; congr 2; ring
      rw [e1]
      have h4 : exp (-(6 / 10) * A0) ≤ 1 / 5 := by
        have hl2 : (0.69 : ℝ) < log 2 := lt_trans (by norm_num) log_two_gt_d9
        have hA60 : 60 ≤ A0 := by
          have : log 2 ≤ log (p 0 : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hp 0)
          have := hA 0
          linarith
        rw [neg_mul, exp_neg]
        have h5 : (5 : ℝ) ≤ exp (6 / 10 * A0) :=
          le_trans (by linarith) (add_one_le_exp _)
        rw [one_div]
        exact inv_anti₀ (by norm_num) h5
      linarith
    have hcos : Real.cos (2 * π * ((enc M t : ℤ) * θ)) = Real.cos (2 * π * y) := by
      have e1 : ((enc M t : ℤ) : ℝ) * θ = y + ((∑ l : Fin m, t l * z l : ℤ) : ℝ) := by
        rw [hy, enc]
        push_cast
        rw [sum_mul, ← sum_add_distrib]
        exact sum_congr rfl (fun l _ => by ring)
      have : 2 * π * (((enc M t : ℤ) : ℝ) * θ)
          = 2 * π * y + ((∑ l : Fin m, t l * z l : ℤ) : ℝ) * (2 * π) := by
        rw [e1]; ring
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
  have hnum : 2 * η ^ 2 * (1 / (W.card : ℝ)) < (4 / 5) / (((16 * X + 1) ^ m : ℕ) : ℝ) := by
    rw [hη2]
    have hXm : (0 : ℝ) < (X : ℝ) ^ m := pow_pos hXpos m
    have e1 : 1 / (W.card : ℝ) ≤ K / (X : ℝ) ^ m := by
      rw [div_le_div_iff₀ hWpos hXm, one_mul]; exact hW
    have e2 := mul_le_mul_of_nonneg_left e1
      (show (0 : ℝ) ≤ 2 * (1 / (5 * 17 ^ m * K)) by positivity)
    have e3 : 2 * (1 / (5 * 17 ^ m * K)) * (K / (X : ℝ) ^ m) = (2 / 5) / (17 * (X : ℝ)) ^ m := by
      rw [mul_pow]; field_simp
    refine lt_of_le_of_lt (le_trans e2 (le_of_eq e3)) ?_
    have e4 : (((16 * X + 1) ^ m : ℕ) : ℝ) ≤ (17 * (X : ℝ)) ^ m := by
      push_cast
      refine pow_le_pow_left₀ (by positivity) ?_ m
      have : (1 : ℝ) ≤ X := by exact_mod_cast hX1
      linarith
    have e5 : (0 : ℝ) < (((16 * X + 1) ^ m : ℕ) : ℝ) := by positivity
    have e6 : (0 : ℝ) < (17 * (X : ℝ)) ^ m := by positivity
    rw [div_lt_div_iff₀ e6 e5]
    linarith
  obtain ⟨i1, m1, i2, m2, i3, m3, i4, m4, hsum⟩ :=
    exists_four I' G (enc M t) R ((16 * X + 1) ^ m) η (1 / W.card) hIne hR hcoll hsupp hspec hnum
  have hvec : ∀ l, (g i1 l - g i2 l) + (g i3 l - g i4 l) = t l := by
    have h2 : enc M (((g i1 - g i2) + (g i3 - g i4)) - t) = 0 := by
      rw [enc_sub, enc_add, enc_sub, enc_sub]
      simp only [hG] at hsum
      omega
    have h3 := enc_eq_zero _ (fun l => by
      have a := hdiffbox _ m1 _ m2 l
      have b := hdiffbox _ m3 _ m4 l
      have c := htle l
      rw [Pi.sub_apply] at a b
      rw [abs_le] at a b
      have c' := abs_le.mp c
      have d' := abs_le.mp (le_refl |t l|)
      rw [abs_lt]
      simp only [Pi.sub_apply, Pi.add_apply]
      rcases abs_cases (t l) with ⟨e, _⟩ | ⟨e, _⟩ <;> omega) h2
    intro l
    have := congrFun h3 l
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at this
    omega
  set Pf : (Fin m → ℤ) × ((j : Fin (m + 1)) → Fin (N j) → ℤ) → ℤ :=
    fun x => u x.1 + value (p 0) (x.2 0) with hPf
  set Qf : Fin m → (Fin m → ℤ) × ((j : Fin (m + 1)) → Fin (N j) → ℤ) → ℤ :=
    fun l x => u x.1 - x.1 l + value (p l.succ) (x.2 l.succ) with hQf
  have hPQ : ∀ x l, g x l = Pf x - Qf l x := by
    intro x l
    simp only [hg, hPf, hQf]; ring
  have sP : ∀ x ∈ I', Small (p 0) (r + 1 / D) (Pf x) := fun x hx =>
    (h0 _ (hmem x hx).1).add (small_value (hp 0) hD ((hmem x hx).2 0))
  have sQ : ∀ l, ∀ x ∈ I', Small (p l.succ) (r + 1 / D) (Qf l x) := fun l x hx =>
    (h1 _ (hmem x hx).1 l).add (small_value (hp l.succ) hD ((hmem x hx).2 l.succ))
  have e4 : 4 * (r + 1 / (D : ℝ))
      = ((r + 1 / D) + (r + 1 / D)) + ((r + 1 / D) + (r + 1 / D)) := by ring
  refine ⟨(Pf i1 - Pf i2) + (Pf i3 - Pf i4), ?_, ?_, ?_⟩
  · have bound : ∀ x ∈ I', |Pf x| ≤ 2 * (X : ℤ) := by
      intro x hx
      have a1 := huX _ (hmem x hx).1
      have a2 := hv 0 _ ((hmem x hx).2 0)
      have := abs_add_le (u x.1) (value (p 0) (x.2 0))
      simp only [hPf]; omega
    have b1 := bound _ m1
    have b2 := bound _ m2
    have b3 := bound _ m3
    have b4 := bound _ m4
    rw [abs_le] at b1 b2 b3 b4
    rw [abs_le]; omega
  · rw [e4]
    exact ((sP _ m1).sub (sP _ m2)).add ((sP _ m3).sub (sP _ m4))
  · intro l
    have hk : (Pf i1 - Pf i2) + (Pf i3 - Pf i4) - t l
        = (Qf l i1 - Qf l i2) + (Qf l i3 - Qf l i4) := by
      have h2 := hvec l
      rw [hPQ i1, hPQ i2, hPQ i3, hPQ i4] at h2
      omega
    rw [e4, hk]
    exact ((sQ l _ m1).sub (sQ l _ m2)).add ((sQ l _ m3).sub (sQ l _ m4))

/-! ## Diagonal density -/

/-- **Diagonal density from a sparse set of shifts at arbitrarily large heights.** -/
theorem diagonal_of_sparse_M13 {m : ℕ} (hm : 1 ≤ m) (p : Fin (m + 1) → ℕ) (hp : ∀ j, 2 ≤ p j)
    (hco : ∀ i j, i ≠ j → Nat.Coprime (p i) (p j))
    (H : ∀ D : ℕ, 1 ≤ D → ∃ γ : ℝ, γ * (24 * (D : ℝ) ^ 2 * log ((m + 1 : ℕ) : ℝ)) < 1 ∧
      ∀ X0 : ℕ, ∃ X : ℕ, X0 ≤ X ∧ ∃ (W : Finset (Fin m → ℤ)) (u : (Fin m → ℤ) → ℤ),
        (X : ℝ) ^ m ≤ (log X) ^ γ * W.card ∧ (∀ w ∈ W, ∀ i, |w i| ≤ 2 * (X : ℤ)) ∧
        (∀ w ∈ W, |u w| ≤ (X : ℤ)) ∧ (∀ w ∈ W, Small (p 0) (1 / D) (u w)) ∧
        (∀ w ∈ W, ∀ i : Fin m, Small (p i.succ) (1 / D) (u w - w i)))
    (b : Fin (m + 1) → ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : ℤ, ∀ j, Small (p j) ε (z - b j) := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : ℕ, 8 / ε < D := exists_nat_gt _
  have hDpos : (0 : ℝ) < D := lt_trans (by positivity) hD
  have hD1 : 1 ≤ D := by
    have : 0 < D := by exact_mod_cast hDpos
    omega
  have hrad : 4 * (1 / (D : ℝ) + 1 / D) < ε := by
    have h1 : 8 < (D : ℝ) * ε := by rwa [div_lt_iff₀ hε] at hD
    have e : 4 * (1 / (D : ℝ) + 1 / D) = 8 / D := by ring
    rw [e, div_lt_iff₀ hDpos]; linarith
  obtain ⟨γ0, hγ0, Hs⟩ := H D hD1
  set t : Fin m → ℤ := fun i => b i.succ - b 0 with ht
  set L : ℝ := log ((m + 1 : ℕ) : ℝ) with hL
  have hL0 : 0 < L := log_pos (by exact_mod_cast (show 1 < m + 1 by omega))
  set γ : ℝ := max γ0 0 with hγ
  have hγnn : 0 ≤ γ := le_max_right _ _
  set θ : ℝ := γ * (24 * (D : ℝ) ^ 2 * L) with hθ
  have hθ1 : θ < 1 := by
    rcases le_total γ0 0 with h | h
    · rw [hθ, hγ, max_eq_right h, zero_mul]; exact one_pos
    · rw [hθ, hγ, max_eq_left h]; exact hγ0
  have hlp : ∀ j, 0 < log (p j : ℝ) := fun j => log_pos' (hp j)
  set A0 : ℝ := (∑ j, (100 * log (p j : ℝ) + log (2 * D) ^ 2 / (4 * log (p j : ℝ))))
    + ∑ i, |(t i : ℝ)| with hA0
  have hterm : ∀ j : Fin (m + 1), 0 ≤ 100 * log (p j : ℝ) + log (2 * D) ^ 2 / (4 * log (p j : ℝ)) := by
    intro j
    have := hlp j
    positivity
  have htnn : 0 ≤ ∑ i, |(t i : ℝ)| := sum_nonneg (fun _ _ => abs_nonneg _)
  have hAj : ∀ j, 100 * log (p j : ℝ) + log (2 * D) ^ 2 / (4 * log (p j : ℝ)) ≤ A0 := by
    intro j
    have := single_le_sum
      (f := fun j => 100 * log (p j : ℝ) + log (2 * D) ^ 2 / (4 * log (p j : ℝ)))
      (fun j _ => hterm j) (mem_univ j)
    rw [hA0]; linarith
  have hA : ∀ j, 100 * log (p j : ℝ) ≤ A0 := by
    intro j
    have h1 := hAj j
    have h2 : 0 ≤ log (2 * D) ^ 2 / (4 * log (p j : ℝ)) := by
      have := hlp j
      positivity
    linarith
  have hDA : ∀ j, log (2 * D) ^ 2 ≤ 4 * log (p j : ℝ) * A0 := by
    intro j
    have h1 : log (2 * D) ^ 2 / (4 * log (p j : ℝ)) ≤ A0 := by
      have := hAj j
      have := hlp j
      linarith
    rw [div_le_iff₀ (by have := hlp j; positivity)] at h1
    linarith
  have hApos : 0 < A0 := lt_of_lt_of_le (by have := hlp 0; positivity) (hA 0)
  have htexp : ∑ i, |(t i : ℝ)| ≤ exp (3 * A0) := by
    have h1 : ∑ i, |(t i : ℝ)| ≤ A0 := by
      have : 0 ≤ ∑ j, (100 * log (p j : ℝ) + log (2 * D) ^ 2 / (4 * log (p j : ℝ))) :=
        sum_nonneg (fun j _ => hterm j)
      rw [hA0]; linarith
    have h2 := add_one_le_exp (3 * A0)
    linarith
  set c1 : ℝ := log (5 * 17 ^ m) with hc1
  have hc1nn : 0 ≤ c1 := by
    refine log_nonneg ?_
    have : (1 : ℝ) ≤ 17 ^ m := one_le_pow₀ (by norm_num)
    linarith
  set C : ℝ := exp (2 * L * (12 * (D : ℝ) ^ 2 * c1 + 1)) with hC
  have hCpos : 0 < C := exp_pos _
  set T : ℝ := max 1 ((C * A0) ^ (1 / (1 - θ))) with hT
  obtain ⟨X0, hX0⟩ : ∃ X0 : ℕ, exp T < X0 := exists_nat_gt _
  obtain ⟨X, hXX0, W, u, hW, hbox, huX, h0, h1⟩ := Hs X0
  have hXexp : exp T < X := lt_of_lt_of_le hX0 (by exact_mod_cast hXX0)
  have hXpos : (0 : ℝ) < X := lt_trans (exp_pos _) hXexp
  have hlogX : T < log X := by
    have := log_lt_log (exp_pos _) hXexp
    rwa [log_exp] at this
  have hlog1 : 1 ≤ log X := le_trans (le_max_left _ _) hlogX.le
  have hlogpos : 0 < log (X : ℝ) := by linarith
  set K : ℝ := (log X) ^ γ with hK
  have hK1 : 1 ≤ K := one_le_rpow hlog1 hγnn
  have hWK : (X : ℝ) ^ m ≤ K * W.card := by
    refine le_trans hW (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    exact rpow_le_rpow_of_exponent_le hlog1 (le_max_left _ _)
  set V : ℕ := ⌊12 * (D : ℝ) ^ 2 * log (5 * 17 ^ m * K)⌋₊ with hV
  have hfit : exp (((m + 1 : ℕ) : ℝ) ^ (2 * (V + 1)) * A0) ≤ X := by
    rw [← exp_log hXpos]
    apply exp_le_exp.mpr
    have hKpos : 0 < K := by linarith
    have hlogK : log (5 * 17 ^ m * K) = c1 + γ * log (log X) := by
      rw [log_mul (by positivity) hKpos.ne', hK, log_rpow hlogpos]
    have hVle : (V : ℝ) ≤ 12 * (D : ℝ) ^ 2 * (c1 + γ * log (log X)) := by
      rw [← hlogK, hV]
      refine Nat.floor_le (mul_nonneg (by positivity) (log_nonneg ?_))
      have h17 : (1 : ℝ) ≤ 17 ^ m := one_le_pow₀ (by norm_num)
      have : (1 : ℝ) ≤ 5 * 17 ^ m := by linarith
      exact one_le_mul_of_one_le_of_one_le this hK1
    have hpow : ((m + 1 : ℕ) : ℝ) ^ (2 * (V + 1)) ≤ C * (log X) ^ θ := by
      have e1 : ((m + 1 : ℕ) : ℝ) ^ (2 * (V + 1)) = exp (L * (2 * ((V : ℝ) + 1))) := by
        have hmpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
        have : exp (((2 * (V + 1) : ℕ) : ℝ) * L) = ((m + 1 : ℕ) : ℝ) ^ (2 * (V + 1)) := by
          rw [exp_nat_mul, hL, exp_log hmpos]
        rw [← this]
        congr 1; push_cast; ring
      have e2 : C * (log X) ^ θ
          = exp (2 * L * (12 * (D : ℝ) ^ 2 * c1 + 1) + log (log X) * θ) := by
        rw [hC, rpow_def_of_pos hlogpos, ← exp_add]
      rw [e1, e2]
      apply exp_le_exp.mpr
      have h2 := mul_le_mul_of_nonneg_left hVle (show (0 : ℝ) ≤ 2 * L by positivity)
      rw [hθ]
      nlinarith
    have hfin : C * A0 ≤ (log X) ^ (1 - θ) := by
      have h1θ : 0 < 1 - θ := by linarith
      have hCA : 0 ≤ C * A0 := by positivity
      have h2 : (C * A0) ^ (1 / (1 - θ)) ≤ log X := le_trans (le_max_right _ _) hlogX.le
      have h3 := rpow_le_rpow (rpow_nonneg hCA _) h2 h1θ.le
      rwa [← rpow_mul hCA, one_div_mul_cancel h1θ.ne', rpow_one] at h3
    have hsplit : (log X) ^ θ * (log X) ^ (1 - θ) = log X := by
      rw [← rpow_add hlogpos]
      have : θ + (1 - θ) = 1 := by ring
      rw [this, rpow_one]
    calc ((m + 1 : ℕ) : ℝ) ^ (2 * (V + 1)) * A0
        ≤ C * (log X) ^ θ * A0 := mul_le_mul_of_nonneg_right hpow hApos.le
      _ = (log X) ^ θ * (C * A0) := by ring
      _ ≤ (log X) ^ θ * (log X) ^ (1 - θ) :=
          mul_le_mul_of_nonneg_left hfin (rpow_nonneg hlogpos.le _)
      _ = log X := hsplit
  obtain ⟨k, _, hk0, hk1⟩ := witness_of_density_M13 hm p hp hco hD1 hK1 hA hDA hV hfit W hWK hbox
    u huX h0 h1 t htexp
  refine ⟨k + b 0, fun j => ?_⟩
  have weaken : ∀ (q : ℕ) (x : ℤ), Small q (4 * (1 / (D : ℝ) + 1 / D)) x → Small q ε x :=
    fun q x h n => lt_trans (h n) hrad
  refine Fin.cases ?_ (fun i => ?_) j
  · have : k + b 0 - b 0 = k := by ring
    rw [this]; exact weaken _ _ hk0
  · have : k + b 0 - b i.succ = k - t i := by simp only [ht]; ring
    rw [this]; exact weaken _ _ (hk1 i)

end ThreePrimesDensityM13
