import LeanCheck.TwoPrimesWindows

/-!
# Free heights occur in every bounded interval of log-height

A height is *free* for a set `S` of bases if it is the integer part of a number `Y` such that no
power `l^(n^2)`, `l ∈ S`, `n ≥ 1`, lies in `(Y/8, D Y]`.

* `exists_free`: every `[R, 2 exp(H) R]` with `H = card S * log(8D) + 1` contains a free height,
  once `R` is large (explicitly).
* `witness_of_density_wide`: `TwoPrimesWindows.witness_of_density_sharp` for all targets
  `|t| ≤ exp(2.19 A₀)/5`.
* `witness_of_free_heights`: if every large free height carries a set of differences of relative
  size `1/K`, then every target `t` has a witness of size at most a constant times
  `(1+|t|)^(E/2.19)`, `E = (9/4)^(B+1)`.  The existence of those sets is a hypothesis.

The bounded gap between free heights and the exponent `E/2.19` are due to ChatGPT.
-/

namespace TwoPrimesFreeHeight

open Finset Real MeasureTheory TwoPrimesEffective TwoPrimesWindows

/-- `X` is the integer part of a `Y` with no power `l^(n^2)` in `(Y/8, D Y]`. -/
def Free (S : Finset ℕ) (D X : ℕ) : Prop :=
  ∃ Y : ℝ, 0 < Y ∧ X = ⌊Y⌋₊ ∧ ∀ l ∈ S, ∀ n : ℕ, 1 ≤ n →
    ¬ (Y / 8 < (l : ℝ) ^ (n ^ 2) ∧ (l : ℝ) ^ (n ^ 2) ≤ D * Y)

/-- **Free heights are never far apart.** -/
theorem exists_free (S : Finset ℕ) (hS : ∀ l ∈ S, 2 ≤ l) {D : ℕ} (hD : 1 ≤ D) {β R : ℝ}
    (hβ : 0 < β) (hlog : ∀ l ∈ S, β ≤ log l)
    (hR : 8 * exp (((S.card * log (8 * D) + 1) + log (8 * D)) ^ 2 / (4 * β)) ≤ R) :
    ∃ X : ℕ, R ≤ X ∧ (X : ℝ) ≤ 2 * exp (S.card * log (8 * D) + 1) * R ∧ Free S D X := by
  classical
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  set L : ℝ := log (8 * D) with hL
  set H : ℝ := S.card * L + 1 with hH
  have hLsum : L = log 8 + log D := by
    rw [hL, log_mul (by norm_num) hD0.ne']
  have h8 : 0 < log (8 : ℝ) := log_pos (by norm_num)
  have hlD : 0 ≤ log (D : ℝ) := log_nonneg hD'
  have hL0 : 0 ≤ L := by rw [hLsum]; linarith
  have hH1 : 1 ≤ H := by
    have : (0 : ℝ) ≤ S.card * L := mul_nonneg (Nat.cast_nonneg _) hL0
    linarith
  have hR8 : 8 ≤ R := by
    have h1 : (1 : ℝ) ≤ exp ((H + L) ^ 2 / (4 * β)) := one_le_exp (by positivity)
    nlinarith
  have hR0 : 0 < R := by linarith
  set c : ℝ := log (2 * R) with hc
  -- the centres whose excluded interval can meet `[c, c + H]`
  set P : ℕ → ℕ → Prop := fun l n => 1 ≤ n ∧ c - log 8 < (n : ℝ) ^ 2 * log l ∧
    (n : ℝ) ^ 2 * log l ≤ c + H + log D with hP
  have hcentre : (H + L) ^ 2 / (4 * β) < c - log 8 := by
    have h1 : log (8 * exp ((H + L) ^ 2 / (4 * β))) ≤ log R :=
      log_le_log (by positivity) hR
    rw [log_mul (by norm_num) (exp_pos _).ne', log_exp] at h1
    have h2 : c = log 2 + log R := by rw [hc, log_mul (by norm_num) hR0.ne']
    have h3 : log (8 : ℝ) < log 2 + log 8 := by
      have : 0 < log (2 : ℝ) := log_pos (by norm_num)
      linarith
    have h4 : log (8 : ℝ) = 3 * log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; norm_num
    have : 0 < log (2 : ℝ) := log_pos (by norm_num)
    linarith
  have huniq : ∀ l ∈ S, ∀ n m, P l n → P l m → n < m → False := by
    intro l hl n m hn hm hnm
    have hll : β ≤ log l := hlog l hl
    have hl0 : 0 < log (l : ℝ) := lt_of_lt_of_le hβ hll
    have hm1 : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnm
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h1 : ((n : ℝ) + 1) ^ 2 * log l ≤ (m : ℝ) ^ 2 * log l :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hm1 2) hl0.le
    have h2 : 2 * (n : ℝ) * log l < H + L := by
      have a1 := hn.2.1
      have a2 := hm.2.2
      have e : ((n : ℝ) + 1) ^ 2 * log l
          = (n : ℝ) ^ 2 * log l + 2 * n * log l + log l := by ring
      rw [hLsum]; linarith
    have h3 : (H + L) ^ 2 < (n : ℝ) ^ 2 * log l * (4 * β) := by
      have := lt_trans hcentre hn.2.1
      rwa [div_lt_iff₀ (by positivity)] at this
    have h4 : (n : ℝ) ^ 2 * log l * (4 * β) ≤ (2 * n * log l) ^ 2 := by
      have e : (2 * (n : ℝ) * log l) ^ 2 = (n : ℝ) ^ 2 * log l * (4 * log l) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (sq_nonneg _) hl0.le)
    have h5 : (2 * (n : ℝ) * log l) ^ 2 < (H + L) ^ 2 :=
      pow_lt_pow_left₀ h2 (by positivity) two_ne_zero
    linarith
  have huniq' : ∀ l ∈ S, ∀ n m, P l n → P l m → n = m := by
    intro l hl n m hn hm
    rcases lt_trichotomy n m with h | h | h
    · exact (huniq l hl n m hn hm h).elim
    · exact h
    · exact (huniq l hl m n hm hn h).elim
  set J : ℕ → Set ℝ := fun l => if h : ∃ n, P l n then
    Set.Ico (((Classical.choose h : ℕ) : ℝ) ^ 2 * log l - log D)
      (((Classical.choose h : ℕ) : ℝ) ^ 2 * log l + log 8) else ∅ with hJ
  have hJvol : ∀ l, volume (J l) ≤ ENNReal.ofReal L := by
    intro l
    simp only [hJ]
    split
    · rw [Real.volume_Ico]
      exact ENNReal.ofReal_le_ofReal (by rw [hLsum]; linarith)
    · simp
  have hex : ∃ y ∈ Set.Icc c (c + H), ∀ l ∈ S, y ∉ J l := by
    by_contra hcon
    have hsub : Set.Icc c (c + H) ⊆ ⋃ l ∈ S, J l := by
      intro y hy
      by_contra h
      refine hcon ⟨y, hy, fun l hl hmem => h ?_⟩
      exact Set.mem_biUnion hl hmem
    have h1 : volume (Set.Icc c (c + H)) ≤ ∑ l ∈ S, volume (J l) :=
      le_trans (measure_mono hsub) (measure_biUnion_finset_le S J)
    have h2 : ∑ l ∈ S, volume (J l) ≤ ENNReal.ofReal (S.card * L) := by
      refine le_trans (sum_le_sum (fun l _ => hJvol l)) (le_of_eq ?_)
      rw [sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    have h3 := le_trans h1 h2
    rw [Real.volume_Icc, ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (Nat.cast_nonneg _) hL0)] at h3
    linarith
  obtain ⟨y, hy, hfree⟩ := hex
  have hY1 : 2 * R ≤ exp y := by
    have := exp_le_exp.mpr hy.1
    rwa [hc, exp_log (by positivity)] at this
  have hY2 : exp y ≤ 2 * R * exp H := by
    have := exp_le_exp.mpr hy.2
    rwa [exp_add, hc, exp_log (by positivity)] at this
  refine ⟨⌊exp y⌋₊, ?_, ?_, exp y, exp_pos _, rfl, ?_⟩
  · have := Nat.sub_one_lt_floor (exp y)
    linarith
  · refine le_trans (Nat.floor_le (exp_pos _).le) (le_trans hY2 (le_of_eq ?_))
    ring
  · intro l hl n hn ⟨h1, h2⟩
    have hl2 : 2 ≤ l := hS l hl
    have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
    have hpow : (0 : ℝ) < (l : ℝ) ^ (n ^ 2) := pow_pos hlpos _
    have hlp : log ((l : ℝ) ^ (n ^ 2)) = (n : ℝ) ^ 2 * log l := by
      rw [log_pow]; push_cast; ring
    have a1 : y - log 8 < (n : ℝ) ^ 2 * log l := by
      have := log_lt_log (by positivity) h1
      rwa [log_div (exp_pos _).ne' (by norm_num), log_exp, hlp] at this
    have a2 : (n : ℝ) ^ 2 * log l ≤ log D + y := by
      have := log_le_log hpow h2
      rwa [log_mul hD0.ne' (exp_pos _).ne', log_exp, hlp] at this
    have hPn : P l n := ⟨hn, by linarith [hy.1], by linarith [hy.2]⟩
    have h : ∃ m, P l m := ⟨n, hPn⟩
    have hch : Classical.choose h = n := huniq' l hl _ _ (Classical.choose_spec h) hPn
    refine hfree l hl ?_
    simp only [hJ, dite_eq_left h, hch, Set.mem_Ico]
    exact ⟨by linarith, by linarith⟩

theorem witness_of_density_wide {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) {K A0 s : ℝ} (hK : 1 ≤ K)
    (hAp : 2500 * log p ≤ A0) (hAq : 2500 * log q ≤ A0)
    (hDp : log (2 * D) ^ 2 ≤ 4 * log p * A0) (hDq : log (2 * D) ^ 2 ≤ 4 * log q * A0)
    {B : ℕ} (hB : B = ⌊12 * (D : ℝ) ^ 2 * log (50 * K)⌋₊)
    {X : ℕ} (hX : exp ((9 / 4) ^ (B + 1) * A0) ≤ X)
    (V : Finset ℤ) (hV : (X : ℝ) ≤ K * V.card) (a b : ℤ → ℤ)
    (hdiff : ∀ v ∈ V, v = a v - b v)
    (haX : ∀ v ∈ V, |a v| ≤ (X : ℤ)) (hbX : ∀ v ∈ V, |b v| ≤ (X : ℤ))
    (ha : ∀ v ∈ V, Small p s (a v)) (hb : ∀ v ∈ V, Small q s (b v))
    (t : ℤ) (ht : |(t : ℝ)| ≤ exp (219 / 100 * A0) / 5) :
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
      have h3 := mul_le_mul ht hz (abs_nonneg _) (by positivity)
      refine le_trans h3 (le_of_eq ?_)
      have e1 : exp (219 / 100 * A0) * exp (-(219 / 100) * A0) = 1 := by
        rw [← exp_add, show 219 / 100 * A0 + -(219 / 100) * A0 = 0 by ring, exp_zero]
      rw [div_mul_div_comm, e1]; norm_num
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

/-- **Fixed radius, every target.**  If every large free height carries enough differences, then
the witness height is at most a constant times `(1+|t|)^(E/2.19)`. -/
theorem witness_of_free_heights {p q D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) {K A0 XD β E H : ℝ} (hK : 1 ≤ K)
    (hAp : 2500 * log p ≤ A0) (hAq : 2500 * log q ≤ A0)
    (hDp : log (2 * D) ^ 2 ≤ 4 * log p * A0) (hDq : log (2 * D) ^ 2 ≤ 4 * log q * A0)
    {B : ℕ} (hB : B = ⌊12 * (D : ℝ) ^ 2 * log (50 * K)⌋₊)
    (hE : E = (9 / 4) ^ (B + 1)) (hH : H = 2 * log (8 * D) + 1)
    (hβ : 0 < β) (hβp : β ≤ log p) (hβq : β ≤ log q)
    (hR0 : 8 * exp ((H + log (8 * D)) ^ 2 / (4 * β)) ≤ exp (E * A0))
    (hXD : XD ≤ exp (E * A0))
    (dens : ∀ X : ℕ, Free {p, q} D X → XD ≤ X → ∃ V : Finset ℤ, ∃ a b : ℤ → ℤ,
      (X : ℝ) ≤ K * V.card ∧ (∀ v ∈ V, v = a v - b v) ∧
      (∀ v ∈ V, |a v| ≤ (X : ℤ)) ∧ (∀ v ∈ V, |b v| ≤ (X : ℤ)) ∧
      (∀ v ∈ V, Small p (2 / D) (a v)) ∧ (∀ v ∈ V, Small q (2 / D) (b v)))
    (t : ℤ) :
    ∃ k : ℤ, |(k : ℝ)| ≤ 16 * exp H * exp (E * A0) * (1 + |(t : ℝ)|) ^ (E / (219 / 100))
      ∧ Small p (12 / D) k ∧ Small q (12 / D) (k - t) := by
  classical
  have hne : p ≠ q := by
    intro h
    rw [← h, Nat.coprime_self] at hpq
    omega
  have hcard : ({p, q} : Finset ℕ).card = 2 := card_pair hne
  have ht1 : (1 : ℝ) ≤ 1 + |(t : ℝ)| := by
    have := abs_nonneg (t : ℝ); linarith
  have ht0 : (0 : ℝ) < 1 + |(t : ℝ)| := by linarith
  set T : ℝ := log (1 + |(t : ℝ)|) with hT
  have hT0 : 0 ≤ T := log_nonneg ht1
  set A : ℝ := A0 + T / (219 / 100) with hA
  have hAA : A0 ≤ A := by
    have : 0 ≤ T / (219 / 100) := by positivity
    linarith
  have hE0 : 0 < E := by rw [hE]; positivity
  have hEA : exp (E * A0) ≤ exp (E * A) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_left hAA hE0.le)
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
  obtain ⟨X, hX1, hX2, hXfree⟩ := exists_free {p, q} hS hD (R := exp (E * A)) hβ hlog
    (by rw [hH2]; exact le_trans hR0 hEA)
  rw [hH2] at hX2
  obtain ⟨V, a, b, hV, hdiff, haX, hbX, ha, hb⟩ :=
    dens X hXfree (le_trans hXD (le_trans hEA hX1))
  have hlp : 0 < log (p : ℝ) := log_pos' hp
  have hlq : 0 < log (q : ℝ) := log_pos' hq
  have htA : |(t : ℝ)| ≤ exp (219 / 100 * A) / 5 := by
    have e : exp (219 / 100 * A) = exp (219 / 100 * A0) * (1 + |(t : ℝ)|) := by
      have e2 : 219 / 100 * A = 219 / 100 * A0 + T := by rw [hA]; ring
      rw [e2, exp_add, hT, exp_log ht0]
    have h5 : (5 : ℝ) ≤ exp (219 / 100 * A0) := by
      have h1 : log 2 ≤ log (p : ℝ) := log_le_log (by norm_num) (by exact_mod_cast hp)
      have h2 : (0.69 : ℝ) < log 2 := lt_trans (by norm_num) log_two_gt_d9
      exact le_trans (by linarith) (add_one_le_exp _)
    have h6 := mul_le_mul_of_nonneg_right h5 ht0.le
    rw [e, le_div_iff₀ (by norm_num : (0 : ℝ) < 5)]
    linarith
  obtain ⟨k, hk, hkp, hkq⟩ := witness_of_density_wide hp hq hpq hD (A0 := A) (s := 2 / D) hK
    (le_trans hAp hAA) (le_trans hAq hAA)
    (le_trans hDp (mul_le_mul_of_nonneg_left hAA (by positivity)))
    (le_trans hDq (mul_le_mul_of_nonneg_left hAA (by positivity)))
    hB (X := X) (by rw [← hE]; exact hX1) V hV a b hdiff haX hbX ha hb t htA
  have er : 4 * (2 / (D : ℝ) + 1 / D) = 12 / D := by ring
  rw [er] at hkp hkq
  refine ⟨k, ?_, hkp, hkq⟩
  have h1 : |(k : ℝ)| ≤ 8 * (X : ℝ) := by exact_mod_cast hk
  have epow : exp (E * A)
      = exp (E * A0) * (1 + |(t : ℝ)|) ^ (E / (219 / 100)) := by
    rw [rpow_def_of_pos ht0, ← hT, ← exp_add]
    congr 1
    rw [hA]; ring
  calc |(k : ℝ)| ≤ 8 * (X : ℝ) := h1
    _ ≤ 8 * (2 * exp H * exp (E * A)) := by linarith
    _ = _ := by rw [epow]; ring

end TwoPrimesFreeHeight
