import Mathlib
import LeanCheck.TwoPrimesSupport
import LeanCheck.TwoPrimesDualSharp

/-!
# The two quantitative claims

`ClaimU p q C` and `ClaimA p q B` are the unit-target claim with the constant `C` and the range claim
with the exponent `B`.

* `claimU_of_density`: differences with inverse density at most `D^(δ+o(1))`, `δ < 1`, at heights
  `ln X ≤ x ln² D` for one `D` in each short range give `ClaimU` for every constant above
  `x/(1-δ)²`.
* `claimA_of_density`: a constant inverse density gives `ClaimA` for every exponent above `x`.
* `claimU_of_visible`: if for every large `D` and every `θ` away from the integers some level with
  `ℓ^(n²) ≤ exp(x ln² D)` has `I_n ‖ℓ^(n²) θ‖ ≥ D^(δ-1)`, `0 < δ ≤ 1`, then `ClaimU` holds for
  every constant above `x/δ²`.
* `claimU_of_dual_condition`: the case of the thresholds `D^(-τ)` for all small `τ`.

The hypotheses are not proved here; they are open.
-/

namespace TwoPrimesClaims

open Finset Real Filter TwoPrimesEffective TwoPrimesDual TwoPrimesDualSharp

def ClaimU (p q : ℕ) (C : ℝ) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ k : ℤ, |(k : ℝ)| ≤ exp (C * log (1 / ε) ^ 2) ∧ Small q ε k ∧ Small p ε (k - 1)

def ClaimA (p q : ℕ) (B : ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ X : ℝ, 1 / η ≤ X ∧ X ≤ exp (B * log (1 / ε) ^ 2) ∧
      ∀ t : ℤ, |(t : ℝ)| ≤ η * X →
        ∃ k : ℤ, |(k : ℝ)| ≤ X ∧ Small q ε k ∧ Small p ε (k - t)

/-- At least `X/K` differences `a - b` of the two balls of radius `1/D` in `[-X, X]`. -/
def Carries (p q D X : ℕ) (K : ℝ) : Prop :=
  ∃ W : Finset ℤ, (X : ℝ) ≤ K * W.card ∧ ∀ w ∈ W, ∃ a b : ℤ, w = a - b ∧ |a| ≤ (X : ℤ)
    ∧ |b| ≤ (X : ℤ) ∧ Small q (1 / D) a ∧ Small p (1 / D) b

/-- `G = max(q^(m²), p^(n²))` with the least levels whose step exceeds `D`. -/
def IsG (p q D G : ℕ) : Prop :=
  ∃ m n : ℕ, D < q ^ (2 * m + 1) ∧ D < p ^ (2 * n + 1) ∧ G = max (q ^ (m ^ 2)) (p ^ (n ^ 2))

lemma Small.mono {p : ℕ} {s s' : ℝ} {k : ℤ} (h : Small p s k) (hs : s ≤ s') : Small p s' k :=
  fun n => lt_of_lt_of_le (h n) hs

/-- Witnesses from a set of differences. -/
lemma witness_of_carries {p q D X G : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    (hD : 1 ≤ D) (hG : IsG p q D G) {K : ℝ} (hX : 1 ≤ X) (hC : Carries p q D X K)
    (t : ℤ) (ht : |t| + (G : ℤ) ≤ X) :
    ∃ k : ℤ, |(k : ℝ)| ≤ 35 * K * X ∧ Small q (35 * K / D) k ∧ Small p (35 * K / D) (k - t) := by
  classical
  obtain ⟨m, n, hm, hn, rfl⟩ := hG
  obtain ⟨W, hW, h⟩ := hC
  choose! a b hab using h
  exact TwoPrimesSupport.witness_of_support hp hq hpq hD hm hn hX W hW a b
    (fun w hw => (hab w hw).1) (fun w hw => (hab w hw).2.1) (fun w hw => (hab w hw).2.2.1)
    (fun w hw => (hab w hw).2.2.2.1) (fun w hw => (hab w hw).2.2.2.2) t ht

lemma eventually_quad {a : ℝ} (ha : 0 < a) (b c : ℝ) :
    ∀ᶠ L : ℝ in atTop, b * L + c ≤ a * L ^ 2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop ((|b| + |c|) / a)] with L h1 h2
  rw [div_le_iff₀ ha] at h2
  have h3 : b * L ≤ |b| * L := mul_le_mul_of_nonneg_right (le_abs_self b) (by linarith)
  have h4 : c ≤ |c| * L := le_trans (le_abs_self c) (le_mul_of_one_le_right (abs_nonneg c) h1)
  have h5 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ L by linarith)
  have e : a * L ^ 2 = L * a * L := by ring
  rw [e]
  nlinarith

/-- A statement for all large `L = ln(1/ε)` holds for all small `ε`. -/
lemma small_eps {P : ℝ → Prop} (h : ∀ᶠ L : ℝ in atTop, P L) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → P (log (1 / ε)) ∧ exp (-log (1 / ε)) = ε := by
  obtain ⟨L0, hL0⟩ := eventually_atTop.mp h
  refine ⟨exp (-L0), exp_pos _, fun ε hε hlt => ?_⟩
  have e : log (1 / ε) = -log ε := by rw [one_div, log_inv]
  have h1 : log ε < -L0 := by
    have := log_lt_log hε hlt
    rwa [log_exp] at this
  refine ⟨hL0 _ (by rw [e]; linarith), ?_⟩
  rw [e, neg_neg, exp_log hε]

theorem claimU_of_density {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    {x δ : ℝ} (hx : 0 < x) (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (h : ∀ η : ℝ, 0 < η → ∃ D1 : ℝ, ∀ D0 : ℝ, D1 ≤ D0 → ∃ D X G : ℕ, ∃ K : ℝ,
      D0 ≤ D ∧ (D : ℝ) ≤ D0 ^ (1 + η) ∧ IsG p q D G ∧ 2 * G ≤ X ∧ log X ≤ x * log D ^ 2
        ∧ K ≤ (D : ℝ) ^ (δ + η) ∧ Carries p q D X K)
    (C : ℝ) (hC : x / (1 - δ) ^ 2 < C) : ClaimU p q C := by
  have hd : 0 < 1 - δ := by linarith
  -- the slack
  set f : ℝ → ℝ := fun η => x * ((1 + η) * (1 / (1 - δ - η) + η)) ^ 2 with hf
  have hf0 : f 0 < C := by
    simp only [hf, add_zero, one_mul, sub_zero]
    rw [div_pow, one_pow, mul_one_div]
    exact hC
  have hcont : ContinuousAt f 0 := by
    have : ContinuousAt (fun η : ℝ => 1 / (1 - δ - η)) 0 :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by simpa using hd.ne')
    exact continuousAt_const.mul (((continuousAt_const.add continuousAt_id).mul
      (this.add continuousAt_id)).pow 2)
  obtain ⟨η, hη0, hη1, hηf⟩ : ∃ η : ℝ, 0 < η ∧ η < 1 - δ ∧ f η < C := by
    have h1 : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi 0), f η < C :=
      (hcont.eventually_lt_const hf0).filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ η in nhdsWithin (0 : ℝ) (Set.Ioi 0), η < 1 - δ :=
      (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds
    obtain ⟨η, hh⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
    exact ⟨η, hh.2.2, hh.2.1, hh.1⟩
  obtain ⟨D1, hD1⟩ := h η hη0
  set a : ℝ := 1 / (1 - δ - η) + η with ha
  have hde : 0 < 1 - δ - η := by linarith
  have ha0 : 0 < a := add_pos (one_div_pos.mpr hde) hη0
  have hgap : 0 < C - x * ((1 + η) * a) ^ 2 := by
    have := hηf
    simp only [hf] at this
    linarith
  have hev : ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ D1 ≤ exp (a * L)
      ∧ log 35 < η * (1 - δ - η) * L
      ∧ (δ + η) * ((1 + η) * a) * L + log 35 ≤ (C - x * ((1 + η) * a) ^ 2) * L ^ 2 := by
    refine (eventually_ge_atTop 1).and (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_))
    · exact (tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha0)).eventually_ge_atTop D1
    · exact (tendsto_id.const_mul_atTop (mul_pos hη0 hde)).eventually_gt_atTop (log 35)
    · exact eventually_quad hgap _ _
  obtain ⟨ε0, hε0, hε⟩ := small_eps hev
  refine ⟨ε0, hε0, fun ε hεp hεl => ?_⟩
  obtain ⟨⟨hL1, hLD, h35, hquad⟩, hexp⟩ := hε ε hεp hεl
  set L := log (1 / ε) with hL
  obtain ⟨D, X, G, K, h0, h1, hG, h2G, hlog, hK, hcar⟩ := hD1 (exp (a * L)) hLD
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le (exp_pos _) h0
  have hDnat : 1 ≤ D := by
    have : 0 < D := by exact_mod_cast hD0
    omega
  have hG1 : 1 ≤ G := by
    obtain ⟨m, n, _, _, rfl⟩ := hG
    exact le_trans (Nat.one_le_pow _ _ (by omega)) (le_max_left _ _)
  have hX1 : 1 ≤ X := by omega
  have ht : |(1 : ℤ)| + (G : ℤ) ≤ X := by
    rw [abs_one]
    have : 1 + G ≤ X := by omega
    exact_mod_cast this
  obtain ⟨k, hk, hkq, hkp⟩ := witness_of_carries hp hq hpq hDnat hG hX1 hcar 1 ht
  have hlD1 : a * L ≤ log D := by
    have := log_le_log (exp_pos _) h0
    rwa [log_exp] at this
  have hlD2 : log D ≤ (1 + η) * a * L := by
    have := log_le_log hD0 h1
    rw [log_rpow (exp_pos _), log_exp] at this
    linarith
  have hlD0 : 0 ≤ log D := le_trans (mul_nonneg ha0.le (by linarith)) hlD1
  -- the radius
  have hK0 : 0 ≤ K := by
    obtain ⟨W, hW, _⟩ := hcar
    have hXr : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
    have hWc : (0 : ℝ) ≤ W.card := by positivity
    by_contra hneg
    have : K * W.card ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hneg) hWc
    linarith
  have hDexp : (D : ℝ) = exp (log D) := (exp_log hD0).symm
  have hKexp : K ≤ exp ((δ + η) * log D) := by
    refine le_trans hK (le_of_eq ?_)
    rw [rpow_def_of_pos hD0, mul_comm]
  have hrad : 35 * K / D ≤ ε := by
    rw [div_le_iff₀ hD0, ← hexp]
    have h2 : 35 * exp ((δ + η) * log D) ≤ exp (-L) * exp (log D) := by
      have e : (35 : ℝ) = exp (log 35) := (exp_log (by norm_num)).symm
      rw [e, ← exp_add, ← exp_add, exp_le_exp]
      have h3 : (1 - δ - η) * (a * L) ≤ (1 - δ - η) * log D := mul_le_mul_of_nonneg_left hlD1 hde.le
      have h4 : (1 - δ - η) * (a * L) = L + η * (1 - δ - η) * L := by
        rw [ha]
        field_simp
      linarith
    rw [← hDexp] at h2
    exact le_trans (mul_le_mul_of_nonneg_left hKexp (by norm_num)) h2
  refine ⟨k, ?_, Small.mono hkq hrad, Small.mono hkp hrad⟩
  -- the height
  have hXr : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hXexp : (X : ℝ) ≤ exp (x * log D ^ 2) := by
    have := exp_le_exp.mpr hlog
    rwa [exp_log hXr] at this
  have h5 : 35 * K * X ≤ exp (log 35 + (δ + η) * log D + x * log D ^ 2) := by
    rw [exp_add, exp_add, exp_log (by norm_num : (0 : ℝ) < 35)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hKexp (by norm_num)) hXexp hXr.le (by positivity)
  refine le_trans hk (le_trans h5 (exp_le_exp.mpr ?_))
  have h6 : (δ + η) * log D ≤ (δ + η) * ((1 + η) * a * L) :=
    mul_le_mul_of_nonneg_left hlD2 (by linarith)
  have h7 : x * log D ^ 2 ≤ x * ((1 + η) * a * L) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlD0 hlD2 2) hx.le
  have e : x * ((1 + η) * a * L) ^ 2 = x * ((1 + η) * a) ^ 2 * L ^ 2 := by ring
  have e2 : (δ + η) * ((1 + η) * a * L) = (δ + η) * ((1 + η) * a) * L := by ring
  nlinarith [hquad]

set_option maxHeartbeats 1000000 in
theorem claimA_of_density {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : Nat.Coprime p q)
    {x K : ℝ} (hx : 0 < x) (hK : 1 ≤ K)
    (h : ∀ θ : ℝ, 0 < θ → ∃ D1 : ℝ, ∀ D0 : ℝ, D1 ≤ D0 → ∃ D X G : ℕ,
      D0 ≤ D ∧ (D : ℝ) ≤ D0 ^ (1 + θ) ∧ IsG p q D G ∧ 2 * G ≤ X
        ∧ log X ≤ x * log D ^ 2 ∧ Carries p q D X K)
    (B : ℝ) (hB : x < B) : ClaimA p q B := by
  have hK0 : 0 < K := by linarith
  set f : ℝ → ℝ := fun θ => x * ((1 + θ) * (1 + θ)) ^ 2 with hf
  have hf0 : f 0 < B := by simpa [hf] using hB
  have hcont : ContinuousAt f 0 :=
    continuousAt_const.mul (((continuousAt_const.add continuousAt_id).mul
      (continuousAt_const.add continuousAt_id)).pow 2)
  obtain ⟨θ, hθ0, hθf⟩ : ∃ θ : ℝ, 0 < θ ∧ f θ < B := by
    have h1 : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), f θ < B :=
      (hcont.eventually_lt_const hf0).filter_mono nhdsWithin_le_nhds
    obtain ⟨θ, hh⟩ := (h1.and self_mem_nhdsWithin).exists
    exact ⟨θ, hh.2, hh.1⟩
  obtain ⟨D1, hD1⟩ := h θ hθ0
  have hgap : 0 < B - f θ := by linarith
  set c1 : ℝ := log (36 * K) with hc1
  set c2 : ℝ := log (35 * K + 2) with hc2
  have hev : ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ max D1 q ≤ exp L * (35 * K) + 2 ∧ c2 ≤ θ * L
      ∧ c1 ≤ (B - f θ) * L ^ 2 := by
    refine (eventually_ge_atTop 1).and (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_))
    · have : Tendsto (fun L => exp L * (35 * K) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ _
          (tendsto_exp_atTop.atTop_mul_const (by positivity))
      exact this.eventually_ge_atTop _
    · exact (tendsto_id.const_mul_atTop hθ0).eventually_ge_atTop c2
    · filter_upwards [eventually_quad hgap 0 c1] with L hL
      simpa using hL
  obtain ⟨ε0, hε0, hε⟩ := small_eps hev
  refine ⟨1 / (80 * K), by positivity, ε0, hε0, fun ε hεp hεl => ?_⟩
  obtain ⟨⟨hL1, hLD, hc2L, hquad⟩, hexp⟩ := hε ε hεp hεl
  set L := log (1 / ε) with hL
  set D0 : ℝ := exp L * (35 * K) + 2 with hD0def
  obtain ⟨D, X, G, h0, h1, hG, h2G, hlog, hcar⟩ := hD1 D0 (le_trans (le_max_left _ _) hLD)
  have hqD : q ≤ D := by
    have : (q : ℝ) ≤ D := le_trans (le_trans (le_max_right _ _) hLD) h0
    exact_mod_cast this
  have h3X : 3 ≤ X := by
    have h2 : q ≤ G := by
      obtain ⟨m, n, hm, _, rfl⟩ := hG
      have hm0 : m ≠ 0 := by
        intro h0
        rw [h0, mul_zero, zero_add, pow_one] at hm
        omega
      exact le_trans (Nat.le_self_pow (pow_ne_zero 2 hm0) q) (le_max_left _ _)
    omega
  have hD00 : 0 < D0 := by
    have := mul_pos (exp_pos L) (show (0 : ℝ) < 35 * K by positivity)
    rw [hD0def]; linarith
  have hD0r : (0 : ℝ) < D := lt_of_lt_of_le hD00 h0
  have hDnat : 1 ≤ D := by
    have : 0 < D := by exact_mod_cast hD0r
    omega
  have hXr : (3 : ℝ) ≤ X := by exact_mod_cast h3X
  have hKX : 3 * K ≤ K * X := by
    have := mul_le_mul_of_nonneg_left hXr hK0.le
    linarith
  set X' : ℝ := 35 * K * X + 1 with hX'
  -- the radius
  have hrad : 35 * K / D ≤ ε := by
    rw [div_le_iff₀ hD0r, ← hexp, exp_neg]
    rw [inv_mul_eq_div, le_div_iff₀ (exp_pos L), mul_comm]
    have : exp L * (35 * K) ≤ D0 := by rw [hD0def]; linarith
    exact le_trans this h0
  -- the height
  have hlD0 : log D0 ≤ L + c2 := by
    have h2 : D0 ≤ exp L * (35 * K + 2) := by
      have : (1 : ℝ) ≤ exp L := one_le_exp (by linarith)
      rw [hD0def]; nlinarith
    have := log_le_log hD00 h2
    rwa [log_mul (exp_pos L).ne' (by positivity), log_exp] at this
  have hlD : log D ≤ (1 + θ) * (1 + θ) * L := by
    have h2 := log_le_log hD0r h1
    rw [log_rpow hD00] at h2
    have h3 : log D0 ≤ (1 + θ) * L := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 1 + θ by linarith)
    linarith
  have hlDnn : 0 ≤ log D := log_nonneg (by exact_mod_cast hDnat)
  have hX'pos : 0 < X' := by
    have : (0 : ℝ) ≤ 35 * K * X := by positivity
    rw [hX']; linarith
  have hX'le : X' ≤ exp (B * L ^ 2) := by
    have h2 : X' ≤ 36 * K * X := by
      rw [hX']; nlinarith
    refine le_trans h2 ?_
    have hX0 : (0 : ℝ) < X := by linarith
    have e : 36 * K * (X : ℝ) = exp (c1 + log X) := by
      rw [exp_add, hc1, exp_log (by positivity), exp_log hX0]
    rw [e, exp_le_exp]
    have h3 : x * log D ^ 2 ≤ x * ((1 + θ) * (1 + θ) * L) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlDnn hlD 2) hx.le
    have e2 : x * ((1 + θ) * (1 + θ) * L) ^ 2 = f θ * L ^ 2 := by simp only [hf]; ring
    nlinarith
  refine ⟨X', ?_, hX'le, fun t ht => ?_⟩
  · rw [one_div_one_div, hX']
    nlinarith
  have hηX : 1 / (80 * K) * X' ≤ (X : ℝ) / 2 := by
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity), hX']
    nlinarith
  have htX : |t| + (G : ℤ) ≤ X := by
    have h2 : |(t : ℝ)| ≤ (X : ℝ) / 2 := le_trans ht hηX
    have h3 : (G : ℝ) ≤ (X : ℝ) / 2 := by
      have : (2 : ℝ) * G ≤ X := by exact_mod_cast h2G
      linarith
    have h4 : |(t : ℝ)| + (G : ℝ) ≤ (X : ℝ) := by linarith
    exact_mod_cast h4
  obtain ⟨k, hk, hkq, hkp⟩ :=
    witness_of_carries hp hq hpq hDnat hG (by omega) hcar t htX
  refine ⟨k, le_trans hk (by rw [hX']; linarith), Small.mono hkq hrad, Small.mono hkp hrad⟩

/-- Some level of `ℓ` below the height `exp(x ln² D)` sees `θ` at the threshold `c`. -/
def Visible (ℓ D : ℕ) (x c θ : ℝ) : Prop :=
  ∃ n : ℕ, (ℓ : ℝ) ^ (n ^ 2) ≤ exp (x * log D ^ 2) ∧ 1 ≤ ℓ ^ (2 * n + 1) / D ∧
    c ≤ ((ℓ ^ (2 * n + 1) / D : ℕ) : ℝ) * nd ((ℓ : ℝ) ^ (n ^ 2) * θ)

lemma exists_height {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (Y : ℝ) : ∃ N : ℕ, Y < (ℓ : ℝ) ^ (N ^ 2) := by
  have h1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt Y h1
  refine ⟨n, lt_of_lt_of_le hn (pow_le_pow_right₀ h1.le ?_)⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Nat.le_self_pow two_ne_zero n

/-- The number of levels up to the height, and the size of the next step. -/
lemma levels_below {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {x l : ℝ} (hx : 0 < x) (hl : 0 ≤ l) :
    ∃ N : ℕ, (∀ n : ℕ, (ℓ : ℝ) ^ (n ^ 2) ≤ exp (x * l ^ 2) → n < N) ∧
      log ((ℓ : ℝ) ^ (N ^ 2))
        ≤ x * l ^ 2 + 2 * (sqrt (x / log ℓ) * log ℓ) * l + log ℓ := by
  classical
  have hℓr : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hlog : 0 < log (ℓ : ℝ) := log_pos hℓr
  set N := Nat.find (exists_height hℓ (exp (x * l ^ 2))) with hN
  have hspec : exp (x * l ^ 2) < (ℓ : ℝ) ^ (N ^ 2) :=
    Nat.find_spec (exists_height hℓ (exp (x * l ^ 2)))
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero] at hspec
    have : (1 : ℝ) ≤ exp (x * l ^ 2) := one_le_exp (mul_nonneg hx.le (sq_nonneg _))
    linarith
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hMle : (ℓ : ℝ) ^ (M ^ 2) ≤ exp (x * l ^ 2) := by
    have := Nat.find_min (exists_height hℓ (exp (x * l ^ 2))) (show M < N by omega)
    exact not_lt.mp this
  refine ⟨N, fun n hn => ?_, ?_⟩
  · by_contra hc
    have h1 : (ℓ : ℝ) ^ (N ^ 2) ≤ (ℓ : ℝ) ^ (n ^ 2) :=
      pow_le_pow_right₀ hℓr.le (Nat.pow_le_pow_left (by omega) 2)
    linarith
  have hM2 : (M : ℝ) ^ 2 * log ℓ ≤ x * l ^ 2 := by
    have := log_le_log (by positivity) hMle
    rw [log_pow, log_exp, Nat.cast_pow] at this
    exact this
  have hMl : (M : ℝ) ≤ sqrt (x / log ℓ) * l := by
    have h1 : (M : ℝ) ^ 2 ≤ x / log ℓ * l ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog]
      exact hM2
    have h2 := sqrt_le_sqrt h1
    rw [sqrt_sq (Nat.cast_nonneg M), sqrt_mul (div_nonneg hx.le hlog.le), sqrt_sq hl] at h2
    exact h2
  rw [log_pow, hM]
  push_cast
  have h3 := mul_le_mul_of_nonneg_right hMl hlog.le
  have e : ((M : ℝ) + 1) ^ 2 * log ℓ = (M : ℝ) ^ 2 * log ℓ + 2 * ((M : ℝ) * log ℓ) + log ℓ := by
    ring
  have e2 : 2 * (sqrt (x / log ℓ) * log ℓ) * l = 2 * (sqrt (x / log ℓ) * l * log ℓ) := by ring
  rw [e, e2]
  linarith

lemma log_le_two_sqrt {y : ℝ} (hy : 0 < y) : log y ≤ 2 * sqrt y := by
  have h := log_le_sub_one_of_pos (sqrt_pos.mpr hy)
  rw [log_sqrt hy.le] at h
  linarith [sqrt_nonneg y]

set_option maxHeartbeats 2000000 in
/-- **Any power improvement over the trivial threshold `1/D` gives the unit-target claim.** -/
theorem claimU_of_visible {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {x δ : ℝ} (hx : 0 < x)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h : ∃ D1 : ℕ, ∀ D : ℕ, D1 ≤ D → ∀ θ : ℝ, 1 / 10 < nd θ →
      Visible q D x ((D : ℝ) ^ (δ - 1)) θ ∨ Visible p D x ((D : ℝ) ^ (δ - 1)) θ)
    (C : ℝ) (hC : x / δ ^ 2 < C) : ClaimU p q C := by
  obtain ⟨D1, hD1⟩ := h
  set f : ℝ → ℝ := fun τ => x * ((1 + τ) / δ) ^ 2 with hf
  have hf0 : f 0 < C := by
    simp only [hf, add_zero]
    rw [div_pow, one_pow, mul_one_div]
    exact hC
  have hcont : ContinuousAt f 0 :=
    continuousAt_const.mul (((continuousAt_const.add continuousAt_id).div_const δ).pow 2)
  obtain ⟨τ, hτ0, hτf⟩ : ∃ τ : ℝ, 0 < τ ∧ f τ < C := by
    have h1 : ∀ᶠ τ in nhdsWithin (0 : ℝ) (Set.Ioi 0), f τ < C :=
      (hcont.eventually_lt_const hf0).filter_mono nhdsWithin_le_nhds
    obtain ⟨τ, hh⟩ := (h1.and self_mem_nhdsWithin).exists
    exact ⟨τ, hh.2, hh.1⟩
  set a : ℝ := (1 + τ) / δ with ha
  have ha0 : 0 < a := div_pos (by linarith) hδ0
  have hgap : 0 < C - x * a ^ 2 := by
    have : f τ = x * a ^ 2 := rfl
    linarith
  set s : ℝ := sqrt (x / log q) * log q + sqrt (x / log p) * log p with hs
  have hs0 : 0 ≤ s := by
    have h1 : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
    have h2 : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
    exact add_nonneg (mul_nonneg (sqrt_nonneg _) h1) (mul_nonneg (sqrt_nonneg _) h2)
  set e0 : ℝ := log q + log p + log 28 + log 2 with he0
  -- conditions on `l = ln D`
  set b1 : ℝ := 2 * sqrt (x + 2) + 1 + 2 * s with hb1
  have hev1 : ∀ᶠ l : ℝ in atTop, 1 ≤ l ∧ b1 * l + (log 7 + log 2 + e0) ≤ (x / 3 + 4 / 3) * l ^ 2 :=
    (eventually_ge_atTop 1).and (eventually_quad (by positivity) _ _)
  obtain ⟨l0, hl0⟩ := eventually_atTop.mp hev1
  have hev : ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ max l0 (log (max D1 3)) ≤ a * L
      ∧ 8 * (x + 2) * (a * L + 1) ^ 2 ≤ exp (τ * L)
      ∧ 2 * s * (a * L + 1) + e0 + x * (2 * a * L + 1) ≤ (C - x * a ^ 2) * L ^ 2 := by
    refine (eventually_ge_atTop 1).and (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_))
    · exact (tendsto_id.const_mul_atTop ha0).eventually_ge_atTop _
    · have h1 : Tendsto (fun L => exp (τ * L) / (τ * L) ^ 2) atTop atTop :=
        (tendsto_exp_div_pow_atTop 2).comp (tendsto_id.const_mul_atTop hτ0)
      filter_upwards [h1.eventually_ge_atTop (8 * (x + 2) * ((a + 1) / τ) ^ 2),
        eventually_ge_atTop (1 : ℝ)] with L hL h1L
      have hτL : 0 < (τ * L) ^ 2 := by
        have : 0 < τ * L := mul_pos hτ0 (by linarith)
        positivity
      rw [le_div_iff₀ hτL] at hL
      refine le_trans ?_ hL
      have e : 8 * (x + 2) * ((a + 1) / τ) ^ 2 * (τ * L) ^ 2 = 8 * (x + 2) * ((a + 1) * L) ^ 2 := by
        field_simp
      rw [e]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ 2) (by positivity)
      · have := mul_nonneg ha0.le (show (0 : ℝ) ≤ L by linarith)
        linarith
      · nlinarith
    · filter_upwards [eventually_quad hgap (2 * s * a + 2 * x * a) (2 * s + e0 + x)] with L hL
      refine le_trans (le_of_eq ?_) hL
      ring
  obtain ⟨ε0, hε0, hε⟩ := small_eps hev
  refine ⟨min ε0 (exp (-1)), lt_min hε0 (exp_pos _), fun ε hεp hεl => ?_⟩
  obtain ⟨⟨hL1, hLl, h8, hquad⟩, hexp⟩ := hε ε hεp (lt_of_lt_of_le hεl (min_le_left _ _))
  set L := log (1 / ε) with hL
  set D : ℕ := ⌈exp (a * L)⌉₊ with hDdef
  have hDge : exp (a * L) ≤ D := Nat.le_ceil _
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le (exp_pos _) hDge
  set l := log (D : ℝ) with hl
  have hlge : a * L ≤ l := by
    have := log_le_log (exp_pos _) hDge
    rwa [log_exp] at this
  have haL : 0 ≤ a * L := mul_nonneg ha0.le (by linarith)
  have hlle : l ≤ a * L + 1 := by
    have h1 : (D : ℝ) ≤ exp (a * L) + 1 := (Nat.ceil_lt_add_one (exp_pos _).le).le
    have h2 : (D : ℝ) ≤ exp (a * L + 1) := by
      have h3 : (1 : ℝ) ≤ exp (a * L) := one_le_exp haL
      have h4 : (2 : ℝ) ≤ exp 1 := by
        have := add_one_le_exp (1 : ℝ)
        linarith
      rw [exp_add]
      have h5 := mul_le_mul_of_nonneg_left h4 (exp_pos (a * L)).le
      linarith
    have := log_le_log hD0 h2
    rwa [log_exp] at this
  have hl0l : l0 ≤ l := le_trans (le_trans (le_max_left _ _) hLl) hlge
  obtain ⟨hl1, hlquad⟩ := hl0 l hl0l
  have hlnn : 0 ≤ l := by linarith
  have hDbig : max D1 3 ≤ D := by
    have h1 : log ((max D1 3 : ℕ) : ℝ) ≤ l := by
      have h2 : log ((max D1 3 : ℕ) : ℝ) ≤ a * L := by
        have e : ((max D1 3 : ℕ) : ℝ) = max (D1 : ℝ) 3 := by rw [Nat.cast_max, Nat.cast_ofNat]
        rw [e]
        exact le_trans (le_max_right _ _) hLl
      exact le_trans h2 hlge
    have h3 : (0 : ℝ) < ((max D1 3 : ℕ) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (le_max_right D1 3))
    have := (log_le_log_iff h3 hD0).mp h1
    exact_mod_cast this
  have hD1D : D1 ≤ D := le_trans (le_max_left _ _) hDbig
  have hDnat : 1 ≤ D := le_trans (by norm_num) (le_trans (le_max_right D1 3) hDbig)
  have hDr1 : (1 : ℝ) ≤ D := by exact_mod_cast hDnat
  -- the data of the dual criterion
  set H : ℕ := ⌈(D : ℝ) ^ (1 - δ)⌉₊ with hHdef
  set c : ℝ := (D : ℝ) ^ (δ - 1) with hc
  have hpow1 : (1 : ℝ) ≤ (D : ℝ) ^ (1 - δ) := one_le_rpow hDr1 (by linarith)
  have hHge : (D : ℝ) ^ (1 - δ) ≤ H := Nat.le_ceil _
  have hHle : (H : ℝ) ≤ 2 * (D : ℝ) ^ (1 - δ) := by
    have := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (D : ℝ) ^ (1 - δ) by positivity)).le
    rw [← hHdef] at this
    linarith
  have hH0 : (0 : ℝ) < H := lt_of_lt_of_le (by linarith) hHge
  have h2cH : 1 ≤ 2 * c * H := by
    have h1 : c * (D : ℝ) ^ (1 - δ) = 1 := by
      rw [hc, ← rpow_add hD0, show δ - 1 + (1 - δ) = 0 by ring, rpow_zero]
    have h2 := mul_le_mul_of_nonneg_left hHge (show 0 ≤ c by positivity)
    linarith
  obtain ⟨Nq, hNq, hNqlog⟩ := levels_below hq hx hlnn
  obtain ⟨Np, hNp, hNplog⟩ := levels_below hp hx hlnn
  set R : ℕ := 2 * q ^ (Nq ^ 2) + 2 * p ^ (Np ^ 2) with hRdef
  have hterm : ∀ (r N : ℕ), 2 ≤ r →
      ∑ n : Fin N, (r : ℤ) ^ ((n : ℕ) ^ 2) * ((r ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℤ)
        ≤ ((2 * r ^ (N ^ 2) : ℕ) : ℤ) := by
    intro r N hr
    have h1 : ∀ n : Fin N, r ^ ((n : ℕ) ^ 2) * (r ^ (2 * (n : ℕ) + 1) / D)
        ≤ r ^ (((n : ℕ) + 1) ^ 2) := by
      intro n
      have e : r ^ (((n : ℕ) + 1) ^ 2) = r ^ ((n : ℕ) ^ 2) * r ^ (2 * (n : ℕ) + 1) := by
        rw [← pow_add]; congr 1; ring
      rw [e]
      exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
    have h2 : ∑ n : Fin N, r ^ ((n : ℕ) ^ 2) * (r ^ (2 * (n : ℕ) + 1) / D) ≤ 2 * r ^ (N ^ 2) := by
      refine le_trans (sum_le_sum fun n _ => h1 n) ?_
      rw [Fin.sum_univ_eq_sum_range (fun n => r ^ ((n + 1) ^ 2)) N]
      exact (sum_levels hr N).le
    exact_mod_cast h2
  have hR : ∑ n : Fin Nq, (q : ℤ) ^ ((n : ℕ) ^ 2) * ((q ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℤ)
      + ∑ n : Fin Np, (p : ℤ) ^ ((n : ℕ) ^ 2) * ((p ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℤ) ≤ R := by
    refine le_trans (add_le_add (hterm q Nq hq) (hterm p Np hp)) (le_of_eq ?_)
    rw [hRdef, Nat.cast_add]
  have hR1 : 1 ≤ R := by
    have : 0 < q ^ (Nq ^ 2) := pow_pos (by omega) _
    omega
  set hh : ℕ := ⌈(x + 1) * l ^ 2⌉₊ with hhdef
  have hl2 : 1 ≤ l ^ 2 := one_le_pow₀ hl1
  have hhge : (x + 1) * l ^ 2 ≤ hh := Nat.le_ceil _
  have hhle : (hh : ℝ) ≤ (x + 2) * l ^ 2 := by
    have := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (x + 1) * l ^ 2 by positivity)).le
    rw [← hhdef] at this
    linarith
  have hh1 : 1 ≤ hh := by
    have : (0 : ℝ) < hh := lt_of_lt_of_le (by positivity) hhge
    exact_mod_cast this
  have hhr : (0 : ℝ) < hh := by exact_mod_cast (by omega : 0 < hh)
  -- logarithm of the next steps
  have hqpos : (0 : ℝ) < (q : ℝ) ^ (Nq ^ 2) := by
    have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity
  have hppos : (0 : ℝ) < (p : ℝ) ^ (Np ^ 2) := by
    have : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    positivity
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlogp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  have hsq : 0 ≤ sqrt (x / log q) * log q := mul_nonneg (sqrt_nonneg _) hlogq
  have hsp : 0 ≤ sqrt (x / log p) * log p := mul_nonneg (sqrt_nonneg _) hlogp
  set M : ℝ := x * l ^ 2 + 2 * s * l + log q + log p with hM
  have hqM : (q : ℝ) ^ (Nq ^ 2) ≤ exp M := by
    rw [← exp_log hqpos, exp_le_exp]
    have := mul_nonneg hsp hlnn
    rw [hM, hs]
    nlinarith [hNqlog]
  have hpM : (p : ℝ) ^ (Np ^ 2) ≤ exp M := by
    rw [← exp_log hppos, exp_le_exp]
    have := mul_nonneg hsq hlnn
    rw [hM, hs]
    nlinarith [hNplog]
  have hRM : (R : ℝ) ≤ 4 * exp M := by
    have e : (R : ℝ) = 2 * (q : ℝ) ^ (Nq ^ 2) + 2 * (p : ℝ) ^ (Np ^ 2) := by
      rw [hRdef]; push_cast; ring
    rw [e]; linarith
  have hlogcond : log (7 * hh * ((H : ℝ) * R)) ≤ 4 * hh / 3 := by
    have hRr : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
    have h1 : 7 * (hh : ℝ) * ((H : ℝ) * R) ≤ 28 * hh * (2 * (D : ℝ) ^ (1 - δ)) * exp M := by
      have h2 := mul_le_mul hHle hRM hRr.le (by positivity)
      have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 7 * hh by positivity)
      refine le_trans h3 (le_of_eq ?_)
      ring
    have h4 := log_le_log (by positivity) h1
    have h5 : log (28 * (hh : ℝ) * (2 * (D : ℝ) ^ (1 - δ)) * exp M)
        = log 28 + log hh + (log 2 + (1 - δ) * l) + M := by
      rw [log_mul (by positivity) (exp_pos _).ne', log_mul (by positivity) (by positivity),
        log_mul (by norm_num) hhr.ne', log_mul (by norm_num) (by positivity),
        log_rpow hD0, log_exp]
    have h6 : log (hh : ℝ) ≤ 2 * sqrt (x + 2) * l := by
      refine le_trans (log_le_two_sqrt hhr) ?_
      have h7 := sqrt_le_sqrt hhle
      rw [sqrt_mul (by positivity), sqrt_sq hlnn] at h7
      linarith
    have h8 : (1 - δ) * l ≤ l := by
      have := mul_le_mul_of_nonneg_right (show 1 - δ ≤ 1 by linarith) hlnn
      linarith
    have h9 : (4 / 3) * ((x + 1) * l ^ 2) ≤ 4 * hh / 3 := by linarith
    have h28 : log 28 ≤ log 7 + log 28 := by
      have : 0 ≤ log (7 : ℝ) := log_nonneg (by norm_num)
      linarith
    have hb : b1 * l = 2 * sqrt (x + 2) * l + l + 2 * s * l := by rw [hb1]; ring
    have e9 : (4 / 3) * ((x + 1) * l ^ 2) = x * l ^ 2 + (x / 3 + 4 / 3) * l ^ 2 := by ring
    rw [h5] at h4
    have h7 : 0 ≤ log (7 : ℝ) := log_nonneg (by norm_num)
    have h2l : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
    have hMe : M = x * l ^ 2 + 2 * s * l + log q + log p := hM
    have he : e0 = log q + log p + log 28 + log 2 := he0
    linarith
  have hvis : ∀ θ : ℝ, 1 / 10 < nd (((1 : ℤ) : ℝ) * θ) →
      (∃ n : Fin Nq, 1 ≤ q ^ (2 * (n : ℕ) + 1) / D ∧
          c ≤ ((q ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℝ) * nd ((q : ℝ) ^ ((n : ℕ) ^ 2) * θ))
      ∨ (∃ n : Fin Np, 1 ≤ p ^ (2 * (n : ℕ) + 1) / D ∧
          c ≤ ((p ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℝ) * nd ((p : ℝ) ^ ((n : ℕ) ^ 2) * θ)) := by
    intro θ hθ
    rw [Int.cast_one, one_mul] at hθ
    rcases hD1 D hD1D θ hθ with ⟨n, h1, h2, h3⟩ | ⟨n, h1, h2, h3⟩
    · exact Or.inl ⟨⟨n, hNq n h1⟩, h2, h3⟩
    · exact Or.inr ⟨⟨n, hNp n h1⟩, h2, h3⟩
  obtain ⟨k, hkq, hkp, hksize⟩ :=
    witness_of_dual_dilated hp hq hDnat 1 h2cH hR hR1 hh1 hlogcond hvis
  -- the radius is at most `ε`
  have hrad : 4 * (hh : ℝ) * H / D ≤ ε := by
    rw [div_le_iff₀ hD0]
    have h1 : (D : ℝ) ^ (1 - δ) * (D : ℝ) ^ δ = D := by
      rw [← rpow_add hD0, show 1 - δ + δ = 1 by ring, rpow_one]
    have h2 : exp ((1 + τ) * L) ≤ (D : ℝ) ^ δ := by
      rw [rpow_def_of_pos hD0, exp_le_exp, ← hl]
      have h3 := mul_le_mul_of_nonneg_right hlge hδ0.le
      have e : a * L * δ = (1 + τ) * L := by rw [ha]; field_simp
      linarith
    have h4 : 8 * (hh : ℝ) ≤ exp (τ * L) := by
      refine le_trans ?_ h8
      have h5 := pow_le_pow_left₀ hlnn hlle 2
      have h6 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ 8 * (x + 2) by positivity)
      linarith
    have h7 : 8 * (hh : ℝ) ≤ ε * (D : ℝ) ^ δ := by
      have e : exp (τ * L) = ε * exp ((1 + τ) * L) := by
        rw [← hexp, ← exp_add]
        congr 1
        ring
      rw [e] at h4
      exact le_trans h4 (mul_le_mul_of_nonneg_left h2 hεp.le)
    have h9 : 4 * (hh : ℝ) * H ≤ 4 * hh * (2 * (D : ℝ) ^ (1 - δ)) :=
      mul_le_mul_of_nonneg_left hHle (by positivity)
    have h10 := mul_le_mul_of_nonneg_right h7 (show (0 : ℝ) ≤ (D : ℝ) ^ (1 - δ) by positivity)
    have e2 : ε * (D : ℝ) ^ δ * (D : ℝ) ^ (1 - δ) = ε * D := by
      rw [mul_assoc, mul_comm ((D : ℝ) ^ δ), h1]
    have e3 : 4 * (hh : ℝ) * (2 * (D : ℝ) ^ (1 - δ)) = 8 * hh * (D : ℝ) ^ (1 - δ) := by ring
    linarith
  refine ⟨k, ?_, Small.mono hkq hrad, Small.mono hkp hrad⟩
  -- the height
  have hε1 : ε ≤ 1 := by
    have h1 : ε < exp (-1) := lt_of_lt_of_le hεl (min_le_right _ _)
    have h2 : exp (-1 : ℝ) ≤ 1 := by
      have := exp_le_exp.mpr (show (-1 : ℝ) ≤ 0 by norm_num)
      rwa [exp_zero] at this
    linarith
  have h1 : |(k : ℝ)| ≤ exp M := by
    refine le_trans hksize (le_trans ?_ hqM)
    exact mul_le_of_le_one_left hqpos.le (le_trans hrad hε1)
  refine le_trans h1 (exp_le_exp.mpr ?_)
  have h2 : x * l ^ 2 ≤ x * (a * L + 1) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlnn hlle 2) hx.le
  have h3 : 2 * s * l ≤ 2 * s * (a * L + 1) := mul_le_mul_of_nonneg_left hlle (by positivity)
  have h4 : 0 ≤ log (28 : ℝ) := log_nonneg (by norm_num)
  have h5 : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have e : x * (a * L + 1) ^ 2 = x * a ^ 2 * L ^ 2 + x * (2 * a * L + 1) := by ring
  rw [hM]
  rw [he0] at hquad
  nlinarith [hquad]

/-- The case of thresholds `D^(-τ)` for all small `τ`: every constant above `x₀`. -/
theorem claimU_of_dual_condition {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) {x0 : ℝ} (hx0 : 0 < x0)
    (h : ∀ x : ℝ, x0 < x → ∀ τ : ℝ, 0 < τ → ∃ D1 : ℕ, ∀ D : ℕ, D1 ≤ D → ∀ θ : ℝ,
      1 / 10 < nd θ → Visible q D x ((D : ℝ) ^ (-τ)) θ ∨ Visible p D x ((D : ℝ) ^ (-τ)) θ)
    (C : ℝ) (hC : x0 < C) : ClaimU p q C := by
  set x : ℝ := (x0 + C) / 2 with hx
  have hx1 : x0 < x := by rw [hx]; linarith
  have hx2 : x < C := by rw [hx]; linarith
  have hxpos : 0 < x := by linarith
  have hC0 : 0 < C := by linarith
  -- choose `τ` with `x / (1 - τ)^2 < C`
  set τ : ℝ := (C - x) / (4 * C) with hτ
  have hτ0 : 0 < τ := div_pos (by linarith) (by linarith)
  have hτ1 : τ < 1 / 4 := by
    rw [hτ, div_lt_iff₀ (by linarith)]
    linarith
  have hkey : x / (1 - τ) ^ 2 < C := by
    have hpos : 0 < (1 - τ) ^ 2 := by
      have : 0 < 1 - τ := by linarith
      positivity
    rw [div_lt_iff₀ hpos]
    have h1 : C * τ = (C - x) / 4 := by rw [hτ]; field_simp
    have h2 : 0 ≤ C * τ ^ 2 := mul_nonneg hC0.le (sq_nonneg _)
    have e : C * (1 - τ) ^ 2 = C - 2 * (C * τ) + C * τ ^ 2 := by ring
    rw [e]; linarith
  refine claimU_of_visible hp hq hxpos (δ := 1 - τ) (by linarith) (by linarith) ?_ C hkey
  have e : (1 : ℝ) - τ - 1 = -τ := by ring
  rw [e]
  exact h x hx1 τ hτ0

/-! ## The range claim is a density statement -/

/-- A nonzero integer which is small at every level is large. -/
lemma large_of_small {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {m : ℤ}
    (hm : m ≠ 0) (h : Small p ε m) :
    ∃ n : ℕ, 1 / (2 * ε) < (p : ℝ) ^ (2 * n + 1) ∧ (p : ℝ) ^ (n ^ 2) ≤ 2 * |(m : ℝ)| := by
  classical
  have hpr : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hex : ∃ N : ℕ, 2 * |(m : ℝ)| < (p : ℝ) ^ (N ^ 2) := exists_height hp _
  set N := Nat.find hex with hN
  have hspec : 2 * |(m : ℝ)| < (p : ℝ) ^ (N ^ 2) := Nat.find_spec hex
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    have : 1 ≤ |m| := Int.one_le_abs hm
    exact_mod_cast this
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0] at hspec
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero] at hspec
    linarith
  obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hle : (p : ℝ) ^ (n ^ 2) ≤ 2 * |(m : ℝ)| := by
    have := Nat.find_min hex (show n < N by omega)
    exact not_lt.mp this
  refine ⟨n, ?_, hle⟩
  -- at the level `N` the norm is `|m| / p^(N^2)`
  have hpos : (0 : ℝ) < (p : ℝ) ^ (N ^ 2) := by
    have : (0 : ℝ) < p := by linarith
    positivity
  have hround : round ((m : ℝ) / (p : ℝ) ^ (N ^ 2)) = 0 := by
    rw [round_eq_zero_iff, Set.mem_Ico]
    have h1 : |(m : ℝ) / (p : ℝ) ^ (N ^ 2)| < 1 / 2 := by
      rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
      linarith
    have h2 := abs_lt.mp h1
    exact ⟨by linarith, h2.2⟩
  have h3 := h N
  rw [hround, Int.cast_zero, sub_zero, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos] at h3
  have h4 : (p : ℝ) ^ (N ^ 2) = (p : ℝ) ^ (2 * n + 1) * (p : ℝ) ^ (n ^ 2) := by
    rw [← pow_add, hn]
    congr 1
    ring
  rw [h4] at h3
  have h5 : |(m : ℝ)| < ε * (p : ℝ) ^ (2 * n + 1) * (2 * |(m : ℝ)|) := by
    refine lt_of_lt_of_le h3 ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hle (by positivity)) hε.le
  have h6 : 1 < 2 * ε * (p : ℝ) ^ (2 * n + 1) := by
    have h7 : |(m : ℝ)| * 1 < |(m : ℝ)| * (2 * ε * (p : ℝ) ^ (2 * n + 1)) := by
      rw [mul_one]
      refine lt_of_lt_of_le h5 (le_of_eq ?_)
      ring
    exact lt_of_mul_lt_mul_left h7 (by positivity)
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- The least levels exist, and `ln G` is at most `ln² D / (4 ln p) + O(ln D)`. -/
lemma exists_G {p q D : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hD : 1 ≤ D) :
    ∃ G : ℕ, IsG p q D G ∧ 1 ≤ G ∧ log G ≤ (log D / log p + 1) ^ 2 / 4 * log q
      ∧ log G ≤ (log D) ^ 2 / (4 * log p) + (log D / 2) * (log q / log p) + log q := by
  classical
  have hq : 2 ≤ q := le_trans hp hpq
  have hex : ∀ r : ℕ, 2 ≤ r → ∃ m : ℕ, D < r ^ (2 * m + 1) := by
    intro r hr
    refine ⟨D, lt_of_lt_of_le (Nat.lt_pow_self (by omega : 1 < r)) ?_⟩
    exact Nat.pow_le_pow_right (by omega) (by omega)
  set m := Nat.find (hex q hq) with hm
  set n := Nat.find (hex p hp) with hn
  have hms : D < q ^ (2 * m + 1) := Nat.find_spec (hex q hq)
  have hns : D < p ^ (2 * n + 1) := Nat.find_spec (hex p hp)
  have hlD : 0 ≤ log (D : ℝ) := log_nonneg (by exact_mod_cast hD)
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < p))
  have hlq : 0 < log (q : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlpq : log (p : ℝ) ≤ log q :=
    log_le_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast hpq)
  have hbound : ∀ (r : ℕ) (hr : 2 ≤ r), (Nat.find (hex r hr) : ℝ) ≤ (log D / log r + 1) / 2 := by
    intro r hr
    have hlr : 0 < log (r : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < r))
    set k := Nat.find (hex r hr) with hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, Nat.cast_zero]
      have : 0 ≤ log D / log r := div_nonneg hlD hlr.le
      linarith
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 : r ^ (2 * j + 1) ≤ D :=
      not_lt.mp (Nat.find_min (hex r hr) (show j < Nat.find (hex r hr) by omega))
    have h2 : ((2 * j + 1 : ℕ) : ℝ) * log r ≤ log D := by
      have h3 : ((r : ℝ)) ^ (2 * j + 1) ≤ D := by exact_mod_cast h1
      have h4 : (0 : ℝ) < (r : ℝ) ^ (2 * j + 1) := by
        have : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
        positivity
      have := log_le_log h4 h3
      rwa [log_pow] at this
    have h5 : ((2 * j + 1 : ℕ) : ℝ) ≤ log D / log r := (le_div_iff₀ hlr).mpr h2
    rw [hj]
    push_cast at h5 ⊢
    linarith
  have hGpos : 1 ≤ max (q ^ (m ^ 2)) (p ^ (n ^ 2)) :=
    le_trans (Nat.one_le_pow _ _ (by omega)) (le_max_left _ _)
  set a : ℝ := (log D / log p + 1) / 2 with ha
  have ha0 : 0 ≤ a := by
    have : 0 ≤ log D / log p := div_nonneg hlD hlp.le
    rw [ha]; linarith
  have hmA : (m : ℝ) ≤ a := by
    refine le_trans (hbound q hq) ?_
    have : log D / log q ≤ log D / log p := div_le_div_of_nonneg_left hlD hlp hlpq
    rw [ha]; linarith
  have hnA : (n : ℝ) ≤ a := hbound p hp
  have hlogG : log ((max (q ^ (m ^ 2)) (p ^ (n ^ 2)) : ℕ) : ℝ) ≤ a ^ 2 * log q := by
    have hm2 : (m : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmA 2
    have hn2 : (n : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnA 2
    rcases max_choice (q ^ (m ^ 2)) (p ^ (n ^ 2)) with h | h <;> rw [h] <;> push_cast <;>
      rw [log_pow] <;> push_cast
    · exact mul_le_mul_of_nonneg_right hm2 hlq.le
    · exact mul_le_mul hn2 hlpq hlp.le (sq_nonneg _)
  have hlogG2 : log ((max (q ^ (m ^ 2)) (p ^ (n ^ 2)) : ℕ) : ℝ)
      ≤ (log D) ^ 2 / (4 * log p) + (log D / 2) * (log q / log p) + log q := by
    -- the level of `q` is computed with `ln q`, the level of `p` with `ln p`
    have hB : (m : ℝ) ≤ (log D / log q + 1) / 2 := hbound q hq
    have hcase : ∀ (r : ℕ) (k : ℕ), 2 ≤ r → p ≤ r → r ≤ q → (k : ℝ) ≤ (log D / log r + 1) / 2 →
        (k : ℝ) ^ 2 * log r
          ≤ (log D) ^ 2 / (4 * log p) + (log D / 2) * (log q / log p) + log q := by
      intro r k hr hpr hrq hk
      have hlr : 0 < log (r : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < r))
      have hlpr : log (p : ℝ) ≤ log r :=
        log_le_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast hpr)
      have hlrq : log (r : ℝ) ≤ log q :=
        log_le_log (by exact_mod_cast (by omega : 0 < r)) (by exact_mod_cast hrq)
      have h1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg k) hk 2) hlr.le
      have e : ((log D / log r + 1) / 2) ^ 2 * log r
          = (log D) ^ 2 / (4 * log r) + log D / 2 + log r / 4 := by
        field_simp
        ring
      have h2 : (log D) ^ 2 / (4 * log r) ≤ (log D) ^ 2 / (4 * log p) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
      have h3 : log D / 2 ≤ (log D / 2) * (log q / log p) := by
        refine le_mul_of_one_le_right (by linarith) ?_
        rw [one_le_div hlp]
        exact hlpq
      rw [e] at h1
      linarith
    rcases max_choice (q ^ (m ^ 2)) (p ^ (n ^ 2)) with h | h <;> rw [h] <;> push_cast <;>
      rw [log_pow] <;> push_cast
    · exact hcase q m hq hpq le_rfl hB
    · exact hcase p n hp le_rfl hpq (hbound p hp)
  refine ⟨_, ⟨m, n, hms, hns, rfl⟩, hGpos, ?_, hlogG2⟩
  have e : (log D / log p + 1) ^ 2 / 4 = a ^ 2 := by rw [ha]; ring
  rw [e]
  exact hlogG

lemma inv_le_dist {q : ℕ} (hq : 2 ≤ q) (m : ℤ) : 1 / (q : ℝ) ≤ |1 / (q : ℝ) - m| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h1 : 1 / (q : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hq)
  have h2 : 0 < 1 / (q : ℝ) := by positivity
  rcases lt_trichotomy m 0 with h | h | h
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [h, Int.cast_zero, sub_zero, abs_of_pos h2]
  · have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

set_option maxHeartbeats 2000000 in
theorem density_of_claimA {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) {B1 B : ℝ} (hB1 : 0 < B1)
    (hB : B1 < B) (hA : ClaimA p q B1) :
    ∃ K : ℝ, ∃ D1 : ℕ, ∀ D : ℕ, D1 ≤ D → ∃ X G : ℕ, IsG p q D G ∧ 2 * G ≤ X
      ∧ log X ≤ B * log D ^ 2 ∧ Carries p q D X K := by
  have hq : 2 ≤ q := by omega
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < p))
  have hlq : 0 < log (q : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < q))
  have hpr : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  -- the radius exponent
  set τ : ℝ := min 1 ((B - B1) / (4 * B1)) with hτ
  have hτ0 : 0 < τ := lt_min one_pos (div_pos (by linarith) (by linarith))
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτB : B1 * (1 + τ) ^ 2 < B := by
    have h1 : τ ≤ (B - B1) / (4 * B1) := min_le_right _ _
    have h2 : τ * (4 * B1) ≤ B - B1 := (le_div_iff₀ (by linarith)).mp h1
    have h4 : τ ^ 2 ≤ τ := by
      have := mul_le_mul_of_nonneg_left hτ1 hτ0.le
      nlinarith
    have h3 : B1 * τ ^ 2 ≤ B1 * τ := mul_le_mul_of_nonneg_left h4 hB1.le
    have e : B1 * (1 + τ) ^ 2 = B1 + 2 * (B1 * τ) + B1 * τ ^ 2 := by ring
    rw [e]
    linarith
  obtain ⟨η, hη, ε0, hε0, hAA⟩ := hA
  set η' : ℝ := min η 1 with hη'
  have hη'0 : 0 < η' := lt_min hη one_pos
  have hη'1 : η' ≤ 1 := min_le_right _ _
  set gap : ℝ := (1 + τ) ^ 2 / (4 * log p) - 1 / (4 * log p) with hgap
  have hgap0 : 0 < gap := by
    rw [hgap, ← sub_div]
    refine div_pos ?_ (by linarith)
    have : 0 < τ ^ 2 := by positivity
    nlinarith
  set m0 : ℝ := min ε0 (min (1 / (2 * (q : ℝ))) (1 / 4)) with hm0
  have hm0pos : 0 < m0 := by
    refine lt_min hε0 (lt_min ?_ (by norm_num))
    positivity
  set b1 : ℝ := (log q / log p) / 2 + (1 + τ) * log (2 * p) / (2 * log p) with hb1
  have hev : ∀ᶠ l : ℝ in atTop, 1 ≤ l ∧ -log m0 < l ∧ log 2 + 5 * log p ≤ l
      ∧ log 2 ≤ (B - B1 * (1 + τ) ^ 2) * l ^ 2
      ∧ b1 * l + (log q + log 8) ≤ gap * l ^ 2 := by
    refine (eventually_ge_atTop 1).and (Filter.Eventually.and (eventually_gt_atTop _)
      (Filter.Eventually.and (eventually_ge_atTop _)
        (Filter.Eventually.and ?_ (eventually_quad hgap0 _ _))))
    filter_upwards [eventually_quad (show 0 < B - B1 * (1 + τ) ^ 2 by linarith) 0 (log 2)] with l hl
    simpa using hl
  obtain ⟨l0, hl0⟩ := eventually_atTop.mp hev
  refine ⟨2 / η', ⌈exp l0⌉₊ + 1, fun D hD => ?_⟩
  have hDge : exp l0 ≤ D := le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : ⌈exp l0⌉₊ ≤ D))
  have hD1 : 1 ≤ D := by omega
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le (exp_pos _) hDge
  set l := log (D : ℝ) with hl
  have hl0l : l0 ≤ l := by
    have := log_le_log (exp_pos _) hDge
    rwa [log_exp] at this
  obtain ⟨hl1, hlsmall, hlbig, hl2, hlgap⟩ := hl0 l hl0l
  have hlnn : 0 ≤ l := by linarith
  set ε : ℝ := exp (-((1 + τ) * l)) with hε
  have hεpos : 0 < ε := exp_pos _
  have hlτ : l ≤ (1 + τ) * l := le_mul_of_one_le_left hlnn (by linarith)
  have hεm : ε < m0 := by
    have h1 : ε < exp (log m0) := by
      rw [hε, exp_lt_exp]
      linarith
    rwa [exp_log hm0pos] at h1
  have hεε0 : ε < ε0 := lt_of_lt_of_le hεm (min_le_left _ _)
  have hεq : ε < 1 / (2 * (q : ℝ)) :=
    lt_of_lt_of_le hεm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε4 : ε < 1 / 4 :=
    lt_of_lt_of_le hεm (le_trans (min_le_right _ _) (min_le_right _ _))
  have hεD : ε ≤ 1 / D := by
    have e : (1 : ℝ) / D = exp (-l) := by rw [exp_neg, hl, exp_log hD0, one_div]
    rw [e, hε, exp_le_exp]
    linarith
  have hlogε : log (1 / ε) = (1 + τ) * l := by
    rw [one_div, log_inv, hε, log_exp, neg_neg]
  obtain ⟨X0, hX1, hX2, hX3⟩ := hAA ε hεpos hεε0
  rw [hlogε] at hX2
  have hX0pos : 0 < X0 := lt_of_lt_of_le (div_pos one_pos hη) hX1
  have hηX : 1 ≤ η * X0 := by
    rw [div_le_iff₀ hη] at hX1
    linarith
  -- the unit target
  obtain ⟨k1, hk1, hk1q, hk1p⟩ := hX3 1 (by rw [Int.cast_one, abs_one]; exact hηX)
  have hk1ne : k1 - 1 ≠ 0 := by
    intro h0
    have hk : k1 = 1 := by omega
    have h1 := hk1q 1
    rw [hk] at h1
    simp only [Int.cast_one, one_pow, pow_one] at h1
    have h2 := inv_le_dist hq (round (1 / (q : ℝ)))
    have h3 : (1 : ℝ) / (2 * q) < 1 / q :=
      one_div_lt_one_div_of_lt hqr (by linarith)
    linarith
  obtain ⟨n, hn1, hn2⟩ := large_of_small hp hεpos (by linarith) hk1ne hk1p
  -- the level found is high
  have hnl : (1 + τ) * l - log 2 ≤ (2 * (n : ℝ) + 1) * log p := by
    have h1 : 0 < 1 / (2 * ε) := by positivity
    have h2 := log_le_log h1 hn1.le
    rw [log_pow, one_div, log_inv, log_mul two_ne_zero hεpos.ne', hε, log_exp] at h2
    push_cast at h2
    linarith
  have hn2le : 2 ≤ n := by
    by_contra hc
    have h1 : (n : ℝ) ≤ 1 := by exact_mod_cast (by omega : n ≤ 1)
    have h2 := mul_le_mul_of_nonneg_right (show 2 * (n : ℝ) + 1 ≤ 3 by linarith) hlp.le
    linarith
  have hpn : (16 : ℝ) ≤ (p : ℝ) ^ (n ^ 2) := by
    have h1 : (2 : ℝ) ^ 4 ≤ (p : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp) 4
    have h2 : (p : ℝ) ^ 4 ≤ (p : ℝ) ^ (n ^ 2) :=
      pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ p))
        (le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_left hn2le 2))
    refine le_trans (le_of_eq (by norm_num)) (le_trans h1 h2)
  have habs : |((k1 - 1 : ℤ) : ℝ)| ≤ X0 + 1 := by
    rw [Int.cast_sub, Int.cast_one]
    refine le_trans (abs_sub _ _) ?_
    rw [abs_one]
    linarith
  have hX01 : 1 ≤ X0 := by linarith
  have hpX : (p : ℝ) ^ (n ^ 2) ≤ 4 * X0 := by linarith
  have hlogX0 : (n : ℝ) ^ 2 * log p - log 4 ≤ log X0 := by
    have h1 := log_le_log (by positivity : (0 : ℝ) < (p : ℝ) ^ (n ^ 2)) hpX
    rw [log_pow, log_mul (by norm_num) hX0pos.ne', Nat.cast_pow] at h1
    linarith
  have hlow : (1 + τ) ^ 2 / (4 * log p) * l ^ 2 - (1 + τ) * log (2 * p) / (2 * log p) * l
      ≤ (n : ℝ) ^ 2 * log p := by
    set a : ℝ := ((1 + τ) * l - log (2 * p)) / (2 * log p) with ha
    have hlog2p : log (2 * (p : ℝ)) = log 2 + log p := log_mul two_ne_zero hpr.ne'
    have ha0 : 0 ≤ a := by
      refine div_nonneg ?_ (by linarith)
      rw [hlog2p]
      linarith
    have han : a ≤ n := by
      rw [ha, div_le_iff₀ (by linarith), hlog2p]
      have e : (n : ℝ) * (2 * log p) = (2 * (n : ℝ) + 1) * log p - log p := by ring
      rw [e]
      linarith
    have h1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha0 han 2) hlp.le
    have e : a ^ 2 * log p = (1 + τ) ^ 2 / (4 * log p) * l ^ 2
        - (1 + τ) * log (2 * p) / (2 * log p) * l + log (2 * p) ^ 2 / (4 * log p) := by
      rw [ha]
      field_simp
      ring
    have h2 : 0 ≤ log (2 * (p : ℝ)) ^ 2 / (4 * log p) := div_nonneg (sq_nonneg _) (by linarith)
    rw [e] at h1
    linarith
  obtain ⟨G, hG, hG1, _, hlogG⟩ := exists_G hp hpq.le hD1
  -- the height
  set F : ℕ := ⌊X0⌋₊ with hF
  have hFle : (F : ℝ) ≤ X0 := Nat.floor_le hX0pos.le
  have hFgt : X0 < F + 1 := Nat.lt_floor_add_one X0
  have hF1 : 1 ≤ F := Nat.le_floor (by exact_mod_cast hX01)
  have hF1r : (1 : ℝ) ≤ F := by exact_mod_cast hF1
  have hXge : X0 ≤ ((2 * F : ℕ) : ℝ) := by push_cast; linarith
  have hXpos : (0 : ℝ) < ((2 * F : ℕ) : ℝ) := lt_of_lt_of_le hX0pos hXge
  have h2G : 2 * G ≤ 2 * F := by
    have hGr : (0 : ℝ) < G := by exact_mod_cast hG1
    have h1 : log (2 * (G : ℝ)) ≤ log X0 := by
      rw [log_mul two_ne_zero hGr.ne']
      have e8 : log (8 : ℝ) = log 2 + log 4 := by
        rw [← log_mul two_ne_zero (by norm_num)]
        norm_num
      have eg : gap * l ^ 2 = (1 + τ) ^ 2 / (4 * log p) * l ^ 2 - l ^ 2 / (4 * log p) := by
        rw [hgap]; ring
      have eb : b1 * l = (l / 2) * (log q / log p)
          + (1 + τ) * log (2 * p) / (2 * log p) * l := by rw [hb1]; ring
      linarith
    have h2 : (2 : ℝ) * G ≤ X0 := (log_le_log_iff (by positivity) hX0pos).mp h1
    have h3 : ((2 * G : ℕ) : ℝ) ≤ ((2 * F : ℕ) : ℝ) := by
      push_cast
      push_cast at hXge
      linarith
    exact_mod_cast h3
  refine ⟨2 * F, G, hG, h2G, ?_, ?_⟩
  · have h1 : ((2 * F : ℕ) : ℝ) ≤ 2 * X0 := by push_cast; linarith
    have h2 := log_le_log hXpos h1
    rw [log_mul two_ne_zero hX0pos.ne'] at h2
    have h3 : log X0 ≤ B1 * ((1 + τ) * l) ^ 2 := by
      have := log_le_log hX0pos hX2
      rwa [log_exp] at this
    have e : B1 * ((1 + τ) * l) ^ 2 = B1 * (1 + τ) ^ 2 * l ^ 2 := by ring
    have e2 : (B - B1 * (1 + τ) ^ 2) * l ^ 2 = B * l ^ 2 - B1 * (1 + τ) ^ 2 * l ^ 2 := by ring
    linarith
  · set T : ℕ := ⌊η' * X0⌋₊ with hT
    have hTle : (T : ℝ) ≤ η' * X0 := Nat.floor_le (mul_nonneg hη'0.le hX0pos.le)
    have hTgt : η' * X0 < T + 1 := Nat.lt_floor_add_one _
    have hηX' : 1 ≤ η' * X0 := by
      rcases min_choice η 1 with h | h
      · rw [hη', h]; exact hηX
      · rw [hη', h, one_mul]; exact hX01
    have hT1 : 1 ≤ T := Nat.le_floor (by exact_mod_cast hηX')
    have hTF : T ≤ F := Nat.floor_le_floor (mul_le_of_le_one_left hX0pos.le hη'1)
    refine ⟨Icc (-(T : ℤ)) T, ?_, fun w hw => ?_⟩
    · have hc : (Icc (-(T : ℤ)) T).card = 2 * T + 1 := by
        rw [Int.card_Icc]; omega
      rw [hc, div_mul_eq_mul_div, le_div_iff₀ hη'0]
      have h1 : ((2 * F : ℕ) : ℝ) * η' ≤ 2 * (η' * X0) := by
        have h2 := mul_le_mul_of_nonneg_right hFle hη'0.le
        push_cast
        nlinarith
      have h3 : (1 : ℝ) ≤ T := by exact_mod_cast hT1
      push_cast
      push_cast at h1
      linarith
    · rw [mem_Icc, ← abs_le] at hw
      have hwr : |(w : ℝ)| ≤ η * X0 := by
        have h1 : |(w : ℝ)| ≤ T := by exact_mod_cast hw
        exact le_trans h1 (le_trans hTle
          (mul_le_mul_of_nonneg_right (min_le_left _ _) hX0pos.le))
      obtain ⟨k, hk, hkq, hkp⟩ := hX3 w hwr
      have hkF : |k| ≤ (F : ℤ) := by
        have h1 : k.natAbs ≤ F := by
          refine Nat.le_floor ?_
          rw [Nat.cast_natAbs, Int.cast_abs]
          exact hk
        rw [Int.abs_eq_natAbs]
        exact_mod_cast h1
      have hwF : |w| ≤ (F : ℤ) := le_trans hw (by exact_mod_cast hTF)
      refine ⟨k, k - w, by ring, ?_, ?_, Small.mono hkq hεD, Small.mono hkp hεD⟩
      · push_cast; omega
      · have := abs_sub k w
        push_cast
        omega

/-- **The range claim is a density statement.** -/
theorem claimA_iff_density {p q : ℕ} (hp : 2 ≤ p) (hpq : p < q) (hco : Nat.Coprime p q)
    {B0 : ℝ} (hB0 : 0 ≤ B0) :
    (∀ B : ℝ, B0 < B → ClaimA p q B) ↔
      (∀ B : ℝ, B0 < B → ∃ K : ℝ, ∃ D1 : ℕ, ∀ D : ℕ, D1 ≤ D → ∃ X G : ℕ, IsG p q D G
        ∧ 2 * G ≤ X ∧ log X ≤ B * log D ^ 2 ∧ Carries p q D X K) := by
  have hq : 2 ≤ q := by omega
  constructor
  · intro h B hB
    have h1 : B0 < (B0 + B) / 2 := by linarith
    exact density_of_claimA hp hpq (by linarith) (by linarith) (h _ h1)
  · intro h B hB
    set x : ℝ := (B0 + B) / 2 with hx
    have hx1 : B0 < x := by rw [hx]; linarith
    have hxB : x < B := by rw [hx]; linarith
    have hx0 : 0 < x := by linarith
    obtain ⟨K, D1, hK⟩ := h x hx1
    refine claimA_of_density hp hq hco hx0 (K := max K 1) (le_max_right _ _) (fun θ hθ => ?_) B hxB
    have hev : ∀ᶠ D0 : ℝ in atTop, (D1 : ℝ) ≤ D0 ∧ 1 ≤ D0 ∧ 2 ≤ D0 ^ θ :=
      (eventually_ge_atTop _).and ((eventually_ge_atTop _).and
        ((tendsto_rpow_atTop hθ).eventually_ge_atTop 2))
    obtain ⟨A, hA⟩ := eventually_atTop.mp hev
    refine ⟨A, fun D0 hD0 => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hA D0 hD0
    have h4 : D0 ≤ (⌈D0⌉₊ : ℝ) := Nat.le_ceil _
    have hD1 : D1 ≤ ⌈D0⌉₊ := by exact_mod_cast le_trans h1 h4
    obtain ⟨X, G, hG, h2G, hlog, W, hW, hWm⟩ := hK _ hD1
    refine ⟨⌈D0⌉₊, X, G, h4, ?_, hG, h2G, hlog, W, ?_, hWm⟩
    · have h5 : (⌈D0⌉₊ : ℝ) ≤ D0 + 1 := (Nat.ceil_lt_add_one (by linarith)).le
      have h6 : D0 ^ (1 + θ) = D0 * D0 ^ θ := by
        rw [rpow_add (by linarith), rpow_one]
      have h7 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ D0 by linarith)
      rw [h6]
      linarith
    · exact le_trans hW (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))

end TwoPrimesClaims
