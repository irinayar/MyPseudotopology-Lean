import LeanCheck.MixedPrimeFlat
import LeanCheck.MixedPrimeRadii

/-!
# TVGaddmore_v17: sparse series (Lemma "sparse-tail", Proposition "sparse-tests", part (b))

`x = ∑_s 1 / q_s` with `q_s = 2^(n_s^2)`, `n` strictly increasing with `n_s ≥ 1`.
Indices start at `0`; the paper's `q_J ∣ k` clears the terms `s ≤ J`, the active term is `s = J+1`,
and the tail is `T_J = ∑_{s ≥ J+2} 1/q_s`, `Q_J = q_{J+2}`.
-/

namespace LeanCheck
namespace MixedPrime

/-- `q_s = 2^(n_s^2)`. -/
def qs (n : ℕ → ℕ) (s : ℕ) : ℕ := 2 ^ (n s ^ 2)

/-- The sparse parameter. -/
noncomputable def xs (n : ℕ → ℕ) : ℝ := ∑' s, 1 / (qs n s : ℝ)

/-- The tail beyond the active term. -/
noncomputable def Tl (n : ℕ → ℕ) (J : ℕ) : ℝ := ∑' m, 1 / (qs n (m + (J + 2)) : ℝ)

section sparse
variable {n : ℕ → ℕ} (hn1 : ∀ s, 1 ≤ n s) (hnm : StrictMono n)
include hn1 hnm

lemma qs_pos (s : ℕ) : 0 < qs n s := by unfold qs; positivity

lemma qs_dvd {s t : ℕ} (h : s ≤ t) : qs n s ∣ qs n t := by
  unfold qs
  apply Nat.pow_dvd_pow
  have : n s ≤ n t := hnm.monotone h
  nlinarith

lemma qs_ratio (s : ℕ) : 8 * qs n s ≤ qs n (s + 1) := by
  unfold qs
  have h1 : n s + 1 ≤ n (s + 1) := hnm (Nat.lt_succ_self s)
  have h2 : n s ^ 2 + 3 ≤ n (s + 1) ^ 2 := by nlinarith [hn1 s]
  calc 8 * 2 ^ (n s ^ 2) = 2 ^ (n s ^ 2 + 3) := by rw [pow_add]; norm_num; ring
    _ ≤ 2 ^ (n (s + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) h2

lemma qs_ratio_iter (s m : ℕ) : 8 ^ m * qs n s ≤ qs n (s + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc 8 ^ (m + 1) * qs n s = 8 * (8 ^ m * qs n s) := by ring
      _ ≤ 8 * qs n (s + m) := by gcongr
      _ ≤ qs n (s + m + 1) := qs_ratio hn1 hnm _

lemma summable_inv_qs : Summable fun s => 1 / (qs n s : ℝ) := by
  have hs : Summable fun s : ℕ => (1 / 8 : ℝ) ^ s := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_nonneg_of_le (fun s => by positivity) (fun s => ?_) hs
  have h0 : 0 < qs n 0 := qs_pos hn1 hnm 0
  have h := qs_ratio_iter hn1 hnm 0 s
  simp only [zero_add] at h
  have hq0 : (1 : ℝ) ≤ qs n 0 := by exact_mod_cast h0
  have h8 : (8 : ℝ) ^ s ≤ qs n s := by
    have : ((8 ^ s * qs n 0 : ℕ) : ℝ) ≤ qs n s := by exact_mod_cast h
    push_cast at this
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 8) s]
  have hp : (0 : ℝ) < 8 ^ s := by positivity
  calc 1 / (qs n s : ℝ) ≤ 1 / (8 : ℝ) ^ s := one_div_le_one_div_of_le hp h8
    _ = (1 / 8 : ℝ) ^ s := by rw [one_div_pow]

/-- Tail bounds `1/Q ≤ T_J ≤ 2/Q`, `Q = q_{J+2}`. -/
lemma Tl_bounds (J : ℕ) :
    1 / (qs n (J + 2) : ℝ) ≤ Tl n J ∧ Tl n J ≤ 2 / (qs n (J + 2) : ℝ) := by
  have hsum : Summable fun m => 1 / (qs n (m + (J + 2)) : ℝ) :=
    (summable_nat_add_iff (J + 2)).mpr (summable_inv_qs hn1 hnm)
  have hQ : (0 : ℝ) < qs n (J + 2) := by exact_mod_cast qs_pos hn1 hnm (J + 2)
  constructor
  · have := hsum.le_tsum 0 (fun m _ => by positivity)
    simpa [Tl] using this
  · have hgeo : Summable fun m : ℕ => (1 / 8 : ℝ) ^ m / (qs n (J + 2) : ℝ) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).div_const _
    have hle : ∀ m : ℕ, 1 / (qs n (m + (J + 2)) : ℝ) ≤ (1 / 8 : ℝ) ^ m / (qs n (J + 2) : ℝ) := by
      intro m
      have h := qs_ratio_iter hn1 hnm (J + 2) m
      have h' : (8 : ℝ) ^ m * qs n (J + 2) ≤ qs n (J + 2 + m) := by exact_mod_cast h
      rw [add_comm (J + 2) m] at h'
      have hp : (0 : ℝ) < 8 ^ m * qs n (J + 2) := by positivity
      calc 1 / (qs n (m + (J + 2)) : ℝ) ≤ 1 / ((8 : ℝ) ^ m * qs n (J + 2)) :=
            one_div_le_one_div_of_le hp h'
        _ = (1 / 8 : ℝ) ^ m / (qs n (J + 2) : ℝ) := by rw [one_div_pow]; field_simp
    have h1 : Tl n J ≤ ∑' m : ℕ, (1 / 8 : ℝ) ^ m / (qs n (J + 2) : ℝ) :=
      hsum.tsum_le_tsum hle hgeo
    have h2 : ∑' m : ℕ, (1 / 8 : ℝ) ^ m / (qs n (J + 2) : ℝ) = (8 / 7) / (qs n (J + 2) : ℝ) := by
      rw [tsum_div_const, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
    have h3 : (8 / 7 : ℝ) / (qs n (J + 2) : ℝ) ≤ 2 / (qs n (J + 2) : ℝ) := by
      gcongr; norm_num
    linarith

/-- If `q_J ∣ k` then `k x ≡ k/q_{J+1} + k T_J (mod 1)`. -/
lemma sparse_decomp (J : ℕ) (k : ℤ) (hk : (qs n J : ℤ) ∣ k) :
    ∃ N : ℤ, (k : ℝ) * xs n = (k : ℝ) / (qs n (J + 1) : ℝ) + (k : ℝ) * Tl n J + N := by
  have hsum := summable_inv_qs hn1 hnm
  have hsplit := hsum.sum_add_tsum_nat_add (J + 2)
  have hx : xs n = ∑ s ∈ Finset.range (J + 2), 1 / (qs n s : ℝ) + Tl n J := by
    unfold xs Tl; exact hsplit.symm
  rw [Finset.sum_range_succ] at hx
  -- the integer part
  refine ⟨∑ s ∈ Finset.range (J + 1), k / (qs n s : ℤ), ?_⟩
  have hint : ∀ s ∈ Finset.range (J + 1), (((k / (qs n s : ℤ) : ℤ)) : ℝ) = (k : ℝ) / (qs n s : ℝ) := by
    intro s hs
    have hsJ : s ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    have hd : (qs n s : ℤ) ∣ k := (Int.natCast_dvd_natCast.mpr (qs_dvd hn1 hnm hsJ)).trans hk
    have hne : ((qs n s : ℤ) : ℝ) ≠ 0 := by exact_mod_cast (qs_pos hn1 hnm s).ne'
    rw [Int.cast_div hd hne]; push_cast; rfl
  rw [hx, mul_add, mul_add, Finset.mul_sum]
  push_cast
  rw [Finset.sum_congr rfl hint]
  have : ∑ s ∈ Finset.range (J + 1), (k : ℝ) * (1 / (qs n s : ℝ)) = ∑ s ∈ Finset.range (J + 1), (k : ℝ) / (qs n s : ℝ) :=
    Finset.sum_congr rfl fun s _ => by ring
  rw [this]
  have e : (k : ℝ) * (1 / (qs n (J + 1) : ℝ)) = (k : ℝ) / (qs n (J + 1) : ℝ) := by ring
  rw [e]; ring

/-- Relative tail estimate: `|nrm (k x) - nrm (k / q_{J+1})| ≤ |k| T_J ≤ 2|k| / Q_J`. -/
lemma sparse_tail (J : ℕ) (k : ℤ) (hk : (qs n J : ℤ) ∣ k) :
    |nrm ((k : ℝ) * xs n) - nrm ((k : ℝ) / (qs n (J + 1) : ℝ))| ≤ |(k : ℝ)| * Tl n J ∧
    |(k : ℝ)| * Tl n J ≤ 2 * |(k : ℝ)| / (qs n (J + 2) : ℝ) := by
  obtain ⟨N, hN⟩ := sparse_decomp hn1 hnm J k hk
  obtain ⟨hT1, hT2⟩ := Tl_bounds hn1 hnm J
  have hT0 : 0 ≤ Tl n J := by
    have : (0 : ℝ) < 1 / (qs n (J + 2) : ℝ) := by
      have : (0 : ℝ) < qs n (J + 2) := by exact_mod_cast qs_pos hn1 hnm _
      positivity
    linarith
  constructor
  · rw [hN, nrm_add_int]
    have h1 := nrm_add_le ((k : ℝ) / (qs n (J + 1) : ℝ)) ((k : ℝ) * Tl n J)
    have h2 : nrm ((k : ℝ) * Tl n J) ≤ |(k : ℝ)| * Tl n J := by
      refine (nrm_le_abs _).trans ?_
      rw [abs_mul, abs_of_nonneg hT0]
    have h3 := nrm_add_le ((k : ℝ) / (qs n (J + 1) : ℝ) + (k : ℝ) * Tl n J) (-((k : ℝ) * Tl n J))
    have e : (k : ℝ) / (qs n (J + 1) : ℝ) + (k : ℝ) * Tl n J + -((k : ℝ) * Tl n J)
        = (k : ℝ) / (qs n (J + 1) : ℝ) := by ring
    rw [e, nrm_neg] at h3
    rw [abs_le]
    constructor <;> linarith
  · calc |(k : ℝ)| * Tl n J ≤ |(k : ℝ)| * (2 / (qs n (J + 2) : ℝ)) := by gcongr
      _ = 2 * |(k : ℝ)| / (qs n (J + 2) : ℝ) := by ring

/-- Lower bound for `P` through the first square scale above `2|k|`:
`P(k) ≥ 2^{-(2 √(log₂ (2|k|)) + 2)}`. -/
lemma sqrt_log_lower (k : ℤ) (hk : k ≠ 0) :
    (2 : ℝ) ^ (-(2 * Real.sqrt (Real.logb 2 (2 * |(k : ℝ)|)) + 2)) ≤ Pn (sqScales 2) k := by
  set a : ℝ := |(k : ℝ)| with ha
  have ha1 : 1 ≤ a := by
    have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
    have : (1 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h1
    simpa [ha] using this
  have ha0 : 0 < a := by linarith
  set m : ℝ := Real.logb 2 (2 * a) with hm
  have hm1 : 1 ≤ m := by
    rw [hm, Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    norm_num; linarith
  have h2m : (2 : ℝ) ^ m = 2 * a := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  set sm : ℝ := Real.sqrt m with hsm
  have hsq : sm * sm = m := Real.mul_self_sqrt (by linarith)
  have hsm0 : 0 ≤ sm := Real.sqrt_nonneg _
  have hsm1 : 1 ≤ sm := by
    rw [hsm]; exact Real.one_le_sqrt.mpr hm1
  set n : ℕ := ⌈sm⌉₊ with hn
  have hnle : sm ≤ n := Nat.le_ceil sm
  have hnlt : (n : ℝ) < sm + 1 := Nat.ceil_lt_add_one hsm0
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := hsm1.trans hnle
    exact_mod_cast this
  have hn2a : m ≤ (n : ℝ) ^ 2 := by nlinarith
  have hn2b : (n : ℝ) ^ 2 < m + 2 * sm + 1 := by nlinarith
  have hcast : (2 : ℝ) ^ ((n : ℝ) ^ 2) = (2 : ℝ) ^ (n ^ 2) := by
    rw [show ((n : ℝ) ^ 2) = ((n ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hq1 : 2 * a ≤ (2 : ℝ) ^ (n ^ 2) := by
    calc 2 * a = (2 : ℝ) ^ m := h2m.symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) ^ 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hn2a
      _ = (2 : ℝ) ^ (n ^ 2) := hcast
  have hq2 : (2 : ℝ) ^ (n ^ 2) ≤ 2 * a * (2 : ℝ) ^ (2 * sm + 1) := by
    calc (2 : ℝ) ^ (n ^ 2) = (2 : ℝ) ^ ((n : ℝ) ^ 2) := hcast.symm
      _ ≤ (2 : ℝ) ^ (m + (2 * sm + 1)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 * a * (2 : ℝ) ^ (2 * sm + 1) := by rw [Real.rpow_add (by norm_num), h2m]
  have hqpos : (0 : ℝ) < (2 : ℝ) ^ (n ^ 2) := by positivity
  have hqe : ((2 ^ (n ^ 2) : ℕ) : ℝ) = (2 : ℝ) ^ (n ^ 2) := by push_cast; rfl
  have hmem : (2 ^ (n ^ 2) : ℕ) ∈ sqScales 2 := mem_sqScales hn1
  have hP := le_Pn hmem k
  have habs : |(k : ℝ) / (((2 ^ (n ^ 2) : ℕ)) : ℝ)| = a / (2 : ℝ) ^ (n ^ 2) := by
    rw [abs_div, hqe, abs_of_pos hqpos]
  have hhalf : |(k : ℝ) / (((2 ^ (n ^ 2) : ℕ)) : ℝ)| ≤ 1 / 2 := by
    rw [habs, div_le_iff₀ hqpos]; linarith
  rw [nrm_eq_abs hhalf, habs] at hP
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ (2 * sm + 1) := by positivity
  have hpow : (2 : ℝ) ^ (-(2 * sm + 2)) = 1 / (2 * (2 : ℝ) ^ (2 * sm + 1)) := by
    rw [Real.rpow_neg (by norm_num), show 2 * sm + 2 = (2 * sm + 1) + 1 by ring,
      Real.rpow_add (by norm_num), Real.rpow_one]
    field_simp
  rw [hpow]
  refine le_trans ?_ hP
  rw [div_le_div_iff₀ (by positivity) hqpos]
  nlinarith [hq2, ha0, hp2]

/-- Relative tail estimate: `|k| T_J ≤ (8|k|/Q_J) · 2^{2√(log₂ 2|k|)} · P(k)`. -/
lemma sparse_relative (S : Set ℕ) (hSub : sqScales 2 ⊆ S) (J : ℕ) (k : ℤ) (hk0 : k ≠ 0) :
    |(k : ℝ)| * Tl n J ≤
      (8 * |(k : ℝ)| / (qs n (J + 2) : ℝ)) * (2 : ℝ) ^ (2 * Real.sqrt (Real.logb 2 (2 * |(k : ℝ)|)))
        * Pn S k := by
  obtain ⟨-, hT2⟩ := Tl_bounds hn1 hnm J
  have hQ : (0 : ℝ) < qs n (J + 2) := by exact_mod_cast qs_pos hn1 hnm _
  have hT0 : 0 ≤ Tl n J := by
    have : (0 : ℝ) < 1 / (qs n (J + 2) : ℝ) := by positivity
    linarith [(Tl_bounds hn1 hnm J).1]
  have hP : (2 : ℝ) ^ (-(2 * Real.sqrt (Real.logb 2 (2 * |(k : ℝ)|)) + 2)) ≤ Pn S k :=
    (sqrt_log_lower hn1 hnm k hk0).trans (Pn_mono hSub k)
  set e : ℝ := 2 * Real.sqrt (Real.logb 2 (2 * |(k : ℝ)|)) with he
  have hpe : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hinv : (1 : ℝ) ≤ (4 : ℝ) * (2 : ℝ) ^ e * (2 : ℝ) ^ (-(e + 2)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_add (by norm_num)]
    field_simp
    norm_num
  have hk : (0 : ℝ) ≤ |(k : ℝ)| := abs_nonneg _
  calc |(k : ℝ)| * Tl n J ≤ |(k : ℝ)| * (2 / (qs n (J + 2) : ℝ)) := by gcongr
    _ = (2 * |(k : ℝ)| / (qs n (J + 2) : ℝ)) * 1 := by ring
    _ ≤ (2 * |(k : ℝ)| / (qs n (J + 2) : ℝ)) * ((4 : ℝ) * (2 : ℝ) ^ e * (2 : ℝ) ^ (-(e + 2))) := by
        gcongr
    _ = (8 * |(k : ℝ)| / (qs n (J + 2) : ℝ)) * (2 : ℝ) ^ e * (2 : ℝ) ^ (-(e + 2)) := by ring
    _ ≤ (8 * |(k : ℝ)| / (qs n (J + 2) : ℝ)) * (2 : ℝ) ^ e * Pn S k := by
        gcongr

/-- **Proposition "sparse-tests", part (b)** (one-sided saturation witnesses exclude continuity):
if `x = ∑ 1/q_s` has a Lipschitz bound, there are no witnesses `0 < k ≤ Q_J/4`, `q_J ∣ k`, `P(k) → 0`,
with `κ P(k) ≤ {k / q_{J+1}} ≤ P(k)`. -/
theorem sparse_exclusion_b (S : Set ℕ) (hSub : sqScales 2 ⊆ S) (hpos : ∀ q ∈ S, 0 < q)
    (hinf : S.Infinite) {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ k : ℤ, nrm ((k : ℝ) * xs n) ≤ C * Pn S k) {κ : ℝ} (hκ : 0 < κ)
    (hwit : ∀ ε : ℝ, 0 < ε → ∃ (J : ℕ) (k : ℤ), 0 < k ∧ (qs n J : ℤ) ∣ k ∧
      4 * (k : ℝ) ≤ qs n (J + 2) ∧ Pn S k < ε ∧
      κ * Pn S k ≤ Int.fract ((k : ℝ) / (qs n (J + 1) : ℝ)) ∧
      Int.fract ((k : ℝ) / (qs n (J + 1) : ℝ)) ≤ Pn S k) : False := by
  obtain ⟨ε0, hε0, hflat⟩ := flatness_necessity hpos hinf hC0 hC hκ
  obtain ⟨J, k, hk0, hdiv, hQ4, hPlt, hlow, hup⟩ :=
    hwit (min ε0 (1 / 6)) (lt_min hε0 (by norm_num))
  have hPε : Pn S k < ε0 := lt_of_lt_of_le hPlt (min_le_left _ _)
  have hP6 : Pn S k < 1 / 6 := lt_of_lt_of_le hPlt (min_le_right _ _)
  have hkne : k ≠ 0 := hk0.ne'
  have hflat' := hflat k hkne hPε
  -- decomposition
  obtain ⟨N, hN⟩ := sparse_decomp hn1 hnm J k hdiv
  obtain ⟨hT1, hT2⟩ := Tl_bounds hn1 hnm J
  have hQ : (0 : ℝ) < qs n (J + 2) := by exact_mod_cast qs_pos hn1 hnm _
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk0
  have hT0 : 0 ≤ Tl n J := by
    have : (0 : ℝ) < 1 / (qs n (J + 2) : ℝ) := by positivity
    linarith
  -- k / Q ≤ P
  have hmem : qs n (J + 2) ∈ S := hSub (mem_sqScales (hn1 _))
  have hkQ : (k : ℝ) / (qs n (J + 2) : ℝ) ≤ Pn S k := by
    have hle : |(k : ℝ) / (qs n (J + 2) : ℝ)| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hQ, abs_of_pos hkr, div_le_iff₀ hQ]; linarith
    have := le_Pn hmem k
    rwa [nrm_eq_abs hle, abs_of_pos (div_pos hkr hQ)] at this
  have hkT : (k : ℝ) * Tl n J ≤ 2 * Pn S k := by
    calc (k : ℝ) * Tl n J ≤ (k : ℝ) * (2 / (qs n (J + 2) : ℝ)) := by gcongr
      _ = 2 * ((k : ℝ) / (qs n (J + 2) : ℝ)) := by ring
      _ ≤ 2 * Pn S k := by gcongr
  -- the real representative f + kT
  set f : ℝ := Int.fract ((k : ℝ) / (qs n (J + 1) : ℝ)) with hf
  have hkx : (k : ℝ) * xs n = f + (k : ℝ) * Tl n J + ((N + ⌊(k : ℝ) / (qs n (J + 1) : ℝ)⌋ : ℤ) : ℝ) := by
    rw [hN]; push_cast
    have := Int.floor_add_fract ((k : ℝ) / (qs n (J + 1) : ℝ))
    rw [hf]; linarith
  have hP0 : 0 ≤ Pn S k := Pn_nonneg S k
  have hfT0 : 0 ≤ f + (k : ℝ) * Tl n J := by
    have : 0 ≤ f := Int.fract_nonneg _
    have : 0 ≤ (k : ℝ) * Tl n J := by positivity
    linarith
  have hfT3 : f + (k : ℝ) * Tl n J ≤ 3 * Pn S k := by linarith
  have hnrm : nrm ((k : ℝ) * xs n) = f + (k : ℝ) * Tl n J := by
    rw [hkx, nrm_add_int, nrm_eq_abs (by rw [abs_of_nonneg hfT0]; linarith), abs_of_nonneg hfT0]
  have : κ * Pn S k ≤ nrm ((k : ℝ) * xs n) := by
    rw [hnrm]
    have : 0 ≤ (k : ℝ) * Tl n J := by positivity
    linarith
  linarith

end sparse

end MixedPrime
end LeanCheck
