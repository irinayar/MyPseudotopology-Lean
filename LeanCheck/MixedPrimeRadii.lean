import LeanCheck.MixedPrimeBasics

/-!
# TVGaddmore_v17: valuation lemma and exact divisibility radii (Proposition "divisibility-radii")

`sqScales ℓ = {ℓ^(n^2) | n ≥ 1}`; the paper's `P_S` is `Pn` of the union over `ℓ ∈ S`.
* `valuation_bound`: `ℓ^a ∤ k ⇒ P(k) ≥ ℓ^(-d(a))`, `d(a) = 2⌊√(a-1)⌋ + 1`.
* exact values for `S = {2,3}`: `μ(9)=μ(18)=μ(27)=μ(81)=1/27`, `μ(2^a)=1/32` for `5 ≤ a ≤ 9`,
  via the witnesses `393744` and `603519984` (finite exact computations).
-/

namespace LeanCheck
namespace MixedPrime

/-- Square-exponent scales of a base `ℓ`. -/
def sqScales (ℓ : ℕ) : Set ℕ := {q | ∃ n : ℕ, 1 ≤ n ∧ q = ℓ ^ (n ^ 2)}

/-- Scales of the mixed metric for `S = {2,3}`. -/
def S23 : Set ℕ := sqScales 2 ∪ sqScales 3

lemma mem_sqScales {ℓ n : ℕ} (hn : 1 ≤ n) : ℓ ^ (n ^ 2) ∈ sqScales ℓ := ⟨n, hn, rfl⟩

lemma Pn_mono {S T : Set ℕ} (hST : S ⊆ T) (k : ℤ) : Pn S k ≤ Pn T k := by
  by_cases hS : S.Nonempty
  · exact Pn_le hS fun q hq => le_Pn (hST hq) k
  · have : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    subst this
    have h0 : Pn ∅ k = 0 := by simp [Pn]
    rw [h0]; exact Pn_nonneg T k

/-- **Valuation lemma**: if `ℓ^a ∤ k` then `P_ℓ(k) ≥ ℓ^(-d(a))`, `d(a)=2⌊√(a-1)⌋+1`. -/
theorem valuation_bound {ℓ : ℕ} (hℓ : ℓ.Prime) {a : ℕ} (ha : 1 ≤ a) {k : ℤ}
    (hk : ¬ ((ℓ : ℤ) ^ a ∣ k)) :
    (1 : ℝ) / (ℓ : ℝ) ^ (2 * Nat.sqrt (a - 1) + 1) ≤ Pn (sqScales ℓ) k := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero _)
  set v := padicValInt ℓ k with hv
  have hva : v < a := by
    by_contra h
    push_neg at h
    apply hk
    rw [padicValInt_dvd_iff]
    exact Or.inr h
  -- k = ℓ^v * k'
  obtain ⟨k', hk1, hk2⟩ : ∃ k' : ℤ, k = (ℓ : ℤ) ^ v * k' ∧ ¬ (ℓ : ℤ) ∣ k' := by
    obtain ⟨c, hc⟩ := (padicValInt_dvd (p := ℓ) k)
    refine ⟨c, hc, ?_⟩
    intro hdiv
    have h2 : ((ℓ : ℤ) ^ (v + 1)) ∣ k := by
      rw [hc, pow_succ]; exact mul_dvd_mul_left _ hdiv
    rw [padicValInt_dvd_iff] at h2
    rcases h2 with h2 | h2
    · exact hk0 h2
    · omega
  set s := Nat.sqrt v with hs
  set n := s + 1 with hn
  have hn1 : 1 ≤ n := by omega
  have hsq : s * s ≤ v := Nat.sqrt_le v
  have hgv : v < n ^ 2 := by
    have := Nat.lt_succ_sqrt v
    nlinarith
  set g := n ^ 2 - v with hg
  have hg1 : 1 ≤ g := by omega
  have hgle : g ≤ 2 * Nat.sqrt (a - 1) + 1 := by
    have h1 : s ≤ Nat.sqrt (a - 1) := Nat.sqrt_le_sqrt (by omega)
    have h2 : n ^ 2 = s * s + 2 * s + 1 := by rw [hn]; ring
    omega
  have hmem : ℓ ^ (n ^ 2) ∈ sqScales ℓ := mem_sqScales hn1
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.pos
  -- nrm (k / ℓ^(n^2)) ≥ 1/ℓ^g
  have hlow : (1 : ℝ) / (ℓ : ℝ) ^ g ≤ nrm ((k : ℝ) / ((ℓ ^ (n ^ 2) : ℕ) : ℝ)) := by
    have e : (k : ℝ) / ((ℓ ^ (n ^ 2) : ℕ) : ℝ) = (k' : ℝ) / ((ℓ ^ g : ℕ) : ℝ) := by
      have hn2 : n ^ 2 = v + g := by omega
      rw [hk1, hn2]; push_cast; rw [pow_add]
      field_simp
    rw [e]
    by_contra hlt
    push_neg at hlt
    have hlt' : nrm ((k' : ℝ) / ((ℓ ^ g : ℕ) : ℝ)) < 1 / ((ℓ ^ g : ℕ) : ℝ) := by
      simpa [Nat.cast_pow] using hlt
    have hdv := dvd_of_nrm_lt k' (ℓ ^ g) (pow_pos hℓ.pos g) hlt'
    apply hk2
    have : (ℓ : ℤ) ∣ (ℓ : ℤ) ^ g := dvd_pow_self _ (by omega)
    exact this.trans (by exact_mod_cast hdv)
  have hP := le_Pn hmem k
  have hpow : (1 : ℝ) / (ℓ : ℝ) ^ (2 * Nat.sqrt (a - 1) + 1) ≤ 1 / (ℓ : ℝ) ^ g := by
    apply one_div_le_one_div_of_le (pow_pos hℓ0 g)
    exact pow_le_pow_right₀ (by exact_mod_cast hℓ.one_lt.le) hgle
  exact hpow.trans (hlow.trans hP)


lemma nrm_of_round (x : ℝ) (m : ℤ) (h : |x - m| ≤ 1 / 2) : nrm x = |x - m| := by
  have : x = (x - m) + m := by ring
  rw [this, nrm_add_int, nrm_eq_abs h]
  simp

/-- Large scales: `nrm (k / q) ≤ |k| / Q` whenever `Q ≤ q`. -/
lemma nrm_big (k : ℤ) {q Q : ℕ} (hQ : 0 < Q) (hq : Q ≤ q) :
    nrm ((k : ℝ) / q) ≤ |(k : ℝ)| / Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hq' : (0 : ℝ) < q := by exact_mod_cast lt_of_lt_of_le hQ hq
  refine (nrm_le_abs _).trans ?_
  rw [abs_div, abs_of_pos hq']
  exact div_le_div_of_nonneg_left (abs_nonneg _) hQ' (by exact_mod_cast hq)

/-- Finite certificate: `Pn S23 k ≤ c` from checks on the first scales of each base and a
bound on all later scales. -/
lemma Pn_S23_le (k : ℤ) (c : ℝ) (N2 N3 : ℕ)
    (h2 : ∀ n : ℕ, 1 ≤ n → n ≤ N2 → nrm ((k : ℝ) / (2 : ℝ) ^ (n ^ 2)) ≤ c)
    (h3 : ∀ n : ℕ, 1 ≤ n → n ≤ N3 → nrm ((k : ℝ) / (3 : ℝ) ^ (n ^ 2)) ≤ c)
    (hb2 : |(k : ℝ)| / (2 : ℝ) ^ ((N2 + 1) ^ 2) ≤ c)
    (hb3 : |(k : ℝ)| / (3 : ℝ) ^ ((N3 + 1) ^ 2) ≤ c) : Pn S23 k ≤ c := by
  apply Pn_le (S := S23)
  · exact ⟨2 ^ (1 ^ 2), Or.inl (mem_sqScales le_rfl)⟩
  · intro q hq
    rcases hq with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
    · by_cases hle : n ≤ N2
      · have := h2 n hn hle
        simpa [Nat.cast_pow] using this
      · push_neg at hle
        have hQ : 2 ^ ((N2 + 1) ^ 2) ≤ 2 ^ (n ^ 2) :=
          Nat.pow_le_pow_right (by norm_num) (by nlinarith)
        have := nrm_big k (pow_pos (by norm_num) _) hQ
        refine this.trans ?_
        simpa [Nat.cast_pow] using hb2
    · by_cases hle : n ≤ N3
      · have := h3 n hn hle
        simpa [Nat.cast_pow] using this
      · push_neg at hle
        have hQ : 3 ^ ((N3 + 1) ^ 2) ≤ 3 ^ (n ^ 2) :=
          Nat.pow_le_pow_right (by norm_num) (by nlinarith)
        have := nrm_big k (pow_pos (by norm_num) _) hQ
        refine this.trans ?_
        simpa [Nat.cast_pow] using hb3


/-! ### The two witnesses -/

/-- `P(393744) = 1/27`, with `3 ∣ 393744`, `9 ∤ 393744`. -/
theorem P_393744_le : Pn S23 (393744 : ℤ) ≤ 1 / 27 := by
  apply Pn_S23_le 393744 (1 / 27) 5 4
  · intro n h1 h5
    interval_cases n
    · rw [nrm_of_round _ 196872 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 24609 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 769 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 6 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 0 (by norm_num)]; norm_num
  · intro n h1 h4
    interval_cases n
    · rw [nrm_of_round _ 131248 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 4861 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 20 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 0 (by norm_num)]; norm_num
  · norm_num
  · norm_num

theorem P_393744_ge : 1 / 27 ≤ Pn S23 (393744 : ℤ) := by
  have h := le_Pn (S := S23) (q := 3 ^ (2 ^ 2)) (Or.inr (mem_sqScales (by norm_num))) 393744
  have e : nrm (((393744 : ℤ) : ℝ) / ((3 ^ (2 ^ 2) : ℕ) : ℝ)) = 1 / 27 := by
    rw [nrm_of_round _ 4861 (by norm_num)]; norm_num
  linarith

/-- `P(603519984) = 1/32`, `v₂ = 4`. -/
theorem P_603519984_le : Pn S23 (603519984 : ℤ) ≤ 1 / 32 := by
  apply Pn_S23_le 603519984 (1 / 32) 5 4
  · intro n h1 h5
    interval_cases n
    · rw [nrm_of_round _ 301759992 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 37719999 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 1178750 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 9209 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 18 (by norm_num)]; norm_num
  · intro n h1 h4
    interval_cases n
    · rw [nrm_of_round _ 201173328 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 7450864 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 30662 (by norm_num)]; norm_num
    · rw [nrm_of_round _ 14 (by norm_num)]; norm_num
  · norm_num
  · norm_num

theorem P_603519984_ge : 1 / 32 ≤ Pn S23 (603519984 : ℤ) := by
  have h := le_Pn (S := S23) (q := 2 ^ (3 ^ 2)) (Or.inl (mem_sqScales (by norm_num))) 603519984
  have e : nrm (((603519984 : ℤ) : ℝ) / ((2 ^ (3 ^ 2) : ℕ) : ℝ)) = 1 / 32 := by
    rw [nrm_of_round _ 1178750 (by norm_num)]; norm_num
  linarith


/-! ### Exact radii `μ(q) = inf {P(k) : q ∤ k}` -/

lemma sqrt_eq_of (n c : ℕ) (h1 : c * c ≤ n) (h2 : n < (c + 1) * (c + 1)) : Nat.sqrt n = c :=
  le_antisymm (Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr h2)) (Nat.le_sqrt.mpr h1)

lemma sqrt_vals : Nat.sqrt 1 = 1 ∧ Nat.sqrt 2 = 1 ∧ Nat.sqrt 3 = 1 ∧ Nat.sqrt 4 = 2 ∧ Nat.sqrt 5 = 2 ∧
    Nat.sqrt 6 = 2 ∧ Nat.sqrt 7 = 2 ∧ Nat.sqrt 8 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply sqrt_eq_of <;> norm_num

lemma three_pow_lower {a : ℕ} (ha : 2 ≤ a) (ha4 : a ≤ 4) {k : ℤ} (hk : ¬ ((3 : ℤ) ^ a ∣ k)) :
    1 / 27 ≤ Pn S23 k := by
  have h := valuation_bound (ℓ := 3) Nat.prime_three (by omega) hk
  have hs : Nat.sqrt (a - 1) = 1 := by
    obtain ⟨h1, h2, h3, -⟩ := sqrt_vals
    interval_cases a <;> simpa
  rw [hs] at h
  have h27 : (1 : ℝ) / ((3 : ℕ) : ℝ) ^ (2 * 1 + 1) = 1 / 27 := by norm_num
  rw [h27] at h
  exact h.trans (Pn_mono (Set.subset_union_right) k)

lemma two_pow_lower {a : ℕ} (ha : 5 ≤ a) (ha9 : a ≤ 9) {k : ℤ} (hk : ¬ ((2 : ℤ) ^ a ∣ k)) :
    1 / 32 ≤ Pn S23 k := by
  have h := valuation_bound (ℓ := 2) Nat.prime_two (by omega) hk
  have hs : Nat.sqrt (a - 1) = 2 := by
    obtain ⟨-, -, -, h4, h5, h6, h7, h8⟩ := sqrt_vals
    interval_cases a <;> simpa
  rw [hs] at h
  have h32 : (1 : ℝ) / ((2 : ℕ) : ℝ) ^ (2 * 2 + 1) = 1 / 32 := by norm_num
  rw [h32] at h
  exact h.trans (Pn_mono (Set.subset_union_left) _)

/-- **Exact radii** (Proposition "divisibility-radii"): `μ(9)=μ(18)=μ(27)=μ(81)=1/27`. -/
theorem mu_three_family (q : ℕ) (hq : q = 9 ∨ q = 18 ∨ q = 27 ∨ q = 81) :
    IsLeast ((fun k : ℤ => Pn S23 k) '' {k : ℤ | ¬ ((q : ℤ) ∣ k)}) (1 / 27) := by
  constructor
  · refine ⟨393744, ?_, le_antisymm P_393744_le P_393744_ge⟩
    rcases hq with rfl | rfl | rfl | rfl <;> norm_num
  · rintro r ⟨k, hk, rfl⟩
    simp only [Set.mem_setOf_eq] at hk
    rcases hq with rfl | rfl | rfl | rfl
    · exact three_pow_lower (a := 2) le_rfl (by norm_num) (by simpa using hk)
    · by_cases h2 : (2 : ℤ) ∣ k
      · have h9 : ¬ ((3 : ℤ) ^ 2 ∣ k) := by
          intro h9
          apply hk
          have : (2 : ℤ) * 9 ∣ k := IsCoprime.mul_dvd (by norm_num) h2 (by simpa using h9)
          simpa using this
        exact three_pow_lower (a := 2) le_rfl (by norm_num) h9
      · have h := valuation_bound (ℓ := 2) Nat.prime_two (a := 1) le_rfl (by simpa using h2)
        have e : Nat.sqrt (1 - 1) = 0 := by decide
        rw [e] at h
        have h' : (1 : ℝ) / 27 ≤ 1 / (2 : ℝ) ^ (2 * 0 + 1) := by norm_num
        exact h'.trans (h.trans (Pn_mono (Set.subset_union_left) k))
    · exact three_pow_lower (a := 3) (by norm_num) (by norm_num) (by simpa using hk)
    · exact three_pow_lower (a := 4) (by norm_num) le_rfl (by simpa using hk)

/-- `μ(2^a) = 1/32` for `5 ≤ a ≤ 9`. -/
theorem mu_two_power (a : ℕ) (ha : 5 ≤ a) (ha9 : a ≤ 9) :
    IsLeast ((fun k : ℤ => Pn S23 k) '' {k : ℤ | ¬ (((2 : ℕ) ^ a : ℤ) ∣ k)}) (1 / 32) := by
  constructor
  · refine ⟨603519984, ?_, le_antisymm P_603519984_le P_603519984_ge⟩
    simp only [Set.mem_setOf_eq]
    interval_cases a <;> norm_num
  · rintro r ⟨k, hk, rfl⟩
    simp only [Set.mem_setOf_eq] at hk
    exact two_pow_lower ha ha9 (by simpa using hk)

end MixedPrime
end LeanCheck
