import LeanCheck.MixedPrimeRadii
import LeanCheck.MixedPrimeColoured

/-!
# TVGplus: valuation thresholds, universal divisor, CRT class, residue independence

Formal counterparts of the elementary results of `TVGplus` (Sections 2, 4 and 5).
Scales: `sqScales p = {p^(n^2) | n ≥ 1}`; the paper's `P_p` is `Pn (sqScales p)`; the ball
`B^S_δ = {k | P_S k < δ}` is `InBall S δ` (the maximum over a finite set is `< δ` iff each term is).
`aThr p δ` is `a_p(δ) = min {a | 1 / p^(2a+1) < δ}`; `Dvis S δ = ∏ p^(a_p(δ)^2)` is `D_S(δ)`.

Checked here (no axiom, no `sorry`):

* `forced_prime`, `forced`: every element of the ball is divisible by `D_S(δ)` (Theorem "universal divisor");
* `sharp_prime`: `p^(a_p(δ)^2)` itself lies in the one-prime ball, so the divisor is sharp for one prime;
* `shell_lower`, `Pn_prime_pow_le`: the exact value of the least norm on a valuation shell;
* `crt_class`, `crt_positive`: the necessary CRT class and the lower bound `max {V, U+1}` for a shifted target;
* `residues`, `valuation_vector_iff`, `gcd_valuation`: residue independence and the valuation-vector criterion
  *under the explicit hypothesis* `DD S` (density of the diagonal), which is not proved here.

Not checked here: the pigeonhole upper bounds, the asymptotic constants, the identification of the dual group,
and the statement `g_S(δ) = D_S(δ)` (which needs the character argument), and `DD S` itself.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- The ball condition `P_p(k) < δ` for every `p ∈ S`. -/
def InBall (S : Finset ℕ) (δ : ℝ) (k : ℤ) : Prop := ∀ p ∈ S, Pn (sqScales p) k < δ

/-- `a_p(δ)`: the least `a` with `p^(-(2a+1)) < δ`. -/
noncomputable def aThr (p : ℕ) (δ : ℝ) : ℕ := sInf {a : ℕ | 1 / (p : ℝ) ^ (2 * a + 1) < δ}

/-- The universal divisor `D_S(δ)`. -/
noncomputable def Dvis (S : Finset ℕ) (δ : ℝ) : ℕ := ∏ p ∈ S, p ^ (aThr p δ ^ 2)

lemma sq_nonempty (p : ℕ) : (sqScales p).Nonempty := ⟨p ^ (1 ^ 2), mem_sqScales le_rfl⟩

lemma exists_thr {p : ℕ} (hp : 2 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℕ, 1 / (p : ℝ) ^ (2 * a + 1) < δ := by
  have hp1 : (1 : ℝ) / p < 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp
    rw [div_lt_one (by linarith)]; exact this
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hp1
  refine ⟨n, lt_of_le_of_lt ?_ hn⟩
  rw [one_div_pow]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  apply one_div_le_one_div_of_le (pow_pos hp0 n)
  exact pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ p)) (by omega)

lemma aThr_spec {p : ℕ} (hp : 2 ≤ p) {δ : ℝ} (hδ : 0 < δ) :
    1 / (p : ℝ) ^ (2 * aThr p δ + 1) < δ :=
  Nat.sInf_mem (exists_thr hp hδ)

lemma aThr_min {p : ℕ} {δ : ℝ} {a : ℕ} (h : a < aThr p δ) :
    δ ≤ 1 / (p : ℝ) ^ (2 * a + 1) := by
  have := Nat.notMem_of_lt_sInf h
  simpa using this

/-- **Universal divisor, one prime.** -/
theorem forced_prime {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) {k : ℤ}
    (hk : Pn (sqScales p) k < δ) : (p : ℤ) ^ (aThr p δ ^ 2) ∣ k := by
  by_contra hnd
  have ha1 : 1 ≤ aThr p δ := by
    by_contra h0
    have h00 : aThr p δ = 0 := by omega
    apply hnd; rw [h00]; simp
  obtain ⟨b, hb⟩ : ∃ b, aThr p δ = b + 1 := ⟨aThr p δ - 1, by omega⟩
  have hA : 1 ≤ aThr p δ ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hv := valuation_bound hp hA hnd
  have hs : Nat.sqrt (aThr p δ ^ 2 - 1) = b := by
    have e : aThr p δ ^ 2 - 1 = b * b + 2 * b := by
      have : aThr p δ ^ 2 = b * b + 2 * b + 1 := by rw [hb]; ring
      omega
    rw [e]
    apply sqrt_eq_of
    · omega
    · nlinarith
  rw [hs] at hv
  have hlt : b < aThr p δ := by omega
  have := aThr_min (p := p) hlt
  linarith

/-- **Universal divisor**: every element of the ball `B^S_δ` is a multiple of `D_S(δ)`. -/
theorem forced {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {δ : ℝ} (hδ : 0 < δ) {k : ℤ}
    (hk : InBall S δ k) : (Dvis S δ : ℤ) ∣ k := by
  unfold Dvis
  push_cast
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    simp only [Function.onFun]
    apply IsCoprime.pow
    exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)
  · intro p hp
    exact forced_prime (hS p hp) hδ (hk p hp)

/-- Upper bound for the norm of a prime power: `P_ℓ(ℓ^m) ≤ ℓ^(m - (⌊√m⌋+1)^2)`. -/
lemma Pn_prime_pow_le {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (m : ℕ) :
    Pn (sqScales ℓ) ((ℓ : ℤ) ^ m) ≤ 1 / (ℓ : ℝ) ^ ((Nat.sqrt m + 1) ^ 2 - m) := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
  apply Pn_le (sq_nonempty ℓ)
  rintro q ⟨n, hn, rfl⟩
  by_cases hnm : n ^ 2 ≤ m
  · have e : (((ℓ : ℤ) ^ m : ℤ) : ℝ) / ((ℓ ^ (n ^ 2) : ℕ) : ℝ)
        = (((ℓ : ℤ) ^ (m - n ^ 2) : ℤ) : ℝ) := by
      push_cast
      rw [pow_sub₀ _ hℓ0.ne' hnm, div_eq_mul_inv]
    rw [e, nrm_int]
    positivity
  · push_neg at hnm
    have hj : Nat.sqrt m + 1 ≤ n := Nat.sqrt_lt'.mpr hnm
    have hjn : (Nat.sqrt m + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hj 2
    have hmj : m ≤ (Nat.sqrt m + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt m
      nlinarith
    refine (nrm_le_abs _).trans ?_
    have hpos : (0 : ℝ) < (ℓ : ℝ) ^ (n ^ 2) := pow_pos hℓ0 _
    have hpos2 : (0 : ℝ) < (ℓ : ℝ) ^ ((Nat.sqrt m + 1) ^ 2 - m) := pow_pos hℓ0 _
    push_cast
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_div_iff₀ hpos hpos2, one_mul, ← pow_add]
    apply pow_le_pow_right₀ hℓ1
    omega

/-- The one-prime ball contains `p^(a_p(δ)^2)`, so `D_{ {p} }(δ)` is attained. -/
theorem sharp_prime {p : ℕ} (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) :
    Pn (sqScales p) ((p : ℤ) ^ (aThr p δ ^ 2)) < δ := by
  have h := Pn_prime_pow_le hp.two_le (aThr p δ ^ 2)
  have hs : Nat.sqrt (aThr p δ ^ 2) = aThr p δ := by rw [pow_two]; exact Nat.sqrt_eq _
  rw [hs] at h
  have e : (aThr p δ + 1) ^ 2 - aThr p δ ^ 2 = 2 * aThr p δ + 1 := by
    have : (aThr p δ + 1) ^ 2 = aThr p δ ^ 2 + (2 * aThr p δ + 1) := by ring
    omega
  rw [e] at h
  exact lt_of_le_of_lt h (aThr_spec hp.two_le hδ)

/-- **Least norm on a valuation shell**: if `p^m ∣ k` but `p^(m+1) ∤ k`, then
`P_p(k) ≥ p^(m - (⌊√m⌋+1)^2)`. -/
theorem shell_lower {p : ℕ} (hp : p.Prime) {m : ℕ} {k : ℤ} (h1 : (p : ℤ) ^ m ∣ k)
    (h2 : ¬ (p : ℤ) ^ (m + 1) ∣ k) :
    1 / (p : ℝ) ^ ((Nat.sqrt m + 1) ^ 2 - m) ≤ Pn (sqScales p) k := by
  obtain ⟨k', rfl⟩ := h1
  have hk2 : ¬ (p : ℤ) ∣ k' := fun hd => h2 (by rw [pow_succ]; exact mul_dvd_mul_left _ hd)
  set n := Nat.sqrt m + 1 with hn
  have hn1 : 1 ≤ n := by omega
  have hgv : m < n ^ 2 := by
    have := Nat.lt_succ_sqrt m
    nlinarith
  set g := n ^ 2 - m with hg
  have hg1 : 1 ≤ g := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hmem : p ^ (n ^ 2) ∈ sqScales p := mem_sqScales hn1
  have hlow : 1 / (p : ℝ) ^ g ≤
      nrm (((((p : ℤ) ^ m * k' : ℤ)) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) := by
    have e : (((((p : ℤ) ^ m * k' : ℤ)) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ))
        = (k' : ℝ) / ((p ^ g : ℕ) : ℝ) := by
      have hn2 : n ^ 2 = m + g := by omega
      rw [hn2]; push_cast; rw [pow_add]
      field_simp
    rw [e]
    by_contra hlt
    push_neg at hlt
    have hlt' : nrm ((k' : ℝ) / ((p ^ g : ℕ) : ℝ)) < 1 / ((p ^ g : ℕ) : ℝ) := by
      simpa [Nat.cast_pow] using hlt
    have hdv := dvd_of_nrm_lt k' (p ^ g) (pow_pos hp.pos g) hlt'
    apply hk2
    have : (p : ℤ) ∣ (p : ℤ) ^ g := dvd_pow_self _ (by omega)
    exact this.trans (by exact_mod_cast hdv)
  exact hlow.trans (le_Pn hmem _)

/-- **Exact value on a valuation shell**: `P_p(p^m) = p^(m - (⌊√m⌋+1)^2)`. -/
theorem Pn_prime_pow_eq {p : ℕ} (hp : p.Prime) (m : ℕ) :
    Pn (sqScales p) ((p : ℤ) ^ m) = 1 / (p : ℝ) ^ ((Nat.sqrt m + 1) ^ 2 - m) := by
  refine le_antisymm (Pn_prime_pow_le hp.two_le m) (shell_lower hp dvd_rfl ?_)
  intro hd
  have h6 : p ^ (m + 1) ∣ p ^ m := by exact_mod_cast hd
  have h7 := Nat.le_of_dvd (pow_pos hp.pos _) h6
  have h8 : p ^ m < p ^ (m + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

/-- **The shell of valuation `m` meets the one-prime ball iff `ρ_p(m) < δ`.** -/
theorem shell_meets_ball_iff {p : ℕ} (hp : p.Prime) (m : ℕ) (δ : ℝ) :
    (∃ k : ℤ, Pn (sqScales p) k < δ ∧ (p : ℤ) ^ m ∣ k ∧ ¬ (p : ℤ) ^ (m + 1) ∣ k) ↔
      1 / (p : ℝ) ^ ((Nat.sqrt m + 1) ^ 2 - m) < δ := by
  constructor
  · rintro ⟨k, hk, h1, h2⟩
    exact lt_of_le_of_lt (shell_lower hp h1 h2) hk
  · intro h
    refine ⟨(p : ℤ) ^ m, ?_, dvd_rfl, ?_⟩
    · rw [Pn_prime_pow_eq hp]; exact h
    · intro hd
      have h6 : p ^ (m + 1) ∣ p ^ m := by exact_mod_cast hd
      have h7 := Nat.le_of_dvd (pow_pos hp.pos _) h6
      have h8 : p ^ m < p ^ (m + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
      omega

/-- **Necessary CRT class** for a shifted target: if `P_q(k) < δ` and `P_p(k - t) < δ`, then
`q^(a_q(δ)^2) ∣ k` and `p^(a_p(δ)^2) ∣ k - t`. -/
theorem crt_class {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {δ : ℝ} (hδ : 0 < δ) {k t : ℤ}
    (hk : Pn (sqScales q) k < δ) (hkt : Pn (sqScales p) (k - t) < δ) :
    (q : ℤ) ^ (aThr q δ ^ 2) ∣ k ∧ (p : ℤ) ^ (aThr p δ ^ 2) ∣ k - t :=
  ⟨forced_prime hq hδ hk, forced_prime hp hδ hkt⟩

/-- For `t = 1` and both moduli `> 1`, every positive witness is at least `max {V, U+1}`. -/
theorem crt_positive {U V : ℤ} {k : ℤ} (hU : 1 < U) (hV : 1 < V) (hk : 0 < k)
    (hkV : V ∣ k) (hkU : U ∣ k - 1) : V ≤ k ∧ U + 1 ≤ k := by
  refine ⟨Int.le_of_dvd hk hkV, ?_⟩
  have hk1 : k ≠ 1 := by
    rintro rfl
    have := Int.le_of_dvd one_pos hkV
    omega
  have hpos : 0 < k - 1 := by omega
  have := Int.le_of_dvd hpos hkU
  omega

/-- Diagonal density: the integers approximate every integer target vector in every `P_p`, `p ∈ S`,
simultaneously.  (Equivalent to density of the diagonal in `∏ X_p`, since `ℤ` is dense in each `X_p`.) -/
def DD (S : Finset ℕ) : Prop :=
  ∀ (t : ℕ → ℤ) (ε : ℝ), 0 < ε → ∃ k : ℤ, ∀ p ∈ S, Pn (sqScales p) (k - t p) < ε

lemma exists_pos_le (S : Finset ℕ) (f : ℕ → ℝ) (h : ∀ p ∈ S, 0 < f p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ S, ε ≤ f p := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨ε, hε, hle⟩ := ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
    refine ⟨min ε (f a), lt_min hε (h a (Finset.mem_insert_self a s)), ?_⟩
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hle p hp)

/-- **Residue independence** under `DD S`: representatives `kp p` of the one-prime balls can be matched
simultaneously, modulo any prescribed prime powers, by one element of the joint ball. -/
theorem residues {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hDD : DD S) {δ : ℝ}
    (kp : ℕ → ℤ) (N : ℕ → ℕ) (hkp : ∀ p ∈ S, Pn (sqScales p) (kp p) < δ) :
    ∃ k : ℤ, InBall S δ k ∧ ∀ p ∈ S, (p : ℤ) ^ (N p) ∣ k - kp p := by
  obtain ⟨ε, hε, hle⟩ := exists_pos_le S
    (fun p => min (δ - Pn (sqScales p) (kp p)) (1 / (p : ℝ) ^ ((N p + 1) ^ 2))) (by
      intro p hp
      apply lt_min
      · linarith [hkp p hp]
      · have : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
        positivity)
  obtain ⟨k, hk⟩ := hDD kp ε hε
  refine ⟨k, ?_, ?_⟩
  · intro p hp
    have h1 := Pn_add_le (sq_nonempty p) (kp p) (k - kp p)
    have e : kp p + (k - kp p) = k := by ring
    rw [e] at h1
    have h2 := hk p hp
    have h3 := (hle p hp).trans (min_le_left _ _)
    linarith
  · intro p hp
    have hp' := hS p hp
    have hmem : p ^ ((N p + 1) ^ 2) ∈ sqScales p := mem_sqScales (by nlinarith)
    have a := le_Pn hmem (k - kp p)
    have b := hk p hp
    have c : ε ≤ 1 / ((p ^ ((N p + 1) ^ 2) : ℕ) : ℝ) := by
      rw [Nat.cast_pow]; exact (hle p hp).trans (min_le_right _ _)
    have h1 : nrm (((k - kp p : ℤ) : ℝ) / ((p ^ ((N p + 1) ^ 2) : ℕ) : ℝ))
        < 1 / ((p ^ ((N p + 1) ^ 2) : ℕ) : ℝ) := by linarith
    have hd := dvd_of_nrm_lt (k - kp p) (p ^ ((N p + 1) ^ 2)) (pow_pos hp'.pos _) h1
    have hN : N p ≤ (N p + 1) ^ 2 := by nlinarith
    exact (pow_dvd_pow (p : ℤ) hN).trans (by exact_mod_cast hd)

/-- **Valuation vectors** under `DD S`: a vector `(m_p)` is the valuation vector of an element of the ball
if and only if `p^(m_p - (⌊√m_p⌋+1)^2) < δ` for all `p ∈ S`. -/
theorem valuation_vector_iff {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hDD : DD S) {δ : ℝ}
    (m : ℕ → ℕ) :
    (∃ k : ℤ, InBall S δ k ∧ ∀ p ∈ S, (p : ℤ) ^ (m p) ∣ k ∧ ¬ (p : ℤ) ^ (m p + 1) ∣ k) ↔
      ∀ p ∈ S, 1 / (p : ℝ) ^ ((Nat.sqrt (m p) + 1) ^ 2 - m p) < δ := by
  constructor
  · rintro ⟨k, hk, hv⟩ p hp
    exact lt_of_le_of_lt (shell_lower (hS p hp) (hv p hp).1 (hv p hp).2) (hk p hp)
  · intro h
    obtain ⟨k, hk, hdv⟩ := residues hS hDD (δ := δ) (fun p => (p : ℤ) ^ (m p)) (fun p => m p + 1)
      (fun p hp => lt_of_le_of_lt (Pn_prime_pow_le (hS p hp).two_le (m p)) (h p hp))
    refine ⟨k, hk, fun p hp => ⟨?_, ?_⟩⟩
    · have h1 := hdv p hp
      have h2 : (p : ℤ) ^ (m p) ∣ (p : ℤ) ^ (m p + 1) := pow_dvd_pow _ (by omega)
      have h3 := h2.trans h1
      have h4 : k = (k - (p : ℤ) ^ (m p)) + (p : ℤ) ^ (m p) := by ring
      rw [h4]
      exact dvd_add h3 dvd_rfl
    · intro hd
      have h1 := hdv p hp
      have h5 : (p : ℤ) ^ (m p + 1) ∣ (p : ℤ) ^ (m p) := by
        have := dvd_sub hd h1
        simpa using this
      have h6 : p ^ (m p + 1) ∣ p ^ (m p) := by exact_mod_cast h5
      have h7 := Nat.le_of_dvd (pow_pos (hS p hp).pos _) h6
      have h8 : p ^ (m p) < p ^ (m p + 1) := Nat.pow_lt_pow_right (hS p hp).one_lt (by omega)
      omega

/-- Under `DD S`, for each `p ∈ S` the ball contains an element of valuation exactly `a_p(δ)^2` at every `p`
simultaneously; hence the valuation of the gcd of the ball at `p` is exactly `a_p(δ)^2`. -/
theorem gcd_valuation {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hDD : DD S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℤ, InBall S δ k ∧ ∀ p ∈ S,
      (p : ℤ) ^ (aThr p δ ^ 2) ∣ k ∧ ¬ (p : ℤ) ^ (aThr p δ ^ 2 + 1) ∣ k := by
  refine (valuation_vector_iff hS hDD (δ := δ) (fun p => aThr p δ ^ 2)).2 ?_
  intro p hp
  have hs : Nat.sqrt (aThr p δ ^ 2) = aThr p δ := by rw [pow_two]; exact Nat.sqrt_eq _
  have e : (aThr p δ + 1) ^ 2 - aThr p δ ^ 2 = 2 * aThr p δ + 1 := by
    have : (aThr p δ + 1) ^ 2 = aThr p δ ^ 2 + (2 * aThr p δ + 1) := by ring
    omega
  simp only [hs, e]
  exact aThr_spec (hS p hp).two_le hδ

#print axioms forced_prime
#print axioms forced
#print axioms sharp_prime
#print axioms shell_lower
#print axioms Pn_prime_pow_le
#print axioms Pn_prime_pow_eq
#print axioms shell_meets_ball_iff
#print axioms crt_class
#print axioms crt_positive
#print axioms residues
#print axioms valuation_vector_iff
#print axioms gcd_valuation

end TVGPlus
end LeanCheck
