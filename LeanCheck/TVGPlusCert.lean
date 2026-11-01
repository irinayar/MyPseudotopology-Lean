import LeanCheck.TVGPlusCount

/-!
# TVGplus: certified finite witnesses for `S = {2, 3}`

A generic, kernel-checkable certificate scheme.  For a natural number `k` and a modulus `Q` let
`idist k Q = min (k mod Q) (Q - k mod Q)` be the integer distance from `k` to a multiple of `Q`.
Then `nrm (k / Q) = idist k Q / Q` exactly (`nrm_eq_idist`), so every statement about finitely many
coordinates is a statement about natural numbers.

* `Pn_le_check`: finitely many integer inequalities plus a tail inequality give `P_p(k) ≤ a/b`.
* `not_inBall_of_fail`: one coordinate with `idist k Q / Q ≥ 1/den` shows `P_p(k) ≥ 1/den`.
* `least_witness_23`: for `S = {2,3}` and radius `1/den`, the number `u` is the least positive element of the
  ball provided (i) `u` passes the finite membership check and (ii) every positive proper multiple of the
  universal divisor `D` below `u` fails at some coordinate.  Non-multiples of `D` are excluded by the
  universal divisor theorem `forced` (so the exhaustive search is over multiples of `D` only).

Instances (all by `decide +kernel`, no `native_decide`) are in `TVGPlusCertData.lean`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- Integer distance from `k` to the nearest multiple of `Q`. -/
def idist (k Q : ℕ) : ℕ := min (k % Q) (Q - k % Q)

lemma nrm_eq_idist (k Q : ℕ) (hQ : 0 < Q) : nrm ((k : ℝ) / Q) = (idist k Q : ℝ) / Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrlt : k % Q < Q := Nat.mod_lt _ hQ
  have hk : k = Q * (k / Q) + k % Q := (Nat.div_add_mod k Q).symm
  have e : (k : ℝ) / Q = ((k % Q : ℕ) : ℝ) / Q + (((k / Q : ℕ) : ℤ) : ℝ) := by
    have h1 : (k : ℝ) = (Q : ℝ) * ((k / Q : ℕ) : ℝ) + ((k % Q : ℕ) : ℝ) := by exact_mod_cast hk
    have h2 : (((k / Q : ℕ) : ℤ) : ℝ) = ((k / Q : ℕ) : ℝ) := Int.cast_natCast _
    rw [h2]
    conv_lhs => rw [h1]
    first | (field_simp; done) | (field_simp; ring)
  rw [e, nrm_add_int, nrm_eq]
  have hx0 : 0 ≤ ((k % Q : ℕ) : ℝ) / Q := by positivity
  have hx1 : ((k % Q : ℕ) : ℝ) / Q < 1 := by
    rw [div_lt_one hQ']; exact_mod_cast hrlt
  by_cases h2 : 2 * (k % Q) < Q
  · have hr : round (((k % Q : ℕ) : ℝ) / Q) = 0 := by
      rw [round_eq, Int.floor_eq_iff]
      have h2' : (2 * (k % Q : ℕ) : ℝ) < Q := by exact_mod_cast h2
      have : ((k % Q : ℕ) : ℝ) / Q < 1 / 2 := by rw [div_lt_iff₀ hQ']; linarith
      constructor <;> push_cast <;> linarith
    have hid : idist k Q = k % Q := by unfold idist; omega
    rw [hr, hid]; simp [abs_of_nonneg hx0]
  · have hr : round (((k % Q : ℕ) : ℝ) / Q) = 1 := by
      rw [round_eq, Int.floor_eq_iff]
      have h2' : (Q : ℝ) ≤ 2 * (k % Q : ℕ) := by exact_mod_cast (by omega : Q ≤ 2 * (k % Q))
      have : (1 / 2 : ℝ) ≤ ((k % Q : ℕ) : ℝ) / Q := by rw [le_div_iff₀ hQ']; linarith
      constructor <;> push_cast <;> linarith
    have hid : idist k Q = Q - k % Q := by unfold idist; omega
    have hcast : ((Q - k % Q : ℕ) : ℝ) = (Q : ℝ) - ((k % Q : ℕ) : ℝ) := by
      rw [Nat.cast_sub hrlt.le]
    rw [hr, hid, hcast]
    have : |((k % Q : ℕ) : ℝ) / Q - ((1 : ℤ) : ℝ)| = 1 - ((k % Q : ℕ) : ℝ) / Q := by
      rw [abs_of_nonpos (by push_cast; linarith)]; push_cast; ring
    rw [this]
    field_simp

/-- Finite membership certificate: all coordinates `n ≤ N` pass and the tail is below `a/b`. -/
lemma Pn_le_check {p : ℕ} (hp : 2 ≤ p) (k a b N : ℕ) (hb : 0 < b)
    (h1 : ∀ n ∈ Finset.Icc 1 N, b * idist k (p ^ (n ^ 2)) ≤ a * p ^ (n ^ 2))
    (h2 : b * k ≤ a * p ^ ((N + 1) ^ 2)) : Pn (sqScales p) (k : ℤ) ≤ (a : ℝ) / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  apply Pn_le (sq_nonempty p)
  rintro q ⟨n, hn, rfl⟩
  by_cases hnN : n ≤ N
  · have hQ : 0 < p ^ (n ^ 2) := pow_pos (by omega) _
    have hQ' : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by exact_mod_cast hQ
    have h := h1 n (Finset.mem_Icc.mpr ⟨hn, hnN⟩)
    have e := nrm_eq_idist k (p ^ (n ^ 2)) hQ
    have e' : nrm (((k : ℤ) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) = (idist k (p ^ (n ^ 2)) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) := by
      simpa using e
    rw [e', div_le_div_iff₀ hQ' hb']
    have : ((b * idist k (p ^ (n ^ 2)) : ℕ) : ℝ) ≤ ((a * p ^ (n ^ 2) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this ⊢
    linarith
  · push_neg at hnN
    have hQ : 0 < p ^ ((N + 1) ^ 2) := pow_pos (by omega) _
    have hle : p ^ ((N + 1) ^ 2) ≤ p ^ (n ^ 2) :=
      Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left hnN 2)
    have := nrm_big (k : ℤ) hQ hle
    refine this.trans ?_
    have hQ' : (0 : ℝ) < ((p ^ ((N + 1) ^ 2) : ℕ) : ℝ) := by exact_mod_cast hQ
    rw [div_le_div_iff₀ hQ' hb']
    have h2' : ((b * k : ℕ) : ℝ) ≤ ((a * p ^ ((N + 1) ^ 2) : ℕ) : ℝ) := by exact_mod_cast h2
    simp only [Int.cast_natCast, Nat.abs_cast]
    push_cast at h2' ⊢
    linarith

/-- One failing coordinate shows that `k` is outside the ball of radius `1/den`. -/
lemma not_inBall_of_fail {p : ℕ} (hp : 2 ≤ p) (k n den : ℕ) (hn : 1 ≤ n) (hden : 0 < den)
    (h : p ^ (n ^ 2) ≤ den * idist k (p ^ (n ^ 2))) :
    ¬ Pn (sqScales p) (k : ℤ) < 1 / (den : ℝ) := by
  have hQ : 0 < p ^ (n ^ 2) := pow_pos (by omega) _
  have hQ' : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by exact_mod_cast hQ
  have hd' : (0 : ℝ) < den := by exact_mod_cast hden
  have e := nrm_eq_idist k (p ^ (n ^ 2)) hQ
  have e' : nrm (((k : ℤ) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) = (idist k (p ^ (n ^ 2)) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) := by
    simpa using e
  have hle := le_Pn (S := sqScales p) (q := p ^ (n ^ 2)) (mem_sqScales hn) (k : ℤ)
  rw [e'] at hle
  intro hlt
  have h1 : 1 / (den : ℝ) ≤ (idist k (p ^ (n ^ 2)) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hd' hQ']
    have : ((p ^ (n ^ 2) : ℕ) : ℝ) ≤ ((den * idist k (p ^ (n ^ 2)) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this ⊢
    linarith
  linarith

lemma aThr_eq_of_nat {p : ℕ} (hp : 2 ≤ p) {den : ℕ} (hden : 0 < den) {a : ℕ}
    (h1 : den < p ^ (2 * a + 1)) (h2 : ∀ b < a, p ^ (2 * b + 1) ≤ den) :
    aThr p (1 / (den : ℝ)) = a := by
  have hd' : (0 : ℝ) < den := by exact_mod_cast hden
  have hδ : (0 : ℝ) < 1 / (den : ℝ) := by positivity
  have spec : ∀ x : ℕ, 1 / (p : ℝ) ^ (2 * x + 1) < 1 / (den : ℝ) ↔ den < p ^ (2 * x + 1) := by
    intro x
    have hp0 : (0 : ℝ) < (p : ℝ) ^ (2 * x + 1) := by
      have : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
      positivity
    rw [one_div_lt_one_div hp0 hd']
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  apply le_antisymm
  · exact Nat.sInf_le ((spec a).2 h1)
  · by_contra hlt
    push_neg at hlt
    have h3 := (spec _).1 (aThr_spec hp hδ)
    have h4 := h2 _ hlt
    omega

lemma Dvis_23 {den a2 a3 : ℕ} (hden : 0 < den)
    (h2 : den < 2 ^ (2 * a2 + 1)) (h2' : ∀ b < a2, 2 ^ (2 * b + 1) ≤ den)
    (h3 : den < 3 ^ (2 * a3 + 1)) (h3' : ∀ b < a3, 3 ^ (2 * b + 1) ≤ den) :
    Dvis {2, 3} (1 / (den : ℝ)) = 2 ^ (a2 ^ 2) * 3 ^ (a3 ^ 2) := by
  unfold Dvis
  rw [Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3),
    aThr_eq_of_nat (by norm_num) hden h2 h2', aThr_eq_of_nat (by norm_num) hden h3 h3']

/-- Membership check for one prime (computable). -/
def memCheck (p k a b N : ℕ) : Bool :=
  (List.range N).all (fun i => decide (b * idist k (p ^ ((i + 1) ^ 2)) ≤ a * p ^ ((i + 1) ^ 2)))
    && decide (b * k ≤ a * p ^ ((N + 1) ^ 2))

/-- Failing-coordinate test for `S = {2,3}` (computable). -/
def fails23 (den N k : ℕ) : Bool :=
  (List.range N).any (fun i =>
    decide (2 ^ ((i + 1) ^ 2) ≤ den * idist k (2 ^ ((i + 1) ^ 2))) ||
    decide (3 ^ ((i + 1) ^ 2) ≤ den * idist k (3 ^ ((i + 1) ^ 2))))

/-- All multiples `D * j` with `a ≤ j < b` fail at some coordinate.  Large searches are split into chunks
(one declaration each, so that the kernel's cache is released between chunks) and reassembled with
`rangeOK_trans`. -/
def rangeOK (den N D a b : ℕ) : Bool :=
  (List.range (b - a)).all (fun i => fails23 den N (D * (a + i)))

lemma rangeOK_spec {den N D a b : ℕ} (h : rangeOK den N D a b = true) :
    ∀ j, a ≤ j → j < b → fails23 den N (D * j) = true := by
  intro j haj hjb
  unfold rangeOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have := h (j - a) (by omega)
  have e : a + (j - a) = j := by omega
  rwa [e] at this

lemma rangeOK_of_forall {den N D a b : ℕ}
    (h : ∀ j, a ≤ j → j < b → fails23 den N (D * j) = true) : rangeOK den N D a b = true := by
  unfold rangeOK
  simp only [List.all_eq_true, List.mem_range]
  intro i hi
  exact h (a + i) (by omega) (by omega)

lemma rangeOK_trans {den N D a b c : ℕ} (h1 : rangeOK den N D a b = true)
    (h2 : rangeOK den N D b c = true) : rangeOK den N D a c = true := by
  apply rangeOK_of_forall
  intro j haj hjc
  by_cases hjb : j < b
  · exact rangeOK_spec h1 j haj hjb
  · exact rangeOK_spec h2 j (by omega) hjc

lemma memCheck_spec {p : ℕ} (hp : 2 ≤ p) {k a b N : ℕ} (hb : 0 < b) (h : memCheck p k a b N = true) :
    Pn (sqScales p) (k : ℤ) ≤ (a : ℝ) / b := by
  unfold memCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  apply Pn_le_check hp k a b N hb _ h.2
  intro n hn
  rw [Finset.mem_Icc] at hn
  have := h.1 (n - 1) (by omega)
  have e : n - 1 + 1 = n := by omega
  rw [e] at this
  exact this

lemma fails23_spec {den N k : ℕ} (hden : 0 < den) (h : fails23 den N k = true) :
    ¬ InBall {2, 3} (1 / (den : ℝ)) (k : ℤ) := by
  intro hball
  unfold fails23 at h
  simp only [List.any_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨i, -, hi⟩ := h
  rcases hi with hi | hi
  · exact not_inBall_of_fail (p := 2) (by norm_num) k (i + 1) den (by omega) hden hi
      (hball 2 (by simp))
  · exact not_inBall_of_fail (p := 3) (by norm_num) k (i + 1) den (by omega) hden hi
      (hball 3 (by simp))

lemma primes_23 : ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> norm_num

/-- **Certified least witness** for `S = {2,3}` and radius `1/den`. -/
theorem least_witness_23 (den a2 a3 u N ca cb J : ℕ) (hden : 0 < den) (hcb : 0 < cb)
    (h2 : den < 2 ^ (2 * a2 + 1)) (h2' : ∀ b < a2, 2 ^ (2 * b + 1) ≤ den)
    (h3 : den < 3 ^ (2 * a3 + 1)) (h3' : ∀ b < a3, 3 ^ (2 * b + 1) ≤ den)
    (hc : ca * den < cb) (hu : 0 < u)
    (hmem2 : memCheck 2 u ca cb N = true) (hmem3 : memCheck 3 u ca cb N = true)
    (hJ : 2 ^ (a2 ^ 2) * 3 ^ (a3 ^ 2) * J = u)
    (hmin : rangeOK den N (2 ^ (a2 ^ 2) * 3 ^ (a3 ^ 2)) 1 J = true) :
    InBall {2, 3} (1 / (den : ℝ)) (u : ℤ) ∧
      ∀ k : ℕ, 1 ≤ k → k < u → ¬ InBall {2, 3} (1 / (den : ℝ)) (k : ℤ) := by
  have hd' : (0 : ℝ) < den := by exact_mod_cast hden
  have hcb' : (0 : ℝ) < cb := by exact_mod_cast hcb
  have hlt : (ca : ℝ) / cb < 1 / (den : ℝ) := by
    rw [div_lt_div_iff₀ hcb' hd']
    have : ((ca * den : ℕ) : ℝ) < (cb : ℝ) := by exact_mod_cast hc
    push_cast at this ⊢
    linarith
  constructor
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact lt_of_le_of_lt (memCheck_spec (by norm_num) hcb hmem2) hlt
    · exact lt_of_le_of_lt (memCheck_spec (by norm_num) hcb hmem3) hlt
  · intro k hk1 hku hball
    have hδ : (0 : ℝ) < 1 / (den : ℝ) := by positivity
    have hdiv := forced primes_23 hδ hball
    rw [Dvis_23 hden h2 h2' h3 h3'] at hdiv
    have hdiv' : 2 ^ (a2 ^ 2) * 3 ^ (a3 ^ 2) ∣ k := by exact_mod_cast hdiv
    obtain ⟨j, hj⟩ := hdiv'
    have hjpos : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0] at hj; omega
      · exact h0
    have hjJ : j < J := by
      by_contra hge
      push_neg at hge
      have : 2 ^ (a2 ^ 2) * 3 ^ (a3 ^ 2) * J ≤ 2 ^ (a2 ^ 2) * 3 ^ (a3 ^ 2) * j :=
        Nat.mul_le_mul_left _ hge
      omega
    have hf := rangeOK_spec hmin j (by omega) hjJ
    rw [hj] at hball
    exact fails23_spec hden hf hball

end TVGPlus
end LeanCheck
