import LeanCheck.ChainG2

/-!
# The explicit sequences showing that the prime-square topologies are not weakly generated
(TVGadd-v2 Theorem `nuclear:primes`, the explicit part)

For a prime `ℓ` let `a_n = (n! / ℓ^{v_ℓ(n!)}) ℓ^{n²-1}`.  Then `a_n → 0` in the weak topology `σ(ℚ,Γ)` of the character group `Γ`
(`gamma0`), but not in `γ_ℓ = ξ_{ℓ^{n²}}`.  (That a topology which has a countable separating dual and differs from its weak topology
cannot be nuclear uses the theory of nuclear groups, which is not formalized.)
-/

namespace LeanCheck

open Filter Topology

section PrimeSeq

/-- `a_n = (n!/ℓ^{v_ℓ(n!)}) ℓ^{n²-1}`. -/
def aSeq (ℓ n : ℕ) : ℕ := (n.factorial / ℓ ^ (n.factorial.factorization ℓ)) * ℓ ^ (n ^ 2 - 1)

lemma aSeq_dvd_eventually {ℓ : ℕ} (hℓ : ℓ.Prime) (N : ℕ) (hN : 0 < N) : ∃ n0, ∀ n ≥ n0, N ∣ aSeq ℓ n := by
  obtain ⟨e, N', hdvd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' ℓ hℓ.ne_one
  refine ⟨N' + e + 1, fun n hn => ?_⟩
  unfold aSeq
  have hN'pos : 0 < N' := Nat.pos_of_ne_zero (by rintro rfl; exact hdvd (dvd_zero _) |>.elim)
  have h1 : N' ∣ n.factorial := Nat.dvd_factorial hN'pos (by omega)
  have hcop : Nat.Coprime N' (ℓ ^ (n.factorial.factorization ℓ)) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hdvd))
  have hmul : ℓ ^ (n.factorial.factorization ℓ) * (n.factorial / ℓ ^ (n.factorial.factorization ℓ)) = n.factorial :=
    Nat.ordProj_mul_ordCompl_eq_self n.factorial ℓ
  have h2 : N' ∣ n.factorial / ℓ ^ (n.factorial.factorization ℓ) := by
    rw [← hmul] at h1
    exact hcop.dvd_of_dvd_mul_left h1
  have h3 : ℓ ^ e ∣ ℓ ^ (n ^ 2 - 1) := by
    apply pow_dvd_pow
    have : n ≤ n ^ 2 := by nlinarith
    omega
  rw [mul_comm (ℓ ^ e) N']
  exact mul_dvd_mul h2 h3

theorem aSeq_weak_null {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Tendsto (fun n => ((aSeq ℓ n : ℕ) : ℚ)) atTop (@nhds ℚ gamma0 0) := by
  unfold gamma0
  rw [nhds_iInf, tendsto_iInf]
  intro r
  rw [nhds_induced, tendsto_comap_iff]
  obtain ⟨n0, hn0⟩ := aSeq_dvd_eventually hℓ r.den r.den_pos
  have hz : ∀ᶠ n in atTop, ((((r * (aSeq ℓ n : ℚ) : ℚ) : ℝ)) : Circ) = 0 := by
    rw [eventually_atTop]
    refine ⟨n0, fun n hn => ?_⟩
    obtain ⟨c, hc⟩ := hn0 n hn
    have : r * (aSeq ℓ n : ℚ) = ((r.num * c : ℤ) : ℚ) := by
      rw [hc]; push_cast
      rw [← mul_assoc, Rat.mul_den_eq_num]
    rw [this]
    have : ((((r.num * c : ℤ) : ℚ) : ℝ)) = (((r.num * c : ℤ)) : ℝ) := by push_cast; ring
    rw [this]; exact coe_int_circ_zero _
  simp only [Function.comp_def, mul_zero, Rat.cast_zero, AddCircle.coe_zero]
  exact tendsto_const_nhds.congr' (hz.mono fun n hn => hn.symm)

lemma norm_div_prime_ge' {ℓ w : ℕ} (hℓ : ℓ.Prime) (hw : ¬ ℓ ∣ w) : 1 / (ℓ : ℝ) ≤ ‖((((w : ℝ) / ℓ : ℝ)) : Circ)‖ := by
  rw [norm_coe_circ]
  set k := round ((w : ℝ) / ℓ) with hk
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.pos
  have hne : ((w : ℤ) - k * ℓ) ≠ 0 := by
    intro h0
    apply hw
    have : (ℓ : ℤ) ∣ (w : ℤ) := ⟨k, by linarith⟩
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ |((w : ℤ) - k * ℓ : ℤ)| := by
    have : (1 : ℤ) ≤ |(w : ℤ) - k * ℓ| := Int.one_le_abs hne
    exact_mod_cast this
  have e : (w : ℝ) / ℓ - k = (((w : ℤ) - k * ℓ : ℤ) : ℝ) / ℓ := by
    push_cast; field_simp
  rw [e, abs_div, abs_of_pos hℓpos, ← Int.cast_abs]
  rw [Int.cast_abs] at h1 ⊢
  exact div_le_div_of_nonneg_right h1 hℓpos.le

theorem aSeq_not_gamma {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ¬ Tendsto (fun n => ((aSeq ℓ n : ℕ) : ℚ)) atTop (@nhds ℚ (xi (Cp ℓ)) 0) := by
  intro h
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.pos
  have hmem : xiSet (Cp ℓ) 1 (1 / (2 * ℓ)) ∈ @nhds ℚ (xi (Cp ℓ)) 0 :=
    (xi_nhds_hasBasis (Cp ℓ)).mem_of_mem (xiSet_mem (Cp ℓ) 1 one_pos _ (by positivity))
  obtain ⟨n, hn1, hn⟩ := ((eventually_ge_atTop 1).and (h.eventually hmem)).exists
  have hc : ℓ ^ (n ^ 2) ∈ Cp ℓ := mem_Cp.2 ⟨n, rfl⟩
  have h1 := hn _ hc
  have hn2 : n ^ 2 - 1 + 1 = n ^ 2 := by
    have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn1
    omega
  have hn0 : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hnd := Nat.not_dvd_ordCompl hℓ hn0
  have e : ((((aSeq ℓ n : ℕ) : ℚ) / (((1 : ℕ) : ℚ) * ((ℓ ^ (n ^ 2) : ℕ) : ℚ)) : ℚ) : ℝ) =
      ((n.factorial / ℓ ^ (n.factorial.factorization ℓ) : ℕ) : ℝ) / ℓ := by
    unfold aSeq
    have hpow : (ℓ : ℝ) ^ (n ^ 2) = (ℓ : ℝ) ^ (n ^ 2 - 1) * ℓ := by
      rw [← pow_succ, hn2]
    push_cast
    rw [hpow]
    field_simp
  have h1' : ‖xt ((aSeq ℓ n : ℕ) : ℚ) 1 (ℓ ^ (n ^ 2))‖ < 1 / (2 * ℓ) := h1
  unfold xt at h1'
  rw [e] at h1'
  have h2 := norm_div_prime_ge' hℓ hnd
  have h3 : (1 : ℝ) / (2 * ℓ) < 1 / ℓ := by
    rw [div_lt_div_iff₀ (by positivity) hℓpos]; linarith
  linarith

end PrimeSeq

end LeanCheck
