import LeanCheck.ChainD5

/-!
# The prime-square topologies `γ_p`
(HamelCharactersTVG_v18 Theorem 22.1 `thm:prime-v8` (membership in `𝒬_Γ`), Theorem 22.2 `thm:prime-incomparable-v8`)

`γ_p = ξ_{{p^{n²} : n ≥ 0}}` is the group topology on `ℚ` with zero-neighbourhood base
`{q : P_{p,d}(q) < ε}`, `P_{p,d}(q) = sup_n ‖q/(d p^{n²})‖`.  The character computation of Theorem 22.1, which the paper
takes from an external theorem, follows here from our Theorem F (the chain `p^n`, the index set of squares).
-/

namespace LeanCheck

open Filter Topology

section PrimeSquares

/-- The prime-square observation set `{p^{n²}}`. -/
def Cp (p : ℕ) : Set ℕ := (fun n : ℕ => p ^ n) '' Set.range (fun n : ℕ => n ^ 2)

lemma mem_Cp {p c : ℕ} : c ∈ Cp p ↔ ∃ n : ℕ, c = p ^ (n ^ 2) := by
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩; exact ⟨n ^ 2, ⟨n, rfl⟩, rfl⟩

lemma pow_chain (p : ℕ) (hp : 2 ≤ p) : ChainSeq (fun n => p ^ n) where
  pos n := pow_pos (by omega) n
  dvd n := pow_dvd_pow p (Nat.le_succ n)
  two n := by
    show 2 * p ^ n ≤ p ^ (n + 1)
    calc 2 * p ^ n ≤ p * p ^ n := Nat.mul_le_mul_right _ hp
      _ = p ^ (n + 1) := by ring

/-- The index set of squares satisfies `H` for the chain `p^n`: ratios between squares tend to infinity. -/
lemma HSet_sq (p : ℕ) (hp : 2 ≤ p) : HSet (fun n => p ^ n) (Set.range fun n : ℕ => n ^ 2) := by
  intro A hA
  refine ⟨⌈A⌉₊, fun k w hw => ?_⟩
  by_contra hk
  push_neg at hk
  have hmem : ∀ j, j ≤ k → ∃ a : ℕ, w j = a ^ 2 := fun j hj => by
    obtain ⟨a, ha⟩ := hw.1 j hj
    exact ⟨a, ha.symm⟩
  choose! a ha using hmem
  have hstep : ∀ j, j < k → a j + 1 ≤ a (j + 1) ∧ ((2 * a j + 1 : ℕ) : ℝ) < A := by
    intro j hj
    obtain ⟨hlt0, hrat⟩ := hw.2 j hj
    have hlt := hlt0
    rw [ha j hj.le, ha (j + 1) hj] at hlt
    have hjj : a j < a (j + 1) := by
      by_contra hcon
      push_neg at hcon
      have := Nat.pow_le_pow_left hcon 2
      exact absurd hlt (not_lt.2 this)
    refine ⟨hjj, ?_⟩
    -- `p^{w(j+1)} = p^{w j} p^t`
    obtain ⟨t, ht⟩ : ∃ t, w (j + 1) = w j + t := ⟨w (j + 1) - w j, by omega⟩
    have ht0 := ht
    have hpt : (p : ℝ) ^ t < A := by
      have hpos : (0 : ℝ) < (p : ℝ) ^ w j := by positivity
      have e : ((p ^ w (j + 1) : ℕ) : ℝ) = (p : ℝ) ^ w j * (p : ℝ) ^ t := by
        rw [ht]; push_cast; ring
      rw [e] at hrat
      have : (p : ℝ) ^ w j * (p : ℝ) ^ t < (p : ℝ) ^ w j * A := by
        calc (p : ℝ) ^ w j * (p : ℝ) ^ t < A * ((p : ℝ) ^ w j) := by simpa using hrat
          _ = (p : ℝ) ^ w j * A := by ring
      exact lt_of_mul_lt_mul_left this hpos.le
    have htlt : (t : ℝ) < (p : ℝ) ^ t := by
      exact_mod_cast Nat.lt_pow_self (by omega : 1 < p)
    have h2 : 2 * a j + 1 ≤ t := by
      rw [ha j hj.le, ha (j + 1) hj] at ht
      have := Nat.pow_le_pow_left hjj 2
      nlinarith
    have : ((2 * a j + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast h2
    linarith
  have hge : ∀ j, j ≤ k → j ≤ a j := by
    intro j
    induction j with
    | zero => intro _; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have := (hstep j (by omega)).1
      have := ih (by omega)
      omega
  have hk1 : 3 ≤ k := by
    have : (2 : ℝ) < ⌈A⌉₊ := lt_of_lt_of_le hA (Nat.le_ceil A)
    have : 2 < ⌈A⌉₊ := by exact_mod_cast this
    omega
  have h1 := (hstep (k - 1) (by omega)).2
  have h2 := hge (k - 1) (by omega)
  have h3 : A ≤ ⌈A⌉₊ := Nat.le_ceil A
  have h4 : (⌈A⌉₊ : ℝ) < k := by exact_mod_cast hk
  have h5 : ((k - 1 : ℕ) : ℝ) ≤ a (k - 1) := by exact_mod_cast h2
  have h6 : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
    have : k = (k - 1) + 1 := by omega
    exact_mod_cast this
  push_cast at h1
  have h7 : (3 : ℝ) ≤ k := by exact_mod_cast hk1
  linarith

lemma Cp_pos {p : ℕ} (hp : 2 ≤ p) : ∀ c ∈ Cp p, 0 < c := by
  intro c hc
  obtain ⟨n, rfl⟩ := mem_Cp.1 hc
  exact pow_pos (by omega) _

lemma Cp_nonempty (p : ℕ) : (Cp p).Nonempty := ⟨1, mem_Cp.2 ⟨0, by simp⟩⟩

/-- **Theorem 22.1 (membership).**  For `p ≥ 2`, `γ_p = ξ_{{p^{n²}}}` has full dual `Γ`, and lies in `𝒬_Γ`. -/
theorem gamma_p_dual (p : ℕ) (hp : 2 ≤ p) :
    ∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ (xi (Cp p)) circTop ψ ↔ ψ ∈ Gam :=
  (chains_F_set (pow_chain p hp) (Set.range fun n : ℕ => n ^ 2) ⟨0, 0, rfl⟩).2 (HSet_sq p hp)

theorem gamma_p_mem (p : ℕ) (hp : 2 ≤ p) : xi (Cp p) ∈ Ccls Gam :=
  xi_mem_Ccls (Cp p) (Cp_pos hp) (Cp_nonempty p) (gamma_p_dual p hp)

/-- A fraction `a/p` with `p ∤ a` is at circle distance `≥ 1/p` from `0`. -/
lemma norm_div_prime_ge (a : ℤ) (p : ℕ) (hp : 0 < p) (h : ¬ (p : ℤ) ∣ a) :
    1 / (p : ℝ) ≤ ‖((((a : ℝ) / p : ℝ)) : Circ)‖ := by
  rw [norm_coe_circ]
  set r : ℤ := round ((a : ℝ) / p) with hr
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hne : a - p * r ≠ 0 := by
    intro h0; apply h; exact ⟨r, by linarith⟩
  have h1 : (1 : ℝ) ≤ |((a - p * r : ℤ) : ℝ)| := by
    have : 1 ≤ |a - p * r| := Int.one_le_abs hne
    exact_mod_cast this
  have e : (a : ℝ) / p - r = ((a - p * r : ℤ) : ℝ) / p := by push_cast; field_simp
  rw [e, abs_div, abs_of_pos hpR]
  exact div_le_div_of_nonneg_right h1 hpR.le

/-- Separating integers for two distinct primes. -/
lemma exists_sep (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (d : ℕ) (ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ Q : ℕ, (Q : ℚ) ∈ xiSet (Cp q) d ε ∧ (Q : ℚ) ∉ xiSet (Cp p) 1 (1 / (p : ℝ)) := by
  obtain ⟨v, e, hpe, hde⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' p hp.one_lt.ne'
  set n : ℕ := v + 1 with hn
  have hvn : v ≤ n ^ 2 - 1 := by
    have h2 : (v + 1) ^ 2 = v ^ 2 + 2 * v + 1 := by ring
    have : v ≤ (v + 1) ^ 2 - 1 := by omega
    simpa [hn] using this
  set m : ℕ := p ^ (n ^ 2 - 1 - v) with hm
  obtain ⟨k, hk⟩ := exists_nat_gt ((m : ℝ) / ε)
  set Q : ℕ := d * m * q ^ (k ^ 2) with hQ
  have hqpos : 2 ≤ q := hq.two_le
  refine ⟨Q, ?_, ?_⟩
  · -- `Q ∈ ξ(C_q)(d, ε)`
    intro c hc
    obtain ⟨N, rfl⟩ := mem_Cp.1 hc
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have hval : ((((Q : ℚ) / ((d : ℚ) * (q ^ (N ^ 2) : ℕ))) : ℚ) : ℝ) =
        (m : ℝ) * (q : ℝ) ^ (k ^ 2) / (q : ℝ) ^ (N ^ 2) := by
      push_cast
      simp only [hQ]
      push_cast
      field_simp
    rw [hval]
    rcases le_or_gt N k with hNk | hNk
    · -- an integer
      obtain ⟨t, ht⟩ : ∃ t, k ^ 2 = N ^ 2 + t := ⟨k ^ 2 - N ^ 2, by
        have : N ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hNk 2
        omega⟩
      have : (m : ℝ) * (q : ℝ) ^ (k ^ 2) / (q : ℝ) ^ (N ^ 2) = ((m * q ^ t : ℕ) : ℤ) := by
        rw [ht, pow_add]; push_cast
        field_simp
      have h0 : ((((m : ℝ) * (q : ℝ) ^ (k ^ 2) / (q : ℝ) ^ (N ^ 2) : ℝ)) : Circ) = 0 := by
        rw [circ_zero_iff]; exact ⟨((m * q ^ t : ℕ) : ℤ), this⟩
      show ‖((((m : ℝ) * (q : ℝ) ^ (k ^ 2) / (q : ℝ) ^ (N ^ 2) : ℝ)) : Circ)‖ < ε
      rw [h0, norm_zero]; exact hε
    · -- small
      obtain ⟨t, ht⟩ : ∃ t, N ^ 2 = k ^ 2 + t := ⟨N ^ 2 - k ^ 2, by
        have : k ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega⟩
      have ht2 : 2 * k + 1 ≤ t := by
        have : (k + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hNk 2
        nlinarith
      have hqk : (q : ℝ) ^ (2 * k + 1) ≤ (q : ℝ) ^ t :=
        pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ q)) ht2
      have hqpowpos : (0 : ℝ) < (q : ℝ) ^ (2 * k + 1) := by positivity
      have e : (m : ℝ) * (q : ℝ) ^ (k ^ 2) / (q : ℝ) ^ (N ^ 2) = (m : ℝ) / (q : ℝ) ^ t := by
        rw [ht, pow_add]; field_simp
      show ‖((((m : ℝ) * (q : ℝ) ^ (k ^ 2) / (q : ℝ) ^ (N ^ 2) : ℝ)) : Circ)‖ < ε
      rw [e]
      refine lt_of_le_of_lt (norm_coe_le _ 0) ?_
      rw [Int.cast_zero, sub_zero, abs_of_nonneg (by positivity)]
      have h1 : (m : ℝ) / (q : ℝ) ^ t ≤ (m : ℝ) / (q : ℝ) ^ (2 * k + 1) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg m) hqpowpos hqk
      have h2 : (k : ℝ) < (q : ℝ) ^ (2 * k + 1) := by
        have : k < q ^ (2 * k + 1) := lt_of_lt_of_le (by omega) (Nat.lt_pow_self (by omega : 1 < q)).le
        exact_mod_cast this
      have h3 : (m : ℝ) / ε < (q : ℝ) ^ (2 * k + 1) := lt_trans hk h2
      rw [div_lt_iff₀ hε] at h3
      calc (m : ℝ) / (q : ℝ) ^ t ≤ (m : ℝ) / (q : ℝ) ^ (2 * k + 1) := h1
        _ < ε := by rw [div_lt_iff₀ hqpowpos]; linarith
  · -- `Q ∉ ξ(C_p)(1, 1/p)`
    intro hmem
    have hc : p ^ (n ^ 2) ∈ Cp p := mem_Cp.2 ⟨n, rfl⟩
    have h1 : ‖xt (Q : ℚ) 1 (p ^ (n ^ 2))‖ < 1 / (p : ℝ) := hmem _ hc
    set E : ℕ := e * q ^ (k ^ 2) with hE
    have hpE : ¬ (p : ℤ) ∣ (E : ℤ) := by
      intro hdvd
      have hdvd' : p ∣ E := by exact_mod_cast hdvd
      rcases (Nat.Prime.dvd_mul hp).1 hdvd' with h | h
      · exact hpe h
      · exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h))
    have hval : (((((Q : ℚ) / (((1 : ℕ) : ℚ) * ((p ^ (n ^ 2) : ℕ) : ℚ))) : ℚ)) : ℝ) = (E : ℝ) / p := by
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hn2 : n ^ 2 = (n ^ 2 - 1) + 1 := by
        have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      have hQE : (Q : ℝ) = (E : ℝ) * (p : ℝ) ^ (n ^ 2 - 1) := by
        have hdv : (d : ℝ) = (p : ℝ) ^ v * e := by rw [hde]; push_cast; ring
        have hmR : (m : ℝ) = (p : ℝ) ^ (n ^ 2 - 1 - v) := by simp [hm]
        simp only [hQ, hE]
        push_cast
        rw [hdv, hmR]
        have : (p : ℝ) ^ (n ^ 2 - 1) = (p : ℝ) ^ v * (p : ℝ) ^ (n ^ 2 - 1 - v) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; ring
      have hpow : (p : ℝ) ^ (n ^ 2) = (p : ℝ) ^ (n ^ 2 - 1) * p := by
        rw [← pow_succ]; congr 1
      push_cast
      rw [hQE, hpow]
      have hp1 : (p : ℝ) ^ (n ^ 2 - 1) ≠ 0 := pow_ne_zero _ hp0
      field_simp
    have h2 : ‖(((((E : ℝ) / p : ℝ))) : Circ)‖ < 1 / (p : ℝ) := by
      have : xt (Q : ℚ) 1 (p ^ (n ^ 2)) = ((((E : ℝ) / p : ℝ)) : Circ) := by
        unfold xt
        rw [hval]
      rwa [this] at h1
    have h3 := norm_div_prime_ge (E : ℤ) p hp.pos hpE
    push_cast at h3
    linarith

/-- **Theorem 22.2 (incomparability) for two distinct primes.**  Neither of `γ_p ⊆ γ_q`. -/
theorem prime_not_finer (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ xi (Cp q) ≤ xi (Cp p) := by
  intro hle
  have hV : xiSet (Cp p) 1 (1 / (p : ℝ)) ∈ @nhds ℚ (xi (Cp p)) 0 :=
    (xi_nhds_hasBasis (Cp p)).mem_of_mem (xiSet_mem (Cp p) 1 one_pos _ (by positivity [hp.pos]))
  have hV' : xiSet (Cp p) 1 (1 / (p : ℝ)) ∈ @nhds ℚ (xi (Cp q)) 0 := nhds_mono hle hV
  obtain ⟨s, ⟨d, hd, ε, hε, rfl⟩, hs⟩ := ((xi_nhds_hasBasis (Cp q)).mem_iff).mp hV'
  obtain ⟨Q, hQ1, hQ2⟩ := exists_sep p q hp hq hpq d ε hd hε
  exact hQ2 (hs hQ1)

/-- **Theorem 22.2 for the pair `(γ_2, γ_3)`.** -/
theorem gamma2_gamma3_incomparable :
    ¬ xi (Cp 3) ≤ xi (Cp 2) ∧ ¬ xi (Cp 2) ≤ xi (Cp 3) :=
  ⟨prime_not_finer 2 3 Nat.prime_two Nat.prime_three (by norm_num),
    prime_not_finer 3 2 Nat.prime_three Nat.prime_two (by norm_num)⟩

end PrimeSquares

end LeanCheck
