import LeanCheck.ThreePrimesDensityM13

/-! Axiom check for `ThreePrimesDensityM13`. -/

#print axioms ThreePrimesDensityM13.rigidity_M13
#print axioms ThreePrimesDensityM13.witness_of_density_M13
#print axioms ThreePrimesDensityM13.diagonal_of_sparse_M13

#check @ThreePrimesDensityM13.witness_of_density_M13
#check @ThreePrimesDensityM13.diagonal_of_sparse_M13

/-- The three primes of the article: bases `2, 3, 5` satisfy the conditions on the bases, so
diagonal density for them follows from the sparse-set hypothesis alone. -/
example (H : ∀ D : ℕ, 1 ≤ D → ∃ γ : ℝ, γ * (24 * (D : ℝ) ^ 2 * Real.log ((2 + 1 : ℕ) : ℝ)) < 1 ∧
      ∀ X0 : ℕ, ∃ X : ℕ, X0 ≤ X ∧ ∃ (W : Finset (Fin 2 → ℤ)) (u : (Fin 2 → ℤ) → ℤ),
        (X : ℝ) ^ 2 ≤ (Real.log X) ^ γ * W.card ∧ (∀ w ∈ W, ∀ i, |w i| ≤ 2 * (X : ℤ)) ∧
        (∀ w ∈ W, |u w| ≤ (X : ℤ)) ∧
        (∀ w ∈ W, TwoPrimesEffective.Small (![2, 3, 5] 0) (1 / D) (u w)) ∧
        (∀ w ∈ W, ∀ i : Fin 2, TwoPrimesEffective.Small (![2, 3, 5] i.succ) (1 / D) (u w - w i)))
    (b : Fin 3 → ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ z : ℤ, ∀ j, TwoPrimesEffective.Small (![2, 3, 5] j) ε (z - b j) :=
  ThreePrimesDensityM13.diagonal_of_sparse_M13 (m := 2) (by norm_num) ![2, 3, 5]
    (by intro j; fin_cases j <;> norm_num)
    (by intro i j h; fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | (simp; norm_num))
    H b ε hε

/-- The hypotheses of `witness_of_density_M13` on the set of shifts can be satisfied: with a radius
above `1/2` every integer is small, so the whole box with `u = 0` and `K = 1` qualifies. -/
example (p X : ℕ) :
    (X : ℝ) ^ 2 ≤ 1 * ((Fintype.piFinset fun _ : Fin 2 =>
        Finset.Icc (-(X : ℤ)) X).card : ℝ) ∧
      ∀ k : ℤ, TwoPrimesEffective.Small p 1 k := by
  constructor
  · rw [one_mul, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Int.card_Icc]
    have : X ≤ ((X : ℤ) + 1 - -(X : ℤ)).toNat := by omega
    exact_mod_cast Nat.pow_le_pow_left this 2
  · intro k n
    exact lt_of_le_of_lt (abs_sub_round _) (by norm_num)
