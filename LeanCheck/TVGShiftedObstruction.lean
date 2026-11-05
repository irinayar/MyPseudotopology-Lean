import Lean.Elab.Tactic.Omega

/-!
# TVGplus: a full CRT period with automatic tails cannot give a height bound for m >= p q

If `m P Q < U` and `m P Q < V` with `P = p^(n^2)`, `Q = q^(j^2)`, `U = p^((n+1)^2)`, `V = q^((j+1)^2)`, then `m < p q`.
(The two tail certificates at height `P Q`, which omit all denominators above `m P Q`, are possible only for `m < p q`.)
-/


namespace LeanCheck.ShiftedHeight

theorem square_exponent (n : Nat) :
    (n + 1) * (n + 1) ≤ 2 * (n * n) + 2 := by
  have h : ∀ j : Nat, 2 * j ≤ j * j + 1 := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
  have hn := h n
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

theorem next_level_bound {p : Nat} (hp : 0 < p) (n : Nat) :
    p ^ ((n + 1) * (n + 1)) ≤
      (p * p ^ (n * n)) * (p * p ^ (n * n)) := by
  calc
    _ ≤ p ^ (n * n + n * n + 2) := Nat.pow_le_pow_right hp (by
      have h := square_exponent n
      omega)
    _ = _ := by
      rw [Nat.pow_add, Nat.pow_add, Nat.pow_two]
      ac_rfl

theorem full_period_tail_obstruction {p q m n j : Nat}
    (hp : 0 < p) (hq : 0 < q)
    (htp : m * p ^ (n * n) * q ^ (j * j) < p ^ ((n + 1) * (n + 1)))
    (htq : m * p ^ (n * n) * q ^ (j * j) < q ^ ((j + 1) * (j + 1))) :
    m < p * q := by
  have hprod := Nat.mul_lt_mul_of_lt_of_lt htp htq
  have hu := Nat.mul_le_mul (next_level_bound hp n) (next_level_bound hq j)
  have he :
      (p * p ^ (n * n)) * (p * p ^ (n * n)) *
        ((q * q ^ (j * j)) * (q * q ^ (j * j))) =
      (p * q * p ^ (n * n) * q ^ (j * j)) *
        (p * q * p ^ (n * n) * q ^ (j * j)) := by ac_rfl
  rw [he] at hu
  have hs := Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_of_lt_of_le hprod hu)
  have hQ : 0 < q ^ (j * j) := Nat.pow_pos hq
  have hP : 0 < p ^ (n * n) := Nat.pow_pos hp
  exact (Nat.mul_lt_mul_right hP).mp ((Nat.mul_lt_mul_right hQ).mp hs)

#print axioms full_period_tail_obstruction
end LeanCheck.ShiftedHeight
