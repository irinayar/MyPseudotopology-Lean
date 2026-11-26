import LeanCheck.ThreePrimesHeightM11

/-! Axiom check for `ThreePrimesHeightM11`. -/

#print axioms LeanCheck.HeightM11.height_M11
#print axioms LeanCheck.HeightM11.all_targets_M11
#print axioms LeanCheck.HeightM11.square_isChainM11
#print axioms LeanCheck.HeightM11.square_coprimeM11
#print axioms LeanCheck.HeightM11.square_ratioM11

#check @LeanCheck.HeightM11.height_M11
#check @LeanCheck.HeightM11.all_targets_M11

/-- The corollary for prime-square chains, composed from the module: nothing but the covering
input is assumed. -/
example {m : ℕ} (p : Fin (m + 1) → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    {r0 c : ℝ} (hr0 : 0 < r0) (hr8 : r0 ≤ 1 / 8) (hc : 0 < c)
    (hI : ∀ X0 : ℕ, ∃ X : ℕ, X0 ≤ X ∧
      LeanCheck.HeightM11.Input (fun j n => p j ^ (n ^ 2)) r0 c X) (t : Fin m → ℤ) :
    ∃ k : ℤ, LeanCheck.HeightM11.Pn (fun n => p 0 ^ (n ^ 2)) k < 16 * r0 ∧
      ∀ i : Fin m, LeanCheck.HeightM11.Pn (fun n => p i.succ ^ (n ^ 2)) (k - t i) < 16 * r0 :=
  LeanCheck.HeightM11.all_targets_M11 (fun j n => p j ^ (n ^ 2))
    (fun j => LeanCheck.HeightM11.square_isChainM11 (hp j).two_le)
    (LeanCheck.HeightM11.square_coprimeM11 p hp hinj)
    (LeanCheck.HeightM11.square_ratioM11 p fun j => (hp j).two_le)
    hr0 hr8 hc hI t

/-- Sanity check that the hypotheses are not contradictory: with one chain (`m = 0`) the covering
input holds at every height. -/
example (Q : Fin 1 → ℕ → ℕ) (X : ℕ) : LeanCheck.HeightM11.Input Q (1 / 8) 1 X := by
  refine ⟨{fun i => i.elim0}, by simp, fun w _ => ⟨fun i => i.elim0, 0, by simp, ?_, fun i => i.elim0⟩⟩
  refine lt_of_le_of_lt (LeanCheck.HeightM11.Pn_le (b := 0) fun n => ?_) (by norm_num)
  simp [LeanCheck.HeightM11.nd]
