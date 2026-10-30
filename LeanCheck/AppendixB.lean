import Mathlib

/-!
# Appendix B of HamelCharactersTVG_v12: factorial segments

We model the circle group `𝕋 = ℝ / ℤ` as `AddCircle (1 : ℝ)`; its norm `‖t‖` is the distance from `t`
to the nearest integer (this is `AddCircle.norm_eq` in Mathlib).  The torsion group `A = ℚ / ℤ`
is the set of elements of finite additive order in `𝕋`.

Checked here:
* Lemma B.1  (contraction along a finite doubling segment)
* Proposition B.2 (the factorial-segment ball `U_C(ε)` contains only `0`; stated for torsion points)
* Proposition B.3 (the raw odd-index half does not separate `1/2` from `0`, so the profinite series
  `ψ = ∑ k!` is not continuous there; continuity is the paper's quarter-arc criterion)
-/

namespace LeanCheck

/-- The circle group `ℝ / ℤ`. -/
abbrev Circ : Type := AddCircle (1 : ℝ)

/-- Every point of the circle has a centered real representative, whose absolute value is the norm. -/
lemma exists_centered (t : Circ) : ∃ x : ℝ, (x : Circ) = t ∧ |x| ≤ 1 / 2 ∧ ‖t‖ = |x| := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hz : (((round y : ℤ) : ℝ) : Circ) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨round y, by simp⟩
  have hx : ((y - round y : ℝ) : Circ) = (y : Circ) := by
    rw [AddCircle.coe_sub, hz, sub_zero]
  refine ⟨y - round y, hx, abs_sub_round y, ?_⟩
  rw [← hx, AddCircle.norm_eq]
  simp

/-- Doubling a point of norm at most `1/4` doubles its norm. -/
lemma norm_two_nsmul (t : Circ) (h : ‖t‖ ≤ 1 / 4) : ‖(2 : ℕ) • t‖ = 2 * ‖t‖ := by
  obtain ⟨x, rfl, hx, hn⟩ := exists_centered t
  have h2 : (2 : ℕ) • (x : Circ) = ((2 * x : ℝ) : Circ) := by
    rw [two_mul, AddCircle.coe_add, two_nsmul]
  have hx4 : |x| ≤ 1 / 4 := by rw [← hn]; exact h
  have h2x : |2 * x| ≤ 1 / 2 := by
    rw [abs_mul]; norm_num; linarith
  rw [h2, (AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) one_ne_zero).2 (by simpa using h2x), hn, abs_mul]
  norm_num

/-- **Lemma B.1** (contraction along a finite doubling segment). -/
lemma lemmaB1 (J : ℕ) : ∀ (t : Circ) (ε : ℝ), 0 < ε → ε < 1 / 8 →
    (∀ j ≤ J, ‖(2 ^ j : ℕ) • t‖ < ε) → ‖t‖ < ε / 2 ^ J := by
  induction J with
  | zero =>
    intro t ε _ _ h
    simpa using h 0 le_rfl
  | succ J ih =>
    intro t ε h0 h8 h
    have h' : ∀ j ≤ J, ‖(2 ^ j : ℕ) • ((2 : ℕ) • t)‖ < ε := by
      intro j hj
      have := h (j + 1) (by omega)
      rw [smul_smul, ← pow_succ]; exact this
    have h2 := ih ((2 : ℕ) • t) ε h0 h8 h'
    have ht : ‖t‖ < ε := by simpa using h 0 (by omega)
    have h4 : ‖t‖ ≤ 1 / 4 := by linarith
    rw [norm_two_nsmul t h4] at h2
    have : ‖t‖ < ε / 2 ^ J / 2 := by linarith
    calc ‖t‖ < ε / 2 ^ J / 2 := this
      _ = ε / 2 ^ (J + 1) := by rw [pow_succ]; field_simp

/-- A nonzero point killed by `m` has norm at least `1/m`. -/
lemma inv_le_norm (t : Circ) (m : ℕ) (hm : 0 < m) (h : m • t = 0) (ht : t ≠ 0) :
    1 / (m : ℝ) ≤ ‖t‖ := by
  obtain ⟨x, rfl, hx, hn⟩ := exists_centered t
  have h' : ((m * x : ℝ) : Circ) = 0 := by
    rw [← h, ← AddCircle.coe_nsmul]; simp
  obtain ⟨n, hn'⟩ := (AddCircle.coe_eq_zero_iff 1).1 h'
  have hx0 : x ≠ 0 := by
    rintro rfl; apply ht; simp
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn'
    rcases hn' with h1 | h1
    · omega
    · exact hx0 h1
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
  have h2 : |(n : ℝ)| = m * |x| := by
    have : (n : ℝ) = m * x := by simpa using hn'
    rw [this, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ m)]
  rw [hn]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hmpos]
  nlinarith

/-- The factorial-segment observations `k! * 2^j`, `1 ≤ k`, `0 ≤ j ≤ J k`. -/
def segSet (J : ℕ → ℕ) : Set ℕ := {c | ∃ k, 1 ≤ k ∧ ∃ j ≤ J k, c = k.factorial * 2 ^ j}

/-- **Proposition B.2**: for torsion `x`, if all observations of the factorial-segment family are
smaller than `ε < 1/8`, then `x = 0` (i.e. `U_C(ε) = {0}`, the topology is discrete). -/
theorem propB2 (J : ℕ → ℕ) (hJ : ∀ k, 1 ≤ k → k ≤ J k) (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 8)
    (x : Circ) (hx : IsOfFinAddOrder x) (hall : ∀ c ∈ segSet J, ‖c • x‖ < ε) : x = 0 := by
  by_contra hx0
  obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hx
  have hex : ∃ m, 2 ≤ m ∧ m.factorial • x = 0 := by
    refine ⟨max n 2, le_max_right _ _, ?_⟩
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hn (le_max_left n 2)
    rw [hc, mul_comm, ← smul_smul, hnx, smul_zero]
  classical
  set m := Nat.find hex with hm
  have hm2 : 2 ≤ m := (Nat.find_spec hex).1
  have hm0 : m.factorial • x = 0 := (Nat.find_spec hex).2
  have hprev : ((m - 1).factorial) • x ≠ 0 := by
    by_cases h1 : m - 1 = 1
    · rw [h1]; simpa using hx0
    · intro hz
      exact Nat.find_min hex (show m - 1 < m by omega) ⟨by omega, hz⟩
  set t := ((m - 1).factorial) • x with ht
  have hmt : m • t = 0 := by
    rw [ht, smul_smul, Nat.mul_factorial_pred (by omega)]; exact hm0
  have hlow := inv_le_norm t m (by omega) hmt hprev
  have hseg : ∀ j ≤ J (m - 1), ‖(2 ^ j : ℕ) • t‖ < ε := by
    intro j hj
    have := hall ((m - 1).factorial * 2 ^ j) ⟨m - 1, by omega, j, hj, rfl⟩
    rw [ht, smul_smul, mul_comm]
    exact this
  have hup := lemmaB1 (J (m - 1)) t ε hε0 hε hseg
  have h2m : (m : ℝ) ≤ 2 ^ (J (m - 1)) := by
    have h1 : m - 1 < 2 ^ (m - 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ (m - 1) ≤ 2 ^ (J (m - 1)) :=
      Nat.pow_le_pow_right (by norm_num) (hJ (m - 1) (by omega))
    have h3 : m ≤ 2 ^ (J (m - 1)) := by omega
    exact_mod_cast h3
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hpos2 : (0 : ℝ) < 2 ^ (J (m - 1)) := by positivity
  have h5 : ε / 2 ^ (J (m - 1)) ≤ ε / m := by
    apply div_le_div_of_nonneg_left hε0.le hmpos h2m
  have h6 : ε / m < 1 / m := by
    apply div_lt_div_of_pos_right _ hmpos; linarith
  linarith


/-! ### Proposition B.3: the raw odd-index half -/

/-- Observations `k! * 2^j` with `j` odd. -/
def oddSet (J : ℕ → ℕ) : Set ℕ := {c | ∃ k, 1 ≤ k ∧ ∃ j ≤ J k, Odd j ∧ c = k.factorial * 2 ^ j}

/-- The point `1/2 + ℤ`. -/
noncomputable def half : Circ := ((1 / 2 : ℝ) : Circ)

lemma two_nsmul_half : (2 : ℕ) • half = 0 := by
  unfold half
  rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff 1]
  exact ⟨1, by simp⟩

lemma half_ne_zero : half ≠ 0 := by
  intro h
  have : ‖half‖ = 1 / 2 := by
    unfold half
    have := AddCircle.norm_half_period_eq (p := (1 : ℝ))
    simpa using this
  rw [h, norm_zero] at this
  norm_num at this

lemma norm_half : ‖half‖ = 1 / 2 := by
  unfold half
  have := AddCircle.norm_half_period_eq (p := (1 : ℝ))
  simpa using this

/-- Every observation of the odd half is an even number, hence kills `1/2`. -/
lemma odd_obs_even (J : ℕ → ℕ) {c : ℕ} (hc : c ∈ oddSet J) : Even c := by
  obtain ⟨k, hk, j, hj, hodd, rfl⟩ := hc
  obtain ⟨i, rfl⟩ := hodd
  exact ⟨k.factorial * 2 ^ (2 * i), by rw [pow_succ]; ring⟩

/-- The profinite series `ψ(x) = ∑_{k ≥ 1} k! • x` (a finite sum at each torsion point). -/
noncomputable def psi (x : Circ) : Circ := ∑ᶠ k : ℕ, if 1 ≤ k then k.factorial • x else 0


lemma obs_kills_half (J : ℕ → ℕ) {c : ℕ} (hc : c ∈ oddSet J) : c • half = 0 := by
  obtain ⟨r, hr⟩ := odd_obs_even J hc
  rw [hr, add_nsmul, ← nsmul_add, ← two_nsmul, two_nsmul_half, smul_zero]

lemma psi_half : psi half = half := by
  unfold psi
  rw [finsum_eq_single _ 1]
  · simp
  · intro k hk
    by_cases h1 : 1 ≤ k
    · have h2 : 2 ≤ k := by omega
      obtain ⟨c, hc⟩ := Nat.dvd_factorial (by norm_num : 0 < 2) h2
      simp only [h1, ite_true]
      rw [hc, mul_nsmul, two_nsmul_half, smul_zero]
    · simp [h1]

/-- **Proposition B.3** (quarter-arc form): for the raw odd-index family there is no `ε > 0` such that the
profinite series `ψ` has all values of norm at most `1/4` on the ball `{x : ∀ c ∈ oddSet, ‖c • x‖ < ε}`.
Hence `ψ` is not continuous for the topology generated by the raw odd half, by the quarter-arc criterion
quoted in the paper. -/
theorem propB3 (J : ℕ → ℕ) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Circ, IsOfFinAddOrder x → (∀ c ∈ oddSet J, ‖c • x‖ < ε) →
      ‖psi x‖ ≤ 1 / 4 := by
  rintro ⟨ε, hε, h⟩
  have hhalf : IsOfFinAddOrder half :=
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨2, by norm_num, two_nsmul_half⟩
  have := h half hhalf (fun c hc => by rw [obs_kills_half J hc, norm_zero]; exact hε)
  rw [psi_half, norm_half] at this
  norm_num at this

/-- The point `1/2` lies in every ball of the raw odd half, although `1/2 ≠ 0`
(so the raw odd half is not Hausdorff). -/
theorem odd_half_not_hausdorff (J : ℕ → ℕ) :
    half ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∀ c ∈ oddSet J, ‖c • half‖ < ε := by
  refine ⟨half_ne_zero, fun ε hε c hc => ?_⟩
  rw [obs_kills_half J hc, norm_zero]; exact hε

end LeanCheck
