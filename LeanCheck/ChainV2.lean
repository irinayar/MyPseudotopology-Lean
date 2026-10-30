import LeanCheck.ChainV1

/-!
# Factorial chains and a corrected null sequence
(TVGQ-v7 Proposition 17.5 `chains:factorial`; HamelCharactersTVG_v18 Proposition D.5)

The chain `1!, 2!, 3!, …` is `facM n = (n+1)!`.  We prove:

* every nonempty subset has `H`, so `dual(ξ_{facM''U}) = Γ`;
* the full-chain topology `ξ` is coarser than the usual topology of `ℚ` and not equal to it;
* with `N_j = (j!)²`, the integers `q_j = j!·N_j!` tend to zero in `ξ` although `q_j → ∞` usually;
* `((n!)!)` is not a null sequence (observation `k = n!`, `d = 2` gives circle norm `1/2`).
-/

namespace LeanCheck

open Filter Topology

section Factorial

/-- The factorial chain `1!, 2!, 3!, …`. -/
def facM (n : ℕ) : ℕ := (n + 1).factorial

lemma facM_chain : ChainSeq facM where
  pos n := Nat.factorial_pos _
  dvd n := Nat.factorial_dvd_factorial (Nat.le_succ _)
  two n := by
    show 2 * (n + 1).factorial ≤ (n + 2).factorial
    rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ]
    exact Nat.mul_le_mul_right _ (by omega)

/-- Every subset of the factorial chain satisfies `H`: consecutive ratios tend to infinity. -/
lemma HSet_fac (U : Set ℕ) : HSet facM U := by
  intro A hA
  refine ⟨⌈A⌉₊, fun k w hw => ?_⟩
  by_contra hk
  push_neg at hk
  have hj : ∀ j, j < k → (w j : ℝ) + 2 < A := fun j hj => by
    obtain ⟨h1, h2⟩ := hw.2 j hj
    have h3 : facM (w j + 1) ≤ facM (w (j + 1)) := facM_chain.mono h1
    have h4 : facM (w j + 1) = (w j + 2) * facM (w j) := by
      show (w j + 1 + 1).factorial = (w j + 2) * (w j + 1).factorial
      rw [Nat.factorial_succ]
    have hpos : (0 : ℝ) < facM (w j) := by exact_mod_cast facM_chain.pos _
    have h5 : (((w j : ℝ) + 2) * facM (w j)) ≤ facM (w (j + 1)) := by
      have : ((facM (w j + 1) : ℕ) : ℝ) ≤ facM (w (j + 1)) := by exact_mod_cast h3
      rw [h4] at this
      push_cast at this
      exact this
    have h6 : ((w j : ℝ) + 2) * facM (w j) < A * facM (w j) := lt_of_le_of_lt h5 h2
    exact lt_of_mul_lt_mul_right h6 hpos.le
  have hwj : ∀ j, j ≤ k → j ≤ w j := by
    intro j
    induction j with
    | zero => intro _; exact Nat.zero_le _
    | succ j ih =>
      intro hjk
      have := (hw.2 j (by omega)).1
      have := ih (by omega)
      omega
  have h1 := hj (k - 1) (by omega)
  have h2 := hwj (k - 1) (by omega)
  have h3 : ((k - 1 : ℕ) : ℝ) ≤ w (k - 1) := by exact_mod_cast h2
  have h4 : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
    have : k = (k - 1) + 1 := by omega
    exact_mod_cast this
  have h5 : A ≤ ⌈A⌉₊ := Nat.le_ceil A
  have h6 : (⌈A⌉₊ : ℝ) < k := by exact_mod_cast hk
  linarith

/-- For the factorial chain, all nonempty subset topologies have full dual `Γ`. -/
theorem fac_full_dual (U : Set ℕ) (hU : U.Nonempty) :
    ∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ (xi (facM '' U)) circTop ψ ↔ ψ ∈ Gam :=
  (chains_F_set facM_chain U hU).2 (HSet_fac U)

/-- `ξ_C` is coarser than the usual topology of `ℚ`. -/
theorem usual_le_xi (C : Set ℕ) : (inferInstance : TopologicalSpace ℚ) ≤ xi C := by
  refine le_of_nhds_le_nhds (fun x => ?_)
  refine ((xiBasis C).nhds_hasBasis x).ge_iff.2 ?_
  rintro V ⟨d, hd, ε, hε, rfl⟩
  have hball : Metric.ball ((x : ℝ)) ε ∩ Set.range ((↑) : ℚ → ℝ) ⊆ ((↑) : ℚ → ℝ) '' ((fun y => x + y) '' xiSet C d ε) := by
    rintro _ ⟨hb, ⟨y, rfl⟩⟩
    refine ⟨x + (y - x), ⟨y - x, ?_, rfl⟩, by push_cast; ring⟩
    apply xiSet_ball C d hd ε
    rw [Metric.mem_ball, Real.dist_eq] at hb
    push_cast
    exact hb
  have : ((fun y => x + y) '' xiSet C d ε) ∈ (𝓝 x : Filter ℚ) := by
    have hnh : ((↑) ⁻¹' Metric.ball (x : ℝ) ε : Set ℚ) ∈ (𝓝 x : Filter ℚ) :=
      Rat.continuous_coe_real.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    refine Filter.mem_of_superset hnh ?_
    intro y hy
    have := hball ⟨hy, ⟨y, rfl⟩⟩
    obtain ⟨z, hz, hzy⟩ := this
    have : z = y := by exact_mod_cast hzy
    rw [← this]; exact hz
  exact this

/-- The null sequence of the factorial chain. -/
def Nfac (j : ℕ) : ℕ := (j.factorial) ^ 2

/-- `q_j = j! · N_j!`. -/
def qfac (j : ℕ) : ℕ := j.factorial * (Nfac j).factorial

lemma qfac_pos (j : ℕ) : 0 < qfac j := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)

/-- `q_j → 0` in `ξ_{range facM}`. -/
theorem qfac_null : Tendsto (fun j => ((qfac j : ℕ) : ℚ)) atTop (@nhds ℚ (xi (Set.range facM)) 0) := by
  rw [(xi_nhds_hasBasis (Set.range facM)).tendsto_right_iff]
  rintro V ⟨d, hd, ε, hε, rfl⟩
  obtain ⟨J1, hJ1⟩ := exists_nat_gt (1 / ε)
  have hJ : ∀ j ≥ max d (J1 + 1), d ∣ j.factorial ∧ 1 / (j.factorial : ℝ) < ε := by
    intro j hj
    have hdj : d ≤ j := (le_max_left _ _).trans hj
    have hjJ : J1 + 1 ≤ j := (le_max_right _ _).trans hj
    refine ⟨Nat.dvd_factorial hd hdj, ?_⟩
    have hjf : (j : ℝ) ≤ j.factorial := by exact_mod_cast Nat.self_le_factorial j
    have hjpos : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    have hj1 : (J1 : ℝ) + 1 ≤ j := by exact_mod_cast hjJ
    rw [div_lt_iff₀ hjpos]
    rw [div_lt_iff₀ hε] at hJ1
    nlinarith
  filter_upwards [eventually_ge_atTop (max d (J1 + 1))] with j hj
  obtain ⟨⟨a, ha⟩, hjε⟩ := hJ j hj
  rintro c ⟨n, rfl⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hfac : ((facM n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (facM_chain.pos n).ne'
  by_cases hk : n + 1 ≤ Nfac j
  · -- the quotient is an integer
    obtain ⟨b, hb⟩ : (n + 1).factorial ∣ (Nfac j).factorial := Nat.factorial_dvd_factorial hk
    have hq : ((qfac j : ℕ) : ℚ) / ((d : ℚ) * (facM n : ℕ)) = ((a * b : ℕ) : ℚ) := by
      have e1 : (qfac j : ℕ) = d * a * ((n + 1).factorial * b) := by
        unfold qfac; rw [ha, hb]
      rw [e1]
      show _ / ((d : ℚ) * ((n + 1).factorial : ℕ)) = _
      have hf' : (((n + 1).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
      push_cast
      field_simp
    have h0 : (((((qfac j : ℕ) : ℚ) / ((d : ℚ) * (facM n : ℕ)) : ℚ) : ℝ) : Circ) = 0 := by
      rw [hq, circ_zero_iff]
      exact ⟨(a * b : ℕ), by push_cast; rfl⟩
    show ‖(((((qfac j : ℕ) : ℚ) / ((d : ℚ) * (facM n : ℕ)) : ℚ) : ℝ) : Circ)‖ < ε
    rw [h0, norm_zero]; exact hε
  · -- the quotient is small
    push_neg at hk
    have hbig : Nfac j + 1 ≤ n + 1 := hk
    have hfj : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    have hfn : ((Nfac j + 1).factorial : ℝ) ≤ (n + 1).factorial := by
      exact_mod_cast Nat.factorial_le hbig
    have hsucc : ((Nfac j + 1).factorial : ℝ) = (Nfac j + 1) * (Nfac j).factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hNf : (0 : ℝ) < (Nfac j).factorial := by exact_mod_cast Nat.factorial_pos _
    have hNj : (Nfac j : ℝ) = (j.factorial : ℝ) ^ 2 := by unfold Nfac; push_cast; ring
    show ‖(((((qfac j : ℕ) : ℚ) / ((d : ℚ) * (facM n : ℕ)) : ℚ) : ℝ) : Circ)‖ < ε
    refine lt_of_le_of_lt (norm_coe_le _ 0) ?_
    rw [Int.cast_zero, sub_zero]
    push_cast
    have hqd : (qfac j : ℝ) = j.factorial * (Nfac j).factorial := by unfold qfac; push_cast; ring
    have hfacn : (facM n : ℝ) = (n + 1).factorial := by unfold facM; rfl
    rw [hqd, hfacn]
    have hfpos : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [abs_of_nonneg (by positivity)]
    have h1 : (j.factorial : ℝ) * (Nfac j).factorial / (d * (n + 1).factorial) ≤
        (j.factorial : ℝ) * (Nfac j).factorial / ((Nfac j + 1) * (Nfac j).factorial) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      calc ((Nfac j : ℝ) + 1) * (Nfac j).factorial = ((Nfac j + 1).factorial : ℝ) := hsucc.symm
        _ ≤ (n + 1).factorial := hfn
        _ ≤ d * (n + 1).factorial := by nlinarith
    have h2 : (j.factorial : ℝ) * (Nfac j).factorial / ((Nfac j + 1) * (Nfac j).factorial)
        = j.factorial / ((Nfac j) + 1) := by
      field_simp
    rw [h2] at h1
    have h3 : (j.factorial : ℝ) / ((Nfac j) + 1) < 1 / j.factorial := by
      rw [div_lt_div_iff₀ (by positivity) hfj, hNj]
      nlinarith
    linarith

/-- `q_j → ∞` in the usual topology; in particular `q_j` is not null there. -/
theorem qfac_not_null_usual : ¬ Tendsto (fun j => ((qfac j : ℕ) : ℚ)) atTop (𝓝 0) := by
  intro h
  have h1 : Tendsto (fun j => ((qfac j : ℕ) : ℚ)) atTop (𝓝 0) := h
  have h2 := (Metric.tendsto_nhds.1 (Rat.continuous_coe_real.tendsto 0 |>.comp h1)) (1 / 2) (by norm_num)
  obtain ⟨j, hj⟩ := h2.exists
  simp only [Function.comp_apply, Rat.cast_zero, Real.dist_eq, sub_zero] at hj
  have : (1 : ℝ) ≤ ((qfac j : ℕ) : ℝ) := by exact_mod_cast qfac_pos j
  push_cast at hj
  rw [abs_of_nonneg (by positivity)] at hj
  linarith

/-- The uncorrected sequence `(n!)!` is not null: observation `k = n!`, `d = 2` gives circle norm `1/2`. -/
theorem fac_fac_not_null : ¬ Tendsto (fun n : ℕ => (((n + 2).factorial.factorial : ℕ) : ℚ)) atTop
    (@nhds ℚ (xi (Set.range facM)) 0) := by
  intro h
  rw [(xi_nhds_hasBasis (Set.range facM)).tendsto_right_iff] at h
  have h1 := h (xiSet (Set.range facM) 2 (1 / 2)) ⟨2, by norm_num, 1 / 2, by norm_num, rfl⟩
  obtain ⟨n, hn⟩ := h1.exists
  have hmem := hn (facM ((n + 2).factorial - 1)) ⟨(n + 2).factorial - 1, rfl⟩
  have hpos : 0 < (n + 2).factorial := Nat.factorial_pos _
  have hfm : facM ((n + 2).factorial - 1) = (n + 2).factorial.factorial := by
    unfold facM; congr 1; omega
  rw [hfm] at hmem
  have hF : (((n + 2).factorial.factorial : ℕ) : ℚ) /
      (((2 : ℕ) : ℚ) * (((n + 2).factorial.factorial : ℕ) : ℚ)) = 1 / 2 := by
    have : (((n + 2).factorial.factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    push_cast
    field_simp
  rw [hF] at hmem
  push_cast at hmem
  have : ‖(((1 / 2 : ℝ)) : Circ)‖ = 1 / 2 := by
    rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by norm_num)]
    norm_num
  rw [this] at hmem
  exact lt_irrefl _ hmem

/-- **Proposition 17.5 / D.5**, strictness: the full-chain topology `ξ_{range facM}` is coarser than, and not equal
to, the usual topology of `ℚ`. -/
theorem xi_fac_strict : (inferInstance : TopologicalSpace ℚ) < xi (Set.range facM) := by
  refine lt_of_le_of_ne (usual_le_xi _) (fun heq => ?_)
  apply qfac_not_null_usual
  have := qfac_null
  rw [← heq] at this
  exact this

end Factorial

end LeanCheck
