import LeanCheck.ChainE5

/-!
# Reduction of the prime-square candidate to an integer polar problem
(HamelCharactersTVG_v18 Proposition 22.4 `prop:integer-v8`)

On `ℤ` let `P(k) = max{P_{2,1}(k), P_{3,1}(k)}` (`P_{p,1}(k) = sup_n ‖k/p^{n²}‖`) and let `ω` be the metric topology of `P`.
Put `H = {α ∈ ℝ : k ↦ p(α k) is ω-continuous}` (`Hint`, with the `ε`–`δ` definition of continuity at `0`).
Then `γ_2 ∨ γ_3` is compatible with `Γ` iff every `α ∈ H` is rational.
-/

namespace LeanCheck

open Filter Topology

section IntegerPolar

lemma xt_add (a b : ℚ) (d c : ℕ) : xt (a + b) d c = xt a d c + xt b d c := by
  unfold xt
  rw [add_div]; push_cast; rw [AddCircle.coe_add]

lemma xt_sub (a b : ℚ) (d c : ℕ) : xt (a - b) d c = xt a d c - xt b d c := by
  unfold xt
  rw [sub_div]; push_cast; rw [AddCircle.coe_sub]

lemma xt_nat_mul (j : ℕ) (q : ℚ) (d c : ℕ) : xt ((j : ℚ) * q) d c = j • xt q d c := by
  unfold xt
  rw [nsmul_coe_circ]
  congr 1
  push_cast
  ring

lemma xt_norm_le (q : ℚ) (d c : ℕ) (hd : 1 ≤ d) (hc : 1 ≤ c) : ‖xt q d c‖ ≤ |(q : ℝ)| := by
  unfold xt
  refine (norm_coe_le _ 0).trans ?_
  rw [Int.cast_zero, sub_zero]
  push_cast
  rw [abs_div]
  have h1 : (1 : ℝ) ≤ |(d : ℝ) * c| := by
    rw [abs_of_nonneg (by positivity)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have : (1 : ℝ) ≤ c := by exact_mod_cast hc
    nlinarith
  calc |(q : ℝ)| / |(d : ℝ) * c| ≤ |(q : ℝ)| / 1 := by
        apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos h1
    _ = |(q : ℝ)| := div_one _

/-- `P(q) < δ` at denominator parameter `d`. -/
def PltQ (q : ℚ) (d : ℕ) (δ : ℝ) : Prop := q ∈ xiSet (Cp 2) d δ ∧ q ∈ xiSet (Cp 3) d δ

/-- `α ∈ H`: the character `k ↦ p(α k)` of `ℤ` is continuous for the metric `P` (at `0`). -/
def Hint (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℤ, PltQ (k : ℚ) 1 δ → ‖((α * (k : ℝ) : ℝ) : Circ)‖ < ε

lemma one_mem_Cp (p : ℕ) : 1 ∈ Cp p := mem_Cp.2 ⟨0, by simp⟩

lemma Cp_pos' {p : ℕ} (hp : 2 ≤ p) {c : ℕ} (hc : c ∈ Cp p) : 1 ≤ c := Cp_pos hp c hc

/-- Observation `n = 0`: if `q` is in the ball then `q` is within `δ` of an integer `k`, and `k` is in the doubled ball. -/
lemma near_int_in_ball (q : ℚ) (δ : ℝ) (hq : PltQ q 1 δ) :
    ∃ k : ℤ, |(q : ℝ) - k| < δ ∧ PltQ (k : ℚ) 1 (2 * δ) := by
  have h1 : ‖xt q 1 1‖ < δ := hq.1 1 (one_mem_Cp 2)
  have h1' : ‖(((q : ℝ)) : Circ)‖ < δ := by
    have : xt q 1 1 = ((q : ℝ) : Circ) := by unfold xt; simp
    rwa [this] at h1
  obtain ⟨k, hk⟩ := exists_int_of_norm_lt h1'
  refine ⟨k, hk, ?_, ?_⟩
  · intro c hc
    have hc1 := Cp_pos' (by norm_num : 2 ≤ 2) hc
    have h2 : ‖xt q 1 c‖ < δ := hq.1 c hc
    have e : xt (k : ℚ) 1 c = xt q 1 c - xt (q - (k : ℚ)) 1 c := by rw [← xt_sub]; congr 1; ring
    have h3 : ‖xt (q - (k : ℚ)) 1 c‖ ≤ |(((q - (k : ℚ) : ℚ)) : ℝ)| := xt_norm_le _ 1 c le_rfl hc1
    have h4 : |(((q - (k : ℚ) : ℚ)) : ℝ)| < δ := by push_cast; exact hk
    show ‖xt (k : ℚ) 1 c‖ < 2 * δ
    rw [e]
    calc ‖xt q 1 c - xt (q - (k : ℚ)) 1 c‖ ≤ ‖xt q 1 c‖ + ‖xt (q - (k : ℚ)) 1 c‖ := norm_sub_le _ _
      _ < 2 * δ := by linarith
  · intro c hc
    have hc1 := Cp_pos' (by norm_num : 2 ≤ 3) hc
    have h2 : ‖xt q 1 c‖ < δ := hq.2 c hc
    have e : xt (k : ℚ) 1 c = xt q 1 c - xt (q - (k : ℚ)) 1 c := by rw [← xt_sub]; congr 1; ring
    have h3 : ‖xt (q - (k : ℚ)) 1 c‖ ≤ |(((q - (k : ℚ) : ℚ)) : ℝ)| := xt_norm_le _ 1 c le_rfl hc1
    have h4 : |(((q - (k : ℚ) : ℚ)) : ℝ)| < δ := by push_cast; exact hk
    show ‖xt (k : ℚ) 1 c‖ < 2 * δ
    rw [e]
    calc ‖xt q 1 c - xt (q - (k : ℚ)) 1 c‖ ≤ ‖xt q 1 c‖ + ‖xt (q - (k : ℚ)) 1 c‖ := norm_sub_le _ _
      _ < 2 * δ := by linarith

/-- Extraction of a joint neighbourhood: continuity of `χ` in the join gives one denominator `d` and radius `ε`. -/
lemma join_cont_extract (χ : ℚ →+ Circ) (h : @Continuous ℚ Circ (xi (Cp 2) ⊓ xi (Cp 3)) circTop χ) :
    ∃ d : ℕ, 0 < d ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℚ, PltQ q d ε → ‖χ q‖ < 1 / 4 := by
  have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (χ 0) := by
    rw [map_zero]
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  have hpre : χ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} ∈ @nhds ℚ (xi (Cp 2) ⊓ xi (Cp 3)) 0 :=
    (@Continuous.continuousAt ℚ Circ (xi (Cp 2) ⊓ xi (Cp 3)) _ χ 0 h) hS
  rw [@nhds_inf ℚ (xi (Cp 2)) (xi (Cp 3)) 0] at hpre
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := Filter.mem_inf_iff_superset.1 hpre
  obtain ⟨s₁, ⟨d₁, hd₁, ε₁, hε₁, rfl⟩, hs₁⟩ := ((xi_nhds_hasBasis (Cp 2)).mem_iff).mp hU₁
  obtain ⟨s₂, ⟨d₂, hd₂, ε₂, hε₂, rfl⟩, hs₂⟩ := ((xi_nhds_hasBasis (Cp 3)).mem_iff).mp hU₂
  refine ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, min (ε₁ / d₂) (ε₂ / d₁), lt_min (by positivity) (by positivity),
    fun q hq => ?_⟩
  have hd₂r : (0 : ℝ) < d₂ := by exact_mod_cast hd₂
  have hd₁r : (0 : ℝ) < d₁ := by exact_mod_cast hd₁
  have hq1 : q ∈ xiSet (Cp 2) d₁ ε₁ := by
    have := xiSet_mono (Cp 2) d₁ d₂ hd₂ ε₁
    exact this (fun c hc => lt_of_lt_of_le (hq.1 c hc) (min_le_left _ _))
  have hq2 : q ∈ xiSet (Cp 3) d₂ ε₂ := by
    have := xiSet_mono (Cp 3) d₂ d₁ hd₁ ε₂
    rw [mul_comm d₂ d₁] at this
    exact this (fun c hc => lt_of_lt_of_le (hq.2 c hc) (min_le_right _ _))
  have : q ∈ U₁ ∩ U₂ := ⟨hs₁ hq1, hs₂ hq2⟩
  exact hsub this

/-- **Proposition 22.4.** `γ₂ ∨ γ₃` is compatible with `Γ` iff `H ⊆ ℚ/ℤ`. -/
theorem integer_polar_reduction :
    (∀ χ : ℚ →+ Circ, @Continuous ℚ Circ (xi (Cp 2) ⊓ xi (Cp 3)) circTop χ → χ ∈ Gam) ↔
      ∀ α : ℝ, Hint α → ∃ r : ℚ, α = r := by
  have hg2 := gamma_p_mem 2 le_rfl
  have hg3 := gamma_p_mem 3 (by norm_num)
  constructor
  · intro hcompat α hα
    by_contra hnot
    have hirr : Irrational α := fun ⟨r, hr⟩ => hnot ⟨r, hr.symm⟩
    obtain ⟨δ, hδ, hH⟩ := hα (1 / 8) (by norm_num)
    set δ' : ℝ := min (δ / 2) (1 / (16 * (|α| + 1))) with hδ'
    have hδ'pos : 0 < δ' := lt_min (by positivity) (by positivity)
    have hcont : @Continuous ℚ Circ (xi (Cp 2) ⊓ xi (Cp 3)) circTop (psiQ α) := by
      refine cont_join_closed_quarter (xi (Cp 2)) (xi (Cp 3)) hg2.1.1 hg3.1.1 (psiQ α)
        (xiSet (Cp 2) 1 δ') (xiSet (Cp 3) 1 δ')
        ((xi_nhds_hasBasis (Cp 2)).mem_of_mem (xiSet_mem (Cp 2) 1 one_pos δ' hδ'pos))
        ((xi_nhds_hasBasis (Cp 3)).mem_of_mem (xiSet_mem (Cp 3) 1 one_pos δ' hδ'pos))
        (fun q hq => ?_)
      obtain ⟨k, hk1, hk2⟩ := near_int_in_ball q δ' ⟨hq.1, hq.2⟩
      have hk2' : PltQ (k : ℚ) 1 δ := by
        have : 2 * δ' ≤ δ := by have := min_le_left (δ / 2) (1 / (16 * (|α| + 1))); linarith
        exact ⟨fun c hc => lt_of_lt_of_le (hk2.1 c hc) this, fun c hc => lt_of_lt_of_le (hk2.2 c hc) this⟩
      have h1 := hH k hk2'
      have e : psiQ α q = ((α * (k : ℝ) : ℝ) : Circ) + ((α * ((q : ℝ) - k) : ℝ) : Circ) := by
        rw [psiQ_apply, ← AddCircle.coe_add]; congr 1; ring
      rw [e]
      have h2 : ‖((α * ((q : ℝ) - k) : ℝ) : Circ)‖ ≤ |α| * δ' := by
        refine (norm_coe_le _ 0).trans ?_
        rw [Int.cast_zero, sub_zero, abs_mul]
        exact mul_le_mul_of_nonneg_left hk1.le (abs_nonneg _)
      have h3 : |α| * δ' ≤ 1 / 16 := by
        have : δ' ≤ 1 / (16 * (|α| + 1)) := min_le_right _ _
        calc |α| * δ' ≤ |α| * (1 / (16 * (|α| + 1))) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
          _ ≤ 1 / 16 := by
              rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith [abs_nonneg α]
      calc ‖((α * (k : ℝ) : ℝ) : Circ) + ((α * ((q : ℝ) - k) : ℝ) : Circ)‖
          ≤ ‖((α * (k : ℝ) : ℝ) : Circ)‖ + ‖((α * ((q : ℝ) - k) : ℝ) : Circ)‖ := norm_add_le _ _
        _ ≤ 1 / 4 := by linarith
    exact psiQ_not_Gam hirr (hcompat _ hcont)
  · intro hH χ hχ
    obtain ⟨d, hd, ε, hε, hsmall⟩ := join_cont_extract χ hχ
    -- `χ` is usual-continuous near `0`, hence `χ q = p(c q)`
    obtain ⟨c, hc⟩ := char_Q_real χ ε hε (fun q hq => hsmall q
      ⟨xiSet_ball _ d hd ε q hq, xiSet_ball _ d hd ε q hq⟩)
    -- `α = c d` lies in `H`
    have hα : Hint ((c * d : ℝ)) := by
      intro ε'' hε''
      obtain ⟨R, hR1, hRε⟩ := exists_R ε'' hε''
      have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
      refine ⟨ε / R, by positivity, fun k hk => ?_⟩
      have hall : ∀ j : ℕ, j ≤ R → ‖j • ((((c * d : ℝ) * (k : ℝ) : ℝ)) : Circ)‖ < 1 / 4 := by
        intro j hj
        have hjR : (j : ℝ) ≤ R := by exact_mod_cast hj
        have hmem : PltQ ((d : ℚ) * ((j : ℚ) * (k : ℚ))) d ε := by
          have key : ∀ (p : ℕ) (hp : 2 ≤ p), (k : ℚ) ∈ xiSet (Cp p) 1 (ε / R) →
              ((d : ℚ) * ((j : ℚ) * (k : ℚ))) ∈ xiSet (Cp p) d ε := by
            intro p hp hkp c' hc'
            have hc1 := Cp_pos' hp hc'
            have h1 : ‖xt (k : ℚ) 1 c'‖ < ε / R := hkp c' hc'
            have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
            have hc0 : (c' : ℝ) ≠ 0 := by exact_mod_cast (by omega : c' ≠ 0)
            have e : xt ((d : ℚ) * ((j : ℚ) * (k : ℚ))) d c' = j • xt (k : ℚ) 1 c' := by
              unfold xt
              rw [nsmul_coe_circ]
              congr 1
              push_cast
              field_simp
            change ‖xt ((d : ℚ) * ((j : ℚ) * (k : ℚ))) d c'‖ < ε
            rw [e]
            calc ‖j • xt (k : ℚ) 1 c'‖ ≤ j * ‖xt (k : ℚ) 1 c'‖ := norm_nsmul_le
              _ ≤ R * ‖xt (k : ℚ) 1 c'‖ := mul_le_mul_of_nonneg_right hjR (norm_nonneg _)
              _ < R * (ε / R) := mul_lt_mul_of_pos_left h1 hRpos
              _ = ε := by field_simp
          exact ⟨key 2 le_rfl hk.1, key 3 (by norm_num) hk.2⟩
        have h1 := hsmall _ hmem
        rw [hc] at h1
        have e : ((c * (((d : ℚ) * ((j : ℚ) * (k : ℚ)) : ℚ) : ℝ) : ℝ) : Circ) =
            j • ((((c * d : ℝ) * (k : ℝ) : ℝ)) : Circ) := by
          rw [nsmul_coe_circ]; congr 1; push_cast; ring
        rw [e] at h1
        exact h1
      have := norm_le_of_multiples ((((c * d : ℝ) * (k : ℝ) : ℝ)) : Circ) R hR1 hall
      exact lt_of_le_of_lt this hRε
    obtain ⟨r, hr⟩ := hH _ hα
    refine ⟨r / d, fun s => ?_⟩
    rw [hc s]
    congr 1
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have : c = (r : ℝ) / d := by
      rw [eq_div_iff hdR]; exact hr
    rw [this]; push_cast; ring

end IntegerPolar

end LeanCheck
