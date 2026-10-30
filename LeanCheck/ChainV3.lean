import LeanCheck.ChainV2

/-!
# An obstruction for every dyadic partition
(TVGQ-v7 Proposition 13.7 `prop:dyadic-v4`; HamelCharactersTVG_v18 Theorem C.1)

For `I ⊆ ℕ₀`, `ξ_I` is the topology `ξ_{{2^n : n ∈ I}}` of the earlier files (`xi (dyad '' I)`).  We prove:

* `dyadic_bounded_gaps` : if `I` has bounded gaps then `ξ_I` is the usual topology of `ℚ`;
* `dyadic_long_blocks`  : if `I` contains consecutive blocks of arbitrarily large length, some irrational
                           `γ` makes `q ↦ p(γ q)` a continuous character of `ξ_I`;
* `dyadic_partition`    : for every partition `ℕ₀ = I ∪ J`, one of `ξ_I`, `ξ_J` has such an irrational character
                           (so it is not compatible with `Γ`).
-/

namespace LeanCheck

open Filter Topology

section Dyadic

/-- The dyadic chain `1, 2, 4, 8, …`. -/
def dyad (n : ℕ) : ℕ := 2 ^ n

lemma dyad_chain : ChainSeq dyad where
  pos n := pow_pos (by norm_num) n
  dvd n := pow_dvd_pow 2 (Nat.le_succ n)
  two n := by
    show 2 * 2 ^ n ≤ 2 ^ (n + 1)
    rw [pow_succ]; omega

/-- Bounded gaps: every interval `[k, k+M]`, `k ≥ N`, meets `I`. -/
def BoundedGaps (I : Set ℕ) : Prop := ∃ M N : ℕ, ∀ k ≥ N, ∃ n ∈ I, k ≤ n ∧ n ≤ k + M

/-- `I` contains consecutive blocks of every length. -/
def LongBlocks (I : Set ℕ) : Prop := ∀ L : ℕ, ∃ a, ∀ n, a ≤ n → n ≤ a + L → n ∈ I

lemma xi_dyad_norm (q : ℚ) (d n : ℕ) (hd : 0 < d) (h : |(q : ℝ)| / (d * 2 ^ n) ≤ 1 / 2) :
    ‖((((q / ((d : ℚ) * ((dyad n : ℕ) : ℚ))) : ℚ) : ℝ) : Circ)‖ = |(q : ℝ)| / (d * 2 ^ n) := by
  have e : (((q / ((d : ℚ) * ((dyad n : ℕ) : ℚ))) : ℚ) : ℝ) = (q : ℝ) / (d * 2 ^ n) := by
    unfold dyad; push_cast; ring
  rw [e, (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by simpa using
    (by rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < d * 2 ^ n)]; exact h : |(q : ℝ) / (d * 2 ^ n)| ≤ 1 / 2))]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < d * 2 ^ n)]

/-- A far-away rational is seen by some dyadic observation. -/
lemma dyad_far (I : Set ℕ) (M N : ℕ) (hI : ∀ k ≥ N, ∃ n ∈ I, k ≤ n ∧ n ≤ k + M) (q : ℚ)
    (hq : (2 : ℝ) ^ (N + 1) ≤ |(q : ℝ)|) :
    ∃ n ∈ I, (1 / 2 : ℝ) ^ (M + 2) ≤ ‖((((q / (((1 : ℕ) : ℚ) * ((dyad n : ℕ) : ℚ))) : ℚ) : ℝ) : Circ)‖ := by
  have hx1 : (1 : ℝ) ≤ |(q : ℝ)| :=
    le_trans (one_le_pow₀ (by norm_num)) hq
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
  have hjN : N < j := by
    have : (2 : ℝ) ^ (N + 1) < 2 ^ (j + 1) := lt_of_le_of_lt hq hj2
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 this
    omega
  obtain ⟨n, hnI, hn1, hn2⟩ := hI (j + 2) (by omega)
  refine ⟨n, hnI, ?_⟩
  have hn2pos : (0 : ℝ) < 2 ^ n := by positivity
  have hup : |(q : ℝ)| / (((1 : ℕ) : ℝ) * 2 ^ n) < 1 / 2 := by
    push_cast
    rw [one_mul, div_lt_iff₀ hn2pos]
    have h1 : (2 : ℝ) ^ (j + 2) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn1
    have h2 : (2 : ℝ) ^ (j + 2) = 4 * 2 ^ j := by ring
    have h3 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
    nlinarith
  rw [xi_dyad_norm q 1 n one_pos hup.le]
  push_cast
  rw [one_mul, le_div_iff₀ hn2pos]
  have h1 : (2 : ℝ) ^ n ≤ 2 ^ (j + 2 + M) := pow_le_pow_right₀ (by norm_num) hn2
  have h2 : (2 : ℝ) ^ (j + 2 + M) = 2 ^ j * 2 ^ (M + 2) := by ring
  have h3 : (1 / 2 : ℝ) ^ (M + 2) * 2 ^ (M + 2) = 1 := by
    rw [← mul_pow]; norm_num
  have hM : (0 : ℝ) < 2 ^ (M + 2) := by positivity
  calc (1 / 2 : ℝ) ^ (M + 2) * 2 ^ n ≤ (1 / 2 : ℝ) ^ (M + 2) * (2 ^ j * 2 ^ (M + 2)) := by
        rw [← h2]; gcongr
    _ = 2 ^ j := by rw [← mul_assoc, mul_comm ((1 / 2 : ℝ) ^ (M + 2)), mul_assoc, h3, mul_one]
    _ ≤ |(q : ℝ)| := hj1

/-- **Bounded gaps give the usual topology** (13.7, first sentence). -/
theorem dyadic_bounded_gaps (I : Set ℕ) (hI : BoundedGaps I) :
    xi (dyad '' I) = (inferInstance : TopologicalSpace ℚ) := by
  obtain ⟨M, N, hMN⟩ := hI
  apply le_antisymm
  · -- `ξ_I` is finer than the usual topology (it has more neighbourhoods)
    obtain ⟨n0, hn0I, -, -⟩ := hMN N le_rfl
    refine le_of_nhds_le_nhds (fun x => ?_)
    rw [Metric.nhds_basis_ball.ge_iff]
    intro ε hε
    set B : ℝ := 2 ^ (N + 1) with hB
    have hBpos : 0 < B := by positivity
    -- the denominator parameter `d`
    set d : ℕ := ⌈2 * B⌉₊ + 1 with hd
    have hdpos : 0 < d := by omega
    have hdR : 2 * B < d := by
      have := Nat.le_ceil (2 * B)
      rw [hd]; push_cast; linarith
    set ε' : ℝ := ε / (d * 2 ^ n0) with hε'
    have hε'pos : 0 < ε' := by positivity
    set δ : ℝ := (1 / 2 : ℝ) ^ (M + 2) with hδ
    have hδpos : 0 < δ := by positivity
    have hsub : xiSet (dyad '' I) 1 δ ∩ xiSet (dyad '' I) d ε' ⊆ {q : ℚ | |(q : ℝ)| < ε} := by
      rintro q ⟨hq1, hq2⟩
      -- first, `|q| < B`
      have hqB : |(q : ℝ)| < B := by
        by_contra hnot
        push_neg at hnot
        obtain ⟨n, hnI, hn⟩ := dyad_far I M N hMN q hnot
        have := hq1 (dyad n) ⟨n, hnI, rfl⟩
        linarith
      have hn0pos : (1 : ℝ) ≤ 2 ^ n0 := one_le_pow₀ (by norm_num)
      have hden : 2 * B < d * 2 ^ n0 := by
        have : (d : ℝ) ≤ d * 2 ^ n0 := le_mul_of_one_le_right (by positivity) hn0pos
        linarith
      have hsm : |(q : ℝ)| / (d * 2 ^ n0) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      have h2 := hq2 (dyad n0) ⟨n0, hn0I, rfl⟩
      rw [xi_dyad_norm q d n0 hdpos hsm, div_lt_iff₀ (by positivity)] at h2
      show |(q : ℝ)| < ε
      have : ε' * (d * 2 ^ n0) = ε := by
        rw [hε']; field_simp
      linarith
    have hW1 := (xiBasis (dyad '' I)).inter_sets (xiSet_mem (dyad '' I) 1 one_pos δ hδpos)
      (xiSet_mem (dyad '' I) d hdpos ε' hε'pos)
    obtain ⟨V, hV, hVsub⟩ := hW1
    have hmem : ((fun y => x + y) '' V) ∈ @nhds ℚ (xi (dyad '' I)) x :=
      ((xiBasis (dyad '' I)).nhds_hasBasis x).mem_of_mem hV
    refine Filter.mem_of_superset hmem ?_
    rintro _ ⟨v, hv, rfl⟩
    have := hsub (hVsub hv)
    show dist ((x + v : ℚ) : ℝ) (x : ℝ) < ε
    rw [Real.dist_eq]
    push_cast
    simpa using this
  · exact usual_le_xi _

/-- A block of `L + 1` consecutive indices in `I` is a chain of length `L` in `I` with ratio `2 < 3`. -/
lemma dyad_chain_of_block (I : Set ℕ) (a L : ℕ) (h : ∀ n, a ≤ n → n ≤ a + L → n ∈ I) :
    IsChain dyad I 3 L (fun i => a + i) := by
  refine ⟨fun j hj => ?_, fun j hj => ⟨?_, ?_⟩⟩
  · exact h (a + j) (by omega) (by omega)
  · show a + j < a + (j + 1)
    omega
  have hp : (0 : ℝ) < dyad (a + j) := by exact_mod_cast dyad_chain.pos _
  have : (dyad (a + (j + 1)) : ℝ) = 2 * dyad (a + j) := by
    unfold dyad; push_cast; ring
  show (dyad (a + (j + 1)) : ℝ) < 3 * dyad (a + j)
  rw [this]; linarith

/-- **Long blocks give an irrational character** (13.7, second sentence). -/
theorem dyadic_long_blocks (I : Set ℕ) (hI : LongBlocks I) :
    ∃ γ : ℝ, Irrational γ ∧ @Continuous ℚ Circ (xi (dyad '' I)) circTop (psiQ γ) := by
  have hinf : I.Infinite := by
    intro hfin
    obtain ⟨a, ha⟩ := hI (hfin.toFinset.sup id + 1)
    have h1 : a + (hfin.toFinset.sup id + 1) ∈ I := ha _ (by omega) le_rfl
    have h2 := Finset.le_sup (f := id) (hfin.mem_toFinset.2 h1)
    simp only [id] at h2
    omega
  have hnot : ¬ HSet dyad I := by
    intro h
    obtain ⟨L, hL⟩ := h 3 (by norm_num)
    obtain ⟨a, ha⟩ := hI (L + 1)
    have := hL (L + 1) _ (dyad_chain_of_block I a (L + 1) ha)
    omega
  have hseq : ¬ HSeq (selSeq dyad I) := fun h => hnot ((HSeq_iff_HSet dyad_chain hinf).1 h)
  obtain ⟨γ, hγ, hc⟩ := xi_neg (selSeq_chain dyad_chain hinf) hseq
  rw [range_selSeq hinf] at hc
  exact ⟨γ, hγ, hc⟩

/-- `q ↦ p(γ q)` is continuous for the usual topology of `ℚ`. -/
lemma psiQ_usual_continuous (γ : ℝ) :
    @Continuous ℚ Circ (inferInstance : TopologicalSpace ℚ) circTop (psiQ γ) := by
  have : Continuous (fun q : ℚ => ((γ * (q : ℝ) : ℝ) : Circ)) :=
    continuous_coe_circ.comp (continuous_const.mul Rat.continuous_coe_real)
  exact this

/-- **Every dyadic partition has a bad side** (13.7, third sentence): if `ℕ₀ = I ∪ J`, then `ξ_I` or `ξ_J` has a
continuous character `q ↦ p(γ q)` with `γ` irrational. -/
theorem dyadic_partition (I J : Set ℕ) (hIJ : I ∪ J = Set.univ) :
    (∃ γ : ℝ, Irrational γ ∧ @Continuous ℚ Circ (xi (dyad '' I)) circTop (psiQ γ)) ∨
    (∃ γ : ℝ, Irrational γ ∧ @Continuous ℚ Circ (xi (dyad '' J)) circTop (psiQ γ)) := by
  by_cases hI : BoundedGaps I
  · left
    refine ⟨Real.sqrt 2, irrational_sqrt_two, ?_⟩
    rw [dyadic_bounded_gaps I hI]
    exact psiQ_usual_continuous _
  · right
    apply dyadic_long_blocks
    unfold BoundedGaps at hI
    push_neg at hI
    intro L
    obtain ⟨k, hk, hkI⟩ := hI L 0
    refine ⟨k, fun n hn1 hn2 => ?_⟩
    have : n ∉ I := fun hnI => by
      have := hkI n hnI hn1
      omega
    have hn : n ∈ I ∪ J := by rw [hIJ]; trivial
    exact hn.resolve_left this

end Dyadic

end LeanCheck
