import LeanCheck.ChainCapstone
import LeanCheck.AppendixB

/-!
# The dictionary: group topologies `λ_C` on `ℚ/ℤ` and the quarter-arc criterion

`A = TorsA` is the torsion subgroup of the circle `AddCircle 1`, i.e. `ℚ/ℤ`.  For a set `C` of positive integers
(the observations `x ↦ c·x`), `λ_C` is the group topology on `A` with zero-neighbourhood base
`obs C δ = {x | ∀ c ∈ C, ‖c • x‖ < δ}`, `δ > 0` (an `AddGroupFilterBasis`, so a genuine topological group).

* `quarter_of_continuous` : a continuous character is below `1/4` on some ball `obs C δ`;
* `continuous_of_quarter` : conversely (via `near_of_all_multiples`: `‖j•t‖ < 1/4` for `j ≤ R` forces `‖t‖ ≤ 1/(4R)`);
* the same for the join `λ_{C₁} ⊓ λ_{C₂}` (Mathlib's `⊓` is the finer topology, the join in the paper's sense),
  whose zero neighbourhoods are `obs C₁ δ ∩ obs C₂ δ'`.
-/

namespace LeanCheck

open Filter Topology

/-- `ℚ/ℤ` as the torsion subgroup of the circle. -/
abbrev TorsA : Type := AddCommGroup.torsion Circ

/-- The ball `{x | ∀ c ∈ C, ‖c • x‖ < δ}`. -/
def obs (C : Set ℕ) (δ : ℝ) : Set TorsA := {x | ∀ c ∈ C, ‖c • (x : Circ)‖ < δ}

lemma norm_coe_circ (x : ℝ) : ‖(x : Circ)‖ = |x - round x| := UnitAddCircle.norm_eq

lemma exists_int_of_norm_lt {x ε : ℝ} (h : ‖(x : Circ)‖ < ε) : ∃ n : ℤ, |x - n| < ε :=
  ⟨round x, by rwa [norm_coe_circ] at h⟩

lemma norm_coe_le (x : ℝ) (n : ℤ) : ‖(x : Circ)‖ ≤ |x - n| := by
  rw [norm_coe_circ]; exact round_le x n

lemma nsmul_coe_circ (c : ℕ) (x : ℝ) : c • (x : Circ) = ((c * x : ℝ) : Circ) := by
  have : ((c * x : ℝ) : Circ) = ((c • x : ℝ) : Circ) := by rw [nsmul_eq_mul]
  rw [this, AddCircle.coe_nsmul]

/-- The group filter basis of `λ_C`. -/
def basisOf (C : Set ℕ) : AddGroupFilterBasis TorsA where
  sets := {s | ∃ δ : ℝ, 0 < δ ∧ s = obs C δ}
  nonempty := ⟨obs C 1, 1, one_pos, rfl⟩
  inter_sets := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨obs C (min a b), ⟨min a b, lt_min ha hb, rfl⟩, ?_⟩
    intro x hx
    exact ⟨fun c hc => lt_of_lt_of_le (hx c hc) (min_le_left _ _),
      fun c hc => lt_of_lt_of_le (hx c hc) (min_le_right _ _)⟩
  zero' := by
    rintro _ ⟨δ, hδ, rfl⟩ c _
    simpa using hδ
  add' := by
    rintro _ ⟨δ, hδ, rfl⟩
    refine ⟨obs C (δ / 2), ⟨δ / 2, by positivity, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩ c hc
    have h1 := hx c hc
    have h2 := hy c hc
    have : ‖c • ((x + y : TorsA) : Circ)‖ ≤ ‖c • (x : Circ)‖ + ‖c • (y : Circ)‖ := by
      rw [AddSubgroup.coe_add, nsmul_add]; exact norm_add_le _ _
    linarith
  neg' := by
    rintro _ ⟨δ, hδ, rfl⟩
    refine ⟨obs C δ, ⟨δ, hδ, rfl⟩, ?_⟩
    intro x hx c hc
    have : ‖c • ((-x : TorsA) : Circ)‖ = ‖c • (x : Circ)‖ := by
      rw [AddSubgroup.coe_neg, smul_neg, norm_neg]
    show ‖c • ((-x : TorsA) : Circ)‖ < δ
    rw [this]; exact hx c hc
  conj' := by
    intro x₀ U hU
    refine ⟨U, hU, ?_⟩
    intro x hx
    simpa using hx

lemma mem_basisOf {C : Set ℕ} {δ : ℝ} (hδ : 0 < δ) : obs C δ ∈ basisOf C := ⟨δ, hδ, rfl⟩

lemma obs_mono {C : Set ℕ} {δ δ' : ℝ} (h : δ ≤ δ') : obs C δ ⊆ obs C δ' :=
  fun _ hx c hc => lt_of_lt_of_le (hx c hc) h

/-- `‖t‖ ≤ 1/(4R)` when `‖j • t‖ < 1/4` for `j ≤ R`. -/
lemma norm_le_of_multiples (t : Circ) (R : ℕ) (hR : 1 ≤ R) (h : ∀ j : ℕ, j ≤ R → ‖j • t‖ < 1 / 4) :
    ‖t‖ ≤ 1 / (4 * R) := by
  obtain ⟨θ, rfl, hθ, hn⟩ := exists_centered t
  have key : ∀ ρ : ℕ, ρ ≤ R → ∃ n : ℤ, |(ρ : ℝ) * θ - n| < 1 / 4 := by
    intro ρ hρ
    have := h ρ hρ
    rw [nsmul_coe_circ] at this
    exact exists_int_of_norm_lt this
  obtain ⟨m, hm⟩ := near_of_all_multiples hR key
  calc ‖(θ : Circ)‖ ≤ |θ - m| := norm_coe_le θ m
    _ ≤ 1 / (4 * R) := hm

/-- A continuous character is below `1/4` on a ball. -/
lemma quarter_of_continuous (C : Set ℕ) (χ : TorsA →+ Circ)
    (h : @Continuous TorsA Circ ((basisOf C).topology) _ χ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ obs C δ, ‖χ x‖ < 1 / 4 := by
  have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (χ 0) := by
    rw [map_zero]
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  have hpre : χ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} ∈ @nhds TorsA ((basisOf C).topology) 0 :=
    (@Continuous.continuousAt TorsA Circ ((basisOf C).topology) _ χ 0 h) hS
  obtain ⟨V, ⟨δ, hδ, rfl⟩, hV⟩ := ((basisOf C).nhds_zero_hasBasis).mem_iff.mp hpre
  exact ⟨δ, hδ, fun x hx => hV hx⟩

lemma smul_mem_obs {C : Set ℕ} {δ : ℝ} (hδ : 0 < δ) (R : ℕ) (hR : 1 ≤ R) {x : TorsA}
    (hx : x ∈ obs C (δ / R)) (j : ℕ) (hj : j ≤ R) : j • x ∈ obs C δ := by
  intro c hc
  have e : c • ((j • x : TorsA) : Circ) = j • (c • (x : Circ)) := by
    rw [AddSubgroup.coe_nsmul, smul_comm]
  rw [e]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simpa using hδ
  · have h1 := hx c hc
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
    have hjR : (j : ℝ) ≤ R := by exact_mod_cast hj
    have hjp : (0 : ℝ) < j := by exact_mod_cast hjpos
    have hd : 0 ≤ δ / R := by positivity
    calc ‖j • (c • (x : Circ))‖ ≤ j * ‖c • (x : Circ)‖ := norm_nsmul_le
      _ < j * (δ / R) := by gcongr
      _ ≤ R * (δ / R) := by gcongr
      _ = δ := by field_simp

lemma exists_R (ε : ℝ) (hε : 0 < ε) : ∃ R : ℕ, 1 ≤ R ∧ 1 / (4 * (R : ℝ)) < ε := by
  refine ⟨⌈1 / (4 * ε)⌉₊ + 1, by omega, ?_⟩
  have h1 : 1 / (4 * ε) < (⌈1 / (4 * ε)⌉₊ + 1 : ℕ) := by
    have := Nat.le_ceil (1 / (4 * ε))
    push_cast; linarith
  have hRpos : (0 : ℝ) < ((⌈1 / (4 * ε)⌉₊ + 1 : ℕ) : ℝ) := by positivity
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ (by positivity)] at h1
  nlinarith

/-- Quarter-arc criterion for a single topology `λ_C`. -/
lemma continuous_of_quarter (C : Set ℕ) (χ : TorsA →+ Circ)
    (h : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ obs C δ, ‖χ x‖ < 1 / 4) :
    @Continuous TorsA Circ ((basisOf C).topology) _ χ := by
  letI : TopologicalSpace TorsA := (basisOf C).topology
  haveI : IsTopologicalAddGroup TorsA := (basisOf C).isTopologicalAddGroup
  obtain ⟨δ, hδ, hq⟩ := h
  apply continuous_of_continuousAt_zero χ
  have hbasis := (basisOf C).nhds_zero_hasBasis
  have : Tendsto χ (𝓝 0) (𝓝 0) := by
    rw [hbasis.tendsto_iff NormedAddGroup.nhds_zero_basis_norm_lt]
    intro ε hε
    obtain ⟨R, hR1, hRε⟩ := exists_R ε hε
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
    refine ⟨obs C (δ / R), mem_basisOf (by positivity), fun x hx => ?_⟩
    have hj : ∀ j : ℕ, j ≤ R → ‖j • χ x‖ < 1 / 4 := by
      intro j hj
      rw [← map_nsmul]
      exact hq _ (smul_mem_obs hδ R hR1 hx j hj)
    exact lt_of_le_of_lt (norm_le_of_multiples (χ x) R hR1 hj) hRε
  rw [ContinuousAt, map_zero]
  exact this

/-- Quarter-arc criterion for the join `λ_{C₁} ∨ λ_{C₂}` (Mathlib's `⊓`). -/
lemma continuous_of_quarter_join (C₁ C₂ : Set ℕ) (χ : TorsA →+ Circ)
    (h : ∃ δ : ℝ, 0 < δ ∧ ∀ x, x ∈ obs C₁ δ → x ∈ obs C₂ δ → ‖χ x‖ < 1 / 4) :
    @Continuous TorsA Circ ((basisOf C₁).topology ⊓ (basisOf C₂).topology) _ χ := by
  haveI h1 : @IsTopologicalAddGroup TorsA ((basisOf C₁).topology) _ := (basisOf C₁).isTopologicalAddGroup
  haveI h2 : @IsTopologicalAddGroup TorsA ((basisOf C₂).topology) _ := (basisOf C₂).isTopologicalAddGroup
  letI : TopologicalSpace TorsA := (basisOf C₁).topology ⊓ (basisOf C₂).topology
  haveI : IsTopologicalAddGroup TorsA := isTopologicalAddGroup_inf h1 h2
  obtain ⟨δ, hδ, hq⟩ := h
  apply continuous_of_continuousAt_zero χ
  have hb1 := (basisOf C₁).nhds_zero_hasBasis
  have hb2 := (basisOf C₂).nhds_zero_hasBasis
  have hbasis := hb1.inf hb2
  have : Tendsto χ (𝓝 0) (𝓝 0) := by
    have hn : (𝓝 (0 : TorsA)) = @nhds TorsA ((basisOf C₁).topology) 0 ⊓ @nhds TorsA ((basisOf C₂).topology) 0 :=
      @nhds_inf TorsA ((basisOf C₁).topology) ((basisOf C₂).topology) 0
    rw [hn, hbasis.tendsto_iff NormedAddGroup.nhds_zero_basis_norm_lt]
    intro ε hε
    obtain ⟨R, hR1, hRε⟩ := exists_R ε hε
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
    refine ⟨(obs C₁ (δ / R), obs C₂ (δ / R)), ⟨mem_basisOf (by positivity),
      mem_basisOf (by positivity)⟩, fun x hx => ?_⟩
    have hj : ∀ j : ℕ, j ≤ R → ‖j • χ x‖ < 1 / 4 := by
      intro j hj
      rw [← map_nsmul]
      exact hq _ (smul_mem_obs hδ R hR1 hx.1 j hj) (smul_mem_obs hδ R hR1 hx.2 j hj)
    exact lt_of_le_of_lt (norm_le_of_multiples (χ x) R hR1 hj) hRε
  rw [ContinuousAt, map_zero]
  exact this

end LeanCheck
