import LeanCheck.ChainT5

/-!
# Rational observation topologies `ξ_C` and characters of `ℚ`
(TVGQ-v7 §17 / HamelCharactersTVG_v18 Appendix D: preliminaries for Theorem F)

* `char_Q_real` : a character `ψ : ℚ →+ Circ` that is `< 1/4` on `(-ε, ε) ∩ ℚ` has the form `q ↦ p(c q)`, `c ∈ ℝ`
  (extend `ψ` to `ℝ` using divisibility of the circle, then linearize on the dense subgroup `ℚ`);
* `xiBasis C` : the additive group topology on `ℚ` with zero-neighbourhood base
  `V(d, ε) = { q | ∀ c ∈ C, ‖p(q/(d c))‖ < ε }` (`d ≥ 1`, `ε > 0`);
* it is a Hausdorff group topology coarser than the usual one, in which every character `q ↦ p(r q)`, `r ∈ ℚ`, is
  continuous.
-/

namespace LeanCheck

open Filter Topology

/-! ### Characters of `ℚ` that are small near zero -/

/-- The rational numbers as an additive subgroup of `ℝ`. -/
noncomputable def QinR : AddSubgroup ℝ := (Rat.castHom ℝ).toAddMonoidHom.range

lemma mem_QinR (x : ℝ) : x ∈ QinR ↔ ∃ q : ℚ, (q : ℝ) = x := by
  unfold QinR
  simp [AddMonoidHom.mem_range]

theorem char_Q_real (ψ : ℚ →+ Circ) (ε : ℝ) (hε : 0 < ε) (hsm : ∀ q : ℚ, |(q : ℝ)| < ε → ‖ψ q‖ < 1 / 4) :
    ∃ c : ℝ, ∀ q : ℚ, ψ q = ((c * (q : ℝ) : ℝ) : Circ) := by
  obtain ⟨χ, hχ⟩ := Module.Baer.extension_property_addMonoidHom (Module.Baer.of_divisible Circ)
    (Rat.castHom ℝ).toAddMonoidHom (Rat.cast_injective (α := ℝ)) ψ
  have hχq : ∀ q : ℚ, χ (q : ℝ) = ψ q := fun q => by
    have := congrArg (fun m : ℚ →+ Circ => m q) hχ
    simpa using this
  have hN : ∀ x ∈ QinR, ∀ q : ℚ, (q : ℝ) * x ∈ QinR := by
    intro x hx q
    obtain ⟨r, rfl⟩ := (mem_QinR x).1 hx
    exact (mem_QinR _).2 ⟨q * r, by push_cast; ring⟩
  have hsm' : ∀ x ∈ QinR, |x| < ε → ‖χ x‖ < 1 / 4 := by
    intro x hx hxε
    obtain ⟨q, rfl⟩ := (mem_QinR x).1 hx
    rw [hχq]
    exact hsm q hxε
  have hdense : Dense (QinR : Set ℝ) := by
    have : (QinR : Set ℝ) = Set.range ((↑) : ℚ → ℝ) := by
      ext x; simp [mem_QinR]
    rw [this]; exact Rat.denseRange_cast
  obtain ⟨c, hc⟩ := linearize χ QinR ε hε hN hsm' hdense
  refine ⟨c, fun q => ?_⟩
  rw [← hχq]
  exact hc (q : ℝ) ((mem_QinR _).2 ⟨q, rfl⟩)

/-! ### The topology `ξ_C` -/

/-- The basic set `V(d, ε) = { q | ∀ c ∈ C, ‖p(q/(d c))‖ < ε }`. -/
def xiSet (C : Set ℕ) (d : ℕ) (ε : ℝ) : Set ℚ :=
  {q | ∀ c ∈ C, ‖((((q / ((d : ℚ) * c)) : ℚ) : ℝ) : Circ)‖ < ε}

lemma norm_circ_add_le (x y : ℝ) : ‖((x + y : ℝ) : Circ)‖ ≤ ‖(x : Circ)‖ + ‖(y : Circ)‖ := by
  rw [AddCircle.coe_add]; exact norm_add_le _ _

lemma norm_circ_nsmul_le (n : ℕ) (x : ℝ) : ‖((n * x : ℝ) : Circ)‖ ≤ n * ‖(x : Circ)‖ := by
  have : ((n * x : ℝ) : Circ) = n • (x : Circ) := (nsmul_coe_circ n x).symm
  rw [this]; exact norm_nsmul_le

/-- Scaling: `V(d d', ε/d') ⊆ V(d, ε)`. -/
lemma xiSet_mono (C : Set ℕ) (d d' : ℕ) (hd' : 0 < d') (ε : ℝ) :
    xiSet C (d * d') (ε / d') ⊆ xiSet C d ε := by
  intro q hq c hc
  have h1 := hq c hc
  have hd'r : (0 : ℝ) < d' := by exact_mod_cast hd'
  have e : (((q / ((d : ℚ) * c)) : ℚ) : ℝ) = (d' : ℝ) * (((q / (((d * d' : ℕ) : ℚ) * c)) : ℚ) : ℝ) := by
    have hq1 : q / ((d : ℚ) * c) = (d' : ℚ) * (q / (((d * d' : ℕ) : ℚ) * c)) := by
      have h2 : ((d * d' : ℕ) : ℚ) * c = (d' : ℚ) * ((d : ℚ) * c) := by push_cast; ring
      rw [h2]
      by_cases hX : ((d : ℚ) * c) = 0
      · simp [hX]
      · have hd'0 : (d' : ℚ) ≠ 0 := by exact_mod_cast hd'.ne'
        field_simp
    rw [hq1]; push_cast; ring
  rw [e]
  calc ‖(((d' : ℝ) * (((q / (((d * d' : ℕ) : ℚ) * c)) : ℚ) : ℝ) : ℝ) : Circ)‖
      ≤ d' * ‖((((q / (((d * d' : ℕ) : ℚ) * c)) : ℚ) : ℝ) : Circ)‖ := norm_circ_nsmul_le d' _
    _ < d' * (ε / d') := by gcongr
    _ = ε := by field_simp

/-- The group filter basis of `ξ_C`. -/
noncomputable def xiBasis (C : Set ℕ) : AddGroupFilterBasis ℚ where
  sets := {s | ∃ d : ℕ, 0 < d ∧ ∃ ε : ℝ, 0 < ε ∧ s = xiSet C d ε}
  nonempty := ⟨xiSet C 1 1, 1, one_pos, 1, one_pos, rfl⟩
  inter_sets := by
    rintro _ _ ⟨d₁, hd₁, ε₁, hε₁, rfl⟩ ⟨d₂, hd₂, ε₂, hε₂, rfl⟩
    refine ⟨xiSet C (d₁ * d₂) (min (ε₁ / d₂) (ε₂ / d₁)), ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, _,
      lt_min (by positivity) (by positivity), rfl⟩, ?_⟩
    intro q hq
    constructor
    · have h1 : xiSet C (d₁ * d₂) (ε₁ / d₂) ⊆ xiSet C d₁ ε₁ := xiSet_mono C d₁ d₂ hd₂ ε₁
      exact h1 (fun c hc => lt_of_lt_of_le (hq c hc) (min_le_left _ _))
    · have h2 : xiSet C (d₂ * d₁) (ε₂ / d₁) ⊆ xiSet C d₂ ε₂ := xiSet_mono C d₂ d₁ hd₁ ε₂
      have hq' : q ∈ xiSet C (d₂ * d₁) (ε₂ / d₁) := by
        intro c hc
        have := hq c hc
        rw [mul_comm d₁ d₂] at this
        exact lt_of_lt_of_le this (min_le_right _ _)
      exact h2 hq'
  zero' := by
    rintro _ ⟨d, hd, ε, hε, rfl⟩ c _
    simpa using hε
  add' := by
    rintro _ ⟨d, hd, ε, hε, rfl⟩
    refine ⟨xiSet C d (ε / 2), ⟨d, hd, ε / 2, by positivity, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩ c hc
    have h1 := hx c hc
    have h2 := hy c hc
    have : ((((x + y) / ((d : ℚ) * c) : ℚ) : ℝ) : Circ) =
        ((((x / ((d : ℚ) * c)) : ℚ) : ℝ) : Circ) + ((((y / ((d : ℚ) * c)) : ℚ) : ℝ) : Circ) := by
      rw [add_div]; push_cast; rw [AddCircle.coe_add]
    rw [this]
    calc _ ≤ _ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := by ring
  neg' := by
    rintro _ ⟨d, hd, ε, hε, rfl⟩
    refine ⟨xiSet C d ε, ⟨d, hd, ε, hε, rfl⟩, ?_⟩
    intro x hx c hc
    have : ((((-x) / ((d : ℚ) * c) : ℚ) : ℝ) : Circ) = -((((x / ((d : ℚ) * c)) : ℚ) : ℝ) : Circ) := by
      rw [neg_div]; push_cast; rw [AddCircle.coe_neg]
    rw [this, norm_neg]
    exact hx c hc
  conj' := by
    intro x₀ U hU
    refine ⟨U, hU, ?_⟩
    intro x hx
    simpa using hx

/-- The topology `ξ_C` on `ℚ`. -/
noncomputable def xi (C : Set ℕ) : TopologicalSpace ℚ := (xiBasis C).topology

lemma xi_group (C : Set ℕ) : @IsTopologicalAddGroup ℚ (xi C) _ := (xiBasis C).isTopologicalAddGroup

lemma xiSet_mem (C : Set ℕ) (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    xiSet C d ε ∈ xiBasis C := ⟨d, hd, ε, hε, rfl⟩

lemma xi_nhds_hasBasis (C : Set ℕ) :
    (@nhds ℚ (xi C) 0).HasBasis (fun s : Set ℚ => s ∈ xiBasis C) id :=
  (xiBasis C).nhds_zero_hasBasis

/-- `ξ_C` is coarser than the usual topology of `ℚ`: `V(d, ε)` contains the usual ball of radius `ε`. -/
lemma xiSet_ball (C : Set ℕ) (d : ℕ) (hd : 0 < d) (ε : ℝ) (q : ℚ) (hq : |(q : ℝ)| < ε) :
    q ∈ xiSet C d ε := by
  intro c hc
  have hε : 0 < ε := lt_of_le_of_lt (abs_nonneg _) hq
  by_cases hX : ((d : ℚ) * c) = 0
  · rw [hX, div_zero]; simpa using hε
  · refine lt_of_le_of_lt (norm_coe_le _ 0) ?_
    rw [Int.cast_zero, sub_zero]
    have hX1 : (1 : ℝ) ≤ |((d : ℝ) * c)| := by
      have hnat : 0 < d * c := Nat.pos_of_ne_zero (fun h => hX (by exact_mod_cast h))
      have : (1 : ℝ) ≤ ((d * c : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [abs_of_nonneg (by positivity)]
      push_cast at this
      exact this
    push_cast
    rw [abs_div]
    have hXr : (0 : ℝ) < |((d : ℝ) * c)| := lt_of_lt_of_le one_pos hX1
    calc |(q : ℝ)| / |((d : ℝ) * c)| ≤ |(q : ℝ)| / 1 := by gcongr
      _ < ε := by simpa using hq

end LeanCheck
