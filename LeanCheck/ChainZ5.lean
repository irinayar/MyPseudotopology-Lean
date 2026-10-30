import LeanCheck.ChainZ4

/-!
# Theorem G: the criterion
(TVGQ-v7 Theorem 17.6 `chains:G`; HamelCharactersTVG_v18 Theorem D.6)

For a profinitely null chain `M` with `M 0 = 1`: `λ_{range M}` is compatible (its continuous characters are exactly
`x ↦ u • x`) if and only if `H(M)`.  For a finite set `C ∋ 1`, `λ_C` is always compatible.
-/

namespace LeanCheck

open Filter Topology

section ZetaFinal

variable {M : ℕ → ℕ}

/-- **Theorem G for chain sequences.** -/
theorem chains_G_seq (hM : ChainSeq M) (hnull : ∀ N, 0 < N → ∃ n0, ∀ n ≥ n0, N ∣ M n) (h0 : M 0 = 1) :
    (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (Set.range M)).topology _ χ ↔
      ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) ↔ HSeq M := by
  constructor
  · intro hdual
    by_contra hnot
    obtain ⟨ζ, hcont, hne⟩ := tors_neg hM hnull hnot
    obtain ⟨u, hu⟩ := (hdual ζ).1 hcont
    obtain ⟨x, hx⟩ := hne u
    exact hx (hu x)
  · intro hH χ
    refine ⟨fun h => tors_pos hM hnull hH χ h, ?_⟩
    rintro ⟨u, hu⟩
    exact intHom_continuous ⟨0, h0⟩ u χ hu

/-- Integer multiples are `λ_C`-continuous when `1 ∈ C`. -/
lemma intHom_continuous_C {C : Set ℕ} (h1 : 1 ∈ C) (u : ℤ) (χ : TorsA →+ Circ)
    (hχ : ∀ x : TorsA, χ x = u • (x : Circ)) :
    @Continuous TorsA Circ (basisOf C).topology _ χ := by
  refine continuous_of_quarter _ χ ⟨1 / (4 * ((|u| : ℝ) + 1)), by positivity, fun x hx => ?_⟩
  have hx1 := hx 1 h1
  rw [hχ, one_nsmul] at *
  have hnorm : ‖u • (x : Circ)‖ ≤ |(u : ℝ)| * ‖(x : Circ)‖ := by
    have := norm_zsmul_le u (x : Circ)
    simpa [Int.norm_eq_abs] using this
  have hpos : (0 : ℝ) < 4 * ((|u| : ℝ) + 1) := by positivity
  calc ‖u • (x : Circ)‖ ≤ |(u : ℝ)| * ‖(x : Circ)‖ := hnorm
    _ ≤ |(u : ℝ)| * (1 / (4 * ((|u| : ℝ) + 1))) := by
        gcongr
    _ < 1 / 4 := by
        rw [mul_one_div, div_lt_div_iff₀ hpos (by norm_num)]
        nlinarith [abs_nonneg (u : ℝ)]

/-- **Theorem G, finite case.**  For a finite set `C ∋ 1`, `λ_C` is compatible. -/
theorem tors_dual_finite (C : Set ℕ) (hfin : C.Finite) (h1 : 1 ∈ C) (χ : TorsA →+ Circ) :
    @Continuous TorsA Circ (basisOf C).topology _ χ ↔ ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ) := by
  refine ⟨fun h => ?_, fun ⟨u, hu⟩ => intHom_continuous_C h1 u χ hu⟩
  obtain ⟨δ, hδ, hq⟩ := quarter_of_continuous C χ h
  set K : ℕ := ∑ c ∈ hfin.toFinset, c + 1 with hK
  have hKpos : (0 : ℝ) < K := by positivity
  have hcK : ∀ c ∈ C, (c : ℝ) ≤ K := fun c hc => by
    have : c ≤ ∑ c ∈ hfin.toFinset, c :=
      Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.2 hc)
    exact_mod_cast (by omega : c ≤ K)
  set ψ : ℚ →+ Circ := χ.comp piHom with hψ
  have hsm : ∀ q : ℚ, |(q : ℝ)| < δ / K → ‖ψ q‖ < 1 / 4 := by
    intro q hqK
    apply hq
    intro c hc
    rw [piHom_coe, nsmul_coe_circ]
    have hb : |(c : ℝ) * (q : ℝ)| < δ := by
      rw [abs_mul, Nat.abs_cast]
      calc (c : ℝ) * |(q : ℝ)| ≤ K * |(q : ℝ)| :=
          mul_le_mul_of_nonneg_right (hcK c hc) (abs_nonneg _)
        _ < K * (δ / K) := by gcongr
        _ = δ := by field_simp
    refine lt_of_le_of_lt ((norm_coe_le _ 0).trans ?_) hb
    rw [Int.cast_zero, sub_zero]
  obtain ⟨c, hc⟩ := char_Q_real ψ (δ / K) (by positivity) hsm
  have hpi1 : piHom 1 = 0 := by
    apply Subtype.ext
    rw [piHom_coe]
    show _ = (0 : Circ)
    rw [circ_zero_iff]
    exact ⟨1, by simp⟩
  have h1c : ((c * ((1 : ℚ) : ℝ) : ℝ) : Circ) = 0 := by
    rw [← hc, hψ]
    simp [hpi1]
  obtain ⟨u, hu⟩ := (circ_zero_iff _).1 h1c
  refine ⟨u, fun x => ?_⟩
  obtain ⟨q, rfl⟩ := piHom_surjective x
  have := hc q
  rw [hψ] at this
  simp only [AddMonoidHom.comp_apply] at this
  rw [this, piHom_coe, zsmul_coe_circ]
  congr 1
  simp at hu
  rw [hu]

end ZetaFinal

end LeanCheck
