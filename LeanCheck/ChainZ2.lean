import LeanCheck.ChainZ1
import LeanCheck.ChainY6

/-!
# Theorem G, compatible direction: the pieces
(TVGQ-v7 Theorem 17.6 `chains:G`, second half; HamelCharactersTVG_v18 Theorem D.6)

Let `M` be a chain with `H(M)` and `ζ` a `λ_{range M}`-continuous character of `ℚ/ℤ`.  Put `e_i = 1/M_i + ℤ`.
Then `ζ(e_i)` has centered representative `r_i`, and `ζ(e_{i+1})` is bounded by `1/(ε α_i)` at every big step.
-/

namespace LeanCheck

open Filter Topology

section ZetaPos

variable {M : ℕ → ℕ}

/-- The element `1/M_i + ℤ` of `ℚ/ℤ`. -/
noncomputable def eT (M : ℕ → ℕ) (i : ℕ) : TorsA := piHom (1 / (M i : ℚ))

lemma eT_coe (i : ℕ) : ((eT M i : TorsA) : Circ) = ((1 / (M i : ℝ) : ℝ) : Circ) := by
  rw [eT, piHom_coe]; push_cast; rfl

lemma eT_rel (hM : ChainSeq M) {i k : ℕ} (h : i ≤ k) :
    ∃ c : ℕ, M k = c * M i ∧ eT M i = c • eT M k := by
  obtain ⟨c, hc⟩ := hM.dvd_of_le h
  refine ⟨c, by rw [hc]; ring, ?_⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    exact (hM.pos k).ne' hc
  rw [eT, eT, ← map_nsmul, nsmul_eq_mul]
  congr 1
  have h1 : (M i : ℚ) ≠ 0 := by exact_mod_cast (hM.pos i).ne'
  have h2 : (M k : ℚ) = M i * c := by exact_mod_cast hc
  have h3 : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
  rw [h2]
  field_simp

/-- **Claim A for `ℚ/ℤ`.**  At a big step `i`, `‖ζ(e_{i+1})‖ ≤ 1/(ε α_i)`. -/
lemma r_bound_G (hM : ChainSeq M) {ε : ℝ} (hε : 0 < ε) (ζ : TorsA →+ Circ)
    (hsmall : ∀ x : TorsA, (∀ l, ‖M l • (x : Circ)‖ < ε) → ‖ζ x‖ < 1 / 4)
    {i : ℕ} (hbig : Big M (64 / ε) i) :
    ‖ζ (eT M (i + 1))‖ ≤ 1 / (ε * ((M (i + 1) : ℝ) / M i)) := by
  have hMi : (0 : ℝ) < M i := by exact_mod_cast hM.pos i
  have hMi1 : (0 : ℝ) < M (i + 1) := by exact_mod_cast hM.pos (i + 1)
  set a : ℝ := (M (i + 1) : ℝ) / M i with ha
  have ha64 : 64 / ε ≤ a := by
    rw [ha, le_div_iff₀ hMi]; exact hbig
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha64
  have hx : 32 ≤ ε / 2 * a := by
    have : 64 ≤ ε * a := by
      have := mul_le_mul_of_nonneg_left ha64 hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    linarith
  set S : ℕ := ⌊ε / 2 * a⌋₊ with hS
  have hS1 : 1 ≤ S := Nat.le_floor (by linarith)
  have hSle : (S : ℝ) ≤ ε / 2 * a := Nat.floor_le (by positivity)
  have hSlt : ε / 2 * a < S + 1 := Nat.lt_floor_add_one _
  have hS1' : (1 : ℝ) ≤ S := by exact_mod_cast hS1
  have hmult : ∀ j : ℕ, j ≤ S → ‖j • ζ (eT M (i + 1))‖ < 1 / 4 := by
    intro j hj
    have hj' : (j : ℝ) ≤ S := by exact_mod_cast hj
    rw [← map_nsmul]
    refine hsmall _ (fun l => ?_)
    have hcoe : (((j • eT M (i + 1) : TorsA)) : Circ) = ((j * (1 / (M (i + 1) : ℝ)) : ℝ) : Circ) := by
      rw [AddSubgroup.coe_nsmul, eT_coe, nsmul_coe_circ]
    rw [hcoe, nsmul_coe_circ]
    by_cases hl : l ≤ i
    · have hMl : (M l : ℝ) ≤ M i := by exact_mod_cast hM.mono hl
      have h2 : (M (i + 1) : ℝ) = a * M i := by rw [ha]; field_simp
      have h3 : (j : ℝ) ≤ ε / 2 * a := hj'.trans hSle
      have hnn : 0 ≤ (M l : ℝ) * ((j : ℝ) * (1 / (M (i + 1) : ℝ))) := by positivity
      have hval : (M l : ℝ) * ((j : ℝ) * (1 / (M (i + 1) : ℝ))) ≤ ε / 2 := by
        have e1 : (M l : ℝ) * ((j : ℝ) * (1 / (M (i + 1) : ℝ))) = ((M l : ℝ) / M i) * ((j : ℝ) / a) := by
          rw [h2]; field_simp
        rw [e1]
        have f1 : (M l : ℝ) / M i ≤ 1 := (div_le_one hMi).2 hMl
        have f2 : (j : ℝ) / a ≤ ε / 2 := by rw [div_le_iff₀ hapos]; exact h3
        calc ((M l : ℝ) / M i) * ((j : ℝ) / a) ≤ 1 * (ε / 2) :=
              mul_le_mul f1 f2 (by positivity) (by norm_num)
          _ = ε / 2 := one_mul _
      refine lt_of_le_of_lt ((norm_coe_le _ 0).trans ?_) (show ε / 2 < ε by linarith)
      rw [Int.cast_zero, sub_zero, abs_of_nonneg hnn]
      exact hval
    · push_neg at hl
      obtain ⟨c, hc, -⟩ := eT_rel hM (show i + 1 ≤ l by omega)
      have hz : ((M l : ℝ) * ((j : ℝ) * (1 / (M (i + 1) : ℝ)))) = ((c * j : ℕ) : ℤ) := by
        rw [hc]; push_cast; field_simp
      have h0 : (((M l : ℝ) * ((j : ℝ) * (1 / (M (i + 1) : ℝ))) : ℝ) : Circ) = 0 := by
        rw [circ_zero_iff]; exact ⟨(c * j : ℕ), hz⟩
      rw [h0, norm_zero]; exact hε
  have hb := norm_le_of_multiples (ζ (eT M (i + 1))) S hS1 hmult
  refine hb.trans ?_
  have : ε * a ≤ 4 * S := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Tail bound for `ℚ/ℤ`.**  A signed combination of the elements `s_j / M_{e_j+1}` with
`s_j M_{e_j} ≤ η M_{e_j+1}` is within `2η` of an integer after multiplication by any `M_l`. -/
lemma tail_bound_G (hM : ChainSeq M) (η : ℝ) (hη : 0 ≤ η) (J : Finset ℕ) (e : ℕ → ℕ)
    (he : Function.Injective e) (σ : ℕ → ℤ) (hσ : ∀ j, |σ j| ≤ 1) (s : ℕ → ℕ)
    (hs : ∀ j, (s j : ℝ) * M (e j) ≤ η * M (e j + 1)) (l : ℕ) :
    ‖(((M l : ℝ) * ∑ j ∈ J, ((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)) : ℝ) : Circ)‖ ≤ 2 * η := by
  classical
  have hMl : (0 : ℝ) < M l := by exact_mod_cast hM.pos l
  set A : Finset ℕ := J.filter (fun j => e j + 1 ≤ l) with hA
  set Bs : Finset ℕ := J.filter (fun j => ¬ e j + 1 ≤ l) with hBs
  have hsplit : ∑ j ∈ J, ((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)) =
      ∑ j ∈ A, ((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)) +
        ∑ j ∈ Bs, ((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not J (fun j => e j + 1 ≤ l) _).symm
  set W : ℤ := ∑ j ∈ A, σ j * s j * ((M l / M (e j + 1) : ℕ) : ℤ) with hW
  have hWeq : (M l : ℝ) * ∑ j ∈ A, ((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)) = (W : ℝ) := by
    rw [hW, Finset.mul_sum]
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjl : e j + 1 ≤ l := (Finset.mem_filter.1 hj).2
    have hd : M (e j + 1) ∣ M l := hM.dvd_of_le hjl
    have hpos : (M (e j + 1) : ℝ) ≠ 0 := by exact_mod_cast (hM.pos _).ne'
    rw [Nat.cast_div hd hpos]
    field_simp
  set R : ℝ := (M l : ℝ) * ∑ j ∈ Bs, ((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)) with hR
  have hcirc : (((M l : ℝ) * ∑ j ∈ J, ((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)) : ℝ) : Circ)
      = (R : Circ) := by
    have : (M l : ℝ) * ∑ j ∈ J, ((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)) = (W : ℝ) + R := by
      rw [hsplit, mul_add, hWeq]
    rw [this, AddCircle.coe_add]
    have h0 : ((W : ℝ) : Circ) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]; exact ⟨W, by simp⟩
    rw [h0, zero_add]
  rw [hcirc]
  refine (norm_coe_le R 0).trans ?_
  rw [Int.cast_zero, sub_zero]
  have hterm : ∀ j ∈ Bs, |(M l : ℝ) * (((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)))|
      ≤ η * (1 / 2) ^ (e j - l) := by
    intro j hj
    have hjl : l ≤ e j := by have := (Finset.mem_filter.1 hj).2; omega
    have hp : 2 ^ (e j - l) * M l ≤ M (e j) := hM.pow_mul_le hjl
    have hp' : (2 : ℝ) ^ (e j - l) * M l ≤ M (e j) := by exact_mod_cast hp
    have hMe : (0 : ℝ) < M (e j + 1) := by exact_mod_cast hM.pos _
    have h2 : (0 : ℝ) < 2 ^ (e j - l) := by positivity
    have hσ' : |(σ j : ℝ)| ≤ 1 := by exact_mod_cast hσ j
    have hsn : (0 : ℝ) ≤ s j := Nat.cast_nonneg _
    have hMln : (0 : ℝ) ≤ M l := hMl.le
    have habs : |(M l : ℝ) * (((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)))|
        ≤ (M l : ℝ) * s j * (1 / (M (e j + 1) : ℝ)) := by
      push_cast
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hMln, Nat.abs_cast,
        abs_of_pos (one_div_pos.2 hMe)]
      have : (M l : ℝ) * (|(σ j : ℝ)| * s j) * (1 / (M (e j + 1) : ℝ)) ≤
          (M l : ℝ) * (1 * s j) * (1 / (M (e j + 1) : ℝ)) := by
        gcongr
      nlinarith [this]
    refine habs.trans ?_
    have key : (2 : ℝ) ^ (e j - l) * ((M l : ℝ) * s j) ≤ η * M (e j + 1) := by
      calc (2 : ℝ) ^ (e j - l) * ((M l : ℝ) * s j) = (2 ^ (e j - l) * M l) * s j := by ring
        _ ≤ M (e j) * s j := by gcongr
        _ ≤ η * M (e j + 1) := by linarith [hs j]
    rw [one_div_pow, mul_one_div, mul_one_div, div_le_div_iff₀ hMe h2]
    linarith [key]
  have hRabs : |R| ≤ ∑ j ∈ Bs, |(M l : ℝ) * (((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)))| := by
    rw [hR, Finset.mul_sum]
    exact Finset.abs_sum_le_sum_abs _ _
  have hgeom : ∑ j ∈ Bs, (1 / 2 : ℝ) ^ (e j - l) ≤ 2 := by
    have hinj : Set.InjOn (fun j => e j - l) (Bs : Set ℕ) := by
      intro x hx y hy hxy
      have hx' : l ≤ e x := by have := (Finset.mem_filter.1 hx).2; omega
      have hy' : l ≤ e y := by have := (Finset.mem_filter.1 hy).2; omega
      exact he (by simp only at hxy; omega)
    obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range (Bs.image (fun j => e j - l))
    calc ∑ j ∈ Bs, (1 / 2 : ℝ) ^ (e j - l)
        = ∑ d ∈ Bs.image (fun j => e j - l), (1 / 2 : ℝ) ^ d := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ d ∈ Finset.range N, (1 / 2 : ℝ) ^ d :=
          Finset.sum_le_sum_of_subset_of_nonneg hN (fun x _ _ => by positivity)
      _ ≤ 2 := sum_geometric_two_le N
  calc |R| ≤ ∑ j ∈ Bs, |(M l : ℝ) * (((σ j * s j : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)))| := hRabs
    _ ≤ ∑ j ∈ Bs, η * (1 / 2) ^ (e j - l) := Finset.sum_le_sum hterm
    _ = η * ∑ j ∈ Bs, (1 / 2 : ℝ) ^ (e j - l) := by rw [Finset.mul_sum]
    _ ≤ η * 2 := mul_le_mul_of_nonneg_left hgeom hη
    _ = 2 * η := by ring

end ZetaPos

end LeanCheck
