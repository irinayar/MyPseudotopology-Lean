import LeanCheck.ChainY3

/-!
# Theorem F, compatible direction: the key proposition
(TVGQ-v7 Theorem 17.3 `chains:F`; HamelCharactersTVG_v18 Theorem D.3)

**Key proposition.**  Let `M` be a chain satisfying `H(M)`, `0 < ε < 1/8`, and `c' ∈ ℝ` such that for every integer
`n` with `‖p(n / M_i)‖ < ε` for all `i`, one has `‖p(c' n)‖ < 1/4`.  Then `c' M_i ∈ ℤ` for some `i` (so `c'` is
rational).

Constants: `B = 64/ε`, `Big i :⇔ B M_i ≤ M_{i+1}`, `r_i` = centered representative of `p(c' M_i)`.
-/

namespace LeanCheck

open Filter Topology

section KeyF

variable {M : ℕ → ℕ} (hM : ChainSeq M)

/-- `Big B i`: the step `i` has ratio at least `B`. -/
def Big (M : ℕ → ℕ) (B : ℝ) (i : ℕ) : Prop := B * M i ≤ M (i + 1)

include hM in
/-- Under `H(M)` there is a uniform `L` such that every window of length `L+1` contains a big step. -/
lemma exists_big_in_window (hH : HSeq M) {B : ℝ} (hB : 2 < B) :
    ∃ L : ℕ, ∀ i, ∃ k, i ≤ k ∧ k ≤ i + L ∧ Big M B k := by
  obtain ⟨L, hL⟩ := hH B hB
  refine ⟨L, fun i => ?_⟩
  by_contra hno
  push_neg at hno
  have hrun : IsRun M B i (i + (L + 1)) := by
    intro j hj hjb
    have := hno j hj (by omega)
    unfold Big at this
    exact not_le.1 this
  have := hL i (i + (L + 1)) hrun
  omega

include hM in
lemma big_infinite_succ (hH : HSeq M) {B : ℝ} (hB : 2 < B) (i : ℕ) : ∃ k, i < k ∧ Big M B k := by
  obtain ⟨L, hL⟩ := exists_big_in_window hM hH hB
  obtain ⟨k, hk1, -, hk3⟩ := hL (i + 1)
  exact ⟨k, by omega, hk3⟩

end KeyF

section KeyF2

variable {M : ℕ → ℕ} (hM : ChainSeq M) {ε : ℝ} {c' : ℝ}
include hM

/-- **Claim A.**  For a big step `i`, `‖p(c' M_i)‖ ≤ 1/(ε α_i)`. -/
lemma r_bound (hε : 0 < ε)
    (hstar : ∀ n : ℤ, (∀ i, ‖(((n : ℝ) / (M i : ℝ) : ℝ) : Circ)‖ < ε) → ‖((c' * n : ℝ) : Circ)‖ < 1 / 4)
    {i : ℕ} (hbig : Big M (64 / ε) i) :
    ‖((c' * M i : ℝ) : Circ)‖ ≤ 1 / (ε * ((M (i + 1) : ℝ) / M i)) := by
  have hMi : (0 : ℝ) < M i := by exact_mod_cast hM.pos i
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
  have hmult : ∀ j : ℕ, j ≤ S → ‖j • (((c' * M i : ℝ)) : Circ)‖ < 1 / 4 := by
    intro j hj
    have hj' : (j : ℝ) ≤ S := by exact_mod_cast hj
    have h1 := hstar ((j : ℤ) * (M i : ℤ)) (fun l => by
      by_cases hl : l ≤ i
      · obtain ⟨c, hc⟩ := hM.dvd_of_le hl
        have hMl : (0 : ℝ) < M l := by exact_mod_cast hM.pos l
        have : (((j : ℤ) * (M i : ℤ) : ℤ) : ℝ) / (M l : ℝ) = (((j * c : ℕ) : ℤ) : ℝ) := by
          rw [hc]; push_cast; field_simp
        have h0 : ((((j * c : ℕ) : ℤ) : ℝ) : Circ) = 0 := by
          rw [AddCircle.coe_eq_zero_iff]; exact ⟨(j * c : ℕ), by simp⟩
        rw [this, h0, norm_zero]; exact hε
      · push_neg at hl
        have hle : M (i + 1) ≤ M l := hM.mono hl
        have hMl : (0 : ℝ) < M l := by exact_mod_cast hM.pos l
        have hnn : 0 ≤ (((j : ℤ) * (M i : ℤ) : ℤ) : ℝ) / (M l : ℝ) := by positivity
        have hup : (((j : ℤ) * (M i : ℤ) : ℤ) : ℝ) / (M l : ℝ) ≤ ε / 2 := by
          push_cast
          rw [div_le_iff₀ hMl]
          have h1 : (M (i + 1) : ℝ) ≤ M l := by exact_mod_cast hle
          have h2 : (M (i + 1) : ℝ) = a * M i := by rw [ha]; field_simp
          have h3 : (j : ℝ) ≤ ε / 2 * a := hj'.trans hSle
          nlinarith [mul_le_mul_of_nonneg_right h3 hMi.le]
        refine lt_of_le_of_lt (norm_coe_le _ 0) ?_
        rw [Int.cast_zero, sub_zero, abs_of_nonneg hnn]
        linarith)
    have e : ((c' * (((j : ℤ) * (M i : ℤ) : ℤ) : ℝ) : ℝ) : Circ) = j • (((c' * M i : ℝ)) : Circ) := by
      rw [nsmul_coe_circ]; push_cast; ring_nf
    rw [← e]; exact h1
  have hb := norm_le_of_multiples ((c' * M i : ℝ) : Circ) S hS1 hmult
  refine hb.trans ?_
  have : ε * a ≤ 4 * S := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Tail bound.**  A signed combination of distinct big terms `s_j M_{e_j}` with `s_j M_{e_j} ≤ η M_{e_j+1}`
is within `2η` of an integer after division by any `M_l`. -/
lemma tail_bound (η : ℝ) (hη : 0 ≤ η) (J : Finset ℕ) (e : ℕ → ℕ) (he : Function.Injective e)
    (σ : ℕ → ℤ) (hσ : ∀ j, |σ j| ≤ 1) (s : ℕ → ℕ)
    (hs : ∀ j, (s j : ℝ) * M (e j) ≤ η * M (e j + 1)) (l : ℕ) :
    ‖((((∑ j ∈ J, σ j * s j * M (e j) : ℤ) : ℝ) / (M l : ℝ) : ℝ) : Circ)‖ ≤ 2 * η := by
  classical
  have hMl : (0 : ℝ) < M l := by exact_mod_cast hM.pos l
  set A : Finset ℕ := J.filter (fun j => e j < l) with hA
  set Bs : Finset ℕ := J.filter (fun j => ¬ e j < l) with hBs
  have hsplit : (∑ j ∈ J, σ j * s j * M (e j) : ℤ) =
      ∑ j ∈ A, σ j * s j * M (e j) + ∑ j ∈ Bs, σ j * s j * M (e j) :=
    (Finset.sum_filter_add_sum_filter_not J (fun j => e j < l) _).symm
  -- the contribution of `Bs` is an integer multiple of `M_l`
  have hBdvd : ((M l : ℕ) : ℤ) ∣ ∑ j ∈ Bs, σ j * s j * M (e j) := by
    refine Finset.dvd_sum (fun j hj => ?_)
    have hj' : ¬ e j < l := (Finset.mem_filter.1 hj).2
    have : M l ∣ M (e j) := hM.dvd_of_le (by omega)
    have h2 : ((M l : ℕ) : ℤ) ∣ ((M (e j) : ℕ) : ℤ) := by exact_mod_cast this
    exact Dvd.dvd.mul_left h2 _
  obtain ⟨w, hw⟩ := hBdvd
  -- the real value of the `A`-part
  set R : ℝ := ((∑ j ∈ A, σ j * s j * M (e j) : ℤ) : ℝ) / M l with hR
  have hcirc : ((((∑ j ∈ J, σ j * s j * M (e j) : ℤ) : ℝ) / (M l : ℝ) : ℝ) : Circ) = (R : Circ) := by
    have : (((∑ j ∈ J, σ j * s j * M (e j) : ℤ) : ℝ) / (M l : ℝ)) = R + (w : ℝ) := by
      rw [hsplit, hw]; push_cast
      rw [hR]; push_cast; field_simp
    rw [this, AddCircle.coe_add]
    have : ((w : ℝ) : Circ) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]; exact ⟨w, by simp⟩
    rw [this, add_zero]
  rw [hcirc]
  refine (norm_coe_le R 0).trans ?_
  rw [Int.cast_zero, sub_zero]
  -- |R| ≤ 2 η
  have hterm : ∀ j ∈ A, |((σ j * s j * M (e j) : ℤ) : ℝ)| / M l ≤ η * (1 / 2) ^ (l - 1 - e j) := by
    intro j hj
    have hjl : e j < l := (Finset.mem_filter.1 hj).2
    have hp : 2 ^ (l - (e j + 1)) * M (e j + 1) ≤ M l := hM.pow_mul_le (by omega)
    have hp' : (2 : ℝ) ^ (l - (e j + 1)) * M (e j + 1) ≤ M l := by exact_mod_cast hp
    have h1 : |((σ j * s j * M (e j) : ℤ) : ℝ)| ≤ s j * M (e j) := by
      push_cast
      rw [abs_mul, abs_mul]
      have : |(σ j : ℝ)| ≤ 1 := by exact_mod_cast hσ j
      rw [Nat.abs_cast, Nat.abs_cast]
      nlinarith [Nat.cast_nonneg (α := ℝ) (s j), Nat.cast_nonneg (α := ℝ) (M (e j)), mul_nonneg (Nat.cast_nonneg (α := ℝ) (s j)) (Nat.cast_nonneg (α := ℝ) (M (e j)))]
    rw [div_le_iff₀ hMl]
    calc |((σ j * s j * M (e j) : ℤ) : ℝ)| ≤ s j * M (e j) := h1
      _ ≤ η * M (e j + 1) := hs j
      _ ≤ η * ((1 / 2) ^ (l - 1 - e j) * M l) := by
          gcongr
          have hpow : (l - 1 - e j) = l - (e j + 1) := by omega
          rw [hpow]
          have h2 : (0 : ℝ) < 2 ^ (l - (e j + 1)) := by positivity
          rw [one_div_pow, div_mul_eq_mul_div, le_div_iff₀ h2]
          linarith
      _ = η * (1 / 2) ^ (l - 1 - e j) * M l := by ring
  have hRabs : |R| ≤ ∑ j ∈ A, |((σ j * s j * M (e j) : ℤ) : ℝ)| / M l := by
    rw [hR, abs_div, abs_of_pos hMl, ← Finset.sum_div, Int.cast_sum]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hMl.le
  have hgeom : ∑ x ∈ Finset.range l, (1 / 2 : ℝ) ^ (l - 1 - x) ≤ 2 := by
    rw [Finset.sum_range_reflect (fun u => (1 / 2 : ℝ) ^ u) l]
    exact sum_geometric_two_le l
  have himg : ∑ j ∈ A, (1 / 2 : ℝ) ^ (l - 1 - e j) ≤ ∑ x ∈ Finset.range l, (1 / 2 : ℝ) ^ (l - 1 - x) := by
    have hinj : Set.InjOn e (A : Set ℕ) := fun x _ y _ h => he h
    rw [← Finset.sum_image (f := fun x => (1 / 2 : ℝ) ^ (l - 1 - x)) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => by positivity)
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (Finset.mem_filter.1 hj).2
  calc |R| ≤ ∑ j ∈ A, |((σ j * s j * M (e j) : ℤ) : ℝ)| / M l := hRabs
    _ ≤ ∑ j ∈ A, η * (1 / 2) ^ (l - 1 - e j) := Finset.sum_le_sum hterm
    _ = η * ∑ j ∈ A, (1 / 2 : ℝ) ^ (l - 1 - e j) := by rw [Finset.mul_sum]
    _ ≤ η * 2 := mul_le_mul_of_nonneg_left (himg.trans hgeom) hη
    _ = 2 * η := by ring

end KeyF2

end LeanCheck
