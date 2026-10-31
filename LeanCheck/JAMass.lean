import Mathlib
import LeanCheck.JAWindowQ
import LeanCheck.JARandom
import LeanCheck.JAEnergyLink

/-!
# Per-realization mass bounds (`lem:random-transfer`, the bounds `c_{p,-} ≤ S/Z ≤ c_{p,+}`)

Let `Q = P α`, `f : ZMod P → ℝ` nonnegative, `w_Q` the window of `JAWindowQ`, and for a shift `τ ∈ ZMod P` let
`g_τ(x) = f(x mod P - τ) w_Q(x)` on `ZMod Q` (`x mod P` is `rd x`).  `JARandom.mass_avg` gives the *average* of the total
weight `S(τ) = ∑_x g_τ(x)` over `τ`.  Here we bound `S(τ)` for **every** `τ`:

* `lift_sum`: for each residue `y ∈ ZMod P`, the lift sum `∑_{x : rd x = y} w_Q(x)` is within `2` of `α I_1`,
  `I_1 = 16/(15 D)` (this is the lattice-sum estimate of `JAWindow.lattice_wD` with step `1/α`);
* `mass_bounds`: `(α I_1 - 2) ∑ f ≤ S(τ) ≤ (α I_1 + 2) ∑ f` for every `τ` (`D ≥ 3`);
* `mass_range`: the same for the sum over `range Q` of the `ℕ`-indexed weight `fn g_τ` used by `JAEnergyLink`;
* `mass_ge_half`: if `α I_1 ≥ 4` then `S(τ) ≥ (α I_1 / 2) ∑ f`; `mass_pos`: `S(τ) > 0` once `α I_1 > 2`.

The key point is `wQ_val`: for `v = val x ∈ [0, Q)`, `w_Q(x) = w_D(v/Q) + w_D((v - Q)/Q)` (only one of the two terms is
nonzero because `D ≥ 2`), so the lift sum is the sum of the two lattice sums `p_0 + i/α` and `(h - p_0) + i/α`
(`p_0 = y.val/Q`, `h = P/Q = 1/α`), each over `α` terms.
-/

namespace LeanCheck
namespace JAMass

open Finset JAWindow JAWindowQ JARandom

section

variable {P Q α : ℕ} [NeZero P] [NeZero Q]

lemma wD_half (D : ℝ) (hD : 2 ≤ D) (t : ℝ) (h : 1 / 2 ≤ |t|) : wD D t = 0 := by
  have hD0 : 0 < D := by linarith
  apply wD_zero D hD0
  have : 1 / D ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hD
  linarith

/-- For `v = val x`, `w_Q(x) = w_D(v/Q) + w_D((v-Q)/Q)`. -/
lemma wQ_val (D : ℝ) (hD : 2 ≤ D) (x : ZMod Q) :
    wQ D Q x = wD D ((x.val : ℝ) / Q) + wD D (((x.val : ℝ) - Q) / Q) := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hv : x.val < Q := ZMod.val_lt x
  have hvr : (x.val : ℝ) < Q := by exact_mod_cast hv
  rw [wQ_eq]
  by_cases h : 2 * x.val ≤ Q
  · have hmin : min x.val (Q - x.val) = x.val := Nat.min_eq_left (by omega)
    rw [hmin]
    have hr : 2 * (x.val : ℝ) ≤ Q := by exact_mod_cast h
    have h0 : wD D (((x.val : ℝ) - Q) / Q) = 0 := by
      apply wD_half D hD
      rw [abs_div, abs_of_pos hQ, abs_of_neg (by linarith), le_div_iff₀ hQ]
      linarith
    rw [h0, add_zero]
  · have hmin : min x.val (Q - x.val) = Q - x.val := Nat.min_eq_right (by omega)
    rw [hmin]
    have hr : (Q : ℝ) < 2 * x.val := by exact_mod_cast (not_le.mp h)
    have h0 : wD D ((x.val : ℝ) / Q) = 0 := by
      apply wD_half D hD
      rw [abs_div, abs_of_pos hQ, abs_of_nonneg (Nat.cast_nonneg _), le_div_iff₀ hQ]
      linarith
    rw [h0, zero_add, Nat.cast_sub hv.le, ← wD_even D (((x.val : ℝ) - Q) / Q)]
    congr 1
    ring

lemma val_cast_lt (hQ : Q = P * α) (y : ZMod P) {k : ℕ} (hk : k < α) : y.val + P * k < Q := by
  have hyv := ZMod.val_lt y
  have h2 : P * (k + 1) ≤ P * α := Nat.mul_le_mul_left P hk
  have h3 : P * (k + 1) = P * k + P := by ring
  rw [hQ]
  omega

/-- The fiber over `y ∈ ZMod P` is `{y.val + P k : k < α}`. -/
lemma fiber_sum (hQ : Q = P * α) (hd : P ∣ Q) (y : ZMod P) (u : ZMod Q → ℝ) :
    ∑ x ∈ (univ : Finset (ZMod Q)).filter (fun x => rd hd x = y), u x =
      ∑ k ∈ range α, u ((y.val + P * k : ℕ) : ZMod Q) := by
  classical
  have hP : 0 < P := Nat.pos_of_ne_zero (NeZero.ne P)
  symm
  refine Finset.sum_bij (fun k _ => ((y.val + P * k : ℕ) : ZMod Q)) ?_ ?_ ?_ ?_
  · intro k _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [map_natCast]
    simp
  · intro k₁ hk₁ k₂ hk₂ h
    have hv1 : (((y.val + P * k₁ : ℕ)) : ZMod Q).val = y.val + P * k₁ := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (val_cast_lt hQ y (Finset.mem_range.mp hk₁))]
    have hv2 : (((y.val + P * k₂ : ℕ)) : ZMod Q).val = y.val + P * k₂ := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (val_cast_lt hQ y (Finset.mem_range.mp hk₂))]
    have := congrArg ZMod.val h
    rw [hv1, hv2] at this
    exact Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel this)
  · intro x hx
    have hrd : rd hd x = y := (Finset.mem_filter.mp hx).2
    refine ⟨x.val / P, ?_, ?_⟩
    · rw [Finset.mem_range]
      apply Nat.div_lt_of_lt_mul
      calc x.val < Q := ZMod.val_lt x
        _ = P * α := hQ
    · show ((y.val + P * (x.val / P) : ℕ) : ZMod Q) = x
      have hyv : y.val = x.val % P := by
        rw [← hrd]
        have : rd hd x = ((x.val : ℕ) : ZMod P) := by
          conv_lhs => rw [← ZMod.natCast_zmod_val x]
          exact map_natCast _ _
        rw [this, ZMod.val_natCast]
      rw [hyv, Nat.mod_add_div, ZMod.natCast_zmod_val]
  · intro k _
    rfl

/-- **Lift sums**: for every residue `y`, `|∑_{x : rd x = y} w_Q(x) - α I_1| ≤ 2`. -/
theorem lift_sum (D : ℝ) (hD : 3 ≤ D) (hQ : Q = P * α) (hd : P ∣ Q) (y : ZMod P) :
    |(∑ x ∈ (univ : Finset (ZMod Q)).filter (fun x => rd hd x = y), wQ D Q x) -
        α * (16 / (15 * D))| ≤ 2 := by
  classical
  have hD0 : 0 < D := by linarith
  have hP : (0 : ℝ) < P := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hα0 : 0 < α := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    exact NeZero.ne Q (by simpa using hQ)
  have hαr : (0 : ℝ) < α := by exact_mod_cast hα0
  have hQr : (Q : ℝ) = P * α := by exact_mod_cast hQ
  rw [fiber_sum hQ hd y]
  set y0 : ℝ := (y.val : ℝ) with hy0
  have hy0P : y0 < P := by
    have h : y.val < P := ZMod.val_lt y
    rw [hy0]
    exact_mod_cast h
  have hy0nn : 0 ≤ y0 := Nat.cast_nonneg _
  have hv : ∀ k ∈ range α, (((y.val + P * k : ℕ)) : ZMod Q).val = y.val + P * k := by
    intro k hk
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (val_cast_lt hQ y (Finset.mem_range.mp hk))]
  set G : ℕ → ℝ := fun k => wD D ((((y.val + P * k : ℕ) : ℝ) - Q) / Q) with hG
  have hF : ∀ j ∈ range α, G (α - 1 - j) = wD D (((P : ℝ) / Q - y0 / Q) + j * ((P : ℝ) / Q)) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hc : ((α - 1 - j : ℕ) : ℝ) = α - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      simp
    have hvr : (((y.val + P * (α - 1 - j) : ℕ)) : ℝ) = y0 + P * (α - 1 - j) := by
      rw [Nat.cast_add, Nat.cast_mul, hc]
    simp only [hG]
    rw [hvr]
    have hnum : y0 + P * ((α : ℝ) - 1 - j) - Q = -(((P : ℝ) - y0) + P * j) := by
      rw [hQr]; ring
    rw [hnum, ← wD_even D (((P : ℝ) / Q - y0 / Q) + j * ((P : ℝ) / Q))]
    congr 1
    ring
  have hsplit : ∑ k ∈ range α, wQ D Q ((y.val + P * k : ℕ) : ZMod Q) =
      ∑ k ∈ range α, wD D (y0 / Q + k * ((P : ℝ) / Q)) +
        ∑ k ∈ range α, wD D (((P : ℝ) / Q - y0 / Q) + k * ((P : ℝ) / Q)) := by
    calc ∑ k ∈ range α, wQ D Q ((y.val + P * k : ℕ) : ZMod Q)
        = ∑ k ∈ range α, (wD D (y0 / Q + k * ((P : ℝ) / Q)) + G k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [wQ_val D (by linarith), hv k hk]
          have e : (((y.val + P * k : ℕ)) : ℝ) / Q = y0 / Q + k * ((P : ℝ) / Q) := by
            push_cast; ring
          rw [e]
      _ = ∑ k ∈ range α, wD D (y0 / Q + k * ((P : ℝ) / Q)) + ∑ k ∈ range α, G k :=
          Finset.sum_add_distrib
      _ = _ := by
          rw [← Finset.sum_range_reflect G α]
          congr 1
          exact Finset.sum_congr rfl hF
  rw [hsplit]
  have hh : (0 : ℝ) < (P : ℝ) / Q := by positivity
  have hαh : (α : ℝ) * ((P : ℝ) / Q) = 1 := by
    rw [hQr]; field_simp
  have hph : y0 / Q ≤ (P : ℝ) / Q := div_le_div_of_nonneg_right hy0P.le hQ0.le
  have hD1 : 1 / D ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hD
  have hlat := lattice_wD D hD0 ((P : ℝ) / Q) (y0 / Q) α α hh (by positivity) hph
    (by have : 0 ≤ y0 / Q := by positivity
        linarith)
    (by have : 0 ≤ (P : ℝ) / Q - y0 / Q := by linarith
        linarith)
  set A := ∑ k ∈ range α, wD D (y0 / Q + k * ((P : ℝ) / Q)) with hA
  set B := ∑ k ∈ range α, wD D (((P : ℝ) / Q - y0 / Q) + k * ((P : ℝ) / Q)) with hB
  have key : A + B - α * (16 / (15 * D)) = α * (((P : ℝ) / Q) * (A + B) - 16 / (15 * D)) := by
    rw [mul_sub, ← mul_assoc, hαh, one_mul]
  rw [key, abs_mul, abs_of_pos hαr]
  calc (α : ℝ) * |((P : ℝ) / Q) * (A + B) - 16 / (15 * D)| ≤ α * (2 * ((P : ℝ) / Q)) :=
        mul_le_mul_of_nonneg_left hlat hαr.le
    _ = 2 := by rw [← mul_assoc, mul_comm (α : ℝ) 2, mul_assoc, hαh, mul_one]

end

section mass

variable {P Q α : ℕ} [NeZero P] [NeZero Q]

/-- **Per-realization mass bounds**: for every shift `τ`. -/
theorem mass_bounds (D : ℝ) (hD : 3 ≤ D) (hQ : Q = P * α) (hd : P ∣ Q) (f : ZMod P → ℝ)
    (hf : ∀ y, 0 ≤ f y) (τ : ZMod P) :
    (α * (16 / (15 * D)) - 2) * ∑ y, f y ≤ ∑ x : ZMod Q, f (rd hd x - τ) * wQ D Q x ∧
    ∑ x : ZMod Q, f (rd hd x - τ) * wQ D Q x ≤ (α * (16 / (15 * D)) + 2) * ∑ y, f y := by
  classical
  have hfib : ∑ x : ZMod Q, f (rd hd x - τ) * wQ D Q x = ∑ y : ZMod P, f (y - τ) *
      ∑ x ∈ (univ : Finset (ZMod Q)).filter (fun x => rd hd x = y), wQ D Q x := by
    rw [← Finset.sum_fiberwise (univ : Finset (ZMod Q)) (rd hd)
      (fun x => f (rd hd x - τ) * wQ D Q x)]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  have hshift : ∑ y : ZMod P, f (y - τ) = ∑ y, f y :=
    Fintype.sum_equiv (Equiv.subRight τ) _ _ (fun y => rfl)
  constructor
  · rw [hfib, ← hshift, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    have h1 := (abs_le.mp (lift_sum D hD hQ hd y)).1
    nlinarith [mul_nonneg (hf (y - τ)) (by linarith : 0 ≤ (∑ x ∈ (univ : Finset (ZMod Q)).filter
      (fun x => rd hd x = y), wQ D Q x) - (α * (16 / (15 * D)) - 2))]
  · rw [hfib, ← hshift, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    have h1 := (abs_le.mp (lift_sum D hD hQ hd y)).2
    nlinarith [mul_nonneg (hf (y - τ)) (by linarith : 0 ≤ (α * (16 / (15 * D)) + 2) -
      (∑ x ∈ (univ : Finset (ZMod Q)).filter (fun x => rd hd x = y), wQ D Q x))]

/-- The same bounds for the sum over `range Q` of the `ℕ`-indexed weight used in `JAEnergyLink`. -/
theorem mass_range (D : ℝ) (hD : 3 ≤ D) (hQ : Q = P * α) (hd : P ∣ Q) (f : ZMod P → ℝ)
    (hf : ∀ y, 0 ≤ f y) (τ : ZMod P) :
    (α * (16 / (15 * D)) - 2) * ∑ y, f y ≤
        ∑ x ∈ range Q, JAEnergyLink.fn (fun x : ZMod Q => f (rd hd x - τ) * wQ D Q x) x ∧
    ∑ x ∈ range Q, JAEnergyLink.fn (fun x : ZMod Q => f (rd hd x - τ) * wQ D Q x) x ≤
        (α * (16 / (15 * D)) + 2) * ∑ y, f y := by
  have h := mass_bounds D hD hQ hd f hf τ
  have e : ∑ x ∈ range Q, JAEnergyLink.fn (fun x : ZMod Q => f (rd hd x - τ) * wQ D Q x) x =
      ∑ x : ZMod Q, f (rd hd x - τ) * wQ D Q x :=
    (JAEnergyLink.sum_zmod (fun x : ZMod Q => f (rd hd x - τ) * wQ D Q x)).symm
  rw [e]
  exact h

/-- If `α I_1 ≥ 4` the total weight of every realization is at least half of `α I_1 ∑ f`. -/
theorem mass_ge_half (D : ℝ) (hD : 3 ≤ D) (hQ : Q = P * α) (hd : P ∣ Q) (f : ZMod P → ℝ)
    (hf : ∀ y, 0 ≤ f y) (τ : ZMod P) (hα : 4 ≤ α * (16 / (15 * D))) :
    (α * (16 / (15 * D)) / 2) * ∑ y, f y ≤ ∑ x : ZMod Q, f (rd hd x - τ) * wQ D Q x := by
  have h := (mass_bounds D hD hQ hd f hf τ).1
  have hs : 0 ≤ ∑ y, f y := Finset.sum_nonneg (fun y _ => hf y)
  nlinarith [mul_nonneg hs (by linarith : 0 ≤ α * (16 / (15 * D)) / 2 - 2)]

/-- Positivity of the total weight once `α I_1 > 2` and `∑ f > 0`. -/
theorem mass_pos (D : ℝ) (hD : 3 ≤ D) (hQ : Q = P * α) (hd : P ∣ Q) (f : ZMod P → ℝ)
    (hf : ∀ y, 0 ≤ f y) (τ : ZMod P) (hα : 2 < α * (16 / (15 * D))) (hs : 0 < ∑ y, f y) :
    0 < ∑ x : ZMod Q, f (rd hd x - τ) * wQ D Q x := by
  have h := (mass_bounds D hD hQ hd f hf τ).1
  have : 0 < (α * (16 / (15 * D)) - 2) * ∑ y, f y := mul_pos (by linarith) hs
  linarith

end mass

#print axioms wQ_val
#print axioms fiber_sum
#print axioms lift_sum
#print axioms mass_bounds
#print axioms mass_range
#print axioms mass_ge_half
#print axioms mass_pos

end JAMass
end LeanCheck
