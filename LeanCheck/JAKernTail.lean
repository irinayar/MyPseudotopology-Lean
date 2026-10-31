import Mathlib
import LeanCheck.JAFar
import LeanCheck.JAWindowTail

/-!
# The central bound, step 4b: from the tails of the kernel measure to the tails of `κ_Q`

The kernel `K = normK N Q (w_Q)` on `ZMod N` has atoms at `a_r = r · (N/Q)` with weight `κ_Q(r) = |Ŵ(r)|^2/(∑ w)^2`.  The far-field
estimate (`JAFar.far_field_ZN`) involves the tail mass `∑_{d : v < cn d} K(d)`.  Here:

* `cn_atom`: `cn(a_r) = ‖r.val / Q‖_{ℝ/ℤ}`; `nrm_val_eq`: this is `|r̃|/Q` for the balanced representative `r̃`;
* `tail_conv`: `∑_{d : v < cn d} K(d) = ∑_{r : v < |r̃|/Q} κ_Q(r)`;
* `kernel_tail_le`: for `D ≥ 3`, `Q ≥ 25 D`, `Q ∣ N`, `v ≥ 0` with `1 ≤ ⌊vQ⌋`:
  `∑_{d : v < cn d} K(d) ≤ 25 D^4 / ⌊vQ⌋^3` (from `JAWindowTail.tail_bound`);
* `kernel_tail_le'`: if `vQ ≥ 2` then the tail is at most `200 D^4/(vQ)^3`.
-/

namespace LeanCheck
namespace JAKernTail

open Finset JATransfer JAMulti JAProduct2 JAFar MixedPrime JAWindowQ JARandom

variable {N : ℕ} [NeZero N]

lemma cn_atom (Q d : ℕ) [NeZero Q] (hd : 0 < d) (hN : N = Q * d) (r : ZMod Q) :
    cn (((r.val * d : ℕ) : ZMod N)) = nrm ((r.val : ℝ) / Q) := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have e : (((r.val * d : ℕ) : ℝ) / N) = (r.val : ℝ) / Q := by
    rw [hN]; push_cast; field_simp
  unfold cn
  rw [ZMod.toAddCircle_natCast, e]
  rfl

lemma nrm_val_eq (Q : ℕ) [NeZero Q] (r : ZMod Q) :
    nrm ((r.val : ℝ) / Q) = |(r.valMinAbs : ℝ)| / Q := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hcong : (Q : ℤ) ∣ (r.val : ℤ) - r.valMinAbs :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub r.valMinAbs (r.val : ℤ) Q).mp
      (by rw [ZMod.coe_valMinAbs, Int.cast_natCast, ZMod.natCast_zmod_val])
  obtain ⟨k, hk⟩ := hcong
  have e : (r.val : ℝ) / Q = (r.valMinAbs : ℝ) / Q + (k : ℝ) := by
    have h1 : (r.val : ℤ) = r.valMinAbs + Q * k := by linarith
    have h2 : (r.val : ℝ) = r.valMinAbs + Q * k := by exact_mod_cast h1
    rw [h2]; field_simp
  rw [e, nrm_add_int ((r.valMinAbs : ℝ) / Q) k]
  have hb := ZMod.valMinAbs_mem_Ioc r
  simp only [Set.mem_Ioc] at hb
  have hbR1 : -(Q : ℝ) < (r.valMinAbs : ℝ) * 2 := by exact_mod_cast hb.1
  have hbR2 : (r.valMinAbs : ℝ) * 2 ≤ Q := by exact_mod_cast hb.2
  have habs : |(r.valMinAbs : ℝ) / Q| ≤ 1 / 2 := by
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hQ]; linarith
    · rw [div_le_iff₀ hQ]; linarith
  rw [nrm_eq_abs habs, abs_div, abs_of_pos hQ]

/-- **Tails of the kernel measure are tails of `κ_Q`.** -/
theorem tail_conv (D : ℝ) (Q : ℕ) [NeZero Q] (hQN : Q ∣ N) (v : ℝ) :
    ∑ x : ZMod N, (if v < cn x then normK N Q (wQ D Q) x else 0) =
      ∑ r : ZMod Q, (if v < |(r.valMinAbs : ℝ)| / Q then
        ‖JARandom.Fq (wQ D Q) r‖ ^ 2 / (∑ x, wQ D Q x) ^ 2 else 0) := by
  classical
  obtain ⟨d, hd⟩ := hQN
  have hQpos : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exfalso; rw [h, mul_zero] at hd; exact NeZero.ne N hd
    · exact h
  have hNd : N / Q = d := by rw [hd]; exact Nat.mul_div_cancel_left d hQpos
  have hnorm : ∀ r : ZMod Q, ∀ x : ZMod N, normK N Q (wQ D Q) x =
      ∑ r : ZMod Q, (1 / (∑ y, wQ D Q y) ^ 2) *
        (if x = ((r.val * d : ℕ) : ZMod N) then ‖JARandom.Fq (wQ D Q) r‖ ^ 2 else 0) := by
    intro _ x
    unfold normK kernq kern
    rw [hNd, Finset.mul_sum]
    rfl
  have step1 : ∀ x : ZMod N, (if v < cn x then normK N Q (wQ D Q) x else 0) =
      ∑ r : ZMod Q, (if v < cn x then (1 / (∑ y, wQ D Q y) ^ 2) *
        (if x = ((r.val * d : ℕ) : ZMod N) then ‖JARandom.Fq (wQ D Q) r‖ ^ 2 else 0) else 0) := by
    intro x
    split_ifs with hx
    · exact hnorm 0 x
    · simp
  simp_rw [step1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single (((r.val * d : ℕ) : ZMod N))]
  · rw [cn_atom (N := N) Q d hdpos hd r, nrm_val_eq]
    simp only [if_true]
    by_cases hv : v < |(r.valMinAbs : ℝ)| / Q
    · simp [hv, div_eq_inv_mul]
    · simp [hv]
  · intro x _ hx
    rw [if_neg hx]
    split_ifs <;> simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Tail of the kernel measure.** -/
theorem kernel_tail_le (D : ℝ) (hD : 3 ≤ D) (Q : ℕ) [NeZero Q] (hQ : 25 * D ≤ Q) (hQN : Q ∣ N) (v : ℝ)
    (hv0 : 0 ≤ v) (hv : 1 ≤ ⌊v * Q⌋₊) :
    ∑ x : ZMod N, (if v < cn x then normK N Q (wQ D Q) x else 0) ≤ 25 * D ^ 4 / (⌊v * Q⌋₊ : ℝ) ^ 3 := by
  classical
  have hQr : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  rw [tail_conv D Q hQN v]
  have hfilter : ∑ r : ZMod Q, (if v < |(r.valMinAbs : ℝ)| / Q then
        ‖JARandom.Fq (wQ D Q) r‖ ^ 2 / (∑ x, wQ D Q x) ^ 2 else 0) =
      ∑ r ∈ (univ : Finset (ZMod Q)).filter (fun r => ((⌊v * Q⌋₊ : ℕ) : ℤ) < |r.valMinAbs|),
        ‖JARandom.Fq (wQ D Q) r‖ ^ 2 / (∑ x, wQ D Q x) ^ 2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    have hiff : v < |(r.valMinAbs : ℝ)| / Q ↔ ((⌊v * Q⌋₊ : ℕ) : ℤ) < |r.valMinAbs| := by
      rw [lt_div_iff₀ hQr]
      constructor
      · intro h
        have h1 : (⌊v * Q⌋₊ : ℝ) ≤ v * Q := Nat.floor_le (by positivity)
        have h2 : ((⌊v * Q⌋₊ : ℕ) : ℝ) < |(r.valMinAbs : ℝ)| := by linarith
        have h3 : (((⌊v * Q⌋₊ : ℕ) : ℤ) : ℝ) < ((|r.valMinAbs| : ℤ) : ℝ) := by
          rw [Int.cast_abs]; push_cast; exact h2
        exact_mod_cast h3
      · intro h
        have h1 : (((⌊v * Q⌋₊ : ℕ) : ℤ) : ℝ) < ((|r.valMinAbs| : ℤ) : ℝ) := by exact_mod_cast h
        rw [Int.cast_abs] at h1
        push_cast at h1
        have h2 : (⌊v * Q⌋₊ : ℝ) + 1 ≤ |(r.valMinAbs : ℝ)| := by
          have : ((⌊v * Q⌋₊ : ℤ) : ℝ) + 1 ≤ |(r.valMinAbs : ℝ)| := by
            have h3 : (⌊v * Q⌋₊ : ℤ) + 1 ≤ |r.valMinAbs| := h
            have h4 : (((⌊v * Q⌋₊ : ℤ) + 1 : ℤ) : ℝ) ≤ ((|r.valMinAbs| : ℤ) : ℝ) := by exact_mod_cast h3
            rw [Int.cast_abs] at h4; push_cast at h4; exact h4
          exact_mod_cast this
        have h5 : v * Q < (⌊v * Q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        linarith
    by_cases h : v < |(r.valMinAbs : ℝ)| / Q
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  rw [hfilter]
  exact JAWindowTail.tail_bound D hD hQ ⌊v * Q⌋₊ hv

/-- A cleaner form: if `v Q ≥ 2` the tail is at most `200 D^4 / (v Q)^3`. -/
theorem kernel_tail_le' (D : ℝ) (hD : 3 ≤ D) (Q : ℕ) [NeZero Q] (hQ : 25 * D ≤ Q) (hQN : Q ∣ N) (v : ℝ)
    (hv : 2 ≤ v * Q) :
    ∑ x : ZMod N, (if v < cn x then normK N Q (wQ D Q) x else 0) ≤ 200 * D ^ 4 / (v * Q) ^ 3 := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hv0 : 0 ≤ v := by
    by_contra h; push Not at h; nlinarith
  have hfl : (v * Q) / 2 ≤ (⌊v * Q⌋₊ : ℝ) := by
    have h1 : v * Q - 1 < (⌊v * Q⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (v * Q); linarith
    linarith
  have hfl1 : 1 ≤ ⌊v * Q⌋₊ := by
    have : (1 : ℝ) ≤ (⌊v * Q⌋₊ : ℝ) := by linarith
    exact_mod_cast this
  refine (kernel_tail_le D hD Q hQ hQN v hv0 hfl1).trans ?_
  have hpos : 0 < (v * Q) / 2 := by linarith
  have h3 : ((v * Q) / 2) ^ 3 ≤ (⌊v * Q⌋₊ : ℝ) ^ 3 := pow_le_pow_left₀ hpos.le hfl 3
  have hD4 : 0 ≤ 25 * D ^ 4 := by positivity
  calc 25 * D ^ 4 / (⌊v * Q⌋₊ : ℝ) ^ 3 ≤ 25 * D ^ 4 / ((v * Q) / 2) ^ 3 :=
        div_le_div_of_nonneg_left hD4 (by positivity) h3
    _ = 200 * D ^ 4 / (v * Q) ^ 3 := by field_simp; ring

#print axioms cn_atom
#print axioms nrm_val_eq
#print axioms tail_conv
#print axioms kernel_tail_le
#print axioms kernel_tail_le'

end JAKernTail
end LeanCheck
