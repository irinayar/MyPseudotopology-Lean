import Mathlib
import LeanCheck.JATransfer

/-!
# Random-translation averaging (component 15, `lem:random-transfer`)

Let `f : ZMod P → ℝ` be a weight of period `P`, `w : ZMod Q → ℝ` a window of period `Q = P α`, and for `τ ∈ ZMod P`
put `g_τ(x) = f(x - τ) w(x)` on `ZMod Q` (`x - τ` means `x mod P - τ`).  Write `f̂(l) = ∑_z f(z) e_P(l z)` and
`Ŵ(r) = ∑_x w(x) e_Q(r x)`.

Checked here (no axiom, no `sorry`):

* `amp_avg`: the exact averaged transfer
  `P · ∑_{τ ∈ ZMod P} |ĝ_τ(j)|^2 = ∑_{l ∈ ZMod P} |f̂(l)|^2 |Ŵ(j + α l)|^2`
  for every frequency `j ∈ ZMod Q`, i.e. `E_τ |ĝ_τ(j)|^2 = P^{-2} ∑_l |f̂(l)|^2 |Ŵ(j + α l)|^2`.  The proof uses
  the autocorrelation identity: summing over `τ` turns the product `ĝ_τ conj ĝ_τ` into the autocorrelation of `f`
  at `x - z`, which `autocorr` expands in the characters of `ZMod P`; the two characters are compared through
  `e_P(l · (x mod P)) = e_Q(α l · x)`.
* `mass_avg`: the exact average of the total weight, `∑_τ ∑_x g_τ(x) = (∑_y f(y)) (∑_x w(x))`.

Not checked here: the sign/reflection conventions needed to read `j + α l` as the convolution of the spectral measures
(`l ↦ -l`, using `|f̂(-l)| = |f̂(l)|`), and the mass bounds `c_{p,-} ≤ S/Z ≤ c_{p,+}` (these need the window sums).
-/

namespace LeanCheck
namespace JARandom

open Finset JALocalize MixedPrimeProduct

section generic

variable {Q : ℕ} [NeZero Q]

/-- `∑_x w(x) e(r x)`. -/
noncomputable def Fq (w : ZMod Q → ℝ) (r : ZMod Q) : ℂ := ∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)

/-- `∑_z w(z) e(-r z)` (the conjugate of `Fq`). -/
noncomputable def Gq (w : ZMod Q → ℝ) (r : ZMod Q) : ℂ := ∑ z, (w z : ℂ) * ZMod.stdAddChar (-(r * z))

lemma FG_normsq (w : ZMod Q → ℝ) (r : ZMod Q) : Fq w r * Gq w r = ((‖Fq w r‖ ^ 2 : ℝ) : ℂ) :=
  coef_mul_conj w r

lemma FG_expand (w : ZMod Q → ℝ) (r : ZMod Q) :
    Fq w r * Gq w r = ∑ x, ∑ z, ((w x : ℂ) * (w z : ℂ)) * ZMod.stdAddChar (r * (x - z)) := by
  unfold Fq Gq
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  have : (ZMod.stdAddChar (r * (x - z)) : ℂ) =
      ZMod.stdAddChar (r * x) * ZMod.stdAddChar (-(r * z)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [this]
  ring

lemma acorr_eq' (w : ZMod Q → ℝ) (t : ZMod Q) :
    (Q : ℂ) * (acorr w t : ℂ) = ∑ r, (Fq w r * Gq w r) * ZMod.stdAddChar (r * t) :=
  acorr_eq w t

end generic

section transfer

variable {P Q α : ℕ} [NeZero P] [NeZero Q]

/-- Reduction `ZMod Q → ZMod P`. -/
noncomputable def rd (hd : P ∣ Q) : ZMod Q →+* ZMod P := ZMod.castHom hd (ZMod P)

/-- The embedding `l ↦ α l` of frequencies `ZMod P → ZMod Q`. -/
noncomputable def iota' (Q α : ℕ) {P : ℕ} [NeZero P] (l : ZMod P) : ZMod Q := ((l.val * α : ℕ) : ZMod Q)

lemma e_compat_nat (hQ : Q = P * α) (m n : ℕ) :
    ZMod.stdAddChar (((m : ℕ) : ZMod P) * ((n : ℕ) : ZMod P)) =
      ZMod.stdAddChar ((((m * α : ℕ)) : ZMod Q) * ((n : ℕ) : ZMod Q)) := by
  have hP : (P : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne P
  have hα : (α : ℝ) ≠ 0 := by
    have : α ≠ 0 := by
      rintro rfl
      simp at hQ
      exact NeZero.ne Q hQ
    exact_mod_cast this
  have e1 : ((m : ZMod P) * (n : ZMod P)) = (((m * n : ℕ) : ℤ) : ZMod P) := by simp
  have e2 : (((m * α : ℕ) : ZMod Q) * (n : ZMod Q)) = (((m * α * n : ℕ) : ℤ) : ZMod Q) := by simp
  rw [e1, e2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  have hQ' : (Q : ℂ) = (P : ℂ) * (α : ℂ) := by exact_mod_cast hQ
  rw [hQ']
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  push_cast
  field_simp

lemma e_compat (hQ : Q = P * α) (hd : P ∣ Q) (l : ZMod P) (x : ZMod Q) :
    ZMod.stdAddChar (l * rd hd x) = ZMod.stdAddChar (iota' Q α l * x) := by
  have key := e_compat_nat hQ l.val x.val
  have hx : rd hd x = ((x.val : ℕ) : ZMod P) := by
    unfold rd
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [map_natCast]
  rw [hx]
  have hl : ((l.val : ℕ) : ZMod P) = l := ZMod.natCast_zmod_val l
  have hx' : ((x.val : ℕ) : ZMod Q) = x := ZMod.natCast_zmod_val x
  rw [hl] at key
  rw [hx'] at key
  exact key

lemma tau_acorr (f : ZMod P → ℝ) (a b : ZMod P) :
    ∑ τ : ZMod P, f (a - τ) * f (b - τ) = acorr f (a - b) := by
  unfold acorr
  rw [← Equiv.sum_comp (Equiv.subLeft b)]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Equiv.subLeft_apply]
  have h1 : a - (b - u) = u + (a - b) := by ring
  have h2 : b - (b - u) = u := by ring
  rw [h1, h2]
  ring

/-- **Exact averaged transfer.** -/
theorem amp_avg (hQ : Q = P * α) (f : ZMod P → ℝ) (w : ZMod Q → ℝ) (j : ZMod Q) :
    (P : ℝ) * ∑ τ : ZMod P,
        ‖Fq (fun x => f (rd (Dvd.intro α hQ.symm) x - τ) * w x) j‖ ^ 2 =
      ∑ l : ZMod P, ‖Fq f l‖ ^ 2 * ‖Fq w (j + iota' Q α l)‖ ^ 2 := by
  have hd : P ∣ Q := Dvd.intro α hQ.symm
  apply Complex.ofReal_injective
  push_cast
  -- left side
  have hL : ∀ τ : ZMod P, (((‖Fq (fun x => f (rd hd x - τ) * w x) j‖ ^ 2 : ℝ)) : ℂ) =
      ∑ x, ∑ z, ((w x : ℂ) * (w z : ℂ)) * ((f (rd hd x - τ) * f (rd hd z - τ) : ℝ) : ℂ) *
        ZMod.stdAddChar (j * (x - z)) := by
    intro τ
    rw [← FG_normsq, FG_expand]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro z _
    push_cast
    ring
  have hL2 : ∑ τ : ZMod P, (((‖Fq (fun x => f (rd hd x - τ) * w x) j‖ ^ 2 : ℝ)) : ℂ) =
      ∑ x, ∑ z, ((w x : ℂ) * (w z : ℂ)) * (acorr f (rd hd x - rd hd z) : ℂ) *
        ZMod.stdAddChar (j * (x - z)) := by
    simp_rw [hL]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have := tau_acorr f (rd hd x) (rd hd z)
    have h2 : ∑ τ : ZMod P, (((f (rd hd x - τ) * f (rd hd z - τ) : ℝ)) : ℂ) = (acorr f (rd hd x - rd hd z) : ℂ) := by
      rw [← this]; push_cast; rfl
    rw [h2]
  have hmain : (P : ℂ) * ∑ τ : ZMod P, (((‖Fq (fun x => f (rd hd x - τ) * w x) j‖ ^ 2 : ℝ)) : ℂ) =
      ∑ l : ZMod P, ((‖Fq f l‖ ^ 2 : ℝ) : ℂ) * ((‖Fq w (j + iota' Q α l)‖ ^ 2 : ℝ) : ℂ) := by
    have hxz : ∀ x z : ZMod Q, (P : ℂ) * (((w x : ℂ) * (w z : ℂ)) * (acorr f (rd hd x - rd hd z) : ℂ) *
        ZMod.stdAddChar (j * (x - z))) =
        ∑ l : ZMod P, (Fq f l * Gq f l) * (((w x : ℂ) * (w z : ℂ)) *
          ZMod.stdAddChar ((j + iota' Q α l) * (x - z))) := by
      intro x z
      have h1 := acorr_eq' f (rd hd x - rd hd z)
      calc (P : ℂ) * (((w x : ℂ) * (w z : ℂ)) * (acorr f (rd hd x - rd hd z) : ℂ) *
            ZMod.stdAddChar (j * (x - z)))
          = ((w x : ℂ) * (w z : ℂ)) * ((P : ℂ) * (acorr f (rd hd x - rd hd z) : ℂ)) *
            ZMod.stdAddChar (j * (x - z)) := by ring
        _ = ((w x : ℂ) * (w z : ℂ)) * (∑ l, (Fq f l * Gq f l) *
            ZMod.stdAddChar (l * (rd hd x - rd hd z))) * ZMod.stdAddChar (j * (x - z)) := by
          rw [h1]
        _ = _ := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l _
          have e1 : (ZMod.stdAddChar (l * (rd hd x - rd hd z)) : ℂ) =
              ZMod.stdAddChar (iota' Q α l * (x - z)) := by
            rw [← map_sub (rd hd)]
            exact e_compat hQ hd l (x - z)
          have e2 : (ZMod.stdAddChar ((j + iota' Q α l) * (x - z)) : ℂ) =
              ZMod.stdAddChar (j * (x - z)) * ZMod.stdAddChar (iota' Q α l * (x - z)) := by
            rw [← AddChar.map_add_eq_mul]
            congr 1
            ring
          rw [e1, e2]
          ring
    calc (P : ℂ) * ∑ τ : ZMod P, (((‖Fq (fun x => f (rd hd x - τ) * w x) j‖ ^ 2 : ℝ)) : ℂ)
        = (P : ℂ) * ∑ x, ∑ z, ((w x : ℂ) * (w z : ℂ)) * (acorr f (rd hd x - rd hd z) : ℂ) *
            ZMod.stdAddChar (j * (x - z)) := by rw [hL2]
      _ = ∑ x, ∑ z, (P : ℂ) * (((w x : ℂ) * (w z : ℂ)) * (acorr f (rd hd x - rd hd z) : ℂ) *
            ZMod.stdAddChar (j * (x - z))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x _ => by rw [Finset.mul_sum])
      _ = ∑ x, ∑ z, ∑ l : ZMod P, (Fq f l * Gq f l) * (((w x : ℂ) * (w z : ℂ)) *
            ZMod.stdAddChar ((j + iota' Q α l) * (x - z))) :=
          Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => hxz x z))
      _ = ∑ l : ZMod P, ∑ x, ∑ z, (Fq f l * Gq f l) * (((w x : ℂ) * (w z : ℂ)) *
            ZMod.stdAddChar ((j + iota' Q α l) * (x - z))) :=
          (Finset.sum_congr rfl (fun x _ => Finset.sum_comm)).trans Finset.sum_comm
      _ = ∑ l : ZMod P, (Fq f l * Gq f l) * (Fq w (j + iota' Q α l) * Gq w (j + iota' Q α l)) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [FG_expand w, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          all_goals (apply Finset.sum_congr rfl; intro z _; ring)
      _ = _ := by
          apply Finset.sum_congr rfl
          intro l _
          rw [FG_normsq, FG_normsq]
  exact_mod_cast hmain

/-- **Exact average of the total weight.** -/
theorem mass_avg (hQ : Q = P * α) (f : ZMod P → ℝ) (w : ZMod Q → ℝ) :
    ∑ τ : ZMod P, ∑ x, f (rd (Dvd.intro α hQ.symm) x - τ) * w x =
      (∑ y, f y) * (∑ x, w x) := by
  rw [Finset.sum_comm]
  have h : ∀ x : ZMod Q, ∑ τ : ZMod P, f (rd (Dvd.intro α hQ.symm) x - τ) * w x =
      (∑ y, f y) * w x := by
    intro x
    rw [← Finset.sum_mul]
    congr 1
    exact Equiv.sum_comp (Equiv.subLeft (rd (Dvd.intro α hQ.symm) x)) f
  simp_rw [h]
  rw [← Finset.mul_sum]

end transfer

#print axioms amp_avg
#print axioms mass_avg

end JARandom
end LeanCheck
