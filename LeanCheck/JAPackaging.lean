import Mathlib
import LeanCheck.JARandom

/-!
# Measure-level packaging of the random-translation average (end of component 15)

With `N = Q d_Q = P d_P`, `Q = P α`, `kern N Q d g` the spectral (kernel) measure of `g : ZMod Q → ℝ` on `ZMod N`
(`JATransfer.kern`), and `g_τ(x) = f(x mod P - τ) w(x)`:

* `fourier_inj`: two real functions on `ZMod N` with the same Fourier coefficients are equal;
* `sum_acorr_tau`: `∑_τ acorr g_τ (t) = acorr w (t) · acorr f (t mod P)`;
* `expected_measure`: the expected spectral measure of the translated lifted weight is the convolution
  `(1/P) ∑_τ kern(g_τ) = P^{-2} · (kern f) * (kern w)` on `ZMod N`.

Consequently `JATransfer.PD.conv`/`spectral_window_conv` apply to the expected measure of the construction.
The proof compares the Fourier coefficients (`kern_coef`: `Q · acorr`) and does not need the reflection `l ↦ -l`.
-/

namespace LeanCheck
namespace JAPackaging

open Finset JALocalize MixedPrimeProduct JATransfer JARandom

section inj

variable {N : ℕ} [NeZero N]

/-- Fourier uniqueness on `ZMod N`. -/
lemma fourier_inj (u v : ZMod N → ℝ)
    (h : ∀ s : ZMod N, ∑ y, (u y : ℂ) * ZMod.stdAddChar (s * y) =
      ∑ y, (v y : ℂ) * ZMod.stdAddChar (s * y)) : u = v := by
  have hprim : (ZMod.stdAddChar : AddChar (ZMod N) ℂ).IsPrimitive := ZMod.isPrimitive_stdAddChar N
  have inv : ∀ (w : ZMod N → ℝ) (y : ZMod N),
      ∑ s : ZMod N, (∑ x, (w x : ℂ) * ZMod.stdAddChar (s * x)) * ZMod.stdAddChar (-(s * y)) =
        (N : ℂ) * (w y : ℂ) := by
    intro w y
    have hsum : ∀ x : ZMod N, ∑ s : ZMod N, (ZMod.stdAddChar (s * (x - y)) : ℂ) =
        if x - y = 0 then (N : ℂ) else 0 := by
      intro x
      rw [AddChar.sum_mulShift _ hprim]
      split_ifs <;> simp [ZMod.card]
    calc ∑ s : ZMod N, (∑ x, (w x : ℂ) * ZMod.stdAddChar (s * x)) * ZMod.stdAddChar (-(s * y))
        = ∑ s : ZMod N, ∑ x, (w x : ℂ) * ZMod.stdAddChar (s * (x - y)) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _
          rw [mul_assoc, ← AddChar.map_add_eq_mul]
          congr 2
          ring
      _ = ∑ x, (w x : ℂ) * ∑ s : ZMod N, ZMod.stdAddChar (s * (x - y)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
      _ = ∑ x, (w x : ℂ) * (if x - y = 0 then (N : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hsum x]
      _ = (N : ℂ) * (w y : ℂ) := by
          rw [Finset.sum_eq_single y]
          · simp; ring
          · intro x _ hx
            have : x - y ≠ 0 := sub_ne_zero.mpr hx
            simp [this]
          · intro h; exact absurd (Finset.mem_univ _) h
  funext y
  have h1 := inv u y
  have h2 := inv v y
  simp_rw [h] at h1
  have h3 : (N : ℂ) * (u y : ℂ) = (N : ℂ) * (v y : ℂ) := by rw [← h1, h2]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  exact_mod_cast mul_left_cancel₀ hN h3

end inj

section pack

variable {P Q α N dP dQ : ℕ} [NeZero P] [NeZero Q] [NeZero N]

lemma sum_acorr_tau (hd : P ∣ Q) (f : ZMod P → ℝ) (w : ZMod Q → ℝ) (t : ZMod Q) :
    ∑ τ : ZMod P, acorr (fun x => f (rd hd x - τ) * w x) t = acorr w t * acorr f (rd hd t) := by
  have h1 : ∀ τ : ZMod P, acorr (fun x => f (rd hd x - τ) * w x) t =
      ∑ x, (w x * w (x + t)) * (f (rd hd x - τ) * f (rd hd x + rd hd t - τ)) := by
    intro τ
    unfold acorr
    apply Finset.sum_congr rfl
    intro x _
    beta_reduce
    rw [map_add]
    ring
  rw [Finset.sum_congr rfl (fun τ _ => h1 τ), Finset.sum_comm]
  have h2 : ∀ x : ZMod Q, ∑ τ : ZMod P, (w x * w (x + t)) *
      (f (rd hd x - τ) * f (rd hd x + rd hd t - τ)) = (w x * w (x + t)) * acorr f (rd hd t) := by
    intro x
    rw [← Finset.mul_sum]
    congr 1
    have := tau_acorr f (rd hd x + rd hd t) (rd hd x)
    rw [add_sub_cancel_left] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro τ _
    ring
  rw [Finset.sum_congr rfl (fun x _ => h2 x), ← Finset.sum_mul]
  rfl

/-- **The expected spectral measure of the translated lifted weight is a convolution.** -/
theorem expected_measure (hQ : Q = P * α) (hNQ : N = Q * dQ) (hNP : N = P * dP)
    (f : ZMod P → ℝ) (w : ZMod Q → ℝ) (y : ZMod N) :
    (1 / (P : ℝ)) * ∑ τ : ZMod P,
        kern N Q dQ (fun x => f (rd (Dvd.intro α hQ.symm) x - τ) * w x) y =
      (1 / (P : ℝ) ^ 2) * conv (kern N P dP f) (kern N Q dQ w) y := by
  have hd : P ∣ Q := Dvd.intro α hQ.symm
  have hP : (P : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne P
  have hfun : (fun y => (1 / (P : ℝ)) * ∑ τ : ZMod P,
        kern N Q dQ (fun x => f (rd hd x - τ) * w x) y) =
      (fun y => (1 / (P : ℝ) ^ 2) * conv (kern N P dP f) (kern N Q dQ w) y) := by
    apply fourier_inj
    intro s
    -- coefficient of the left side
    have hl : ∑ y : ZMod N, (((1 / (P : ℝ)) * ∑ τ : ZMod P,
        kern N Q dQ (fun x => f (rd hd x - τ) * w x) y : ℝ) : ℂ) * ZMod.stdAddChar (s * y) =
        ((1 / (P : ℝ) * ∑ τ : ZMod P, (Q : ℝ) *
          acorr (fun x => f (rd hd x - τ) * w x) ((s.val : ℕ) : ZMod Q) : ℝ) : ℂ) := by
      have : ∀ y : ZMod N, (((1 / (P : ℝ)) * ∑ τ : ZMod P,
          kern N Q dQ (fun x => f (rd hd x - τ) * w x) y : ℝ) : ℂ) * ZMod.stdAddChar (s * y) =
          ((1 / (P : ℝ) : ℝ) : ℂ) * ∑ τ : ZMod P,
            (kern N Q dQ (fun x => f (rd hd x - τ) * w x) y : ℂ) * ZMod.stdAddChar (s * y) := by
        intro y
        push_cast
        rw [mul_assoc, Finset.sum_mul]
      simp_rw [this]
      rw [← Finset.mul_sum, Finset.sum_comm]
      have h2 : ∀ τ : ZMod P, ∑ y : ZMod N, (kern N Q dQ (fun x => f (rd hd x - τ) * w x) y : ℂ) *
          ZMod.stdAddChar (s * y) =
          (((Q : ℝ) * acorr (fun x => f (rd hd x - τ) * w x) ((s.val : ℕ) : ZMod Q) : ℝ) : ℂ) :=
        fun τ => kern_coef hNQ _ s
      simp_rw [h2]
      push_cast
      rfl
    -- coefficient of the right side
    have hr : ∑ y : ZMod N, (((1 / (P : ℝ) ^ 2) * conv (kern N P dP f) (kern N Q dQ w) y : ℝ) : ℂ) *
        ZMod.stdAddChar (s * y) =
        (((1 / (P : ℝ) ^ 2) * (((P : ℝ) * acorr f ((s.val : ℕ) : ZMod P)) *
          ((Q : ℝ) * acorr w ((s.val : ℕ) : ZMod Q))) : ℝ) : ℂ) := by
      have h3 := fourier_conv (kern N P dP f) (kern N Q dQ w) s
      rw [kern_coef hNP, kern_coef hNQ] at h3
      have : ∀ y : ZMod N, (((1 / (P : ℝ) ^ 2) * conv (kern N P dP f) (kern N Q dQ w) y : ℝ) : ℂ) *
          ZMod.stdAddChar (s * y) = (((1 / (P : ℝ) ^ 2 : ℝ)) : ℂ) *
          ((conv (kern N P dP f) (kern N Q dQ w) y : ℂ) * ZMod.stdAddChar (s * y)) := by
        intro y; push_cast; ring
      simp_rw [this]
      rw [← Finset.mul_sum, h3]
      push_cast
      rfl
    rw [hl, hr]
    congr 1
    -- compare the two real numbers
    have hrd : rd hd (((s.val : ℕ) : ZMod Q)) = ((s.val : ℕ) : ZMod P) := by
      unfold rd; rw [map_natCast]
    have hS : ∑ τ : ZMod P, (Q : ℝ) * acorr (fun x => f (rd hd x - τ) * w x) ((s.val : ℕ) : ZMod Q) =
        (Q : ℝ) * (acorr w ((s.val : ℕ) : ZMod Q) * acorr f ((s.val : ℕ) : ZMod P)) := by
      rw [← Finset.mul_sum, sum_acorr_tau hd f w, hrd]
    rw [hS]
    field_simp
  exact congrFun hfun y


/-- **The spectral window bound for the expected spectral measure** of the translated lifted weight. -/
theorem spectral_window_expected (hQ : Q = P * α) (hNQ : N = Q * dQ) (hNP : N = P * dP)
    (f : ZMod P → ℝ) (w : ZMod Q → ℝ) (hf : ∀ x, 0 ≤ f x) (hw : ∀ x, 0 ≤ w x)
    (L m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hLm : N ≤ L * m) :
    ∑ y, ((1 / (P : ℝ)) * ∑ τ : ZMod P,
        kern N Q dQ (fun x => f (rd (Dvd.intro α hQ.symm) x - τ) * w x) y) *
        JASpectral.Psi L (JABlocks.ang N y) ≤
      3 * (L : ℝ) ^ 3 * ∑ t ∈ JALocalize.arc N (m - 1), ((1 / (P : ℝ)) * ∑ τ : ZMod P,
        kern N Q dQ (fun x => f (rd (Dvd.intro α hQ.symm) x - τ) * w x) t) := by
  have hpt : ∀ y, (1 / (P : ℝ)) * ∑ τ : ZMod P,
        kern N Q dQ (fun x => f (rd (Dvd.intro α hQ.symm) x - τ) * w x) y =
      (1 / (P : ℝ) ^ 2) * conv (kern N P dP f) (kern N Q dQ w) y :=
    expected_measure hQ hNQ hNP f w
  have hPD : PD (fun y => (1 / (P : ℝ) ^ 2) * conv (kern N P dP f) (kern N Q dQ w) y) :=
    ((kern_PD hNP f hf).conv (kern_PD hNQ w hw)).smul (by positivity)
  have h := JABlocks.spectral_window L m hm hmN hLm _ hPD.nonneg hPD.coef
  simp only [hpt]
  exact h

#print axioms fourier_inj
#print axioms sum_acorr_tau
#print axioms expected_measure
#print axioms spectral_window_expected

end pack

end JAPackaging
end LeanCheck
