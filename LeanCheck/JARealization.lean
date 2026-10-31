import Mathlib
import LeanCheck.JAPackaging
import LeanCheck.JAEnergyLink

/-!
# From the expectation to one realization of the shifts (end of the elementary chain)

Two independently translated lifted weights `g_a(τ_a)(x) = f_a(x mod P_a - τ_a) w_a(x)` on `ZMod Q_a` and
`g_b(τ_b)(y) = f_b(y mod P_b - τ_b) w_b(y)` on `ZMod Q_b` (`Q_a = P_a α_a`, `Q_b = P_b α_b`, all dividing `N`).

Checked here (no axiom, no `sorry`):

* `sum_conv`: `∑_i ∑_k (A_i * B_k) = (∑_i A_i) * (∑_k B_k)` for convolutions on `ZMod N` (independence of the shifts);
* `realization`: there are shifts `τ_a, τ_b` such that the weighted collision energy of the pair of weights, restricted
  to `[0, X]`, satisfies
  `E ≤ 3 L^3 · (C_a * C_b)(arc(m-1)) / ((Q_a Q_b)^2 (P_a P_b)^2)`, `C_p = kern f_p * kern w_p`, `L = X + 1 + Q_a + Q_b`.
  (Each realization is bounded by the spectral window, the average over `(τ_a, τ_b)` is the convolution of the
  expected spectral measures `expected_measure`, which is PD, so `spectral_window` applies to the average; some pair is
  at most the mean.)

Not checked here: the normalization by the total weights (needs `T_p ≥` a deterministic lower bound for every
realization: the mass bounds of component 11) and the bound of the central arc mass `(C_a * C_b)(arc(m-1))`.
-/

namespace LeanCheck
namespace JARealization

open Finset JALocalize JABlocks JATransfer JARandom JAPackaging JAEnergyLink

section conv

variable {N : ℕ} [NeZero N]

lemma sum_conv {ι κ : Type*} [Fintype ι] [Fintype κ] (A : ι → ZMod N → ℝ) (B : κ → ZMod N → ℝ)
    (x : ZMod N) :
    ∑ i, ∑ k, conv (A i) (B k) x = conv (fun y => ∑ i, A i y) (fun y => ∑ k, B k y) x := by
  unfold conv
  calc ∑ i, ∑ k, ∑ y, A i y * B k (x - y)
      = ∑ y, ∑ i, ∑ k, A i y * B k (x - y) := by
        rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
        exact Finset.sum_comm
    _ = ∑ y, (∑ i, A i y) * (∑ k, B k (x - y)) :=
        Finset.sum_congr rfl (fun y _ => by rw [Finset.sum_mul_sum])

lemma conv_smul (a b : ℝ) (ν₁ ν₂ : ZMod N → ℝ) (x : ZMod N) :
    conv (fun y => a * ν₁ y) (fun y => b * ν₂ y) x = (a * b) * conv ν₁ ν₂ x := by
  unfold conv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

end conv

section real

variable {N Pa Qa αa dPa dQa Pb Qb αb dPb dQb : ℕ} [NeZero N] [NeZero Pa] [NeZero Qa]
  [NeZero Pb] [NeZero Qb]

/-- **Realization of the shifts.** -/
theorem realization (hQa : Qa = Pa * αa) (hNQa : N = Qa * dQa) (hNPa : N = Pa * dPa)
    (hQb : Qb = Pb * αb) (hNQb : N = Qb * dQb) (hNPb : N = Pb * dPb)
    (fa : ZMod Pa → ℝ) (wa : ZMod Qa → ℝ) (fb : ZMod Pb → ℝ) (wb : ZMod Qb → ℝ)
    (hfa : ∀ x, 0 ≤ fa x) (hwa : ∀ x, 0 ≤ wa x) (hfb : ∀ x, 0 ≤ fb x) (hwb : ∀ x, 0 ≤ wb x)
    (X m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hLm : N ≤ (X + 1 + Qa + Qb) * m) :
    ∃ τa : ZMod Pa, ∃ τb : ZMod Pb,
      energyE (fun x => fa (rd (Dvd.intro αa hQa.symm) x - τa) * wa x)
        (fun x => fb (rd (Dvd.intro αb hQb.symm) x - τb) * wb x) X ≤
      3 * ((X + 1 + Qa + Qb : ℕ) : ℝ) ^ 3 *
        (∑ t ∈ arc N (m - 1), conv (conv (kern N Pa dPa fa) (kern N Qa dQa wa))
          (conv (kern N Pb dPb fb) (kern N Qb dQb wb)) t) /
        (((Qa : ℝ) * Qb) ^ 2 * ((Pa : ℝ) * Pb) ^ 2) := by
  classical
  set L : ℕ := X + 1 + Qa + Qb with hL
  set ga : ZMod Pa → ZMod Qa → ℝ := fun τ x => fa (rd (Dvd.intro αa hQa.symm) x - τ) * wa x with hga
  set gb : ZMod Pb → ZMod Qb → ℝ := fun τ x => fb (rd (Dvd.intro αb hQb.symm) x - τ) * wb x with hgb
  have hga0 : ∀ τ x, 0 ≤ ga τ x := fun τ x => mul_nonneg (hfa _) (hwa x)
  have hgb0 : ∀ τ x, 0 ≤ gb τ x := fun τ x => mul_nonneg (hfb _) (hwb x)
  set Ca := conv (kern N Pa dPa fa) (kern N Qa dQa wa) with hCa
  set Cb := conv (kern N Pb dPb fb) (kern N Qb dQb wb) with hCb
  have hPa : (Pa : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Pa
  have hPb : (Pb : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Pb
  have hQa0 : (Qa : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Qa
  have hQb0 : (Qb : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Qb
  -- the sum over the shifts of the kernel measures
  have hKa : ∀ y, ∑ τ : ZMod Pa, kern N Qa dQa (ga τ) y = (1 / (Pa : ℝ)) * Ca y := by
    intro y
    have h := expected_measure hQa hNQa hNPa fa wa y
    have : ∑ τ : ZMod Pa, kern N Qa dQa (ga τ) y =
        (Pa : ℝ) * ((1 / (Pa : ℝ)) * ∑ τ : ZMod Pa, kern N Qa dQa (ga τ) y) := by
      field_simp
    rw [this]
    have h' : (1 / (Pa : ℝ)) * ∑ τ : ZMod Pa, kern N Qa dQa (ga τ) y =
        (1 / (Pa : ℝ) ^ 2) * Ca y := h
    rw [h']
    field_simp
  have hKb : ∀ y, ∑ τ : ZMod Pb, kern N Qb dQb (gb τ) y = (1 / (Pb : ℝ)) * Cb y := by
    intro y
    have h := expected_measure hQb hNQb hNPb fb wb y
    have : ∑ τ : ZMod Pb, kern N Qb dQb (gb τ) y =
        (Pb : ℝ) * ((1 / (Pb : ℝ)) * ∑ τ : ZMod Pb, kern N Qb dQb (gb τ) y) := by
      field_simp
    rw [this]
    have h' : (1 / (Pb : ℝ)) * ∑ τ : ZMod Pb, kern N Qb dQb (gb τ) y =
        (1 / (Pb : ℝ) ^ 2) * Cb y := h
    rw [h']
    field_simp
  -- the average of the realized spectral measures
  have hsum : ∀ x, ∑ p : ZMod Pa × ZMod Pb, nuM N Qa Qb dQa dQb (ga p.1) (gb p.2) x =
      (1 / (Pa : ℝ)) * (1 / (Pb : ℝ)) * conv Ca Cb x := by
    intro x
    rw [Fintype.sum_prod_type]
    unfold nuM
    rw [sum_conv (fun τ => kern N Qa dQa (ga τ)) (fun τ => kern N Qb dQb (gb τ)) x]
    have e1 : (fun y => ∑ τ : ZMod Pa, kern N Qa dQa (ga τ) y) = fun y => (1 / (Pa : ℝ)) * Ca y :=
      funext hKa
    have e2 : (fun y => ∑ τ : ZMod Pb, kern N Qb dQb (gb τ) y) = fun y => (1 / (Pb : ℝ)) * Cb y :=
      funext hKb
    rw [e1, e2, conv_smul]
  -- the averaged measure is PD
  have hPDa : PD Ca := (kern_PD hNPa fa hfa).conv (kern_PD hNQa wa hwa)
  have hPDb : PD Cb := (kern_PD hNPb fb hfb).conv (kern_PD hNQb wb hwb)
  have hPD : PD (fun x => ((1 / (Pa : ℝ)) * (1 / (Pb : ℝ))) * conv Ca Cb x) :=
    (hPDa.conv hPDb).smul (by positivity)
  have hwin := spectral_window L m hm hmN hLm _ hPD.nonneg hPD.coef
  -- each realization is bounded by the spectral window
  have hE : ∀ p : ZMod Pa × ZMod Pb, energyE (ga p.1) (gb p.2) X ≤
      1 / ((Qa : ℝ) * Qb) ^ 2 * ∑ x, nuM N Qa Qb dQa dQb (ga p.1) (gb p.2) x *
        JASpectral.Psi L (ang N x) :=
    fun p => energy_le_psi hNQa hNQb (ga p.1) (gb p.2) (hga0 p.1) (hgb0 p.2) X
  have hsumE : ∑ p : ZMod Pa × ZMod Pb, energyE (ga p.1) (gb p.2) X ≤
      1 / ((Qa : ℝ) * Qb) ^ 2 * (3 * (L : ℝ) ^ 3 * ∑ t ∈ arc N (m - 1),
        ((1 / (Pa : ℝ)) * (1 / (Pb : ℝ))) * conv Ca Cb t) := by
    calc ∑ p : ZMod Pa × ZMod Pb, energyE (ga p.1) (gb p.2) X
        ≤ ∑ p : ZMod Pa × ZMod Pb, 1 / ((Qa : ℝ) * Qb) ^ 2 * ∑ x,
            nuM N Qa Qb dQa dQb (ga p.1) (gb p.2) x * JASpectral.Psi L (ang N x) :=
          Finset.sum_le_sum (fun p _ => hE p)
      _ = 1 / ((Qa : ℝ) * Qb) ^ 2 * ∑ x, (∑ p : ZMod Pa × ZMod Pb,
            nuM N Qa Qb dQa dQb (ga p.1) (gb p.2) x) * JASpectral.Psi L (ang N x) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
      _ = 1 / ((Qa : ℝ) * Qb) ^ 2 * ∑ x, (((1 / (Pa : ℝ)) * (1 / (Pb : ℝ))) * conv Ca Cb x) *
            JASpectral.Psi L (ang N x) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          rw [hsum x]
      _ ≤ _ := mul_le_mul_of_nonneg_left hwin (by positivity)
  -- some realization is at most the mean
  have hne : (Finset.univ : Finset (ZMod Pa × ZMod Pb)).Nonempty := Finset.univ_nonempty
  set c : ℝ := 3 * (L : ℝ) ^ 3 * (∑ t ∈ arc N (m - 1), conv Ca Cb t) /
    (((Qa : ℝ) * Qb) ^ 2 * ((Pa : ℝ) * Pb) ^ 2) with hc
  have hcard : ((Finset.univ : Finset (ZMod Pa × ZMod Pb)).card : ℝ) = (Pa : ℝ) * Pb := by
    rw [Finset.card_univ, Fintype.card_prod, ZMod.card, ZMod.card]
    push_cast
    rfl
  have hle : ∑ p : ZMod Pa × ZMod Pb, energyE (ga p.1) (gb p.2) X ≤
      ∑ p : ZMod Pa × ZMod Pb, c := by
    refine hsumE.trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, hcard, hc, ← Finset.mul_sum]
    field_simp
  obtain ⟨p, _, hp⟩ := Finset.exists_le_of_sum_le hne hle
  exact ⟨p.1, p.2, hp⟩

end real

#print axioms sum_conv
#print axioms realization

end JARealization
end LeanCheck
