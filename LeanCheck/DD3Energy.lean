import Mathlib
import LeanCheck.DD3Reduction
import LeanCheck.JAEnergyFinal
import LeanCheck.JAMulti

/-!
# Diagonal density for three primes: the cubic Fejér step and the three-fold energy link (Lean check)

Scope. Phase 5d of the Lean version of the conditional proof of `DD({2,3,5})` (research note
`TVGplus_conditional_DD235_2026-11-07.md`). It is the three-weight counterpart of `JASpectral.spectral_step`,
`JABlocks.spectral_window`, `JAEnergyLink` and `JAEnergyIdentity.sum_sq_rep_energyE`.

* `Psi3 L θ = L³ + 2 ∑_{h<L} (L-h)³ cos hθ`, `spectral_step3`: `∑ w Ψ³_L ≤ L² ∑ w F_L` for a nonnegative measure with
  nonnegative cosine coefficients (the step `(L-h)³ ≤ L² (L-h)`), `spectral_window3`:
  `∑ ν Ψ³_L ≤ 3 L⁴ ν(arc (m-1))` (with `JABlocks.fej_block_sum`);
* `energyE3 f₂ f₃ f₅ X = ∑_h α₂(h) α₃(h) α₅(h)` (the weighted three-fold collision energy of three periodic weights
  restricted to `[0, X]`), `nuM3 = |f̂₂|² ∗ (|f̂₃|² ∗ |f̂₅|²)`, `nu_cos3` (its cosine coefficients), `energy3_le_psi`,
  `energy3_le_arc`: `E₃ ≤ 3 L⁴ ν(arc (m-1)) / (q₂ q₃ q₅)²`, `L = X+1+q₂+q₃+q₅`, `energy3_normalized`;
* `collision_Aset_eq_energyE3`: the collision sum over triples in the window `{0..X}³` (written as in `DD3.energy3_eq_acf`)
  equals `energyE3`; `collision_support`: it is unchanged by restricting to sets outside which the weights vanish.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Energy

open Finset JALocalize JABlocks JATransfer JAEnergyLink JAEnergyIdentity JASpectral

/-! ### The cubic Fejér step -/

/-- `Ψ³_L(θ) = L³ + 2 ∑_{h=1}^{L-1} (L-h)³ cos (hθ)`. -/
noncomputable def Psi3 (L : ℕ) (θ : ℝ) : ℝ :=
  (L : ℝ) ^ 3 + 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 3 * Real.cos (h * θ)

theorem spectral_step3 {ι : Type*} (s : Finset ι) (w θ : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hpd : ∀ h : ℕ, 0 ≤ ∑ i ∈ s, w i * Real.cos (h * θ i)) (L : ℕ) :
    ∑ i ∈ s, w i * Psi3 L (θ i) ≤ (L : ℝ) ^ 2 * ∑ i ∈ s, w i * Fej L (θ i) := by
  unfold Psi3 Fej
  rw [expand_sum s w θ L (fun h => ((L : ℝ) - h) ^ 3) ((L : ℝ) ^ 3),
    expand_sum s w θ L (fun h => (L : ℝ) - h) (L : ℝ)]
  have hW : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hsum : ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 3 * ∑ i ∈ s, w i * Real.cos (h * θ i) ≤
      (L : ℝ) ^ 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) * ∑ i ∈ s, w i * Real.cos (h * θ i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    rw [Finset.mem_Ico] at hh
    have hLh : (h : ℝ) + 1 ≤ L := by exact_mod_cast hh.2
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh.1
    have hc := hpd h
    have h0 : 0 ≤ (L : ℝ) - h := by linarith
    have hsq : ((L : ℝ) - h) ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
    have h3 : ((L : ℝ) - h) ^ 3 ≤ (L : ℝ) ^ 2 * ((L : ℝ) - h) := by
      have := mul_le_mul_of_nonneg_right hsq h0
      nlinarith [this]
    have := mul_le_mul_of_nonneg_right h3 hc
    nlinarith [this]
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ 3 := by positivity
  nlinarith [mul_nonneg hL0 hW]

/-- **The cubic spectral window bound.** `N ≤ L m` gives `∑ ν Ψ³_L ≤ 3 L⁴ ν(arc (m-1))`. -/
theorem spectral_window3 {N : ℕ} [NeZero N] (L m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hLm : N ≤ L * m)
    (ν : ZMod N → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (hc : ∀ s : ZMod N, ∃ c : ℝ, 0 ≤ c ∧ ∑ x, (ν x : ℂ) * ZMod.stdAddChar (s * x) = (c : ℂ)) :
    ∑ x, ν x * Psi3 L (ang N x) ≤ 3 * (L : ℝ) ^ 4 * ∑ t ∈ arc N (m - 1), ν t := by
  have h1 := spectral_step3 Finset.univ ν (ang N) hν (hpd_of_hc ν hc) L
  have h2 := fej_block_sum L m hm hmN hLm ν hν hc
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  calc ∑ x, ν x * Psi3 L (ang N x) ≤ (L : ℝ) ^ 2 * ∑ x, ν x * Fej L (ang N x) := h1
    _ ≤ (L : ℝ) ^ 2 * (3 * (L : ℝ) ^ 2 * ∑ t ∈ arc N (m - 1), ν t) :=
        mul_le_mul_of_nonneg_left h2 hL0
    _ = 3 * (L : ℝ) ^ 4 * ∑ t ∈ arc N (m - 1), ν t := by ring

/-! ### The three-fold weighted energy -/

section energy3

variable {q₂ q₃ q₅ N d₂ d₃ d₅ : ℕ} [NeZero q₂] [NeZero q₃] [NeZero q₅] [NeZero N]

/-- The weighted three-fold collision energy `E₃ = ∑_h α₂(h) α₃(h) α₅(h)`, written with `α(-h) = α(h)`. -/
noncomputable def energyE3 (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ) (f₅ : ZMod q₅ → ℝ) (X : ℕ) : ℝ :=
  alpha f₂ X 0 * alpha f₃ X 0 * alpha f₅ X 0 +
    2 * ∑ h ∈ Ico 1 (X + 1), alpha f₂ X h * alpha f₃ X h * alpha f₅ X h

/-- The spectral measure `ν = |f̂₂|² ∗ (|f̂₃|² ∗ |f̂₅|²)` on `ZMod N`. -/
noncomputable def nuM3 (N q₂ q₃ q₅ d₂ d₃ d₅ : ℕ) [NeZero N] [NeZero q₂] [NeZero q₃] [NeZero q₅]
    (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ) (f₅ : ZMod q₅ → ℝ) : ZMod N → ℝ :=
  conv (kern N q₂ d₂ f₂) (conv (kern N q₃ d₃ f₃) (kern N q₅ d₅ f₅))

lemma nuM3_PD (hN₂ : N = q₂ * d₂) (hN₃ : N = q₃ * d₃) (hN₅ : N = q₅ * d₅) (f₂ : ZMod q₂ → ℝ)
    (f₃ : ZMod q₃ → ℝ) (f₅ : ZMod q₅ → ℝ) (hf₂ : ∀ y, 0 ≤ f₂ y) (hf₃ : ∀ y, 0 ≤ f₃ y)
    (hf₅ : ∀ y, 0 ≤ f₅ y) : PD (nuM3 N q₂ q₃ q₅ d₂ d₃ d₅ f₂ f₃ f₅) :=
  (kern_PD hN₂ f₂ hf₂).conv ((kern_PD hN₃ f₃ hf₃).conv (kern_PD hN₅ f₅ hf₅))

/-- Cosine coefficients of `ν`: the product of the three period autocorrelations. -/
lemma nu_cos3 (hN₂ : N = q₂ * d₂) (hN₃ : N = q₃ * d₃) (hN₅ : N = q₅ * d₅) (f₂ : ZMod q₂ → ℝ)
    (f₃ : ZMod q₃ → ℝ) (f₅ : ZMod q₅ → ℝ) (h : ℕ) :
    ∑ x, nuM3 N q₂ q₃ q₅ d₂ d₃ d₅ f₂ f₃ f₅ x * Real.cos (h * ang N x) =
      ((q₂ : ℝ) * pi f₂ h) * ((q₃ : ℝ) * pi f₃ h) * ((q₅ : ℝ) * pi f₅ h) := by
  have h1 := fourier_conv (kern N q₂ d₂ f₂) (conv (kern N q₃ d₃ f₃) (kern N q₅ d₅ f₅)) (h : ZMod N)
  have h1b := fourier_conv (kern N q₃ d₃ f₃) (kern N q₅ d₅ f₅) (h : ZMod N)
  rw [coef_pi hN₃, coef_pi hN₅] at h1b
  rw [h1b, coef_pi hN₂] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.re_sum, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re] at h2
  rw [mul_assoc, ← h2]
  apply Finset.sum_congr rfl
  intro x _
  unfold nuM3
  rw [Complex.re_ofReal_mul, stdAddChar_re]

/-- **The weighted three-fold energy is bounded by the cubic spectral window.** -/
theorem energy3_le_psi (hN₂ : N = q₂ * d₂) (hN₃ : N = q₃ * d₃) (hN₅ : N = q₅ * d₅)
    (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ) (f₅ : ZMod q₅ → ℝ)
    (hf₂ : ∀ y, 0 ≤ f₂ y) (hf₃ : ∀ y, 0 ≤ f₃ y) (hf₅ : ∀ y, 0 ≤ f₅ y) (X : ℕ) :
    energyE3 f₂ f₃ f₅ X ≤ 1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 *
      ∑ x, nuM3 N q₂ q₃ q₅ d₂ d₃ d₅ f₂ f₃ f₅ x * Psi3 (X + 1 + q₂ + q₃ + q₅) (ang N x) := by
  set L : ℕ := X + 1 + q₂ + q₃ + q₅ with hL
  have hq₂ : (0 : ℝ) < q₂ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₂)
  have hq₃ : (0 : ℝ) < q₃ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₃)
  have hq₅ : (0 : ℝ) < q₅ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₅)
  have hQ : (0 : ℝ) < ((q₂ : ℝ) * q₃ * q₅) ^ 2 := by positivity
  set c : ℕ → ℝ := fun h => ((q₂ : ℝ) * pi f₂ h) * ((q₃ : ℝ) * pi f₃ h) * ((q₅ : ℝ) * pi f₅ h) with hc
  have hc0 : ∀ h, 0 ≤ c h := fun h =>
    mul_nonneg (mul_nonneg (mul_nonneg hq₂.le (pi_nonneg f₂ hf₂ h)) (mul_nonneg hq₃.le (pi_nonneg f₃ hf₃ h)))
      (mul_nonneg hq₅.le (pi_nonneg f₅ hf₅ h))
  have hexp : ∑ x, nuM3 N q₂ q₃ q₅ d₂ d₃ d₅ f₂ f₃ f₅ x * Psi3 L (ang N x) =
      (L : ℝ) ^ 3 * c 0 + 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 3 * c h := by
    unfold Psi3
    rw [expand_sum Finset.univ (nuM3 N q₂ q₃ q₅ d₂ d₃ d₅ f₂ f₃ f₅) (ang N) L
      (fun h => ((L : ℝ) - h) ^ 3) ((L : ℝ) ^ 3)]
    have h0 := nu_cos3 hN₂ hN₃ hN₅ f₂ f₃ f₅ 0
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one] at h0
    rw [h0]
    congr 2
    apply Finset.sum_congr rfl
    intro h _
    rw [nu_cos3 hN₂ hN₃ hN₅ f₂ f₃ f₅ h]
  rw [hexp]
  have hLR : (L : ℝ) = X + 1 + q₂ + q₃ + q₅ := by rw [hL]; push_cast; ring
  have hterm : ∀ h : ℕ, h ≤ X → alpha f₂ X h * alpha f₃ X h * alpha f₅ X h ≤
      1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * (((L : ℝ) - h) ^ 3 * c h) := by
    intro h hh
    have a2 := alpha_le_pi (q₂ := q₂) f₂ hf₂ X h hh
    have a3 : alpha f₃ X h ≤ ((X : ℝ) + 1 - h + q₃) / q₃ * pi f₃ h :=
      alpha_le_pi (q₂ := q₃) f₃ hf₃ X h hh
    have a5 : alpha f₅ X h ≤ ((X : ℝ) + 1 - h + q₅) / q₅ * pi f₅ h :=
      alpha_le_pi (q₂ := q₅) f₅ hf₅ X h hh
    have hhR : (h : ℝ) ≤ X := by exact_mod_cast hh
    have b2 : ((X : ℝ) + 1 - h + q₂) / q₂ * pi f₂ h ≤ ((L : ℝ) - h) / q₂ * pi f₂ h := by
      apply mul_le_mul_of_nonneg_right _ (pi_nonneg f₂ hf₂ h)
      apply div_le_div_of_nonneg_right _ hq₂.le
      rw [hLR]; linarith
    have b3 : ((X : ℝ) + 1 - h + q₃) / q₃ * pi f₃ h ≤ ((L : ℝ) - h) / q₃ * pi f₃ h := by
      apply mul_le_mul_of_nonneg_right _ (pi_nonneg f₃ hf₃ h)
      apply div_le_div_of_nonneg_right _ hq₃.le
      rw [hLR]; linarith
    have b5 : ((X : ℝ) + 1 - h + q₅) / q₅ * pi f₅ h ≤ ((L : ℝ) - h) / q₅ * pi f₅ h := by
      apply mul_le_mul_of_nonneg_right _ (pi_nonneg f₅ hf₅ h)
      apply div_le_div_of_nonneg_right _ hq₅.le
      rw [hLR]; linarith
    have hLh : 0 ≤ (L : ℝ) - h := by rw [hLR]; linarith
    have hprod : alpha f₂ X h * alpha f₃ X h * alpha f₅ X h ≤
        (((L : ℝ) - h) / q₂ * pi f₂ h) * (((L : ℝ) - h) / q₃ * pi f₃ h) *
          (((L : ℝ) - h) / q₅ * pi f₅ h) := by
      refine mul_le_mul (mul_le_mul (a2.trans b2) (a3.trans b3) (alpha_nonneg f₃ hf₃ X h)
        (mul_nonneg (div_nonneg hLh hq₂.le) (pi_nonneg f₂ hf₂ h))) (a5.trans b5)
        (alpha_nonneg f₅ hf₅ X h)
        (mul_nonneg (mul_nonneg (div_nonneg hLh hq₂.le) (pi_nonneg f₂ hf₂ h))
          (mul_nonneg (div_nonneg hLh hq₃.le) (pi_nonneg f₃ hf₃ h)))
    refine hprod.trans (le_of_eq ?_)
    simp only [hc]
    field_simp
  unfold energyE3
  have hs : ∑ h ∈ Ico 1 (X + 1), alpha f₂ X h * alpha f₃ X h * alpha f₅ X h ≤
      ∑ h ∈ Ico 1 (X + 1), 1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * (((L : ℝ) - h) ^ 3 * c h) :=
    Finset.sum_le_sum (fun h hh => hterm h (by rw [Finset.mem_Ico] at hh; omega))
  have hs2 : ∑ h ∈ Ico 1 (X + 1), 1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * (((L : ℝ) - h) ^ 3 * c h) ≤
      ∑ h ∈ Ico 1 L, 1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * (((L : ℝ) - h) ^ 3 * c h) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro h hh
      rw [Finset.mem_Ico] at hh ⊢
      omega
    · intro h hh _
      rw [Finset.mem_Ico] at hh
      have hLh : (h : ℝ) + 1 ≤ L := by exact_mod_cast hh.2
      have h0 : 0 ≤ (L : ℝ) - h := by linarith
      have := hc0 h
      positivity
  have h0 := hterm 0 (Nat.zero_le X)
  have hs4 : ∑ h ∈ Ico 1 L, 1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * (((L : ℝ) - h) ^ 3 * c h) =
      1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 3 * c h := by
    rw [Finset.mul_sum]
  have hs3 : ∑ h ∈ Ico 1 (X + 1), 1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * (((L : ℝ) - h) ^ 3 * c h) ≤
      ∑ h ∈ Ico 1 L, 1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * (((L : ℝ) - h) ^ 3 * c h) := hs2
  rw [Nat.cast_zero, sub_zero] at h0
  have : 1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * ((L : ℝ) ^ 3 * c 0 + 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 3 * c h) =
      1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * ((L : ℝ) ^ 3 * c 0) +
        2 * (1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * ∑ h ∈ Ico 1 L, ((L : ℝ) - h) ^ 3 * c h) := by ring
  rw [this, ← hs4]
  linarith

/-- **Weighted three-fold energy ≤ cubic spectral window at the central arc.** -/
theorem energy3_le_arc (hN₂ : N = q₂ * d₂) (hN₃ : N = q₃ * d₃) (hN₅ : N = q₅ * d₅)
    (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ) (f₅ : ZMod q₅ → ℝ)
    (hf₂ : ∀ y, 0 ≤ f₂ y) (hf₃ : ∀ y, 0 ≤ f₃ y) (hf₅ : ∀ y, 0 ≤ f₅ y) (X m : ℕ) (hm : 1 ≤ m)
    (hmN : m ≤ N) (hLm : N ≤ (X + 1 + q₂ + q₃ + q₅) * m) :
    energyE3 f₂ f₃ f₅ X ≤ 3 * ((X + 1 + q₂ + q₃ + q₅ : ℕ) : ℝ) ^ 4 *
      (∑ t ∈ arc N (m - 1), nuM3 N q₂ q₃ q₅ d₂ d₃ d₅ f₂ f₃ f₅ t) / ((q₂ : ℝ) * q₃ * q₅) ^ 2 := by
  have h1 := energy3_le_psi hN₂ hN₃ hN₅ f₂ f₃ f₅ hf₂ hf₃ hf₅ X
  have hPD := nuM3_PD hN₂ hN₃ hN₅ f₂ f₃ f₅ hf₂ hf₃ hf₅
  have h2 := spectral_window3 (X + 1 + q₂ + q₃ + q₅) m hm hmN hLm
    (nuM3 N q₂ q₃ q₅ d₂ d₃ d₅ f₂ f₃ f₅) hPD.nonneg hPD.coef
  have hq : (0 : ℝ) < ((q₂ : ℝ) * q₃ * q₅) ^ 2 := by
    have : (0 : ℝ) < q₂ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₂)
    have : (0 : ℝ) < q₃ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₃)
    have : (0 : ℝ) < q₅ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₅)
    positivity
  calc energyE3 f₂ f₃ f₅ X ≤ 1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 *
        ∑ x, nuM3 N q₂ q₃ q₅ d₂ d₃ d₅ f₂ f₃ f₅ x * Psi3 (X + 1 + q₂ + q₃ + q₅) (ang N x) := h1
    _ ≤ 1 / ((q₂ : ℝ) * q₃ * q₅) ^ 2 * (3 * ((X + 1 + q₂ + q₃ + q₅ : ℕ) : ℝ) ^ 4 *
        ∑ t ∈ arc N (m - 1), nuM3 N q₂ q₃ q₅ d₂ d₃ d₅ f₂ f₃ f₅ t) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by field_simp

end energy3

section normalized3

variable {q₂ q₃ q₅ N d₂ d₃ d₅ : ℕ} [NeZero q₂] [NeZero q₃] [NeZero q₅] [NeZero N]

/-- **Normalized weighted three-fold energy.** With `S_p = ∑_{x<q_p} f_p(x)` and `T_p = ∑_{x ≤ X} f_p(x)`,
`E₃ ≤ K (T₂ T₃ T₅)²`, `K = 3 L⁴ ν(arc(m-1)) / ((X+1-q₂)(X+1-q₃)(X+1-q₅) S₂ S₃ S₅)²`. -/
theorem energy3_normalized (hN₂ : N = q₂ * d₂) (hN₃ : N = q₃ * d₃) (hN₅ : N = q₅ * d₅)
    (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ) (f₅ : ZMod q₅ → ℝ)
    (hf₂ : ∀ y, 0 ≤ f₂ y) (hf₃ : ∀ y, 0 ≤ f₃ y) (hf₅ : ∀ y, 0 ≤ f₅ y) (X m : ℕ) (hm : 1 ≤ m)
    (hmN : m ≤ N) (hLm : N ≤ (X + 1 + q₂ + q₃ + q₅) * m) (hX₂ : q₂ < X + 1) (hX₃ : q₃ < X + 1)
    (hX₅ : q₅ < X + 1) (hS₂ : 0 < ∑ x ∈ range q₂, fn f₂ x) (hS₃ : 0 < ∑ x ∈ range q₃, fn f₃ x)
    (hS₅ : 0 < ∑ x ∈ range q₅, fn f₅ x) :
    energyE3 f₂ f₃ f₅ X ≤
      (3 * ((X + 1 + q₂ + q₃ + q₅ : ℕ) : ℝ) ^ 4 *
        (∑ t ∈ arc N (m - 1), nuM3 N q₂ q₃ q₅ d₂ d₃ d₅ f₂ f₃ f₅ t) /
        ((((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) * ((X : ℝ) + 1 - q₅) *
          ((∑ x ∈ range q₂, fn f₂ x) * (∑ x ∈ range q₃, fn f₃ x) * (∑ x ∈ range q₅, fn f₅ x))) ^ 2)) *
      ((∑ x ∈ range (X + 1), fn f₂ x) * (∑ x ∈ range (X + 1), fn f₃ x) *
        (∑ x ∈ range (X + 1), fn f₅ x)) ^ 2 := by
  have hE := energy3_le_arc hN₂ hN₃ hN₅ f₂ f₃ f₅ hf₂ hf₃ hf₅ X m hm hmN hLm
  have hq₂ : (0 : ℝ) < q₂ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₂)
  have hq₃ : (0 : ℝ) < q₃ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₃)
  have hq₅ : (0 : ℝ) < q₅ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q₅)
  set S₂ := ∑ x ∈ range q₂, fn f₂ x with hS₂d
  set S₃ := ∑ x ∈ range q₃, fn f₃ x with hS₃d
  set S₅ := ∑ x ∈ range q₅, fn f₅ x with hS₅d
  set T₂ := ∑ x ∈ range (X + 1), fn f₂ x with hT₂d
  set T₃ := ∑ x ∈ range (X + 1), fn f₃ x with hT₃d
  set T₅ := ∑ x ∈ range (X + 1), fn f₅ x with hT₅d
  set B := ∑ t ∈ arc N (m - 1), nuM3 N q₂ q₃ q₅ d₂ d₃ d₅ f₂ f₃ f₅ t with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun t _ =>
    (nuM3_PD hN₂ hN₃ hN₅ f₂ f₃ f₅ hf₂ hf₃ hf₅).nonneg t)
  have hX₂R : (0 : ℝ) < (X : ℝ) + 1 - q₂ := by
    have : (q₂ : ℝ) < X + 1 := by exact_mod_cast hX₂
    linarith
  have hX₃R : (0 : ℝ) < (X : ℝ) + 1 - q₃ := by
    have : (q₃ : ℝ) < X + 1 := by exact_mod_cast hX₃
    linarith
  have hX₅R : (0 : ℝ) < (X : ℝ) + 1 - q₅ := by
    have : (q₅ : ℝ) < X + 1 := by exact_mod_cast hX₅
    linarith
  have t₂ := total_ge (fn f₂) q₂ (Nat.pos_of_ne_zero (NeZero.ne q₂)) (fun x => hf₂ _) (fn_per f₂) X
  have t₃ := total_ge (fn f₃) q₃ (Nat.pos_of_ne_zero (NeZero.ne q₃)) (fun x => hf₃ _) (fn_per f₃) X
  have t₅ := total_ge (fn f₅) q₅ (Nat.pos_of_ne_zero (NeZero.ne q₅)) (fun x => hf₅ _) (fn_per f₅) X
  set P : ℝ := ((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) * ((X : ℝ) + 1 - q₅) * (S₂ * S₃ * S₅) /
    ((q₂ : ℝ) * q₃ * q₅) with hP
  have hP0 : 0 < P := by positivity
  have hPT : P ≤ T₂ * T₃ * T₅ := by
    have e : P = (((X : ℝ) + 1 - q₂) / q₂ * S₂) * (((X : ℝ) + 1 - q₃) / q₃ * S₃) *
        (((X : ℝ) + 1 - q₅) / q₅ * S₅) := by
      rw [hP]; field_simp
    rw [e]
    have e2 : 0 ≤ ((X : ℝ) + 1 - q₂) / q₂ * S₂ := by positivity
    have e3 : 0 ≤ ((X : ℝ) + 1 - q₃) / q₃ * S₃ := by positivity
    have e5 : 0 ≤ ((X : ℝ) + 1 - q₅) / q₅ * S₅ := by positivity
    exact mul_le_mul (mul_le_mul t₂ t₃ e3 (le_trans e2 t₂)) t₅ e5
      (mul_nonneg (le_trans e2 t₂) (le_trans e3 t₃))
  have hPT2 : P ^ 2 ≤ (T₂ * T₃ * T₅) ^ 2 := pow_le_pow_left₀ hP0.le hPT 2
  have hD : 0 < (((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) * ((X : ℝ) + 1 - q₅) *
      (S₂ * S₃ * S₅)) ^ 2 := by positivity
  have hK : 0 ≤ 3 * ((X + 1 + q₂ + q₃ + q₅ : ℕ) : ℝ) ^ 4 * B /
      (((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) * ((X : ℝ) + 1 - q₅) * (S₂ * S₃ * S₅)) ^ 2 := by
    positivity
  have hEq : 3 * ((X + 1 + q₂ + q₃ + q₅ : ℕ) : ℝ) ^ 4 * B / ((q₂ : ℝ) * q₃ * q₅) ^ 2 =
      (3 * ((X + 1 + q₂ + q₃ + q₅ : ℕ) : ℝ) ^ 4 * B /
        (((X : ℝ) + 1 - q₂) * ((X : ℝ) + 1 - q₃) * ((X : ℝ) + 1 - q₅) * (S₂ * S₃ * S₅)) ^ 2) *
        P ^ 2 := by
    rw [hP]; field_simp
  calc energyE3 f₂ f₃ f₅ X ≤ 3 * ((X + 1 + q₂ + q₃ + q₅ : ℕ) : ℝ) ^ 4 * B /
        ((q₂ : ℝ) * q₃ * q₅) ^ 2 := hE
    _ = _ := hEq
    _ ≤ _ := mul_le_mul_of_nonneg_left hPT2 hK

end normalized3

/-! ### The collision sum over the window -/

section collision

/-- The window `{0, ..., X}` and the weights `Fw` of `JAEnergyIdentity`: the collision sum equals `energyE3`. -/
theorem collision_Aset_eq_energyE3 {q₂ q₃ q₅ : ℕ} [NeZero q₂] [NeZero q₃] [NeZero q₅]
    (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ) (f₅ : ZMod q₅ → ℝ) (X : ℕ) :
    ∑ p ∈ Aset X ×ˢ (Aset X ×ˢ Aset X), ∑ q ∈ Aset X ×ˢ (Aset X ×ˢ Aset X),
        (if DD3.phi p = DD3.phi q then DD3.wt (Fw f₂) (Fw f₃) (Fw f₅) p * DD3.wt (Fw f₂) (Fw f₃) (Fw f₅) q
          else 0) = energyE3 f₂ f₃ f₅ X := by
  have hD : ∀ a ∈ Aset X, ∀ a' ∈ Aset X, a' - a ∈ Finset.Icc (-(X : ℤ)) X := by
    intro a ha a' ha'
    unfold Aset at ha ha'
    simp only [Finset.mem_image, Finset.mem_range] at ha ha'
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := ha'
    rw [Finset.mem_Icc]; omega
  rw [DD3.energy3_eq_acf (A := Aset X) (B := Aset X) (C := Aset X) (Fw f₂) (Fw f₃) (Fw f₅) _ hD]
  rw [sum_Icc_symm (fun h => acf (Aset X) (Fw f₂) h * acf (Aset X) (Fw f₃) h * acf (Aset X) (Fw f₅) h) X]
  have a2 : acf (Aset X) (Fw f₂) (0 : ℤ) = alpha f₂ X 0 := by simpa using acf_Aset_nat f₂ X 0
  have a3 : acf (Aset X) (Fw f₃) (0 : ℤ) = alpha f₃ X 0 := by simpa using acf_Aset_nat f₃ X 0
  have a5 : acf (Aset X) (Fw f₅) (0 : ℤ) = alpha f₅ X 0 := by simpa using acf_Aset_nat f₅ X 0
  unfold energyE3
  simp only [acf_neg, acf_Aset_nat, a2, a3, a5]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => by ring)

/-- The collision sum does not change if the index sets are restricted to sets outside which the weights vanish. -/
theorem collision_support (A A' B B' C C' : Finset ℤ) (f g h : ℤ → ℝ) (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hC : C' ⊆ C) (hf : ∀ a ∈ A, a ∉ A' → f a = 0) (hg : ∀ a ∈ B, a ∉ B' → g a = 0)
    (hh : ∀ a ∈ C, a ∉ C' → h a = 0) :
    ∑ p ∈ A' ×ˢ (B' ×ˢ C'), ∑ q ∈ A' ×ˢ (B' ×ˢ C'),
        (if DD3.phi p = DD3.phi q then DD3.wt f g h p * DD3.wt f g h q else 0) =
      ∑ p ∈ A ×ˢ (B ×ˢ C), ∑ q ∈ A ×ˢ (B ×ˢ C),
        (if DD3.phi p = DD3.phi q then DD3.wt f g h p * DD3.wt f g h q else 0) := by
  have hsub : A' ×ˢ (B' ×ˢ C') ⊆ A ×ˢ (B ×ˢ C) := by
    intro p hp
    simp only [Finset.mem_product] at hp ⊢
    exact ⟨hA hp.1, hB hp.2.1, hC hp.2.2⟩
  have hzero : ∀ p ∈ A ×ˢ (B ×ˢ C), p ∉ A' ×ˢ (B' ×ˢ C') → DD3.wt f g h p = 0 := by
    intro p hp hnp
    simp only [Finset.mem_product] at hp hnp
    unfold DD3.wt
    by_cases h1 : p.1 ∈ A'
    · by_cases h2 : p.2.1 ∈ B'
      · have h3 : p.2.2 ∉ C' := fun h3 => hnp ⟨h1, h2, h3⟩
        rw [hh _ hp.2.2 h3, mul_zero]
      · rw [hg _ hp.2.1 h2, mul_zero, zero_mul]
    · rw [hf _ hp.1 h1, zero_mul, zero_mul]
  calc ∑ p ∈ A' ×ˢ (B' ×ˢ C'), ∑ q ∈ A' ×ˢ (B' ×ˢ C'),
        (if DD3.phi p = DD3.phi q then DD3.wt f g h p * DD3.wt f g h q else 0)
      = ∑ p ∈ A' ×ˢ (B' ×ˢ C'), ∑ q ∈ A ×ˢ (B ×ˢ C),
        (if DD3.phi p = DD3.phi q then DD3.wt f g h p * DD3.wt f g h q else 0) := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_subset hsub
        intro q hq hnq
        simp [hzero q hq hnq]
    _ = ∑ p ∈ A ×ˢ (B ×ˢ C), ∑ q ∈ A ×ˢ (B ×ˢ C),
        (if DD3.phi p = DD3.phi q then DD3.wt f g h p * DD3.wt f g h q else 0) := by
        apply Finset.sum_subset hsub
        intro p hp hnp
        apply Finset.sum_eq_zero
        intro q _
        simp [hzero p hp hnp]

end collision

#print axioms spectral_step3
#print axioms spectral_window3
#print axioms nu_cos3
#print axioms energy3_le_psi
#print axioms energy3_le_arc
#print axioms energy3_normalized
#print axioms collision_Aset_eq_energyE3
#print axioms collision_support

end DD3Energy
end LeanCheck
