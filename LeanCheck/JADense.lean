import Mathlib
import LeanCheck.JARealization
import LeanCheck.JAMass
import LeanCheck.JAEnergyFinal

/-!
# Constant bookkeeping: realization + mass bounds ⟹ a large difference set

Combines
* `JARealization.realization` (there are shifts `τ_a, τ_b` with
  `E ≤ 3 L^3 B / ((Q_a Q_b)^2 (P_a P_b)^2)`, `B = (C_a * C_b)(arc(m-1))`, for the lifted weights
  `g_p(x) = f_p(x mod P_p - τ_p) w_{Q_p}(x)`),
* `JAMass.mass_range` / `total_lower` (for EVERY shift: `T_p ≥ ((X+1-Q_p)/Q_p) (α_p I_1 - 2) ∑ f_p`, the total weight over
  `[0, X]`), and
* `JAAssembly.card_V_ge` (weighted Cauchy–Schwarz; here in the form `card_V_ge_of_energy`: any bound `E ≤ R` and any
  lower bound `M ≤ T_a T_b` give `|A_b - A_a| ≥ M^2 / R`).

Checked here (no axiom, no `sorry`):

* `card_V_ge_of_energy`: `energyE f₂ f₃ X ≤ R`, `0 < M ≤ T₂ T₃`, `0 < R` ⟹ `M^2 / R ≤ |A₃ - A₂|` for supports `A_p ⊆ [0, X]`;
* `total_lower`: the lower bound for the total weight over `range (X+1)` of a realized weight, valid for every shift;
* `realized_difference_bound`: for the concrete windows `w_{D_p}` on `ZMod Q_p` (`D_p ≥ 3`, `α_p I_1(D_p) > 2`,
  `Q_p < X + 1`) there are shifts such that for all supports `A_a, A_b ⊆ [0, X]` outside which the windows vanish
  `((X+1-Q_a)(X+1-Q_b)(α_a I_a - 2)(α_b I_b - 2) ∑f_a ∑f_b P_a P_b)^2 / (3 L^3 B) ≤ |A_b - A_a|`,
  `L = X + 1 + Q_a + Q_b`, `B` the arc mass of `(kern f_a * kern w_a) * (kern f_b * kern w_b)`.

Not checked here: a bound of `B` independent of the seeds (component 13, two-term separation), the support argument and
the compact-quotient criterion.
-/

namespace LeanCheck
namespace JADense

open Finset JAEnergy JAEnergyLink JAEnergyIdentity JAAssembly JABlocks JALocalize JATransfer JARandom JAWindowQ JARealization JAMass

/-- **From an energy bound and a mass bound to a large difference set.** -/
theorem card_V_ge_of_energy {q₂ q₃ : ℕ} [NeZero q₂] [NeZero q₃] (f₂ : ZMod q₂ → ℝ) (f₃ : ZMod q₃ → ℝ)
    (X : ℕ) (A₂ A₃ : Finset ℤ) (hA₂ : A₂ ⊆ Aset X) (hA₃ : A₃ ⊆ Aset X)
    (hs₂ : ∀ a ∈ Aset X, a ∉ A₂ → Fw f₂ a = 0) (hs₃ : ∀ a ∈ Aset X, a ∉ A₃ → Fw f₃ a = 0)
    (R M : ℝ) (hR : 0 < R) (hM : 0 < M) (hE : energyE f₂ f₃ X ≤ R)
    (hMT : M ≤ (∑ x ∈ range (X + 1), fn f₂ x) * (∑ x ∈ range (X + 1), fn f₃ x)) :
    M ^ 2 / R ≤ ((Vset A₃ A₂).card : ℝ) := by
  set Kc : ℝ := R / M ^ 2 with hKc
  have hKpos : 0 < Kc := by positivity
  have hT : 0 < (∑ x ∈ range (X + 1), fn f₂ x) * (∑ x ∈ range (X + 1), fn f₃ x) :=
    lt_of_lt_of_le hM hMT
  have hE' : energyE f₂ f₃ X ≤
      Kc * ((∑ x ∈ range (X + 1), fn f₂ x) * (∑ x ∈ range (X + 1), fn f₃ x)) ^ 2 := by
    calc energyE f₂ f₃ X ≤ R := hE
      _ = Kc * M ^ 2 := by rw [hKc]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM.le hMT 2) hKpos.le
  have hI := sum_sq_rep_energyE f₂ f₃ X
  have hT₂ : ∑ a ∈ A₂, Fw f₂ a = ∑ x ∈ range (X + 1), fn f₂ x := by
    rw [JAEnergyFinal.sum_support (Aset X) A₂ _ hA₂ hs₂, sum_Aset]
    simp [Fw]
  have hT₃ : ∑ a ∈ A₃, Fw f₃ a = ∑ x ∈ range (X + 1), fn f₃ x := by
    rw [JAEnergyFinal.sum_support (Aset X) A₃ _ hA₃ hs₃, sum_Aset]
    simp [Fw]
  have hrep : ∀ d, rep A₃ A₂ (Fw f₃) (Fw f₂) d = rep (Aset X) (Aset X) (Fw f₃) (Fw f₂) d :=
    fun d => JAEnergyFinal.rep_support (Aset X) A₃ (Aset X) A₂ _ _ hA₃ hA₂ hs₃ hs₂ d
  have hmain : ∑ d ∈ Finset.Icc (-(X : ℤ)) X, (rep A₃ A₂ (Fw f₃) (Fw f₂) d) ^ 2 =
      energyE f₂ f₃ X := by
    rw [← hI]
    exact Finset.sum_congr rfl (fun d _ => by rw [hrep d])
  have hXpos : (0 : ℝ) < 2 * (X : ℝ) + 1 := by positivity
  have hm0 : 0 < (∑ a ∈ A₃, Fw f₃ a) * (∑ b ∈ A₂, Fw f₂ b) := by
    rw [hT₂, hT₃, mul_comm]; exact hT
  have hcard := card_V_ge X A₃ A₂ (Fw f₃) (Fw f₂)
    (fun a ha => by
      have := hA₃ ha
      unfold Aset at this
      simp only [Finset.mem_image, Finset.mem_range] at this
      obtain ⟨x, hx, rfl⟩ := this
      omega)
    (fun a ha => by
      have := hA₂ ha
      unfold Aset at this
      simp only [Finset.mem_image, Finset.mem_range] at this
      obtain ⟨x, hx, rfl⟩ := this
      omega)
    hm0 (Kc * (2 * (X : ℝ) + 1)) (by positivity) (by
      rw [hmain]
      have : Kc * (2 * (X : ℝ) + 1) * ((∑ a ∈ A₃, Fw f₃ a) * (∑ b ∈ A₂, Fw f₂ b)) ^ 2 /
          (2 * (X : ℝ) + 1) = Kc * ((∑ a ∈ A₃, Fw f₃ a) * (∑ b ∈ A₂, Fw f₂ b)) ^ 2 := by
        field_simp
      rw [this, hT₂, hT₃, mul_comm (∑ x ∈ range (X + 1), fn f₃ x)]
      exact hE')
  have h1 : (2 * (X : ℝ) + 1) / (Kc * (2 * (X : ℝ) + 1)) = M ^ 2 / R := by
    rw [hKc]; field_simp
  rw [h1] at hcard
  exact hcard

section total

variable {P Q α : ℕ} [NeZero P] [NeZero Q]

/-- The total weight over `[0, X]` of a realized weight is bounded below, for every shift. -/
lemma total_lower (D : ℝ) (hD : 3 ≤ D) (hQ : Q = P * α) (hd : P ∣ Q) (f : ZMod P → ℝ)
    (hf : ∀ y, 0 ≤ f y) (τ : ZMod P) (X : ℕ) (hX : Q ≤ X + 1) :
    ((X : ℝ) + 1 - Q) / Q * ((α * (16 / (15 * D)) - 2) * ∑ y, f y) ≤
      ∑ x ∈ range (X + 1), fn (fun x : ZMod Q => f (rd hd x - τ) * wQ D Q x) x := by
  have hQ0 : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have h1 := total_ge (fn (fun x : ZMod Q => f (rd hd x - τ) * wQ D Q x)) Q hQ0
    (fun x => by unfold fn; exact mul_nonneg (hf _) (wQ_nonneg D _)) (fn_per _) X
  have h2 := (mass_range D hD hQ hd f hf τ).1
  have hc : 0 ≤ ((X : ℝ) + 1 - Q) / Q := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    have : (Q : ℝ) ≤ X + 1 := by exact_mod_cast hX
    linarith
  exact (mul_le_mul_of_nonneg_left h2 hc).trans h1

end total

section main

variable {N Pa Qa αa dPa dQa Pb Qb αb dPb dQb : ℕ} [NeZero N] [NeZero Pa] [NeZero Qa]
  [NeZero Pb] [NeZero Qb]

/-- **Realization with mass bounds: a large difference set.** -/
theorem realized_difference_bound
    (hQa : Qa = Pa * αa) (hNQa : N = Qa * dQa) (hNPa : N = Pa * dPa)
    (hQb : Qb = Pb * αb) (hNQb : N = Qb * dQb) (hNPb : N = Pb * dPb)
    (Da Db : ℝ) (hDa : 3 ≤ Da) (hDb : 3 ≤ Db)
    (fa : ZMod Pa → ℝ) (fb : ZMod Pb → ℝ) (hfa : ∀ x, 0 ≤ fa x) (hfb : ∀ x, 0 ≤ fb x)
    (hsa : 0 < ∑ y, fa y) (hsb : 0 < ∑ y, fb y)
    (hαa : 2 < αa * (16 / (15 * Da))) (hαb : 2 < αb * (16 / (15 * Db)))
    (X m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hLm : N ≤ (X + 1 + Qa + Qb) * m)
    (hXa : Qa < X + 1) (hXb : Qb < X + 1)
    (hB : 0 < ∑ t ∈ arc N (m - 1), conv (conv (kern N Pa dPa fa) (kern N Qa dQa (wQ Da Qa)))
      (conv (kern N Pb dPb fb) (kern N Qb dQb (wQ Db Qb))) t) :
    ∃ τa : ZMod Pa, ∃ τb : ZMod Pb, ∀ A₂ A₃ : Finset ℤ, A₂ ⊆ Aset X → A₃ ⊆ Aset X →
      (∀ a ∈ Aset X, a ∉ A₂ → Fw (wQ Da Qa) a = 0) → (∀ a ∈ Aset X, a ∉ A₃ → Fw (wQ Db Qb) a = 0) →
      (((X : ℝ) + 1 - Qa) * ((X : ℝ) + 1 - Qb) * ((αa * (16 / (15 * Da)) - 2) *
          (αb * (16 / (15 * Db)) - 2)) * ((∑ y, fa y) * (∑ y, fb y)) * ((Pa : ℝ) * Pb)) ^ 2 /
        (3 * ((X + 1 + Qa + Qb : ℕ) : ℝ) ^ 3 * (∑ t ∈ arc N (m - 1),
          conv (conv (kern N Pa dPa fa) (kern N Qa dQa (wQ Da Qa)))
            (conv (kern N Pb dPb fb) (kern N Qb dQb (wQ Db Qb))) t)) ≤ ((Vset A₃ A₂).card : ℝ) := by
  classical
  have hda : Pa ∣ Qa := Dvd.intro αa hQa.symm
  have hdb : Pb ∣ Qb := Dvd.intro αb hQb.symm
  obtain ⟨τa, τb, hE⟩ := realization hQa hNQa hNPa hQb hNQb hNPb fa (wQ Da Qa) fb (wQ Db Qb)
    hfa (wQ_nonneg Da) hfb (wQ_nonneg Db) X m hm hmN hLm
  refine ⟨τa, τb, ?_⟩
  intro A₂ A₃ hA₂ hA₃ hs₂ hs₃
  set B := ∑ t ∈ arc N (m - 1), conv (conv (kern N Pa dPa fa) (kern N Qa dQa (wQ Da Qa)))
      (conv (kern N Pb dPb fb) (kern N Qb dQb (wQ Db Qb))) t with hBdef
  set R : ℝ := 3 * ((X + 1 + Qa + Qb : ℕ) : ℝ) ^ 3 * B / (((Qa : ℝ) * Qb) ^ 2 * ((Pa : ℝ) * Pb) ^ 2)
    with hR
  have hPa : (0 : ℝ) < Pa := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Pa)
  have hPb : (0 : ℝ) < Pb := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Pb)
  have hQa0 : (0 : ℝ) < Qa := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Qa)
  have hQb0 : (0 : ℝ) < Qb := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Qb)
  have hL : (0 : ℝ) < ((X + 1 + Qa + Qb : ℕ) : ℝ) := by positivity
  have hRpos : 0 < R := by rw [hR]; positivity
  have hXa' : (Qa : ℝ) < X + 1 := by exact_mod_cast hXa
  have hXb' : (Qb : ℝ) < X + 1 := by exact_mod_cast hXb
  have hca : 0 < ((X : ℝ) + 1 - Qa) / Qa * ((αa * (16 / (15 * Da)) - 2) * ∑ y, fa y) := by
    have : 0 < (X : ℝ) + 1 - Qa := by linarith
    have : 0 < αa * (16 / (15 * Da)) - 2 := by linarith
    positivity
  have hcb : 0 < ((X : ℝ) + 1 - Qb) / Qb * ((αb * (16 / (15 * Db)) - 2) * ∑ y, fb y) := by
    have : 0 < (X : ℝ) + 1 - Qb := by linarith
    have : 0 < αb * (16 / (15 * Db)) - 2 := by linarith
    positivity
  have hTa := total_lower (α := αa) Da hDa hQa hda fa hfa τa X hXa.le
  have hTb := total_lower (α := αb) Db hDb hQb hdb fb hfb τb X hXb.le
  have hMT := mul_le_mul hTa hTb hcb.le (le_trans hca.le hTa)
  have hcard := card_V_ge_of_energy
    (fun x : ZMod Qa => fa (rd hda x - τa) * wQ Da Qa x)
    (fun x : ZMod Qb => fb (rd hdb x - τb) * wQ Db Qb x) X A₂ A₃ hA₂ hA₃
    (fun a ha hna => by
      have h0 : wQ Da Qa ((a.toNat : ℕ) : ZMod Qa) = 0 := hs₂ a ha hna
      show fa (rd hda ((a.toNat : ℕ) : ZMod Qa) - τa) * wQ Da Qa ((a.toNat : ℕ) : ZMod Qa) = 0
      rw [h0, mul_zero])
    (fun a ha hna => by
      have h0 : wQ Db Qb ((a.toNat : ℕ) : ZMod Qb) = 0 := hs₃ a ha hna
      show fb (rd hdb ((a.toNat : ℕ) : ZMod Qb) - τb) * wQ Db Qb ((a.toNat : ℕ) : ZMod Qb) = 0
      rw [h0, mul_zero])
    R _ hRpos (mul_pos hca hcb) hE hMT
  refine le_trans (le_of_eq ?_) hcard
  rw [hR]
  field_simp

/-- **Same bound, supports taken from the realized weights.** The supports `A_p` only have to contain the support of
the realized weight `g_p(τ_p)` (not of the window), which is what the cascade needs: `A_p` is then the support of the
last-level weight and `A_p - A_p ⊆ U_{p,2/D}` by `JASupport`. -/
theorem realized_difference_bound_supp
    (hQa : Qa = Pa * αa) (hNQa : N = Qa * dQa) (hNPa : N = Pa * dPa)
    (hQb : Qb = Pb * αb) (hNQb : N = Qb * dQb) (hNPb : N = Pb * dPb)
    (Da Db : ℝ) (hDa : 3 ≤ Da) (hDb : 3 ≤ Db)
    (fa : ZMod Pa → ℝ) (fb : ZMod Pb → ℝ) (hfa : ∀ x, 0 ≤ fa x) (hfb : ∀ x, 0 ≤ fb x)
    (hsa : 0 < ∑ y, fa y) (hsb : 0 < ∑ y, fb y)
    (hαa : 2 < αa * (16 / (15 * Da))) (hαb : 2 < αb * (16 / (15 * Db)))
    (X m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hLm : N ≤ (X + 1 + Qa + Qb) * m)
    (hXa : Qa < X + 1) (hXb : Qb < X + 1)
    (hB : 0 < ∑ t ∈ arc N (m - 1), conv (conv (kern N Pa dPa fa) (kern N Qa dQa (wQ Da Qa)))
      (conv (kern N Pb dPb fb) (kern N Qb dQb (wQ Db Qb))) t) :
    ∃ τa : ZMod Pa, ∃ τb : ZMod Pb, ∀ A₂ A₃ : Finset ℤ, A₂ ⊆ Aset X → A₃ ⊆ Aset X →
      (∀ a ∈ Aset X, a ∉ A₂ → Fw (fun x : ZMod Qa =>
        fa (rd (Dvd.intro αa hQa.symm) x - τa) * wQ Da Qa x) a = 0) →
      (∀ a ∈ Aset X, a ∉ A₃ → Fw (fun x : ZMod Qb =>
        fb (rd (Dvd.intro αb hQb.symm) x - τb) * wQ Db Qb x) a = 0) →
      (((X : ℝ) + 1 - Qa) * ((X : ℝ) + 1 - Qb) * ((αa * (16 / (15 * Da)) - 2) *
          (αb * (16 / (15 * Db)) - 2)) * ((∑ y, fa y) * (∑ y, fb y)) * ((Pa : ℝ) * Pb)) ^ 2 /
        (3 * ((X + 1 + Qa + Qb : ℕ) : ℝ) ^ 3 * (∑ t ∈ arc N (m - 1),
          conv (conv (kern N Pa dPa fa) (kern N Qa dQa (wQ Da Qa)))
            (conv (kern N Pb dPb fb) (kern N Qb dQb (wQ Db Qb))) t)) ≤ ((Vset A₃ A₂).card : ℝ) := by
  classical
  have hda : Pa ∣ Qa := Dvd.intro αa hQa.symm
  have hdb : Pb ∣ Qb := Dvd.intro αb hQb.symm
  obtain ⟨τa, τb, hE⟩ := realization hQa hNQa hNPa hQb hNQb hNPb fa (wQ Da Qa) fb (wQ Db Qb)
    hfa (wQ_nonneg Da) hfb (wQ_nonneg Db) X m hm hmN hLm
  refine ⟨τa, τb, ?_⟩
  intro A₂ A₃ hA₂ hA₃ hs₂ hs₃
  set B := ∑ t ∈ arc N (m - 1), conv (conv (kern N Pa dPa fa) (kern N Qa dQa (wQ Da Qa)))
      (conv (kern N Pb dPb fb) (kern N Qb dQb (wQ Db Qb))) t with hBdef
  set R : ℝ := 3 * ((X + 1 + Qa + Qb : ℕ) : ℝ) ^ 3 * B / (((Qa : ℝ) * Qb) ^ 2 * ((Pa : ℝ) * Pb) ^ 2)
    with hR
  have hPa : (0 : ℝ) < Pa := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Pa)
  have hPb : (0 : ℝ) < Pb := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Pb)
  have hQa0 : (0 : ℝ) < Qa := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Qa)
  have hQb0 : (0 : ℝ) < Qb := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Qb)
  have hL : (0 : ℝ) < ((X + 1 + Qa + Qb : ℕ) : ℝ) := by positivity
  have hRpos : 0 < R := by rw [hR]; positivity
  have hXa' : (Qa : ℝ) < X + 1 := by exact_mod_cast hXa
  have hXb' : (Qb : ℝ) < X + 1 := by exact_mod_cast hXb
  have hca : 0 < ((X : ℝ) + 1 - Qa) / Qa * ((αa * (16 / (15 * Da)) - 2) * ∑ y, fa y) := by
    have : 0 < (X : ℝ) + 1 - Qa := by linarith
    have : 0 < αa * (16 / (15 * Da)) - 2 := by linarith
    positivity
  have hcb : 0 < ((X : ℝ) + 1 - Qb) / Qb * ((αb * (16 / (15 * Db)) - 2) * ∑ y, fb y) := by
    have : 0 < (X : ℝ) + 1 - Qb := by linarith
    have : 0 < αb * (16 / (15 * Db)) - 2 := by linarith
    positivity
  have hTa := total_lower (α := αa) Da hDa hQa hda fa hfa τa X hXa.le
  have hTb := total_lower (α := αb) Db hDb hQb hdb fb hfb τb X hXb.le
  have hMT := mul_le_mul hTa hTb hcb.le (le_trans hca.le hTa)
  have hcard := card_V_ge_of_energy
    (fun x : ZMod Qa => fa (rd hda x - τa) * wQ Da Qa x)
    (fun x : ZMod Qb => fb (rd hdb x - τb) * wQ Db Qb x) X A₂ A₃ hA₂ hA₃ hs₂ hs₃
    R _ hRpos (mul_pos hca hcb) hE hMT
  refine le_trans (le_of_eq ?_) hcard
  rw [hR]
  field_simp

end main

#print axioms card_V_ge_of_energy
#print axioms total_lower
#print axioms realized_difference_bound
#print axioms realized_difference_bound_supp

end JADense
end LeanCheck
