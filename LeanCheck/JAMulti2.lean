import Mathlib
import LeanCheck.JAMulti
import LeanCheck.JAFinal

/-!
# Multi-level realization: energy bound, mass bound and support for a whole cascade

Uses `JAMulti.multi_exists` (shifts at ALL levels) and the per-level results of `JAMass` / `JASupport`.

Checked here (no axiom, no `sorry`):

* `multi_realization`: for two chains there are shifts at every level with
  `E(g_n^a, g_n^b) ≤ 3 L^3 (Mavg_a ∗ Mavg_b)(arc(m-1)) / (Q_a Q_b)^2`, `L = X + 1 + Q_a + Q_b`, where `Mavg` is the
  DETERMINISTIC expected kernel measure of the whole cascade (the seed's kernel measure convolved with the window kernels,
  with the factors `q_k^{-2}`);
* `Mavg_nonneg_pos0`, `central_pos`: `Mavg` is nonnegative with positive mass at `0`, hence the central arc mass is positive;
* `mass_chain`, `total_lower_chain`: for EVERY choice of shifts, the total mass of the `n`-th weight is at least
  `∏_{k<n} (α_k I_1 - 2) · ∑ seed`, and the total over `[0, X]` at least `((X+1-Q)/Q)` times that;
* `support_chain`: if the seed is supported at `0` and the windows are `w_{q_k}`, then two integers in the support of the
  `n`-th weight satisfy `q_0 ∣ a - a'` and `‖(a - a')/q_i‖ < 2/D` for all `1 ≤ i ≤ n`;
* `dense_step_multi`: `DenseDifferences` at one height, now with a purely DETERMINISTIC hypothesis on the central mass
  `Mavg_a ∗ Mavg_b`: no earlier shift appears in the hypothesis.
-/

namespace LeanCheck
namespace JAMulti2

open Finset MixedPrime JATransfer JARandom JAPackaging JAEnergyLink JARealization JABlocks JALocalize JAMulti
  JAWindowQ JASupport JADense JAFinal JAAssembly JAEnergyIdentity

/-! ### The energy bound for the whole cascade -/

theorem multi_realization {N : ℕ} [NeZero N] (na nb : ℕ) (ca cb : Chain)
    (hNa : ∀ k, k ≤ na → ca.q k ∣ N) (hNb : ∀ k, k ≤ nb → cb.q k ∣ N)
    (hwa : ∀ k x, 0 ≤ ca.w k x) (hwb : ∀ k x, 0 ≤ cb.w k x)
    (seeda : ZMod (ca.q 0) → ℝ) (seedb : ZMod (cb.q 0) → ℝ)
    (hsa : ∀ x, 0 ≤ seeda x) (hsb : ∀ x, 0 ≤ seedb x)
    (X m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ N) (hLm : N ≤ (X + 1 + ca.q na + cb.q nb) * m) :
    ∃ (τa : ∀ k, ZMod (ca.q k)) (τb : ∀ k, ZMod (cb.q k)),
      energyE (ca.weights τa seeda na) (cb.weights τb seedb nb) X ≤
        3 * ((X + 1 + ca.q na + cb.q nb : ℕ) : ℝ) ^ 3 *
          (∑ t ∈ arc N (m - 1), conv (Mavg N na ca (kernq N (ca.q 0) seeda))
            (Mavg N nb cb (kernq N (cb.q 0) seedb)) t) / (((ca.q na : ℝ) * cb.q nb) ^ 2) := by
  classical
  set L : ℕ := X + 1 + ca.q na + cb.q nb with hL
  obtain ⟨τa, τb, hΦ⟩ := multi_exists N L na nb ca cb hNa hNb seeda seedb
  refine ⟨τa, τb, ?_⟩
  have hga := weights_nonneg ca hwa τa seeda hsa na
  have hgb := weights_nonneg cb hwb τb seedb hsb nb
  have hN₂ : N = ca.q na * (N / ca.q na) := (Nat.mul_div_cancel' (hNa na le_rfl)).symm
  have hN₃ : N = cb.q nb * (N / cb.q nb) := (Nat.mul_div_cancel' (hNb nb le_rfl)).symm
  have hE := energy_le_psi (N := N) (q₂ := ca.q na) (q₃ := cb.q nb) (d₂ := N / ca.q na)
    (d₃ := N / cb.q nb) hN₂ hN₃ (ca.weights τa seeda na) (cb.weights τb seedb nb) hga hgb X
  have hPDa : PD (Mavg N na ca (kernq N (ca.q 0) seeda)) :=
    Mavg_PD N na ca hwa hNa _ (kernq_PD N (ca.q 0) (hNa 0 (Nat.zero_le _)) seeda hsa)
  have hPDb : PD (Mavg N nb cb (kernq N (cb.q 0) seedb)) :=
    Mavg_PD N nb cb hwb hNb _ (kernq_PD N (cb.q 0) (hNb 0 (Nat.zero_le _)) seedb hsb)
  have hPD := hPDa.conv hPDb
  have hwin := spectral_window L m hm hmN hLm _ hPD.nonneg hPD.coef
  have hQ : (0 : ℝ) < ((ca.q na : ℝ) * cb.q nb) ^ 2 := by
    have h1 : (0 : ℝ) < ca.q na := by exact_mod_cast ca.pos na
    have h2 : (0 : ℝ) < cb.q nb := by exact_mod_cast cb.pos nb
    positivity
  have hΦ' : ∑ x, nuM N (ca.q na) (cb.q nb) (N / ca.q na) (N / cb.q nb) (ca.weights τa seeda na)
        (cb.weights τb seedb nb) x * JASpectral.Psi L (ang N x) ≤
      3 * (L : ℝ) ^ 3 * ∑ t ∈ arc N (m - 1), conv (Mavg N na ca (kernq N (ca.q 0) seeda))
        (Mavg N nb cb (kernq N (cb.q 0) seedb)) t :=
    hΦ.trans hwin
  calc energyE (ca.weights τa seeda na) (cb.weights τb seedb nb) X
      ≤ 1 / ((ca.q na : ℝ) * cb.q nb) ^ 2 * ∑ x, nuM N (ca.q na) (cb.q nb) (N / ca.q na)
          (N / cb.q nb) (ca.weights τa seeda na) (cb.weights τb seedb nb) x *
            JASpectral.Psi L (ang N x) := hE
    _ ≤ 1 / ((ca.q na : ℝ) * cb.q nb) ^ 2 * (3 * (L : ℝ) ^ 3 * ∑ t ∈ arc N (m - 1),
          conv (Mavg N na ca (kernq N (ca.q 0) seeda)) (Mavg N nb cb (kernq N (cb.q 0) seedb)) t) :=
        mul_le_mul_of_nonneg_left hΦ' (by positivity)
    _ = _ := by rw [hL]; ring

/-! ### Positivity of the central mass -/

lemma Mavg_nonneg_pos0 {N : ℕ} [NeZero N] (D : ℝ) :
    ∀ (n : ℕ) (c : Chain), (∀ k, c.w (k + 1) = wQ D (c.q (k + 1))) →
      ∀ s : ZMod N → ℝ, (∀ x, 0 ≤ s x) → 0 < s 0 →
        (∀ x, 0 ≤ Mavg N n c s x) ∧ 0 < Mavg N n c s 0 := by
  intro n
  induction n with
  | zero => intro c _ s hs hs0; exact ⟨hs, hs0⟩
  | succ n ih =>
    intro c hw s hs hs0
    simp only [Mavg]
    have hkw0 : ∀ x, 0 ≤ kernq N (c.q 1) (c.w 1) x := fun x => kern_nonneg' _ _ _ x
    have hkwpos : 0 < kernq N (c.q 1) (c.w 1) 0 := by
      have h1 := kern_zero_ge (N := N) (c.q 1) (N / c.q 1) (c.w 1)
      have h2 : 0 < ∑ x, c.w 1 x := by rw [hw 0]; exact sum_wQ_pos D
      exact lt_of_lt_of_le (by positivity) h1
    have hP : (0 : ℝ) < 1 / ((c.q 0 : ℕ) : ℝ) ^ 2 := by
      have : (0 : ℝ) < ((c.q 0 : ℕ) : ℝ) := by exact_mod_cast c.pos 0
      positivity
    apply ih c.tail (fun k => hw (k + 1))
    · intro x
      exact mul_nonneg hP.le (conv_nonneg' _ _ hs hkw0 x)
    · exact mul_pos hP (lt_of_lt_of_le (mul_pos hs0 hkwpos) (conv_zero_ge _ _ hs hkw0))

/-! ### Mass of the cascade for every shift -/

lemma mass_chain (c : Chain) (D : ℝ) (hD : 3 ≤ D) (hw : ∀ k, c.w (k + 1) = wQ D (c.q (k + 1)))
    (hw0 : ∀ k x, 0 ≤ c.w k x) (α : ℕ → ℕ) (hα : ∀ k, c.q (k + 1) = c.q k * α k)
    (τ : ∀ k, ZMod (c.q k)) (seed : ZMod (c.q 0) → ℝ) (hs : ∀ x, 0 ≤ seed x) :
    ∀ n : ℕ, (∀ k, k < n → 2 < (α k : ℝ) * (16 / (15 * D))) →
      (∏ k ∈ range n, ((α k : ℝ) * (16 / (15 * D)) - 2)) * ∑ y, seed y ≤
        ∑ x, c.weights τ seed n x := by
  intro n
  induction n with
  | zero => intro _; simp only [Finset.range_zero, Finset.prod_empty, one_mul]; exact le_rfl
  | succ n ih =>
    intro hI
    have ih' := ih (fun k hk => hI k (by omega))
    have hg := weights_nonneg c hw0 τ seed hs n
    have hfac : 0 < (α n : ℝ) * (16 / (15 * D)) - 2 := by linarith [hI n (by omega)]
    have hmass := (JAMass.mass_bounds D hD (hα n) (c.dvd n) (c.weights τ seed n) hg (τ n)).1
    have e : ∀ x, c.weights τ seed (n + 1) x =
        c.weights τ seed n (rd (c.dvd n) x - τ n) * wQ D (c.q (n + 1)) x := by
      intro x
      show c.weights τ seed n (rd (c.dvd n) x - τ n) * c.w (n + 1) x = _
      rw [hw n]
    simp_rw [e]
    rw [Finset.prod_range_succ]
    calc (∏ k ∈ range n, ((α k : ℝ) * (16 / (15 * D)) - 2)) *
          ((α n : ℝ) * (16 / (15 * D)) - 2) * ∑ y, seed y
        = ((α n : ℝ) * (16 / (15 * D)) - 2) *
          ((∏ k ∈ range n, ((α k : ℝ) * (16 / (15 * D)) - 2)) * ∑ y, seed y) := by ring
      _ ≤ ((α n : ℝ) * (16 / (15 * D)) - 2) * ∑ y, c.weights τ seed n y :=
          mul_le_mul_of_nonneg_left ih' hfac.le
      _ ≤ _ := hmass

lemma total_lower_chain (c : Chain) (D : ℝ) (hD : 3 ≤ D) (hw : ∀ k, c.w (k + 1) = wQ D (c.q (k + 1)))
    (hw0 : ∀ k x, 0 ≤ c.w k x) (α : ℕ → ℕ) (hα : ∀ k, c.q (k + 1) = c.q k * α k)
    (τ : ∀ k, ZMod (c.q k)) (seed : ZMod (c.q 0) → ℝ) (hs : ∀ x, 0 ≤ seed x) (n : ℕ)
    (hI : ∀ k, k < n → 2 < (α k : ℝ) * (16 / (15 * D))) (X : ℕ) (hX : c.q n ≤ X + 1) :
    ((X : ℝ) + 1 - c.q n) / c.q n *
        ((∏ k ∈ range n, ((α k : ℝ) * (16 / (15 * D)) - 2)) * ∑ y, seed y) ≤
      ∑ x ∈ range (X + 1), fn (c.weights τ seed n) x := by
  have hg := weights_nonneg c hw0 τ seed hs n
  have h1 := total_ge (fn (c.weights τ seed n)) (c.q n) (c.pos n)
    (fun x => by unfold fn; exact hg _) (fn_per _) X
  have e : ∑ x ∈ range (c.q n), fn (c.weights τ seed n) x = ∑ x, c.weights τ seed n x :=
    (sum_zmod (c.weights τ seed n)).symm
  have h2 := mass_chain c D hD hw hw0 α hα τ seed hs n hI
  have hc : 0 ≤ ((X : ℝ) + 1 - c.q n) / c.q n := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    have : (c.q n : ℝ) ≤ X + 1 := by exact_mod_cast hX
    linarith
  rw [e] at h1
  exact (mul_le_mul_of_nonneg_left h2 hc).trans h1

/-! ### Support of the whole cascade -/

lemma support_chain (c : Chain) (D : ℝ) (hD : 0 < D) (hw : ∀ k, c.w (k + 1) = wQ D (c.q (k + 1)))
    (τ : ∀ k, ZMod (c.q k)) (seed : ZMod (c.q 0) → ℝ) (hseed : ∀ x, seed x ≠ 0 → x = 0) :
    ∀ (n : ℕ) (a a' : ℤ), c.weights τ seed n (a : ZMod (c.q n)) ≠ 0 →
      c.weights τ seed n (a' : ZMod (c.q n)) ≠ 0 →
      ((c.q 0 : ℕ) : ℤ) ∣ a - a' ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ n → nrm (((a - a' : ℤ) : ℝ) / (c.q i : ℕ)) < 2 / D := by
  intro n
  induction n with
  | zero =>
    intro a a' ha ha'
    refine ⟨?_, fun i hi1 hi2 => by omega⟩
    have h1 := hseed _ ha
    have h2 := hseed _ ha'
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
    exact dvd_sub h1 h2
  | succ n ih =>
    intro a a' ha ha'
    have hshift : ∀ b : ℤ, rd (c.dvd n) (b : ZMod (c.q (n + 1))) - τ n =
        ((b - ((τ n).val : ℤ) : ℤ) : ZMod (c.q n)) := by
      intro b
      rw [map_intCast, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hfa : c.weights τ seed (n + 1) (a : ZMod (c.q (n + 1))) =
        c.weights τ seed n (((a - ((τ n).val : ℤ) : ℤ)) : ZMod (c.q n)) *
          wQ D (c.q (n + 1)) (a : ZMod (c.q (n + 1))) := by
      show c.weights τ seed n (rd (c.dvd n) (a : ZMod (c.q (n + 1))) - τ n) *
        c.w (n + 1) (a : ZMod (c.q (n + 1))) = _
      rw [hshift, hw n]
    have hfa' : c.weights τ seed (n + 1) (a' : ZMod (c.q (n + 1))) =
        c.weights τ seed n (((a' - ((τ n).val : ℤ) : ℤ)) : ZMod (c.q n)) *
          wQ D (c.q (n + 1)) (a' : ZMod (c.q (n + 1))) := by
      show c.weights τ seed n (rd (c.dvd n) (a' : ZMod (c.q (n + 1))) - τ n) *
        c.w (n + 1) (a' : ZMod (c.q (n + 1))) = _
      rw [hshift, hw n]
    rw [hfa] at ha
    rw [hfa'] at ha'
    have ha1 := left_ne_zero_of_mul ha
    have ha2 := right_ne_zero_of_mul ha
    have ha1' := left_ne_zero_of_mul ha'
    have ha2' := right_ne_zero_of_mul ha'
    obtain ⟨hdv, hlev⟩ := ih (a - ((τ n).val : ℤ)) (a' - ((τ n).val : ℤ)) ha1 ha1'
    have e : (a - ((τ n).val : ℤ)) - (a' - ((τ n).val : ℤ)) = a - a' := by ring
    rw [e] at hdv hlev
    refine ⟨hdv, ?_⟩
    intro i hi1 hi2
    rcases Nat.lt_or_ge n i with h | h
    · have hi : i = n + 1 := by omega
      subst hi
      exact window_diff hD a a' ha2 ha2'
    · exact hlev i hi1 h

/-! ### One height, deterministic hypothesis -/

lemma chain_dvd_of_le (c : Chain) : ∀ (k n : ℕ), k ≤ n → c.q k ∣ c.q n := by
  intro k n h
  induction n, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ n hn ih => exact ih.trans (c.dvd n)

theorem dense_step_multi (ca cb : Chain) (D C ε : ℝ) (hD : 3 ≤ D) (hC : 0 < C)
    (hwa : ∀ k, ca.w (k + 1) = wQ D (ca.q (k + 1))) (hwb : ∀ k, cb.w (k + 1) = wQ D (cb.q (k + 1)))
    (hw0a : ∀ k x, 0 ≤ ca.w k x) (hw0b : ∀ k x, 0 ≤ cb.w k x)
    (αa αb : ℕ → ℕ) (hαa : ∀ k, ca.q (k + 1) = ca.q k * αa k) (hαb : ∀ k, cb.q (k + 1) = cb.q k * αb k)
    (seeda : ZMod (ca.q 0) → ℝ) (seedb : ZMod (cb.q 0) → ℝ)
    (hsa : ∀ x, 0 ≤ seeda x) (hsb : ∀ x, 0 ≤ seedb x)
    (hsa0 : 0 < seeda 0) (hsb0 : 0 < seedb 0)
    (hsa1 : 0 < ∑ y, seeda y) (hsb1 : 0 < ∑ y, seedb y)
    (na nb : ℕ) (hIa : ∀ k, k < na → 2 < (αa k : ℝ) * (16 / (15 * D)))
    (hIb : ∀ k, k < nb → 2 < (αb k : ℝ) * (16 / (15 * D)))
    (X m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ ca.q na * cb.q nb)
    (hLm : ca.q na * cb.q nb ≤ (X + 1 + ca.q na + cb.q nb) * m)
    (h4a : 4 * ca.q na ≤ X) (h4b : 4 * cb.q nb ≤ X)
    (hcen : ∑ t ∈ arc (ca.q na * cb.q nb) (m - 1),
        conv (Mavg (ca.q na * cb.q nb) na ca (kernq (ca.q na * cb.q nb) (ca.q 0) seeda))
          (Mavg (ca.q na * cb.q nb) nb cb (kernq (ca.q na * cb.q nb) (cb.q 0) seedb)) t ≤
      C * (((∏ k ∈ range na, ((αa k : ℝ) * (16 / (15 * D)) - 2)) * ∑ y, seeda y) *
        ((∏ k ∈ range nb, ((αb k : ℝ) * (16 / (15 * D)) - 2)) * ∑ y, seedb y)) ^ 2)
    (hdiffa : ∀ τ : ∀ k, ZMod (ca.q k), ∀ a ∈ suppSet (ca.weights τ seeda na) X,
      ∀ a' ∈ suppSet (ca.weights τ seeda na) X, Pn (sqScales 2) (a - a') < ε)
    (hdiffb : ∀ τ : ∀ k, ZMod (cb.q k), ∀ a ∈ suppSet (cb.weights τ seedb nb) X,
      ∀ a' ∈ suppSet (cb.weights τ seedb nb) X, Pn (sqScales 3) (a - a') < ε) :
    ∃ A2 A3 : Finset ℤ, (∀ a ∈ A2, 0 ≤ a ∧ a ≤ X) ∧ (∀ a ∈ A3, 0 ≤ a ∧ a ≤ X) ∧
      (∀ a ∈ A3, ∀ a' ∈ A3, Pn (sqScales 3) (a - a') < ε) ∧
      (∀ b ∈ A2, ∀ b' ∈ A2, Pn (sqScales 2) (b - b') < ε) ∧
      1 / (64 * C) * (2 * (X : ℝ) + 1) ≤ ((Vset A3 A2).card : ℝ) := by
  classical
  have hD0 : 0 < D := by linarith
  set N := ca.q na * cb.q nb with hN
  have hNa : ∀ k, k ≤ na → ca.q k ∣ N := fun k hk =>
    (chain_dvd_of_le ca k na hk).trans (Dvd.intro _ rfl)
  have hNb : ∀ k, k ≤ nb → cb.q k ∣ N := fun k hk =>
    (chain_dvd_of_le cb k nb hk).trans (Dvd.intro_left _ rfl)
  -- positivity of the central mass
  have hMa := Mavg_nonneg_pos0 (N := N) D na ca hwa (kernq N (ca.q 0) seeda) (fun x => kern_nonneg' _ _ _ x)
    (lt_of_lt_of_le (by positivity) (kern_zero_ge (N := N) (ca.q 0) (N / ca.q 0) seeda))
  have hMb := Mavg_nonneg_pos0 (N := N) D nb cb hwb (kernq N (cb.q 0) seedb) (fun x => kern_nonneg' _ _ _ x)
    (lt_of_lt_of_le (by positivity) (kern_zero_ge (N := N) (cb.q 0) (N / cb.q 0) seedb))
  have hBpos : 0 < ∑ t ∈ arc N (m - 1), conv (Mavg N na ca (kernq N (ca.q 0) seeda))
      (Mavg N nb cb (kernq N (cb.q 0) seedb)) t := by
    have h0arc : (0 : ZMod N) ∈ arc N (m - 1) := by
      unfold arc
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), by simp⟩)
    have hsingle := Finset.single_le_sum (f := fun t => conv (Mavg N na ca (kernq N (ca.q 0) seeda))
      (Mavg N nb cb (kernq N (cb.q 0) seedb)) t)
      (fun t _ => conv_nonneg' _ _ hMa.1 hMb.1 t) h0arc
    exact lt_of_lt_of_le (lt_of_lt_of_le (mul_pos hMa.2 hMb.2) (conv_zero_ge _ _ hMa.1 hMb.1)) hsingle
  obtain ⟨τa, τb, hE⟩ := multi_realization (N := N) na nb ca cb hNa hNb hw0a hw0b seeda seedb hsa hsb X m hm hmN hLm
  set fa := ca.weights τa seeda na with hfa
  set fb := cb.weights τb seedb nb with hfb
  have hQa : (0 : ℝ) < ca.q na := by exact_mod_cast ca.pos na
  have hQb : (0 : ℝ) < cb.q nb := by exact_mod_cast cb.pos nb
  have hQa4 : (4 : ℝ) * ca.q na ≤ X := by exact_mod_cast h4a
  have hQb4 : (4 : ℝ) * cb.q nb ≤ X := by exact_mod_cast h4b
  have hTa := total_lower_chain ca D hD hwa hw0a αa hαa τa seeda hsa na hIa X (by omega)
  have hTb := total_lower_chain cb D hD hwb hw0b αb hαb τb seedb hsb nb hIb X (by omega)
  have hpa : 0 < ∏ k ∈ range na, ((αa k : ℝ) * (16 / (15 * D)) - 2) :=
    Finset.prod_pos (fun k hk => by linarith [hIa k (Finset.mem_range.mp hk)])
  have hpb : 0 < ∏ k ∈ range nb, ((αb k : ℝ) * (16 / (15 * D)) - 2) :=
    Finset.prod_pos (fun k hk => by linarith [hIb k (Finset.mem_range.mp hk)])
  set ma := (∏ k ∈ range na, ((αa k : ℝ) * (16 / (15 * D)) - 2)) * ∑ y, seeda y with hma
  set mb := (∏ k ∈ range nb, ((αb k : ℝ) * (16 / (15 * D)) - 2)) * ∑ y, seedb y with hmb
  have hma0 : 0 < ma := mul_pos hpa hsa1
  have hmb0 : 0 < mb := mul_pos hpb hsb1
  have hXa : (0 : ℝ) < (X : ℝ) + 1 - ca.q na := by linarith
  have hXb : (0 : ℝ) < (X : ℝ) + 1 - cb.q nb := by linarith
  have hca : 0 < ((X : ℝ) + 1 - ca.q na) / ca.q na * ma := by positivity
  have hcb : 0 < ((X : ℝ) + 1 - cb.q nb) / cb.q nb * mb := by positivity
  have hMT := mul_le_mul hTa hTb hcb.le (le_trans hca.le hTa)
  set B := ∑ t ∈ arc N (m - 1), conv (Mavg N na ca (kernq N (ca.q 0) seeda))
      (Mavg N nb cb (kernq N (cb.q 0) seedb)) t with hB
  set R : ℝ := 3 * ((X + 1 + ca.q na + cb.q nb : ℕ) : ℝ) ^ 3 * B / (((ca.q na : ℝ) * cb.q nb) ^ 2)
    with hR
  have hL : (0 : ℝ) < ((X + 1 + ca.q na + cb.q nb : ℕ) : ℝ) := by positivity
  have hRpos : 0 < R := by rw [hR]; positivity
  have hdA : ∀ τ : ∀ k, ZMod (ca.q k), ∀ a ∈ suppSet (ca.weights τ seeda na) X, ∀ a' ∈ suppSet (ca.weights τ seeda na) X,
      Pn (sqScales 2) (a - a') < ε := hdiffa
  refine ⟨suppSet fa X, suppSet fb X, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; exact (mem_suppSet fa X ha).1
  · intro a ha; exact (mem_suppSet fb X ha).1
  · intro a ha a' ha'; exact hdiffb τb a ha a' ha'
  · intro a ha a' ha'; exact hdiffa τa a ha a' ha'
  · have hcard := card_V_ge_of_energy fa fb X (suppSet fa X) (suppSet fb X) (suppSet_subset fa X)
      (suppSet_subset fb X) (suppSet_vanish fa X) (suppSet_vanish fb X) R _ hRpos (mul_pos hca hcb) hE hMT
    refine le_trans ?_ hcard
    have hY : 0 < ma * mb := mul_pos hma0 hmb0
    have hBY : B ≤ C * (ma * mb) ^ 2 := hcen
    have key := final_ineq (X : ℝ) (ca.q na) (cb.q nb) (ma * mb) B C (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hQa4 hQb4 hY hC hBpos hBY
    refine le_trans key (le_of_eq ?_)
    have hLc : ((X + 1 + ca.q na + cb.q nb : ℕ) : ℝ) = (X : ℝ) + 1 + ca.q na + cb.q nb := by
      push_cast; ring
    rw [hR, hLc]
    field_simp

#print axioms multi_realization
#print axioms Mavg_nonneg_pos0
#print axioms mass_chain
#print axioms total_lower_chain
#print axioms support_chain
#print axioms dense_step_multi

end JAMulti2
end LeanCheck
