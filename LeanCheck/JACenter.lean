import Mathlib
import LeanCheck.JAProduct2

/-!
# The central bound, step 3: center maximality and the bounds `1 ≤ f_i ≤ B_D`

Checked here (no axiom, no `sorry`):

* `fourier_inversion`, `PD.apply_le` (**center maximality**): a positive definite function `ν` on `ZMod N` (`ν ≥ 0` with real
  nonnegative Fourier coefficients) satisfies `ν(y) ≤ ν(0)` for all `y`;
* `Ftri_PD`: the triangle `F` is positive definite (its Fourier coefficients are `|ŵ(s)|^2/(2m)`);
* `Hs_PD`: all tails `H_i = K_{i+1} ∗ ⋯ ∗ K_L ∗ F` are positive definite;
* `sum_kern`, `sum_normK_le`: the total mass of the unit-atom kernel is `K_Q(T) ≤ 30 D/7` (`KQ_le`, Parseval);
* `normK_PD`, `normK_props`: the unit-atom kernels of the windows are positive definite, `K(0) ≥ 1`, `∑K ≤ 30D/7`;
* `factor_bounds`: `1 ≤ (K ∗ H)(0)/H(0) ≤ B` for a kernel with `K ≥ 0`, `K(0) ≥ 1`, `∑K ≤ B` and `H` positive definite;
* `factors_bounded`: every `f_i` of a list of such kernels satisfies `1 ≤ f_i ≤ B`;
* `S0_bounds`: `0 ≤ S_0 ≤ ∑μ`, and `sum_conv_total : ∑(A ∗ B) = (∑A)(∑B)`.
-/

namespace LeanCheck
namespace JACenter

open Finset JATransfer JAMulti JAProduct JAProduct2 JALocalize

variable {N : ℕ} [NeZero N]

/-! ### Fourier inversion and center maximality -/

lemma fourier_inversion (w : ZMod N → ℝ) (y : ZMod N) :
    ∑ s : ZMod N, (∑ x, (w x : ℂ) * ZMod.stdAddChar (s * x)) * ZMod.stdAddChar (-(s * y)) =
      (N : ℂ) * (w y : ℂ) := by
  have hprim : (ZMod.stdAddChar : AddChar (ZMod N) ℂ).IsPrimitive := ZMod.isPrimitive_stdAddChar N
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

/-- **Center maximality**: a positive definite function on `ZMod N` is largest at the origin. -/
theorem PD.apply_le {ν : ZMod N → ℝ} (h : PD ν) (y : ZMod N) : ν y ≤ ν 0 := by
  choose c hc0 hcc using h.coef
  have key : ∀ y : ZMod N, (N : ℂ) * (ν y : ℂ) = ∑ s, (c s : ℂ) * ZMod.stdAddChar (-(s * y)) := by
    intro y
    rw [← fourier_inversion ν y]
    apply Finset.sum_congr rfl
    intro s _
    rw [hcc s]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h0 : (N : ℝ) * ν 0 = ∑ s, c s := by
    have := key 0
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one] at this
    exact_mod_cast this
  have hy : (N : ℝ) * ν y ≤ ∑ s, c s := by
    have e : (((N : ℝ) * ν y : ℝ) : ℂ) = ∑ s, (c s : ℂ) * ZMod.stdAddChar (-(s * y)) := by
      push_cast; exact key y
    have := congrArg Complex.re e
    rw [Complex.ofReal_re, Complex.re_sum] at this
    rw [this]
    apply Finset.sum_le_sum
    intro s _
    rw [Complex.re_ofReal_mul]
    have h1 : (ZMod.stdAddChar (-(s * y)) : ℂ).re ≤ 1 := by
      refine (Complex.re_le_norm _).trans ?_
      rw [AddChar.norm_apply]
    nlinarith [hc0 s]
  rw [← mul_le_mul_iff_of_pos_left hN, h0]
  exact hy

/-! ### Positive definiteness of the triangle and of the tails -/

lemma Ftri_coef (m : ℕ) (s : ZMod N) :
    ∑ t, (Ftri N m t : ℂ) * ZMod.stdAddChar (s * t) =
      (((‖∑ x, ((win N (2 * m)) x : ℂ) * ZMod.stdAddChar (s * x)‖ ^ 2) / (2 * m : ℝ) : ℝ) : ℂ) := by
  set w := win N (2 * m) with hw
  have hS : ∑ t, (acorr w t : ℂ) * ZMod.stdAddChar (s * t) =
      (((‖∑ x, (w x : ℂ) * ZMod.stdAddChar (s * x)‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← coef_mul_conj w s]
    unfold acorr
    push_cast
    rw [Finset.sum_mul_sum]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    refine Fintype.sum_equiv (Equiv.addLeft z) _ _ (fun t => ?_)
    simp only [Equiv.coe_addLeft]
    have e : ZMod.stdAddChar (s * (z + t)) * ZMod.stdAddChar (-(s * z)) =
        ZMod.stdAddChar (s * t) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    calc (w z : ℂ) * (w (z + t) : ℂ) * ZMod.stdAddChar (s * t)
        = (w z : ℂ) * (w (z + t) : ℂ) *
          (ZMod.stdAddChar (s * (z + t)) * ZMod.stdAddChar (-(s * z))) := by rw [e]
      _ = _ := by ring
  have hterm : ∀ t, (Ftri N m t : ℂ) * ZMod.stdAddChar (s * t) =
      ((1 / (2 * m : ℝ) : ℝ) : ℂ) * ((acorr w t : ℂ) * ZMod.stdAddChar (s * t)) := by
    intro t
    unfold Ftri
    push_cast
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, hS]
  push_cast
  ring

/-- The triangle is positive definite. -/
lemma Ftri_PD (m : ℕ) : PD (Ftri N m) :=
  ⟨Ftri_nonneg m, fun s => ⟨(‖∑ x, ((win N (2 * m)) x : ℂ) * ZMod.stdAddChar (s * x)‖ ^ 2) / (2 * m : ℝ),
    div_nonneg (sq_nonneg _) (by positivity), Ftri_coef m s⟩⟩

lemma Hs_PD (F : ZMod N → ℝ) (hF : PD F) :
    ∀ ks : List (ZMod N → ℝ), (∀ K ∈ ks, PD K) → PD (Hs F ks) := by
  intro ks
  induction ks with
  | nil => intro _; exact hF
  | cons K ks ih =>
    intro h
    exact (h K (List.mem_cons_self)).conv (ih (fun K' hK' => h K' (List.mem_cons_of_mem _ hK')))

/-! ### Total mass of the kernels -/

lemma sum_kern (Q d : ℕ) [NeZero Q] (w : ZMod Q → ℝ) :
    ∑ x : ZMod N, kern N Q d w x =
      ∑ r : ZMod Q, ‖∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)‖ ^ 2 := by
  classical
  unfold kern
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp

lemma sum_normK_le (D : ℝ) (hD : 3 ≤ D) (Q : ℕ) [NeZero Q] (hQ : 25 * D ≤ Q) :
    ∑ x : ZMod N, normK N Q (JAWindowQ.wQ D Q) x ≤ 30 * D / 7 := by
  have hD0 : 0 < D := by linarith
  have h1 : ∑ x : ZMod N, normK N Q (JAWindowQ.wQ D Q) x =
      JAWindowQ.KQ D Q := by
    unfold normK kernq JAWindowQ.KQ
    rw [← Finset.mul_sum, sum_kern]
    rw [one_div, inv_mul_eq_div]
    rfl
  rw [h1]
  exact JAWindowQ.KQ_le D hD hQ

lemma normK_PD (Q : ℕ) [NeZero Q] (hQ : Q ∣ N) (w : ZMod Q → ℝ) (hw : ∀ x, 0 ≤ w x) :
    PD (normK N Q w) :=
  (kernq_PD N Q hQ w hw).smul (by positivity)

/-- The unit-atom kernels of the windows at scales `Q ≥ 25 D`: positive definite, unit atom, mass `≤ 30D/7`. -/
lemma normK_props (D : ℝ) (hD : 3 ≤ D) (Q : ℕ) [NeZero Q] (hQ : 25 * D ≤ Q) (hQN : Q ∣ N) :
    PD (normK N Q (JAWindowQ.wQ D Q)) ∧ 1 ≤ normK N Q (JAWindowQ.wQ D Q) 0 ∧
      ∑ x, normK N Q (JAWindowQ.wQ D Q) x ≤ 30 * D / 7 :=
  ⟨normK_PD Q hQN _ (JAWindowQ.wQ_nonneg D), normK_zero_ge Q _ (JAFinal.sum_wQ_pos D),
    sum_normK_le D hD Q hQ⟩

/-! ### The factors `f_i` and `S_0` -/

lemma sum_conv_total (A B : ZMod N → ℝ) : ∑ x, conv A B x = (∑ x, A x) * ∑ x, B x := by
  unfold conv
  rw [Finset.sum_comm, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun x => rfl)

lemma factor_bounds (K H : ZMod N → ℝ) (hK : ∀ x, 0 ≤ K x) (hK0 : 1 ≤ K 0) (B : ℝ)
    (hKB : ∑ x, K x ≤ B) (hH : PD H) (hH0 : 0 < H 0) :
    1 ≤ conv K H 0 / H 0 ∧ conv K H 0 / H 0 ≤ B := by
  constructor
  · rw [le_div_iff₀ hH0, one_mul]
    have := JAFinal.conv_zero_ge K H hK hH.nonneg
    nlinarith
  · rw [div_le_iff₀ hH0]
    unfold conv
    calc ∑ y, K y * H (0 - y) ≤ ∑ y, K y * H 0 :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (PD.apply_le hH _) (hK y))
      _ = (∑ y, K y) * H 0 := by rw [Finset.sum_mul]
      _ ≤ B * H 0 := mul_le_mul_of_nonneg_right hKB hH0.le

lemma S0_bounds (μ H : ZMod N → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hH : PD H) (hH0 : 0 < H 0) :
    0 ≤ conv μ H 0 / H 0 ∧ conv μ H 0 / H 0 ≤ ∑ x, μ x := by
  constructor
  · exact div_nonneg (JAFinal.conv_nonneg' _ _ hμ hH.nonneg 0) hH0.le
  · rw [div_le_iff₀ hH0]
    unfold conv
    calc ∑ y, μ y * H (0 - y) ≤ ∑ y, μ y * H 0 :=
          Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (PD.apply_le hH _) (hμ y))
      _ = (∑ y, μ y) * H 0 := by rw [Finset.sum_mul]

/-- **Every factor `f_i` of a list of good kernels lies in `[1, B]`.** -/
lemma factors_bounded (F : ZMod N → ℝ) (hFPD : PD F) (hF0 : 1 ≤ F 0) (B : ℝ) (ks : List (ZMod N → ℝ))
    (hks : ∀ K ∈ ks, PD K ∧ (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 ∧ ∑ x, K x ≤ B) :
    ∀ i < ks.length, 1 ≤ Hs F (ks.drop i) 0 / Hs F (ks.drop (i + 1)) 0 ∧
      Hs F (ks.drop i) 0 / Hs F (ks.drop (i + 1)) 0 ≤ B := by
  intro i hi
  have hdrop : ks.drop i = ks[i] :: ks.drop (i + 1) := List.drop_eq_getElem_cons hi
  have hmem : ks[i] ∈ ks := List.getElem_mem hi
  obtain ⟨hKPD, hKnn, hK0, hKB⟩ := hks _ hmem
  have hsub : ∀ K ∈ ks.drop (i + 1), K ∈ ks := fun K hK => List.mem_of_mem_drop hK
  have hHPD : PD (Hs F (ks.drop (i + 1))) :=
    Hs_PD F hFPD _ (fun K hK => (hks K (hsub K hK)).1)
  have hH1 := (Hs_atom F hFPD.nonneg hF0 (ks.drop (i + 1))
    (fun K hK => ⟨(hks K (hsub K hK)).2.1, (hks K (hsub K hK)).2.2.1⟩)).2
  rw [hdrop]
  exact factor_bounds ks[i] _ hKnn hK0 B hKB hHPD (by linarith)

#print axioms PD.apply_le
#print axioms Ftri_PD
#print axioms sum_normK_le
#print axioms normK_props
#print axioms factors_bounded
#print axioms S0_bounds

end JACenter
end LeanCheck
