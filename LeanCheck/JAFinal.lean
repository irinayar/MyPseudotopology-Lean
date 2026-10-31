import Mathlib
import LeanCheck.JASupport

/-!
# The `DenseDifferences` assembly

`JAAssembly.DenseDifferences ε` asks for a constant `c > 0` such that for every `M` there is a height `X ≥ M` and finite sets
`A_2, A_3 ⊆ [0, X]` with `P_p(a - a') < ε` on `A_p - A_p` and `c (2X + 1) ≤ |A_3 - A_2|`.

This file assembles it from the pieces proved so far, plus **one explicit hypothesis** `HeightBound D C X`
(packaging what is *not* formalized: buffered heights, the cascade with its early-level shifts, and the uniform bound on the
central arc mass, i.e. the normalized-product argument of component 13).

Checked here (no axiom, no `sorry`):

* `cascadeG`, `cascadeG_nonneg`: the cascade `g_0 = 1`, `g_{k+1}(x) = g_k(x mod q_k - τ_k) w_{q_{k+1}}(x)`, `q_k = p^{k^2}`,
  for arbitrary shifts `τ`;
* `support_last`: the support argument for the last level, where the last shift `σ` is arbitrary (it is produced by the
  averaging step): `P_p(a - a') < 2/D` on the support in `[0, X]` once the next scale exceeds `D X`;
* `centralMass_pos`: the central arc mass of the product measure is positive for nonnegative seeds with positive mass;
* `final_ineq`: the numerical inequality `(X+1-Q_a)(X+1-Q_b)Y)^2 / (3 L^3 B) ≥ (2X+1)/(64 C)` for `4Q_p ≤ X`, `B ≤ C Y^2`;
* `dense_step`: at one height, from the seeds, the central-mass bound and the difference properties of the supports, the
  conclusion of `DenseDifferences` with `c = 1/(64 C)` (uses `JADense.realized_difference_bound_supp`);
* `denseDifferences_of_heightBounds`: `HeightBound D C X` for arbitrarily large `X` (with `3 ≤ D`, `2/D ≤ ε`, `C > 0`)
  implies `DenseDifferences ε`.

`HeightBound` is NOT proved here.  It says: at the height `X` there are levels `n_2, n_3` and shifts such that the scales
`2^{(n_2+1)^2} ≤ DX < 2^{(n_2+2)^2}` (and likewise for `3`) are buffered (`4 q ≤ X`), the last windows have `α I_1 > 2`, the
earlier-level weights have positive mass, and, for some `m` with `N ≤ (X+1+Q_a+Q_b) m`, the central arc mass is at most
`C ((α_aI_a-2)(α_bI_b-2) S_a S_b P_aP_b)^2`.
-/

namespace LeanCheck
namespace JAFinal

open Finset MixedPrime JAWindowQ JAEnergyLink JAEnergyIdentity JARandom JAAssembly JASupport JATransfer JALocalize JADense

/-! ### The cascade -/

/-- The cascade `g_0 = 1`, `g_{k+1}(x) = g_k(x mod q_k - τ_k) w_{q_{k+1}}(x)`, `q_k = p^{k^2}`. -/
noncomputable def cascadeG (p : ℕ) [NeZero p] (D : ℝ) (τ : (k : ℕ) → ZMod (p ^ (k ^ 2))) :
    (k : ℕ) → ZMod (p ^ (k ^ 2)) → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun x => cascadeG p D τ k (rd (sq_dvd p k) x - τ k) * wQ D (p ^ ((k + 1) ^ 2)) x

lemma cascadeG_nonneg (p : ℕ) [NeZero p] (D : ℝ) (τ : (k : ℕ) → ZMod (p ^ (k ^ 2))) :
    ∀ (k : ℕ) (x : ZMod (p ^ (k ^ 2))), 0 ≤ cascadeG p D τ k x := by
  intro k
  induction k with
  | zero => intro x; simp [cascadeG]
  | succ k ih => intro x; exact mul_nonneg (ih _) (wQ_nonneg D _)

/-- The tail argument: levels `1..L` have small differences and the next scale exceeds `D X`. -/
lemma Pn_of_levels {p : ℕ} [NeZero p] (hp : 2 ≤ p) (D : ℝ) (hD : 0 < D) (X L : ℕ)
    (hL : D * X < (p : ℝ) ^ ((L + 1) ^ 2)) (a a' : ℤ) (haX : 0 ≤ a ∧ a ≤ X) (ha'X : 0 ≤ a' ∧ a' ≤ X)
    (hlev : ∀ i : ℕ, 1 ≤ i → i ≤ L → nrm (((a - a' : ℤ) : ℝ) / ((p ^ (i ^ 2) : ℕ) : ℝ)) < 2 / D) :
    Pn (sqScales p) (a - a') < 2 / D := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  obtain ⟨c₁, hc₁, hc₁'⟩ := exists_lt_bound (Finset.Icc 1 L)
    (fun i => nrm (((a - a' : ℤ) : ℝ) / ((p ^ (i ^ 2) : ℕ) : ℝ))) (2 / D)
    (fun i hi => hlev i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)
  have hXD : (X : ℝ) / (p : ℝ) ^ ((L + 1) ^ 2) < 1 / D := by
    rw [div_lt_div_iff₀ (by positivity) hD]
    linarith
  have hc₂ : (X : ℝ) / (p : ℝ) ^ ((L + 1) ^ 2) < 2 / D := by
    have : 1 / D < 2 / D := div_lt_div_of_pos_right (by norm_num) hD
    linarith
  have hS : (sqScales p).Nonempty := ⟨p ^ (1 ^ 2), mem_sqScales (le_refl 1)⟩
  have hle : Pn (sqScales p) (a - a') ≤ max c₁ ((X : ℝ) / (p : ℝ) ^ ((L + 1) ^ 2)) := by
    apply Pn_le hS
    rintro s ⟨n, hn, rfl⟩
    by_cases hnL : n ≤ L
    · exact (hc₁' n (Finset.mem_Icc.mpr ⟨hn, hnL⟩)).trans (le_max_left _ _)
    · push Not at hnL
      refine le_trans ?_ (le_max_right _ _)
      refine (nrm_le_abs _).trans ?_
      have hpn : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by positivity
      rw [abs_div, abs_of_pos hpn]
      have habs : |((a - a' : ℤ) : ℝ)| ≤ X := by
        have h1 : ((a - a' : ℤ) : ℝ) ≤ X := by
          have : a - a' ≤ (X : ℤ) := by omega
          exact_mod_cast this
        have h2 : -(X : ℝ) ≤ ((a - a' : ℤ) : ℝ) := by
          have : -(X : ℤ) ≤ a - a' := by omega
          exact_mod_cast this
        exact abs_le.mpr ⟨h2, h1⟩
      have hmono : (p : ℝ) ^ ((L + 1) ^ 2) ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        push_cast
        apply pow_le_pow_right₀ hp1
        nlinarith
      calc |((a - a' : ℤ) : ℝ)| / ((p ^ (n ^ 2) : ℕ) : ℝ) ≤ (X : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right habs hpn.le
        _ ≤ (X : ℝ) / (p : ℝ) ^ ((L + 1) ^ 2) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hmono
  exact lt_of_le_of_lt hle (max_lt hc₁ hc₂)

/-- **Support argument for the last level** (the last shift `σ` is arbitrary). -/
theorem support_last {p : ℕ} [NeZero p] (hp : 2 ≤ p) (D : ℝ) (hD : 0 < D)
    (τ : (k : ℕ) → ZMod (p ^ (k ^ 2))) (n X : ℕ) (σ : ZMod (p ^ (n ^ 2)))
    (hd : p ^ (n ^ 2) ∣ p ^ ((n + 1) ^ 2))
    (hL : D * X < (p : ℝ) ^ ((n + 1 + 1) ^ 2)) (a a' : ℤ)
    (ha : cascadeG p D τ n (rd hd (a : ZMod (p ^ ((n + 1) ^ 2))) - σ) *
      wQ D (p ^ ((n + 1) ^ 2)) (a : ZMod (p ^ ((n + 1) ^ 2))) ≠ 0)
    (ha' : cascadeG p D τ n (rd hd (a' : ZMod (p ^ ((n + 1) ^ 2))) - σ) *
      wQ D (p ^ ((n + 1) ^ 2)) (a' : ZMod (p ^ ((n + 1) ^ 2))) ≠ 0)
    (haX : 0 ≤ a ∧ a ≤ X) (ha'X : 0 ≤ a' ∧ a' ≤ X) :
    Pn (sqScales p) (a - a') < 2 / D := by
  have hshift : ∀ b : ℤ, rd hd (b : ZMod (p ^ ((n + 1) ^ 2))) - σ =
      ((b - (σ.val : ℤ) : ℤ) : ZMod (p ^ (n ^ 2))) := by
    intro b
    rw [map_intCast, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hshift] at ha ha'
  have ha1 := left_ne_zero_of_mul ha
  have ha2 := right_ne_zero_of_mul ha
  have ha1' := left_ne_zero_of_mul ha'
  have ha2' := right_ne_zero_of_mul ha'
  have hdiff := support_diff D (fun k => p ^ (k ^ 2)) (sq_dvd p) (cascadeG p D τ) τ
    (fun k x => rfl) hD n (a - (σ.val : ℤ)) (a' - (σ.val : ℤ)) ha1 ha1'
  refine Pn_of_levels hp D hD X (n + 1) hL a a' haX ha'X ?_
  intro i hi1 hi2
  rcases Nat.lt_or_ge n i with h | h
  · have hi : i = n + 1 := by omega
    subst hi
    exact window_diff hD a a' ha2 ha2'
  · have := hdiff i hi1 h
    have e : (a - (σ.val : ℤ)) - (a' - (σ.val : ℤ)) = a - a' := by ring
    rwa [e] at this

/-! ### The central arc mass -/

/-- The central arc mass `(C_a * C_b)(arc(m-1))`, `C_p = kern f_p * kern w_p`, on `ZMod (Q_a Q_b)`. -/
noncomputable def centralMass (D : ℝ) {Pa Qa αa Pb Qb αb : ℕ} [NeZero Pa] [NeZero Qa] [NeZero Pb]
    [NeZero Qb] (fa : ZMod Pa → ℝ) (fb : ZMod Pb → ℝ) (m : ℕ) : ℝ :=
  ∑ t ∈ arc (Qa * Qb) (m - 1),
    conv (conv (kern (Qa * Qb) Pa (αa * Qb) fa) (kern (Qa * Qb) Qa Qb (wQ D Qa)))
      (conv (kern (Qa * Qb) Pb (αb * Qa) fb) (kern (Qa * Qb) Qb Qa (wQ D Qb))) t

section pos

variable {N : ℕ} [NeZero N]

lemma kern_nonneg' (Q d : ℕ) [NeZero Q] (w : ZMod Q → ℝ) (x : ZMod N) : 0 ≤ kern N Q d w x :=
  Finset.sum_nonneg (fun r _ => by split_ifs <;> positivity)

lemma kern_zero_ge (Q d : ℕ) [NeZero Q] (w : ZMod Q → ℝ) : (∑ x, w x) ^ 2 ≤ kern N Q d w 0 := by
  classical
  unfold kern
  have h := Finset.single_le_sum (f := fun r : ZMod Q => if (0 : ZMod N) = ((r.val * d : ℕ) : ZMod N) then
      ‖∑ x, (w x : ℂ) * ZMod.stdAddChar (r * x)‖ ^ 2 else 0)
    (fun r _ => by split_ifs <;> positivity) (Finset.mem_univ (0 : ZMod Q))
  refine le_trans (le_of_eq ?_) h
  show (∑ x, w x) ^ 2 = if (0 : ZMod N) = (((0 : ZMod Q).val * d : ℕ) : ZMod N) then
      ‖∑ x, (w x : ℂ) * ZMod.stdAddChar ((0 : ZMod Q) * x)‖ ^ 2 else 0
  rw [if_pos (by simp)]
  have h0 : (∑ x, (w x : ℂ) * ZMod.stdAddChar ((0 : ZMod Q) * x)) = ((∑ x, w x : ℝ) : ℂ) := by
    simp
  rw [h0, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma conv_nonneg' (u v : ZMod N → ℝ) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) (x : ZMod N) :
    0 ≤ conv u v x :=
  Finset.sum_nonneg (fun y _ => mul_nonneg (hu y) (hv _))

lemma conv_zero_ge (u v : ZMod N → ℝ) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) :
    u 0 * v 0 ≤ conv u v 0 := by
  unfold conv
  have := Finset.single_le_sum (f := fun y => u y * v (0 - y)) (fun y _ => mul_nonneg (hu y) (hv _))
    (Finset.mem_univ (0 : ZMod N))
  simpa using this

end pos

lemma wQ_zero_one (D : ℝ) {Q : ℕ} [NeZero Q] : wQ D Q 0 = 1 := by
  unfold wQ JAWindow.wD
  simp

lemma sum_wQ_pos (D : ℝ) {Q : ℕ} [NeZero Q] : 0 < ∑ x : ZMod Q, wQ D Q x := by
  have h := Finset.single_le_sum (f := fun x : ZMod Q => wQ D Q x) (fun x _ => wQ_nonneg D x)
    (Finset.mem_univ (0 : ZMod Q))
  rw [wQ_zero_one] at h
  linarith

lemma centralMass_pos (D : ℝ) {Pa Qa αa Pb Qb αb : ℕ} [NeZero Pa] [NeZero Qa] [NeZero Pb] [NeZero Qb]
    (fa : ZMod Pa → ℝ) (fb : ZMod Pb → ℝ) (hfa : ∀ x, 0 ≤ fa x) (hfb : ∀ x, 0 ≤ fb x)
    (hsa : 0 < ∑ y, fa y) (hsb : 0 < ∑ y, fb y) (m : ℕ) (hm : 1 ≤ m) :
    0 < centralMass D (αa := αa) (αb := αb) (Qa := Qa) (Qb := Qb) fa fb m := by
  classical
  unfold centralMass
  set N := Qa * Qb with hN
  set ka := kern N Pa (αa * Qb) fa with hka
  set kwa := kern N Qa Qb (wQ D Qa) with hkwa
  set kb := kern N Pb (αb * Qa) fb with hkb
  set kwb := kern N Qb Qa (wQ D Qb) with hkwb
  have hka0 : ∀ x, 0 ≤ ka x := fun x => kern_nonneg' _ _ _ x
  have hkwa0 : ∀ x, 0 ≤ kwa x := fun x => kern_nonneg' _ _ _ x
  have hkb0 : ∀ x, 0 ≤ kb x := fun x => kern_nonneg' _ _ _ x
  have hkwb0 : ∀ x, 0 ≤ kwb x := fun x => kern_nonneg' _ _ _ x
  have hU0 : ∀ x, 0 ≤ conv ka kwa x := conv_nonneg' _ _ hka0 hkwa0
  have hV0 : ∀ x, 0 ≤ conv kb kwb x := conv_nonneg' _ _ hkb0 hkwb0
  have hF0 : ∀ x, 0 ≤ conv (conv ka kwa) (conv kb kwb) x := conv_nonneg' _ _ hU0 hV0
  have h0arc : (0 : ZMod N) ∈ arc N (m - 1) := by
    unfold arc
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), by simp⟩)
  have hsingle := Finset.single_le_sum (f := fun t => conv (conv ka kwa) (conv kb kwb) t)
    (fun t _ => hF0 t) h0arc
  refine lt_of_lt_of_le ?_ hsingle
  have hA : 0 < ka 0 := lt_of_lt_of_le (by positivity) (kern_zero_ge Pa (αa * Qb) fa)
  have hAw : 0 < kwa 0 := lt_of_lt_of_le (by have := sum_wQ_pos D (Q := Qa); positivity)
    (kern_zero_ge Qa Qb (wQ D Qa))
  have hB' : 0 < kb 0 := lt_of_lt_of_le (by positivity) (kern_zero_ge Pb (αb * Qa) fb)
  have hBw : 0 < kwb 0 := lt_of_lt_of_le (by have := sum_wQ_pos D (Q := Qb); positivity)
    (kern_zero_ge Qb Qa (wQ D Qb))
  have hU : 0 < conv ka kwa 0 := lt_of_lt_of_le (mul_pos hA hAw) (conv_zero_ge _ _ hka0 hkwa0)
  have hV : 0 < conv kb kwb 0 := lt_of_lt_of_le (mul_pos hB' hBw) (conv_zero_ge _ _ hkb0 hkwb0)
  exact lt_of_lt_of_le (mul_pos hU hV) (conv_zero_ge _ _ hU0 hV0)

/-! ### The numerical inequality -/

lemma final_ineq (X Qa Qb Y B C : ℝ) (hX : 0 ≤ X) (hQa : 0 ≤ Qa) (hQb : 0 ≤ Qb)
    (h4a : 4 * Qa ≤ X) (h4b : 4 * Qb ≤ X) (hY : 0 < Y) (hC : 0 < C) (hB : 0 < B)
    (hBY : B ≤ C * Y ^ 2) :
    1 / (64 * C) * (2 * X + 1) ≤
      (((X + 1 - Qa) * (X + 1 - Qb)) * Y) ^ 2 / (3 * (X + 1 + Qa + Qb) ^ 3 * B) := by
  have hLc : 0 < X + 1 + Qa + Qb := by linarith
  have hE1 : 9 / 16 * (X + 1) ^ 2 ≤ (X + 1 - Qa) * (X + 1 - Qb) := by
    have ha : 3 / 4 * (X + 1) ≤ X + 1 - Qa := by linarith
    have hb : 3 / 4 * (X + 1) ≤ X + 1 - Qb := by linarith
    calc 9 / 16 * (X + 1) ^ 2 = (3 / 4 * (X + 1)) * (3 / 4 * (X + 1)) := by ring
      _ ≤ (X + 1 - Qa) * (X + 1 - Qb) :=
        mul_le_mul ha hb (by positivity) (by linarith)
  have hE1sq : 81 / 256 * (X + 1) ^ 4 ≤ ((X + 1 - Qa) * (X + 1 - Qb)) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hE1 2
    nlinarith [this]
  have hLub : X + 1 + Qa + Qb ≤ 3 / 2 * (X + 1) := by linarith
  have hL3 : (X + 1 + Qa + Qb) ^ 3 ≤ 27 / 8 * (X + 1) ^ 3 := by
    have := pow_le_pow_left₀ hLc.le hLub 3
    nlinarith [this]
  have h3 : 3 * (X + 1 + Qa + Qb) ^ 3 * (2 * X + 1) ≤ 64 * ((X + 1 - Qa) * (X + 1 - Qb)) ^ 2 := by
    have h2X : 2 * X + 1 ≤ 2 * (X + 1) := by linarith
    calc 3 * (X + 1 + Qa + Qb) ^ 3 * (2 * X + 1)
        ≤ 3 * (27 / 8 * (X + 1) ^ 3) * (2 * (X + 1)) := by
          apply mul_le_mul (by linarith) h2X (by positivity) (by positivity)
      _ = 64 * (81 / 256 * (X + 1) ^ 4) := by ring
      _ ≤ 64 * ((X + 1 - Qa) * (X + 1 - Qb)) ^ 2 := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hC0 : 0 < 64 * C := by positivity
  calc 1 / (64 * C) * (2 * X + 1) * (3 * (X + 1 + Qa + Qb) ^ 3 * B)
      ≤ 1 / (64 * C) * (2 * X + 1) * (3 * (X + 1 + Qa + Qb) ^ 3 * (C * Y ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hBY (by positivity)
    _ = (3 * (X + 1 + Qa + Qb) ^ 3 * (2 * X + 1)) * Y ^ 2 / 64 := by
        field_simp
    _ ≤ (64 * ((X + 1 - Qa) * (X + 1 - Qb)) ^ 2) * Y ^ 2 / 64 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = (((X + 1 - Qa) * (X + 1 - Qb)) * Y) ^ 2 := by ring

/-! ### One height -/

section step

variable {Pa Qa αa Pb Qb αb : ℕ} [NeZero Pa] [NeZero Qa] [NeZero Pb] [NeZero Qb]

/-- **`DenseDifferences` at one height**, from the seeds, the bound on the central mass, and the difference properties of the
supports of the realized last-level weights. -/
theorem dense_step (hQa : Qa = Pa * αa) (hQb : Qb = Pb * αb) (D C ε : ℝ) (hD : 3 ≤ D) (hC : 0 < C)
    (fa : ZMod Pa → ℝ) (fb : ZMod Pb → ℝ) (hfa : ∀ x, 0 ≤ fa x) (hfb : ∀ x, 0 ≤ fb x)
    (hsa : 0 < ∑ y, fa y) (hsb : 0 < ∑ y, fb y)
    (hαa : 2 < αa * (16 / (15 * D))) (hαb : 2 < αb * (16 / (15 * D)))
    (X m : ℕ) (hm : 1 ≤ m) (hmN : m ≤ Qa * Qb) (hLm : Qa * Qb ≤ (X + 1 + Qa + Qb) * m)
    (h4a : 4 * Qa ≤ X) (h4b : 4 * Qb ≤ X)
    (hcen : centralMass D (αa := αa) (αb := αb) (Qa := Qa) (Qb := Qb) fa fb m ≤
      C * ((((αa : ℝ) * (16 / (15 * D)) - 2) * ((αb : ℝ) * (16 / (15 * D)) - 2)) *
        ((∑ y, fa y) * (∑ y, fb y)) * ((Pa : ℝ) * Pb)) ^ 2)
    (hdiffa : ∀ σ : ZMod Pa, ∀ a ∈ suppSet (fun x : ZMod Qa =>
        fa (rd (Dvd.intro αa hQa.symm) x - σ) * wQ D Qa x) X,
      ∀ a' ∈ suppSet (fun x : ZMod Qa => fa (rd (Dvd.intro αa hQa.symm) x - σ) * wQ D Qa x) X,
        Pn (sqScales 2) (a - a') < ε)
    (hdiffb : ∀ σ : ZMod Pb, ∀ a ∈ suppSet (fun x : ZMod Qb =>
        fb (rd (Dvd.intro αb hQb.symm) x - σ) * wQ D Qb x) X,
      ∀ a' ∈ suppSet (fun x : ZMod Qb => fb (rd (Dvd.intro αb hQb.symm) x - σ) * wQ D Qb x) X,
        Pn (sqScales 3) (a - a') < ε) :
    ∃ A2 A3 : Finset ℤ, (∀ a ∈ A2, 0 ≤ a ∧ a ≤ X) ∧ (∀ a ∈ A3, 0 ≤ a ∧ a ≤ X) ∧
      (∀ a ∈ A3, ∀ a' ∈ A3, Pn (sqScales 3) (a - a') < ε) ∧
      (∀ b ∈ A2, ∀ b' ∈ A2, Pn (sqScales 2) (b - b') < ε) ∧
      1 / (64 * C) * (2 * (X : ℝ) + 1) ≤ ((Vset A3 A2).card : ℝ) := by
  classical
  have hD0 : 0 < D := by linarith
  have hB := centralMass_pos D (αa := αa) (αb := αb) (Qa := Qa) (Qb := Qb) fa fb hfa hfb hsa hsb m hm
  have hXa : Qa < X + 1 := by omega
  have hXb : Qb < X + 1 := by omega
  have hNPa : Qa * Qb = Pa * (αa * Qb) := by rw [hQa]; ring
  have hNQb : Qa * Qb = Qb * Qa := mul_comm _ _
  have hNPb : Qa * Qb = Pb * (αb * Qa) := by
    have : Qa * Qb = Qa * (Pb * αb) := by rw [← hQb]
    rw [this]; ring
  obtain ⟨τa, τb, hmain⟩ := realized_difference_bound_supp (N := Qa * Qb) (dQa := Qb)
    (dPa := αa * Qb) (dQb := Qa) (dPb := αb * Qa) hQa rfl hNPa hQb hNQb hNPb D D hD hD fa fb hfa hfb
    hsa hsb hαa hαb X m hm hmN hLm hXa hXb hB
  set Ga : ZMod Qa → ℝ := fun x => fa (rd (Dvd.intro αa hQa.symm) x - τa) * wQ D Qa x with hGa
  set Gb : ZMod Qb → ℝ := fun x => fb (rd (Dvd.intro αb hQb.symm) x - τb) * wQ D Qb x with hGb
  have hbound := hmain (suppSet Ga X) (suppSet Gb X) (suppSet_subset Ga X) (suppSet_subset Gb X)
    (suppSet_vanish Ga X) (suppSet_vanish Gb X)
  refine ⟨suppSet Ga X, suppSet Gb X, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; exact (mem_suppSet Ga X ha).1
  · intro a ha; exact (mem_suppSet Gb X ha).1
  · intro a ha a' ha'; exact hdiffb τb a ha a' ha'
  · intro a ha a' ha'; exact hdiffa τa a ha a' ha'
  · refine le_trans ?_ hbound
    have hcen' : (∑ t ∈ arc (Qa * Qb) (m - 1),
        conv (conv (kern (Qa * Qb) Pa (αa * Qb) fa) (kern (Qa * Qb) Qa Qb (wQ D Qa)))
          (conv (kern (Qa * Qb) Pb (αb * Qa) fb) (kern (Qa * Qb) Qb Qa (wQ D Qb))) t) ≤ _ := hcen
    have hB' : 0 < (∑ t ∈ arc (Qa * Qb) (m - 1),
        conv (conv (kern (Qa * Qb) Pa (αa * Qb) fa) (kern (Qa * Qb) Qa Qb (wQ D Qa)))
          (conv (kern (Qa * Qb) Pb (αb * Qa) fb) (kern (Qa * Qb) Qb Qa (wQ D Qb))) t) := hB
    generalize (∑ t ∈ arc (Qa * Qb) (m - 1),
        conv (conv (kern (Qa * Qb) Pa (αa * Qb) fa) (kern (Qa * Qb) Qa Qb (wQ D Qa)))
          (conv (kern (Qa * Qb) Pb (αb * Qa) fb) (kern (Qa * Qb) Qb Qa (wQ D Qb))) t) = B at hcen' hB' ⊢
    have hQa4 : (4 : ℝ) * Qa ≤ X := by exact_mod_cast h4a
    have hQb4 : (4 : ℝ) * Qb ≤ X := by exact_mod_cast h4b
    have hYa : 0 < (αa : ℝ) * (16 / (15 * D)) - 2 := by linarith
    have hYb : 0 < (αb : ℝ) * (16 / (15 * D)) - 2 := by linarith
    have hPa : (0 : ℝ) < Pa := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Pa)
    have hPb : (0 : ℝ) < Pb := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Pb)
    have hY : 0 < (((αa : ℝ) * (16 / (15 * D)) - 2) * ((αb : ℝ) * (16 / (15 * D)) - 2)) *
        ((∑ y, fa y) * (∑ y, fb y)) * ((Pa : ℝ) * Pb) := by positivity
    have key := final_ineq (X : ℝ) Qa Qb _ B C (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hQa4 hQb4 hY hC hB' hcen'
    refine le_trans key (le_of_eq ?_)
    have hL : ((X + 1 + Qa + Qb : ℕ) : ℝ) = (X : ℝ) + 1 + Qa + Qb := by push_cast; ring
    rw [hL]
    congr 2
    ring

end step

/-! ### The height hypothesis and the assembly -/

/-- **The hypothesis packaging what is not formalized**: buffered heights, the cascade of the earlier levels, and the uniform
bound on the central arc mass (component 13). -/
def HeightBound (D C : ℝ) (X : ℕ) : Prop :=
  ∃ (n₂ n₃ : ℕ) (τ₂ : (k : ℕ) → ZMod (2 ^ (k ^ 2))) (τ₃ : (k : ℕ) → ZMod (3 ^ (k ^ 2))) (m : ℕ),
    D * X < (2 : ℝ) ^ ((n₂ + 1 + 1) ^ 2) ∧ D * X < (3 : ℝ) ^ ((n₃ + 1 + 1) ^ 2) ∧
    4 * 2 ^ ((n₂ + 1) ^ 2) ≤ X ∧ 4 * 3 ^ ((n₃ + 1) ^ 2) ≤ X ∧
    2 < ((2 ^ (2 * n₂ + 1) : ℕ) : ℝ) * (16 / (15 * D)) ∧
    2 < ((3 ^ (2 * n₃ + 1) : ℕ) : ℝ) * (16 / (15 * D)) ∧
    0 < ∑ y, cascadeG 2 D τ₂ n₂ y ∧ 0 < ∑ y, cascadeG 3 D τ₃ n₃ y ∧
    1 ≤ m ∧ m ≤ 2 ^ ((n₂ + 1) ^ 2) * 3 ^ ((n₃ + 1) ^ 2) ∧
    2 ^ ((n₂ + 1) ^ 2) * 3 ^ ((n₃ + 1) ^ 2) ≤
      (X + 1 + 2 ^ ((n₂ + 1) ^ 2) + 3 ^ ((n₃ + 1) ^ 2)) * m ∧
    centralMass D (Qa := 2 ^ ((n₂ + 1) ^ 2)) (Qb := 3 ^ ((n₃ + 1) ^ 2)) (αa := 2 ^ (2 * n₂ + 1))
        (αb := 3 ^ (2 * n₃ + 1)) (cascadeG 2 D τ₂ n₂) (cascadeG 3 D τ₃ n₃) m ≤
      C * (((((2 ^ (2 * n₂ + 1) : ℕ) : ℝ) * (16 / (15 * D)) - 2) *
          (((3 ^ (2 * n₃ + 1) : ℕ) : ℝ) * (16 / (15 * D)) - 2)) *
        ((∑ y, cascadeG 2 D τ₂ n₂ y) * (∑ y, cascadeG 3 D τ₃ n₃ y)) *
        (((2 ^ (n₂ ^ 2) : ℕ) : ℝ) * ((3 ^ (n₃ ^ 2) : ℕ) : ℝ))) ^ 2

lemma pow_succ_sq (p n : ℕ) : p ^ ((n + 1) ^ 2) = p ^ (n ^ 2) * p ^ (2 * n + 1) := by
  rw [← pow_add]; congr 1; ring

/-- **The assembly.**  `HeightBound D C X` at arbitrarily large `X` gives `DenseDifferences ε`. -/
theorem denseDifferences_of_heightBounds {ε : ℝ} (D C : ℝ) (hD : 3 ≤ D) (hDε : 2 / D ≤ ε) (hC : 0 < C)
    (hH : ∀ M : ℕ, ∃ X : ℕ, M ≤ X ∧ HeightBound D C X) : DenseDifferences ε := by
  have hD0 : 0 < D := by linarith
  refine ⟨1 / (64 * C), by positivity, ?_⟩
  intro M
  obtain ⟨X, hMX, n₂, n₃, τ₂, τ₃, m, hL₂, hL₃, hb₂, hb₃, hα₂, hα₃, hs₂, hs₃, hm1, hmN, hLm, hcen⟩ :=
    hH M
  refine ⟨X, hMX, ?_⟩
  have hQa : 2 ^ ((n₂ + 1) ^ 2) = 2 ^ (n₂ ^ 2) * 2 ^ (2 * n₂ + 1) := pow_succ_sq 2 n₂
  have hQb : 3 ^ ((n₃ + 1) ^ 2) = 3 ^ (n₃ ^ 2) * 3 ^ (2 * n₃ + 1) := pow_succ_sq 3 n₃
  have hdiffa : ∀ σ : ZMod (2 ^ (n₂ ^ 2)), ∀ a ∈ suppSet (fun x : ZMod (2 ^ ((n₂ + 1) ^ 2)) =>
        cascadeG 2 D τ₂ n₂ (rd (Dvd.intro _ hQa.symm) x - σ) * wQ D (2 ^ ((n₂ + 1) ^ 2)) x) X,
      ∀ a' ∈ suppSet (fun x : ZMod (2 ^ ((n₂ + 1) ^ 2)) =>
        cascadeG 2 D τ₂ n₂ (rd (Dvd.intro _ hQa.symm) x - σ) * wQ D (2 ^ ((n₂ + 1) ^ 2)) x) X,
        Pn (sqScales 2) (a - a') < ε := by
    intro σ a ha a' ha'
    obtain ⟨hX, hg⟩ := mem_suppSet _ X ha
    obtain ⟨hX', hg'⟩ := mem_suppSet _ X ha'
    exact lt_of_lt_of_le (support_last (p := 2) (by norm_num) D hD0 τ₂ n₂ X σ
      (Dvd.intro _ hQa.symm) hL₂ a a' hg hg' hX hX') hDε
  have hdiffb : ∀ σ : ZMod (3 ^ (n₃ ^ 2)), ∀ a ∈ suppSet (fun x : ZMod (3 ^ ((n₃ + 1) ^ 2)) =>
        cascadeG 3 D τ₃ n₃ (rd (Dvd.intro _ hQb.symm) x - σ) * wQ D (3 ^ ((n₃ + 1) ^ 2)) x) X,
      ∀ a' ∈ suppSet (fun x : ZMod (3 ^ ((n₃ + 1) ^ 2)) =>
        cascadeG 3 D τ₃ n₃ (rd (Dvd.intro _ hQb.symm) x - σ) * wQ D (3 ^ ((n₃ + 1) ^ 2)) x) X,
        Pn (sqScales 3) (a - a') < ε := by
    intro σ a ha a' ha'
    obtain ⟨hX, hg⟩ := mem_suppSet _ X ha
    obtain ⟨hX', hg'⟩ := mem_suppSet _ X ha'
    exact lt_of_lt_of_le (support_last (p := 3) (by norm_num) D hD0 τ₃ n₃ X σ
      (Dvd.intro _ hQb.symm) hL₃ a a' hg hg' hX hX') hDε
  exact dense_step (Pa := 2 ^ (n₂ ^ 2)) (Qa := 2 ^ ((n₂ + 1) ^ 2)) (αa := 2 ^ (2 * n₂ + 1))
    (Pb := 3 ^ (n₃ ^ 2)) (Qb := 3 ^ ((n₃ + 1) ^ 2)) (αb := 3 ^ (2 * n₃ + 1)) hQa hQb D C ε hD hC
    (cascadeG 2 D τ₂ n₂) (cascadeG 3 D τ₃ n₃) (cascadeG_nonneg 2 D τ₂ n₂) (cascadeG_nonneg 3 D τ₃ n₃)
    hs₂ hs₃ hα₂ hα₃ X m hm1 hmN hLm hb₂ hb₃ hcen hdiffa hdiffb

/-- **JA from the two remaining hypotheses**: the compact-quotient criterion and the height bounds at every precision. -/
theorem JA_of_heightBounds (hQ : CompactQuotientCriterion)
    (h : ∀ ε : ℝ, 0 < ε → ∃ D C : ℝ, 3 ≤ D ∧ 2 / D ≤ ε ∧ 0 < C ∧
      ∀ M : ℕ, ∃ X : ℕ, M ≤ X ∧ HeightBound D C X) : JAProp := by
  refine JA_of_dense_differences hQ (fun ε hε => ?_)
  obtain ⟨D, C, hD, hDε, hC, hH⟩ := h ε hε
  exact denseDifferences_of_heightBounds D C hD hDε hC hH

#print axioms cascadeG_nonneg
#print axioms support_last
#print axioms centralMass_pos
#print axioms final_ineq
#print axioms dense_step
#print axioms denseDifferences_of_heightBounds
#print axioms JA_of_heightBounds

end JAFinal
end LeanCheck
