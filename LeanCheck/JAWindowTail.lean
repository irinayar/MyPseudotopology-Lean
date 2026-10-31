import Mathlib
import LeanCheck.JAWindowQ

/-!
# The window kernel (component 11), stage 3: the tail bound by second differences

For the window `w_Q` on `ZMod Q` of `JAWindowQ` and `κ_Q(r) = |Ŵ(r)|^2 / (∑ w)^2`, we show (`D ≥ 3`, `Q ≥ 25 D`,
`u ≥ 1`, `r̃` the balanced representative of `r`):

* `phi_second_diff`: the profile `φ(s) = (max 0 (1 - s^2))^2` has second differences `|φ(s+a)+φ(s-a)-2φ(s)| ≤ 32 a^2`;
* `sd_bound`, `sum_sd_le`: `|w_Q(x+1)+w_Q(x-1)-2w_Q(x)| ≤ 32 (D/Q)^2` and `∑_x |Δ^2 w_Q(x)| ≤ 96 D / Q`
  (the support of `Δ^2 w_Q` has at most `3Q/D` points, and the wrap-around at `±Q/2` is harmless, `wQ_shift`);
* `Fq_d2`: `\widehat{Δ^2 w}(r) = (e(-r) + e(r) - 2) Ŵ(r)`, and `cos_gap`: `2 - 2cos(2π r̃/Q) ≥ 16 r̃^2/Q^2`;
* `Fq_bound`: `|Ŵ(r)| ≤ 6 D Q / r̃^2` for `r ≠ 0`;
* `kappa_le`: `κ_Q(r) ≤ 37 D^4 / r̃^4`;
* `tail_bound`: `∑_{|r̃| > u} κ_Q(r) ≤ 25 D^4 / u^3`.
-/

namespace LeanCheck
namespace JAWindowTail

open Finset JAWindow JARandom JAWindowQ Real

/-! ### The profile and its second differences -/

/-- The profile `φ(s) = (max 0 (1 - s^2))^2`, so that `w_D(t) = φ(D t)`. -/
noncomputable def phi (s : ℝ) : ℝ := (max 0 (1 - s ^ 2)) ^ 2

lemma phi_nonneg (s : ℝ) : 0 ≤ phi s := sq_nonneg _

lemma wD_eq_phi (D t : ℝ) : wD D t = phi (D * t) := by
  unfold wD phi
  rw [mul_pow]

lemma phi_of_le {t : ℝ} (h : |t| ≤ 1) : phi t = (1 - t ^ 2) ^ 2 := by
  unfold phi
  have := abs_le.mp h
  rw [max_eq_right (by nlinarith)]

lemma phi_of_gt {t : ℝ} (h : 1 < |t|) : phi t = 0 := by
  unfold phi
  have h1 : 1 < t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  rw [max_eq_left (by linarith)]
  simp

lemma phi_le_of_far {a : ℝ} (ha : 0 ≤ a) (t t' : ℝ) (hd : |t - t'| ≤ 2 * a) (ht' : 1 < |t'|) :
    phi t ≤ 16 * a ^ 2 := by
  by_cases ht : |t| ≤ 1
  · rw [phi_of_le ht]
    have h0 : 0 ≤ |t| := abs_nonneg t
    have h1 : 1 - |t| ≤ 2 * a := by
      have := abs_sub_abs_le_abs_sub t' t
      rw [abs_sub_comm] at this
      linarith
    have h2 : 1 - t ^ 2 ≤ 4 * a := by
      nlinarith [sq_abs t, mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℝ) ≤ 1 + |t|)]
    have h3 : 0 ≤ 1 - t ^ 2 := by nlinarith [sq_abs t]
    calc (1 - t ^ 2) ^ 2 ≤ (4 * a) ^ 2 := pow_le_pow_left₀ h3 h2 2
      _ = 16 * a ^ 2 := by ring
  · rw [phi_of_gt (not_le.mp ht)]
    positivity

/-- Second differences of the profile are `O(a^2)`. -/
theorem phi_second_diff (s a : ℝ) (ha : 0 ≤ a) :
    |phi (s + a) + phi (s - a) - 2 * phi s| ≤ 32 * a ^ 2 := by
  by_cases hall : |s + a| ≤ 1 ∧ |s| ≤ 1 ∧ |s - a| ≤ 1
  · obtain ⟨h1, h2, h3⟩ := hall
    rw [phi_of_le h1, phi_of_le h2, phi_of_le h3]
    have hs : s ^ 2 ≤ 1 := by nlinarith [abs_le.mp h2]
    have ha1 : a ≤ 1 := by linarith [abs_le.mp h1, abs_le.mp h3]
    have ha2 : a ^ 2 ≤ 1 := by nlinarith
    have key : (1 - (s + a) ^ 2) ^ 2 + (1 - (s - a) ^ 2) ^ 2 - 2 * (1 - s ^ 2) ^ 2 =
        a ^ 2 * (12 * s ^ 2 + 2 * a ^ 2 - 4) := by ring
    rw [key, abs_le]
    constructor <;>
      nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 hs), mul_nonneg (sq_nonneg a) (sub_nonneg.2 ha2),
        sq_nonneg a, mul_nonneg (sq_nonneg a) (sq_nonneg s), mul_nonneg (sq_nonneg a) (sq_nonneg a)]
  · have hout : 1 < |s + a| ∨ 1 < |s| ∨ 1 < |s - a| := by
      by_contra hh
      push Not at hh
      exact hall ⟨hh.1, hh.2.1, hh.2.2⟩
    have key : ∀ t t' : ℝ, |t - t'| ≤ 2 * a → 1 < |t'| → phi t ≤ 16 * a ^ 2 :=
      fun t t' hd ht' => phi_le_of_far ha t t' hd ht'
    rcases hout with h | h | h <;>
    · have e1 := key (s + a) _ (by rw [abs_le]; constructor <;> linarith) h
      have e2 := key s _ (by rw [abs_le]; constructor <;> linarith) h
      have e3 := key (s - a) _ (by rw [abs_le]; constructor <;> linarith) h
      have n1 := phi_nonneg (s + a)
      have n2 := phi_nonneg s
      have n3 := phi_nonneg (s - a)
      rw [abs_le]
      constructor <;> linarith

/-! ### Shifting the balanced representative on `ZMod Q` -/

section zmod

variable {Q : ℕ} [NeZero Q]

lemma far_zero (D : ℝ) (hD : 3 ≤ D) (hQ6 : 6 ≤ Q) (m : ℤ) (hm : (Q : ℤ) - 2 ≤ 2 * |m|) :
    wD D ((m : ℝ) / Q) = 0 := by
  have hD0 : 0 < D := by linarith
  have hQr : (6 : ℝ) ≤ Q := by exact_mod_cast hQ6
  have hmr : (Q : ℝ) - 2 ≤ 2 * |(m : ℝ)| := by exact_mod_cast hm
  apply wD_zero D hD0
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < Q), le_div_iff₀ (by linarith)]
  have h1 : 1 / D ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hD
  have h2 : 1 / D * Q ≤ 1 / 3 * Q := mul_le_mul_of_nonneg_right h1 (by linarith)
  linarith

/-- Adding `c ∈ {-1, 0, 1}` to `x` shifts the balanced representative by `c`; at the wrap-around
point `±Q/2` both window values vanish. -/
lemma wQ_shift (D : ℝ) (hD : 3 ≤ D) (hQ : 25 * D ≤ Q) (x : ZMod Q) (c : ℤ) (hc : |c| ≤ 1) :
    wQ D Q (x + (c : ZMod Q)) = wD D (((x.valMinAbs + c : ℤ) : ℝ) / Q) := by
  have hQ75 : (75 : ℝ) ≤ Q := by linarith
  have hQn : 75 ≤ Q := by exact_mod_cast hQ75
  have hQz : (75 : ℤ) ≤ Q := by exact_mod_cast hQn
  have hc' := abs_le.mp hc
  set y := (x + (c : ZMod Q)).valMinAbs with hy
  have hyc : ((y : ℤ) : ZMod Q) = x + c := ZMod.coe_valMinAbs _
  have hxc : ((x.valMinAbs : ℤ) : ZMod Q) = x := ZMod.coe_valMinAbs x
  have hdvd : (Q : ℤ) ∣ (x.valMinAbs + c) - y :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub y (x.valMinAbs + c) Q).mp (by rw [hyc, Int.cast_add, hxc])
  obtain ⟨k, hk⟩ := hdvd
  have b1 := ZMod.valMinAbs_mem_Ioc (x + (c : ZMod Q))
  have b2 := ZMod.valMinAbs_mem_Ioc x
  simp only [Set.mem_Ioc] at b1 b2
  rw [← hy] at b1
  have hk3 : k = 0 ∨ k = 1 ∨ k = -1 := by
    have h1 : k ≤ 1 := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ Q) (by linarith : (0 : ℤ) ≤ k - 2)]
    have h2 : -1 ≤ k := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ Q) (by linarith : (0 : ℤ) ≤ -2 - k)]
    omega
  unfold wQ
  rcases hk3 with h0 | h1 | h1
  · subst h0
    have hye : y = x.valMinAbs + c := by linarith
    have hye2 : (x + (c : ZMod Q)).valMinAbs = x.valMinAbs + c := hye
    rw [hye2]
  · subst h1
    have e1 : (Q : ℤ) - 2 ≤ 2 * |y| := by
      have := neg_abs_le y
      linarith
    have e2 : (Q : ℤ) - 2 ≤ 2 * |x.valMinAbs + c| := by
      have := le_abs_self (x.valMinAbs + c)
      linarith
    rw [far_zero D hD (by omega) y e1, far_zero D hD (by omega) _ e2]
  · subst h1
    have e1 : (Q : ℤ) - 2 ≤ 2 * |y| := by
      have := le_abs_self y
      linarith
    have e2 : (Q : ℤ) - 2 ≤ 2 * |x.valMinAbs + c| := by
      have := neg_le_abs (x.valMinAbs + c)
      linarith
    rw [far_zero D hD (by omega) y e1, far_zero D hD (by omega) _ e2]

lemma wQ_succ (D : ℝ) (hD : 3 ≤ D) (hQ : 25 * D ≤ Q) (x : ZMod Q) :
    wQ D Q (x + 1) = wD D (((x.valMinAbs : ℝ) + 1) / Q) := by
  have h := wQ_shift D hD hQ x 1 (by simp)
  simp only [Int.cast_one] at h
  exact_mod_cast h

lemma wQ_pred (D : ℝ) (hD : 3 ≤ D) (hQ : 25 * D ≤ Q) (x : ZMod Q) :
    wQ D Q (x - 1) = wD D (((x.valMinAbs : ℝ) - 1) / Q) := by
  have h := wQ_shift D hD hQ x (-1) (by simp)
  simp only [Int.cast_neg, Int.cast_one, ← sub_eq_add_neg] at h
  exact_mod_cast h

/-- **Pointwise second difference** of the window on `ZMod Q`. -/
theorem sd_bound (D : ℝ) (hD : 3 ≤ D) (hQ : 25 * D ≤ Q) (x : ZMod Q) :
    |wQ D Q (x + 1) + wQ D Q (x - 1) - 2 * wQ D Q x| ≤ 32 * (D / Q) ^ 2 := by
  have hD0 : 0 < D := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have e0 : wQ D Q x = phi (D * ((x.valMinAbs : ℝ) / Q)) := by
    unfold wQ; rw [wD_eq_phi]
  have e1 : wQ D Q (x + 1) = phi (D * ((x.valMinAbs : ℝ) / Q) + D / Q) := by
    rw [wQ_succ D hD hQ x, wD_eq_phi]; congr 1; ring
  have e2 : wQ D Q (x - 1) = phi (D * ((x.valMinAbs : ℝ) / Q) - D / Q) := by
    rw [wQ_pred D hD hQ x, wD_eq_phi]; congr 1; ring
  rw [e0, e1, e2]
  exact phi_second_diff _ _ (div_nonneg hD0.le hQ0.le)

lemma wD_far (D : ℝ) (hD : 0 < D) (m : ℝ) (hm : (Q : ℝ) / D ≤ |m|) : wD D (m / Q) = 0 := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  apply wD_zero D hD
  rw [abs_div, abs_of_pos hQ0, le_div_iff₀ hQ0]
  have : 1 / D * Q = Q / D := by ring
  linarith

lemma sd_zero (D : ℝ) (hD : 3 ≤ D) (hQ : 25 * D ≤ Q) (x : ZMod Q)
    (h : (Q : ℝ) / D + 1 ≤ |(x.valMinAbs : ℝ)|) :
    wQ D Q (x + 1) + wQ D Q (x - 1) - 2 * wQ D Q x = 0 := by
  have hD0 : 0 < D := by linarith
  have hx1 : (Q : ℝ) / D ≤ |(x.valMinAbs : ℝ) + 1| := by
    have := le_abs_self ((x.valMinAbs : ℝ) + 1)
    have := neg_le_abs ((x.valMinAbs : ℝ) + 1)
    rcases abs_cases (x.valMinAbs : ℝ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hx2 : (Q : ℝ) / D ≤ |(x.valMinAbs : ℝ) - 1| := by
    have := le_abs_self ((x.valMinAbs : ℝ) - 1)
    have := neg_le_abs ((x.valMinAbs : ℝ) - 1)
    rcases abs_cases (x.valMinAbs : ℝ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hx0 : (Q : ℝ) / D ≤ |(x.valMinAbs : ℝ)| := by linarith
  rw [wQ_succ D hD hQ x, wQ_pred D hD hQ x]
  unfold wQ
  rw [wD_far D hD0 _ hx1, wD_far D hD0 _ hx2, wD_far D hD0 _ hx0]
  ring

/-- **Total second difference**: `∑_x |Δ^2 w_Q(x)| ≤ 96 D / Q`. -/
theorem sum_sd_le (D : ℝ) (hD : 3 ≤ D) (hQ : 25 * D ≤ Q) :
    ∑ x : ZMod Q, |wQ D Q (x + 1) + wQ D Q (x - 1) - 2 * wQ D Q x| ≤ 96 * D / Q := by
  classical
  have hD0 : 0 < D := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  set M : ℤ := ⌊(Q : ℝ) / D + 1⌋ with hM
  have hM0 : 0 ≤ M := Int.floor_nonneg.mpr (by positivity)
  set S := (univ : Finset (ZMod Q)).filter (fun x => |x.valMinAbs| ≤ M) with hS
  have hsupp : ∀ x ∈ (univ : Finset (ZMod Q)),
      |wQ D Q (x + 1) + wQ D Q (x - 1) - 2 * wQ D Q x| ≠ 0 → |x.valMinAbs| ≤ M := by
    intro x _ hne
    by_contra hnot
    apply hne
    have h1 : M < |x.valMinAbs| := not_le.mp hnot
    have h2 : (Q : ℝ) / D + 1 ≤ |(x.valMinAbs : ℝ)| := by
      have h3 : (M : ℝ) + 1 ≤ |(x.valMinAbs : ℝ)| := by
        have : M + 1 ≤ |x.valMinAbs| := Int.add_one_le_iff.mpr h1
        exact_mod_cast this
      have h4 := Int.lt_floor_add_one ((Q : ℝ) / D + 1)
      rw [← hM] at h4
      linarith
    rw [sd_zero D hD hQ x h2, abs_zero]
  have hcard : (S.card : ℝ) ≤ 3 * ((Q : ℝ) / D) := by
    have h1 : S.card ≤ (Finset.Icc (-M) M).card := by
      apply Finset.card_le_card_of_injOn (fun x : ZMod Q => x.valMinAbs)
      · intro x hx
        have := (Finset.mem_filter.mp hx).2
        exact Finset.mem_Icc.mpr (abs_le.mp this)
      · intro a _ b _ hab
        exact ZMod.injective_valMinAbs hab
    have h2 : ((Finset.Icc (-M) M).card : ℤ) = 2 * M + 1 := by
      rw [Int.card_Icc]; omega
    have h3 : (S.card : ℝ) ≤ 2 * (M : ℝ) + 1 := by
      have : (S.card : ℤ) ≤ 2 * M + 1 := by omega
      exact_mod_cast this
    have h4 : (M : ℝ) ≤ Q / D + 1 := by rw [hM]; exact Int.floor_le _
    have h25 : 25 ≤ (Q : ℝ) / D := by rw [le_div_iff₀ hD0]; linarith
    linarith
  calc ∑ x : ZMod Q, |wQ D Q (x + 1) + wQ D Q (x - 1) - 2 * wQ D Q x|
      = ∑ x ∈ S, |wQ D Q (x + 1) + wQ D Q (x - 1) - 2 * wQ D Q x| :=
        (Finset.sum_filter_of_ne (p := fun x : ZMod Q => |x.valMinAbs| ≤ M) hsupp).symm
    _ ≤ S.card • (32 * (D / Q) ^ 2) :=
        Finset.sum_le_card_nsmul _ _ _ (fun x _ => sd_bound D hD hQ x)
    _ = (S.card : ℝ) * (32 * (D / Q) ^ 2) := by rw [nsmul_eq_mul]
    _ ≤ 3 * ((Q : ℝ) / D) * (32 * (D / Q) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 96 * D / Q := by
        first
        | (field_simp; ring)
        | field_simp

end zmod

/-! ### Fourier side -/

section fourier

variable {Q : ℕ} [NeZero Q]

lemma Fq_shift (w : ZMod Q → ℝ) (c r : ZMod Q) :
    Fq (fun x => w (x + c)) r = ZMod.stdAddChar (-(r * c)) * Fq w r := by
  unfold Fq
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight c) _ _ (fun x => ?_)
  show (w (x + c) : ℂ) * ZMod.stdAddChar (r * x) =
    ZMod.stdAddChar (-(r * c)) * ((w (x + c) : ℂ) * ZMod.stdAddChar (r * (x + c)))
  rw [mul_add, AddChar.map_add_eq_mul]
  have h : ZMod.stdAddChar (-(r * c)) * ZMod.stdAddChar (r * c) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc (w (x + c) : ℂ) * ZMod.stdAddChar (r * x)
      = (w (x + c) : ℂ) * ZMod.stdAddChar (r * x) *
          (ZMod.stdAddChar (-(r * c)) * ZMod.stdAddChar (r * c)) := by rw [h, mul_one]
    _ = _ := by ring

lemma Fq_lin (a b c : ZMod Q → ℝ) (r : ZMod Q) :
    Fq (fun x => a x + b x - 2 * c x) r = Fq a r + Fq b r - 2 * Fq c r := by
  unfold Fq
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  push_cast
  ring

/-- The Fourier coefficient of the second difference. -/
lemma Fq_d2 (w : ZMod Q → ℝ) (r : ZMod Q) :
    Fq (fun x => w (x + 1) + w (x - 1) - 2 * w x) r =
      (ZMod.stdAddChar (-r) + ZMod.stdAddChar r - 2) * Fq w r := by
  have h := Fq_lin (fun x => w (x + 1)) (fun x => w (x - 1)) w r
  refine h.trans ?_
  have e : (fun x : ZMod Q => w (x - 1)) = (fun x => w (x + (-1))) := by
    funext x; rw [sub_eq_add_neg]
  rw [e, Fq_shift w 1 r, Fq_shift w (-1) r]
  simp only [mul_one, mul_neg, neg_neg]
  ring

lemma norm_Fq_le (a : ZMod Q → ℝ) (r : ZMod Q) : ‖Fq a r‖ ≤ ∑ x, |a x| := by
  unfold Fq
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [norm_mul, AddChar.norm_apply, mul_one, Complex.norm_real, Real.norm_eq_abs]

lemma psi_pair (r : ZMod Q) :
    ZMod.stdAddChar (-r) + ZMod.stdAddChar r - 2 =
      ((2 * Real.cos (2 * π * (r.valMinAbs : ℝ) / Q) - 2 : ℝ) : ℂ) := by
  have hr : ((r.valMinAbs : ℤ) : ZMod Q) = r := ZMod.coe_valMinAbs r
  have h1 : ZMod.stdAddChar r =
      Complex.exp (((2 * π * (r.valMinAbs : ℝ) / Q : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [← hr]
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  have h2 : (ZMod.stdAddChar r).re = Real.cos (2 * π * (r.valMinAbs : ℝ) / Q) := by
    rw [h1]; exact Complex.exp_ofReal_mul_I_re _
  rw [AddChar.map_neg_eq_conj, add_comm (starRingEnd ℂ _), Complex.add_conj, h2]
  push_cast
  ring

lemma cos_gap (m : ℤ) (hm : 2 * |m| ≤ (Q : ℤ)) :
    16 * (m : ℝ) ^ 2 / (Q : ℝ) ^ 2 ≤ 2 - 2 * Real.cos (2 * π * (m : ℝ) / Q) := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hm' : 2 * |(m : ℝ)| ≤ Q := by exact_mod_cast hm
  have key : (2 * |(m : ℝ)| / Q) ^ 2 ≤ (Real.sin (π * m / Q)) ^ 2 := by
    have hx0 : 0 ≤ π * |(m : ℝ)| / Q := by positivity
    have hx1 : π * |(m : ℝ)| / Q ≤ π / 2 := by
      rw [div_le_iff₀ hQ]; nlinarith [Real.pi_pos]
    have h := Real.mul_le_sin hx0 hx1
    have e : 2 / π * (π * |(m : ℝ)| / Q) = 2 * |(m : ℝ)| / Q := by field_simp
    rw [e] at h
    have hsq : (Real.sin (π * m / Q)) ^ 2 = (Real.sin (π * |(m : ℝ)| / Q)) ^ 2 := by
      rcases abs_cases (m : ℝ) with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]
      · rw [h1]
        have : π * (-(m : ℝ)) / Q = -(π * m / Q) := by ring
        rw [this, Real.sin_neg, neg_sq]
    rw [hsq]
    exact pow_le_pow_left₀ (by positivity) h 2
  have e2 : (2 * |(m : ℝ)| / Q) ^ 2 = 4 * (m : ℝ) ^ 2 / (Q : ℝ) ^ 2 := by
    rw [div_pow, mul_pow, sq_abs]; ring
  rw [e2] at key
  have e3 : 2 * π * (m : ℝ) / Q = 2 * (π * m / Q) := by ring
  rw [e3, Real.cos_two_mul]
  have := Real.sin_sq_add_cos_sq (π * m / Q)
  have e4 : 16 * (m : ℝ) ^ 2 / (Q : ℝ) ^ 2 = 4 * (4 * (m : ℝ) ^ 2 / (Q : ℝ) ^ 2) := by ring
  rw [e4]
  nlinarith [key, this]

/-- **Fourier decay by second differences**: `|Ŵ(r)| ≤ 6 D Q / r̃^2` for `r ≠ 0`. -/
theorem Fq_bound (D : ℝ) (hD : 3 ≤ D) (hQ : 25 * D ≤ Q) (r : ZMod Q) (hr : r ≠ 0) :
    ‖Fq (wQ D Q) r‖ ≤ 6 * D * Q / ((r.valMinAbs : ℝ)) ^ 2 := by
  have hD0 : 0 < D := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hm0 : r.valMinAbs ≠ 0 := by
    intro h0
    apply hr
    rw [← ZMod.coe_valMinAbs r, h0]
    simp
  have hm0' : (r.valMinAbs : ℝ) ≠ 0 := by exact_mod_cast hm0
  have hm2 : 2 * |r.valMinAbs| ≤ (Q : ℤ) := by
    have b := ZMod.valMinAbs_mem_Ioc r
    simp only [Set.mem_Ioc] at b
    rcases abs_cases r.valMinAbs with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [b.1, b.2]
  have h1 := Fq_d2 (wQ D Q) r
  have h2 : ‖Fq (fun x => wQ D Q (x + 1) + wQ D Q (x - 1) - 2 * wQ D Q x) r‖ ≤ 96 * D / Q :=
    (norm_Fq_le _ r).trans (sum_sd_le D hD hQ)
  rw [h1, psi_pair, norm_mul, Complex.norm_real, Real.norm_eq_abs] at h2
  have hcos : 2 * Real.cos (2 * π * (r.valMinAbs : ℝ) / Q) - 2 ≤ 0 := by
    linarith [Real.cos_le_one (2 * π * (r.valMinAbs : ℝ) / Q)]
  rw [abs_of_nonpos hcos] at h2
  have hg := cos_gap (Q := Q) r.valMinAbs hm2
  have h3 : 16 * (r.valMinAbs : ℝ) ^ 2 / (Q : ℝ) ^ 2 * ‖Fq (wQ D Q) r‖ ≤ 96 * D / Q := by
    refine le_trans ?_ h2
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    linarith
  have hmsq : 0 < (r.valMinAbs : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hmsq]
  calc ‖Fq (wQ D Q) r‖ * (r.valMinAbs : ℝ) ^ 2
      = ((Q : ℝ) ^ 2 / 16) * (16 * (r.valMinAbs : ℝ) ^ 2 / (Q : ℝ) ^ 2 * ‖Fq (wQ D Q) r‖) := by
        field_simp
    _ ≤ ((Q : ℝ) ^ 2 / 16) * (96 * D / Q) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 6 * D * Q := by field_simp; ring

lemma sum_ge (D : ℝ) (hD : 3 ≤ D) (hQ : 25 * D ≤ Q) :
    74 * Q / (75 * D) ≤ ∑ x : ZMod Q, wQ D Q x := by
  have hD0 : 0 < D := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hS1 := sum_wQ (Q := Q) D hD
  have h2Q : 2 / (Q : ℝ) ≤ 2 / (25 * D) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hQ
  have ha : 74 / (75 * D) ≤ (∑ x : ZMod Q, wQ D Q x) / Q := by
    have := (abs_le.mp hS1).1
    have e : 16 / (15 * D) - 2 / (25 * D) = 74 / (75 * D) := by field_simp; norm_num
    linarith
  have := (le_div_iff₀ hQ0).mp ha
  calc 74 * (Q : ℝ) / (75 * D) = 74 / (75 * D) * Q := by ring
    _ ≤ _ := this

/-- **The normalized spectral weight**: `κ_Q(r) ≤ 37 D^4 / r̃^4` for `r ≠ 0`. -/
theorem kappa_le (D : ℝ) (hD : 3 ≤ D) (hQ : 25 * D ≤ Q) (r : ZMod Q) (hr : r ≠ 0) :
    ‖Fq (wQ D Q) r‖ ^ 2 / (∑ x, wQ D Q x) ^ 2 ≤ 37 * D ^ 4 / ((r.valMinAbs : ℝ)) ^ 4 := by
  have hD0 : 0 < D := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hm0 : r.valMinAbs ≠ 0 := by
    intro h0
    apply hr
    rw [← ZMod.coe_valMinAbs r, h0]
    simp
  have hm0' : (r.valMinAbs : ℝ) ≠ 0 := by exact_mod_cast hm0
  have hF := Fq_bound D hD hQ r hr
  have hS := sum_ge D hD hQ
  have hS0 : 0 < 74 * (Q : ℝ) / (75 * D) := by positivity
  calc ‖Fq (wQ D Q) r‖ ^ 2 / (∑ x, wQ D Q x) ^ 2
      ≤ (6 * D * Q / ((r.valMinAbs : ℝ)) ^ 2) ^ 2 / (74 * (Q : ℝ) / (75 * D)) ^ 2 :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hF 2) (by positivity)
          (pow_le_pow_left₀ hS0.le hS 2)
    _ = (36 * 75 ^ 2 / 74 ^ 2) * (D ^ 4 / (r.valMinAbs : ℝ) ^ 4) := by
        field_simp
        norm_num
    _ ≤ 37 * (D ^ 4 / (r.valMinAbs : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = 37 * D ^ 4 / (r.valMinAbs : ℝ) ^ 4 := by ring

end fourier

/-! ### Summing the tail -/

lemma inv4_aux (u : ℕ) (hu : 1 ≤ u) :
    ∀ M : ℕ, u ≤ M →
      ∑ k ∈ Finset.Ioc u M, (1 : ℝ) / (k : ℝ) ^ 4 ≤ (1 / 3) * (1 / (u : ℝ) ^ 3 - 1 / (M : ℝ) ^ 3) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top hM]
    have hMpos : (1 : ℝ) ≤ M := by exact_mod_cast le_trans hu hM
    have step : (1 : ℝ) / ((M + 1 : ℕ) : ℝ) ^ 4 ≤
        (1 / 3) * (1 / (M : ℝ) ^ 3 - 1 / ((M + 1 : ℕ) : ℝ) ^ 3) := by
      push_cast
      set m : ℝ := (M : ℝ) with hm
      have hm0 : 0 < m := by linarith
      rw [← sub_nonneg]
      have : 1 / 3 * (1 / m ^ 3 - 1 / (m + 1) ^ 3) - 1 / (m + 1) ^ 4 =
          (6 * m ^ 2 + 4 * m + 1) / (3 * m ^ 3 * (m + 1) ^ 4) := by
        field_simp; ring
      rw [this]; positivity
    linarith

lemma inv4_tail (u : ℕ) (hu : 1 ≤ u) (M : ℕ) :
    ∑ k ∈ Finset.Ioc u M, (1 : ℝ) / (k : ℝ) ^ 4 ≤ 1 / (3 * (u : ℝ) ^ 3) := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  by_cases h : u ≤ M
  · refine (inv4_aux u hu M h).trans ?_
    have : 0 ≤ 1 / (M : ℝ) ^ 3 := by positivity
    have e : 1 / (3 * (u : ℝ) ^ 3) = 1 / 3 * (1 / (u : ℝ) ^ 3) := by field_simp
    rw [e]
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity

lemma G_eq (m : ℤ) : (1 : ℝ) / ((m.natAbs : ℕ) : ℝ) ^ 4 = 1 / (m : ℝ) ^ 4 := by
  have h : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    simp
  rw [h, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]

variable {Q : ℕ} [NeZero Q]

/-- **The tail bound**: `∑_{|r̃| > u} κ_Q(r) ≤ A_D u^{-3}` with `A_D = 25 D^4`. -/
theorem tail_bound (D : ℝ) (hD : 3 ≤ D) (hQ : 25 * D ≤ Q) (u : ℕ) (hu : 1 ≤ u) :
    ∑ r ∈ (univ : Finset (ZMod Q)).filter (fun r => (u : ℤ) < |r.valMinAbs|),
        ‖Fq (wQ D Q) r‖ ^ 2 / (∑ x, wQ D Q x) ^ 2 ≤ 25 * D ^ 4 / (u : ℝ) ^ 3 := by
  classical
  have hD0 : 0 < D := by linarith
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  set T := (univ : Finset (ZMod Q)).filter (fun r => (u : ℤ) < |r.valMinAbs|) with hT
  set G : ℕ → ℝ := fun k => 1 / (k : ℝ) ^ 4 with hG
  have hG0 : ∀ k, 0 ≤ G k := fun k => by simp only [hG]; positivity
  have hpt : ∀ r ∈ T, ‖Fq (wQ D Q) r‖ ^ 2 / (∑ x, wQ D Q x) ^ 2 ≤
      37 * D ^ 4 * G r.valMinAbs.natAbs := by
    intro r hr
    have hr' : (u : ℤ) < |r.valMinAbs| := (Finset.mem_filter.mp hr).2
    have hne : r.valMinAbs ≠ 0 := by
      intro h
      rw [h, abs_zero] at hr'
      omega
    have hr0 : r ≠ 0 := by
      intro h0
      apply hne
      rw [h0]
      exact ZMod.valMinAbs_zero _
    have h := kappa_le D hD hQ r hr0
    have e : G r.valMinAbs.natAbs = 1 / (r.valMinAbs : ℝ) ^ 4 := G_eq _
    rw [e]
    calc _ ≤ 37 * D ^ 4 / (r.valMinAbs : ℝ) ^ 4 := h
      _ = 37 * D ^ 4 * (1 / (r.valMinAbs : ℝ) ^ 4) := by ring
  have piece : ∀ (p : ZMod Q → Prop) [DecidablePred p],
      (∀ r r' : ZMod Q, p r → p r' → r.valMinAbs.natAbs = r'.valMinAbs.natAbs → r = r') →
      ∑ r ∈ T.filter p, G r.valMinAbs.natAbs ≤ ∑ k ∈ Finset.Ioc u (Q / 2), G k := by
    intro p _ hinj
    rw [← Finset.sum_image (f := G) (g := fun r : ZMod Q => r.valMinAbs.natAbs) (s := T.filter p)]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hk
        have hr' : (u : ℤ) < |r.valMinAbs| := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
        rw [Int.abs_eq_natAbs] at hr'
        rw [Finset.mem_Ioc]
        exact ⟨by exact_mod_cast hr', ZMod.natAbs_valMinAbs_le r⟩
      · intro k _ _
        exact hG0 k
    · intro a ha b hb hab
      exact hinj a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  have hfib : ∑ r ∈ T, G r.valMinAbs.natAbs ≤ 2 * ∑ k ∈ Finset.Ioc u (Q / 2), G k := by
    rw [← Finset.sum_filter_add_sum_filter_not T (fun r : ZMod Q => 0 ≤ r.valMinAbs)]
    have h1 := piece (fun r : ZMod Q => 0 ≤ r.valMinAbs) (by
      intro r r' h h' e
      apply ZMod.injective_valMinAbs
      omega)
    have h2 := piece (fun r : ZMod Q => ¬ 0 ≤ r.valMinAbs) (by
      intro r r' h h' e
      apply ZMod.injective_valMinAbs
      omega)
    linarith
  have hsum : ∑ k ∈ Finset.Ioc u (Q / 2), G k ≤ 1 / (3 * (u : ℝ) ^ 3) := inv4_tail u hu (Q / 2)
  have h37 : (0 : ℝ) ≤ 37 * D ^ 4 := by positivity
  calc ∑ r ∈ T, ‖Fq (wQ D Q) r‖ ^ 2 / (∑ x, wQ D Q x) ^ 2
      ≤ ∑ r ∈ T, 37 * D ^ 4 * G r.valMinAbs.natAbs := Finset.sum_le_sum hpt
    _ = 37 * D ^ 4 * ∑ r ∈ T, G r.valMinAbs.natAbs := by rw [← Finset.mul_sum]
    _ ≤ 37 * D ^ 4 * (2 * (1 / (3 * (u : ℝ) ^ 3))) :=
        mul_le_mul_of_nonneg_left (by linarith) h37
    _ = (74 / 3) * D ^ 4 / (u : ℝ) ^ 3 := by field_simp; norm_num
    _ ≤ 25 * D ^ 4 / (u : ℝ) ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [pow_nonneg hD0.le 4]

#print axioms phi_second_diff
#print axioms wQ_shift
#print axioms sd_bound
#print axioms sum_sd_le
#print axioms Fq_d2
#print axioms cos_gap
#print axioms Fq_bound
#print axioms kappa_le
#print axioms tail_bound

end JAWindowTail
end LeanCheck
