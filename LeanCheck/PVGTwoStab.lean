import Mathlib

/-!
# Nearly additive functions on boxes of integer points (Lean check)

Used in `PVGTwoDescribe`.

* `KaltonRoberts` : the statement of Theorem 4.1 of Kalton and Roberts (Trans. AMS 278, 1983) for finitely many atoms,
  with the constant `45`. It is NOT proved here; it is a hypothesis of the results that use it.
* `lift` : a function with values in `ℝ/ℤ` that is additive up to `δ < 1/8` on a box of natural points has a real lift
  with the same property;
* `real_box` : (using `KaltonRoberts`) a real function additive up to `δ` on the box `a ≤ 2R`, where every `R k` is `0`
  or a power of `2`, is within `93 δ` of a linear function on `a ≤ R`;
* `signed_box`, `inf_box` : the same for `ℝ/ℤ`-valued functions of integer points, with finitely or infinitely many
  coordinates, with the bound `188 δ`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Stab

/-- Kalton–Roberts, Theorem 4.1, for the algebra of all subsets of a finite set. -/
def KaltonRoberts : Prop :=
  ∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (Δ : ℝ),
    (∀ A B : Finset (Fin n), Disjoint A B → |f (A ∪ B) - f A - f B| ≤ Δ) →
      ∃ μ : Fin n → ℝ, ∀ A : Finset (Fin n), |f A - ∑ k ∈ A, μ k| ≤ 45 * Δ

abbrev T := AddCircle (1 : ℝ)

lemma norm_coe (u : ℝ) : ‖(u : T)‖ = |u - round u| := by
  rw [AddCircle.norm_eq]; simp

/-! ## Lifting -/

section Lift
variable {n : ℕ} (B : Fin n → ℕ) (r : (Fin n → ℕ) → ℝ)

def unit (j : Fin n) : Fin n → ℕ := Pi.single j 1

noncomputable def D (a b : Fin n → ℕ) : ℤ := round (r (a + b) - r a - r b)

def supp (a : Fin n → ℕ) : Finset (Fin n) := Finset.univ.filter fun k => a k ≠ 0

lemma supp_nonempty {a : Fin n → ℕ} (h : a ≠ 0) : (supp a).Nonempty := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 h
  exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using hk⟩⟩

lemma pred_add {a : Fin n → ℕ} {m : Fin n} (h : a m ≠ 0) : (a - unit m) + unit m = a := by
  funext k
  simp only [unit, Pi.add_apply, Pi.sub_apply]
  by_cases hk : k = m
  · subst hk; rw [Pi.single_eq_same]; omega
  · rw [Pi.single_eq_of_ne hk]; omega

lemma sum_unit (j : Fin n) : ∑ k, unit j k = 1 := by
  unfold unit
  rw [Finset.sum_pi_single' j (1 : ℕ) Finset.univ]
  simp

lemma sum_pred {a : Fin n → ℕ} {m : Fin n} (h : a m ≠ 0) : ∑ k, (a - unit m) k + 1 = ∑ k, a k := by
  conv_rhs => rw [← pred_add h]
  simp only [Pi.add_apply, Finset.sum_add_distrib, sum_unit]

noncomputable def hl (a : Fin n → ℕ) : ℤ :=
  if h : a = 0 then 0
  else
    let m := (supp a).max' (supp_nonempty h)
    hl (a - unit m) + D r (a - unit m) (unit m)
  termination_by ∑ k, a k
  decreasing_by
    have hm := (Finset.mem_filter.1 ((supp a).max'_mem (supp_nonempty h))).2
    have := sum_pred hm
    omega

lemma hl_zero : hl r (0 : Fin n → ℕ) = 0 := by rw [hl]; simp

lemma hl_step (a : Fin n → ℕ) (m : Fin n) (hm : a m ≠ 0) (htop : ∀ k, a k ≠ 0 → k ≤ m) :
    hl r a = hl r (a - unit m) + D r (a - unit m) (unit m) := by
  have h : a ≠ 0 := fun h => hm (by rw [h]; rfl)
  have hmax : (supp a).max' (supp_nonempty h) = m := by
    refine le_antisymm (Finset.max'_le _ _ _ fun k hk => htop k (Finset.mem_filter.1 hk).2) ?_
    exact Finset.le_max' (supp a) m (Finset.mem_filter.2 ⟨Finset.mem_univ _, hm⟩)
  conv_lhs => rw [hl]
  rw [dif_neg h]
  simp only [hmax]

variable (δ : ℝ) (hδ : δ < 1 / 8)
  (hr : ∀ a b : Fin n → ℕ, a + b ≤ B → |r (a + b) - r a - r b - D r a b| ≤ δ) (h0 : |r 0| < 1 / 2)

include h0 in
lemma D_zero (a : Fin n → ℕ) : D r a 0 = 0 := by
  unfold D
  rw [add_zero, sub_self, zero_sub, round_eq_zero_iff]
  obtain ⟨h1, h2⟩ := abs_lt.1 h0
  exact ⟨by linarith, by linarith⟩

lemma D_comm (a b : Fin n → ℕ) : D r a b = D r b a := by
  unfold D; rw [add_comm a b]; congr 1; ring

include hδ hr in
lemma D_cocycle (a b c : Fin n → ℕ) (h : a + b + c ≤ B) :
    D r a b + D r (a + b) c = D r b c + D r a (b + c) := by
  have hab : a + b ≤ B := le_trans le_self_add h
  have hbc : b + c ≤ B := by
    refine le_trans ?_ h
    rw [add_assoc]; exact le_add_self
  have habc : a + (b + c) ≤ B := by rw [← add_assoc]; exact h
  have h1 := abs_le.1 (hr a b hab)
  have h2 := abs_le.1 (hr (a + b) c h)
  have h3 := abs_le.1 (hr b c hbc)
  have h4 := abs_le.1 (hr a (b + c) habc)
  rw [← add_assoc] at h4
  have hlt : |((D r a b + D r (a + b) c - (D r b c + D r a (b + c)) : ℤ) : ℝ)| < 1 := by
    rw [abs_lt]
    push_cast
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  have := Int.abs_lt_one_iff.1 (by exact_mod_cast hlt :
    |D r a b + D r (a + b) c - (D r b c + D r a (b + c))| < 1)
  omega

include hδ hr h0 in
lemma D_unit (a : Fin n → ℕ) (j : Fin n) (h : a + unit j ≤ B) : D r a (unit j) = hl r (a + unit j) - hl r a := by
  induction hN : ∑ k, a k using Nat.strong_induction_on generalizing a j with
  | _ N ih =>
    have hj1 : (a + unit j) j ≠ 0 := by simp [unit]
    by_cases htop : ∀ k, a k ≠ 0 → k ≤ j
    · have htop' : ∀ k, (a + unit j) k ≠ 0 → k ≤ j := by
        intro k hk
        by_cases hkj : k = j
        · exact hkj.le
        · refine htop k ?_
          simpa [unit, Pi.single_eq_of_ne hkj] using hk
      have e1 : (a + unit j) - unit j = a := by
        funext k; simp
      rw [hl_step r (a + unit j) j hj1 htop', e1]
      ring
    · push Not at htop
      obtain ⟨k0, hk0, hjk0⟩ := htop
      have ha : a ≠ 0 := fun h => hk0 (by rw [h]; rfl)
      set m := (supp a).max' (supp_nonempty ha) with hm
      have hma : a m ≠ 0 := (Finset.mem_filter.1 ((supp a).max'_mem (supp_nonempty ha))).2
      have hmax : ∀ k, a k ≠ 0 → k ≤ m := fun k hk =>
        Finset.le_max' (supp a) k (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)
      have hjm : j < m := lt_of_lt_of_le hjk0 (hmax k0 hk0)
      set a' := a - unit m with ha'
      have haa : a' + unit m = a := pred_add hma
      have hsum := sum_pred hma
      rw [← ha'] at hsum
      have h3 : a' + unit m + unit j ≤ B := by rw [haa]; exact h
      have h3' : a' + unit j + unit m ≤ B := by rw [add_right_comm]; exact h3
      have haj : a' + unit j ≤ B := le_trans le_self_add h3'
      have c1 := D_cocycle B r δ hδ hr a' (unit m) (unit j) h3
      have c2 := D_cocycle B r δ hδ hr a' (unit j) (unit m) h3'
      rw [haa] at c1
      rw [D_comm r (unit j) (unit m), add_comm (unit j) (unit m)] at c2
      have iha := ih (∑ k, a' k) (by omega) a' j haj rfl
      have e2 : hl r a = hl r a' + D r a' (unit m) := hl_step r a m hma hmax
      have e3 : hl r (a + unit j) = hl r (a' + unit j) + D r (a' + unit j) (unit m) := by
        have hm1 : (a + unit j) m ≠ 0 := by
          simp only [Pi.add_apply]; omega
        have htop' : ∀ k, (a + unit j) k ≠ 0 → k ≤ m := by
          intro k hk
          by_cases hkj : k = j
          · rw [hkj]; exact hjm.le
          · refine hmax k ?_
            simpa [unit, Pi.single_eq_of_ne hkj] using hk
        have e4 : (a + unit j) - unit m = a' + unit j := by
          funext k
          have := congrFun haa k
          simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
          omega
        rw [hl_step r (a + unit j) m hm1 htop', e4]
      omega

include hδ hr h0 in
lemma D_coboundary (a b : Fin n → ℕ) (h : a + b ≤ B) : D r a b = hl r (a + b) - hl r a - hl r b := by
  induction hN : ∑ k, b k using Nat.strong_induction_on generalizing a b with
  | _ N ih =>
    by_cases hb : b = 0
    · subst hb
      rw [add_zero, D_zero r h0, hl_zero]; ring
    · set m := (supp b).max' (supp_nonempty hb) with hm
      have hmb : b m ≠ 0 := (Finset.mem_filter.1 ((supp b).max'_mem (supp_nonempty hb))).2
      have hmax : ∀ k, b k ≠ 0 → k ≤ m := fun k hk =>
        Finset.le_max' (supp b) k (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)
      set b' := b - unit m with hb'
      have hbb : b' + unit m = b := pred_add hmb
      have hsum := sum_pred hmb
      rw [← hb'] at hsum
      have h3 : a + b' + unit m ≤ B := by rw [add_assoc, hbb]; exact h
      have c := D_cocycle B r δ hδ hr a b' (unit m) h3
      rw [hbb] at c
      have i1 := ih (∑ k, b' k) (by omega) a b' (le_trans le_self_add h3) rfl
      have i2 := D_unit B r δ hδ hr h0 (a + b') m h3
      have i3 : D r b' (unit m) = hl r b - hl r b' := by
        rw [hl_step r b m hmb hmax]; ring
      have e : a + b' + unit m = a + b := by rw [add_assoc, hbb]
      rw [e] at i2
      omega

end Lift

/-- A nearly additive `ℝ/ℤ`-valued function on a box of natural points has a nearly additive real lift. -/
theorem lift {n : ℕ} (B : Fin n → ℕ) (F : (Fin n → ℕ) → T) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 8)
    (hF : ∀ a b : Fin n → ℕ, a + b ≤ B → ‖F (a + b) - F a - F b‖ ≤ δ) :
    ∃ f : (Fin n → ℕ) → ℝ, (∀ a, (f a : T) = F a) ∧ ∀ a b : Fin n → ℕ, a + b ≤ B → |f (a + b) - f a - f b| ≤ δ := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  set r : (Fin n → ℕ) → ℝ := fun a => (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (F a) : ℝ) with hr
  have hrF : ∀ a, (r a : T) = F a := fun a => (AddCircle.equivIco (1 : ℝ) (-(1 / 2))).symm_apply_apply (F a)
  have hbound : ∀ a b : Fin n → ℕ, a + b ≤ B → |r (a + b) - r a - r b - D r a b| ≤ δ := by
    intro a b h
    unfold D
    rw [← norm_coe]
    rw [AddCircle.coe_sub, AddCircle.coe_sub, hrF, hrF, hrF]
    exact hF a b h
  have h00 : ‖F 0‖ ≤ δ := by
    have := hF 0 0 (by rw [add_zero]; exact fun k => Nat.zero_le _)
    rwa [add_zero, sub_self, zero_sub, norm_neg] at this
  have h0 : |r 0| < 1 / 2 := by
    have hmem := (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) (F 0)).2
    have hn : ‖(r 0 : T)‖ ≤ δ := by rw [hrF]; exact h00
    refine abs_lt.2 ⟨lt_of_le_of_ne hmem.1 ?_, lt_of_lt_of_le hmem.2 (by norm_num)⟩
    intro h
    have e : r 0 = -(1 / 2) := h.symm
    rw [e, AddCircle.coe_neg, norm_neg] at hn
    have h2 : ‖((1 / 2 : ℝ) : T)‖ = 1 / 2 := by
      rw [AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero |>.2 (by norm_num)]
      norm_num
    rw [h2] at hn
    linarith
  refine ⟨fun a => r a - hl r a, fun a => ?_, fun a b h => ?_⟩
  · rw [AddCircle.coe_sub, hrF]
    have : ((hl r a : ℝ) : T) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨hl r a, by simp⟩
    rw [this, sub_zero]
  · have hD := D_coboundary B r δ hδ hbound h0 a b h
    have h2 := hbound a b h
    have e : r (a + b) - hl r (a + b) - (r a - hl r a) - (r b - hl r b) = r (a + b) - r a - r b - D r a b := by
      rw [hD]; push_cast; ring
    rw [e]; exact h2

/-! ## The box -/

/-- Nearly additive real functions on a box are nearly linear. -/
theorem real_box (hKR : KaltonRoberts) {n : ℕ} (R p : Fin n → ℕ) (hR : ∀ k, R k = 0 ∨ R k = 2 ^ p k)
    (f : (Fin n → ℕ) → ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hf : ∀ a b : Fin n → ℕ, (∀ k, a k + b k ≤ 2 * R k) → |f (a + b) - f a - f b| ≤ δ) :
    ∃ lam : Fin n → ℝ, ∀ d : Fin n → ℕ, (∀ k, d k ≤ R k) → |f d - ∑ k, lam k * d k| ≤ 93 * δ := by
  classical
  set cut : Finset (Fin n) → (Fin n → ℕ) := fun A k => if k ∈ A then R k else 0 with hcut
  have hν : ∀ A C : Finset (Fin n), Disjoint A C → |f (cut (A ∪ C)) - f (cut A) - f (cut C)| ≤ δ := by
    intro A C hAC
    have e : cut (A ∪ C) = cut A + cut C := by
      funext k
      simp only [hcut, Pi.add_apply, Finset.mem_union]
      by_cases h1 : k ∈ A
      · have h2 : k ∉ C := Finset.disjoint_left.1 hAC h1
        simp [h1, h2]
      · by_cases h2 : k ∈ C <;> simp [h1, h2]
    rw [e]
    refine hf _ _ fun k => ?_
    simp only [hcut]
    split_ifs <;> omega
  obtain ⟨μ, hμ⟩ := hKR n (fun A => f (cut A)) δ hν
  set lam : Fin n → ℝ := fun k => if R k = 0 then 0 else μ k / R k with hlam
  set G : (Fin n → ℕ) → ℝ := fun a => f a - ∑ k, lam k * a k with hG
  have hGadd : ∀ a b : Fin n → ℕ, (∀ k, a k + b k ≤ 2 * R k) → |G (a + b) - G a - G b| ≤ δ := by
    intro a b h
    have e : G (a + b) - G a - G b = f (a + b) - f a - f b := by
      simp only [hG, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
      ring
    rw [e]; exact hf a b h
  have hGcut : ∀ A : Finset (Fin n), (∀ k ∈ A, R k ≠ 0) → |G (cut A)| ≤ 45 * δ := by
    intro A hA
    have e : ∑ k, lam k * (cut A k : ℝ) = ∑ k ∈ A, μ k := by
      rw [← Finset.sum_subset (Finset.subset_univ A)]
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hk0 := hA k hk
        have hk1 : (R k : ℝ) ≠ 0 := by exact_mod_cast hk0
        simp only [hlam, hcut, if_neg hk0, if_pos hk]
        exact div_mul_cancel₀ _ hk1
      · intro k _ hk
        simp [hcut, hk]
    simp only [hG, e]
    exact hμ A
  have hG0 : |G 0| ≤ δ := by
    have := hGadd 0 0 (fun k => by simp)
    rwa [add_zero, sub_self, zero_sub, abs_neg] at this
  refine ⟨lam, fun d hd => ?_⟩
  set u : ℕ → (Fin n → ℕ) := fun i k =>
    if R k ≠ 0 ∧ i ≤ p k then 2 ^ i * (d k % 2 ^ (p k - i + 1)) else 0 with hu
  set v : ℕ → (Fin n → ℕ) := fun i k =>
    if R k ≠ 0 ∧ i < p k then 2 ^ i * (d k % 2 ^ (p k - i)) else 0 with hv
  set A : ℕ → Finset (Fin n) := fun i => Finset.univ.filter fun k =>
    R k ≠ 0 ∧ i ≤ p k ∧ 2 ^ (p k - i) ≤ d k % 2 ^ (p k - i + 1) with hA
  have hRp : ∀ k, R k ≠ 0 → R k = 2 ^ p k := fun k h => (hR k).resolve_left h
  have hvv : ∀ i, u (i + 1) = v i + v i := by
    intro i
    funext k
    simp only [hu, hv, Pi.add_apply]
    by_cases h : R k ≠ 0 ∧ i < p k
    · have h' : R k ≠ 0 ∧ i + 1 ≤ p k := ⟨h.1, h.2⟩
      rw [if_pos h', if_pos h]
      have e : p k - (i + 1) + 1 = p k - i := by omega
      rw [e, pow_succ]; ring
    · have h' : ¬ (R k ≠ 0 ∧ i + 1 ≤ p k) := fun h' => h ⟨h'.1, h'.2⟩
      rw [if_neg h', if_neg h]
  have huv : ∀ i, u i = cut (A i) + v i := by
    intro i
    funext k
    simp only [hu, hv, hcut, hA, Pi.add_apply, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : R k ≠ 0 ∧ i ≤ p k
    · rw [if_pos h]
      obtain ⟨h1, h2⟩ := h
      have hsplit : d k % 2 ^ (p k - i + 1) =
          d k % 2 ^ (p k - i) + 2 ^ (p k - i) * (d k / 2 ^ (p k - i) % 2) := by
        rw [pow_succ, Nat.mod_mul]
      have hbit : d k / 2 ^ (p k - i) % 2 < 2 := Nat.mod_lt _ two_pos
      have hlow : d k % 2 ^ (p k - i) < 2 ^ (p k - i) := Nat.mod_lt _ (by positivity)
      have hpow : 2 ^ i * 2 ^ (p k - i) = R k := by
        rw [hRp k h1, ← pow_add]; congr 1; omega
      have hv' : (if R k ≠ 0 ∧ i < p k then 2 ^ i * (d k % 2 ^ (p k - i)) else 0) =
          2 ^ i * (d k % 2 ^ (p k - i)) := by
        by_cases h3 : i < p k
        · rw [if_pos ⟨h1, h3⟩]
        · have e : p k - i = 0 := by omega
          rw [if_neg (fun h => h3 h.2), e]
          simp [Nat.mod_one]
      rw [hv']
      rcases Nat.lt_succ_iff_lt_or_eq.1 hbit with hb | hb
      · have hb0 : d k / 2 ^ (p k - i) % 2 = 0 := by omega
        rw [hb0, mul_zero, add_zero] at hsplit
        have hnot : ¬ (R k ≠ 0 ∧ i ≤ p k ∧ 2 ^ (p k - i) ≤ d k % 2 ^ (p k - i + 1)) := by
          rintro ⟨-, -, h4⟩
          omega
        rw [if_neg hnot, zero_add, hsplit]
      · rw [hb, mul_one] at hsplit
        have hyes : R k ≠ 0 ∧ i ≤ p k ∧ 2 ^ (p k - i) ≤ d k % 2 ^ (p k - i + 1) := ⟨h1, h2, by omega⟩
        rw [if_pos hyes, hsplit, mul_add, hpow, add_comm]
    · rw [if_neg h]
      have h1 : ¬ (R k ≠ 0 ∧ i < p k) := fun h' => h ⟨h'.1, h'.2.le⟩
      have h2 : ¬ (R k ≠ 0 ∧ i ≤ p k ∧ 2 ^ (p k - i) ≤ d k % 2 ^ (p k - i + 1)) := fun h' => h ⟨h'.1, h'.2.1⟩
      rw [if_neg h1, if_neg h2]
  have hubound : ∀ i k, u i k ≤ 2 * R k := by
    intro i k
    simp only [hu]
    split_ifs with h
    · have h1 : d k % 2 ^ (p k - i + 1) < 2 ^ (p k - i + 1) := Nat.mod_lt _ (by positivity)
      have h2 : 2 ^ i * 2 ^ (p k - i + 1) = 2 * R k := by
        rw [hRp k h.1, ← pow_add, ← pow_succ']; congr 1; omega
      rw [← h2]
      exact Nat.mul_le_mul_left _ h1.le
    · exact Nat.zero_le _
  have hstep : ∀ i, |G (u (i + 1))| ≤ 93 * δ → |G (u i)| ≤ 93 * δ := by
    intro i hi
    have hsum1 : ∀ k, cut (A i) k + v i k ≤ 2 * R k := by
      intro k
      have := hubound i k
      rwa [huv i] at this
    have hsum2 : ∀ k, v i k + v i k ≤ 2 * R k := by
      intro k
      have := hubound (i + 1) k
      rwa [hvv i] at this
    have h1 := hGadd _ _ hsum1
    have h2 := hGadd _ _ hsum2
    rw [← huv i] at h1
    rw [← hvv i] at h2
    have h3 := hGcut (A i) fun k hk => (Finset.mem_filter.1 hk).2.1
    have a1 := abs_le.1 h1
    have a2 := abs_le.1 h2
    have a3 := abs_le.1 h3
    have a4 := abs_le.1 hi
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  set top := ∑ k, p k + 1 with htop
  have huTop : u top = 0 := by
    funext k
    have : p k ≤ ∑ j, p j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    simp only [hu, Pi.zero_apply]
    rw [if_neg]
    rintro ⟨-, h⟩
    omega
  have hall : ∀ i, i ≤ top → |G (u i)| ≤ 93 * δ := by
    intro i hi
    induction hi using Nat.decreasingInduction with
    | self => rw [huTop]; linarith
    | of_succ j _ ih => exact hstep j ih
  have hu0 : u 0 = d := by
    funext k
    simp only [hu]
    by_cases h : R k = 0
    · have := hd k
      rw [if_neg (fun h' => h'.1 h)]
      omega
    · rw [if_pos ⟨h, Nat.zero_le _⟩, pow_zero, one_mul, Nat.sub_zero]
      refine Nat.mod_eq_of_lt (lt_of_le_of_lt (hd k) ?_)
      rw [hRp k h, pow_succ]
      have : 0 < 2 ^ p k := by positivity
      omega
  have := hall 0 (Nat.zero_le _)
  rw [hu0] at this
  exact this

/-- The same for `ℝ/ℤ`-valued functions of integer points. -/
theorem signed_box (hKR : KaltonRoberts) {n : ℕ} (R p : Fin n → ℕ) (hR : ∀ k, R k = 0 ∨ R k = 2 ^ p k)
    (F : (Fin n → ℤ) → T) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 8)
    (hF : ∀ a b : Fin n → ℤ, (∀ k, |a k| ≤ 2 * R k) → (∀ k, |b k| ≤ 2 * R k) → (∀ k, |a k + b k| ≤ 2 * R k) →
      ‖F (a + b) - F a - F b‖ ≤ δ) :
    ∃ lam : Fin n → ℝ, ∀ d : Fin n → ℤ, (∀ k, |d k| ≤ R k) →
      ‖F d - ((∑ k, lam k * d k : ℝ) : T)‖ ≤ 188 * δ := by
  set c : (Fin n → ℕ) → (Fin n → ℤ) := fun a k => (a k : ℤ) with hc
  have hcadd : ∀ a b, c (a + b) = c a + c b := fun a b => by
    funext k; simp [hc]
  have hnat : ∀ a b : Fin n → ℕ, (∀ k, a k + b k ≤ 2 * R k) → ‖F (c (a + b)) - F (c a) - F (c b)‖ ≤ δ := by
    intro a b h
    rw [hcadd]
    refine hF _ _ (fun k => ?_) (fun k => ?_) (fun k => ?_)
    all_goals
      have := h k
      simp only [hc]
      rw [abs_of_nonneg (by positivity)]
      omega
  obtain ⟨f, hfF, hfadd⟩ := lift (fun k => 2 * R k) (fun a => F (c a)) δ hδ0 hδ fun a b h => hnat a b h
  obtain ⟨lam, hlam⟩ := real_box hKR R p hR f δ hδ0 fun a b h => hfadd a b h
  refine ⟨lam, fun d hd => ?_⟩
  set dp : Fin n → ℕ := fun k => (d k).toNat with hdp
  set dm : Fin n → ℕ := fun k => (-d k).toNat with hdm
  have hsplit : ∀ k, d k + (dm k : ℤ) = (dp k : ℤ) := by
    intro k; simp only [hdp, hdm]; omega
  have hpm : ∀ k, dp k ≤ R k ∧ dm k ≤ R k := by
    intro k
    have h := abs_le.1 (hd k)
    simp only [hdp, hdm]
    omega
  have hpos : ∀ a : Fin n → ℕ, (∀ k, a k ≤ R k) → ‖F (c a) - ((∑ k, lam k * (a k : ℝ) : ℝ) : T)‖ ≤ 93 * δ := by
    intro a ha
    have h := hlam a ha
    have e : F (c a) - ((∑ k, lam k * (a k : ℝ) : ℝ) : T) = ((f a - ∑ k, lam k * (a k : ℝ) : ℝ) : T) := by
      rw [AddCircle.coe_sub, hfF]
    rw [e, norm_coe]
    exact (round_le _ 0).trans (by simpa using h)
  have hsum : d + c dm = c dp := by
    funext k; exact hsplit k
  have h1 : ‖F (c dp) - F d - F (c dm)‖ ≤ δ := by
    rw [← hsum]
    refine hF d (c dm) (fun k => (hd k).trans (by omega)) (fun k => ?_) (fun k => ?_)
    · have := (hpm k).2
      simp only [hc]
      rw [abs_of_nonneg (by positivity)]
      omega
    · have := (hpm k).1
      have e := hsplit k
      simp only [hc]
      rw [e, abs_of_nonneg (by positivity)]
      omega
  have h2 := hpos dp fun k => (hpm k).1
  have h3 := hpos dm fun k => (hpm k).2
  have e : ((∑ k, lam k * (d k : ℝ) : ℝ) : T) =
      ((∑ k, lam k * (dp k : ℝ) : ℝ) : T) - ((∑ k, lam k * (dm k : ℝ) : ℝ) : T) := by
    rw [← AddCircle.coe_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have h4 : (d k : ℝ) = (dp k : ℝ) - (dm k : ℝ) := by
      have h5 : d k = (dp k : ℤ) - (dm k : ℤ) := by have := hsplit k; omega
      exact_mod_cast h5
    rw [h4]; ring
  have key : F d - ((∑ k, lam k * (d k : ℝ) : ℝ) : T) =
      -(F (c dp) - F d - F (c dm)) + (F (c dp) - ((∑ k, lam k * (dp k : ℝ) : ℝ) : T)) -
        (F (c dm) - ((∑ k, lam k * (dm k : ℝ) : ℝ) : T)) := by
    rw [e]; abel
  rw [key]
  refine (norm_sub_le _ _).trans (le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_)
  rw [norm_neg]
  linarith

/-- Infinitely many coordinates, finitely supported points. -/
theorem inf_box (hKR : KaltonRoberts) (R p : ℕ → ℕ) (hR : ∀ k, R k = 0 ∨ R k = 2 ^ p k)
    (F : (ℕ →₀ ℤ) → T) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 8)
    (hF : ∀ a b : ℕ →₀ ℤ, (∀ k, |a k| ≤ 2 * R k) → (∀ k, |b k| ≤ 2 * R k) → (∀ k, |a k + b k| ≤ 2 * R k) →
      ‖F (a + b) - F a - F b‖ ≤ δ) :
    ∃ lam : ℕ → T, ∀ d : ℕ →₀ ℤ, (∀ k, |d k| ≤ R k) →
      ‖F d - d.sum (fun k z => z • lam k)‖ ≤ 188 * δ := by
  classical
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have fin : ∀ n : ℕ, ∃ lam : ℕ → T, ∀ d : ℕ →₀ ℤ, d.support ⊆ Finset.range n → (∀ k, |d k| ≤ R k) →
      ‖F d - d.sum (fun k z => z • lam k)‖ ≤ 188 * δ := by
    intro n
    set ext : (Fin n → ℤ) → (ℕ →₀ ℤ) := fun a =>
      Finsupp.onFinset (Finset.range n) (fun k => if h : k < n then a ⟨k, h⟩ else 0)
        (fun k hk => by
          refine Finset.mem_range.2 ?_
          by_contra hc
          exact hk (dif_neg hc)) with hext
    have hex : ∀ a k, ext a k = if h : k < n then a ⟨k, h⟩ else 0 := fun a k => rfl
    have hadd : ∀ a b, ext (a + b) = ext a + ext b := by
      intro a b
      ext k
      simp only [Finsupp.add_apply, hex]
      split_ifs <;> simp
    have hbd : ∀ a : Fin n → ℤ, (∀ k : Fin n, |a k| ≤ 2 * R k.val) → ∀ k, |ext a k| ≤ 2 * R k := by
      intro a ha k
      rw [hex]
      split_ifs with h
      · exact ha ⟨k, h⟩
      · simp
    obtain ⟨lam, hlam⟩ := signed_box hKR (fun k : Fin n => R k.val) (fun k => p k.val) (fun k => hR k.val)
      (fun a => F (ext a)) δ hδ0 hδ (by
        intro a b ha hb hab
        show ‖F (ext (a + b)) - F (ext a) - F (ext b)‖ ≤ δ
        rw [hadd]
        refine hF _ _ (hbd a ha) (hbd b hb) fun k => ?_
        have := hbd (a + b) hab k
        rwa [hadd, Finsupp.add_apply] at this)
    refine ⟨fun k => if h : k < n then ((lam ⟨k, h⟩ : ℝ) : T) else 0, fun d hd hdR => ?_⟩
    set a : Fin n → ℤ := fun k => d k.val with ha
    have hed : ext a = d := by
      ext k
      rw [hex]
      split_ifs with h
      · rfl
      · symm
        by_contra hc
        exact h (Finset.mem_range.1 (hd (Finsupp.mem_support_iff.2 hc)))
    have h := hlam a fun k => hdR k.val
    rw [hed] at h
    have e : ((∑ k : Fin n, lam k * (a k : ℝ) : ℝ) : T) =
        d.sum (fun k z => z • (if h : k < n then ((lam ⟨k, h⟩ : ℝ) : T) else 0)) := by
      rw [Finsupp.sum_of_support_subset d hd
          (fun k z => z • (if h : k < n then ((lam ⟨k, h⟩ : ℝ) : T) else 0)) (fun i _ => zero_smul _ _),
        ← Fin.sum_univ_eq_sum_range (fun k => d k • (if h : k < n then ((lam ⟨k, h⟩ : ℝ) : T) else 0)) n]
      have e2 : ∀ k : Fin n, d k.val • (if h : k.val < n then ((lam ⟨k.val, h⟩ : ℝ) : T) else 0) =
          ((lam k * (a k : ℝ) : ℝ) : T) := by
        intro k
        rw [dif_pos k.isLt, ← AddCircle.coe_zsmul]
        congr 1
        rw [zsmul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl fun k _ => e2 k]
      exact map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _
    rw [e] at h
    exact h
  choose lam hlam using fin
  obtain ⟨l, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq lam
  refine ⟨l, fun d hd => ?_⟩
  have hc : Tendsto (fun j => ‖F d - d.sum (fun k z => z • lam (φ j) k)‖) atTop
      (𝓝 ‖F d - d.sum (fun k z => z • l k)‖) := by
    refine (tendsto_const_nhds.sub ?_).norm
    refine tendsto_finsetSum _ fun k _ => ?_
    exact (tendsto_pi_nhds.1 hlim k).const_smul (d k)
  refine le_of_tendsto hc ?_
  obtain ⟨M, hM⟩ : ∃ M : ℕ, d.support ⊆ Finset.range M := d.support.exists_nat_subset_range
  refine eventually_atTop.2 ⟨M, fun j hj => ?_⟩
  refine hlam (φ j) d (hM.trans (Finset.range_mono ?_)) hd
  exact hj.trans hφ.le_apply

end Stab
end PVG
