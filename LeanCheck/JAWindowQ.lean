import Mathlib
import LeanCheck.JAWindow
import LeanCheck.JARandom

/-!
# The window kernel (component 11), stage 2: the window on `ZMod Q`, its mean, Parseval, the mass `K_Q(T)`

`wQ D Q x = w_D(x̃ / Q)` with `x̃ = x.valMinAbs ∈ (-Q/2, Q/2]` the balanced representative (paper, Section
"normalized product argument").

Checked here (no axiom, no `sorry`):

* `sum_wQ`, `sum_wQ_sq`: `|m_Q - I_1| ≤ 2/Q` and `|(1/Q) ∑ w_Q^2 - I_2| ≤ 2/Q`, with `m_Q = (1/Q) ∑ w_Q`,
  `I_1 = 16/(15D)`, `I_2 = 256/(315D)` (the bridge from sums over `ZMod Q` to the one-sided lattice sums of
  `JAWindow`, via `|x̃| = min (val x, Q - val x)`);
* `parseval_Fq`: `∑_r |Ŵ(r)|^2 = Q ∑_x w(x)^2` for any real `w` on `ZMod Q`;
* `Fq_zero`: `Ŵ(0) = ∑ w`, hence `κ_Q(0) = 1`;
* `KQ_le`: for `D ≥ 3` and `Q ≥ 25 D`, `K_Q(T) = ∑_r κ_Q(r) = Q ∑ w^2 / (∑ w)^2 ≤ 30 D / 7 = B_D`.

Not checked here: the tail bound `∑_{|r|>u} κ_Q(r) ≤ A_D u^{-3}` (second differences).
-/

namespace LeanCheck
namespace JAWindowQ

open Finset JAWindow JARandom JALocalize

section window

variable {Q : ℕ} [NeZero Q]

/-- The window on `ZMod Q` with balanced representatives. -/
noncomputable def wQ (D : ℝ) (Q : ℕ) [NeZero Q] (x : ZMod Q) : ℝ := wD D ((x.valMinAbs : ℝ) / Q)

lemma wQ_nonneg (D : ℝ) (x : ZMod Q) : 0 ≤ wQ D Q x := wD_nonneg _ _

lemma sum_zmod_val (G : ℕ → ℝ) : ∑ x : ZMod Q, G x.val = ∑ v ∈ range Q, G v := by
  refine Finset.sum_bij (fun x _ => x.val) (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x)) ?_ ?_
    (fun _ _ => rfl)
  · intro a _ b _ h
    exact ZMod.val_injective Q h
  · intro v hv
    rw [Finset.mem_range] at hv
    exact ⟨(v : ZMod Q), Finset.mem_univ _, by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv]⟩

lemma wD_abs (D z : ℝ) : wD D z = wD D |z| := by
  rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, wD_even]

lemma wQ_eq (D : ℝ) (x : ZMod Q) :
    wQ D Q x = wD D (((min x.val (Q - x.val) : ℕ) : ℝ) / Q) := by
  unfold wQ
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have h := ZMod.valMinAbs_natAbs_eq_min x
  have hcast : (((min x.val (Q - x.val) : ℕ)) : ℝ) = |(x.valMinAbs : ℝ)| := by
    rw [← h, ← Int.cast_abs, Int.abs_eq_natAbs]
    simp
  rw [hcast, wD_abs D ((x.valMinAbs : ℝ) / Q), abs_div, abs_of_pos hQ]

lemma sum_fold (hQ : 0 < Q) (G : ℕ → ℝ) :
    ∑ v ∈ range Q, G (min v (Q - v)) =
      ∑ i ∈ range (Q / 2 + 1), G i + ∑ i ∈ range (Q - Q / 2 - 1), G (i + 1) := by
  have hle : Q / 2 + 1 ≤ Q := by omega
  rw [← Finset.sum_range_add_sum_Ico _ hle]
  congr 1
  · apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mem_range] at hv
    congr 1
    omega
  · rw [Finset.sum_Ico_eq_sum_range]
    have hn : Q - (Q / 2 + 1) = Q - Q / 2 - 1 := by omega
    rw [hn]
    rw [← Finset.sum_range_reflect (fun i => G (min (Q / 2 + 1 + i) (Q - (Q / 2 + 1 + i)))) (Q - Q / 2 - 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    congr 1
    omega

lemma sum_wQ_fold (D : ℝ) (g : ℝ → ℝ) (hg : ∀ x : ZMod Q, g (wQ D Q x) =
    (fun j : ℕ => g (wD D ((j : ℝ) / Q))) (min x.val (Q - x.val))) :
    ∑ x : ZMod Q, g (wQ D Q x) =
      ∑ i ∈ range (Q / 2 + 1), g (wD D ((i : ℝ) / Q)) +
        ∑ i ∈ range (Q - Q / 2 - 1), g (wD D (((i + 1 : ℕ) : ℝ) / Q)) := by
  have hQ : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  rw [Finset.sum_congr rfl (fun x _ => hg x)]
  rw [sum_zmod_val (fun v => (fun j : ℕ => g (wD D ((j : ℝ) / Q))) (min v (Q - v)))]
  exact sum_fold hQ (fun j : ℕ => g (wD D ((j : ℝ) / Q)))

lemma lattice_params (D : ℝ) (hD : 3 ≤ D) :
    (1 / D ≤ 0 + ((Q / 2 + 1 : ℕ) : ℝ) * (1 / (Q : ℝ))) ∧
      (1 / D ≤ (1 / (Q : ℝ) - 0) + ((Q - Q / 2 - 1 : ℕ) : ℝ) * (1 / (Q : ℝ))) := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hD0 : 0 < D := by linarith
  have h1 : (Q : ℝ) ≤ 2 * ((Q / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : Q ≤ 2 * (Q / 2 + 1))
  have h2 : (Q : ℝ) ≤ 2 * (1 + ((Q - Q / 2 - 1 : ℕ) : ℝ)) := by
    have : Q ≤ 2 * (1 + (Q - Q / 2 - 1)) := by omega
    exact_mod_cast this
  have hD2 : 1 / D ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hD
  constructor
  · have : (1 : ℝ) / 2 ≤ 0 + ((Q / 2 + 1 : ℕ) : ℝ) * (1 / (Q : ℝ)) := by
      rw [zero_add, mul_one_div, le_div_iff₀ hQ]; linarith
    linarith
  · have : (1 : ℝ) / 2 ≤ (1 / (Q : ℝ) - 0) + ((Q - Q / 2 - 1 : ℕ) : ℝ) * (1 / (Q : ℝ)) := by
      have e : (1 / (Q : ℝ) - 0) + ((Q - Q / 2 - 1 : ℕ) : ℝ) * (1 / (Q : ℝ)) =
          (1 + ((Q - Q / 2 - 1 : ℕ) : ℝ)) / Q := by field_simp; ring
      rw [e, le_div_iff₀ hQ]; linarith
    linarith

/-- `|m_Q - I_1| ≤ 2/Q`. -/
theorem sum_wQ (D : ℝ) (hD : 3 ≤ D) :
    |(∑ x : ZMod Q, wQ D Q x) / Q - 16 / (15 * D)| ≤ 2 / Q := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hD0 : 0 < D := by linarith
  have hfold := sum_wQ_fold (Q := Q) D id (fun x => by simp only [id]; rw [wQ_eq])
  obtain ⟨hk, hk'⟩ := lattice_params (Q := Q) D hD
  have hlat := lattice_wD D hD0 (1 / (Q : ℝ)) 0 (Q / 2 + 1) (Q - Q / 2 - 1) (by positivity) le_rfl
    (by positivity) hk hk'
  simp only [id] at hfold
  rw [hfold]
  have e1 : ∀ i : ℕ, wD D (0 + (i : ℝ) * (1 / (Q : ℝ))) = wD D ((i : ℝ) / Q) := by
    intro i; congr 1; ring
  have e2 : ∀ i : ℕ, wD D ((1 / (Q : ℝ) - 0) + (i : ℝ) * (1 / (Q : ℝ))) =
      wD D (((i + 1 : ℕ) : ℝ) / Q) := by
    intro i; congr 1; push_cast; ring
  simp_rw [e1, e2] at hlat
  have e3 : (∑ i ∈ range (Q / 2 + 1), wD D ((i : ℝ) / Q) +
      ∑ i ∈ range (Q - Q / 2 - 1), wD D (((i + 1 : ℕ) : ℝ) / Q)) / Q =
      1 / (Q : ℝ) * (∑ i ∈ range (Q / 2 + 1), wD D ((i : ℝ) / Q) +
        ∑ i ∈ range (Q - Q / 2 - 1), wD D (((i + 1 : ℕ) : ℝ) / Q)) := by ring
  rw [e3]
  have e4 : 2 / (Q : ℝ) = 2 * (1 / (Q : ℝ)) := by ring
  rw [e4]
  exact hlat

/-- `|(1/Q) ∑ w_Q^2 - I_2| ≤ 2/Q`. -/
theorem sum_wQ_sq (D : ℝ) (hD : 3 ≤ D) :
    |(∑ x : ZMod Q, (wQ D Q x) ^ 2) / Q - 256 / (315 * D)| ≤ 2 / Q := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hD0 : 0 < D := by linarith
  have hfold := sum_wQ_fold (Q := Q) D (fun y => y ^ 2) (fun x => by simp only []; rw [wQ_eq])
  obtain ⟨hk, hk'⟩ := lattice_params (Q := Q) D hD
  have hlat := lattice_wD_sq D hD0 (1 / (Q : ℝ)) 0 (Q / 2 + 1) (Q - Q / 2 - 1) (by positivity)
    le_rfl (by positivity) hk hk'
  rw [hfold]
  have e1 : ∀ i : ℕ, wD D (0 + (i : ℝ) * (1 / (Q : ℝ))) = wD D ((i : ℝ) / Q) := by
    intro i; congr 1; ring
  have e2 : ∀ i : ℕ, wD D ((1 / (Q : ℝ) - 0) + (i : ℝ) * (1 / (Q : ℝ))) =
      wD D (((i + 1 : ℕ) : ℝ) / Q) := by
    intro i; congr 1; push_cast; ring
  simp_rw [e1, e2] at hlat
  have e3 : (∑ i ∈ range (Q / 2 + 1), (wD D ((i : ℝ) / Q)) ^ 2 +
      ∑ i ∈ range (Q - Q / 2 - 1), (wD D (((i + 1 : ℕ) : ℝ) / Q)) ^ 2) / Q =
      1 / (Q : ℝ) * (∑ i ∈ range (Q / 2 + 1), (wD D ((i : ℝ) / Q)) ^ 2 +
        ∑ i ∈ range (Q - Q / 2 - 1), (wD D (((i + 1 : ℕ) : ℝ) / Q)) ^ 2) := by ring
  rw [e3]
  have e4 : 2 / (Q : ℝ) = 2 * (1 / (Q : ℝ)) := by ring
  rw [e4]
  exact hlat

end window

section parseval

variable {Q : ℕ} [NeZero Q]

/-- **Parseval**: `∑_r |Ŵ(r)|^2 = Q ∑_x w(x)^2`. -/
theorem parseval_Fq (w : ZMod Q → ℝ) : ∑ r : ZMod Q, ‖Fq w r‖ ^ 2 = Q * ∑ x, (w x) ^ 2 := by
  have h := acorr_eq' w 0
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one] at h
  have h2 : ∑ r : ZMod Q, Fq w r * Gq w r = ∑ r : ZMod Q, ((‖Fq w r‖ ^ 2 : ℝ) : ℂ) :=
    Finset.sum_congr rfl (fun r _ => FG_normsq w r)
  rw [h2] at h
  have h3 : (Q : ℂ) * ((acorr w 0 : ℝ) : ℂ) = ((Q * ∑ x, (w x) ^ 2 : ℝ) : ℂ) := by
    unfold acorr
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    simp [sq]
  rw [h3] at h
  exact_mod_cast h.symm

lemma Fq_zero (w : ZMod Q → ℝ) : Fq w 0 = ((∑ x, w x : ℝ) : ℂ) := by
  unfold Fq
  simp

/-- `κ_Q(0) = 1`: `|Ŵ(0)|^2 = (∑ w)^2` for a nonnegative window. -/
theorem norm_Fq_zero (w : ZMod Q → ℝ) (hw : ∀ x, 0 ≤ w x) :
    ‖Fq w 0‖ ^ 2 = (∑ x, w x) ^ 2 := by
  rw [Fq_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The total mass `K_Q(T) = ∑_r κ_Q(r) = ∑_r |Ŵ(r)|^2 / (∑ w)^2`. -/
noncomputable def KQ (D : ℝ) (Q : ℕ) [NeZero Q] : ℝ :=
  (∑ r : ZMod Q, ‖Fq (wQ D Q) r‖ ^ 2) / (∑ x, wQ D Q x) ^ 2

/-- **The mass bound** `K_Q(T) ≤ B_D = 30 D / 7` for late `Q`. -/
theorem KQ_le (D : ℝ) (hD : 3 ≤ D) (hQ : 25 * D ≤ Q) : KQ D Q ≤ 30 * D / 7 := by
  have hD0 : 0 < D := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hS1 := sum_wQ (Q := Q) D hD
  have hS2 := sum_wQ_sq (Q := Q) D hD
  set S1 := ∑ x : ZMod Q, wQ D Q x with hS1d
  set S2 := ∑ x : ZMod Q, (wQ D Q x) ^ 2 with hS2d
  have h2Q : 2 / (Q : ℝ) ≤ 2 / (25 * D) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hQ
  have ha : 74 / (75 * D) ≤ S1 / Q := by
    have := (abs_le.mp hS1).1
    have e : 16 / (15 * D) - 2 / (25 * D) = 74 / (75 * D) := by field_simp; norm_num
    linarith
  have hb : S2 / Q ≤ 7030 / (7875 * D) := by
    have := (abs_le.mp hS2).2
    have e : 256 / (315 * D) + 2 / (25 * D) = 7030 / (7875 * D) := by field_simp; norm_num
    linarith
  have hK : KQ D Q = (S2 / Q) / (S1 / Q) ^ 2 := by
    unfold KQ
    rw [parseval_Fq]
    field_simp
    rfl
  rw [hK]
  have ha0 : 0 < 74 / (75 * D) := by positivity
  have hb0 : 0 ≤ S2 / Q := by
    apply div_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _)) hQ0.le
  calc (S2 / Q) / (S1 / Q) ^ 2 ≤ (7030 / (7875 * D)) / (74 / (75 * D)) ^ 2 := by
        exact div_le_div₀ (by positivity) hb (by positivity) (pow_le_pow_left₀ ha0.le ha 2)
    _ = (7030 * 75 ^ 2 / (7875 * 74 ^ 2)) * D := by field_simp
    _ ≤ 30 * D / 7 := by
        have : (7030 * 75 ^ 2 / (7875 * 74 ^ 2) : ℝ) ≤ 30 / 7 := by norm_num
        nlinarith

end parseval

#print axioms sum_wQ
#print axioms sum_wQ_sq
#print axioms parseval_Fq
#print axioms norm_Fq_zero
#print axioms KQ_le

end JAWindowQ
end LeanCheck
