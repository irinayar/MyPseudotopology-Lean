import Mathlib
import LeanCheck.JAEnergy
import LeanCheck.JAEnergyLink

/-!
# The energy identity `∑_d R(d)^2 = ∑_h r_3(h) r_2(h)` (Proposition `prop:energy-JA`)

For finite `A ⊆ ℤ` and weights `F, G`, let `R(d) = ∑_{a - b = d} F(a) G(b)` (`JAEnergy.rep`) and
`r_F(h) = ∑_{a' - a = h} F(a) F(a')` (`acf`).  Counting quadruples with `a - b = a' - b'` by the common
shift `a' - a = b' - b` gives, for any finite `T` containing all differences of `A`,
`∑_{d ∈ T} R(d)^2 = ∑_{h ∈ T} r_F(h) r_G(h)`.
-/

namespace LeanCheck
namespace JAEnergyIdentity

open Finset JAEnergy

lemma rep_eq (A : Finset ℤ) (F G : ℤ → ℝ) (d : ℤ) :
    rep A A F G d = ∑ a ∈ A, ∑ b ∈ A, if a - b = d then F a * G b else 0 := by
  unfold rep
  rw [Finset.sum_filter, Finset.sum_product]

/-- Autocorrelation of a weight supported on `A`. -/
def acf (A : Finset ℤ) (F : ℤ → ℝ) (h : ℤ) : ℝ :=
  ∑ a ∈ A, ∑ a' ∈ A, if a' - a = h then F a * F a' else 0

lemma sum_comm4 {α β γ δ : Type*} (T : Finset α) (A : Finset β) (B : Finset γ) (C : Finset δ)
    (D : Finset β) (f : α → β → β → γ → δ → ℝ) :
    ∑ d ∈ T, ∑ a ∈ A, ∑ a' ∈ D, ∑ b ∈ B, ∑ b' ∈ C, f d a a' b b' =
      ∑ a ∈ A, ∑ a' ∈ D, ∑ b ∈ B, ∑ b' ∈ C, ∑ d ∈ T, f d a a' b b' := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a' _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

theorem sum_sq_rep (A : Finset ℤ) (F G : ℤ → ℝ) (T : Finset ℤ)
    (hT : ∀ a ∈ A, ∀ b ∈ A, a - b ∈ T) :
    ∑ d ∈ T, (rep A A F G d) ^ 2 = ∑ h ∈ T, acf A F h * acf A G h := by
  classical
  -- left side as a quadruple sum
  have hL : ∀ d, (rep A A F G d) ^ 2 = ∑ a ∈ A, ∑ a' ∈ A, ∑ b ∈ A, ∑ b' ∈ A,
      (if a - b = d then F a * G b else 0) * (if a' - b' = d then F a' * G b' else 0) := by
    intro d
    rw [rep_eq, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro a' _
    rw [Finset.sum_mul_sum]
  -- right side as a quadruple sum
  have hR : ∀ h, acf A F h * acf A G h = ∑ a ∈ A, ∑ a' ∈ A, ∑ b ∈ A, ∑ b' ∈ A,
      (if a' - a = h then F a * F a' else 0) * (if b' - b = h then G b * G b' else 0) := by
    intro h
    unfold acf
    rw [Finset.sum_mul_sum]
    rw [show (∑ a ∈ A, ∑ b ∈ A, (∑ a' ∈ A, if a' - a = h then F a * F a' else 0) *
        (∑ b' ∈ A, if b' - b = h then G b * G b' else 0)) =
        ∑ a ∈ A, ∑ b ∈ A, ∑ a' ∈ A, ∑ b' ∈ A,
          (if a' - a = h then F a * F a' else 0) * (if b' - b = h then G b * G b' else 0) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [Finset.sum_mul_sum]))]
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  have e1 : ∑ d ∈ T, (rep A A F G d) ^ 2 = ∑ a ∈ A, ∑ a' ∈ A, ∑ b ∈ A, ∑ b' ∈ A, ∑ d ∈ T,
      (if a - b = d then F a * G b else 0) * (if a' - b' = d then F a' * G b' else 0) := by
    rw [Finset.sum_congr rfl (fun d _ => hL d)]
    exact sum_comm4 T A A A A (fun d a a' b b' =>
      (if a - b = d then F a * G b else 0) * (if a' - b' = d then F a' * G b' else 0))
  have e2 : ∑ h ∈ T, acf A F h * acf A G h = ∑ a ∈ A, ∑ a' ∈ A, ∑ b ∈ A, ∑ b' ∈ A, ∑ h ∈ T,
      (if a' - a = h then F a * F a' else 0) * (if b' - b = h then G b * G b' else 0) := by
    rw [Finset.sum_congr rfl (fun h _ => hR h)]
    exact sum_comm4 T A A A A (fun h a a' b b' =>
      (if a' - a = h then F a * F a' else 0) * (if b' - b = h then G b * G b' else 0))
  rw [e1, e2]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro a' ha'
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro b' hb'
  have hab : a - b ∈ T := hT a ha b hb
  have ha'a : a' - a ∈ T := by
    have := hT a' ha' a ha
    exact this
  by_cases hc : a - b = a' - b'
  · have hc' : a' - a = b' - b := by omega
    have e1 : ∑ d ∈ T, (if a - b = d then F a * G b else 0) * (if a' - b' = d then F a' * G b' else 0)
        = F a * G b * (F a' * G b') := by
      rw [Finset.sum_eq_single (a - b)]
      · simp [hc]
      · intro d _ hd
        rw [if_neg (Ne.symm hd), zero_mul]
      · intro h; exact absurd hab h
    have e2 : ∑ h ∈ T, (if a' - a = h then F a * F a' else 0) * (if b' - b = h then G b * G b' else 0)
        = F a * F a' * (G b * G b') := by
      rw [Finset.sum_eq_single (a' - a)]
      · simp [hc']
      · intro d _ hd
        rw [if_neg (Ne.symm hd), zero_mul]
      · intro h; exact absurd ha'a h
    rw [e1, e2]; ring
  · have hc' : ¬ (a' - a = b' - b) := by omega
    have e1 : ∑ d ∈ T, (if a - b = d then F a * G b else 0) * (if a' - b' = d then F a' * G b' else 0)
        = 0 := by
      apply Finset.sum_eq_zero
      intro d _
      by_cases h1 : a - b = d
      · have : ¬ (a' - b' = d) := by omega
        rw [if_neg this, mul_zero]
      · rw [if_neg h1, zero_mul]
    have e2 : ∑ h ∈ T, (if a' - a = h then F a * F a' else 0) * (if b' - b = h then G b * G b' else 0)
        = 0 := by
      apply Finset.sum_eq_zero
      intro d _
      by_cases h1 : a' - a = d
      · have : ¬ (b' - b = d) := by omega
        rw [if_neg this, mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [e1, e2]


/-! ### Specialization to the periodic weights restricted to `[0, X]` -/

section special

open JAEnergyLink

/-- The window `{0, ..., X}` as a finite set of integers. -/
def Aset (X : ℕ) : Finset ℤ := (range (X + 1)).image (fun x : ℕ => (x : ℤ))

/-- The weight on `ℤ` attached to `fz : ZMod q → ℝ` (values at negative integers are irrelevant). -/
def Fw {q : ℕ} [NeZero q] (fz : ZMod q → ℝ) (a : ℤ) : ℝ := fn fz a.toNat

lemma sum_Aset (X : ℕ) (g : ℤ → ℝ) : ∑ a ∈ Aset X, g a = ∑ x ∈ range (X + 1), g (x : ℤ) := by
  unfold Aset
  rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]

lemma acf_neg (A : Finset ℤ) (F : ℤ → ℝ) (h : ℤ) : acf A F (-h) = acf A F h := by
  unfold acf
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a' _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hc : a - a' = h
  · rw [if_pos hc, if_pos (by omega)]
    ring
  · rw [if_neg hc, if_neg (by omega)]

lemma acf_Aset_nat {q : ℕ} [NeZero q] (fz : ZMod q → ℝ) (X n : ℕ) :
    acf (Aset X) (Fw fz) (n : ℤ) = alpha fz X n := by
  classical
  unfold acf alpha
  rw [sum_Aset]
  have h1 : ∀ x : ℕ, (∑ a' ∈ Aset X, if a' - (x : ℤ) = (n : ℤ) then Fw fz (x : ℤ) * Fw fz a' else 0) =
      if x + n < X + 1 then fn fz x * fn fz (x + n) else 0 := by
    intro x
    rw [sum_Aset]
    have : ∀ y : ℕ, ((y : ℤ) - (x : ℤ) = (n : ℤ)) ↔ y = x + n := by
      intro y; constructor <;> intro h <;> omega
    simp_rw [this]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range, Fw, Int.toNat_natCast]
    all_goals simp
  simp_rw [h1]
  rw [← Finset.sum_filter]
  have : (range (X + 1)).filter (fun x => x + n < X + 1) = range (X + 1 - n) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this]

lemma sum_Icc_symm (φ : ℤ → ℝ) (X : ℕ) :
    ∑ h ∈ Finset.Icc (-(X : ℤ)) X, φ h = φ 0 + ∑ n ∈ Ico 1 (X + 1), (φ (n : ℤ) + φ (-(n : ℤ))) := by
  induction X with
  | zero => simp
  | succ X ih =>
    have hs : Finset.Icc (-((X + 1 : ℕ) : ℤ)) ((X + 1 : ℕ) : ℤ) =
        insert (-((X + 1 : ℕ) : ℤ)) (insert ((X + 1 : ℕ) : ℤ) (Finset.Icc (-(X : ℤ)) X)) := by
      ext h; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have hn1 : (-((X + 1 : ℕ) : ℤ)) ∉ insert ((X + 1 : ℕ) : ℤ) (Finset.Icc (-(X : ℤ)) X) := by
      simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have hn2 : ((X + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(X : ℤ)) X := by
      simp only [Finset.mem_Icc]; push_cast; omega
    have hI : ∑ n ∈ Ico 1 (X + 1 + 1), (φ (n : ℤ) + φ (-(n : ℤ))) =
        ∑ n ∈ Ico 1 (X + 1), (φ (n : ℤ) + φ (-(n : ℤ))) +
          (φ ((X + 1 : ℕ) : ℤ) + φ (-((X + 1 : ℕ) : ℤ))) :=
      Finset.sum_Ico_succ_top (by omega) _
    rw [hs, Finset.sum_insert hn1, Finset.sum_insert hn2, ih, hI]
    ring

/-- **The representation energy equals the autocorrelation energy** `E` of `JAEnergyLink.energyE`. -/
theorem sum_sq_rep_energyE {q₂ q₃ : ℕ} [NeZero q₂] [NeZero q₃] (f₂ : ZMod q₂ → ℝ)
    (f₃ : ZMod q₃ → ℝ) (X : ℕ) :
    ∑ d ∈ Finset.Icc (-(X : ℤ)) X, (rep (Aset X) (Aset X) (Fw f₃) (Fw f₂) d) ^ 2 =
      energyE f₂ f₃ X := by
  have hT : ∀ a ∈ Aset X, ∀ b ∈ Aset X, a - b ∈ Finset.Icc (-(X : ℤ)) X := by
    intro a ha b hb
    unfold Aset at ha hb
    simp only [Finset.mem_image, Finset.mem_range] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    rw [Finset.mem_Icc]; omega
  rw [sum_sq_rep (Aset X) (Fw f₃) (Fw f₂) _ hT]
  rw [sum_Icc_symm (fun h => acf (Aset X) (Fw f₃) h * acf (Aset X) (Fw f₂) h) X]
  have a3 : acf (Aset X) (Fw f₃) (0 : ℤ) = alpha f₃ X 0 := by
    simpa using acf_Aset_nat f₃ X 0
  have a2 : acf (Aset X) (Fw f₂) (0 : ℤ) = alpha f₂ X 0 := by
    simpa using acf_Aset_nat f₂ X 0
  unfold energyE
  simp only [acf_neg, acf_Aset_nat, a3, a2]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => by ring)

end special

#print axioms sum_sq_rep
#print axioms sum_sq_rep_energyE

end JAEnergyIdentity
end LeanCheck
