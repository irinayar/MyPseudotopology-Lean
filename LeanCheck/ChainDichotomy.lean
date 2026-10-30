import LeanCheck.ChainLemmas
import LeanCheck.ChainDigits

/-!
# Theorem G, compatible direction: the Case I / Case II dichotomy (`ChainSubsetTheorem_note.md`)

Abstract finite-level formulation.  `α : ℕ → ℕ` are the ratios (`α i ≥ 2`, `α i → ∞`), `M = Mseq α`.
A profinite integer `ζ` is a compatible system of residues `z : ℕ → ℤ` (`M k ∣ z (k+1) - z k`); on
`x = ∑_{j<K} ρ_j / M_{j+1}` it takes the value `∑_{j<K} ρ_j θ_j` modulo 1, `θ_j = z_{j+1} / M_{j+1}`.

`Cont α z δ` is the quarter-arc form of continuity of `ζ` for the topology `λ_C`:
whenever every `M_i x` (`i ≤ K`) is within `δ` of an integer, `ζ x` is within `1/4` of an integer.

Main result `case_dichotomy`: if `ζ` is `δ`-continuous then `ζ` is an integer, i.e. there are `u` and `i₀`
with `M_{i+1} ∣ z_{i+1} - u` for all `i ≥ i₀`.
-/

namespace LeanCheck

open Finset

/-- The value of `ζ` on `x = ∑_{j<K} ρ_j / M_{j+1}` (modulo 1). -/
noncomputable def chi (α : ℕ → ℕ) (z : ℕ → ℤ) (ρ : ℕ → ℤ) (K : ℕ) : ℝ :=
  ∑ j ∈ range K, (ρ j : ℝ) * ((z (j + 1) : ℝ) / (Mseq α (j + 1) : ℝ))

/-- Quarter-arc continuity of `ζ` with radius `δ`. -/
def Cont (α : ℕ → ℕ) (z : ℕ → ℤ) (δ : ℝ) : Prop :=
  ∀ (K : ℕ) (ρ : ℕ → ℤ),
    (∀ i ≤ K, ∃ n : ℤ, |((((Mseq α i : ℚ) * xval α ρ K : ℚ)) : ℝ) - n| < δ) →
      ∃ n : ℤ, |chi α z ρ K - n| < 1 / 4

/-! ### Digits bounded by `η α_t` give `|w_n| ≤ 2η` -/

lemma digit_bound {α : ℕ → ℕ} (hα : ∀ i, 2 ≤ α i) (ρ : ℕ → ℤ) {η : ℝ} (hη : 0 ≤ η)
    (hρ : ∀ t, |(ρ t : ℝ)| ≤ η * α t) {K n : ℕ} (hn : n ≤ K) :
    |((wval α ρ K n : ℚ) : ℝ)| ≤ 2 * η := by
  have hα0 : ∀ i, 0 < α i := fun i => lt_of_lt_of_le (by norm_num) (hα i)
  have hM : ∀ i, (0 : ℝ) < Mseq α i := fun i => by exact_mod_cast Mseq_pos hα0 i
  have hcast : ((wval α ρ K n : ℚ) : ℝ) =
      ∑ t ∈ Finset.Ico n K, (ρ t : ℝ) * (Mseq α n : ℝ) / (Mseq α (t + 1) : ℝ) := by
    unfold wval; push_cast; rfl
  rw [hcast, Finset.sum_Ico_eq_sum_range]
  set a : ℕ → ℝ := fun j => η * (Mseq α n : ℝ) / (Mseq α (n + j) : ℝ) with ha
  have hMs : ∀ j, (Mseq α (n + j + 1) : ℝ) = α (n + j) * Mseq α (n + j) := by
    intro j; simp [Mseq]
  have hterm : ∀ j, |(ρ (n + j) : ℝ) * (Mseq α n : ℝ) / (Mseq α (n + j + 1) : ℝ)| ≤ a j := by
    intro j
    have h1 : (0 : ℝ) < α (n + j) := by exact_mod_cast hα0 (n + j)
    have h2 := hM (n + j)
    have h3 := hM n
    rw [abs_div, abs_mul, abs_of_pos h3, abs_of_pos (hM _), hMs]
    simp only [ha]
    rw [div_le_div_iff₀ (by positivity) h2]
    have := hρ (n + j)
    nlinarith [mul_pos h1 h2, mul_pos h3 h2]
  have hnn : ∀ j, 0 ≤ a j := fun j => by simp only [ha]; have := hM (n + j); have := hM n; positivity
  have hhalf : ∀ j, a (j + 1) ≤ a j / 2 := by
    intro j
    have h1 : (2 : ℝ) ≤ α (n + j) := by exact_mod_cast hα (n + j)
    have h2 := hM (n + j)
    have h3 := hM n
    have e : a (j + 1) = a j / α (n + j) := by
      simp only [ha]
      rw [show n + (j + 1) = n + j + 1 by ring, hMs]
      field_simp
    rw [e]
    have : 0 ≤ a j := hnn j
    apply div_le_div_of_nonneg_left this (by norm_num) h1
  calc |∑ j ∈ Finset.range (K - n), (ρ (n + j) : ℝ) * (Mseq α n : ℝ) / (Mseq α (n + j + 1) : ℝ)|
      ≤ ∑ j ∈ Finset.range (K - n), |(ρ (n + j) : ℝ) * (Mseq α n : ℝ) / (Mseq α (n + j + 1) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (K - n), a j := Finset.sum_le_sum (fun j _ => hterm j)
    _ ≤ 2 * a 0 := geom_tail hnn hhalf _
    _ = 2 * η := by
      simp only [ha, add_zero]
      have := hM n
      field_simp

/-! ### Step 1: the one-digit witness bounds `dist(θ_i, ℤ)` -/

/-- A digit string with the single digit `ρ` at position `i`. -/
def unit (i : ℕ) (ρ : ℤ) : ℕ → ℤ := fun j => if j = i then ρ else 0

lemma xval_unit (α : ℕ → ℕ) (i : ℕ) (ρ : ℤ) :
    xval α (unit i ρ) (i + 1) = (ρ : ℚ) / (Mseq α (i + 1) : ℚ) := by
  unfold xval
  rw [Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp [unit]
  · intro j hj
    have : j ≠ i := by have := Finset.mem_range.mp hj; omega
    simp [unit, this]

lemma chi_unit (α : ℕ → ℕ) (z : ℕ → ℤ) (i : ℕ) (ρ : ℤ) :
    chi α z (unit i ρ) (i + 1) = (ρ : ℝ) * ((z (i + 1) : ℝ) / (Mseq α (i + 1) : ℝ)) := by
  unfold chi
  rw [Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp [unit]
  · intro j hj
    have : j ≠ i := by have := Finset.mem_range.mp hj; omega
    simp [unit, this]

lemma step1 {α : ℕ → ℕ} (hα : ∀ i, 2 ≤ α i) {z : ℕ → ℤ} {δ : ℝ} (hδ : 0 < δ) (hC : Cont α z δ)
    {i : ℕ} (hbig : 8 / δ ≤ α i) :
    ∃ m : ℤ, |((z (i + 1) : ℝ) / (Mseq α (i + 1) : ℝ)) - m| ≤ 2 / (δ * α i) := by
  have hα0 : ∀ i, 0 < α i := fun i => lt_of_lt_of_le (by norm_num) (hα i)
  have hαi : (0 : ℝ) < α i := by exact_mod_cast hα0 i
  have hbig' : 8 ≤ δ * α i := by
    have := (div_le_iff₀ hδ).mp hbig
    linarith
  set R : ℕ := ⌊(δ / 4) * α i⌋₊ with hRdef
  have hx2 : 2 ≤ (δ / 4) * α i := by linarith
  have hR1 : 1 ≤ R := Nat.le_floor (by push_cast; linarith)
  have hRge : δ * α i / 8 ≤ R := by
    have := Nat.lt_floor_add_one ((δ / 4) * α i)
    linarith
  have hRle : (R : ℝ) ≤ (δ / 4) * α i := Nat.floor_le (by positivity)
  have key : ∀ ρ : ℕ, ρ ≤ R →
      ∃ n : ℤ, |(ρ : ℝ) * ((z (i + 1) : ℝ) / (Mseq α (i + 1) : ℝ)) - n| < 1 / 4 := by
    intro ρ hρ
    have hρR : (ρ : ℝ) ≤ R := by exact_mod_cast hρ
    have hball : ∀ j ≤ i + 1, ∃ n : ℤ,
        |((((Mseq α j : ℚ) * xval α (unit i (ρ : ℤ)) (i + 1) : ℚ)) : ℝ) - n| < δ := by
      intro j hj
      rw [xval_unit]
      simp only [Int.cast_natCast]
      by_cases hji : j ≤ i
      · obtain ⟨h0, h1⟩ := single_digit_small hα0 ρ hji
        refine ⟨0, ?_⟩
        have h0' : (0 : ℝ) ≤ (((Mseq α j : ℚ) * ((ρ : ℚ) / Mseq α (i + 1)) : ℚ) : ℝ) := by
          exact_mod_cast h0
        have h1' : (((Mseq α j : ℚ) * ((ρ : ℚ) / Mseq α (i + 1)) : ℚ) : ℝ) ≤ (ρ : ℝ) / α i :=
          le_trans (Rat.cast_le.mpr h1) (le_of_eq (by push_cast; ring))
        have h2 : (ρ : ℝ) / α i ≤ δ / 4 := by
          rw [div_le_iff₀ hαi]; nlinarith
        simp only [Int.cast_zero, sub_zero]
        rw [abs_of_nonneg h0']
        linarith
      · have hj' : j = i + 1 := by omega
        subst hj'
        obtain ⟨n, hn⟩ := single_digit_int hα0 ρ (le_refl (i + 1))
        refine ⟨n, ?_⟩
        have : (((Mseq α (i + 1) : ℚ) * ((ρ : ℚ) / Mseq α (i + 1)) : ℚ) : ℝ) = n := by
          exact_mod_cast hn
        rw [this]; simpa using hδ
    obtain ⟨n, hn⟩ := hC (i + 1) (unit i (ρ : ℤ)) hball
    rw [chi_unit] at hn
    exact ⟨n, by simpa using hn⟩
  obtain ⟨m, hm⟩ := near_of_all_multiples hR1 key
  refine ⟨m, hm.trans ?_⟩
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### Step 2: the integer relation between consecutive levels -/

/-- `θ_i = z_{i+1} / M_{i+1}`. -/
noncomputable def thetaR (α : ℕ → ℕ) (z : ℕ → ℤ) (i : ℕ) : ℝ :=
  (z (i + 1) : ℝ) / (Mseq α (i + 1) : ℝ)

lemma theta_rel {α : ℕ → ℕ} (hα : ∀ i, 2 ≤ α i) {z : ℕ → ℤ}
    (hz : ∀ k, (Mseq α k : ℤ) ∣ z (k + 1) - z k) (i : ℕ) (mm : ℕ → ℤ) :
    ∃ b : ℤ, (α (i + 1) : ℝ) * (thetaR α z (i + 1) - mm (i + 1)) - (thetaR α z i - mm i) = b := by
  have hα0 : ∀ i, 0 < α i := fun i => lt_of_lt_of_le (by norm_num) (hα i)
  obtain ⟨c, hc⟩ := hz (i + 1)
  refine ⟨c - α (i + 1) * mm (i + 1) + mm i, ?_⟩
  have hM1 : (0 : ℝ) < Mseq α (i + 1) := by exact_mod_cast Mseq_pos hα0 (i + 1)
  have hα1 : (0 : ℝ) < α (i + 1) := by exact_mod_cast hα0 (i + 1)
  have hMs : (Mseq α (i + 1 + 1) : ℝ) = α (i + 1) * Mseq α (i + 1) := by simp [Mseq]
  have hzc : (z (i + 1 + 1) : ℝ) = z (i + 1) + Mseq α (i + 1) * c := by
    have : z (i + 1 + 1) = z (i + 1) + (Mseq α (i + 1) : ℤ) * c := by linarith
    exact_mod_cast this
  unfold thetaR
  rw [hMs, hzc]
  push_cast
  field_simp
  ring

/-- Case I: if `α_{i+1} r_{i+1} = r_i` for all `i ≥ i₁` then `z_{i+1} - M_{i+1} m_i` is constant. -/
lemma caseI {α : ℕ → ℕ} (hα : ∀ i, 2 ≤ α i) {z : ℕ → ℤ} (mm : ℕ → ℤ) {i1 : ℕ}
    (h : ∀ i ≥ i1, (α (i + 1) : ℝ) * (thetaR α z (i + 1) - mm (i + 1)) = thetaR α z i - mm i) :
    ∀ i ≥ i1, z (i + 1) - (Mseq α (i + 1) : ℤ) * mm i
      = z (i1 + 1) - (Mseq α (i1 + 1) : ℤ) * mm i1 := by
  have hα0 : ∀ i, 0 < α i := fun i => lt_of_lt_of_le (by norm_num) (hα i)
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => rfl
  | succ i hi ih =>
    rw [← ih]
    have h1 := h i hi
    have hM : (0 : ℝ) < Mseq α (i + 1) := by exact_mod_cast Mseq_pos hα0 (i + 1)
    have hαp : (0 : ℝ) < α (i + 1) := by exact_mod_cast hα0 (i + 1)
    have hMs : (Mseq α (i + 1 + 1) : ℝ) = α (i + 1) * Mseq α (i + 1) := by simp [Mseq]
    have e1 : thetaR α z i - mm i = ((z (i + 1) : ℝ) - Mseq α (i + 1) * mm i) / Mseq α (i + 1) := by
      unfold thetaR; field_simp
    have e2 : thetaR α z (i + 1) - mm (i + 1)
        = ((z (i + 1 + 1) : ℝ) - Mseq α (i + 1 + 1) * mm (i + 1)) / Mseq α (i + 1 + 1) := by
      unfold thetaR
      have : (Mseq α (i + 1 + 1) : ℝ) ≠ 0 := by rw [hMs]; positivity
      field_simp
    rw [e1, e2, hMs] at h1
    field_simp at h1
    have : (z (i + 1 + 1) : ℝ) - ((Mseq α (i + 1 + 1) : ℤ) : ℝ) * mm (i + 1)
        = (z (i + 1) : ℝ) - ((Mseq α (i + 1) : ℤ) : ℝ) * mm i := by
      push_cast; rw [hMs]; exact h1
    exact_mod_cast this

/-! ### Case II: infinitely many nonzero integer relations contradict continuity -/

lemma caseII_false {α : ℕ → ℕ} (hα : ∀ i, 2 ≤ α i) {z : ℕ → ℤ}
    (hz : ∀ k, (Mseq α k : ℤ) ∣ z (k + 1) - z k) {δ : ℝ} (hδ : 0 < δ) (hC : Cont α z δ)
    (mm : ℕ → ℤ) {i0 : ℕ} (hbig : ∀ i ≥ i0, 32 / δ ≤ α i)
    (hmm : ∀ i ≥ i0, |thetaR α z i - mm i| ≤ 2 / (δ * α i))
    (hinf : ∀ i1, ∃ i ≥ i1,
      (α (i + 1) : ℝ) * (thetaR α z (i + 1) - mm (i + 1)) ≠ thetaR α z i - mm i) :
    False := by
  have hα0 : ∀ i, 0 < α i := fun i => lt_of_lt_of_le (by norm_num) (hα i)
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, ∀ j, r j = thetaR α z j - mm j := ⟨_, fun _ => rfl⟩
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = δ / 16 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; positivity
  obtain ⟨p, hp⟩ : ∃ p : ℕ → Prop, ∀ k, p k ↔ (i0 < k ∧ (α k : ℝ) * r k ≠ r (k - 1)) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hpinf : (setOf p).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨i, hi, hne⟩ := hinf (max a i0)
    refine ⟨i + 1, ?_, by omega⟩
    show p (i + 1)
    rw [hp]
    refine ⟨by omega, ?_⟩
    simpa [hr] using hne
  -- bounds for the weights at levels in `p`
  have hbound : ∀ k, p k →
      (3 * η / 8 ≤ (⌊η * α k⌋₊ : ℝ) * |r k| ∧ (⌊η * α k⌋₊ : ℝ) * |r k| ≤ 1 / 8) := by
    intro k hk
    rw [hp] at hk
    obtain ⟨hk0, hne⟩ := hk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    have hi : i0 ≤ i := by omega
    obtain ⟨b, hb⟩ := theta_rel hα hz i mm
    rw [← hr, ← hr] at hb
    have hbne : b ≠ 0 := by
      intro h0
      apply hne
      simp only [Nat.add_sub_cancel]
      rw [h0] at hb
      simpa using sub_eq_zero.mp (by simpa using hb)
    have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by
      have : 1 ≤ |b| := Int.one_le_abs hbne
      exact_mod_cast this
    have hAi : (0 : ℝ) < α i := by exact_mod_cast hα0 i
    have hA : (0 : ℝ) < α (i + 1) := by exact_mod_cast hα0 (i + 1)
    have hbigi : δ * α i ≥ 32 := by
      have := (div_le_iff₀ hδ).mp (hbig i hi); linarith
    have hbigk : δ * α (i + 1) ≥ 32 := by
      have := (div_le_iff₀ hδ).mp (hbig (i + 1) (by omega)); linarith
    -- |r i| ≤ 1/16
    have hri : |r i| ≤ 1 / 16 := by
      rw [hr]
      refine (hmm i hi).trans ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hrk : |r (i + 1)| * (δ * α (i + 1)) ≤ 2 := by
      have := hmm (i + 1) (by omega)
      rw [← hr, le_div_iff₀ (by positivity)] at this
      exact this
    -- |α r| ≥ 3/4
    have hlow : 3 / 4 ≤ (α (i + 1) : ℝ) * |r (i + 1)| := by
      have h1 : (α (i + 1) : ℝ) * r (i + 1) = b + r i := by linarith
      have h2 : |(α (i + 1) : ℝ) * r (i + 1)| = α (i + 1) * |r (i + 1)| := by
        rw [abs_mul, abs_of_pos hA]
      rw [← h2, h1]
      have h4 := abs_sub_abs_le_abs_sub (b : ℝ) (-(r i))
      rw [abs_neg, sub_neg_eq_add] at h4
      linarith
    -- floor facts
    have hx2 : 2 ≤ η * α (i + 1) := by rw [hηdef]; nlinarith
    have hF1 : η * α (i + 1) / 2 ≤ (⌊η * α (i + 1)⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (η * α (i + 1)); linarith
    have hF2 : (⌊η * α (i + 1)⌋₊ : ℝ) ≤ η * α (i + 1) := Nat.floor_le (by positivity)
    constructor
    · have : (η * α (i + 1) / 2) * |r (i + 1)| ≤ (⌊η * α (i + 1)⌋₊ : ℝ) * |r (i + 1)| :=
        mul_le_mul_of_nonneg_right hF1 (abs_nonneg _)
      nlinarith
    · have h5 : (⌊η * α (i + 1)⌋₊ : ℝ) * |r (i + 1)| ≤ η * α (i + 1) * |r (i + 1)| :=
        mul_le_mul_of_nonneg_right hF2 (abs_nonneg _)
      have h6 : η * α (i + 1) * |r (i + 1)| = (η / δ) * (|r (i + 1)| * (δ * α (i + 1))) := by
        field_simp
      have hηδ : η / δ = 1 / 16 := by rw [hηdef]; field_simp
      rw [h6, hηδ] at h5
      nlinarith [hrk]
  -- enumerate the levels in `p`
  obtain ⟨kseq, hkseq⟩ : ∃ kseq : ℕ → ℕ, kseq = Nat.nth p := ⟨_, rfl⟩
  have hkp : ∀ j, p (kseq j) := by
    intro j; rw [hkseq]; exact Nat.nth_mem_of_infinite hpinf j
  have hkmono : StrictMono kseq := by rw [hkseq]; exact Nat.nth_strictMono hpinf
  obtain ⟨m, hm1, hm2⟩ := crossing
    (t := fun j => (⌊η * α (kseq j)⌋₊ : ℝ) * |r (kseq j)|) (c := 3 * η / 8)
    (by positivity) (fun j => (hbound _ (hkp j)).1) (fun j => (hbound _ (hkp j)).2)
  -- the digit string
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℤ, ∀ t, ρ t = if t ∈ (Finset.range m).image kseq then
      (if 0 ≤ r t then (1 : ℤ) else -1) * ((⌊η * α t⌋₊ : ℕ) : ℤ) else 0 := ⟨_, fun _ => rfl⟩
  have hF : ∀ t, (⌊η * α t⌋₊ : ℝ) ≤ η * α t := fun t => Nat.floor_le (by positivity)
  have hρb : ∀ t, |(ρ t : ℝ)| ≤ η * α t := by
    intro t
    rw [hρ t]
    split_ifs
    · push_cast; rw [one_mul, abs_of_nonneg (Nat.cast_nonneg _)]; exact hF t
    · push_cast; rw [neg_one_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]; exact hF t
    · simp; positivity
  have hball : ∀ n ≤ kseq m, ∃ N : ℤ,
      |((((Mseq α n : ℚ) * xval α ρ (kseq m) : ℚ)) : ℝ) - N| < δ := by
    intro n hn
    obtain ⟨N, hN⟩ := digit_int hα0 ρ hn
    refine ⟨N, ?_⟩
    have e : ((((Mseq α n : ℚ) * xval α ρ (kseq m) : ℚ)) : ℝ) - N
        = ((wval α ρ (kseq m) n : ℚ) : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) hN
      simp only [Rat.cast_sub, Rat.cast_intCast] at this
      linarith
    rw [e]
    have := digit_bound hα ρ hη0.le hρb hn
    rw [hηdef] at this
    linarith
  obtain ⟨n, hn⟩ := hC (kseq m) ρ hball
  have hsub : (Finset.range m).image kseq ⊆ Finset.range (kseq m) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hkmono (Finset.mem_range.mp hj))
  have hchi : chi α z ρ (kseq m) =
      (∑ j ∈ Finset.range (kseq m), (ρ j : ℝ) * r j)
        + ((∑ j ∈ Finset.range (kseq m), ρ j * mm j : ℤ) : ℝ) := by
    unfold chi
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hr]; unfold thetaR; ring
  have hsum : ∑ j ∈ Finset.range (kseq m), (ρ j : ℝ) * r j
      = ∑ i ∈ Finset.range m, (⌊η * α (kseq i)⌋₊ : ℝ) * |r (kseq i)| := by
    rw [← Finset.sum_subset hsub (f := fun j => (ρ j : ℝ) * r j)
      (fun x _ hx => by simp [hρ x, hx])]
    rw [Finset.sum_image (fun x _ y _ h => hkmono.injective h)]
    apply Finset.sum_congr rfl
    intro i hi
    have hmem : kseq i ∈ (Finset.range m).image kseq := Finset.mem_image_of_mem _ hi
    rw [hρ, if_pos hmem]
    by_cases hnn : 0 ≤ r (kseq i)
    · rw [if_pos hnn, abs_of_nonneg hnn]; push_cast; ring
    · rw [if_neg hnn, abs_of_neg (not_le.mp hnn)]; push_cast; ring
  rw [hchi, hsum] at hn
  obtain ⟨S, hS⟩ : ∃ S : ℤ, S = ∑ j ∈ Finset.range (kseq m), ρ j * mm j := ⟨_, rfl⟩
  rw [← hS] at hn
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ i ∈ Finset.range m, (⌊η * α (kseq i)⌋₊ : ℝ) * |r (kseq i)| :=
    ⟨_, rfl⟩
  rw [← hT] at hn hm1 hm2
  have h6 : |T - ((n - S : ℤ) : ℝ)| < 1 / 4 := by
    have : T - ((n - S : ℤ) : ℝ) = T + (S : ℝ) - n := by push_cast; ring
    rw [this]; exact hn
  rw [abs_lt] at h6
  have hk1 : (0 : ℝ) < ((n - S : ℤ) : ℝ) := by linarith [h6.2]
  have hk2 : ((n - S : ℤ) : ℝ) < 1 := by linarith [h6.1]
  have hk1' : (0 : ℤ) < n - S := by exact_mod_cast hk1
  have hk2' : n - S < 1 := by exact_mod_cast hk2
  omega

/-! ### The dichotomy: a `δ`-continuous profinite integer is an ordinary integer -/

theorem case_dichotomy {α : ℕ → ℕ} (hα : ∀ i, 2 ≤ α i)
    (hlarge : ∀ A : ℝ, ∃ i0 : ℕ, ∀ i ≥ i0, A ≤ α i)
    {z : ℕ → ℤ} (hz : ∀ k, (Mseq α k : ℤ) ∣ z (k + 1) - z k) {δ : ℝ} (hδ : 0 < δ)
    (hC : Cont α z δ) :
    ∃ (u : ℤ) (i1 : ℕ), ∀ i ≥ i1, (Mseq α (i + 1) : ℤ) ∣ z (i + 1) - u := by
  obtain ⟨i0, hi0⟩ := hlarge (32 / δ)
  have step : ∀ i ≥ i0, ∃ m : ℤ, |thetaR α z i - m| ≤ 2 / (δ * α i) := by
    intro i hi
    have h8 : 8 / δ ≤ α i := by
      refine le_trans ?_ (hi0 i hi)
      exact div_le_div_of_nonneg_right (by norm_num) hδ.le
    exact step1 hα hδ hC h8
  choose! mm hmm using step
  by_cases hI : ∃ i1 ≥ i0, ∀ i ≥ i1,
      (α (i + 1) : ℝ) * (thetaR α z (i + 1) - mm (i + 1)) = thetaR α z i - mm i
  · obtain ⟨i1, _, h⟩ := hI
    have key := caseI hα mm h
    refine ⟨z (i1 + 1) - (Mseq α (i1 + 1) : ℤ) * mm i1, i1, fun i hi => ?_⟩
    have := key i hi
    exact ⟨mm i, by linarith⟩
  · exfalso
    have hI' : ∀ i1, ∃ i ≥ i1,
        (α (i + 1) : ℝ) * (thetaR α z (i + 1) - mm (i + 1)) ≠ thetaR α z i - mm i := by
      intro i1
      by_contra hcon
      apply hI
      refine ⟨max i1 i0, le_max_right _ _, fun i hi => ?_⟩
      by_contra h
      exact hcon ⟨i, le_trans (le_max_left _ _) hi, h⟩
    exact caseII_false hα hz hδ hC mm hi0 hmm hI'

end LeanCheck
