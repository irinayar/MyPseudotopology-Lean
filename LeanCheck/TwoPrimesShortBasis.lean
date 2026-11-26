import Mathlib
import LeanCheck.TwoPrimesEffective
import LeanCheck.TwoPrimesWitnessLarge

/-!
# A short lattice basis gives witnesses

`witness_of_short_basis`: digits of two coprime bases `q`, `p`, with `u = q^(s^2)`; a nonsingular
integer matrix whose rows lie in the congruence lattice of the digit weights modulo `u`, with column
sums at most `ρ (2 J j + 1)`, where `J j = ⌊ℓ^(2n-1)/D⌋ ≥ 1` for the digit number `n` of `ℓ`.  Then
every `a` with `|a| + 3ρ p^(r^2)/D < 3ρ q^((s+1)^2)/D` has a witness at the radius `3ρ/D`.
-/

namespace TwoPrimesShortBasis

open Finset Matrix TwoPrimesEffective

/-- A number which differs from `y` by a multiple of the modulus is within `|y| / M` of an
integer. -/
lemma dist_le (x y : ℤ) (M : ℕ) (hM : 0 < M) (h : (M : ℤ) ∣ x - y) :
    |(x : ℝ) / M - round ((x : ℝ) / M)| ≤ |(y : ℝ)| / M := by
  obtain ⟨q, hq⟩ := h
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have e : (x : ℝ) / M = (y : ℝ) / M + (q : ℝ) := by
    have h1 : x = y + (M : ℤ) * q := by omega
    rw [h1]
    push_cast
    field_simp
  refine le_trans (round_le _ q) (le_of_eq ?_)
  rw [e, add_sub_cancel_right, abs_div, abs_of_pos hMr]

theorem witness_of_short_basis {h p q s r D : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hpq : Nat.Coprime p q) (hD : 1 ≤ D) {ρ : ℝ} (hρ : 0 < ρ)
    (base num : Fin h → ℕ) (hinj : Function.Injective fun j => (base j, num j))
    (hbase : ∀ j, base j = p ∨ base j = q) (hnum : ∀ j, 1 ≤ num j)
    (hnq : ∀ j, base j = q → num j ≤ s) (hnp : ∀ j, base j = p → num j ≤ r)
    (hJ : ∀ j, 1 ≤ base j ^ (2 * num j - 1) / D) (hp0 : ∃ j, base j = p)
    (B : Matrix (Fin h) (Fin h) ℤ) (hdet : B.det ≠ 0)
    (hrow : ∀ i, (q : ℤ) ^ (s ^ 2) ∣ ∑ j, B i j * (base j : ℤ) ^ ((num j - 1) ^ 2))
    (hcol : ∀ j, ((∑ i, |B i j| : ℤ) : ℝ) ≤ ρ * (2 * ((base j ^ (2 * num j - 1) / D : ℕ) : ℝ) + 1))
    (a : ℤ) (ha : |(a : ℝ)| + 3 * ρ * (p : ℝ) ^ (r ^ 2) / D
      < 3 * ρ * (q : ℝ) ^ ((s + 1) ^ 2) / D) :
    ∃ k : ℤ, |((k - a : ℤ) : ℝ)| ≤ 3 * ρ * (p : ℝ) ^ (r ^ 2) / D ∧
      Small q (3 * ρ / D) k ∧ Small p (3 * ρ / D) (k - a) := by
  classical
  have hne : p ≠ q := by
    intro e
    rw [e, Nat.coprime_self] at hpq
    omega
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  set w : Fin h → ℤ := fun j => (base j : ℤ) ^ ((num j - 1) ^ 2) with hw
  set u : ℤ := (q : ℤ) ^ (s ^ 2) with hu
  -- rounding
  obtain ⟨j0, hj0⟩ := hp0
  have hco : IsCoprime (w j0) u := by
    have h1 : Nat.Coprime (p ^ ((num j0 - 1) ^ 2)) (q ^ (s ^ 2)) := Nat.Coprime.pow _ _ hpq
    have h2 := Nat.Coprime.isCoprime h1
    rw [Nat.cast_pow, Nat.cast_pow] at h2
    simpa [hw, hu, hj0] using h2
  obtain ⟨α, β, hαβ⟩ := hco
  have hzsum : u ∣ (∑ j, (Pi.single j0 (α * a) : Fin h → ℤ) j * w j) - a := by
    have e : ∑ j, (Pi.single j0 (α * a) : Fin h → ℤ) j * w j = α * a * w j0 := by
      rw [sum_eq_single j0]
      · rw [Pi.single_eq_same]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_mul]
      · intro h'
        exact absurd (mem_univ _) h'
    rw [e]
    exact ⟨-(β * a), by linear_combination a * hαβ⟩
  obtain ⟨d, hd, hbound⟩ := TwoPrimesWitnessLarge.rounding B w _ u a hrow hdet hzsum
  -- the size of the digits
  have hdig : ∀ j, |(d j : ℝ)| ≤ 3 * ρ / (2 * D) * (base j : ℝ) ^ (2 * num j - 1) := by
    intro j
    set J : ℕ := base j ^ (2 * num j - 1) / D with hJdef
    have h1 : (2 : ℝ) * |(d j : ℝ)| ≤ ((∑ i, |B i j| : ℤ) : ℝ) := by exact_mod_cast hbound j
    have h2 := le_trans h1 (hcol j)
    have h3 : (1 : ℝ) ≤ J := by exact_mod_cast hJ j
    have h4 : (J : ℝ) * D ≤ (base j : ℝ) ^ (2 * num j - 1) := by
      exact_mod_cast Nat.div_mul_le_self (base j ^ (2 * num j - 1)) D
    have h5 : ρ * (2 * (J : ℝ) + 1) ≤ ρ * (3 * J) := mul_le_mul_of_nonneg_left (by linarith) hρ.le
    have h6 : (J : ℝ) ≤ (base j : ℝ) ^ (2 * num j - 1) / D := by
      rw [le_div_iff₀ hD0]; exact h4
    have h7 := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ 3 * ρ)
    have e : 3 * ρ / (2 * D) * (base j : ℝ) ^ (2 * num j - 1)
        = 3 * ρ * ((base j : ℝ) ^ (2 * num j - 1) / D) / 2 := by
      field_simp
    rw [e]
    linarith
  -- sums of digits of one prime up to a level
  set low : ℕ → ℕ → ℤ := fun l m => ∑ j, if base j = l ∧ num j ≤ m then d j * w j else 0
    with hlowdef
  have hlow : ∀ l m, 2 ≤ l → |((low l m : ℤ) : ℝ)| < 3 * ρ / D * (l : ℝ) ^ (m ^ 2) := by
    intro l m hl
    set S : Finset (Fin h) := univ.filter fun j => base j = l ∧ num j ≤ m with hS
    have e0 : low l m = ∑ j ∈ S, d j * w j := by
      rw [hlowdef, hS, sum_filter]
    have h1 : |((low l m : ℤ) : ℝ)| ≤ ∑ j ∈ S, 3 * ρ / (2 * D) * (l : ℝ) ^ (num j ^ 2) := by
      rw [e0, Int.cast_sum]
      refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun j hj => ?_)
      have hj' := (mem_filter.mp hj).2
      have ew : ((w j : ℤ) : ℝ) = (l : ℝ) ^ ((num j - 1) ^ 2) := by
        simp only [hw, hj'.1]
        push_cast
        ring
      rw [Int.cast_mul, abs_mul, ew, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ ((num j - 1) ^ 2))]
      have h2 := mul_le_mul_of_nonneg_right (hdig j)
        (by positivity : (0 : ℝ) ≤ (l : ℝ) ^ ((num j - 1) ^ 2))
      refine le_trans h2 (le_of_eq ?_)
      have e1 : num j ^ 2 = (2 * num j - 1) + (num j - 1) ^ 2 := by
        obtain ⟨n, hn⟩ : ∃ n, num j = n + 1 := ⟨num j - 1, by have := hnum j; omega⟩
        rw [hn, show 2 * (n + 1) - 1 = 2 * n + 1 by omega, show n + 1 - 1 = n by omega]
        ring
      rw [e1, pow_add, hj'.1]
      ring
    have h3 : ∑ j ∈ S, (l : ℝ) ^ (num j ^ 2) ≤ ∑ n ∈ range m, (l : ℝ) ^ ((n + 1) ^ 2) := by
      have hinjS : Set.InjOn (fun j => num j - 1) S := by
        intro x hx y hy hxy
        have hx' := (mem_filter.mp hx).2
        have hy' := (mem_filter.mp hy).2
        refine hinj (Prod.ext ?_ ?_)
        · exact hx'.1.trans hy'.1.symm
        · have := hnum x
          have := hnum y
          simp only at hxy ⊢
          omega
      have e1 : ∑ j ∈ S, (l : ℝ) ^ (num j ^ 2)
          = ∑ n ∈ S.image (fun j => num j - 1), (l : ℝ) ^ ((n + 1) ^ 2) := by
        rw [sum_image hinjS]
        refine sum_congr rfl fun j _ => ?_
        have := hnum j
        rw [show num j - 1 + 1 = num j by omega]
      rw [e1]
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
      intro n hn
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
      have hj' := (mem_filter.mp hj).2
      have := hnum j
      exact mem_range.mpr (by omega)
    have h4 : ∑ n ∈ range m, (l : ℝ) ^ ((n + 1) ^ 2) < 2 * (l : ℝ) ^ (m ^ 2) := by
      exact_mod_cast sum_levels hl m
    have hc : (0 : ℝ) < 3 * ρ / (2 * D) := by positivity
    refine lt_of_le_of_lt h1 ?_
    rw [← mul_sum]
    have h5 := mul_lt_mul_of_pos_left (lt_of_le_of_lt h3 h4) hc
    refine lt_of_lt_of_le h5 (le_of_eq ?_)
    field_simp
  -- the two sides
  set side : ℕ → ℤ := fun l => ∑ j, if base j = l then d j * w j else 0 with hsidedef
  have hsides : ∑ j, d j * w j = side p + side q := by
    simp only [hsidedef]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rcases hbase j with h' | h'
    · rw [ite_eq_left h', ite_eq_right (by rw [h']; exact hne), add_zero]
    · rw [ite_eq_right (by rw [h']; exact Ne.symm hne), ite_eq_left h', zero_add]
  have hsplit : ∀ l m : ℕ, (l : ℤ) ^ (m ^ 2) ∣ side l - low l m := by
    intro l m
    simp only [hsidedef, hlowdef]
    rw [← sum_sub_distrib]
    refine dvd_sum fun j _ => ?_
    by_cases hb : base j = l
    · by_cases hm : num j ≤ m
      · rw [ite_eq_left hb, ite_eq_left ⟨hb, hm⟩, sub_self]
        exact dvd_zero _
      · rw [ite_eq_left hb, ite_eq_right (fun c => hm c.2), sub_zero]
        refine Dvd.dvd.mul_left ?_ _
        simp only [hw, hb]
        exact pow_dvd_pow _ (Nat.pow_le_pow_left (by omega) 2)
    · rw [ite_eq_right hb, ite_eq_right (fun c => hb c.1), sub_self]
      exact dvd_zero _
  have hfullp : side p = low p r := by
    simp only [hsidedef, hlowdef]
    refine sum_congr rfl fun j _ => ?_
    by_cases hb : base j = p
    · rw [ite_eq_left hb, ite_eq_left ⟨hb, hnp j hb⟩]
    · rw [ite_eq_right hb, ite_eq_right (fun c => hb c.1)]
  have hfullq : side q = low q s := by
    simp only [hsidedef, hlowdef]
    refine sum_congr rfl fun j _ => ?_
    by_cases hb : base j = q
    · rw [ite_eq_left hb, ite_eq_left ⟨hb, hnq j hb⟩]
    · rw [ite_eq_right hb, ite_eq_right (fun c => hb c.1)]
  have hsmall : ∀ (l : ℕ), 2 ≤ l → ∀ (m : ℕ) (x : ℤ),
      (l : ℤ) ^ (m ^ 2) ∣ x - low l m ∨ (l : ℤ) ^ (m ^ 2) ∣ x - -low l m →
      |(x : ℝ) / (l : ℝ) ^ (m ^ 2) - round ((x : ℝ) / (l : ℝ) ^ (m ^ 2))| < 3 * ρ / D := by
    intro l hl m x hx
    have hpos : 0 < l ^ (m ^ 2) := pow_pos (by omega) _
    obtain ⟨y, hy, hxy⟩ : ∃ y : ℤ, |(y : ℝ)| < 3 * ρ / D * (l : ℝ) ^ (m ^ 2)
        ∧ (l : ℤ) ^ (m ^ 2) ∣ x - y := by
      rcases hx with h' | h'
      · exact ⟨_, hlow l m hl, h'⟩
      · refine ⟨-low l m, ?_, h'⟩
        rw [Int.cast_neg, abs_neg]
        exact hlow l m hl
    have h1 := dist_le x y (l ^ (m ^ 2)) hpos (by rw [Nat.cast_pow]; exact hxy)
    rw [Nat.cast_pow] at h1
    refine lt_of_le_of_lt h1 ?_
    rw [div_lt_iff₀ (by positivity)]
    exact hy
  -- assembly
  set k : ℤ := a - side p with hk
  have hzabs : |((side p : ℤ) : ℝ)| < 3 * ρ * (p : ℝ) ^ (r ^ 2) / D := by
    rw [hfullp]
    refine lt_of_lt_of_le (hlow p r hp) (le_of_eq ?_)
    ring
  have hcong : u ∣ k - side q := by
    have h1 := hd
    rw [hsides] at h1
    have e : k - side q = -(side p + side q - a) := by rw [hk]; ring
    rw [e]
    exact h1.neg_right
  have hka : k - a = -side p := by rw [hk]; ring
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [hka, Int.cast_neg, abs_neg]
    exact hzabs.le
  · intro m
    by_cases hm : m ≤ s
    · refine hsmall q hq m k (Or.inl ?_)
      have h1 : (q : ℤ) ^ (m ^ 2) ∣ k - side q :=
        dvd_trans (pow_dvd_pow _ (Nat.pow_le_pow_left hm 2)) hcong
      have h2 := dvd_add h1 (hsplit q m)
      have e : k - side q + (side q - low q m) = k - low q m := by ring
      rwa [e] at h2
    · have hpos : (0 : ℝ) < (q : ℝ) ^ (m ^ 2) := by positivity
      have h1 := dist_le k k (q ^ (m ^ 2)) (pow_pos (by omega) _) (by simp)
      rw [Nat.cast_pow] at h1
      refine lt_of_le_of_lt h1 ?_
      have h2 : |(k : ℝ)| ≤ |(a : ℝ)| + 3 * ρ * (p : ℝ) ^ (r ^ 2) / D := by
        rw [hk, Int.cast_sub]
        refine le_trans (abs_sub _ _) ?_
        have := hzabs.le
        linarith
      have h3 : (q : ℝ) ^ ((s + 1) ^ 2) ≤ (q : ℝ) ^ (m ^ 2) :=
        pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ q))
          (Nat.pow_le_pow_left (by omega) 2)
      have h4 : 3 * ρ * (q : ℝ) ^ ((s + 1) ^ 2) / D ≤ 3 * ρ / D * (q : ℝ) ^ (m ^ 2) := by
        have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 3 * ρ / D)
        refine le_trans (le_of_eq ?_) h5
        ring
      rw [div_lt_iff₀ hpos]
      linarith
  · intro m
    refine hsmall p hp m (k - a) (Or.inr ?_)
    rw [hka]
    have e : -side p - -low p m = -(side p - low p m) := by ring
    rw [e]
    exact (hsplit p m).neg_right

end TwoPrimesShortBasis
