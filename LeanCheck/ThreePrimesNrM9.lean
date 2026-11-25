import LeanCheck.ThreePrimesExactM5
import LeanCheck.ThreePrimesPackingM8

/-!
# ThreePrimesNrM9: the criterion for `N_r` stated for prime-square ball elements

Connects the lattice statements of `ThreePrimesPackingM8` with the ball `InBall S (1/m)`.
For a set `S` of integers `≥ 2`, exponents `a`, `D = ∏ p^(a p²)` and a real height `T`, the retained
coordinates are `retNrM9 S a m T = {(p,n) : n > a p, p^(n²) < m D T}`.

* `pn_lt_of_retained`: if `s / (m T) < c` and every retained coordinate of `D s` is `< c`, then
  `P_p(D s) < c` for all `p ∈ S` (the coordinates `n ≤ a p` vanish, the omitted ones are `≤ s/(mT)`).
* `ball_of_box`: a box vector of the lattice with `r ∤ s` gives a ball element `D s < D T` with `r ∤ D s`.
* `nr_sharp_ball`, `nr_two_ball`: the criterion with a lower bound `lam` for the gauge of the nonzero
  lattice vectors (in particular the first minimum).
* `nr_eps_ball`: if `P_S(D s) ≥ eps` for all `0 < s < T` and `2 ≤ T eps^c`, then there is a ball element
  `D s < D T` not divisible by `r`.
* `nrcrit_ball`: the same conclusion from `T > (c+1) r eps^(-c) / 2` when `(c+1) r ≥ 4`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- The retained coordinates at the real height `T`: `n > a p` and `p^(n²) < m D T`. -/
noncomputable def retNrM9 (S : Finset ℕ) (a : ℕ → ℕ) (m : ℕ) (T : ℝ) : Finset (ℕ × ℕ) :=
  (CCset S a m ⌈T⌉₊).filter (fun x => ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ) < m * Dprod S a * T)

lemma mem_retNrM9 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (m : ℕ) (T : ℝ) (p n : ℕ) :
    (p, n) ∈ retNrM9 S a m T ↔ p ∈ S ∧ a p < n ∧ ((p ^ (n ^ 2) : ℕ) : ℝ) < m * Dprod S a * T := by
  unfold retNrM9
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨h, hlt⟩
    unfold CCset at h
    rw [Finset.mem_filter, Finset.mem_product] at h
    exact ⟨h.1.1, h.2.1, hlt⟩
  · rintro ⟨hp, han, hlt⟩
    refine ⟨mem_ccset (hS p hp) hp han ?_, hlt⟩
    have h1 : ((p ^ (n ^ 2) : ℕ) : ℝ) ≤ ((m * Dprod S a * ⌈T⌉₊ : ℕ) : ℝ) := by
      refine le_trans hlt.le ?_
      rw [Nat.cast_mul (m * Dprod S a), Nat.cast_mul m]
      exact mul_le_mul_of_nonneg_left (Nat.le_ceil T) (by positivity)
    exact_mod_cast h1

lemma dprod_pos {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) : 0 < Dprod S a := by
  unfold Dprod
  apply Finset.prod_pos
  intro p hp
  have := hS p hp
  positivity

/-- `‖x‖ ≤ |x - j|` for every integer `j`. -/
lemma nrm_le_sub_int (x : ℝ) (j : ℤ) : nrm x ≤ |x - j| := by
  rw [nrm_eq]; exact round_le x j

/-- All coordinates of `D s` are `< c` once the retained ones are and `s / (m T) < c`. -/
theorem pn_lt_of_retained {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (T : ℝ) (hT : 0 < T) (s : ℤ) (hs : 0 ≤ s) (c : ℝ) (htail : (s : ℝ) / (m * T) < c)
    (hret : ∀ x ∈ retNrM9 S a m T,
      nrm (((Dprod S a : ℤ) * s : ℤ) / ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ)) < c) :
    ∀ p ∈ S, Pn (sqScales p) ((Dprod S a : ℤ) * s) < c := by
  intro p hp
  have hp2 := hS p hp
  have hDpos := dprod_pos hS a
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hD0 : (0 : ℝ) < Dprod S a := by exact_mod_cast hDpos
  have hs0 : (0 : ℝ) ≤ s := by exact_mod_cast hs
  have hB0 : 0 ≤ (s : ℝ) / (m * T) := div_nonneg hs0 (by positivity)
  have hc0 : 0 < c := lt_of_le_of_lt hB0 htail
  have hqpos : ∀ n : ℕ, (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := fun n => by
    exact_mod_cast pow_pos (by omega : 0 < p) _
  have big : ∀ n : ℕ, (m : ℝ) * Dprod S a * T ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) →
      nrm ((((Dprod S a : ℤ) * s : ℤ) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) ≤ (s : ℝ) / (m * T) := by
    intro n hn
    refine (nrm_le_abs _).trans ?_
    have hk0 : (0 : ℝ) ≤ (((Dprod S a : ℤ) * s : ℤ) : ℝ) := by
      push_cast; exact mul_nonneg hD0.le hs0
    rw [abs_of_nonneg (div_nonneg hk0 (hqpos n).le), div_le_div_iff₀ (hqpos n) (by positivity)]
    have e : (((Dprod S a : ℤ) * s : ℤ) : ℝ) * (m * T) = (s : ℝ) * ((m : ℝ) * Dprod S a * T) := by
      push_cast; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hn hs0
  refine Pn_sq_lt p _ ⌈(m : ℝ) * Dprod S a * T⌉₊ htail ?_ ?_
  · intro n _ _
    by_cases han : n ≤ a p
    · have hdvd1 : p ^ (n ^ 2) ∣ Dprod S a := by
        calc p ^ (n ^ 2) ∣ p ^ (a p ^ 2) := pow_dvd_pow p (Nat.pow_le_pow_left han 2)
          _ ∣ Dprod S a := Finset.dvd_prod_of_mem (fun p => p ^ (a p ^ 2)) hp
      have hdvd : ((p ^ (n ^ 2) : ℕ) : ℤ) ∣ (Dprod S a : ℤ) * s :=
        Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hdvd1) s
      obtain ⟨z, hz⟩ := hdvd
      have hne : ((p ^ (n ^ 2) : ℕ) : ℝ) ≠ 0 := (hqpos n).ne'
      have hkz : ((((Dprod S a : ℤ) * s : ℤ) : ℝ)) / ((p ^ (n ^ 2) : ℕ) : ℝ) = (z : ℝ) := by
        rw [hz, Int.cast_mul, Int.cast_natCast]
        field_simp
      rw [hkz, nrm_int]
      exact hc0
    · by_cases hq : ((p ^ (n ^ 2) : ℕ) : ℝ) < m * Dprod S a * T
      · exact hret (p, n) ((mem_retNrM9 hS a m T p n).mpr ⟨hp, by omega, hq⟩)
      · exact lt_of_le_of_lt (big n (not_lt.mp hq)) htail
  · intro n hn
    refine big n ?_
    have h1 : n < p ^ (n ^ 2) := n_lt_pow_sq hp2 n
    have h2 : ⌈(m : ℝ) * Dprod S a * T⌉₊ ≤ p ^ (n ^ 2) := by omega
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h2)

/-- A box vector with `r ∤ s` gives a ball element `D s` with `0 < s < T` and `r ∤ D s`. -/
theorem ball_of_box {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (T : ℝ) (hT : 0 < T) (r : ℤ) (hcop : IsCoprime r (Dprod S a : ℤ))
    (h : ∃ s : ℤ, ¬ r ∣ s ∧ |(s : ℝ)| < T ∧ ∀ x ∈ retNrM9 S a m T, ∃ j : ℤ,
      (m : ℝ) * |(Dprod S a : ℝ) * s - j * ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ)| < ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ)) :
    ∃ s : ℤ, 0 < s ∧ (s : ℝ) < T ∧ ¬ r ∣ (Dprod S a : ℤ) * s ∧
      InBall S (1 / (m : ℝ)) ((Dprod S a : ℤ) * s) := by
  obtain ⟨s, hrs, hsT, hbox⟩ := h
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs0 : s ≠ 0 := fun h => hrs (h ▸ dvd_zero r)
  have habs : ((|s| : ℤ) : ℝ) = |(s : ℝ)| := Int.cast_abs
  have hrabs : ¬ r ∣ |s| := fun h => hrs ((dvd_abs r s).mp h)
  refine ⟨|s|, abs_pos.mpr hs0, by rw [habs]; exact hsT,
    fun h => hrabs (hcop.dvd_of_dvd_mul_left h), ?_⟩
  refine pn_lt_of_retained hS a m hm T hT |s| (abs_nonneg s) _ ?_ ?_
  · rw [habs, div_lt_div_iff₀ (by positivity) hm0]
    nlinarith
  · intro x hx
    obtain ⟨j, hj⟩ := hbox x hx
    have hxS := (mem_retNrM9 hS a m T x.1 x.2).mp hx
    have hq : (0 : ℝ) < ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ) := by
      have := hS x.1 hxS.1
      exact_mod_cast pow_pos (by omega : 0 < x.1) _
    set q : ℝ := ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ) with hqdef
    -- the sign of `s` passes to the integer `j`
    obtain ⟨j', hj'⟩ : ∃ j' : ℤ, |(Dprod S a : ℝ) * |(s : ℝ)| - j' * q|
        = |(Dprod S a : ℝ) * s - j * q| := by
      rcases abs_cases (s : ℝ) with ⟨he, _⟩ | ⟨he, _⟩
      · exact ⟨j, by rw [he]⟩
      · refine ⟨-j, ?_⟩
        rw [he, ← abs_neg]
        congr 1
        push_cast; ring
    refine lt_of_le_of_lt (nrm_le_sub_int _ j') ?_
    have e : ((((Dprod S a : ℤ) * |s| : ℤ)) : ℝ) / q - j'
        = ((Dprod S a : ℝ) * |(s : ℝ)| - j' * q) / q := by
      rw [Int.cast_mul, Int.cast_natCast, habs]
      field_simp
    rw [e, abs_div, abs_of_pos hq, hj', div_lt_div_iff₀ hq hm0]
    linarith

/-- The retained moduli listed by `Fin`, as integers. -/
noncomputable def qNrM9 (C : Finset (ℕ × ℕ)) (i : Fin C.card) : ℤ :=
  (((C.equivFin.symm i).1.1 ^ ((C.equivFin.symm i).1.2 ^ 2) : ℕ) : ℤ)

lemma qNrM9_cast (C : Finset (ℕ × ℕ)) (i : Fin C.card) :
    (qNrM9 C i : ℝ) = (((C.equivFin.symm i).1.1 ^ ((C.equivFin.symm i).1.2 ^ 2) : ℕ) : ℝ) := by
  unfold qNrM9; rw [Int.cast_natCast]

lemma qNrM9_pos {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (m : ℕ) (T : ℝ)
    (i : Fin (retNrM9 S a m T).card) : 0 < qNrM9 (retNrM9 S a m T) i := by
  unfold qNrM9
  have hx := ((retNrM9 S a m T).equivFin.symm i).2
  have := hS _ ((mem_retNrM9 hS a m T _ _).mp hx).1
  exact_mod_cast pow_pos (lt_of_lt_of_le two_pos this) _

/-- From the `Fin`-indexed box of `ThreePrimesPackingM8` to the box over the retained coordinates. -/
lemma box_of_fin (C : Finset (ℕ × ℕ)) (D : ℕ) (m : ℕ) (s : ℤ)
    (h : ∀ i : Fin C.card, ∃ j : ℤ,
      (m : ℝ) * |((D : ℤ) : ℝ) * s - j * qNrM9 C i| < qNrM9 C i) :
    ∀ x ∈ C, ∃ j : ℤ, (m : ℝ) * |(D : ℝ) * s - j * ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ)|
      < ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ) := by
  intro x hx
  obtain ⟨j, hj⟩ := h (C.equivFin ⟨x, hx⟩)
  refine ⟨j, ?_⟩
  rw [qNrM9_cast, Equiv.symm_apply_apply, Int.cast_natCast] at hj
  exact hj

/-- **Sharp form.** `lam` is a lower bound for the gauge of the nonzero vectors of the witness lattice;
`m^c / T < ⌊1/lam⌋ lam^(c+1)` gives a ball element `D s < D T` not divisible by `r`. -/
theorem nr_sharp_ball {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (T : ℝ) (hT : 0 < T) (r : ℤ) (hr : ¬ r ∣ 1) (hcop : IsCoprime r (Dprod S a : ℤ))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ s : ℤ, ∀ j : ℕ × ℕ → ℤ, (s ≠ 0 ∨ ∃ x ∈ retNrM9 S a m T, j x ≠ 0) →
      lam ≤ |(s : ℝ)| / T ∨ ∃ x ∈ retNrM9 S a m T,
        lam ≤ m * |(Dprod S a : ℝ) * s - j x * ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ)|
          / ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ))
    (hcrit : (m : ℝ) ^ (retNrM9 S a m T).card / T
      < (⌊1 / lam⌋₊ : ℝ) * lam ^ ((retNrM9 S a m T).card + 1)) :
    ∃ s : ℤ, 0 < s ∧ (s : ℝ) < T ∧ ¬ r ∣ (Dprod S a : ℤ) * s ∧
      InBall S (1 / (m : ℝ)) ((Dprod S a : ℤ) * s) := by
  classical
  set C := retNrM9 S a m T with hC
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmin' : ∀ s : ℤ, ∀ j : Fin C.card → ℤ, (s ≠ 0 ∨ j ≠ 0) →
      lam ≤ |(s : ℝ)| / T ∨ ∃ i, lam ≤ (m : ℝ) * |(((Dprod S a : ℤ)) : ℝ) * s - j i * qNrM9 C i|
        / qNrM9 C i := by
    intro s j hne
    set J : ℕ × ℕ → ℤ := fun x => if h : x ∈ C then j (C.equivFin ⟨x, h⟩) else 0 with hJ
    have hJi : ∀ i : Fin C.card, J (C.equivFin.symm i).1 = j i := by
      intro i
      simp only [hJ, dite_eq_left (C.equivFin.symm i).2, Subtype.coe_eta, Equiv.apply_symm_apply]
    have hne' : s ≠ 0 ∨ ∃ x ∈ C, J x ≠ 0 := by
      rcases hne with h | h
      · exact Or.inl h
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
        exact Or.inr ⟨_, (C.equivFin.symm i).2, by rw [hJi]; simpa using hi⟩
    rcases hmin s J hne' with h | ⟨x, hx, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨C.equivFin ⟨x, hx⟩, ?_⟩
      rw [qNrM9_cast, Equiv.symm_apply_apply, Int.cast_natCast]
      have e : J x = j (C.equivFin ⟨x, hx⟩) := by simp only [hJ, dite_eq_left hx]
      rwa [e] at h
  obtain ⟨s, j, hrs, hsT, hbox⟩ := nr_sharp C.card (qNrM9 C) (Dprod S a : ℤ) m T hm0 hT
    (qNrM9_pos hS a m T) r hr lam hlam hmin' hcrit
  exact ball_of_box hS a m hm T hT r hcop
    ⟨s, hrs, hsT, box_of_fin C (Dprod S a) m s fun i => ⟨j i, hbox i⟩⟩

/-- **The form `T ≥ 2 (m/lam)^c`.** -/
theorem nr_two_ball {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (T : ℝ) (hT : 0 < T) (r : ℤ) (hr : ¬ r ∣ 1) (hcop : IsCoprime r (Dprod S a : ℤ))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ s : ℤ, ∀ j : ℕ × ℕ → ℤ, (s ≠ 0 ∨ ∃ x ∈ retNrM9 S a m T, j x ≠ 0) →
      lam ≤ |(s : ℝ)| / T ∨ ∃ x ∈ retNrM9 S a m T,
        lam ≤ m * |(Dprod S a : ℝ) * s - j x * ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ)|
          / ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ))
    (hcrit : 2 * (m : ℝ) ^ (retNrM9 S a m T).card ≤ T * lam ^ (retNrM9 S a m T).card) :
    ∃ s : ℤ, 0 < s ∧ (s : ℝ) < T ∧ ¬ r ∣ (Dprod S a : ℤ) * s ∧
      InBall S (1 / (m : ℝ)) ((Dprod S a : ℤ) * s) := by
  classical
  set C := retNrM9 S a m T with hC
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmin' : ∀ s : ℤ, ∀ j : Fin C.card → ℤ, (s ≠ 0 ∨ j ≠ 0) →
      lam ≤ |(s : ℝ)| / T ∨ ∃ i, lam ≤ (m : ℝ) * |(((Dprod S a : ℤ)) : ℝ) * s - j i * qNrM9 C i|
        / qNrM9 C i := by
    intro s j hne
    set J : ℕ × ℕ → ℤ := fun x => if h : x ∈ C then j (C.equivFin ⟨x, h⟩) else 0 with hJ
    have hJi : ∀ i : Fin C.card, J (C.equivFin.symm i).1 = j i := by
      intro i
      simp only [hJ, dite_eq_left (C.equivFin.symm i).2, Subtype.coe_eta, Equiv.apply_symm_apply]
    have hne' : s ≠ 0 ∨ ∃ x ∈ C, J x ≠ 0 := by
      rcases hne with h | h
      · exact Or.inl h
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
        exact Or.inr ⟨_, (C.equivFin.symm i).2, by rw [hJi]; simpa using hi⟩
    rcases hmin s J hne' with h | ⟨x, hx, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨C.equivFin ⟨x, hx⟩, ?_⟩
      rw [qNrM9_cast, Equiv.symm_apply_apply, Int.cast_natCast]
      have e : J x = j (C.equivFin ⟨x, hx⟩) := by simp only [hJ, dite_eq_left hx]
      rwa [e] at h
  obtain ⟨s, j, hrs, hsT, hbox⟩ := nr_two C.card (qNrM9 C) (Dprod S a : ℤ) m T hm0 hT
    (qNrM9_pos hS a m T) r hr lam hlam hmin' hcrit
  exact ball_of_box hS a m hm T hT r hcop
    ⟨s, hrs, hsT, box_of_fin C (Dprod S a) m s fun i => ⟨j i, hbox i⟩⟩

/-- **Criterion with `eps`.** If every `0 < s < T` has `P_p(D s) ≥ eps` for some `p ∈ S`, `m eps < 1` and
`2 ≤ T eps^c`, then there is a ball element `D s` with `0 < s < T` and `r ∤ D s`; hence `N_r < D T`. -/
theorem nr_eps_ball {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (T : ℝ) (hT : 0 < T) (r : ℤ) (hr : ¬ r ∣ 1) (hcop : IsCoprime r (Dprod S a : ℤ))
    (eps : ℝ) (heps : 0 < eps) (hme : (m : ℝ) * eps < 1)
    (hsep : ∀ s : ℤ, 0 < s → (s : ℝ) < T →
      ∃ p ∈ S, eps ≤ Pn (sqScales p) ((Dprod S a : ℤ) * s))
    (hcrit : 2 ≤ T * eps ^ (retNrM9 S a m T).card) :
    ∃ s : ℤ, 0 < s ∧ (s : ℝ) < T ∧ ¬ r ∣ (Dprod S a : ℤ) * s ∧
      InBall S (1 / (m : ℝ)) ((Dprod S a : ℤ) * s) := by
  classical
  set C := retNrM9 S a m T with hC
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfar : ∀ s : ℤ, 0 < s → (s : ℝ) < T →
      (m : ℝ) * eps ≤ s / T ∨ ∃ i, ∀ j : ℤ,
        eps * qNrM9 C i ≤ |(((Dprod S a : ℤ)) : ℝ) * s - j * qNrM9 C i| := by
    intro s hs hsT
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    have htail : (s : ℝ) / (m * T) < eps := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hT] at h1
      linarith
    have hret : ∀ x ∈ C, nrm (((Dprod S a : ℤ) * s : ℤ) / ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ)) < eps := by
      intro x hx
      obtain ⟨j, hj⟩ := h2 (C.equivFin ⟨x, hx⟩)
      rw [qNrM9_cast, Equiv.symm_apply_apply, Int.cast_natCast] at hj
      have hxS := (mem_retNrM9 hS a m T x.1 x.2).mp hx
      have hq : (0 : ℝ) < ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ) := by
        have := hS x.1 hxS.1
        exact_mod_cast pow_pos (by omega : 0 < x.1) _
      set q : ℝ := ((x.1 ^ (x.2 ^ 2) : ℕ) : ℝ) with hqdef
      refine lt_of_le_of_lt (nrm_le_sub_int _ j) ?_
      have e : ((((Dprod S a : ℤ) * s : ℤ)) : ℝ) / q - j = ((Dprod S a : ℝ) * s - j * q) / q := by
        rw [Int.cast_mul, Int.cast_natCast]
        field_simp
      rw [e, abs_div, abs_of_pos hq, div_lt_iff₀ hq]
      exact hj
    obtain ⟨p, hp, hle⟩ := hsep s hs hsT
    exact absurd (pn_lt_of_retained hS a m hm T hT s hs.le eps htail hret p hp) (not_lt.mpr hle)
  obtain ⟨s, hs, hsT, hrs, hbox⟩ := nr_eps C.card (qNrM9 C) (Dprod S a : ℤ) m T hm1 hT
    (qNrM9_pos hS a m T) r hr hcop eps heps hme hfar hcrit
  have hrs' : ¬ r ∣ s := fun h => hrs (h.mul_left _)
  refine ball_of_box hS a m hm T hT r hcop
    ⟨s, hrs', ?_, box_of_fin C (Dprod S a) m s hbox⟩
  rw [abs_of_pos (by exact_mod_cast hs : (0 : ℝ) < s)]
  exact hsT

/-- The condition `T > (c+1) r eps^(-c) / 2` is covered when `(c+1) r ≥ 4`. -/
theorem nrcrit_ball {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (T : ℝ) (hT : 0 < T) (r : ℕ) (hr : 2 ≤ r) (hcop : IsCoprime (r : ℤ) (Dprod S a : ℤ))
    (eps : ℝ) (heps : 0 < eps) (hme : (m : ℝ) * eps < 1)
    (hsep : ∀ s : ℤ, 0 < s → (s : ℝ) < T →
      ∃ p ∈ S, eps ≤ Pn (sqScales p) ((Dprod S a : ℤ) * s))
    (hbig : 4 ≤ ((retNrM9 S a m T).card + 1) * r)
    (hcrit : (((retNrM9 S a m T).card : ℝ) + 1) * r / 2 / eps ^ (retNrM9 S a m T).card < T) :
    ∃ s : ℤ, 0 < s ∧ (s : ℝ) < T ∧ ¬ (r : ℤ) ∣ (Dprod S a : ℤ) * s ∧
      InBall S (1 / (m : ℝ)) ((Dprod S a : ℤ) * s) := by
  have hr1 : ¬ (r : ℤ) ∣ 1 := by
    intro h
    have : r ∣ 1 := by exact_mod_cast h
    have := Nat.le_of_dvd one_pos this
    omega
  refine nr_eps_ball hS a m hm T hT r hr1 hcop eps heps hme hsep ?_
  have hpos : 0 < eps ^ (retNrM9 S a m T).card := pow_pos heps _
  have h4 : (4 : ℝ) ≤ (((retNrM9 S a m T).card : ℝ) + 1) * r := by exact_mod_cast hbig
  rw [div_lt_iff₀ hpos] at hcrit
  linarith

#print axioms pn_lt_of_retained
#print axioms ball_of_box
#print axioms nr_sharp_ball
#print axioms nr_two_ball
#print axioms nr_eps_ball
#print axioms nrcrit_ball

end TVGPlus
end LeanCheck
