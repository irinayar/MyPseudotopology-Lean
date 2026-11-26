import Mathlib
import LeanCheck.TwoPrimesFormula
import LeanCheck.TwoPrimesBox
import LeanCheck.TwoPrimesBasis

/-!
# The energy bound from the 124-dimensional certificate

`finite_energy`: for every integer `D` with `9·10^14 ≤ D ≤ 10^15`, with `u = 3^6400`, `v = 2^10201`,
`Y` the digit sums `Σ_{k<80} 3^(k²) j k`, `|j k| ≤ ⌊3^(2k+1)/D⌋`, and `Z` the digit sums
`Σ_{k<101} 2^(k²) j k`, `|j k| ≤ ⌊2^(2k+1)/D⌋`, the normalized collision energy of
`{j u + y}` and `{k v + z}` in `[0, D v]` is less than `1.711`.

That the two balls are these sets is the digit description of the first article; it is not part of
this module.  `window` is the statement `3.4 < ln(D v) / ln² D < 6`.
-/

namespace TwoPrimesBoxCertificate

open Finset Real TwoPrimesFormula

/-! ## Digit sets -/

def J (l D k : ℕ) : ℕ := l ^ (2 * k + 1) / D

def vectors (l D n : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun k : Fin n => Icc (-(J l D k : ℤ)) (J l D k)

def value (l : ℕ) {n : ℕ} (j : Fin n → ℤ) : ℤ := ∑ k : Fin n, (l : ℤ) ^ ((k : ℕ) ^ 2) * j k

def digitSet (l D n : ℕ) : Finset ℤ := (vectors l D n).image (value l)

lemma mem_vectors {l D n : ℕ} {j : Fin n → ℤ} :
    j ∈ vectors l D n ↔ ∀ k : Fin n, |j k| ≤ (J l D k : ℤ) := by
  rw [vectors, Fintype.mem_piFinset]
  exact forall_congr' fun k => by rw [mem_Icc, abs_le]

lemma sum_levels_lt {l : ℕ} (hl : 2 ≤ l) (m : ℕ) :
    ∑ k ∈ range m, l ^ ((k + 1) ^ 2) < 2 * l ^ (m ^ 2) :=
  TwoPrimesEffective.sum_levels hl m

/-- Balanced digits with these ranges are unique. -/
lemma value_injOn {l D n : ℕ} (hl : 2 ≤ l) (hD : 5 ≤ D) :
    Set.InjOn (value l (n := n)) (vectors l D n) := by
  intro j hj j' hj' heq
  rw [mem_coe, mem_vectors] at hj hj'
  by_contra hne
  have hex : (univ.filter fun k : Fin n => j k ≠ j' k).Nonempty := by
    rw [filter_nonempty_iff]
    by_contra hc
    push Not at hc
    exact hne (funext fun k => hc k (mem_univ k))
  set m := (univ.filter fun k : Fin n => j k ≠ j' k).max' hex with hm
  have hmne : j m ≠ j' m := (mem_filter.mp (max'_mem _ hex)).2
  have habove : ∀ k : Fin n, m < k → j k = j' k := by
    intro k hk
    by_contra h
    have := le_max' (univ.filter fun k : Fin n => j k ≠ j' k) k (mem_filter.mpr ⟨mem_univ k, h⟩)
    rw [← hm] at this
    exact absurd hk (not_lt.mpr this)
  set d : Fin n → ℤ := fun k => j k - j' k with hd
  have hsum : ∑ k : Fin n, (l : ℤ) ^ ((k : ℕ) ^ 2) * d k = 0 := by
    have e : ∑ k : Fin n, (l : ℤ) ^ ((k : ℕ) ^ 2) * d k = value l j - value l j' := by
      unfold value
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by rw [hd]; ring
    rw [e, heq, sub_self]
  have hsplit : ∑ k : Fin n, (l : ℤ) ^ ((k : ℕ) ^ 2) * d k
      = (l : ℤ) ^ ((m : ℕ) ^ 2) * d m
        + ∑ k ∈ univ.filter (fun k : Fin n => k < m), (l : ℤ) ^ ((k : ℕ) ^ 2) * d k := by
    rw [← sum_filter_add_sum_filter_not univ (fun k : Fin n => k < m), add_comm]
    congr 1
    have : ∑ k ∈ univ.filter (fun k : Fin n => ¬ k < m), (l : ℤ) ^ ((k : ℕ) ^ 2) * d k
        = (l : ℤ) ^ ((m : ℕ) ^ 2) * d m := by
      refine sum_eq_single m (fun k hk hkm => ?_) (fun h => ?_)
      · have h1 : m < k := lt_of_le_of_ne (not_lt.mp (mem_filter.mp hk).2) (Ne.symm hkm)
        rw [hd]
        simp only [habove k h1, sub_self, mul_zero]
      · exact absurd (mem_filter.mpr ⟨mem_univ m, lt_irrefl m⟩) h
    exact this
  -- the lower terms are smaller than the leading weight
  have hlow : (D : ℤ) * |∑ k ∈ univ.filter (fun k : Fin n => k < m), (l : ℤ) ^ ((k : ℕ) ^ 2) * d k|
      ≤ 2 * ∑ k ∈ range (m : ℕ), (l : ℤ) ^ ((k + 1) ^ 2) := by
    have h1 : ∀ k : Fin n, (D : ℤ) * |(l : ℤ) ^ ((k : ℕ) ^ 2) * d k|
        ≤ 2 * (l : ℤ) ^ (((k : ℕ) + 1) ^ 2) := by
      intro k
      have h2 : |d k| ≤ 2 * (J l D k : ℤ) := by
        refine le_trans (abs_sub _ _) ?_
        have := hj k
        have := hj' k
        omega
      have h3 : (D : ℤ) * (J l D k : ℤ) ≤ (l : ℤ) ^ (2 * (k : ℕ) + 1) := by
        have : D * J l D k ≤ l ^ (2 * (k : ℕ) + 1) := Nat.mul_div_le _ _
        exact_mod_cast this
      have h4 : (D : ℤ) * |d k| ≤ 2 * (l : ℤ) ^ (2 * (k : ℕ) + 1) := by
        have := mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg D)
        nlinarith
      have e : (l : ℤ) ^ (((k : ℕ) + 1) ^ 2)
          = (l : ℤ) ^ ((k : ℕ) ^ 2) * (l : ℤ) ^ (2 * (k : ℕ) + 1) := by
        rw [← pow_add]; congr 1; ring
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (l : ℤ) ^ ((k : ℕ) ^ 2)), e]
      have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℤ) ≤ (l : ℤ) ^ ((k : ℕ) ^ 2))
      nlinarith
    refine le_trans (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (Int.natCast_nonneg D)) ?_
    rw [mul_sum]
    refine le_trans (sum_le_sum fun k _ => h1 k) ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have himg : ∑ k ∈ univ.filter (fun k : Fin n => k < m), (l : ℤ) ^ (((k : ℕ) + 1) ^ 2)
        = ∑ k ∈ (univ.filter (fun k : Fin n => k < m)).image (fun k : Fin n => (k : ℕ)),
          (l : ℤ) ^ ((k + 1) ^ 2) := by
      rw [sum_image]
      exact fun a _ b _ h => Fin.ext h
    rw [himg]
    refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => by positivity)
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (mem_filter.mp hi).2
  have hlev : ∑ k ∈ range (m : ℕ), (l : ℤ) ^ ((k + 1) ^ 2) < 2 * (l : ℤ) ^ ((m : ℕ) ^ 2) := by
    exact_mod_cast sum_levels_lt hl (m : ℕ)
  set R := ∑ k ∈ univ.filter (fun k : Fin n => k < m), (l : ℤ) ^ ((k : ℕ) ^ 2) * d k with hR
  have hpos : (0 : ℤ) < (l : ℤ) ^ ((m : ℕ) ^ 2) := by
    have : (0 : ℤ) < l := by exact_mod_cast (by omega : 0 < l)
    positivity
  have hRlt : |R| < (l : ℤ) ^ ((m : ℕ) ^ 2) := by
    have h5 : (5 : ℤ) ≤ D := by exact_mod_cast hD
    have h6 := mul_le_mul_of_nonneg_right h5 (abs_nonneg R)
    omega
  rw [hsplit] at hsum
  have hdm : d m ≠ 0 := sub_ne_zero.mpr hmne
  have h7 : (l : ℤ) ^ ((m : ℕ) ^ 2) ≤ |R| := by
    have e : R = -((l : ℤ) ^ ((m : ℕ) ^ 2) * d m) := by omega
    rw [e, abs_neg, abs_mul, abs_of_pos hpos]
    exact le_mul_of_one_le_right hpos.le (Int.one_le_abs hdm)
  omega

lemma card_digitSet {l D n : ℕ} (hl : 2 ≤ l) (hD : 5 ≤ D) :
    (digitSet l D n).card = ∏ k : Fin n, (2 * J l D k + 1) := by
  rw [digitSet, card_image_of_injOn (value_injOn hl hD), vectors, Fintype.card_piFinset]
  refine prod_congr rfl fun k _ => ?_
  rw [Int.card_Icc]
  omega

/-- The average of `e(x j)` over `|j| ≤ J`. -/
noncomputable def factor (J : ℕ) (x : ℝ) : ℂ := (∑ j ∈ Icc (-(J : ℤ)) J, e (x * j)) / (2 * J + 1 : ℕ)

lemma norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  exact Complex.norm_exp_ofReal_mul_I _

lemma normSq_factor_le (J : ℕ) (x : ℝ) : Complex.normSq (factor J x) ≤ 1 := by
  rw [Complex.normSq_eq_norm_sq]
  have h1 : ‖factor J x‖ ≤ 1 := by
    unfold factor
    rw [norm_div, Complex.norm_natCast, div_le_one (by positivity)]
    refine le_trans (norm_sum_le _ _) ?_
    rw [sum_congr rfl fun j _ => norm_e _, sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
    exact_mod_cast (by omega : ((J : ℤ) + 1 - -(J : ℤ)).toNat ≤ 2 * J + 1)
  exact pow_le_one₀ (norm_nonneg _) h1

lemma e_sum {α : Type*} (s : Finset α) (f : α → ℝ) : e (∑ a ∈ s, f a) = ∏ a ∈ s, e (f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [e]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, e_add, ih]

/-- The characteristic function of a box of independent digits is a product. -/
lemma sum_box_e {n : ℕ} (I : Fin n → Finset ℤ) (c : Fin n → ℝ) :
    ∑ j ∈ Fintype.piFinset I, e (∑ k, c k * j k) = ∏ k, ∑ x ∈ I k, e (c k * x) := by
  rw [prod_univ_sum]
  exact sum_congr rfl fun j _ => e_sum _ _

lemma normSq_digitSet {l D n : ℕ} (hl : 2 ≤ l) (hD : 5 ≤ D) (u ξ : ℕ) :
    power u (digitSet l D n) ξ / ((digitSet l D n).card : ℝ) ^ 2
      = ∏ k : Fin n, Complex.normSq (factor (J l D k) ((ξ : ℝ) * (l : ℝ) ^ ((k : ℕ) ^ 2) / u)) := by
  have hsum : ∑ y ∈ digitSet l D n, e ((ξ : ℝ) * y / u)
      = ∏ k : Fin n, ∑ j ∈ Icc (-(J l D k : ℤ)) (J l D k),
          e ((ξ : ℝ) * (l : ℝ) ^ ((k : ℕ) ^ 2) / u * j) := by
    rw [digitSet, sum_image (value_injOn hl hD), vectors, ← sum_box_e]
    refine sum_congr rfl fun j _ => ?_
    congr 1
    unfold value
    push_cast
    rw [mul_sum, sum_div]
    exact sum_congr rfl fun k _ => by ring
  unfold power
  rw [hsum, card_digitSet hl hD, map_prod, Nat.cast_prod, ← prod_pow, ← prod_div_distrib]
  refine prod_congr rfl fun k _ => ?_
  unfold factor
  rw [map_div₀, Complex.normSq_natCast, ← sq]

/-! ## The certificate -/

def u : ℕ := 3 ^ 6400

def v : ℕ := 2 ^ 10201

def Y (D : ℕ) : Finset ℤ := digitSet 3 D 80

def Z (D : ℕ) : Finset ℤ := digitSet 2 D 101

/-- The number of values of the certificate digit `j` at the radius parameter `D`. -/
def N (D : ℕ) (j : Fin 124) : ℕ := 2 * J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1) + 1

def r (j : Fin 124) : ℕ := TwoPrimesBasisData.widths.getD j 0

def D0 : ℕ := 10 ^ 15

lemma check_r : (List.finRange 124).all (fun j => decide (1 ≤ r j)
    && decide (r j ≤ N D0 j + 1)) = true := by decide +kernel

lemma check_prod :
    (∏ j, (N D0 j - 1 + r j) - ∏ j, N D0 j) * (∏ j, N D0 j - ∏ j, (N D0 j + 1 - r j)) * 10 ^ 12
        < 282780231673 * (∏ j, N D0 j) ^ 2
      ∧ ∏ j, N D0 j ≤ ∏ j, (N D0 j - 1 + r j)
      ∧ ∏ j, (N D0 j + 1 - r j) ≤ ∏ j, N D0 j := by decide +kernel

lemma check_inj : Function.Injective (fun j : Fin 124 => (TwoPrimesBasis.base j, TwoPrimesBasis.dig j)) := by
  decide +kernel

lemma check_v : 20 * D0 * u ≤ v := by decide +kernel

lemma u_eq : u = TwoPrimesBasis.u := rfl

attribute [local irreducible] u v TwoPrimesBasis.u

lemma check_widthsum : ∀ j : Fin 124, (∑ i, |TwoPrimesBasis.B i j|) = (r j : ℤ) :=
  fun j => TwoPrimesBasis.column_sum j

lemma bezout : ∃ x : Fin 124 → ℤ,
    (u : ℤ) ∣ (∑ j, (TwoPrimesBasis.wN j : ℤ) * x j) - 1 := by
  have hco : IsCoprime ((TwoPrimesBasis.wN 0 : ℕ) : ℤ) (u : ℤ) := by
    have h : Nat.Coprime (TwoPrimesBasis.wN 0) u := by
      unfold TwoPrimesBasis.wN u
      rw [TwoPrimesBasis.check_first.1]
      exact Nat.Coprime.pow _ _ (by norm_num)
    exact Nat.Coprime.isCoprime h
  obtain ⟨a, b, hab⟩ := hco
  refine ⟨Pi.single 0 a, -b, ?_⟩
  have e : ∑ j, (TwoPrimesBasis.wN j : ℤ) * (Pi.single 0 a : Fin 124 → ℤ) j
      = (TwoPrimesBasis.wN 0 : ℤ) * a := by
    rw [sum_eq_single (0 : Fin 124)]
    · rw [Pi.single_eq_same]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · intro h
      exact absurd (mem_univ _) h
  rw [e]
  linear_combination hab

noncomputable def data : TwoPrimesBox.Data 124 :=
  { Q := u
    hQ := by unfold u; exact pow_pos (by norm_num) _
    w := fun j => (TwoPrimesBasis.wN j : ℤ)
    B := TwoPrimesBasis.B
    hdet := TwoPrimesBasis.det_ne_zero
    hrow := fun i => u_eq ▸ TwoPrimesBasis.row_dvd i
    u := bezout.choose
    hu := bezout.choose_spec }

lemma data_r (j : Fin 124) : data.r j = (r j : ℝ) := by
  have h := check_widthsum j
  have h' : (∑ i, |(TwoPrimesBasis.B i j : ℝ)|) = (r j : ℝ) := by exact_mod_cast h
  exact h'

lemma r_bounds (j : Fin 124) : 1 ≤ r j ∧ r j ≤ N D0 j + 1 := by
  have h := List.all_eq_true.mp check_r j (List.mem_finRange j)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

lemma N_mono {D : ℕ} (hD : 5 ≤ D) (hD0 : D ≤ D0) (j : Fin 124) : N D0 j ≤ N D j := by
  unfold N J
  have h := Nat.div_le_div_left (a := TwoPrimesBasis.base j ^ (2 * (TwoPrimesBasis.dig j - 1) + 1))
    hD0 (by omega : 0 < D)
  omega

/-- `(U - 1)(1 - L)` at any `D ≤ 10^15`. -/
lemma box_constant {D : ℕ} (hD : 5 ≤ D) (hD0 : D ≤ D0) :
    (data.U (N D) - 1) * (1 - data.L (N D)) ≤ 282780231673 / 10 ^ 12 := by
  have hN0 : ∀ j, (0 : ℝ) < N D0 j := fun j => by
    have : 0 < N D0 j := by unfold N; omega
    exact_mod_cast this
  have hN : ∀ j, (0 : ℝ) < N D j := fun j => by
    have : 0 < N D j := by unfold N; omega
    exact_mod_cast this
  have hr1 : ∀ j, (1 : ℝ) ≤ r j := fun j => by exact_mod_cast (r_bounds j).1
  have hr2 : ∀ j, (r j : ℝ) ≤ N D0 j + 1 := fun j => by exact_mod_cast (r_bounds j).2
  have hmono : ∀ j, (N D0 j : ℝ) ≤ N D j := fun j => by exact_mod_cast N_mono hD hD0 j
  set U0 : ℝ := ∏ j, ((N D0 j : ℝ) - 1 + r j) / N D0 j with hU0
  set L0 : ℝ := ∏ j, ((N D0 j : ℝ) + 1 - r j) / N D0 j with hL0
  have hUe : data.U (N D) = ∏ j, ((N D j : ℝ) - 1 + r j) / N D j := by
    unfold TwoPrimesBox.Data.U
    exact prod_congr rfl fun j _ => by rw [data_r]
  have hLe : data.L (N D) = ∏ j, ((N D j : ℝ) + 1 - r j) / N D j := by
    unfold TwoPrimesBox.Data.L
    refine prod_congr rfl fun j _ => ?_
    rw [data_r, max_eq_left]
    have := hr2 j
    have := hmono j
    linarith
  have hUle : data.U (N D) ≤ U0 := by
    rw [hUe, hU0]
    refine prod_le_prod₀ (fun j _ => ?_) fun j _ => ?_
    · refine div_nonneg ?_ (hN j).le
      have := hr1 j
      have := (hN j).le
      linarith
    · rw [div_le_div_iff₀ (hN j) (hN0 j)]
      have h1 := mul_le_mul_of_nonneg_left (hmono j) (sub_nonneg.mpr (hr1 j))
      nlinarith
  have hU1 : 1 ≤ data.U (N D) := by
    rw [hUe]
    calc (1 : ℝ) = ∏ _j : Fin 124, (1 : ℝ) := by rw [prod_const_one]
      _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one) fun j _ => by
        rw [le_div_iff₀ (hN j)]
        have := hr1 j
        linarith
  have hL0nn : ∀ j, 0 ≤ ((N D0 j : ℝ) + 1 - r j) / N D0 j := fun j => by
    refine div_nonneg ?_ (hN0 j).le
    have := hr2 j
    linarith
  have hLge : L0 ≤ data.L (N D) := by
    rw [hLe, hL0]
    refine prod_le_prod₀ (fun j _ => hL0nn j) fun j _ => ?_
    rw [div_le_div_iff₀ (hN0 j) (hN j)]
    have h1 := mul_le_mul_of_nonneg_left (hmono j) (sub_nonneg.mpr (hr1 j))
    nlinarith
  have hL1 : data.L (N D) ≤ 1 := by
    rw [hLe]
    refine prod_le_one₀ (fun j _ => ?_) fun j _ => ?_
    · refine div_nonneg ?_ (hN j).le
      have := hr2 j
      have := hmono j
      linarith
    · rw [div_le_one (hN j)]
      have := hr1 j
      linarith
  have hnum : (U0 - 1) * (1 - L0) ≤ 282780231673 / 10 ^ 12 := by
    obtain ⟨h, h1, h2⟩ := check_prod
    obtain ⟨PN, hPN⟩ : ∃ x : ℕ, x = ∏ j, N D0 j := ⟨_, rfl⟩
    obtain ⟨PU, hPU⟩ : ∃ x : ℕ, x = ∏ j, (N D0 j - 1 + r j) := ⟨_, rfl⟩
    obtain ⟨PL, hPL⟩ : ∃ x : ℕ, x = ∏ j, (N D0 j + 1 - r j) := ⟨_, rfl⟩
    rw [← hPN, ← hPU] at h h1
    rw [← hPL] at h
    rw [← hPL, ← hPN] at h2
    have hPN0 : (0 : ℝ) < PN := by
      have : 0 < PN := by
        rw [hPN]
        exact prod_pos fun j _ => by unfold N; omega
      exact_mod_cast this
    have eU : U0 = (PU : ℝ) / PN := by
      rw [hU0, prod_div_distrib, hPU, hPN, Nat.cast_prod, Nat.cast_prod]
      refine congrArg₂ (· / ·) (prod_congr rfl fun j _ => ?_) rfl
      have : 1 ≤ N D0 j := by unfold N; omega
      rw [Nat.cast_add, Nat.cast_sub this, Nat.cast_one]
    have eL : L0 = (PL : ℝ) / PN := by
      rw [hL0, prod_div_distrib, hPL, hPN, Nat.cast_prod, Nat.cast_prod]
      refine congrArg₂ (· / ·) (prod_congr rfl fun j _ => ?_) rfl
      rw [Nat.cast_sub (r_bounds j).2, Nat.cast_add, Nat.cast_one]
    have hr : ((PU : ℝ) - PN) * ((PN : ℝ) - PL) * 10 ^ 12 < 282780231673 * (PN : ℝ) ^ 2 := by
      have := (Nat.cast_lt (α := ℝ)).mpr h
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub h1,
        Nat.cast_sub h2] at this
      simpa only [Nat.cast_ofNat] using this
    have e : (U0 - 1) * (1 - L0) = (((PU : ℝ) - PN) * ((PN : ℝ) - PL)) / (PN : ℝ) ^ 2 := by
      rw [eU, eL]
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    exact hr.le
  refine le_trans ?_ hnum
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

/-- `κ ≤ 1 + (U - 1)(1 - L)`. -/
lemma kappa_le {D : ℕ} (hD : 5 ≤ D) (hD0 : D ≤ D0) :
    kappa u (Y D) (Z D) ≤ 1 + 282780231673 / 10 ^ 12 := by
  have hu : 0 < u := by unfold u; exact pow_pos (by norm_num) _
  set a : Fin 124 → ℤ := fun j => -(J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1) : ℤ)
    with ha
  have hcoeff : ∀ ξ : ℕ, data.coeff a (N D) ξ = ∏ j : Fin 124, Complex.normSq
      (factor (J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1))
        ((ξ : ℝ) * (TwoPrimesBasis.base j : ℝ) ^ ((TwoPrimesBasis.dig j - 1) ^ 2) / u)) := by
    intro ξ
    have hbox : TwoPrimesBox.Data.box a (N D) = Fintype.piFinset fun j =>
        Icc (-(J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1) : ℤ))
          (J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1)) := by
      unfold TwoPrimesBox.Data.box
      refine congrArg _ (funext fun j => ?_)
      ext x
      rw [mem_Ico, mem_Icc]
      simp only [ha]
      unfold N
      omega
    have hsum : ∑ z ∈ TwoPrimesBox.Data.box a (N D), e ((ξ : ℝ) * data.res z / data.Q)
        = ∏ j : Fin 124, ∑ x ∈ Icc (-(J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1) : ℤ))
            (J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1)),
          e ((ξ : ℝ) * (TwoPrimesBasis.base j : ℝ) ^ ((TwoPrimesBasis.dig j - 1) ^ 2) / u * x) := by
      rw [hbox, ← sum_box_e]
      refine sum_congr rfl fun z _ => ?_
      congr 1
      have e1 : (data.res z : ℝ) = ∑ j, ((TwoPrimesBasis.base j : ℝ)
          ^ ((TwoPrimesBasis.dig j - 1) ^ 2)) * (z j : ℝ) := by
        unfold TwoPrimesBox.Data.res data TwoPrimesBasis.wN
        push_cast
        rfl
      have e2 : (data.Q : ℝ) = (u : ℝ) := rfl
      rw [e1, e2, mul_sum, sum_div]
      exact sum_congr rfl fun j _ => by ring
    unfold TwoPrimesBox.Data.coeff
    rw [hsum, map_prod, Nat.cast_prod, ← prod_pow, ← prod_div_distrib]
    refine prod_congr rfl fun j _ => ?_
    unfold factor N
    rw [map_div₀, Complex.normSq_natCast, ← sq]
  have hG : ∀ ξ : ℕ, G u (Y D) (Z D) ξ ≤ data.coeff a (N D) ξ := by
    intro ξ
    set F3 : Fin 80 → ℝ := fun k =>
      Complex.normSq (factor (J 3 D k) ((ξ : ℝ) * ((3 : ℕ) : ℝ) ^ ((k : ℕ) ^ 2) / u)) with hF3
    set F2 : Fin 101 → ℝ := fun k =>
      Complex.normSq (factor (J 2 D k) ((ξ : ℝ) * ((2 : ℕ) : ℝ) ^ ((k : ℕ) ^ 2) / u)) with hF2
    have e : G u (Y D) (Z D) ξ = (∏ k, F3 k) * ∏ k, F2 k := by
      have h3 := normSq_digitSet (l := 3) (D := D) (n := 80) (by norm_num) hD u ξ
      have h2 := normSq_digitSet (l := 2) (D := D) (n := 101) le_rfl hD u ξ
      unfold G Y Z
      rw [hF3, hF2]
      rw [← h3, ← h2]
      ring
    -- one product over the disjoint union of the two sets of digits
    set F : Fin 80 ⊕ Fin 101 → ℝ := Sum.elim F3 F2 with hF
    have hF0 : ∀ i, 0 ≤ F i := by
      rintro (k | k) <;> exact Complex.normSq_nonneg _
    have hF1 : ∀ i, F i ≤ 1 := by
      rintro (k | k) <;> exact normSq_factor_le _ _
    have hshape : ∀ j : Fin 124, (TwoPrimesBasis.base j = 3 ∧ TwoPrimesBasis.dig j - 1 < 80)
        ∨ (TwoPrimesBasis.base j = 2 ∧ TwoPrimesBasis.dig j - 1 < 101) := by
      intro j
      obtain ⟨h1, h2, h3, h4⟩ := TwoPrimesBasis.shape j
      rcases h3 with h | h
      · exact Or.inr ⟨h, by omega⟩
      · have := h4 h
        exact Or.inl ⟨h, by omega⟩
    set g : Fin 124 → Fin 80 ⊕ Fin 101 := fun j =>
      if h : TwoPrimesBasis.base j = 3 ∧ TwoPrimesBasis.dig j - 1 < 80 then
        Sum.inl ⟨TwoPrimesBasis.dig j - 1, h.2⟩
      else if h' : TwoPrimesBasis.dig j - 1 < 101 then Sum.inr ⟨TwoPrimesBasis.dig j - 1, h'⟩
      else Sum.inl 0 with hg
    have hg3 : ∀ j, TwoPrimesBasis.base j = 3 → ∃ h : TwoPrimesBasis.dig j - 1 < 80,
        g j = Sum.inl ⟨TwoPrimesBasis.dig j - 1, h⟩ := by
      intro j hj
      rcases hshape j with h | h
      · exact ⟨h.2, by rw [hg]; exact dif_pos h⟩
      · omega
    have hg2 : ∀ j, TwoPrimesBasis.base j = 2 → ∃ h : TwoPrimesBasis.dig j - 1 < 101,
        g j = Sum.inr ⟨TwoPrimesBasis.dig j - 1, h⟩ := by
      intro j hj
      rcases hshape j with h | h
      · omega
      · refine ⟨h.2, ?_⟩
        rw [hg]
        have hn : ¬ (TwoPrimesBasis.base j = 3 ∧ TwoPrimesBasis.dig j - 1 < 80) := by omega
        simp only [dif_neg hn, dif_pos h.2]
    have hginj : Function.Injective g := by
      intro i j hij
      refine check_inj (Prod.ext ?_ ?_)
      · rcases hshape i with hi | hi <;> rcases hshape j with hj | hj
        · exact hi.1.trans hj.1.symm
        · obtain ⟨_, e1⟩ := hg3 i hi.1
          obtain ⟨_, e2⟩ := hg2 j hj.1
          rw [e1, e2] at hij
          exact absurd hij Sum.inl_ne_inr
        · obtain ⟨_, e1⟩ := hg2 i hi.1
          obtain ⟨_, e2⟩ := hg3 j hj.1
          rw [e1, e2] at hij
          exact absurd hij Sum.inr_ne_inl
        · exact hi.1.trans hj.1.symm
      · have h1 := (TwoPrimesBasis.shape i).2.1
        have h2 := (TwoPrimesBasis.shape j).2.1
        have key : TwoPrimesBasis.dig i - 1 = TwoPrimesBasis.dig j - 1 := by
          rcases hshape i with hi | hi <;> rcases hshape j with hj | hj
          · obtain ⟨_, e1⟩ := hg3 i hi.1
            obtain ⟨_, e2⟩ := hg3 j hj.1
            rw [e1, e2] at hij
            exact Fin.mk.inj_iff.mp (Sum.inl.inj hij)
          · obtain ⟨_, e1⟩ := hg3 i hi.1
            obtain ⟨_, e2⟩ := hg2 j hj.1
            rw [e1, e2] at hij
            exact absurd hij Sum.inl_ne_inr
          · obtain ⟨_, e1⟩ := hg2 i hi.1
            obtain ⟨_, e2⟩ := hg3 j hj.1
            rw [e1, e2] at hij
            exact absurd hij Sum.inr_ne_inl
          · obtain ⟨_, e1⟩ := hg2 i hi.1
            obtain ⟨_, e2⟩ := hg2 j hj.1
            rw [e1, e2] at hij
            exact Fin.mk.inj_iff.mp (Sum.inr.inj hij)
        show TwoPrimesBasis.dig i = TwoPrimesBasis.dig j
        omega
    have hle : ∏ i, F i ≤ ∏ j, F (g j) := by
      have himg : ∏ j, F (g j) = ∏ i ∈ univ.image g, F i := by
        rw [prod_image hginj.injOn]
      rw [himg, ← prod_sdiff (subset_univ (univ.image g))]
      exact mul_le_of_le_one_left (prod_nonneg fun i _ => hF0 i)
        (prod_le_one₀ (fun i _ => hF0 i) fun i _ => hF1 i)
    have hFg : ∏ j, F (g j) = data.coeff a (N D) ξ := by
      rw [hcoeff]
      refine prod_congr rfl fun j _ => ?_
      rcases hshape j with h | h
      · obtain ⟨_, e1⟩ := hg3 j h.1
        rw [e1, hF, Sum.elim_inl, hF3]
        simp only [h.1]
      · obtain ⟨_, e1⟩ := hg2 j h.1
        rw [e1, hF, Sum.elim_inr, hF2]
        simp only [h.1]
    rw [e, ← hFg]
    refine le_trans (le_of_eq ?_) hle
    rw [Fintype.prod_sum_type]
    rfl
  have h1 : kappa u (Y D) (Z D) ≤ ∑ ξ ∈ range u, data.coeff a (N D) ξ := by
    unfold kappa
    exact sum_le_sum fun ξ _ => hG ξ
  have h2 : ∑ ξ ∈ range u, data.coeff a (N D) ξ
      = data.coeff a (N D) 0 + ∑ ξ ∈ Ico 1 data.Q, data.coeff a (N D) ξ := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hu]
    rfl
  have h3 : data.coeff a (N D) 0 = 1 := by
    rw [hcoeff]
    refine prod_eq_one fun j _ => ?_
    have : factor (J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1))
        (((0 : ℕ) : ℝ) * (TwoPrimesBasis.base j : ℝ) ^ ((TwoPrimesBasis.dig j - 1) ^ 2) / u) = 1 := by
      unfold factor
      have e0 : ∀ x ∈ Icc (-(J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1) : ℤ))
          (J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1)),
          e (((0 : ℕ) : ℝ) * (TwoPrimesBasis.base j : ℝ) ^ ((TwoPrimesBasis.dig j - 1) ^ 2) / u
            * x) = 1 := by
        intro x _
        unfold TwoPrimesFormula.e
        rw [Nat.cast_zero, zero_mul, zero_div, zero_mul, mul_zero, Complex.ofReal_zero, zero_mul,
          Complex.exp_zero]
      rw [sum_congr rfl e0, sum_const, nsmul_eq_mul, mul_one, Int.card_Icc, div_eq_one_iff_eq]
      · exact_mod_cast (by omega :
          ((J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1) : ℤ) + 1
            - -(J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1) : ℤ)).toNat
          = 2 * J (TwoPrimesBasis.base j) D (TwoPrimesBasis.dig j - 1) + 1)
      · exact Nat.cast_ne_zero.mpr (by omega)
    rw [this, map_one]
  have h4 := data.box_energy a (N D) fun j => by unfold N; omega
  have h5 := box_constant hD hD0
  linarith

/-! ## The setting and the bound -/

lemma digit_bound {l D n : ℕ} (hnd : ∀ k, ¬ D ∣ l ^ (2 * k + 1)) {y : ℤ}
    (hy : y ∈ digitSet l D n) (hl : 1 ≤ l) : (D : ℤ) * |y| < (l : ℤ) ^ (n ^ 2) := by
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
  rw [mem_vectors] at hj
  have h1 : (D : ℤ) * |value l j|
      ≤ ∑ k : Fin n, ((l : ℤ) ^ (((k : ℕ) + 1) ^ 2) - (l : ℤ) ^ ((k : ℕ) ^ 2)) := by
    unfold value
    refine le_trans (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (Int.natCast_nonneg D)) ?_
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    have h2 : D * J l D k ≠ l ^ (2 * (k : ℕ) + 1) := fun h => hnd k ⟨_, h.symm⟩
    have h3 : D * J l D k ≤ l ^ (2 * (k : ℕ) + 1) := Nat.mul_div_le _ _
    have h4 : (D : ℤ) * (J l D k : ℤ) ≤ (l : ℤ) ^ (2 * (k : ℕ) + 1) - 1 := by
      have : D * J l D k + 1 ≤ l ^ (2 * (k : ℕ) + 1) := by omega
      have h5 : (D : ℤ) * (J l D k : ℤ) + 1 ≤ (l : ℤ) ^ (2 * (k : ℕ) + 1) := by exact_mod_cast this
      omega
    have h6 : (D : ℤ) * |j k| ≤ (l : ℤ) ^ (2 * (k : ℕ) + 1) - 1 :=
      le_trans (mul_le_mul_of_nonneg_left (hj k) (Int.natCast_nonneg D)) h4
    have e : (l : ℤ) ^ (((k : ℕ) + 1) ^ 2)
        = (l : ℤ) ^ ((k : ℕ) ^ 2) * (l : ℤ) ^ (2 * (k : ℕ) + 1) := by
      rw [← pow_add]; congr 1; ring
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (l : ℤ) ^ ((k : ℕ) ^ 2)), e]
    have h7 := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℤ) ≤ (l : ℤ) ^ ((k : ℕ) ^ 2))
    nlinarith
  have h8 : ∑ k : Fin n, ((l : ℤ) ^ (((k : ℕ) + 1) ^ 2) - (l : ℤ) ^ ((k : ℕ) ^ 2))
      = (l : ℤ) ^ (n ^ 2) - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (l : ℤ) ^ ((k + 1) ^ 2) - (l : ℤ) ^ (k ^ 2)) n,
      sum_range_sub (fun k => (l : ℤ) ^ (k ^ 2))]
    norm_num
  omega

lemma not_dvd_pow {D p : ℕ} (hp : p.Prime) (h : ∀ i, p ^ i ≠ D) (n : ℕ) : ¬ D ∣ p ^ n := by
  intro hd
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp hd
  exact h i hi.symm

lemma setting {D : ℕ} (h1 : 9 * 10 ^ 14 ≤ D) (h2 : D ≤ 10 ^ 15) : Setting D u v (Y D) (Z D) := by
  have hD : 5 ≤ D := le_trans (by norm_num) h1
  have hnp : ∀ (p a : ℕ), 1 < p → p ^ a < 9 * 10 ^ 14 → 10 ^ 15 < p ^ (a + 1) → ∀ i, p ^ i ≠ D := by
    intro p a hp hlo hhi i hi
    rcases Nat.lt_or_ge i (a + 1) with h | h
    · have : p ^ i ≤ p ^ a := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · have : p ^ (a + 1) ≤ p ^ i := Nat.pow_le_pow_right (by omega) h
      omega
  have h3 : ∀ n, ¬ D ∣ 3 ^ n :=
    not_dvd_pow Nat.prime_three (hnp 3 31 (by norm_num) (by norm_num) (by norm_num))
  have h2' : ∀ n, ¬ D ∣ 2 ^ n :=
    not_dvd_pow Nat.prime_two (hnp 2 49 (by norm_num) (by norm_num) (by norm_num))
  refine ⟨le_trans (by norm_num) h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h2d : D ≤ D0 := h2
    exact le_trans (Nat.mul_le_mul_right u (Nat.mul_le_mul_left 20 h2d)) check_v
  · exact Finset.Nonempty.image ⟨0, mem_vectors.mpr fun k => by simp⟩ _
  · intro y hy
    have h := digit_bound (fun k => h3 _) hy (by norm_num)
    have e : (u : ℤ) = ((3 : ℕ) : ℤ) ^ (80 ^ 2) := by
      rw [← Nat.cast_pow]
      refine congrArg _ ?_
      unfold u
      exact congrArg _ (by norm_num)
    rwa [e]
  · intro z hz
    have h := digit_bound (fun k => h2' _) hz (by norm_num)
    have e : (v : ℤ) = ((2 : ℕ) : ℤ) ^ (101 ^ 2) := by
      rw [← Nat.cast_pow]
      refine congrArg _ ?_
      unfold v
      exact congrArg _ (by norm_num)
    rwa [e]
  · refine mem_image.mpr ⟨0, mem_vectors.mpr fun k => by simp, ?_⟩
    simp [value]
  · rw [Z, card_digitSet le_rfl hD]
    have h4 : 2 * J 2 D 100 + 1
        ≤ ∏ k : Fin 101, (2 * J 2 D k + 1) :=
      Finset.single_le_prod (f := fun k : Fin 101 => 2 * J 2 D k + 1)
        (fun k _ => by omega) (mem_univ (⟨100, by norm_num⟩ : Fin 101))
    have h5 : 2 ≤ J 2 D 100 := by
      unfold J
      rw [Nat.le_div_iff_mul_le (by omega : 0 < D)]
      exact le_trans (Nat.mul_le_mul_left 2 h2) (by norm_num)
    omega

/-- **The energy bound of the certificate**, for every `D` in `[9·10^14, 10^15]`. -/
theorem finite_energy {D : ℕ} (h1 : 9 * 10 ^ 14 ≤ D) (h2 : D ≤ 10 ^ 15) :
    TwoPrimesFormula.C D u v (Y D) (Z D) < 1711 / 1000 := by
  have hD : 5 ≤ D := le_trans (by norm_num) h1
  have S := setting h1 h2
  have h3 := (energy_formula S).2
  have h4 : kappaD D u v (Y D) (Z D) ≤ kappa u (Y D) (Z D) := by
    unfold kappaD kappa
    refine sum_le_sum fun ξ _ => ?_
    have hG : 0 ≤ G u (Y D) (Z D) ξ := by
      unfold G
      exact div_nonneg (mul_nonneg (power_nonneg _ _ _) (power_nonneg _ _ _))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    refine mul_le_of_le_one_right hG ?_
    exact div_le_one_of_le₀ (H_le_at_zero _ _) (H_nonneg _ _)
  have h5 := kappa_le hD h2
  have h6 : 5 / (D : ℝ) ≤ 5 / (9 * 10 ^ 14) := by
    have h : ((9 * 10 ^ 14 : ℕ) : ℝ) ≤ D := by exact_mod_cast h1
    refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  have h7 : 0 ≤ 5 / (D : ℝ) := by positivity
  have h8 : (1 + 5 / (D : ℝ)) * (4 / 3) * kappaD D u v (Y D) (Z D)
      ≤ (1 + 5 / (9 * 10 ^ 14)) * (4 / 3) * (1 + 282780231673 / 10 ^ 12) := by
    have h9 : 0 ≤ kappaD D u v (Y D) (Z D) := by
      unfold kappaD
      refine sum_nonneg fun ξ _ => mul_nonneg ?_ (div_nonneg (H_nonneg _ _) (H_nonneg _ _))
      unfold G
      exact div_nonneg (mul_nonneg (power_nonneg _ _ _) (power_nonneg _ _ _))
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (by norm_num))
      (le_trans h4 h5) h9 (by norm_num)
  have h10 : (1 + 5 / (9 * 10 ^ 14)) * (4 / 3) * (1 + 282780231673 / 10 ^ 12) < (1711 / 1000 : ℝ) := by
    norm_num
  linarith

/-- The height `X = D v` lies in the window: `3.4 ln² D < ln X < 6 ln² D`. -/
theorem window {D : ℕ} (h1 : 9 * 10 ^ 14 ≤ D) (h2 : D ≤ 10 ^ 15) :
    34 / 10 * log D ^ 2 < log ((D : ℝ) * v) ∧ log ((D : ℝ) * v) < 6 * log D ^ 2 := by
  have hD0 : (0 : ℝ) < D := by
    have : 0 < D := lt_of_lt_of_le (by norm_num) h1
    exact_mod_cast this
  have hv : (v : ℝ) = (2 : ℝ) ^ 10201 := by
    unfold v
    rw [Nat.cast_pow, Nat.cast_ofNat]
  have hX : log ((D : ℝ) * v) = log D + 10201 * log 2 := by
    rw [hv, log_mul hD0.ne' (pow_ne_zero _ two_ne_zero), log_pow]
    norm_num
  have hlo : 149 * log 2 ≤ 3 * log D := by
    have h : (2 : ℝ) ^ 149 ≤ (D : ℝ) ^ 3 := by
      have h3 : 2 ^ 149 ≤ (9 * 10 ^ 14) ^ 3 := by norm_num
      have h4 : 2 ^ 149 ≤ D ^ 3 := le_trans h3 (Nat.pow_le_pow_left h1 3)
      exact_mod_cast h4
    have := log_le_log (by positivity) h
    rwa [log_pow, log_pow] at this
  have hhi : log D ≤ 50 * log 2 := by
    have h : (D : ℝ) ≤ (2 : ℝ) ^ 50 := by
      have h3 : (10 : ℕ) ^ 15 ≤ 2 ^ 50 := by norm_num
      exact_mod_cast le_trans h2 h3
    have := log_le_log hD0 h
    rwa [log_pow] at this
  have hl2a := log_two_gt_d9
  have hl2b := log_two_lt_d9
  have hlD : 0 ≤ log D := by linarith
  rw [hX]
  have h5 := mul_le_mul hhi hhi hlD (by linarith : (0 : ℝ) ≤ 50 * log 2)
  have h6 := mul_le_mul hlo hlo (by linarith : (0 : ℝ) ≤ 149 * log 2) (by linarith)
  constructor <;> nlinarith

end TwoPrimesBoxCertificate
