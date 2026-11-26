import Mathlib

/-!
# ThreePrimesHeightM11: an explicit height for shifted targets from a covering estimate

`m + 1` chains of moduli `Q j 0 = 1`, `Q j n ∣ Q j (n+1)`, `2 * Q j n ≤ Q j (n+1)`, pairwise coprime
between different chains; `Pn (Q j) z` is the supremum over `n ≥ 1` of the distance from `z / Q j n`
to the nearest integer.  Chain `0` is the anchor; chain `i.succ` receives the target `t i`.

* `height_M11`: if the covering input `Input` holds at a height `X` which is large compared with the
  explicit constants, then every target `t` with `|t i| ≤ τ` has `k` with `|k| ≤ 48 X`,
  `Pn (Q 0) k < 16 r0` and `Pn (Q i.succ) (k - t i) < 16 r0`.
* `all_targets_M11`: if the input holds at arbitrarily large heights, every target has such a `k`.
* `square_isChainM11`, `square_coprimeM11`, `square_ratioM11`: the chains `p ^ (n^2)` satisfy the
  chain hypotheses.

The input `Input` is a hypothesis here; it is not proved in this file.  No compactness and no
character theorem is used: finite Fourier analysis on `(ℤ/M)^m`, a short expansion for each chain,
and a gap argument.
-/

namespace LeanCheck
namespace HeightM11

open Finset

/-! ## Distance to the nearest integer -/

noncomputable def nd (x : ℝ) : ℝ := |x - round x|

lemma nd_nonneg (x : ℝ) : 0 ≤ nd x := abs_nonneg _

lemma nd_le_half (x : ℝ) : nd x ≤ 1 / 2 := abs_sub_round x

lemma nd_le (x : ℝ) (z : ℤ) : nd x ≤ |x - z| := round_le x z

lemma nd_le_abs (x : ℝ) : nd x ≤ |x| := by
  simpa using nd_le x 0

lemma nd_add_int (x : ℝ) (a : ℤ) : nd (x + a) = nd x := by
  unfold nd
  rw [round_add_intCast]
  push_cast
  congr 1
  ring

lemma nd_int (a : ℤ) : nd (a : ℝ) = 0 := by
  simp [nd]

lemma nd_add_le (x y : ℝ) : nd (x + y) ≤ nd x + nd y := by
  refine le_trans (nd_le (x + y) (round x + round y)) ?_
  have h : x + y - ((round x + round y : ℤ) : ℝ) = (x - round x) + (y - round y) := by
    push_cast; ring
  rw [h]
  exact abs_add_le _ _

lemma nd_neg (x : ℝ) : nd (-x) = nd x := by
  have key : ∀ y : ℝ, nd (-y) ≤ nd y := by
    intro y
    refine le_trans (nd_le (-y) (-round y)) (le_of_eq ?_)
    unfold nd
    rw [← abs_neg]
    congr 1
    push_cast; ring
  refine le_antisymm (key x) ?_
  have := key (-x)
  rwa [neg_neg] at this

lemma nd_int_mul_le (a : ℤ) (x : ℝ) : nd (a * x) ≤ |(a : ℝ)| * nd x := by
  refine le_trans (nd_le _ (a * round x)) (le_of_eq ?_)
  unfold nd
  rw [← abs_mul]
  congr 1
  push_cast; ring

lemma nd_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) : nd (∑ i ∈ s, f i) ≤ ∑ i ∈ s, nd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nd]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact le_trans (nd_add_le _ _) (add_le_add le_rfl ih)

lemma nd_of_small {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1 / 2) : nd y = y := by
  have : round y = 0 := by
    rw [round_eq_zero_iff]
    constructor
    · linarith
    · exact h1
  unfold nd
  rw [this]
  simp [abs_of_nonneg h0]

/-! ## The chain pseudonorm -/

noncomputable def Pn (Q : ℕ → ℕ) (z : ℤ) : ℝ := ⨆ n : ℕ, nd ((z : ℝ) / Q (n + 1))

lemma Pn_bdd (Q : ℕ → ℕ) (z : ℤ) :
    BddAbove (Set.range fun n : ℕ => nd ((z : ℝ) / Q (n + 1))) := by
  refine ⟨1 / 2, ?_⟩
  rintro y ⟨n, rfl⟩
  exact nd_le_half _

lemma le_Pn (Q : ℕ → ℕ) (z : ℤ) (n : ℕ) : nd ((z : ℝ) / Q (n + 1)) ≤ Pn Q z :=
  le_ciSup (Pn_bdd Q z) n

lemma Pn_le {Q : ℕ → ℕ} {z : ℤ} {b : ℝ} (h : ∀ n, nd ((z : ℝ) / Q (n + 1)) ≤ b) : Pn Q z ≤ b :=
  ciSup_le h

lemma Pn_nonneg (Q : ℕ → ℕ) (z : ℤ) : 0 ≤ Pn Q z := le_trans (nd_nonneg _) (le_Pn Q z 0)

lemma Pn_add_le (Q : ℕ → ℕ) (a b : ℤ) : Pn Q (a + b) ≤ Pn Q a + Pn Q b := by
  refine Pn_le fun n => ?_
  have h : (((a + b : ℤ)) : ℝ) / Q (n + 1) = (a : ℝ) / Q (n + 1) + (b : ℝ) / Q (n + 1) := by
    push_cast; ring
  rw [h]
  exact le_trans (nd_add_le _ _) (add_le_add (le_Pn Q a n) (le_Pn Q b n))

lemma Pn_neg (Q : ℕ → ℕ) (a : ℤ) : Pn Q (-a) = Pn Q a := by
  unfold Pn
  congr 1
  funext n
  rw [Int.cast_neg, neg_div, nd_neg]

lemma Pn_sub_le (Q : ℕ → ℕ) (a b : ℤ) : Pn Q (a - b) ≤ Pn Q a + Pn Q b := by
  have h := Pn_add_le Q a (-b)
  rw [Pn_neg] at h
  rwa [sub_eq_add_neg]

/-! ## Chains -/

structure IsChain (Q : ℕ → ℕ) : Prop where
  zero : Q 0 = 1
  dvd : ∀ n, Q n ∣ Q (n + 1)
  two : ∀ n, 2 * Q n ≤ Q (n + 1)

namespace IsChain

variable {Q : ℕ → ℕ}

lemma two_pow (h : IsChain Q) (n : ℕ) : 2 ^ n ≤ Q n := by
  induction n with
  | zero => simp [h.zero]
  | succ n ih =>
    have := h.two n
    rw [pow_succ]
    omega

lemma pos (h : IsChain Q) (n : ℕ) : 0 < Q n :=
  lt_of_lt_of_le (by positivity) (h.two_pow n)

lemma mono (h : IsChain Q) : Monotone Q := by
  refine monotone_nat_of_le_succ fun n => ?_
  have := h.two n
  omega

lemma dvd_of_le (h : IsChain Q) {a b : ℕ} (hab : a ≤ b) : Q a ∣ Q b := by
  induction hab with
  | refl => exact dvd_rfl
  | step _ ih => exact ih.trans (h.dvd _)

lemma sum_le (h : IsChain Q) (k : ℕ) : ∑ n ∈ range k, Q (n + 1) ≤ 2 * Q k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have := h.two k
    omega

def ratio (Q : ℕ → ℕ) (n : ℕ) : ℕ := Q (n + 1) / Q n

lemma ratio_mul (h : IsChain Q) (n : ℕ) : ratio Q n * Q n = Q (n + 1) :=
  Nat.div_mul_cancel (h.dvd n)

lemma two_le_ratio (h : IsChain Q) (n : ℕ) : 2 ≤ ratio Q n := by
  unfold ratio
  exact (Nat.le_div_iff_mul_le (h.pos n)).2 (h.two n)

lemma ratio_cast (h : IsChain Q) (n : ℕ) : (ratio Q n : ℝ) = (Q (n + 1) : ℝ) / Q n := by
  have h0 : (Q n : ℝ) ≠ 0 := by exact_mod_cast (h.pos n).ne'
  rw [eq_div_iff h0]
  exact_mod_cast h.ratio_mul n

end IsChain

/-! ## One chain: an approximate character is a short signed sum -/

lemma one_chain {Q : ℕ → ℕ} (hQ : IsChain Q) {x r θ C X1 : ℝ} (hr : 0 < r) (hr2 : r ≤ 1 / 2)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC : C = 1 / (θ * r)) (J : ℕ) (hJ : (Q (J + 1) : ℝ) ≤ X1)
    (hx : ∀ z : ℤ, nd (z * x) ≤ (Pn Q z / r + 2 * |(z : ℝ)| / X1) / θ)
    (nstar : ℕ) (hn : ∀ S : Finset ℕ, (∀ n ∈ S, (Q (n + 1) : ℝ) / Q n < 32 * C) → S.card ≤ nstar) :
    ∃ (a0 : ℤ) (h : ℕ → ℤ), (∑ n ∈ range J, |(h n : ℝ)|) ≤ 2 * C * (8 + 2 * nstar) ∧
      |x - a0 - ∑ n ∈ range J, (h n : ℝ) / Q (n + 1)| ≤ 2 * C / Q (J + 1) := by
  classical
  have hθr : 0 < θ * r := mul_pos hθ hr
  have hCpos : 0 < C := by rw [hC]; positivity
  have hθr' : θ * r ≤ 1 / 2 := by
    have := mul_le_mul hθ1 hr2 hr.le zero_le_one
    linarith
  have hC2 : 2 ≤ C := by
    rw [hC, le_div_iff₀ hθr]
    linarith
  have hCθr : C * (θ * r) = 1 := by
    rw [hC]; field_simp
  have hQr : ∀ n, (0 : ℝ) < Q n := fun n => by exact_mod_cast hQ.pos n
  have hX1 : 0 < X1 := lt_of_lt_of_le (hQr _) hJ
  set R : ℕ → ℝ := fun n => (IsChain.ratio Q n : ℝ) with hR
  have hR2 : ∀ n, 2 ≤ R n := fun n => by simp only [hR]; exact_mod_cast hQ.two_le_ratio n
  have hRpos : ∀ n, 0 < R n := fun n => lt_of_lt_of_le two_pos (hR2 n)
  have hRQ : ∀ n, R n * Q n = Q (n + 1) := fun n => by
    simp only [hR]; exact_mod_cast hQ.ratio_mul n
  set a : ℕ → ℤ := fun n => round (x * Q n) with ha
  set ε : ℕ → ℝ := fun n => x * Q n - a n with hε
  have hxa : ∀ n, x * Q n = a n + ε n := fun n => by simp only [hε]; ring
  -- (i)
  have hi : ∀ n, n ≤ J → |ε n| ≤ 2 * C / R n := by
    intro n hnJ
    have h1 : nd (((Q n : ℤ) : ℝ) * x) = |ε n| := by
      unfold nd
      simp only [hε, ha]
      push_cast
      rw [mul_comm]
    have hP : Pn Q (Q n : ℤ) ≤ 1 / R n := by
      refine Pn_le fun k => ?_
      by_cases hk : k + 1 ≤ n
      · obtain ⟨d, hd⟩ := hQ.dvd_of_le hk
        have : (((Q n : ℤ)) : ℝ) / Q (k + 1) = ((d : ℤ) : ℝ) := by
          rw [hd]
          push_cast
          have := (hQr (k + 1)).ne'
          field_simp
        rw [this, nd_int]
        exact (div_pos one_pos (hRpos n)).le
      · have hle : Q (n + 1) ≤ Q (k + 1) := hQ.mono (by omega)
        refine le_trans (nd_le_abs _) ?_
        rw [abs_of_nonneg (by positivity)]
        rw [div_le_div_iff₀ (hQr _) (hRpos n)]
        have : (Q (n + 1) : ℝ) ≤ Q (k + 1) := by exact_mod_cast hle
        have h2 := hRQ n
        push_cast
        nlinarith
    have hsize : (Q n : ℝ) / X1 ≤ 1 / R n := by
      rw [div_le_div_iff₀ hX1 (hRpos n)]
      have h2 : (Q (n + 1) : ℝ) ≤ Q (J + 1) := by exact_mod_cast hQ.mono (by omega)
      have h3 := hRQ n
      nlinarith
    have h2 := hx (Q n : ℤ)
    rw [h1] at h2
    refine le_trans h2 ?_
    have habs : |(((Q n : ℤ)) : ℝ)| = (Q n : ℝ) := by
      push_cast; exact abs_of_nonneg (hQr n).le
    rw [habs]
    have h4 : Pn Q (Q n : ℤ) / r + 2 * (Q n : ℝ) / X1 ≤ (1 / R n) / r + 2 * (1 / R n) := by
      refine add_le_add (div_le_div_of_nonneg_right hP hr.le) ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hsize two_pos.le
    refine le_trans (div_le_div_of_nonneg_right h4 hθ.le) ?_
    have h5 : (1 / R n) / r + 2 * (1 / R n) ≤ 2 * ((1 / R n) / r) := by
      have h6 : 2 * (1 / R n) ≤ (1 / R n) / r := by
        rw [le_div_iff₀ hr]
        have : 0 ≤ 1 / R n := (div_pos one_pos (hRpos n)).le
        nlinarith
      linarith
    refine le_trans (div_le_div_of_nonneg_right h5 hθ.le) (le_of_eq ?_)
    rw [hC]
    have := (hRpos n).ne'
    have := hr.ne'
    have := hθ.ne'
    field_simp
  -- (ii)
  set η : ℝ := 1 / (32 * C) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηC : η * C = 1 / 32 := by
    rw [hη]
    have := hCpos.ne'
    field_simp
  set G : Finset ℕ := (range (J + 1)).filter (fun n => 1 ≤ η * R n) with hG
  set cf : ℕ → ℕ := fun n => ⌊η * R n⌋₊ with hcf
  have hcf_le : ∀ n, (cf n : ℝ) ≤ η * R n := fun n =>
    Nat.floor_le (mul_nonneg hηpos.le (hRpos n).le)
  have hcf_ge : ∀ n ∈ G, η * R n / 2 ≤ cf n := by
    intro n hnG
    have h1 : 1 ≤ η * R n := (mem_filter.1 hnG).2
    have h2 : (1 : ℝ) ≤ cf n := by
      have : 1 ≤ cf n := Nat.le_floor (by simpa using h1)
      exact_mod_cast this
    have h3 : η * R n < cf n + 1 := Nat.lt_floor_add_one _
    linarith
  have hcfQ : ∀ n, (cf n : ℝ) * Q n ≤ η * Q (n + 1) := by
    intro n
    rw [← hRQ n, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hcf_le n) (hQr n).le
  have hsumQ : ∀ k, ∑ n ∈ range k, (Q (n + 1) : ℝ) ≤ 2 * Q k := fun k => by
    exact_mod_cast hQ.sum_le k
  have hterm : ∀ n ∈ G, (cf n : ℝ) * |ε n| ≤ 1 / 16 := by
    intro n hnG
    have hnJ : n ≤ J := by
      have := mem_range.1 (mem_filter.1 hnG).1
      omega
    have h1 := mul_le_mul (hcf_le n) (hi n hnJ) (abs_nonneg _) (mul_nonneg hηpos.le (hRpos n).le)
    refine le_trans h1 (le_of_eq ?_)
    have h2 : η * R n * (2 * C / R n) = 2 * (η * C) := by
      have := (hRpos n).ne'
      field_simp
    rw [h2, hηC]; norm_num
  have hsubset : ∀ S : Finset ℕ, S ⊆ G → ∑ n ∈ S, (cf n : ℝ) * |ε n| ≤ 1 / 4 →
      ∑ n ∈ S, (cf n : ℝ) * |ε n| ≤ 1 / 8 := by
    intro S hSG hS4
    set σ : ℕ → ℤ := fun n => if 0 ≤ ε n then 1 else -1 with hσ
    set z : ℤ := ∑ n ∈ S, σ n * (cf n : ℤ) * (Q n : ℤ) with hz
    have hσabs : ∀ n, |(σ n : ℝ)| = 1 := fun n => by
      simp only [hσ]; split_ifs <;> simp
    have hσε : ∀ n, (σ n : ℝ) * ε n = |ε n| := fun n => by
      simp only [hσ]
      split_ifs with h
      · simp [abs_of_nonneg h]
      · push_neg at h
        simp [abs_of_neg h]
    have htermabs : ∀ n, |(σ n : ℝ) * cf n * Q n| = (cf n : ℝ) * Q n := fun n => by
      rw [abs_mul, abs_mul, hσabs, one_mul, Nat.abs_cast, Nat.abs_cast]
    have hSrange : ∀ n ∈ S, n < J + 1 := fun n hnS => mem_range.1 (mem_filter.1 (hSG hnS)).1
    have hPz : Pn Q z ≤ 2 * η := by
      refine Pn_le fun k => ?_
      set K := k + 1 with hK
      set z1 : ℤ := ∑ n ∈ S.filter (fun n => n < K), σ n * (cf n : ℤ) * (Q n : ℤ) with hz1
      set z2 : ℤ := ∑ n ∈ S.filter (fun n => ¬ n < K), σ n * (cf n : ℤ) * (Q n : ℤ) with hz2
      have hsplit : z = z1 + z2 := (sum_filter_add_sum_filter_not S (fun n => n < K) _).symm
      have hdvd : (Q K : ℤ) ∣ z2 := by
        refine dvd_sum fun n hn => ?_
        have hKn : K ≤ n := not_lt.1 (mem_filter.1 hn).2
        exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 (hQ.dvd_of_le hKn)) _
      obtain ⟨d, hd⟩ := hdvd
      have h1 : (z : ℝ) / Q K = (z1 : ℝ) / Q K + (d : ℝ) := by
        rw [hsplit, hd]
        push_cast
        have := (hQr K).ne'
        field_simp
      rw [h1, nd_add_int]
      refine le_trans (nd_le_abs _) ?_
      rw [abs_div, abs_of_pos (hQr K), div_le_iff₀ (hQr K)]
      have h2 : |(z1 : ℝ)| ≤ ∑ n ∈ S.filter (fun n => n < K), (cf n : ℝ) * Q n := by
        rw [hz1]
        push_cast
        refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun n _ => le_of_eq (htermabs n))
      refine le_trans h2 ?_
      have h3 : ∑ n ∈ S.filter (fun n => n < K), (cf n : ℝ) * Q n
          ≤ ∑ n ∈ range K, η * Q (n + 1) := by
        refine le_trans (sum_le_sum fun n _ => hcfQ n) ?_
        refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => ?_)
        · exact mem_range.2 (mem_filter.1 hn).2
        · exact mul_nonneg hηpos.le (hQr _).le
      refine le_trans h3 ?_
      rw [← mul_sum]
      have := mul_le_mul_of_nonneg_left (hsumQ K) hηpos.le
      linarith
    have hzabs : |(z : ℝ)| ≤ 2 * η * X1 := by
      have h2 : |(z : ℝ)| ≤ ∑ n ∈ S, (cf n : ℝ) * Q n := by
        rw [hz]
        push_cast
        refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun n _ => le_of_eq (htermabs n))
      refine le_trans h2 ?_
      have h3 : ∑ n ∈ S, (cf n : ℝ) * Q n ≤ ∑ n ∈ range (J + 1), η * Q (n + 1) := by
        refine le_trans (sum_le_sum fun n _ => hcfQ n) ?_
        refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => ?_)
        · exact mem_range.2 (hSrange n hn)
        · exact mul_nonneg hηpos.le (hQr _).le
      refine le_trans h3 ?_
      rw [← mul_sum]
      have h4 := mul_le_mul_of_nonneg_left (hsumQ (J + 1)) hηpos.le
      have h5 := mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ 2 * η)
      linarith
    have hnz : nd (z * x) ≤ 1 / 8 := by
      refine le_trans (hx z) ?_
      have h1 : Pn Q z / r + 2 * |(z : ℝ)| / X1 ≤ (2 * η) / r + 4 * η := by
        refine add_le_add (div_le_div_of_nonneg_right hPz hr.le) ?_
        rw [div_le_iff₀ hX1]
        linarith
      have h2 : (2 * η) / r + 4 * η ≤ (4 * η) / r := by
        have h3 : 4 * η ≤ (2 * η) / r := by
          rw [le_div_iff₀ hr]
          nlinarith
        have h4 : (4 * η) / r = (2 * η) / r + (2 * η) / r := by ring
        linarith
      refine le_trans (div_le_div_of_nonneg_right (le_trans h1 h2) hθ.le) (le_of_eq ?_)
      have h5 : 4 * η / r / θ = 4 * (η * C) := by
        rw [hC]
        have := hr.ne'
        have := hθ.ne'
        field_simp
      rw [h5, hηC]; norm_num
    have hzx : (z : ℝ) * x = (∑ n ∈ S, (cf n : ℝ) * |ε n|)
        + ((∑ n ∈ S, σ n * (cf n : ℤ) * a n : ℤ) : ℝ) := by
      rw [hz]
      push_cast
      rw [sum_mul, ← sum_add_distrib]
      refine sum_congr rfl fun n _ => ?_
      have h1 : (σ n : ℝ) * cf n * Q n * x = (σ n : ℝ) * cf n * (x * Q n) := by ring
      rw [h1, hxa n, ← hσε n]
      ring
    rw [hzx, nd_add_int, nd_of_small] at hnz
    · exact hnz
    · exact sum_nonneg fun n _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
    · linarith
  have hall : ∀ S : Finset ℕ, S ⊆ G → ∑ n ∈ S, (cf n : ℝ) * |ε n| ≤ 1 / 8 := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simp
    | insert b S hb ih =>
      intro hsub
      have hbG : b ∈ G := hsub (mem_insert_self _ _)
      have hSG : S ⊆ G := fun y hy => hsub (mem_insert_of_mem hy)
      refine hsubset _ hsub ?_
      rw [sum_insert hb]
      have := ih hSG
      have := hterm b hbG
      linarith
  have hGsum : ∑ n ∈ G, R n * |ε n| ≤ 8 * C := by
    have h1 : ∀ n ∈ G, R n * |ε n| ≤ (2 / η) * ((cf n : ℝ) * |ε n|) := by
      intro n hnG
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      rw [div_mul_eq_mul_div, le_div_iff₀ hηpos]
      have := hcf_ge n hnG
      linarith
    refine le_trans (sum_le_sum h1) ?_
    rw [← mul_sum]
    refine le_trans (mul_le_mul_of_nonneg_left (hall G subset_rfl) (by positivity)) (le_of_eq ?_)
    rw [hη]
    have := hCpos.ne'
    field_simp
    ring
  -- (iii)
  have hrest : ∑ n ∈ (range (J + 1)).filter (fun n => ¬ 1 ≤ η * R n), R n * |ε n|
      ≤ 2 * C * nstar := by
    set B := (range (J + 1)).filter (fun n => ¬ 1 ≤ η * R n) with hB
    have h1 : ∀ n ∈ B, R n * |ε n| ≤ 2 * C := by
      intro n hnB
      have hnJ : n ≤ J := by
        have := mem_range.1 (mem_filter.1 hnB).1
        omega
      have := mul_le_mul_of_nonneg_left (hi n hnJ) (hRpos n).le
      refine le_trans this (le_of_eq ?_)
      have := (hRpos n).ne'
      field_simp
    have h2 : B.card ≤ nstar := by
      refine hn B fun n hnB => ?_
      have h3 : η * R n < 1 := not_le.1 (mem_filter.1 hnB).2
      rw [← hQ.ratio_cast n]
      change R n < 32 * C
      rw [hη, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)] at h3
      exact h3
    refine le_trans (sum_le_sum h1) ?_
    rw [sum_const, nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast h2) (by positivity)
  have htot : ∑ n ∈ range (J + 1), R n * |ε n| ≤ 8 * C + 2 * C * nstar := by
    rw [← sum_filter_add_sum_filter_not (range (J + 1)) (fun n => 1 ≤ η * R n)]
    exact add_le_add hGsum hrest
  -- (iv)
  set h : ℕ → ℤ := fun n => a (n + 1) - (IsChain.ratio Q n : ℤ) * a n with hh
  have hhε : ∀ n, (h n : ℝ) = R n * ε n - ε (n + 1) := by
    intro n
    have h1 : x * Q (n + 1) = R n * (x * Q n) := by
      rw [← hRQ n]; ring
    rw [hxa (n + 1), hxa n] at h1
    have h2 : (h n : ℝ) = a (n + 1) - R n * a n := by
      simp only [hh, hR]; push_cast; ring
    rw [h2]
    linear_combination h1
  refine ⟨a 0, h, ?_, ?_⟩
  · have h1 : ∀ n ∈ range J, |(h n : ℝ)| ≤ R n * |ε n| + |ε (n + 1)| := by
      intro n _
      rw [hhε]
      refine le_trans (abs_sub _ _) (le_of_eq ?_)
      rw [abs_mul, abs_of_pos (hRpos n)]
    refine le_trans (sum_le_sum h1) ?_
    rw [sum_add_distrib]
    have h2 : ∑ n ∈ range J, R n * |ε n| ≤ ∑ n ∈ range (J + 1), R n * |ε n| := by
      rw [sum_range_succ]
      have := mul_nonneg (hRpos J).le (abs_nonneg (ε J))
      linarith
    have h3 : ∑ n ∈ range J, |ε (n + 1)| ≤ ∑ n ∈ range (J + 1), R n * |ε n| := by
      have h4 : ∑ n ∈ range J, |ε (n + 1)| ≤ ∑ n ∈ range (J + 1), |ε n| := by
        rw [sum_range_succ' (fun n => |ε n|)]
        have := abs_nonneg (ε 0)
        linarith
      refine le_trans h4 (sum_le_sum fun n _ => ?_)
      have := hR2 n
      have := abs_nonneg (ε n)
      nlinarith
    linarith
  · have h1 : ∀ n, (h n : ℝ) / Q (n + 1) = (a (n + 1) : ℝ) / Q (n + 1) - (a n : ℝ) / Q n := by
      intro n
      have h2 : (h n : ℝ) = a (n + 1) - R n * a n := by
        simp only [hh, hR]; push_cast; ring
      rw [h2, sub_div, ← hRQ n]
      have := (hRpos n).ne'
      have := (hQr n).ne'
      field_simp
    have h3 : ∑ n ∈ range J, (h n : ℝ) / Q (n + 1) = (a J : ℝ) / Q J - a 0 := by
      rw [sum_congr rfl fun n _ => h1 n, sum_range_sub (fun n => (a n : ℝ) / Q n)]
      simp [hQ.zero]
    have h4 : x - (a 0 : ℝ) - ∑ n ∈ range J, (h n : ℝ) / Q (n + 1) = ε J / Q J := by
      rw [h3]
      have h5 : x = ((a J : ℝ) + ε J) / Q J := by
        rw [← hxa J]
        have := (hQr J).ne'
        field_simp
      rw [h5]
      ring
    rw [h4, abs_div, abs_of_pos (hQr J)]
    refine le_trans (div_le_div_of_nonneg_right (hi J le_rfl) (hQr J).le) (le_of_eq ?_)
    rw [← hRQ J, div_div]

/-! ## The gap argument -/

def Tseq (s H T0 : ℕ) : ℕ → ℕ
  | 0 => T0
  | i + 1 => 2 * s * H * (Tseq s H T0 i) ^ s

lemma Tseq_mono {s H T0 : ℕ} (hs : 1 ≤ s) (hH : 1 ≤ H) (hT : 1 ≤ T0) :
    Monotone (Tseq s H T0) ∧ ∀ i, 1 ≤ Tseq s H T0 i := by
  have step : ∀ i, 1 ≤ Tseq s H T0 i → Tseq s H T0 i ≤ Tseq s H T0 (i + 1) := by
    intro i hi
    change Tseq s H T0 i ≤ 2 * s * H * (Tseq s H T0 i) ^ s
    have h1 : Tseq s H T0 i ≤ (Tseq s H T0 i) ^ s := Nat.le_self_pow (by omega) _
    have h2 : 1 ≤ 2 * s * H := by
      have : 1 ≤ s * H := Nat.mul_pos hs hH
      rw [mul_assoc]; omega
    calc Tseq s H T0 i ≤ 1 * (Tseq s H T0 i) ^ s := by simpa using h1
      _ ≤ 2 * s * H * (Tseq s H T0 i) ^ s := Nat.mul_le_mul_right _ h2
  have pos : ∀ i, 1 ≤ Tseq s H T0 i := by
    intro i
    induction i with
    | zero => exact hT
    | succ i ih => exact le_trans ih (step i ih)
  exact ⟨monotone_nat_of_le_succ fun i => step i (pos i), pos⟩

lemma gap {m : ℕ} (Q : Fin (m + 1) → ℕ → ℕ) (hQ : ∀ j, IsChain (Q j))
    (hco : ∀ i j, i ≠ j → ∀ a b, Nat.Coprime (Q i a) (Q j b))
    (H : ℕ) (hH : 1 ≤ H) (J : Fin (m + 1) → ℕ) (h : Fin (m + 1) → ℕ → ℤ)
    (hsum : ∀ j, ∑ n ∈ range (J j), (h j n).natAbs ≤ H)
    (T0 : ℕ) (hT0 : 1 ≤ T0) (σ : Fin (m + 1) → ℤ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hsmall : nd (∑ j, (σ j : ℝ) * ∑ n ∈ range (J j), (h j n : ℝ) / Q j (n + 1))
      < 1 / (2 * (Tseq (m + 1) H T0 ((m + 1) * H) : ℝ) ^ (m + 1))) :
    ∀ j, nd (∑ n ∈ range (J j), (h j n : ℝ) / Q j (n + 1)) ≤ (H : ℝ) / Tseq (m + 1) H T0 1 := by
  classical
  let s : ℕ := m + 1
  have hs : s = m + 1 := rfl
  have hs1 : 1 ≤ s := by omega
  set T := Tseq s H T0 with hT
  obtain ⟨hmono, hpos⟩ := Tseq_mono hs1 hH hT0
  rw [← hT] at hmono hpos
  set D : Finset (Σ _ : Fin (m + 1), ℕ) :=
    univ.sigma fun j => (range (J j)).filter (fun n => h j n ≠ 0) with hD
  have hDcard : D.card ≤ s * H := by
    rw [hD, card_sigma]
    have h1 : ∀ j : Fin (m + 1), ((range (J j)).filter (fun n => h j n ≠ 0)).card ≤ H := by
      intro j
      refine le_trans ?_ (hsum j)
      rw [card_eq_sum_ones]
      refine le_trans (sum_le_sum fun n hn => ?_)
        (sum_le_sum_of_subset (f := fun n => (h j n).natAbs) (filter_subset _ _))
      have := Int.natAbs_pos.2 (mem_filter.1 hn).2
      omega
    refine le_trans (sum_le_sum fun j _ => h1 j) ?_
    simp [hs]
  have hgap : ∃ i, i < s * H + 1 ∧ ∀ d ∈ D, ¬ (T i < Q d.1 (d.2 + 1) ∧ Q d.1 (d.2 + 1) ≤ T (i + 1)) := by
    by_contra hcon
    push_neg at hcon
    choose f hfD hflt hfle using fun i : Fin (s * H + 1) => hcon i.1 i.2
    have hinj : Function.Injective (fun i : Fin (s * H + 1) => (⟨f i, hfD i⟩ : D)) := by
      intro i k hik
      have hfk : f i = f k := congrArg Subtype.val hik
      rcases lt_trichotomy i.1 k.1 with hlt | heq | hgt
      · have h1 := hfle i
        have h2 := hflt k
        have h3 : T (i.1 + 1) ≤ T k.1 := hmono hlt
        rw [hfk] at h1
        omega
      · exact Fin.ext heq
      · have h1 := hfle k
        have h2 := hflt i
        have h3 : T (k.1 + 1) ≤ T i.1 := hmono hgt
        rw [← hfk] at h1
        omega
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_fin, Fintype.card_coe] at this
    omega
  obtain ⟨i, hi, hempty⟩ := hgap
  set Ti := T i with hTi
  have hTi1 : 1 ≤ Ti := hpos i
  have hTnext : T (i + 1) = 2 * s * H * Ti ^ s := rfl
  have hTir : (0 : ℝ) < Ti := by exact_mod_cast hTi1
  have hQr : ∀ j n, (0 : ℝ) < Q j n := fun j n => by exact_mod_cast (hQ j).pos n
  -- largest modulus of each chain not exceeding `Ti`
  set N : Fin (m + 1) → ℕ := fun j => Nat.findGreatest (fun n => Q j n ≤ Ti) Ti with hN
  set P : Fin (m + 1) → ℕ := fun j => Q j (N j) with hP
  have hPle : ∀ j, P j ≤ Ti := by
    intro j
    have h0 : Q j 0 ≤ Ti := by rw [(hQ j).zero]; exact hTi1
    exact Nat.findGreatest_spec (P := fun n => Q j n ≤ Ti) (Nat.zero_le _) h0
  have hPpos : ∀ j, 0 < P j := fun j => (hQ j).pos _
  have hPdvd : ∀ j n, Q j n ≤ Ti → Q j n ∣ P j := by
    intro j n hn
    refine (hQ j).dvd_of_le (Nat.le_findGreatest ?_ hn)
    have h1 := (hQ j).two_pow n
    have h2 : n < 2 ^ n := Nat.lt_two_pow_self
    omega
  set A : Fin (m + 1) → ℤ := fun j =>
    ∑ n ∈ (range (J j)).filter (fun n => Q j (n + 1) ≤ Ti), h j n * ((P j / Q j (n + 1) : ℕ) : ℤ) with hA
  set fine : Fin (m + 1) → ℝ := fun j =>
    ∑ n ∈ (range (J j)).filter (fun n => ¬ Q j (n + 1) ≤ Ti), (h j n : ℝ) / Q j (n + 1) with hfine
  have hsplit : ∀ j, ∑ n ∈ range (J j), (h j n : ℝ) / Q j (n + 1) = (A j : ℝ) / P j + fine j := by
    intro j
    rw [← sum_filter_add_sum_filter_not (range (J j)) (fun n => Q j (n + 1) ≤ Ti)]
    congr 1
    simp only [hA]
    rw [Int.cast_sum, sum_div]
    refine sum_congr rfl fun n hn => ?_
    have hdv : Q j (n + 1) ∣ P j := hPdvd j (n + 1) (mem_filter.1 hn).2
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hdv (hQr j (n + 1)).ne']
    have := (hQr j (n + 1)).ne'
    have : (P j : ℝ) ≠ 0 := by exact_mod_cast (hPpos j).ne'
    field_simp
  have hTnr : (0 : ℝ) < T (i + 1) := by exact_mod_cast hpos (i + 1)
  have hfineb : ∀ j, |fine j| ≤ (H : ℝ) / T (i + 1) := by
    intro j
    simp only [hfine]
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    have h1 : ∀ n ∈ (range (J j)).filter (fun n => ¬ Q j (n + 1) ≤ Ti),
        |(h j n : ℝ) / Q j (n + 1)| ≤ ((h j n).natAbs : ℝ) / T (i + 1) := by
      intro n hn
      have habs : |(h j n : ℝ)| = ((h j n).natAbs : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [abs_div, abs_of_pos (hQr j (n + 1)), habs]
      by_cases h0 : h j n = 0
      · simp [h0]
      · have hmem : (⟨j, n⟩ : Σ _ : Fin (m + 1), ℕ) ∈ D := by
          rw [hD, mem_sigma]
          exact ⟨mem_univ _, mem_filter.2 ⟨(mem_filter.1 hn).1, h0⟩⟩
        have h2 := hempty _ hmem
        have h3 : Ti < Q j (n + 1) := not_le.1 (mem_filter.1 hn).2
        have h4 : T (i + 1) < Q j (n + 1) := by
          by_contra h5
          exact h2 ⟨h3, not_lt.1 h5⟩
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hTnr (by exact_mod_cast h4.le)
    refine le_trans (sum_le_sum h1) ?_
    rw [← sum_div]
    refine div_le_div_of_nonneg_right ?_ hTnr.le
    have h6 : ∑ n ∈ (range (J j)).filter (fun n => ¬ Q j (n + 1) ≤ Ti), (h j n).natAbs ≤ H :=
      le_trans (sum_le_sum_of_subset (filter_subset _ _)) (hsum j)
    exact_mod_cast h6
  -- the coarse combination
  set Prd : ℕ := ∏ j, P j with hPrd
  set Z : ℤ := ∑ j, σ j * A j * ∏ k ∈ univ.erase j, (P k : ℤ) with hZ
  have hPrdos : 0 < Prd := prod_pos fun j _ => hPpos j
  have hPrdr : (0 : ℝ) < Prd := by exact_mod_cast hPrdos
  have hPrdle : Prd ≤ Ti ^ s := by
    refine le_trans (prod_le_prod' fun j _ => hPle j) ?_
    simp [hs]
  have hZu : (Z : ℝ) / Prd = ∑ j, (σ j : ℝ) * ((A j : ℝ) / P j) := by
    rw [hZ]
    push_cast
    rw [sum_div]
    refine sum_congr rfl fun j _ => ?_
    have h1 : (Prd : ℝ) = (P j : ℝ) * ∏ k ∈ univ.erase j, (P k : ℝ) := by
      rw [hPrd]
      push_cast
      rw [mul_prod_erase univ (fun k => (P k : ℝ)) (mem_univ j)]
    have h2 : ∏ k ∈ univ.erase j, (P k : ℝ) ≠ 0 :=
      prod_ne_zero_iff.2 fun k _ => by exact_mod_cast (hPpos k).ne'
    have h3 : (P j : ℝ) ≠ 0 := by exact_mod_cast (hPpos j).ne'
    rw [h1]
    field_simp
  have hPrddvd : (Prd : ℤ) ∣ Z := by
    by_contra hnd
    have h1 : 1 / (Prd : ℝ) ≤ nd ((Z : ℝ) / Prd) := by
      unfold nd
      set b := round ((Z : ℝ) / Prd) with hb
      have h2 : (Z : ℝ) / Prd - b = ((Z - b * Prd : ℤ) : ℝ) / Prd := by
        push_cast
        have := hPrdr.ne'
        field_simp
      have h3 : Z - b * (Prd : ℤ) ≠ 0 := by
        intro h4
        exact hnd ⟨b, by rw [mul_comm]; omega⟩
      have h5 : (1 : ℝ) ≤ |((Z - b * Prd : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs h3
      rw [h2, abs_div, abs_of_pos hPrdr]
      exact div_le_div_of_nonneg_right h5 hPrdr.le
    have h6 : 1 / (Ti : ℝ) ^ s ≤ 1 / (Prd : ℝ) :=
      one_div_le_one_div_of_le hPrdr (by exact_mod_cast hPrdle)
    set total := ∑ j, (σ j : ℝ) * ∑ n ∈ range (J j), (h j n : ℝ) / Q j (n + 1) with htotal
    set ft := ∑ j, (σ j : ℝ) * fine j with hft
    have h7 : (Z : ℝ) / Prd = total + (-ft) := by
      rw [hZu, htotal, hft, ← sub_eq_add_neg, ← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      rw [hsplit j]
      ring
    have h8 : |ft| ≤ 1 / (2 * (Ti : ℝ) ^ s) := by
      rw [hft]
      refine le_trans (abs_sum_le_sum_abs _ _) ?_
      have h9 : ∀ j : Fin (m + 1), |(σ j : ℝ) * fine j| ≤ (H : ℝ) / T (i + 1) := by
        intro j
        have h10 : |(σ j : ℝ)| = 1 := by
          rcases hσ j with h | h <;> simp [h]
        rw [abs_mul, h10, one_mul]
        exact hfineb j
      refine le_trans (sum_le_sum fun j _ => h9 j) (le_of_eq ?_)
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← hs, hTnext]
      push_cast
      have h11 : (H : ℝ) ≠ 0 := by
        have : (0 : ℝ) < H := by exact_mod_cast hH
        exact this.ne'
      have h12 : (s : ℝ) ≠ 0 := by
        have : (0 : ℝ) < s := by exact_mod_cast hs1
        exact this.ne'
      have h13 := hTir.ne'
      field_simp
    have h14 : nd ((Z : ℝ) / Prd) ≤ nd total + |ft| := by
      rw [h7]
      refine le_trans (nd_add_le _ _) (add_le_add le_rfl ?_)
      rw [nd_neg]
      exact nd_le_abs _
    have h15 : 1 / (2 * (T (s * H) : ℝ) ^ s) ≤ 1 / (2 * (Ti : ℝ) ^ s) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have h16 : Ti ≤ T (s * H) := hmono (by omega)
      have h17 : (Ti : ℝ) ≤ T (s * H) := by exact_mod_cast h16
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hTir.le h17 _) two_pos.le
    have h18 : 1 / (Ti : ℝ) ^ s = 1 / (2 * (Ti : ℝ) ^ s) + 1 / (2 * (Ti : ℝ) ^ s) := by
      have := hTir.ne'
      field_simp
      ring
    linarith
  have hPdvdA : ∀ j, (P j : ℤ) ∣ A j := by
    intro j
    have h1 : (P j : ℤ) ∣ Z := by
      refine dvd_trans (Int.natCast_dvd_natCast.2 ?_) hPrddvd
      exact dvd_prod_of_mem _ (mem_univ j)
    have h2 : (P j : ℤ) ∣ ∑ k ∈ univ.erase j, σ k * A k * ∏ l ∈ univ.erase k, (P l : ℤ) := by
      refine dvd_sum fun k hk => ?_
      have hjk : j ∈ univ.erase k := mem_erase.2 ⟨(mem_erase.1 hk).1.symm, mem_univ _⟩
      exact Dvd.dvd.mul_left (dvd_prod_of_mem _ hjk) _
    have h3 : (P j : ℤ) ∣ σ j * A j * ∏ k ∈ univ.erase j, (P k : ℤ) := by
      have h4 := add_sum_erase univ (fun k => σ k * A k * ∏ l ∈ univ.erase k, (P l : ℤ)) (mem_univ j)
      rw [← hZ] at h4
      have h5 := dvd_sub h1 h2
      rwa [← h4, add_sub_cancel_right] at h5
    have h6 : IsCoprime (P j : ℤ) (∏ k ∈ univ.erase j, (P k : ℤ)) := by
      refine IsCoprime.prod_right fun k hk => ?_
      exact Nat.isCoprime_iff_coprime.2 (hco j k (mem_erase.1 hk).1.symm _ _)
    have h7 : (P j : ℤ) ∣ σ j * A j := h6.dvd_of_dvd_mul_right h3
    rcases hσ j with h8 | h8
    · simpa [h8] using h7
    · simpa [h8] using h7
  intro j
  obtain ⟨q, hq⟩ := hPdvdA j
  have h1 : (A j : ℝ) / P j = (q : ℝ) := by
    rw [hq]
    push_cast
    have : (P j : ℝ) ≠ 0 := by exact_mod_cast (hPpos j).ne'
    field_simp
  rw [hsplit j, h1, add_comm, nd_add_int]
  refine le_trans (nd_le_abs _) (le_trans (hfineb j) ?_)
  have h2 : T 1 ≤ T (i + 1) := hmono (by omega)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hpos 1)
    (by exact_mod_cast h2)

/-! ## Finite Fourier analysis on `(ℤ/M)^m` -/

noncomputable def om (M : ℕ) (a : ℤ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * a / M)

lemma om_add (M : ℕ) (a b : ℤ) : om M (a + b) = om M a * om M b := by
  unfold om
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

lemma om_zero (M : ℕ) : om M 0 = 1 := by simp [om]

lemma om_natmul (M : ℕ) (k : ℕ) (a : ℤ) : om M (k * a) = om M a ^ k := by
  unfold om
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

lemma om_sum {ι : Type*} (M : ℕ) (s : Finset ι) (f : ι → ℤ) :
    om M (∑ i ∈ s, f i) = ∏ i ∈ s, om M (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [om_zero]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, om_add, ih]

lemma om_eq_one_iff {M : ℕ} (hM : 0 < M) (a : ℤ) : om M a = 1 ↔ (M : ℤ) ∣ a := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  unfold om
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h1 : (a : ℂ) = (M : ℂ) * n := by
      rw [div_eq_iff hMc] at hn
      have h2 : (2 * (Real.pi : ℂ) * Complex.I) * a = (2 * (Real.pi : ℂ) * Complex.I) * ((M : ℂ) * n) := by
        rw [hn]; ring
      exact mul_left_cancel₀ h2pi h2
    exact_mod_cast h1
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    push_cast
    field_simp

noncomputable def chi {m : ℕ} (M : ℕ) (ξ : Fin m → Fin M) (t : Fin m → ℤ) : ℂ :=
  om M (∑ i, ((ξ i : ℕ) : ℤ) * t i)

lemma chi_add {m : ℕ} (M : ℕ) (ξ : Fin m → Fin M) (t u : Fin m → ℤ) :
    chi M ξ (t + u) = chi M ξ t * chi M ξ u := by
  unfold chi
  rw [← om_add, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun i _ => by rw [Pi.add_apply, mul_add]

lemma chi_norm {m : ℕ} (M : ℕ) (ξ : Fin m → Fin M) (t : Fin m → ℤ) : ‖chi M ξ t‖ = 1 := by
  unfold chi om
  have h : (2 * (Real.pi : ℂ) * Complex.I * ((∑ i, ((ξ i : ℕ) : ℤ) * t i : ℤ) : ℂ) / M)
      = ((2 * Real.pi * ((∑ i, ((ξ i : ℕ) : ℤ) * t i : ℤ) : ℝ) / M : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma chi_conj {m : ℕ} (M : ℕ) (ξ : Fin m → Fin M) (t : Fin m → ℤ) :
    (starRingEnd ℂ) (chi M ξ t) = chi M ξ (-t) := by
  unfold chi om
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_natCast,
    map_ofNat, Pi.neg_apply, mul_neg, sum_neg_distrib, Int.cast_neg]
  ring

lemma chi_orth {m M : ℕ} (hM : 0 < M) (t : Fin m → ℤ) :
    ∑ ξ : Fin m → Fin M, chi M ξ t = if (∀ i, (M : ℤ) ∣ t i) then (M : ℂ) ^ m else 0 := by
  have h1 : ∀ ξ : Fin m → Fin M, chi M ξ t = ∏ i, om M (t i) ^ ((ξ i : ℕ)) := by
    intro ξ
    unfold chi
    rw [om_sum]
    exact prod_congr rfl fun i _ => om_natmul M _ _
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (i : Fin m) (x : Fin M) => om M (t i) ^ (x : ℕ))]
  have h2 : ∀ a : ℤ, ∑ x : Fin M, om M a ^ (x : ℕ) = if (M : ℤ) ∣ a then (M : ℂ) else 0 := by
    intro a
    rw [Fin.sum_univ_eq_sum_range (fun x => om M a ^ x)]
    split_ifs with h
    · rw [(om_eq_one_iff hM a).2 h]; simp
    · have h3 : om M a ≠ 1 := fun h4 => h ((om_eq_one_iff hM a).1 h4)
      have h5 : om M a ^ M = 1 := by
        rw [← om_natmul, om_eq_one_iff hM]
        exact dvd_mul_right _ _
      rw [geom_sum_eq h3, h5, sub_self, zero_div]
  simp_rw [h2]
  split_ifs with h
  · rw [prod_congr rfl fun i _ => if_pos (h i), prod_const, card_univ, Fintype.card_fin]
  · obtain ⟨i, hi⟩ := not_forall.1 h
    exact prod_eq_zero (mem_univ i) (if_neg hi)

/-- Parseval for a finitely supported function whose support does not wrap around. -/
lemma parseval {m M : ℕ} (hM : 0 < M) (T : Finset (Fin m → ℤ)) (f : (Fin m → ℤ) → ℝ)
    (hinj : ∀ a ∈ T, ∀ b ∈ T, (∀ i, (M : ℤ) ∣ b i - a i) → a = b) :
    ∑ ξ : Fin m → Fin M, ‖∑ a ∈ T, (f a : ℂ) * chi M ξ (-a)‖ ^ 2
      = (M : ℝ) ^ m * ∑ a ∈ T, f a ^ 2 := by
  classical
  have h1 : ∑ ξ : Fin m → Fin M,
      (∑ a ∈ T, (f a : ℂ) * chi M ξ (-a)) * (starRingEnd ℂ) (∑ b ∈ T, (f b : ℂ) * chi M ξ (-b))
      = (M : ℂ) ^ m * ∑ a ∈ T, (f a : ℂ) ^ 2 := by
    have h2 : ∀ ξ : Fin m → Fin M,
        (∑ a ∈ T, (f a : ℂ) * chi M ξ (-a)) * (starRingEnd ℂ) (∑ b ∈ T, (f b : ℂ) * chi M ξ (-b))
        = ∑ a ∈ T, ∑ b ∈ T, ((f a : ℂ) * f b) * chi M ξ (b - a) := by
      intro ξ
      rw [map_sum, sum_mul_sum]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [map_mul, Complex.conj_ofReal, chi_conj, neg_neg, sub_eq_neg_add, add_comm (-a) b]
      rw [chi_add M ξ b (-a)]
      ring
    simp_rw [h2]
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun a ha => ?_
    rw [sum_comm]
    simp_rw [← mul_sum, chi_orth hM]
    rw [sum_eq_single a]
    · rw [if_pos (fun i => by simp)]
      ring
    · intro b hb hba
      rw [if_neg, mul_zero]
      intro h
      exact hba (hinj a ha b hb fun i => by simpa using h i).symm
    · intro h
      exact absurd ha h
  have h3 : ((∑ ξ : Fin m → Fin M, ‖∑ a ∈ T, (f a : ℂ) * chi M ξ (-a)‖ ^ 2 : ℝ) : ℂ)
      = (((M : ℝ) ^ m * ∑ a ∈ T, f a ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [← h1]
    refine sum_congr rfl fun ξ _ => ?_
    rw [Complex.mul_conj']
  exact_mod_cast h3

lemma four_norm_exp (y : ℝ) :
    4 * nd y ≤ ‖Complex.exp (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)) - 1‖ := by
  set u := y - round y with hu
  have h1 : Complex.exp (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((2 * Real.pi * u : ℝ) : ℂ)) := by
    have h2 : Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)
        = Complex.I * ((2 * Real.pi * u : ℝ) : ℂ) + (round y : ℤ) * (2 * Real.pi * Complex.I) := by
      rw [hu]; push_cast; ring
    rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h3 : 2 * Real.pi * u / 2 = Real.pi * u := by ring
  rw [h3, Real.norm_eq_abs, abs_mul, abs_two]
  have h4 : |u| ≤ 1 / 2 := abs_sub_round y
  have h5 : |Real.sin (Real.pi * u)| = |Real.sin (Real.pi * |u|)| := by
    rcases abs_choice u with h | h
    · rw [h]
    · rw [h, mul_neg, Real.sin_neg, abs_neg]
  rw [h5]
  have h6 : 0 ≤ Real.pi * |u| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
  have h7 : Real.pi * |u| ≤ Real.pi / 2 := by
    have := mul_le_mul_of_nonneg_left h4 Real.pi_pos.le
    linarith
  have h8 := Real.mul_le_sin h6 h7
  have h9 : 2 / Real.pi * (Real.pi * |u|) = 2 * |u| := by
    have := Real.pi_pos.ne'
    field_simp
  rw [h9] at h8
  have h10 := le_abs_self (Real.sin (Real.pi * |u|))
  have h11 : nd y = |u| := rfl
  rw [h11]
  linarith

lemma om_eq_exp (M : ℕ) (a : ℤ) :
    om M a = Complex.exp (Complex.I * ((2 * Real.pi * ((a : ℝ) / M) : ℝ) : ℂ)) := by
  unfold om
  congr 1
  push_cast; ring

lemma re_om_ge (M : ℕ) (a : ℤ) (h : nd ((a : ℝ) / M) ≤ 1 / 8) : 7 / 10 ≤ (om M a).re := by
  set y := (a : ℝ) / M with hy
  set u := y - round y with hu
  have h1 : (om M a).re = Real.cos (2 * Real.pi * u) := by
    rw [om_eq_exp, mul_comm, Complex.exp_ofReal_mul_I_re, ← hy]
    have h2 : 2 * Real.pi * y = 2 * Real.pi * u + (round y : ℤ) * (2 * Real.pi) := by
      rw [hu]; ring
    rw [h2, Real.cos_add_int_mul_two_pi]
  rw [h1, ← Real.cos_abs]
  have h3 : |u| ≤ 1 / 8 := h
  have h4 : |2 * Real.pi * u| ≤ Real.pi / 4 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    linarith
  have h5 := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (2 * Real.pi * u))
    (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi) h4
  refine le_trans ?_ h5
  rw [Real.cos_pi_div_four]
  have h6 : (7 : ℝ) / 5 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  linarith

/-! ## The weight and the theorem -/

/-- The covering input at height `X`: a set of target vectors of density `c` in the box of side
about `2X`, each reached by some `|k| ≤ X` with all errors below `r0`. -/
def Input {m : ℕ} (Q : Fin (m + 1) → ℕ → ℕ) (r0 c : ℝ) (X : ℕ) : Prop :=
  ∃ W : Finset (Fin m → ℤ), c * (X : ℝ) ^ m ≤ W.card ∧ ∀ w ∈ W, (∀ i, |w i| ≤ 2 * (X : ℤ)) ∧
    ∃ k : ℤ, |k| ≤ (X : ℤ) ∧ Pn (Q 0) k < r0 ∧ ∀ i : Fin m, Pn (Q i.succ) (k - w i) < r0

noncomputable def alphaM (m : ℕ) (c : ℝ) : ℝ := c / (2 * 24 ^ m)

noncomputable def thetaM (m : ℕ) (c : ℝ) : ℝ := alphaM m c ^ 2 / Real.sqrt (2 ^ (m + 4))

noncomputable def CM (m : ℕ) (r0 c : ℝ) : ℝ := 1 / (thetaM m c * (4 * r0))

noncomputable def HM (m : ℕ) (r0 c : ℝ) (nstar : ℕ) : ℕ := ⌊2 * CM m r0 c * (8 + 2 * nstar)⌋₊

noncomputable def TM (m : ℕ) (r0 c : ℝ) (nstar τ : ℕ) : ℕ → ℕ :=
  Tseq (m + 1) (HM m r0 c nstar) (16 * (m + 1) * τ)

def box (m : ℕ) (L : ℤ) : Finset (Fin m → ℤ) := Fintype.piFinset fun _ => Icc (-L) L

lemma mem_box {m : ℕ} {L : ℤ} {t : Fin m → ℤ} : t ∈ box m L ↔ ∀ i, |t i| ≤ L := by
  simp [box, abs_le]

lemma card_box (m : ℕ) (L : ℤ) (hL : 0 ≤ L) : ((box m L).card : ℤ) = (2 * L + 1) ^ m := by
  unfold box
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, prod_const, card_univ, Fintype.card_fin]
  push_cast
  rw [Int.toNat_of_nonneg (by omega)]
  ring

set_option maxHeartbeats 1600000 in
/-- **Explicit height for shifted targets.** -/
theorem height_M11 {m : ℕ} (Q : Fin (m + 1) → ℕ → ℕ) (hQ : ∀ j, IsChain (Q j))
    (hco : ∀ i j, i ≠ j → ∀ a b, Nat.Coprime (Q i a) (Q j b))
    {r0 c : ℝ} (hr0 : 0 < r0) (hr8 : r0 ≤ 1 / 8) (hc : 0 < c) {X : ℕ} (hX : 1 ≤ X)
    (hI : Input Q r0 c X)
    (nstar : ℕ) (hn : ∀ j, ∀ S : Finset ℕ,
      (∀ n ∈ S, (Q j (n + 1) : ℝ) / Q j n < 32 * CM m r0 c) → S.card ≤ nstar)
    (τ : ℕ) (hτ : 1 ≤ τ) (J : Fin (m + 1) → ℕ) (hJ : ∀ j, Q j (J j + 1) ≤ 12 * X)
    (hbig : ∑ j, 2 * CM m r0 c / Q j (J j + 1)
      < 1 / (2 * (TM m r0 c nstar τ ((m + 1) * HM m r0 c nstar) : ℝ) ^ (m + 1)))
    (t : Fin m → ℤ) (ht : ∀ i, |t i| ≤ (τ : ℤ)) :
    ∃ k : ℤ, |k| ≤ 48 * (X : ℤ) ∧ Pn (Q 0) k < 16 * r0 ∧
      ∀ i : Fin m, Pn (Q i.succ) (k - t i) < 16 * r0 := by
  classical
  set r : ℝ := 4 * r0 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  have hr2 : r ≤ 1 / 2 := by rw [hr]; linarith
  set X1 : ℤ := 12 * (X : ℤ) with hX1
  have hX1pos : 0 < X1 := by rw [hX1]; omega
  set X1r : ℝ := (X1 : ℝ) with hX1r
  have hX1rpos : 0 < X1r := by rw [hX1r]; exact_mod_cast hX1pos
  -- errors, the bracket and the weight
  set err : (Fin m → ℤ) → ℤ → Fin (m + 1) → ℝ := fun s k =>
    Fin.cases (Pn (Q 0) k) (fun i => Pn (Q i.succ) (k - s i)) with herr
  set E : (Fin m → ℤ) → ℤ → ℝ := fun s k => univ.sup' univ_nonempty (err s k) with hE
  set tn : (Fin m → ℤ) → ℕ := fun s => univ.sup fun i => (s i).natAbs with htn
  set br : (Fin m → ℤ) → ℤ → ℝ := fun s k =>
    1 - E s k / r - |(k : ℝ)| / X1r - (tn s : ℝ) / X1r with hbr
  have hne : (Icc (-X1) X1).Nonempty := ⟨0, mem_Icc.2 ⟨by omega, by omega⟩⟩
  set φ : (Fin m → ℤ) → ℝ := fun s => (Icc (-X1) X1).sup' hne (fun k => max (br s k) 0) with hφ
  have herr0 : ∀ s k, err s k 0 = Pn (Q 0) k := fun s k => rfl
  have herrs : ∀ s k (i : Fin m), err s k i.succ = Pn (Q i.succ) (k - s i) := fun s k i => by
    simp [herr]
  have herrnn : ∀ s k l, 0 ≤ err s k l := by
    intro s k l
    refine Fin.cases ?_ (fun i => ?_) l
    · rw [herr0]; exact Pn_nonneg _ _
    · rw [herrs]; exact Pn_nonneg _ _
  have hErr_le_E : ∀ s k l, err s k l ≤ E s k := fun s k l => le_sup' (err s k) (mem_univ l)
  have hEnn : ∀ s k, 0 ≤ E s k := fun s k => le_trans (herrnn s k 0) (hErr_le_E s k 0)
  have htnle : ∀ s i, ((s i).natAbs) ≤ tn s := fun s i =>
    le_sup (f := fun i => (s i).natAbs) (mem_univ i)
  have hφnn : ∀ s, 0 ≤ φ s := by
    intro s
    obtain ⟨k, hk⟩ := hne
    exact le_trans (le_max_right (br s k) 0) (le_sup' (fun k => max (br s k) 0) hk)
  have hbr_le_one : ∀ s k, br s k ≤ 1 := by
    intro s k
    simp only [hbr]
    have h1 : 0 ≤ E s k / r := div_nonneg (hEnn s k) hrpos.le
    have h2 : 0 ≤ |(k : ℝ)| / X1r := div_nonneg (abs_nonneg _) hX1rpos.le
    have h3 : 0 ≤ (tn s : ℝ) / X1r := div_nonneg (Nat.cast_nonneg _) hX1rpos.le
    linarith
  have hφ1 : ∀ s, φ s ≤ 1 := fun s =>
    sup'_le _ _ fun k _ => max_le (hbr_le_one s k) zero_le_one
  have hbrφ : ∀ s k, br s k ≤ φ s := by
    intro s k
    by_cases hk : k ∈ Icc (-X1) X1
    · exact le_trans (le_max_left _ 0) (le_sup' (fun k => max (br s k) 0) hk)
    · refine le_trans ?_ (hφnn s)
      have h1 : X1 < |k| := by
        rw [mem_Icc, ← abs_le] at hk
        exact not_le.1 hk
      have h2 : 1 < |(k : ℝ)| / X1r := by
        rw [one_lt_div hX1rpos, hX1r, ← Int.cast_abs]
        exact_mod_cast h1
      simp only [hbr]
      have h3 : 0 ≤ E s k / r := div_nonneg (hEnn s k) hrpos.le
      have h4 : 0 ≤ (tn s : ℝ) / X1r := div_nonneg (Nat.cast_nonneg _) hX1rpos.le
      linarith
  have hφpos : ∀ s, 0 < φ s → ∃ k : ℤ, 0 < br s k := by
    intro s hs
    obtain ⟨k, _, hk⟩ := exists_mem_eq_sup' hne (fun k => max (br s k) 0)
    refine ⟨k, ?_⟩
    have h1 : 0 < max (br s k) 0 := by
      rw [← hk]; exact hs
    rcases lt_max_iff.1 h1 with h | h
    · exact h
    · exact absurd h (lt_irrefl _)
  have hbr_data : ∀ s k, 0 < br s k → |k| < X1 ∧ (∀ i, |s i| < X1) ∧ ∀ l, err s k l < r := by
    intro s k h
    simp only [hbr] at h
    have h1 : 0 ≤ E s k / r := div_nonneg (hEnn s k) hrpos.le
    have h2 : 0 ≤ |(k : ℝ)| / X1r := div_nonneg (abs_nonneg _) hX1rpos.le
    have h3 : 0 ≤ (tn s : ℝ) / X1r := div_nonneg (Nat.cast_nonneg _) hX1rpos.le
    refine ⟨?_, fun i => ?_, fun l => ?_⟩
    · have h4 : |(k : ℝ)| / X1r < 1 := by linarith
      rw [div_lt_one hX1rpos, hX1r, ← Int.cast_abs] at h4
      exact_mod_cast h4
    · have h4 : (tn s : ℝ) / X1r < 1 := by linarith
      rw [div_lt_one hX1rpos] at h4
      have h5 : (((s i).natAbs : ℕ) : ℝ) < X1r := lt_of_le_of_lt (by exact_mod_cast htnle s i) h4
      rw [Nat.cast_natAbs, hX1r] at h5
      exact_mod_cast h5
    · have h4 : E s k / r < 1 := by linarith
      rw [div_lt_one hrpos] at h4
      exact lt_of_le_of_lt (hErr_le_E s k l) h4
  set S : Finset (Fin m → ℤ) := box m (X1 - 1) with hS
  have hφsupp : ∀ s, s ∉ S → φ s = 0 := by
    intro s hs
    refine le_antisymm (not_lt.1 fun h => hs ?_) (hφnn s)
    obtain ⟨k, hk⟩ := hφpos s h
    have := (hbr_data s k hk).2.1
    rw [hS, mem_box]
    intro i
    have := this i
    omega
  set N : ℝ := (24 * (X : ℝ)) ^ m with hN
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hNpos : 0 < N := by rw [hN]; positivity
  have hSN : (S.card : ℝ) ≤ N := by
    have h1 : (S.card : ℤ) = (2 * (X1 - 1) + 1) ^ m := card_box m (X1 - 1) (by omega)
    have h2 : (S.card : ℤ) ≤ (24 * (X : ℤ)) ^ m := by
      rw [h1]
      exact pow_le_pow_left₀ (by omega) (by omega) m
    rw [hN]
    exact_mod_cast h2
  -- the shift estimate
  set u : Fin (m + 1) → (Fin m → ℤ) := fun j =>
    Fin.cases (fun _ => (1 : ℤ)) (fun i => Pi.single i (1 : ℤ)) j with hu
  set dk : Fin (m + 1) → ℤ := fun j => Fin.cases (1 : ℤ) (fun _ => (0 : ℤ)) j with hdk
  set lam : Fin (m + 1) → ℤ → ℝ := fun j z => Pn (Q j) z / r + 2 * |(z : ℝ)| / X1r with hlam
  have hu0 : ∀ i, u 0 i = 1 := fun i => rfl
  have hus : ∀ (a i : Fin m), u a.succ i = if i = a then 1 else 0 := fun a i => by
    simp [hu, Pi.single_apply]
  have hdk0 : dk 0 = 1 := rfl
  have hdks : ∀ a : Fin m, dk a.succ = 0 := fun a => by simp [hdk]
  have herr_shift : ∀ j (z : ℤ) s k l, err (s + z • u j) (k + z * dk j) l ≤ err s k l + Pn (Q j) z := by
    intro j z s k l
    have hPz : ∀ j : Fin (m + 1), 0 ≤ Pn (Q j) z := fun j => Pn_nonneg _ _
    refine Fin.cases ?_ (fun a => ?_) j
    · refine Fin.cases ?_ (fun i => ?_) l
      · rw [herr0, herr0, hdk0, mul_one]
        exact Pn_add_le _ _ _
      · rw [herrs, herrs, hdk0, mul_one]
        have h1 : k + z - (s + z • u 0) i = k - s i := by
          simp [hu0]
        rw [h1]
        linarith [hPz 0]
    · refine Fin.cases ?_ (fun i => ?_) l
      · rw [herr0, herr0, hdks, mul_zero, add_zero]
        linarith [hPz a.succ]
      · rw [herrs, herrs, hdks, mul_zero, add_zero]
        by_cases hia : i = a
        · have h1 : k - (s + z • u a.succ) i = (k - s i) - z := by
            simp [hus, hia]; ring
          rw [h1, hia]
          exact Pn_sub_le _ _ _
        · have h1 : k - (s + z • u a.succ) i = k - s i := by
            simp [hus, hia]
          rw [h1]
          linarith [hPz a.succ]
  have hu_abs : ∀ j i, |u j i| ≤ 1 := by
    intro j i
    refine Fin.cases ?_ (fun a => ?_) j
    · rw [hu0]; norm_num
    · rw [hus]; split_ifs <;> norm_num
  have hdk_abs : ∀ j, |dk j| ≤ 1 := by
    intro j
    refine Fin.cases ?_ (fun a => ?_) j
    · rw [hdk0]; norm_num
    · rw [hdks]; norm_num
  have htn_shift : ∀ j (z : ℤ) s, (tn (s + z • u j) : ℝ) ≤ tn s + |(z : ℝ)| := by
    intro j z s
    have h1 : tn (s + z • u j) ≤ tn s + z.natAbs := by
      refine Finset.sup_le fun i _ => ?_
      rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine le_trans (Int.natAbs_add_le _ _) (add_le_add (htnle s i) ?_)
      rw [Int.natAbs_mul]
      have h2 : (u j i).natAbs ≤ 1 := by
        have := hu_abs j i
        rw [Int.abs_eq_natAbs] at this
        omega
      simpa using Nat.mul_le_mul_left z.natAbs h2
    have h3 : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← h3]
    exact_mod_cast h1
  have hbr_shift : ∀ j (z : ℤ) s k, br s k - lam j z ≤ br (s + z • u j) (k + z * dk j) := by
    intro j z s k
    have h1 : E (s + z • u j) (k + z * dk j) ≤ E s k + Pn (Q j) z :=
      sup'_le _ _ fun l _ => le_trans (herr_shift j z s k l)
        (add_le_add (hErr_le_E s k l) le_rfl)
    have h2 : |((k + z * dk j : ℤ) : ℝ)| ≤ |(k : ℝ)| + |(z : ℝ)| := by
      push_cast
      refine le_trans (abs_add_le _ _) (add_le_add le_rfl ?_)
      rw [abs_mul]
      have h3 : |((dk j : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]; exact_mod_cast hdk_abs j
      simpa using mul_le_mul_of_nonneg_left h3 (abs_nonneg (z : ℝ))
    have h4 := htn_shift j z s
    have h5 := div_le_div_of_nonneg_right h1 hrpos.le
    have h6 := div_le_div_of_nonneg_right h2 hX1rpos.le
    have h7 := div_le_div_of_nonneg_right h4 hX1rpos.le
    rw [add_div] at h5 h6 h7
    have h8 : 2 * |(z : ℝ)| / X1r = |(z : ℝ)| / X1r + |(z : ℝ)| / X1r := by ring
    simp only [hbr, hlam]
    linarith
  have hlam_nn : ∀ j (z : ℤ), 0 ≤ lam j z := by
    intro j z
    simp only [hlam]
    exact add_nonneg (div_nonneg (Pn_nonneg _ _) hrpos.le)
      (div_nonneg (mul_nonneg two_pos.le (abs_nonneg _)) hX1rpos.le)
  have hlam_neg : ∀ j (z : ℤ), lam j (-z) = lam j z := by
    intro j z
    simp only [hlam, Pn_neg, Int.cast_neg, abs_neg]
  have hφ_shift1 : ∀ j (z : ℤ) s, φ s - lam j z ≤ φ (s + z • u j) := by
    intro j z s
    by_cases h : 0 < φ s
    · obtain ⟨k, _, hk⟩ := exists_mem_eq_sup' hne (fun k => max (br s k) 0)
      have hk' : φ s = max (br s k) 0 := hk
      have h1 : φ s = br s k := by
        rw [hk'] at h ⊢
        rcases le_or_gt (br s k) 0 with h2 | h2
        · rw [max_eq_right h2] at h
          exact absurd h (lt_irrefl _)
        · exact max_eq_left h2.le
      rw [h1]
      exact le_trans (hbr_shift j z s k) (hbrφ _ _)
    · have := hφnn (s + z • u j)
      have := hlam_nn j z
      linarith [not_lt.1 h]
  have hφ_shift : ∀ j (z : ℤ) s, |φ (s + z • u j) - φ s| ≤ lam j z := by
    intro j z s
    have h1 := hφ_shift1 j z s
    have h2 := hφ_shift1 j (-z) (s + z • u j)
    have h3 : s + z • u j + (-z) • u j = s := by
      rw [neg_smul, add_neg_cancel_right]
    rw [h3, hlam_neg] at h2
    rw [abs_le]
    constructor <;> linarith
  -- the input gives mass
  set α := alphaM m c with hα
  have hαpos : 0 < α := by rw [hα]; unfold alphaM; positivity
  set Φ : ℝ := ∑ s ∈ S, φ s with hΦ
  have hmass : α * N ≤ Φ := by
    obtain ⟨W, hWc, hW⟩ := hI
    have hWφ : ∀ w ∈ W, 1 / 2 ≤ φ w := by
      intro w hw
      obtain ⟨hwb, k, hk, hP0, hPi⟩ := hW w hw
      refine le_trans ?_ (hbrφ w k)
      have h1 : E w k ≤ r0 := by
        refine sup'_le _ _ fun l _ => ?_
        refine Fin.cases ?_ (fun i => ?_) l
        · rw [herr0]; exact hP0.le
        · rw [herrs]; exact (hPi i).le
      have h2 : E w k / r ≤ 1 / 4 := by
        rw [div_le_iff₀ hrpos, hr]; linarith
      have h3 : |(k : ℝ)| / X1r ≤ 1 / 12 := by
        rw [div_le_iff₀ hX1rpos, hX1r, hX1]
        have : |(k : ℝ)| ≤ (X : ℝ) := by
          rw [← Int.cast_abs]; exact_mod_cast hk
        push_cast
        linarith
      have h4 : tn w ≤ 2 * X := by
        refine Finset.sup_le fun i _ => ?_
        have := hwb i
        rw [Int.abs_eq_natAbs] at this
        omega
      have h5 : (tn w : ℝ) / X1r ≤ 2 / 12 := by
        rw [div_le_iff₀ hX1rpos, hX1r, hX1]
        have : (tn w : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast h4
        push_cast
        linarith
      simp only [hbr]
      linarith
    have hWS : W ⊆ S := by
      intro w hw
      by_contra h
      have := hWφ w hw
      rw [hφsupp w h] at this
      norm_num at this
    have h1 : (W.card : ℝ) * (1 / 2) ≤ ∑ s ∈ W, φ s := by
      have := card_nsmul_le_sum W φ (1 / 2) hWφ
      rwa [nsmul_eq_mul] at this
    have h2 : ∑ s ∈ W, φ s ≤ Φ := sum_le_sum_of_subset_of_nonneg hWS fun s _ _ => hφnn s
    have h3 : α * N = c * (X : ℝ) ^ m * (1 / 2) := by
      rw [hα, hN]
      unfold alphaM
      rw [mul_pow]
      have : (24 : ℝ) ^ m ≠ 0 := by positivity
      field_simp
    rw [h3]
    have := mul_le_mul_of_nonneg_right hWc (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have hΦN : Φ ≤ N := by
    refine le_trans (sum_le_sum fun s _ => hφ1 s) ?_
    rw [sum_const, nsmul_eq_mul, mul_one]
    exact hSN
  have hα1 : α ≤ 1 := by
    have h1 : α * N ≤ 1 * N := by
      rw [one_mul]; exact le_trans hmass hΦN
    exact le_of_mul_le_mul_right h1 hNpos
  set θ := thetaM m c with hθ
  have hsq : 0 < Real.sqrt (2 ^ (m + 4)) := Real.sqrt_pos.2 (by positivity)
  have hsq1 : 1 ≤ Real.sqrt (2 ^ (m + 4)) := by
    rw [Real.one_le_sqrt]
    exact one_le_pow₀ one_le_two
  have hθpos : 0 < θ := by
    rw [hθ]; unfold thetaM; rw [← hα]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ]; unfold thetaM; rw [← hα, div_le_one hsq]
    exact le_trans (pow_le_one₀ hαpos.le hα1) hsq1
  have hθ2 : θ ^ 2 = α ^ 4 / 2 ^ (m + 4) := by
    rw [hθ]; unfold thetaM; rw [← hα, div_pow, Real.sq_sqrt (by positivity)]
    ring
  set C := CM m r0 c with hC
  have hCeq : C = 1 / (θ * r) := rfl
  have hCpos : 0 < C := by rw [hCeq]; exact div_pos one_pos (mul_pos hθpos hrpos)
  have hCge : 1 ≤ C := by
    rw [hCeq, le_div_iff₀ (mul_pos hθpos hrpos), one_mul]
    have := mul_le_mul hθ1 (le_trans hr2 (by norm_num : (1 : ℝ) / 2 ≤ 1)) hrpos.le zero_le_one
    linarith
  -- the modulus of the finite group
  set M : ℕ := 8 * (12 * X) + 2 * (∑ i, (t i).natAbs) + 1 with hM
  have hMpos : 0 < M := by omega
  have hMint : (M : ℤ) = 8 * X1 + 2 * ((∑ i, (t i).natAbs : ℕ) : ℤ) + 1 := by
    rw [hM, hX1]; push_cast; ring
  have hsmall_dvd : ∀ a : ℤ, (M : ℤ) ∣ a → |a| < (M : ℤ) → a = 0 := fun a h1 h2 =>
    Int.eq_zero_of_abs_lt_dvd h1 h2
  set hat : (Fin m → Fin M) → ℂ := fun ξ => ∑ s ∈ S, (φ s : ℂ) * chi M ξ (-s) with hhat
  -- large frequencies
  have hlarge : ∀ ξ : Fin m → Fin M, θ * N ≤ ‖hat ξ‖ → ∀ j (z : ℤ),
      nd ((z : ℝ) * (((∑ i, ((ξ i : ℕ) : ℤ) * u j i : ℤ) : ℝ) / M)) ≤ lam j z / θ := by
    intro ξ hξ j z
    set v : Fin m → ℤ := z • u j with hv
    set S' : Finset (Fin m → ℤ) := S.image (fun s => s - v) with hS'
    have h1 : ∑ s ∈ S', (φ (s + v) : ℂ) * chi M ξ (-s) = chi M ξ v * hat ξ := by
      rw [hS', sum_image (fun a _ b _ h => sub_left_injective h)]
      simp only [hhat]
      rw [mul_sum]
      refine sum_congr rfl fun s _ => ?_
      rw [sub_add_cancel, neg_sub, sub_eq_add_neg, chi_add]
      ring
    have h2 : (chi M ξ v - 1) * hat ξ
        = ∑ s ∈ S ∪ S', ((φ (s + v) : ℂ) - φ s) * chi M ξ (-s) := by
      have h3 : ∑ s ∈ S ∪ S', (φ (s + v) : ℂ) * chi M ξ (-s)
          = ∑ s ∈ S', (φ (s + v) : ℂ) * chi M ξ (-s) := by
        refine (sum_subset subset_union_right fun s _ hs => ?_).symm
        have h4 : s + v ∉ S := by
          intro h5
          exact hs (mem_image.2 ⟨s + v, h5, add_sub_cancel_right s v⟩)
        rw [hφsupp _ h4]; simp
      have h6 : ∑ s ∈ S ∪ S', (φ s : ℂ) * chi M ξ (-s) = hat ξ := by
        simp only [hhat]
        refine (sum_subset subset_union_left fun s _ hs => ?_).symm
        rw [hφsupp _ hs]; simp
      simp_rw [sub_mul]
      rw [sum_sub_distrib, h3, h6, h1, one_mul]
    have h7 : ‖(chi M ξ v - 1) * hat ξ‖ ≤ 2 * N * lam j z := by
      rw [h2]
      refine le_trans (norm_sum_le _ _) ?_
      have h8 : ∀ s ∈ S ∪ S', ‖((φ (s + v) : ℂ) - φ s) * chi M ξ (-s)‖ ≤ lam j z := by
        intro s _
        rw [norm_mul, chi_norm, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact hφ_shift j z s
      refine le_trans (sum_le_sum h8) ?_
      rw [sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (hlam_nn j z)
      have h9 : (S ∪ S').card ≤ S.card + S.card :=
        le_trans (card_union_le _ _) (Nat.add_le_add le_rfl card_image_le)
      have h10 : ((S ∪ S').card : ℝ) ≤ (S.card : ℝ) + S.card := by exact_mod_cast h9
      linarith
    have h11 : ‖chi M ξ v - 1‖ * (θ * N) ≤ 2 * N * lam j z := by
      refine le_trans (mul_le_mul_of_nonneg_left hξ (norm_nonneg _)) ?_
      rw [← norm_mul]
      exact h7
    have h12 : chi M ξ v = Complex.exp (Complex.I *
        ((2 * Real.pi * ((z : ℝ) * (((∑ i, ((ξ i : ℕ) : ℤ) * u j i : ℤ) : ℝ) / M)) : ℝ) : ℂ)) := by
      unfold chi
      have h13 : (∑ i, ((ξ i : ℕ) : ℤ) * v i) = z * ∑ i, ((ξ i : ℕ) : ℤ) * u j i := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [hv, Pi.smul_apply, smul_eq_mul]; ring
      rw [h13, om_eq_exp]
      congr 3
      rw [Int.cast_mul, mul_div_assoc]
    have h14 := four_norm_exp ((z : ℝ) * (((∑ i, ((ξ i : ℕ) : ℤ) * u j i : ℤ) : ℝ) / M))
    rw [← h12] at h14
    rw [le_div_iff₀ hθpos]
    set w := nd ((z : ℝ) * (((∑ i, ((ξ i : ℕ) : ℤ) * u j i : ℤ) : ℝ) / M)) with hw
    have h15 : 4 * w * (θ * N) ≤ 2 * N * lam j z :=
      le_trans (mul_le_mul_of_nonneg_right h14 (mul_pos hθpos hNpos).le) h11
    have h16 : (4 * (w * θ)) * N ≤ (2 * lam j z) * N := by
      calc (4 * (w * θ)) * N = 4 * w * (θ * N) := by ring
        _ ≤ 2 * N * lam j z := h15
        _ = (2 * lam j z) * N := by ring
    have h17 := le_of_mul_le_mul_right h16 hNpos
    have := hlam_nn j z
    linarith
  have hchar : ∀ ξ : Fin m → Fin M, θ * N ≤ ‖hat ξ‖ →
      nd (((∑ i, ((ξ i : ℕ) : ℤ) * t i : ℤ) : ℝ) / M) ≤ 1 / 8 := by
    intro ξ hξ
    set x : Fin (m + 1) → ℝ := fun j => ((∑ i, ((ξ i : ℕ) : ℤ) * u j i : ℤ) : ℝ) / M with hx
    have hxs : ∀ a : Fin m, x a.succ = ((ξ a : ℕ) : ℝ) / M := by
      intro a
      simp only [hx, hus]
      rw [sum_eq_single a]
      · simp
      · intro b _ hb
        rw [if_neg hb, mul_zero]
      · intro h; exact absurd (mem_univ a) h
    have hx0 : x 0 = ∑ a : Fin m, x a.succ := by
      rw [sum_congr rfl fun a _ => hxs a]
      simp only [hx, hu0, mul_one]
      push_cast
      rw [sum_div]
    set H := HM m r0 c nstar with hH
    have hHR : (16 : ℝ) ≤ 2 * C * (8 + 2 * nstar) := by
      have h1 : (0 : ℝ) ≤ nstar := Nat.cast_nonneg _
      have := mul_le_mul hCge (by linarith : (8 : ℝ) ≤ 8 + 2 * nstar) (by norm_num) hCpos.le
      linarith
    have hH1 : 1 ≤ H := by
      refine Nat.le_floor ?_
      rw [← hC]
      push_cast
      linarith
    have hchain : ∀ j, ∃ (a0 : ℤ) (h : ℕ → ℤ), (∑ n ∈ range (J j), (h n).natAbs ≤ H) ∧
        |x j - a0 - ∑ n ∈ range (J j), (h n : ℝ) / Q j (n + 1)| ≤ 2 * C / Q j (J j + 1) := by
      intro j
      have hJr : (Q j (J j + 1) : ℝ) ≤ X1r := by
        rw [hX1r, hX1]; exact_mod_cast hJ j
      obtain ⟨a0, h, h1, h2⟩ := one_chain (hQ j) (x := x j) hrpos hr2 hθpos hθ1 hCeq (J j) hJr
        (fun z => hlarge ξ hξ j z) nstar (hn j)
      refine ⟨a0, h, ?_, h2⟩
      refine Nat.le_floor ?_
      rw [← hC]
      refine le_trans (le_of_eq ?_) h1
      rw [Nat.cast_sum]
      exact sum_congr rfl fun n _ => by rw [Nat.cast_natAbs, Int.cast_abs]
    choose a0 h hsum herrx using hchain
    set β : Fin (m + 1) → ℝ := fun j => ∑ n ∈ range (J j), (h j n : ℝ) / Q j (n + 1) with hβ
    set e : Fin (m + 1) → ℝ := fun j => x j - a0 j - β j with he
    set σ : Fin (m + 1) → ℤ := fun j => Fin.cases (1 : ℤ) (fun _ => (-1 : ℤ)) j with hσ
    have hσ0 : σ 0 = 1 := rfl
    have hσs : ∀ a : Fin m, σ a.succ = -1 := fun a => by simp [hσ]
    have hσ1 : ∀ j, σ j = 1 ∨ σ j = -1 := by
      intro j
      refine Fin.cases ?_ (fun a => ?_) j
      · exact Or.inl hσ0
      · exact Or.inr (hσs a)
    have hσx : ∑ j, (σ j : ℝ) * x j = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [hσ0, hσs, Int.cast_one, one_mul, Int.cast_neg, neg_one_mul, sum_neg_distrib]
      rw [hx0]; ring
    have hesum : ∑ j, |e j| ≤ ∑ j, 2 * C / Q j (J j + 1) :=
      sum_le_sum fun j _ => herrx j
    set TT := (TM m r0 c nstar τ ((m + 1) * H) : ℝ) with hTT
    have hbig' : ∑ j, 2 * C / Q j (J j + 1) < 1 / (2 * TT ^ (m + 1)) := hbig
    have hsmall : nd (∑ j, (σ j : ℝ) * β j) < 1 / (2 * TT ^ (m + 1)) := by
      have h1 : ∑ j, (σ j : ℝ) * β j
          = (-(∑ j, (σ j : ℝ) * e j)) + ((-(∑ j, σ j * a0 j) : ℤ) : ℝ) := by
        have h2 : ∑ j, (σ j : ℝ) * β j
            = ∑ j, (σ j : ℝ) * x j - ∑ j, (σ j : ℝ) * a0 j - ∑ j, (σ j : ℝ) * e j := by
          rw [← sum_sub_distrib, ← sum_sub_distrib]
          refine sum_congr rfl fun j _ => ?_
          simp only [he]; ring
        rw [h2, hσx]
        push_cast; ring
      rw [h1, nd_add_int, nd_neg]
      refine lt_of_le_of_lt (le_trans (nd_le_abs _) ?_) (lt_of_le_of_lt hesum hbig')
      refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun j _ => le_of_eq ?_)
      have h3 : |(σ j : ℝ)| = 1 := by
        rcases hσ1 j with h | h <;> simp [h]
      rw [abs_mul, h3, one_mul]
    set T0 : ℕ := 16 * (m + 1) * τ with hT0
    have hT01 : 1 ≤ T0 := by
      have : 0 < 16 * (m + 1) * τ := Nat.mul_pos (by omega) hτ
      omega
    have hgap := gap Q hQ hco H hH1 J h hsum T0 hT01 σ hσ1 hsmall
    obtain ⟨hmono, hpos⟩ := Tseq_mono (s := m + 1) (H := H) (by omega) hH1 hT01
    set B : ℝ := 1 / (32 * ((m : ℝ) + 1) * τ) with hB
    have hτr : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
    have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hT0r : (T0 : ℝ) = 16 * ((m : ℝ) + 1) * τ := by rw [hT0]; push_cast; ring
    have hT0pos : (0 : ℝ) < T0 := by exact_mod_cast hT01
    have hT0pow : (T0 : ℝ) ≤ (T0 : ℝ) ^ (m + 1) :=
      le_self_pow₀ (by exact_mod_cast hT01) (by omega)
    have hβB : ∀ j, nd (β j) ≤ B := by
      intro j
      refine le_trans (hgap j) ?_
      have h1 : Tseq (m + 1) H T0 1 = 2 * (m + 1) * H * T0 ^ (m + 1) := rfl
      rw [h1]
      have hHr : (0 : ℝ) < H := by exact_mod_cast hH1
      push_cast
      have h2 : (H : ℝ) / (2 * ((m : ℝ) + 1) * H * (T0 : ℝ) ^ (m + 1))
          = 1 / (2 * ((m : ℝ) + 1) * (T0 : ℝ) ^ (m + 1)) := by
        have := hHr.ne'
        field_simp
      rw [h2, hB]
      refine one_div_le_one_div_of_le (by positivity) ?_
      have h3 : (16 : ℝ) * τ ≤ (T0 : ℝ) ^ (m + 1) := by
        refine le_trans ?_ hT0pow
        rw [hT0r]
        have := mul_nonneg hmr (le_trans zero_le_one hτr)
        nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * ((m : ℝ) + 1))
      have h5 : (0 : ℝ) ≤ ((m : ℝ) + 1) * τ := by positivity
      nlinarith
    have heB : ∀ j, |e j| ≤ B := by
      intro j
      have h1 : |e j| ≤ ∑ j, |e j| := single_le_sum (f := fun j => |e j|)
        (fun _ _ => abs_nonneg _) (mem_univ j)
      refine le_trans h1 (le_trans hesum (le_trans hbig'.le ?_))
      rw [hB]
      refine one_div_le_one_div_of_le (by positivity) ?_
      have h2 : T0 ≤ Tseq (m + 1) H T0 ((m + 1) * H) := hmono (Nat.zero_le _)
      have h3 : (T0 : ℝ) ≤ TT := by
        rw [hTT]; exact_mod_cast h2
      have h4 : (T0 : ℝ) ≤ TT ^ (m + 1) := le_trans hT0pow (pow_le_pow_left₀ hT0pos.le h3 _)
      rw [hT0r] at h4
      linarith
    have hxB : ∀ j, nd (x j) ≤ 2 * B := by
      intro j
      have h1 : x j = β j + e j + (a0 j : ℝ) := by simp only [he]; ring
      rw [h1, nd_add_int, two_mul]
      exact le_trans (nd_add_le _ _) (add_le_add (hβB j) (le_trans (nd_le_abs _) (heB j)))
    have h1 : (((∑ i, ((ξ i : ℕ) : ℤ) * t i : ℤ) : ℝ) / M) = ∑ i, (t i : ℝ) * x i.succ := by
      push_cast
      rw [sum_div]
      refine sum_congr rfl fun i _ => ?_
      rw [hxs]
      push_cast; ring
    rw [h1]
    refine le_trans (nd_sum_le _ _) ?_
    have h2 : ∀ i : Fin m, nd ((t i : ℝ) * x i.succ) ≤ (τ : ℝ) * (2 * B) := by
      intro i
      refine le_trans (nd_int_mul_le _ _) ?_
      have h3 : |((t i : ℤ) : ℝ)| ≤ (τ : ℝ) := by
        rw [← Int.cast_abs]; exact_mod_cast ht i
      exact mul_le_mul h3 (hxB _) (nd_nonneg _) (Nat.cast_nonneg _)
    refine le_trans (sum_le_sum fun i _ => h2 i) ?_
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hB]
    have h4 : (m : ℝ) * ((τ : ℝ) * (2 * (1 / (32 * ((m : ℝ) + 1) * τ)))) = (m : ℝ) / (16 * ((m : ℝ) + 1)) := by
      have : (τ : ℝ) ≠ 0 := by
        have : (0 : ℝ) < τ := lt_of_lt_of_le one_pos hτr
        exact this.ne'
      have : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [h4, div_le_iff₀ (by positivity)]
    linarith
  -- the fourth moment
  have hpar2 : ∑ ξ : Fin m → Fin M, ‖hat ξ‖ ^ 2 = (M : ℝ) ^ m * ∑ s ∈ S, φ s ^ 2 := by
    refine parseval hMpos S φ fun a ha b hb h => ?_
    funext i
    have h1 := mem_box.1 ha i
    have h2 := mem_box.1 hb i
    have h3 : b i - a i = 0 := by
      refine hsmall_dvd _ (h i) ?_
      rw [hMint]
      have h4 := abs_sub (b i) (a i)
      have h5 : (0 : ℤ) ≤ ((∑ i, (t i).natAbs : ℕ) : ℤ) := Nat.cast_nonneg _
      omega
    omega
  set Y : Finset (Fin m → ℤ) := box m (2 * (X1 - 1)) with hY
  set f2 : (Fin m → ℤ) → ℝ := fun y =>
    ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 = y), φ p.1 * φ p.2 with hf2
  have hmaps : ∀ p ∈ S ×ˢ S, p.1 + p.2 ∈ Y := by
    intro p hp
    rw [mem_product] at hp
    rw [hY, mem_box]
    intro i
    have h1 := mem_box.1 hp.1 i
    have h2 := mem_box.1 hp.2 i
    rw [Pi.add_apply]
    refine le_trans (abs_add_le _ _) ?_
    omega
  have hsq_hat : ∀ ξ : Fin m → Fin M, hat ξ ^ 2 = ∑ y ∈ Y, (f2 y : ℂ) * chi M ξ (-y) := by
    intro ξ
    have h1 : hat ξ ^ 2 = ∑ p ∈ S ×ˢ S, ((φ p.1 * φ p.2 : ℝ) : ℂ) * chi M ξ (-(p.1 + p.2)) := by
      simp only [hhat]
      rw [sq, sum_mul_sum, sum_product]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [neg_add, chi_add]
      push_cast; ring
    rw [h1, ← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl fun y _ => ?_
    simp only [hf2]
    rw [Complex.ofReal_sum, sum_mul]
    refine sum_congr rfl fun p hp => ?_
    rw [(mem_filter.1 hp).2]
  have hpar4 : ∑ ξ : Fin m → Fin M, ‖hat ξ‖ ^ 4 = (M : ℝ) ^ m * ∑ y ∈ Y, f2 y ^ 2 := by
    have h1 : ∀ ξ : Fin m → Fin M, ‖hat ξ‖ ^ 4 = ‖∑ y ∈ Y, (f2 y : ℂ) * chi M ξ (-y)‖ ^ 2 := by
      intro ξ
      rw [← hsq_hat, norm_pow, ← pow_mul]
    simp_rw [h1]
    refine parseval hMpos Y f2 fun a ha b hb h => ?_
    funext i
    have h1 := mem_box.1 ha i
    have h2 := mem_box.1 hb i
    have h3 : b i - a i = 0 := by
      refine hsmall_dvd _ (h i) ?_
      rw [hMint]
      have h4 := abs_sub (b i) (a i)
      have h5 : (0 : ℤ) ≤ ((∑ i, (t i).natAbs : ℕ) : ℤ) := Nat.cast_nonneg _
      omega
    omega
  have hf2sum : ∑ y ∈ Y, f2 y = Φ ^ 2 := by
    simp only [hf2]
    rw [sum_fiberwise_of_maps_to hmaps (fun p => φ p.1 * φ p.2), hΦ, sq, sum_mul_sum, sum_product]
  have hYcard : (Y.card : ℝ) ≤ 2 ^ m * N := by
    have h1 : (Y.card : ℤ) = (2 * (2 * (X1 - 1)) + 1) ^ m := card_box m _ (by omega)
    have h2 : (Y.card : ℤ) ≤ (2 * (24 * (X : ℤ))) ^ m := by
      rw [h1]
      exact pow_le_pow_left₀ (by omega) (by omega) m
    rw [hN, ← mul_pow]
    exact_mod_cast h2
  set L0 : ℝ := (M : ℝ) ^ m * (α ^ 4 * N ^ 3 / 2 ^ m) with hL0
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hL0pos : 0 < L0 := by rw [hL0]; positivity
  have hlower : L0 ≤ ∑ ξ : Fin m → Fin M, ‖hat ξ‖ ^ 4 := by
    rw [hpar4, hL0]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hMr.le _)
    have h1 := sq_sum_le_card_mul_sum_sq (s := Y) (f := f2)
    rw [hf2sum] at h1
    have h2 : ∑ y ∈ Y, f2 y ^ 2 ≥ 0 := sum_nonneg fun _ _ => sq_nonneg _
    have h3 : (α * N) ^ 4 ≤ (Φ ^ 2) ^ 2 := by
      rw [← pow_mul]
      exact pow_le_pow_left₀ (mul_pos hαpos hNpos).le hmass 4
    have h4 : (α * N) ^ 4 ≤ (2 ^ m * N) * ∑ y ∈ Y, f2 y ^ 2 :=
      le_trans h3 (le_trans h1 (mul_le_mul_of_nonneg_right hYcard h2))
    rw [div_le_iff₀ (by positivity)]
    have h5 : (α ^ 4 * N ^ 3) * N ≤ ((∑ y ∈ Y, f2 y ^ 2) * 2 ^ m) * N := by
      calc (α ^ 4 * N ^ 3) * N = (α * N) ^ 4 := by ring
        _ ≤ (2 ^ m * N) * ∑ y ∈ Y, f2 y ^ 2 := h4
        _ = ((∑ y ∈ Y, f2 y ^ 2) * 2 ^ m) * N := by ring
    exact le_of_mul_le_mul_right h5 hNpos
  set Lg : Finset (Fin m → Fin M) := univ.filter (fun ξ => θ * N ≤ ‖hat ξ‖) with hLg
  set Sm : Finset (Fin m → Fin M) := univ.filter (fun ξ => ¬ θ * N ≤ ‖hat ξ‖) with hSm
  have hsmallpart : ∑ ξ ∈ Sm, ‖hat ξ‖ ^ 4 ≤ L0 / 16 := by
    have h1 : ∀ ξ ∈ Sm, ‖hat ξ‖ ^ 4 ≤ (θ * N) ^ 2 * ‖hat ξ‖ ^ 2 := by
      intro ξ hξ
      have h2 : ‖hat ξ‖ ≤ θ * N := (not_le.1 (mem_filter.1 hξ).2).le
      have h3 : ‖hat ξ‖ ^ 4 = ‖hat ξ‖ ^ 2 * ‖hat ξ‖ ^ 2 := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h2 2) (sq_nonneg _)
    refine le_trans (sum_le_sum h1) ?_
    rw [← mul_sum]
    have h4 : ∑ ξ ∈ Sm, ‖hat ξ‖ ^ 2 ≤ ∑ ξ : Fin m → Fin M, ‖hat ξ‖ ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
    have h5 : ∑ s ∈ S, φ s ^ 2 ≤ N := by
      have h6 : ∀ s ∈ S, φ s ^ 2 ≤ 1 := fun s _ => pow_le_one₀ (hφnn s) (hφ1 s)
      refine le_trans (sum_le_sum h6) ?_
      rw [sum_const, nsmul_eq_mul, mul_one]
      exact hSN
    have h7 : ∑ ξ ∈ Sm, ‖hat ξ‖ ^ 2 ≤ (M : ℝ) ^ m * N := by
      refine le_trans h4 ?_
      rw [hpar2]
      exact mul_le_mul_of_nonneg_left h5 (pow_nonneg hMr.le _)
    refine le_trans (mul_le_mul_of_nonneg_left h7 (sq_nonneg _)) (le_of_eq ?_)
    rw [hL0, mul_pow, hθ2, pow_add]
    have : (2 : ℝ) ^ m ≠ 0 := by positivity
    field_simp
    ring
  -- a quadruple exists
  have hquad : ∃ a b c' d : Fin m → ℤ, 0 < φ a ∧ 0 < φ b ∧ 0 < φ c' ∧ 0 < φ d ∧
      t = a + b - c' - d := by
    by_contra hno
    set F : ℂ := ∑ ξ : Fin m → Fin M, ((‖hat ξ‖ ^ 4 : ℝ) : ℂ) * chi M ξ t with hF
    have hF0 : F = 0 := by
      have h1 : ∀ ξ : Fin m → Fin M, ((‖hat ξ‖ ^ 4 : ℝ) : ℂ) * chi M ξ t
          = ∑ p ∈ S ×ˢ S, ∑ q ∈ S ×ˢ S,
              ((φ p.1 * φ p.2 * (φ q.1 * φ q.2) : ℝ) : ℂ) * chi M ξ (t + (q.1 + q.2) - (p.1 + p.2)) := by
        intro ξ
        have h2 : hat ξ ^ 2 = ∑ p ∈ S ×ˢ S, ((φ p.1 * φ p.2 : ℝ) : ℂ) * chi M ξ (-(p.1 + p.2)) := by
          simp only [hhat]
          rw [sq, sum_mul_sum, sum_product]
          refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
          rw [neg_add, chi_add]
          push_cast; ring
        have h3 : ((‖hat ξ‖ ^ 4 : ℝ) : ℂ) = hat ξ ^ 2 * (starRingEnd ℂ) (hat ξ ^ 2) := by
          rw [Complex.mul_conj', norm_pow]
          push_cast; ring
        rw [h3, h2, map_sum, sum_mul_sum, sum_mul]
        refine sum_congr rfl fun p _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun q _ => ?_
        rw [map_mul, Complex.conj_ofReal, chi_conj, neg_neg]
        have h4 : t + (q.1 + q.2) - (p.1 + p.2) = -(p.1 + p.2) + (q.1 + q.2) + t := by abel
        rw [h4]
        simp only [chi_add]
        push_cast; ring
      rw [hF]
      simp_rw [h1]
      rw [sum_comm]
      refine sum_eq_zero fun p hp => ?_
      rw [sum_comm]
      refine sum_eq_zero fun q hq => ?_
      rw [← mul_sum, chi_orth hMpos]
      split_ifs with hdvd
      swap
      · rw [mul_zero]
      rw [mem_product] at hp hq
      by_cases hzero : φ p.1 * φ p.2 * (φ q.1 * φ q.2) = 0
      · rw [hzero]; simp
      exfalso
      have hne0 : φ p.1 ≠ 0 ∧ φ p.2 ≠ 0 ∧ φ q.1 ≠ 0 ∧ φ q.2 ≠ 0 := by
        simp only [mul_ne_zero_iff] at hzero
        exact ⟨hzero.1.1, hzero.1.2, hzero.2.1, hzero.2.2⟩
      refine hno ⟨p.1, p.2, q.1, q.2, lt_of_le_of_ne (hφnn _) hne0.1.symm,
        lt_of_le_of_ne (hφnn _) hne0.2.1.symm, lt_of_le_of_ne (hφnn _) hne0.2.2.1.symm,
        lt_of_le_of_ne (hφnn _) hne0.2.2.2.symm, ?_⟩
      funext i
      have h5 := mem_box.1 hp.1 i
      have h6 := mem_box.1 hp.2 i
      have h7 := mem_box.1 hq.1 i
      have h8 := mem_box.1 hq.2 i
      have h9 : (t + (q.1 + q.2) - (p.1 + p.2)) i = 0 := by
        refine hsmall_dvd _ (hdvd i) ?_
        have h10 : ((t i).natAbs : ℤ) ≤ ((∑ i, (t i).natAbs : ℕ) : ℤ) := by
          exact_mod_cast single_le_sum (f := fun i => (t i).natAbs) (fun _ _ => Nat.zero_le _)
            (mem_univ i)
        rw [hMint]
        simp only [Pi.sub_apply, Pi.add_apply]
        rw [abs_lt]
        rw [abs_le] at h5 h6 h7 h8
        omega
      simp only [Pi.sub_apply, Pi.add_apply] at h9 ⊢
      omega
    have hFre : F.re = ∑ ξ : Fin m → Fin M, ‖hat ξ‖ ^ 4 * (chi M ξ t).re := by
      rw [hF, Complex.re_sum]
      exact sum_congr rfl fun ξ _ => Complex.re_ofReal_mul _ _
    have hlg : ∑ ξ ∈ Lg, ‖hat ξ‖ ^ 4 * (7 / 10) ≤ ∑ ξ ∈ Lg, ‖hat ξ‖ ^ 4 * (chi M ξ t).re := by
      refine sum_le_sum fun ξ hξ => mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact re_om_ge M _ (hchar ξ (mem_filter.1 hξ).2)
    have hsm : ∑ ξ ∈ Sm, -(‖hat ξ‖ ^ 4) ≤ ∑ ξ ∈ Sm, ‖hat ξ‖ ^ 4 * (chi M ξ t).re := by
      refine sum_le_sum fun ξ _ => ?_
      have h1 : -1 ≤ (chi M ξ t).re := by
        have h2 := Complex.abs_re_le_norm (chi M ξ t)
        rw [chi_norm] at h2
        exact (abs_le.1 h2).1
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ ‖hat ξ‖ ^ 4)
      linarith
    have hsplitF := sum_filter_add_sum_filter_not (univ : Finset (Fin m → Fin M))
      (fun ξ => θ * N ≤ ‖hat ξ‖) (fun ξ => ‖hat ξ‖ ^ 4 * (chi M ξ t).re)
    have hsplit4 := sum_filter_add_sum_filter_not (univ : Finset (Fin m → Fin M))
      (fun ξ => θ * N ≤ ‖hat ξ‖) (fun ξ => ‖hat ξ‖ ^ 4)
    rw [← hLg, ← hSm] at hsplitF hsplit4
    rw [← sum_mul] at hlg
    rw [sum_neg_distrib] at hsm
    have h0 : F.re = 0 := by rw [hF0]; rfl
    rw [hFre] at h0
    linarith
  obtain ⟨a, b, c', d, ha, hb, hc', hd, habcd⟩ := hquad
  obtain ⟨k1, hk1⟩ := hφpos a ha
  obtain ⟨k2, hk2⟩ := hφpos b hb
  obtain ⟨k3, hk3⟩ := hφpos c' hc'
  obtain ⟨k4, hk4⟩ := hφpos d hd
  obtain ⟨hb1, _, he1⟩ := hbr_data a k1 hk1
  obtain ⟨hb2, _, he2⟩ := hbr_data b k2 hk2
  obtain ⟨hb3, _, he3⟩ := hbr_data c' k3 hk3
  obtain ⟨hb4, _, he4⟩ := hbr_data d k4 hk4
  have h16 : (16 : ℝ) * r0 = r + r + r + r := by rw [hr]; ring
  have hfour : ∀ (j : Fin (m + 1)) (y1 y2 y3 y4 : ℤ), Pn (Q j) y1 < r → Pn (Q j) y2 < r →
      Pn (Q j) y3 < r → Pn (Q j) y4 < r → Pn (Q j) (y1 + y2 - y3 - y4) < 16 * r0 := by
    intro j y1 y2 y3 y4 h1 h2 h3 h4
    have h5 := Pn_sub_le (Q j) (y1 + y2 - y3) y4
    have h6 := Pn_sub_le (Q j) (y1 + y2) y3
    have h7 := Pn_add_le (Q j) y1 y2
    rw [h16]
    linarith
  refine ⟨k1 + k2 - k3 - k4, ?_, ?_, fun i => ?_⟩
  · rw [abs_le]
    rw [abs_lt] at hb1 hb2 hb3 hb4
    omega
  · exact hfour 0 k1 k2 k3 k4 (he1 0) (he2 0) (he3 0) (he4 0)
  · have h1 : k1 + k2 - k3 - k4 - t i = (k1 - a i) + (k2 - b i) - (k3 - c' i) - (k4 - d i) := by
      rw [habcd]
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [h1]
    have g : ∀ s k, (∀ l, err s k l < r) → Pn (Q i.succ) (k - s i) < r := fun s k h => by
      rw [← herrs]; exact h _
    exact hfour i.succ _ _ _ _ (g a k1 he1) (g b k2 he2) (g c' k3 he3) (g d k4 he4)

/-- If the covering input holds at arbitrarily large heights, then every target is reached. -/
theorem all_targets_M11 {m : ℕ} (Q : Fin (m + 1) → ℕ → ℕ) (hQ : ∀ j, IsChain (Q j))
    (hco : ∀ i j, i ≠ j → ∀ a b, Nat.Coprime (Q i a) (Q j b))
    (hratio : ∀ K : ℝ, ∃ n0 : ℕ, ∀ j n, (Q j (n + 1) : ℝ) / Q j n < K → n < n0)
    {r0 c : ℝ} (hr0 : 0 < r0) (hr8 : r0 ≤ 1 / 8) (hc : 0 < c)
    (hI : ∀ X0 : ℕ, ∃ X : ℕ, X0 ≤ X ∧ Input Q r0 c X) (t : Fin m → ℤ) :
    ∃ k : ℤ, Pn (Q 0) k < 16 * r0 ∧ ∀ i : Fin m, Pn (Q i.succ) (k - t i) < 16 * r0 := by
  classical
  obtain ⟨n0, hn0⟩ := hratio (32 * CM m r0 c)
  set τ : ℕ := 1 + ∑ i, (t i).natAbs with hτ
  have ht : ∀ i, |t i| ≤ (τ : ℤ) := by
    intro i
    have h1 : (t i).natAbs ≤ ∑ i, (t i).natAbs :=
      single_le_sum (f := fun i => (t i).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
    rw [Int.abs_eq_natAbs]
    omega
  set B : ℝ := 1 / (2 * (TM m r0 c n0 τ ((m + 1) * HM m r0 c n0) : ℝ) ^ (m + 1)) with hB
  have hTpos : 0 < (TM m r0 c n0 τ ((m + 1) * HM m r0 c n0) : ℝ) := by
    -- the sequence stays positive as soon as `HM ≥ 1`, which follows from a nonempty input
    obtain ⟨X, hX1, hIX⟩ := hI 1
    have hCpos : 0 < CM m r0 c := by
      have h1 : 0 < thetaM m c := by
        unfold thetaM alphaM
        have : 0 < Real.sqrt (2 ^ (m + 4)) := Real.sqrt_pos.2 (by positivity)
        positivity
      unfold CM
      exact div_pos one_pos (mul_pos h1 (by linarith))
    have hC1 : 1 ≤ CM m r0 c := by
      obtain ⟨W, hWc, hW⟩ := hIX
      have hXr : (0 : ℝ) < X := by exact_mod_cast hX1
      have hWb : W ⊆ box m (2 * (X : ℤ)) := fun w hw => mem_box.2 (hW w hw).1
      have h2 : (W.card : ℤ) ≤ (2 * (2 * (X : ℤ)) + 1) ^ m := by
        rw [← card_box m _ (by omega)]
        exact_mod_cast card_le_card hWb
      have h3 : (W.card : ℝ) ≤ (5 * (X : ℝ)) ^ m := by
        have h4 : (W.card : ℤ) ≤ (5 * (X : ℤ)) ^ m :=
          le_trans h2 (pow_le_pow_left₀ (by omega) (by omega) m)
        exact_mod_cast h4
      have hc5 : c ≤ 5 ^ m := by
        have h5 := le_trans hWc h3
        rw [mul_pow] at h5
        exact le_of_mul_le_mul_right h5 (pow_pos hXr m)
      have hα1 : alphaM m c ≤ 1 := by
        unfold alphaM
        rw [div_le_one (by positivity)]
        have h6 : (5 : ℝ) ^ m ≤ 24 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
        have h7 : (0 : ℝ) ≤ 24 ^ m := by positivity
        linarith
      have hα0 : 0 < alphaM m c := by unfold alphaM; positivity
      have hθ1 : thetaM m c ≤ 1 := by
        unfold thetaM
        have h8 : 0 < Real.sqrt (2 ^ (m + 4)) := Real.sqrt_pos.2 (by positivity)
        rw [div_le_one h8]
        refine le_trans (pow_le_one₀ hα0.le hα1) ?_
        rw [Real.one_le_sqrt]
        exact one_le_pow₀ one_le_two
      have hθ0 : 0 < thetaM m c := by
        unfold thetaM
        have : 0 < Real.sqrt (2 ^ (m + 4)) := Real.sqrt_pos.2 (by positivity)
        positivity
      unfold CM
      rw [le_div_iff₀ (mul_pos hθ0 (by linarith)), one_mul]
      have := mul_le_mul hθ1 (by linarith : 4 * r0 ≤ 1) (by linarith) zero_le_one
      linarith
    have hH1 : 1 ≤ HM m r0 c n0 := by
      refine Nat.le_floor ?_
      have h1 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
      have := mul_le_mul hC1 (by linarith : (8 : ℝ) ≤ 8 + 2 * n0) (by norm_num) hCpos.le
      push_cast
      linarith
    have hT01 : 1 ≤ 16 * (m + 1) * τ := by
      have : 0 < 16 * (m + 1) * τ := Nat.mul_pos (by omega) (by omega)
      omega
    obtain ⟨_, hpos⟩ := Tseq_mono (s := m + 1) (H := HM m r0 c n0) (by omega) hH1 hT01
    exact_mod_cast hpos _
  have hBpos : 0 < B := by rw [hB]; positivity
  obtain ⟨J0, hJ0⟩ := pow_unbounded_of_one_lt
    (∑ _j : Fin (m + 1), 2 * |CM m r0 c| / B) (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨X, hX, hIX⟩ := hI (1 + ∑ j, Q j (J0 + 1))
  have hXQ : ∀ j, Q j (J0 + 1) ≤ 12 * X := by
    intro j
    have h1 : Q j (J0 + 1) ≤ ∑ j, Q j (J0 + 1) :=
      single_le_sum (f := fun j => Q j (J0 + 1)) (fun _ _ => Nat.zero_le _) (mem_univ j)
    omega
  have hbig : ∑ j, 2 * CM m r0 c / Q j (J0 + 1) < B := by
    have h1 : ∀ j, 2 * CM m r0 c / Q j (J0 + 1) ≤ 2 * |CM m r0 c| / 2 ^ (J0 + 1) := by
      intro j
      have h2 : (2 : ℝ) ^ (J0 + 1) ≤ Q j (J0 + 1) := by exact_mod_cast (hQ j).two_pow (J0 + 1)
      have h3 : (0 : ℝ) < Q j (J0 + 1) := by exact_mod_cast (hQ j).pos _
      refine le_trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self _) two_pos.le) h3.le) ?_
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2
    refine lt_of_le_of_lt (sum_le_sum fun j _ => h1 j) ?_
    rw [← sum_div] at hJ0 ⊢
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hBpos] at hJ0
    refine lt_of_lt_of_le hJ0 ?_
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (Nat.le_succ _)) hBpos.le
  obtain ⟨k, _, h1, h2⟩ := height_M11 Q hQ hco hr0 hr8 hc (X := X) (by omega) hIX n0
    (fun j S hS => by
      have h3 : S ⊆ range n0 := fun n hn => mem_range.2 (hn0 j n (hS n hn))
      simpa using card_le_card h3)
    τ (by omega) (fun _ => J0) hXQ hbig t ht
  exact ⟨k, h1, h2⟩

/-! ## The prime-square chains -/

lemma square_isChainM11 {p : ℕ} (hp : 2 ≤ p) : IsChain (fun n => p ^ (n ^ 2)) := by
  have hstep : ∀ n, p ^ ((n + 1) ^ 2) = p ^ (n ^ 2) * p ^ (2 * n + 1) := fun n => by
    rw [← pow_add]; congr 1; ring
  refine ⟨by simp, fun n => ?_, fun n => ?_⟩
  · rw [hstep]; exact dvd_mul_right _ _
  · rw [hstep, mul_comm 2]
    refine Nat.mul_le_mul_left _ (le_trans hp ?_)
    exact Nat.le_self_pow (by omega) p

lemma square_coprimeM11 {m : ℕ} (p : Fin (m + 1) → ℕ) (hp : ∀ j, (p j).Prime)
    (hinj : Function.Injective p) :
    ∀ i j, i ≠ j → ∀ a b, Nat.Coprime (p i ^ (a ^ 2)) (p j ^ (b ^ 2)) := fun i j hij _ _ =>
  Nat.coprime_pow_primes _ _ (hp i) (hp j) (fun h => hij (hinj h))

lemma square_ratioM11 {m : ℕ} (p : Fin (m + 1) → ℕ) (hp : ∀ j, 2 ≤ p j) (K : ℝ) :
    ∃ n0 : ℕ, ∀ (j : Fin (m + 1)) (n : ℕ),
      (((p j) ^ ((n + 1) ^ 2) : ℕ) : ℝ) / (((p j) ^ (n ^ 2) : ℕ) : ℝ) < K → n < n0 := by
  refine ⟨⌈K⌉₊, fun j n h => ?_⟩
  have hp0 : (0 : ℝ) < p j := by
    have : 0 < p j := by have := hp j; omega
    exact_mod_cast this
  have h1 : (((p j) ^ ((n + 1) ^ 2) : ℕ) : ℝ) / (((p j) ^ (n ^ 2) : ℕ) : ℝ)
      = (p j : ℝ) ^ (2 * n + 1) := by
    have h2 : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
    have h3 : (p j : ℝ) ^ (n ^ 2) ≠ 0 := pow_ne_zero _ hp0.ne'
    push_cast
    rw [h2, pow_add]
    field_simp
  rw [h1] at h
  have h4 : (n : ℝ) ≤ (p j : ℝ) ^ (2 * n + 1) := by
    have h5 : n ≤ (p j) ^ (2 * n + 1) := by
      have h6 : n < 2 ^ n := Nat.lt_two_pow_self
      have h7 : 2 ^ n ≤ (p j) ^ n := Nat.pow_le_pow_left (hp j) n
      have h8 : (p j) ^ n ≤ (p j) ^ (2 * n + 1) := Nat.pow_le_pow_right (by have := hp j; omega) (by omega)
      omega
    exact_mod_cast h5
  exact Nat.lt_ceil.2 (lt_of_le_of_lt h4 h)

end HeightM11
end LeanCheck
