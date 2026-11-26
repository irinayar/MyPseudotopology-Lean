import Mathlib
import LeanCheck.TwoPrimesFormula
import LeanCheck.TwoPrimesBoxCertificate

/-!
# The exact statements on the weighted sum

* `diag`: for any finite sets, `κ_M ≥ (3M/(2M²+1)) u / (|Y| |Z|)`.
* `average`: averaging the kernel over the units modulo `q^R` leaves at most the share
  `3M/(2M²+1)` of every non-zero frequency.
* `lowcond`: the frequencies of a conductor `Q` prime to the weights of `p` are bounded through one
  digit factor and the sizes of the others.
* `qmass`: the closed formula for `Σ_{b mod q^a} |φ_Y(b/q^a)|²`.
-/

namespace TwoPrimesSum

open Finset Real TwoPrimesFormula TwoPrimesBoxCertificate

/-! ## The diagonal solutions -/

theorem diag (M u v : ℕ) (hM : 1 ≤ M) (hu : 0 < u) (Y Z : Finset ℤ) (hY : Y.Nonempty)
    (hZ : Z.Nonempty) :
    3 * (M : ℝ) / (2 * (M : ℝ) ^ 2 + 1) * (u / ((Y.card : ℝ) * Z.card))
      ≤ kappaD M u v Y Z := by
  have hYc : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hZc : (0 : ℝ) < Z.card := by exact_mod_cast hZ.card_pos
  have hur : (0 : ℝ) < u := by exact_mod_cast hu
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hH0 := H_at_zero_pos M hM
  have hf := fourier u v hu (range M) (fun m => (M : ℝ) - |(m : ℝ)|) Y Z
  have hlow : (M : ℝ) ^ 2 * ((Y.card : ℝ) * Z.card)
      ≤ ∑ k ∈ range M, ∑ k' ∈ range M, ((M : ℝ) - |(((k : ℤ) - k' : ℤ) : ℝ)|) *
          (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
            TwoPrimesFormula.ind u (((k : ℤ) - k') * v + (z - z') - (y - y'))) := by
    have hdiagc : (Y.card : ℝ) * Z.card ≤ ∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
        TwoPrimesFormula.ind u (((0 : ℤ)) * v + (z - z') - (y - y')) := by
      have h1 : ∀ z ∈ Z, (Y.card : ℝ) ≤ ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
          TwoPrimesFormula.ind u (((0 : ℤ)) * v + (z - z') - (y - y')) := by
        intro z hz
        refine le_trans ?_ (single_le_sum (f := fun z' => ∑ y ∈ Y, ∑ y' ∈ Y,
          TwoPrimesFormula.ind u (((0 : ℤ)) * v + (z - z') - (y - y')))
          (fun z' _ => sum_nonneg fun y _ => sum_nonneg fun y' _ => ind_nonneg _ _) hz)
        rw [card_eq_sum_ones, Nat.cast_sum]
        refine sum_le_sum fun y hy => ?_
        refine le_trans ?_ (single_le_sum (f := fun y' =>
          TwoPrimesFormula.ind u (((0 : ℤ)) * v + (z - z) - (y - y')))
          (fun y' _ => ind_nonneg _ _) hy)
        simp [TwoPrimesFormula.ind]
      have h2 := sum_le_sum h1
      rw [sum_const, nsmul_eq_mul, mul_comm] at h2
      exact h2
    have hterm : ∀ k ∈ range M, (M : ℝ) * ((Y.card : ℝ) * Z.card)
        ≤ ∑ k' ∈ range M, ((M : ℝ) - |(((k : ℤ) - k' : ℤ) : ℝ)|) *
          (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
            TwoPrimesFormula.ind u (((k : ℤ) - k') * v + (z - z') - (y - y'))) := by
      intro k hk
      have hnn : ∀ k' ∈ range M, 0 ≤ ((M : ℝ) - |(((k : ℤ) - k' : ℤ) : ℝ)|) *
          (∑ z ∈ Z, ∑ z' ∈ Z, ∑ y ∈ Y, ∑ y' ∈ Y,
            TwoPrimesFormula.ind u (((k : ℤ) - k') * v + (z - z') - (y - y'))) := by
        intro k' hk'
        refine mul_nonneg ?_ (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
          sum_nonneg fun _ _ => ind_nonneg _ _)
        have h1 := mem_range.mp hk
        have h2 := mem_range.mp hk'
        have h3 : |(k : ℤ) - k'| ≤ (M : ℤ) := by rw [abs_le]; omega
        have h4 : |(((k : ℤ) - k' : ℤ) : ℝ)| ≤ (M : ℝ) := by exact_mod_cast h3
        linarith
      refine le_trans ?_ (single_le_sum hnn hk)
      rw [sub_self, Int.cast_zero, abs_zero, sub_zero]
      exact mul_le_mul_of_nonneg_left hdiagc hMr.le
    have h := sum_le_sum hterm
    rw [sum_const, card_range, nsmul_eq_mul] at h
    refine le_trans (le_of_eq ?_) h
    ring
  rw [hf] at hlow
  have hsum : ∑ ξ ∈ range u, power u Y ξ * power u Z ξ *
        (∑ k ∈ range M, ∑ k' ∈ range M, ((M : ℝ) - |(((k : ℤ) - k' : ℤ) : ℝ)|)
          * c ((ξ : ℝ) * v / u) ((k : ℤ) - k'))
      = (Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * (H M 0 * kappaD M u v Y Z) := by
    unfold kappaD
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun ξ _ => ?_
    have e : (∑ k ∈ range M, ∑ k' ∈ range M, ((M : ℝ) - |(((k : ℤ) - k' : ℤ) : ℝ)|)
        * c ((ξ : ℝ) * v / u) ((k : ℤ) - k')) = H M ((ξ : ℝ) * v / u) := rfl
    rw [e]
    unfold G
    have h1 := hYc.ne'
    have h2 := hZc.ne'
    have h3 := hH0.ne'
    field_simp
  rw [hsum] at hlow
  have hK : H M 0 = (M : ℝ) * (2 * (M : ℝ) ^ 2 + 1) / 3 := H_at_zero M
  have hκ : (M : ℝ) ^ 2 * u ≤ (Y.card : ℝ) * Z.card * H M 0 * kappaD M u v Y Z := by
    have hpos : 0 < (Y.card : ℝ) * Z.card := mul_pos hYc hZc
    refine le_of_mul_le_mul_left ?_ hpos
    have h := mul_le_mul_of_nonneg_left hlow hur.le
    have e1 : (u : ℝ) * (1 / (u : ℝ) *
        ((Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * (H M 0 * kappaD M u v Y Z)))
        = (Y.card : ℝ) ^ 2 * (Z.card : ℝ) ^ 2 * (H M 0 * kappaD M u v Y Z) := by
      field_simp
    rw [e1] at h
    refine le_trans (le_of_eq (by ring)) (le_trans h (le_of_eq (by ring)))
  rw [hK] at hκ
  rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
  have h4 : (M : ℝ) * (3 * M * u) ≤ (M : ℝ) * (kappaD M u v Y Z
      * ((2 * (M : ℝ) ^ 2 + 1) * ((Y.card : ℝ) * Z.card))) := by
    refine le_trans (le_of_eq (by ring)) (le_trans (mul_le_mul_of_nonneg_left hκ (by norm_num
      : (0 : ℝ) ≤ 3)) (le_of_eq (by ring)))
  exact le_of_mul_le_mul_left h4 hMr

/-! ## Averaging over the units -/

/-- A sum over a square which depends only on the difference. -/
lemma sum_diag (M : ℕ) (f : ℤ → ℝ) (hf : ∀ m, f (-m) = f m) :
    ∑ k ∈ range M, ∑ l ∈ range M, f ((k : ℤ) - l)
      = (M : ℝ) * f 0 + 2 * ∑ j ∈ range M, ((M - (j + 1) : ℕ) : ℝ) * f (j + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hsplit : ∑ k ∈ range (M + 1), ∑ l ∈ range (M + 1), f ((k : ℤ) - l)
        = (∑ k ∈ range M, ∑ l ∈ range M, f ((k : ℤ) - l))
          + 2 * (∑ j ∈ range M, f (j + 1)) + f 0 := by
      have e1 : ∀ k : ℕ, ∑ l ∈ range (M + 1), f ((k : ℤ) - l)
          = ∑ l ∈ range M, f ((k : ℤ) - l) + f ((k : ℤ) - M) :=
        fun k => sum_range_succ _ _
      rw [sum_range_succ, sum_congr rfl fun k _ => e1 k, sum_add_distrib, e1 M]
      have h1 : ∑ l ∈ range M, f ((M : ℤ) - l) = ∑ j ∈ range M, f (j + 1) := by
        rw [← sum_range_reflect (fun j => f ((j : ℤ) + 1)) M]
        refine sum_congr rfl fun l hl => congrArg f ?_
        have := mem_range.mp hl
        omega
      have h2 : ∑ k ∈ range M, f ((k : ℤ) - M) = ∑ j ∈ range M, f (j + 1) := by
        rw [← h1]
        refine sum_congr rfl fun k _ => ?_
        rw [← hf, neg_sub]
      rw [h1, h2, sub_self]
      ring
    rw [hsplit, ih]
    have h3 : ∑ j ∈ range (M + 1), ((M + 1 - (j + 1) : ℕ) : ℝ) * f (j + 1)
        = (∑ j ∈ range M, ((M - (j + 1) : ℕ) : ℝ) * f (j + 1)) + ∑ j ∈ range M, f (j + 1) := by
      rw [sum_range_succ, show M + 1 - (M + 1) = 0 by omega, Nat.cast_zero, zero_mul, add_zero,
        ← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      have := mem_range.mp hj
      rw [show M + 1 - (j + 1) = (M - (j + 1)) + 1 by omega, Nat.cast_add, Nat.cast_one]
      ring
    rw [h3, Nat.cast_add, Nat.cast_one]
    ring

/-- `S(g) = Σ_{k,l<M, g ∣ k-l} (M - |k-l|)`. -/
noncomputable def S (M g : ℕ) : ℝ :=
  ∑ k ∈ range M, ∑ l ∈ range M,
    if (g : ℤ) ∣ (k : ℤ) - l then (M : ℝ) - |(((k : ℤ) - l : ℤ) : ℝ)| else 0

lemma S_eq (M g : ℕ) : S M g = (M : ℝ) ^ 2
    + 2 * ∑ j ∈ range M, if g ∣ j + 1 then ((M - (j + 1) : ℕ) : ℝ) ^ 2 else 0 := by
  unfold S
  rw [sum_diag M (fun m => if (g : ℤ) ∣ m then (M : ℝ) - |((m : ℤ) : ℝ)| else 0)
    (fun m => by simp only [dvd_neg, Int.cast_neg, abs_neg])]
  rw [if_pos (dvd_zero _), Int.cast_zero, abs_zero, sub_zero, ← sq]
  congr 2
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  have hc : (g : ℤ) ∣ (j : ℤ) + 1 ↔ g ∣ j + 1 := by
    rw [← Int.natCast_dvd_natCast, Nat.cast_add, Nat.cast_one]
  have hv : (M : ℝ) - |((((j : ℤ) + 1 : ℤ)) : ℝ)| = ((M - (j + 1) : ℕ) : ℝ) := by
    rw [Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1), Nat.cast_sub (by omega : j + 1 ≤ M),
      Nat.cast_add, Nat.cast_one]
  by_cases h : g ∣ j + 1
  · rw [if_pos (hc.mpr h), if_pos h, hv, sq]
  · rw [if_neg (fun c => h (hc.mp c)), if_neg h, mul_zero]

/-- Sums over the multiples of `g` written with the multiplier. -/
lemma sum_multiples (M g : ℕ) (hg : 1 ≤ g) (F : ℕ → ℝ) (hF : ∀ n, M ≤ n → F n = 0) :
    ∑ j ∈ range M, (if g ∣ j + 1 then F (j + 1) else 0) = ∑ i ∈ range M, F (g * (i + 1)) := by
  rw [← sum_filter]
  have h1 : ∑ i ∈ range M, F (g * (i + 1))
      = ∑ i ∈ (range M).filter (fun i => g * (i + 1) ≤ M), F (g * (i + 1)) := by
    rw [sum_filter]
    refine sum_congr rfl fun i _ => ?_
    split
    · rfl
    · exact hF _ (by omega)
  rw [h1]
  refine (sum_bij' (fun i _ => g * (i + 1) - 1) (fun j _ => (j + 1) / g - 1) ?_ ?_ ?_ ?_ ?_).symm
  · intro i hi
    rw [mem_filter, mem_range] at hi ⊢
    have h2 : 1 ≤ g * (i + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    refine ⟨by omega, ?_⟩
    rw [show g * (i + 1) - 1 + 1 = g * (i + 1) by omega]
    exact Nat.dvd_mul_right _ _
  · intro j hj
    rw [mem_filter, mem_range] at hj ⊢
    obtain ⟨hj1, k, hk⟩ := hj
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; omega
      · exact h
    have hdiv : (j + 1) / g = k := by rw [hk, Nat.mul_div_cancel_left _ (by omega : 0 < g)]
    have hkM : k ≤ j + 1 := by
      rw [hk]; exact Nat.le_mul_of_pos_left _ (by omega)
    rw [hdiv, show k - 1 + 1 = k by omega, ← hk]
    omega
  · intro i hi
    have h2 : 1 ≤ g * (i + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rw [show g * (i + 1) - 1 + 1 = g * (i + 1) by omega,
      Nat.mul_div_cancel_left _ (by omega : 0 < g)]
    omega
  · intro j hj
    rw [mem_filter] at hj
    obtain ⟨_, k, hk⟩ := hj
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; omega
      · exact h
    have hdiv : (j + 1) / g = k := by rw [hk, Nat.mul_div_cancel_left _ (by omega : 0 < g)]
    rw [hdiv, show k - 1 + 1 = k by omega, ← hk]
    omega
  · intro i hi
    have h2 : 1 ≤ g * (i + 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rw [show g * (i + 1) - 1 + 1 = g * (i + 1) by omega]

lemma S_bound (M q h : ℕ) (hq : 1 ≤ q) (hh : 1 ≤ h) :
    (q : ℝ) * S M (h * q) - S M h ≤ ((q : ℝ) - 1) * (M : ℝ) ^ 2 := by
  set F : ℕ → ℝ := fun n => ((M - n : ℕ) : ℝ) ^ 2 with hF
  have hF0 : ∀ n, M ≤ n → F n = 0 := by
    intro n hn
    simp only [hF, Nat.sub_eq_zero_of_le hn, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  have hFmono : ∀ a b, a ≤ b → F b ≤ F a := by
    intro a b hab
    simp only [hF]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.sub_le_sub_left hab M)) 2
  have key : (q : ℝ) * ∑ i ∈ range M, F (h * q * (i + 1)) ≤ ∑ i ∈ range M, F (h * (i + 1)) := by
    have hblock : ∀ J : ℕ, (q : ℝ) * ∑ i ∈ range J, F (h * q * (i + 1))
        ≤ ∑ n ∈ range (q * J), F (h * (n + 1)) := by
      intro J
      induction J with
      | zero => simp
      | succ J ih =>
        rw [sum_range_succ, mul_add, Nat.mul_succ q J, sum_range_add]
        refine add_le_add ih ?_
        have e : (q : ℝ) * F (h * q * (J + 1)) = ∑ _i ∈ range q, F (h * q * (J + 1)) := by
          rw [sum_const, card_range, nsmul_eq_mul]
        rw [e]
        refine sum_le_sum fun i hi => hFmono _ _ ?_
        have hi' := mem_range.mp hi
        rw [mul_assoc]
        refine Nat.mul_le_mul_left _ ?_
        rw [Nat.mul_succ]
        omega
    refine le_trans (hblock M) (le_of_eq ?_)
    refine (sum_subset (range_mono (Nat.le_mul_of_pos_left M (by omega))) fun n _ hn => ?_).symm
    have h1 : M ≤ n := by simpa using hn
    exact hF0 _ (le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega)))
  have e1 := sum_multiples M (h * q) (Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))) F hF0
  have e2 := sum_multiples M h hh F hF0
  rw [S_eq, S_eq]
  have e3 : (∑ j ∈ range M, if h * q ∣ j + 1 then ((M - (j + 1) : ℕ) : ℝ) ^ 2 else 0)
      = ∑ i ∈ range M, F (h * q * (i + 1)) := e1
  have e4 : (∑ j ∈ range M, if h ∣ j + 1 then ((M - (j + 1) : ℕ) : ℝ) ^ 2 else 0)
      = ∑ i ∈ range M, F (h * (i + 1)) := e2
  rw [e3, e4]
  nlinarith [key]

/-- The sum of the cosines over the residues prime to `q`. -/
lemma sum_units (q R : ℕ) (hq : q.Prime) (hR : 1 ≤ R) (n : ℤ) :
    ∑ a ∈ (range (q ^ R)).filter (fun a => ¬ q ∣ a),
        Real.cos (2 * π * ((a : ℝ) * n / (q ^ R : ℕ)))
      = (if ((q ^ R : ℕ) : ℤ) ∣ n then ((q ^ R : ℕ) : ℝ) else 0)
        - (if ((q ^ (R - 1) : ℕ) : ℤ) ∣ n then ((q ^ (R - 1) : ℕ) : ℝ) else 0) := by
  have hq0 : 0 < q := hq.pos
  have huR : q ^ R = q * q ^ (R - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1 := sum_cos_mod (q ^ R) (pow_pos hq0 R) n
  have h2 := sum_cos_mod (q ^ (R - 1)) (pow_pos hq0 _) n
  rw [← sum_filter_add_sum_filter_not (range (q ^ R)) (fun a => q ∣ a)] at h1
  have hmult : ∑ a ∈ (range (q ^ R)).filter (fun a => q ∣ a),
        Real.cos (2 * π * ((a : ℝ) * n / (q ^ R : ℕ)))
      = ∑ b ∈ range (q ^ (R - 1)), Real.cos (2 * π * ((b : ℝ) * n / (q ^ (R - 1) : ℕ))) := by
    have himg : (range (q ^ R)).filter (fun a => q ∣ a)
        = (range (q ^ (R - 1))).image (fun b => q * b) := by
      ext a
      rw [mem_filter, mem_image, mem_range]
      constructor
      · rintro ⟨ha, b, rfl⟩
        refine ⟨b, mem_range.mpr ?_, rfl⟩
        rw [huR] at ha
        exact Nat.lt_of_mul_lt_mul_left ha
      · rintro ⟨b, hb, rfl⟩
        refine ⟨?_, Nat.dvd_mul_right _ _⟩
        rw [huR]
        exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hb) hq0
    rw [himg, sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hq0 h]
    refine sum_congr rfl fun b _ => ?_
    congr 2
    rw [huR, Nat.cast_mul, Nat.cast_mul]
    have : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    field_simp
  rw [hmult, h2] at h1
  rw [← h1]
  ring

/-- **Averaging over the units.** -/
theorem average (q R M : ℕ) (hq : q.Prime) (hR : 1 ≤ R) (hM : 1 ≤ M) (G : ℕ → ℝ)
    (hG : ∀ ξ, 0 ≤ G ξ) (hG0 : G 0 = 1) :
    (∑ a ∈ (range (q ^ R)).filter (fun a => ¬ q ∣ a),
        ∑ ξ ∈ range (q ^ R), G ξ * (H M (((a * ξ : ℕ) : ℝ) / (q ^ R : ℕ)) / H M 0))
      / (((range (q ^ R)).filter fun a => ¬ q ∣ a).card : ℝ)
      ≤ 1 + 3 * (M : ℝ) / (2 * (M : ℝ) ^ 2 + 1) * ((∑ ξ ∈ range (q ^ R), G ξ) - 1) := by
  set u := q ^ R with hu
  set U := (range u).filter fun a => ¬ q ∣ a with hU
  have hq0 : 0 < q := hq.pos
  have hq2 : 2 ≤ q := hq.two_le
  have hu0 : 0 < u := pow_pos hq0 R
  have hu1 : 1 < u := Nat.one_lt_pow (by omega) (by omega)
  have hH0 := H_at_zero_pos M hM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have huR : u = q * q ^ (R - 1) := by
    rw [hu, ← pow_succ']
    congr 1
    omega
  -- the number of units
  have hcard : (U.card : ℝ) = (u : ℝ) - (q ^ (R - 1) : ℕ) := by
    have h := sum_units q R hq hR 0
    simp only [Int.cast_zero, mul_zero, zero_div, mul_zero, Real.cos_zero, dvd_zero, if_true] at h
    rw [sum_const, nsmul_eq_mul, mul_one] at h
    exact h
  have hh0 : (0 : ℝ) < (q ^ (R - 1) : ℕ) := by
    have : 0 < q ^ (R - 1) := pow_pos hq0 _
    exact_mod_cast this
  have hcardpos : (0 : ℝ) < U.card := by
    rw [hcard, huR, Nat.cast_mul]
    have h1 : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    have := mul_le_mul_of_nonneg_right h1 hh0.le
    linarith
  have hKM : (M : ℝ) ^ 2 / H M 0 = 3 * M / (2 * (M : ℝ) ^ 2 + 1) := by
    rw [H_at_zero]
    field_simp
  -- the average of the kernel at a non-zero frequency
  have hkey : ∀ ξ ∈ range u, ξ ≠ 0 →
      ∑ a ∈ U, H M (((a * ξ : ℕ) : ℝ) / u) ≤ (U.card : ℝ) * (M : ℝ) ^ 2 := by
    intro ξ hξ hξ0
    have hξu := mem_range.mp hξ
    -- the conductor
    obtain ⟨e, heR, hdvd⟩ : ∃ e, e < R ∧ Nat.gcd ξ u = q ^ e := by
      have h1 : Nat.gcd ξ u ∣ q ^ R := hu ▸ Nat.gcd_dvd_right ξ u
      obtain ⟨e, he, hg⟩ := (Nat.dvd_prime_pow hq).mp h1
      refine ⟨e, lt_of_le_of_ne he fun h => ?_, hg⟩
      have h2 : u ∣ ξ := by
        have := Nat.gcd_dvd_left ξ u
        rwa [hg, h, ← hu] at this
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hξ0) h2
      omega
    set d : ℕ := q ^ (R - e) with hd
    set h : ℕ := q ^ (R - e - 1) with hhd
    have hdh : d = h * q := by
      rw [hd, hhd, ← pow_succ]
      congr 1
      omega
    obtain ⟨ξ', hξ'⟩ : q ^ e ∣ ξ := hdvd ▸ Nat.gcd_dvd_left ξ u
    have hco : Nat.Coprime ξ' q := by
      refine (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun hc => ?_))
      have h1 : q ^ (e + 1) ∣ Nat.gcd ξ u := by
        refine Nat.dvd_gcd ?_ (hu ▸ pow_dvd_pow q (by omega))
        rw [hξ', pow_succ]
        exact Nat.mul_dvd_mul_left _ hc
      rw [hdvd] at h1
      have := Nat.le_of_dvd (pow_pos hq0 _) h1
      exact absurd (Nat.pow_lt_pow_right (by omega : 1 < q) (Nat.lt_succ_self e)) (not_lt.mpr this)
    have hdiv : ∀ (k : ℕ), k ≤ R - e → ∀ m : ℤ,
        ((q ^ (e + k) : ℕ) : ℤ) ∣ (ξ : ℤ) * m ↔ ((q ^ k : ℕ) : ℤ) ∣ m := by
      intro k _ m
      have e1 : (ξ : ℤ) * m = ((q ^ e : ℕ) : ℤ) * ((ξ' : ℤ) * m) := by
        rw [hξ', Nat.cast_mul, mul_assoc]
      have e2 : ((q ^ (e + k) : ℕ) : ℤ) = ((q ^ e : ℕ) : ℤ) * ((q ^ k : ℕ) : ℤ) := by
        rw [pow_add, Nat.cast_mul]
      have hne : ((q ^ e : ℕ) : ℤ) ≠ 0 := by
        have : 0 < q ^ e := pow_pos hq0 _
        exact_mod_cast this.ne'
      rw [e1, e2, mul_dvd_mul_iff_left hne]
      have hc : IsCoprime ((q ^ k : ℕ) : ℤ) (ξ' : ℤ) :=
        Nat.Coprime.isCoprime (Nat.Coprime.pow_left k (Nat.coprime_comm.mp hco))
      exact ⟨fun h => hc.dvd_of_dvd_mul_left h, fun h => h.mul_left _⟩
    have hsum : ∑ a ∈ U, H M (((a * ξ : ℕ) : ℝ) / u)
        = (u : ℝ) * S M d - (q ^ (R - 1) : ℕ) * S M h := by
      have e1 : ∀ a ∈ U, H M (((a * ξ : ℕ) : ℝ) / u)
          = ∑ k ∈ range M, ∑ l ∈ range M, ((M : ℝ) - |(((k : ℤ) - l : ℤ) : ℝ)|)
              * Real.cos (2 * π * ((a : ℝ) * (((ξ : ℤ) * ((k : ℤ) - l) : ℤ) : ℝ) / u)) := by
        intro a _
        unfold H c
        refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
        congr 2
        push_cast
        ring
      rw [sum_congr rfl e1, sum_comm]
      unfold S
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_comm, mul_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun l _ => ?_
      rw [← mul_sum]
      have h1 := sum_units q R hq hR ((ξ : ℤ) * ((k : ℤ) - l))
      rw [← hu, ← hU] at h1
      rw [h1]
      have c1 : ((u : ℕ) : ℤ) ∣ (ξ : ℤ) * ((k : ℤ) - l) ↔ (d : ℤ) ∣ (k : ℤ) - l := by
        have := hdiv (R - e) le_rfl ((k : ℤ) - l)
        rwa [show e + (R - e) = R by omega, ← hu, ← hd] at this
      have c2 : ((q ^ (R - 1) : ℕ) : ℤ) ∣ (ξ : ℤ) * ((k : ℤ) - l) ↔ (h : ℤ) ∣ (k : ℤ) - l := by
        have := hdiv (R - e - 1) (by omega) ((k : ℤ) - l)
        rwa [show e + (R - e - 1) = R - 1 by omega, ← hhd] at this
      by_cases a1 : (d : ℤ) ∣ (k : ℤ) - l <;> by_cases a2 : (h : ℤ) ∣ (k : ℤ) - l <;>
        simp only [c1, c2, a1, a2, if_true, if_false] <;> ring
    have hb := S_bound M q h (by omega) (Nat.one_le_pow _ _ hq0)
    rw [← hdh] at hb
    rw [hsum, hcard]
    have hur : (u : ℝ) = q * (q ^ (R - 1) : ℕ) := by rw [huR, Nat.cast_mul]
    rw [hur]
    have := mul_le_mul_of_nonneg_left hb hh0.le
    nlinarith
  rw [div_le_iff₀ hcardpos, sum_comm]
  have hsplit : range u = insert 0 ((range u).erase 0) :=
    (insert_erase (mem_range.mpr hu0)).symm
  have hGsum : ∑ ξ ∈ range u, G ξ = 1 + ∑ ξ ∈ (range u).erase 0, G ξ := by
    rw [← add_sum_erase _ _ (mem_range.mpr hu0), hG0]
  rw [← add_sum_erase _ _ (mem_range.mpr hu0), hGsum, add_sub_cancel_left]
  have h0 : ∑ a ∈ U, G 0 * (H M (((a * 0 : ℕ) : ℝ) / u) / H M 0) = (U.card : ℝ) := by
    have : ∀ a ∈ U, G 0 * (H M (((a * 0 : ℕ) : ℝ) / u) / H M 0) = 1 := by
      intro a _
      rw [hG0, mul_zero, Nat.cast_zero, zero_div, div_self hH0.ne', mul_one]
    rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_one]
  rw [h0]
  have hrest : ∑ ξ ∈ (range u).erase 0, ∑ a ∈ U, G ξ * (H M (((a * ξ : ℕ) : ℝ) / u) / H M 0)
      ≤ ∑ ξ ∈ (range u).erase 0, G ξ * ((U.card : ℝ) * (3 * M / (2 * (M : ℝ) ^ 2 + 1))) := by
    refine sum_le_sum fun ξ hξ => ?_
    rw [← mul_sum, ← sum_div]
    refine mul_le_mul_of_nonneg_left ?_ (hG ξ)
    have h1 := hkey ξ (mem_of_mem_erase hξ) (ne_of_mem_erase hξ)
    rw [← hKM, mul_div_assoc']
    exact div_le_div_of_nonneg_right h1 hH0.le
  refine le_trans (add_le_add le_rfl hrest) (le_of_eq ?_)
  rw [← sum_mul]
  ring

/-! ## Digit factors at a modulus -/

/-- `#{x' < N : m ∣ x - x'}` summed over `x < N`, with `N = κ m + r`. -/
lemma pairs_count (N m : ℕ) (hm : 0 < m) :
    ((range N ×ˢ range N).filter fun p : ℕ × ℕ => p.1 % m = p.2 % m).card
      = (N / m) ^ 2 * m + 2 * (N % m) * (N / m) + N % m := by
  have hfib : ∀ x ∈ range N, ((range N).filter fun y => x % m = y % m).card
      = N / m + if x % m < N % m then 1 else 0 := by
    intro x _
    have h := Nat.count_modEq_card N hm x
    rw [Nat.count_eq_card_filter_range] at h
    rw [← h]
    congr 1
    refine filter_congr fun y _ => ?_
    exact eq_comm
  have hsum : ((range N ×ˢ range N).filter fun p : ℕ × ℕ => p.1 % m = p.2 % m).card
      = ∑ x ∈ range N, ((range N).filter fun y => x % m = y % m).card := by
    rw [card_filter, sum_product]
    exact sum_congr rfl fun x _ => (card_filter _ _).symm
  rw [hsum, sum_congr rfl hfib, sum_add_distrib, sum_const, card_range, smul_eq_mul]
  have hcount : ∑ x ∈ range N, (if x % m < N % m then 1 else 0)
      = (N % m) * (N / m) + N % m := by
    have hr : N % m < m := Nat.mod_lt _ hm
    have hind : ∀ K : ℕ, ∑ x ∈ range (m * K), (if x % m < N % m then 1 else 0) = (N % m) * K := by
      intro K
      induction K with
      | zero => simp
      | succ K ih =>
        rw [Nat.mul_succ, sum_range_add, ih, Nat.mul_succ]
        congr 1
        have e : ∀ x ∈ range m, (if (m * K + x) % m < N % m then 1 else 0)
            = if x < N % m then 1 else 0 := by
          intro x hx
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (mem_range.mp hx)]
        rw [sum_congr rfl e, ← card_filter]
        have : (range m).filter (fun x => x < N % m) = range (N % m) := by
          ext x
          rw [mem_filter, mem_range, mem_range]
          omega
        rw [this, card_range]
    have hN : N = m * (N / m) + N % m := (Nat.div_add_mod N m).symm
    have hsplit : ∑ x ∈ range N, (if x % m < N % m then 1 else 0)
        = (∑ x ∈ range (m * (N / m)), (if x % m < N % m then 1 else 0))
          + ∑ x ∈ range (N % m), (if (m * (N / m) + x) % m < N % m then 1 else 0) := by
      rw [← sum_range_add (fun x => if x % m < N % m then 1 else 0), ← hN]
    rw [hsplit, hind]
    congr 1
    have e : ∀ x ∈ range (N % m), (if (m * (N / m) + x) % m < N % m then 1 else 0) = 1 := by
      intro x hx
      have hx' := mem_range.mp hx
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega), if_pos hx']
    rw [sum_congr rfl e, sum_const, card_range, smul_eq_mul, mul_one]
  rw [hcount]
  have e : N * (N / m) = (m * (N / m) + N % m) * (N / m) := by rw [Nat.div_add_mod]
  rw [e]
  ring

/-- The sum of `|Σ_{x<N} e(b x / Q)|²` over `b < Q`. -/
lemma sum_normSq_range (N Q : ℕ) (hQ : 0 < Q) :
    ∑ b ∈ range Q, Complex.normSq (∑ x ∈ range N, e ((b : ℝ) * x / Q))
      = (Q : ℝ) * ((range N ×ˢ range N).filter fun p : ℕ × ℕ => p.1 % Q = p.2 % Q).card := by
  have hexp : ∀ b : ℕ, Complex.normSq (∑ x ∈ range N, e ((b : ℝ) * x / Q))
      = ∑ x ∈ range N, ∑ y ∈ range N,
          Real.cos (2 * π * ((b : ℝ) * (((x : ℤ) - y : ℤ) : ℝ) / Q)) := by
    intro b
    have hre : ∀ t : ℝ, (e t).re = Real.cos (2 * π * t) ∧ (e t).im = Real.sin (2 * π * t) := by
      intro t
      unfold TwoPrimesFormula.e
      exact ⟨Complex.exp_ofReal_mul_I_re _, Complex.exp_ofReal_mul_I_im _⟩
    rw [Complex.normSq_apply, Complex.re_sum, Complex.im_sum, sum_mul_sum, sum_mul_sum,
      ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    rw [(hre _).1, (hre _).1, (hre _).2, (hre _).2, ← Real.cos_sub]
    congr 1
    push_cast
    ring
  rw [sum_congr rfl fun b _ => hexp b, sum_comm, card_filter, sum_product, Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm, Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_cos_mod Q hQ]
  have hc : (Q : ℤ) ∣ (x : ℤ) - y ↔ x % Q = y % Q := by
    rw [← Int.modEq_iff_dvd, Int.natCast_modEq_iff]
    exact eq_comm
  by_cases h : x % Q = y % Q
  · rw [if_pos (hc.mpr h), if_pos h, Nat.cast_one, mul_one]
  · rw [if_neg (fun c => h (hc.mp c)), if_neg h, Nat.cast_zero, mul_zero]

/-- Orthogonality for a general family of integers. -/
lemma sum_normSq_family {ι : Type*} (I : Finset ι) (f : ι → ℤ) (Q : ℕ) (hQ : 0 < Q) :
    ∑ b ∈ range Q, Complex.normSq (∑ i ∈ I, e ((b : ℝ) * f i / Q))
      = (Q : ℝ) * ((I ×ˢ I).filter fun p : ι × ι => (Q : ℤ) ∣ f p.1 - f p.2).card := by
  classical
  have hexp : ∀ b : ℕ, Complex.normSq (∑ i ∈ I, e ((b : ℝ) * f i / Q))
      = ∑ i ∈ I, ∑ j ∈ I, Real.cos (2 * π * ((b : ℝ) * ((f i - f j : ℤ) : ℝ) / Q)) := by
    intro b
    have hre : ∀ t : ℝ, (e t).re = Real.cos (2 * π * t) ∧ (e t).im = Real.sin (2 * π * t) := by
      intro t
      unfold TwoPrimesFormula.e
      exact ⟨Complex.exp_ofReal_mul_I_re _, Complex.exp_ofReal_mul_I_im _⟩
    rw [Complex.normSq_apply, Complex.re_sum, Complex.im_sum, sum_mul_sum, sum_mul_sum,
      ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [(hre _).1, (hre _).1, (hre _).2, (hre _).2, ← Real.cos_sub]
    congr 1
    push_cast
    ring
  rw [sum_congr rfl fun b _ => hexp b, sum_comm, card_filter, sum_product, Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm, Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_cos_mod Q hQ]
  split <;> simp

/-- The geometric sum bound: `|Σ_{x<N} e(x θ)| ≤ Q / 2` when `‖θ‖ ≥ 1/Q`. -/
lemma norm_geom_le (N Q : ℕ) (hQ : 0 < Q) (b : ℤ) (hb : ¬ (Q : ℤ) ∣ b) :
    ‖∑ x ∈ range N, e ((x : ℝ) * ((b : ℝ) / Q))‖ ≤ (Q : ℝ) / 2 := by
  set θ : ℝ := (b : ℝ) / Q with hθ
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hpow : ∀ x : ℕ, e ((x : ℝ) * θ) = e θ ^ x := by
    intro x
    unfold TwoPrimesFormula.e
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- distance from the integers
  have hdist : 1 / (Q : ℝ) ≤ |θ - round θ| := by
    have e1 : θ - round θ = ((b - round θ * Q : ℤ) : ℝ) / Q := by
      rw [hθ]
      push_cast
      field_simp
    have h0 : b - round θ * Q ≠ 0 := by
      intro h
      apply hb
      have : b = round θ * Q := by omega
      rw [this]
      exact dvd_mul_left _ _
    have h1 : (1 : ℝ) ≤ |((b - round θ * Q : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
    rw [e1, abs_div, abs_of_pos hQr]
    exact div_le_div_of_nonneg_right h1 hQr.le
  have hnorm : 4 / (Q : ℝ) ≤ ‖e θ - 1‖ := by
    have hsin : ‖e θ - 1‖ = 2 * |Real.sin (π * θ)| := by
      have e1 : e θ - 1 = Complex.exp (Complex.I * ((2 * π * θ : ℝ) : ℂ)) - 1 := by
        unfold TwoPrimesFormula.e
        rw [mul_comm]
      rw [e1, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
      congr 2
      congr 1
      ring
    have hper : |Real.sin (π * θ)| = |Real.sin (π * (θ - round θ))| := by
      have e1 : π * θ = π * (θ - round θ) + (round θ : ℤ) * π := by ring
      rw [e1, Real.sin_add_int_mul_pi, abs_mul]
      simp
    have hhalf : |θ - round θ| ≤ 1 / 2 := abs_sub_round θ
    have hj : 2 * |θ - round θ| ≤ |Real.sin (π * (θ - round θ))| := by
      have h1 : |π * (θ - round θ)| ≤ π / 2 := by
        rw [abs_mul, abs_of_pos pi_pos]
        have := mul_le_mul_of_nonneg_left hhalf pi_pos.le
        linarith
      have h2 := Real.mul_abs_le_abs_sin h1
      rw [abs_mul, abs_of_pos pi_pos] at h2
      refine le_trans (le_of_eq ?_) h2
      field_simp
    rw [hsin, hper]
    have h3 := mul_le_mul_of_nonneg_left hdist (by norm_num : (0 : ℝ) ≤ 4)
    have e2 : 4 / (Q : ℝ) = 4 * (1 / (Q : ℝ)) := by ring
    rw [e2]
    linarith
  have hgeom : (∑ x ∈ range N, e θ ^ x) * (e θ - 1) = e θ ^ N - 1 := geom_sum_mul _ _
  rw [sum_congr rfl fun x _ => hpow x]
  have h1 : ‖∑ x ∈ range N, e θ ^ x‖ * ‖e θ - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    refine le_trans (norm_sub_le _ _) ?_
    have h2 : ‖e θ‖ = 1 := TwoPrimesBoxCertificate.norm_e θ
    rw [norm_pow, h2, one_pow, norm_one]
    norm_num
  have h3 := le_trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)) h1
  rw [mul_div_assoc', div_le_iff₀ hQr] at h3
  linarith

/-- The symmetric digit factor has the modulus of the one-sided sum. -/
lemma normSq_factor_eq (J : ℕ) (x : ℝ) :
    Complex.normSq (factor J x)
      = Complex.normSq (∑ k ∈ range (2 * J + 1), e ((k : ℝ) * x)) / ((2 * J + 1 : ℕ) : ℝ) ^ 2 := by
  have h : ∑ j ∈ Icc (-(J : ℤ)) J, e (x * j)
      = e (-(J : ℝ) * x) * ∑ k ∈ range (2 * J + 1), e ((k : ℝ) * x) := by
    rw [mul_sum]
    have himg : Icc (-(J : ℤ)) J = (range (2 * J + 1)).image (fun k : ℕ => (k : ℤ) - J) := by
      ext j
      rw [mem_Icc, mem_image]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(j + J).toNat, mem_range.mpr (by omega), by omega⟩
      · rintro ⟨k, hk, rfl⟩
        have := mem_range.mp hk
        omega
    rw [himg, sum_image fun a _ b _ hab => by omega]
    refine sum_congr rfl fun k _ => ?_
    rw [← e_add]
    congr 1
    push_cast
    ring
  unfold factor
  rw [h, map_div₀, map_mul, Complex.normSq_natCast, ← sq]
  have h1 : Complex.normSq (e (-(J : ℝ) * x)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, TwoPrimesBoxCertificate.norm_e, one_pow]
  rw [h1, one_mul]

/-- The squared factor at a frequency `c / Q` which is not an integer. -/
lemma normSq_factor_le_min (J Q : ℕ) (hQ : 0 < Q) (c : ℤ) (hc : ¬ (Q : ℤ) ∣ c) :
    Complex.normSq (factor J ((c : ℝ) / Q))
      ≤ min 1 ((Q : ℝ) ^ 2 / (4 * ((2 * J + 1 : ℕ) : ℝ) ^ 2)) := by
  refine le_min (normSq_factor_le _ _) ?_
  rw [normSq_factor_eq]
  have h := norm_geom_le (2 * J + 1) Q hQ c hc
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Complex.normSq_eq_norm_sq]
  have e1 : (Q : ℝ) ^ 2 / (4 * ((2 * J + 1 : ℕ) : ℝ) ^ 2)
      = ((Q : ℝ) / 2) ^ 2 / ((2 * J + 1 : ℕ) : ℝ) ^ 2 := by ring
  rw [e1]
  exact div_le_div_of_nonneg_right h2 (sq_nonneg _)

lemma e_int (n : ℤ) : e (n : ℝ) = 1 := by
  unfold TwoPrimesFormula.e
  have : ((2 * π * (n : ℝ) : ℝ) : ℂ) * Complex.I = (n : ℂ) * (2 * π * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma e_mod (Q : ℕ) (hQ : 0 < Q) (a b : ℤ) (h : (Q : ℤ) ∣ a - b) :
    e ((a : ℝ) / Q) = e ((b : ℝ) / Q) := by
  obtain ⟨k, hk⟩ := h
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have e1 : (a : ℝ) / Q = (b : ℝ) / Q + (k : ℝ) := by
    have h1 : a = b + (Q : ℤ) * k := by omega
    rw [h1]
    push_cast
    field_simp
  rw [e1, e_add, e_int, mul_one]

/-- The sum over the non-zero frequencies of one factor with a weight prime to `Q`. -/
lemma sum_factor (J Q w : ℕ) (hQ : 0 < Q) (hw : Nat.Coprime w Q) :
    ∑ b ∈ Ico 1 Q, Complex.normSq (factor J ((b : ℝ) * w / Q))
      = (((2 * J + 1) % Q : ℕ) : ℝ) * ((Q : ℝ) - (((2 * J + 1) % Q : ℕ) : ℝ))
        / ((2 * J + 1 : ℕ) : ℝ) ^ 2 := by
  set N := 2 * J + 1 with hN
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  set g : ℕ → ℝ := fun c => Complex.normSq (∑ x ∈ range N, e ((c : ℝ) * x / Q)) with hg
  have hterm : ∀ b : ℕ, Complex.normSq (factor J ((b : ℝ) * w / Q))
      = g (b * w % Q) / (N : ℝ) ^ 2 := by
    intro b
    rw [normSq_factor_eq, ← hN]
    congr 1
    simp only [hg]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    have h1 := e_mod Q hQ ((k : ℤ) * (b * w : ℕ)) (((b * w % Q : ℕ) : ℤ) * k) (by
      have h2 : (Q : ℤ) ∣ ((b * w : ℕ) : ℤ) - ((b * w % Q : ℕ) : ℤ) := by
        rw [Int.natCast_mod]
        exact Int.dvd_self_sub_emod
      have e3 : (k : ℤ) * ((b * w : ℕ) : ℤ) - ((b * w % Q : ℕ) : ℤ) * k
          = (k : ℤ) * (((b * w : ℕ) : ℤ) - ((b * w % Q : ℕ) : ℤ)) := by ring
      rw [e3]
      exact h2.mul_left _)
    have e4 : (k : ℝ) * ((b : ℝ) * w / Q) = (((k : ℤ) * (b * w : ℕ) : ℤ) : ℝ) / Q := by
      push_cast; ring
    have e5 : (((b * w % Q : ℕ)) : ℝ) * k / Q
        = ((((b * w % Q : ℕ) : ℤ) * k : ℤ) : ℝ) / Q := by
      rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
    rw [e4, e5]
    exact h1
  -- the map `b ↦ b w mod Q` permutes the residues
  have hperm : ∑ b ∈ range Q, g (b * w % Q) = ∑ c ∈ range Q, g c := by
    have hinj : Set.InjOn (fun b => b * w % Q) (range Q) := by
      intro x hx y hy hxy
      have hx' := mem_range.mp hx
      have hy' := mem_range.mp hy
      have h1 : x * w ≡ y * w [MOD Q] := hxy
      have h2 : x ≡ y [MOD Q] := Nat.ModEq.cancel_right_of_coprime (Nat.coprime_comm.mp hw) h1
      have h3 : x % Q = y % Q := h2
      rwa [Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] at h3
    have himg : (range Q).image (fun b => b * w % Q) = range Q := by
      refine eq_of_subset_of_card_le (fun c hc => ?_) ?_
      · obtain ⟨b, _, rfl⟩ := mem_image.mp hc
        exact mem_range.mpr (Nat.mod_lt _ hQ)
      · rw [card_image_of_injOn hinj]
    conv_rhs => rw [← himg]
    rw [sum_image hinj]
  have hall : ∑ c ∈ range Q, g c
      = (Q : ℝ) * (((N / Q) ^ 2 * Q + 2 * (N % Q) * (N / Q) + N % Q : ℕ) : ℝ) := by
    simp only [hg]
    rw [sum_normSq_range N Q hQ, pairs_count N Q hQ]
  have h0 : g (0 * w % Q) = (N : ℝ) ^ 2 := by
    simp only [hg, zero_mul, Nat.zero_mod, Nat.cast_zero, zero_div]
    have : ∀ x ∈ range N, e (0 : ℝ) = 1 := fun _ _ => by simpa using e_int 0
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul, mul_one, Complex.normSq_natCast, sq]
  have hsplit : ∑ b ∈ range Q, g (b * w % Q) = g (0 * w % Q) + ∑ b ∈ Ico 1 Q, g (b * w % Q) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hQ]
  rw [hperm, hall, h0] at hsplit
  rw [sum_congr rfl fun b _ => hterm b, ← sum_div]
  congr 1
  have hdm : (N : ℝ) = ((N / Q : ℕ) : ℝ) * Q + ((N % Q : ℕ) : ℝ) := by
    have : N = N / Q * Q + N % Q := (Nat.div_add_mod' N Q).symm
    exact_mod_cast this
  have e1 : (((N / Q) ^ 2 * Q + 2 * (N % Q) * (N / Q) + N % Q : ℕ) : ℝ)
      = ((N / Q : ℕ) : ℝ) ^ 2 * Q + 2 * ((N % Q : ℕ) : ℝ) * ((N / Q : ℕ) : ℝ)
        + ((N % Q : ℕ) : ℝ) := by
    push_cast
    ring
  rw [e1] at hsplit
  have h3 : ∑ b ∈ Ico 1 Q, g (b * w % Q)
      = (Q : ℝ) * (((N / Q : ℕ) : ℝ) ^ 2 * Q + 2 * ((N % Q : ℕ) : ℝ) * ((N / Q : ℕ) : ℝ)
        + ((N % Q : ℕ) : ℝ)) - (N : ℝ) ^ 2 := by linarith
  rw [h3, hdm]
  ring

/-- **The low conductors.** -/
theorem lowcond (p D t Q M v : ℕ) (hQ : 0 < Q) (hco : Nat.Coprime p Q) (hM : 1 ≤ M)
    (Y : Finset ℤ) (hp : 2 ≤ p) (hD : 5 ≤ D) (j : Fin t) :
    ∑ b ∈ Ico 1 Q, power Q Y b / (Y.card : ℝ) ^ 2
          * (power Q (digitSet p D t) b / ((digitSet p D t).card : ℝ) ^ 2)
          * (H M ((b : ℝ) * v / Q) / H M 0)
      ≤ (((2 * J p D j + 1) % Q : ℕ) : ℝ) * ((Q : ℝ) - (((2 * J p D j + 1) % Q : ℕ) : ℝ))
          / ((2 * J p D j + 1 : ℕ) : ℝ) ^ 2
        * ∏ i ∈ univ.erase j, min 1 ((Q : ℝ) ^ 2 / (4 * ((2 * J p D i + 1 : ℕ) : ℝ) ^ 2)) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hH0 := H_at_zero_pos M hM
  rw [← sum_factor (J p D j) Q (p ^ ((j : ℕ) ^ 2)) hQ (Nat.Coprime.pow_left _ hco), sum_mul]
  refine sum_le_sum fun b hb => ?_
  have hb' := mem_Ico.mp hb
  have hbQ : ¬ Q ∣ b := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hZ := normSq_digitSet (l := p) (D := D) (n := t) hp hD Q b
  have hY1 : power Q Y b / (Y.card : ℝ) ^ 2 ≤ 1 := by
    refine div_le_one_of_le₀ ?_ (sq_nonneg _)
    unfold power
    rw [Complex.normSq_eq_norm_sq]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    refine le_trans (norm_sum_le _ _) ?_
    rw [sum_congr rfl fun y _ => TwoPrimesBoxCertificate.norm_e _, sum_const, nsmul_eq_mul, mul_one]
  have hW : H M ((b : ℝ) * v / Q) / H M 0 ≤ 1 := div_le_one_of_le₀ (H_le_at_zero _ _) hH0.le
  have hZnn : 0 ≤ power Q (digitSet p D t) b / ((digitSet p D t).card : ℝ) ^ 2 :=
    div_nonneg (power_nonneg _ _ _) (sq_nonneg _)
  have h1 : power Q Y b / (Y.card : ℝ) ^ 2
        * (power Q (digitSet p D t) b / ((digitSet p D t).card : ℝ) ^ 2)
        * (H M ((b : ℝ) * v / Q) / H M 0)
      ≤ power Q (digitSet p D t) b / ((digitSet p D t).card : ℝ) ^ 2 := by
    refine le_trans (mul_le_of_le_one_right (mul_nonneg
      (div_nonneg (power_nonneg _ _ _) (sq_nonneg _)) hZnn) hW) ?_
    exact mul_le_of_le_one_left hZnn hY1
  refine le_trans h1 ?_
  rw [hZ, ← mul_prod_erase univ _ (mem_univ j)]
  have earg : ∀ i : Fin t, (b : ℝ) * (p : ℝ) ^ ((i : ℕ) ^ 2) / Q
      = (((b * p ^ ((i : ℕ) ^ 2) : ℕ) : ℤ) : ℝ) / Q := by
    intro i
    push_cast
    ring
  have ej : (b : ℝ) * ((p ^ ((j : ℕ) ^ 2) : ℕ) : ℝ) / Q = (b : ℝ) * (p : ℝ) ^ ((j : ℕ) ^ 2) / Q := by
    rw [Nat.cast_pow]
  rw [ej]
  refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun i _ => Complex.normSq_nonneg _)
    fun i _ => ?_) (Complex.normSq_nonneg _)
  rw [earg i]
  refine normSq_factor_le_min _ Q hQ _ fun h => hbQ ?_
  have h2 : Q ∣ b * p ^ ((i : ℕ) ^ 2) := by exact_mod_cast h
  exact (Nat.Coprime.pow_right _ (Nat.coprime_comm.mp hco)).dvd_of_dvd_mul_right h2

/-! ## The conductor masses of the digits of `q` -/

/-- Digit sums of the levels below `k` are distinct modulo `q^(k^2)`. -/
lemma distinct_mod {q D k : ℕ} (hq : 2 ≤ q) (hD : 5 ≤ D) {x y : ℤ} (hx : x ∈ digitSet q D k)
    (hy : y ∈ digitSet q D k) (h : ((q ^ (k ^ 2) : ℕ) : ℤ) ∣ x - y) : x = y := by
  have hbound : ∀ z ∈ digitSet q D k, (D : ℤ) * |z| ≤ 2 * (q : ℤ) ^ (k ^ 2) := by
    intro z hz
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hz
    rw [mem_vectors] at hd
    have h1 : (D : ℤ) * |value q d| ≤ ∑ i : Fin k, (q : ℤ) ^ (((i : ℕ) + 1) ^ 2) := by
      unfold value
      refine le_trans (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (Int.natCast_nonneg D)) ?_
      rw [mul_sum]
      refine sum_le_sum fun i _ => ?_
      have h3 : (D : ℤ) * (J q D i : ℤ) ≤ (q : ℤ) ^ (2 * (i : ℕ) + 1) := by
        have : D * J q D i ≤ q ^ (2 * (i : ℕ) + 1) := Nat.mul_div_le _ _
        exact_mod_cast this
      have h4 : (D : ℤ) * |d i| ≤ (q : ℤ) ^ (2 * (i : ℕ) + 1) :=
        le_trans (mul_le_mul_of_nonneg_left (hd i) (Int.natCast_nonneg D)) h3
      have e1 : (q : ℤ) ^ (((i : ℕ) + 1) ^ 2)
          = (q : ℤ) ^ ((i : ℕ) ^ 2) * (q : ℤ) ^ (2 * (i : ℕ) + 1) := by
        rw [← pow_add]; congr 1; ring
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (q : ℤ) ^ ((i : ℕ) ^ 2)), e1]
      have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℤ) ≤ (q : ℤ) ^ ((i : ℕ) ^ 2))
      nlinarith
    have h6 : ∑ i : Fin k, (q : ℤ) ^ (((i : ℕ) + 1) ^ 2) ≤ 2 * (q : ℤ) ^ (k ^ 2) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (q : ℤ) ^ ((i + 1) ^ 2)) k]
      exact_mod_cast (sum_levels_lt hq k).le
    exact le_trans h1 h6
  by_contra hne
  have hpos : (0 : ℤ) < (q : ℤ) ^ (k ^ 2) := by
    have : (0 : ℤ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity
  rw [Nat.cast_pow] at h
  have h1 : (q : ℤ) ^ (k ^ 2) ≤ |x - y| :=
    Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hne)) ((dvd_abs _ _).mpr h)
  have h2 := hbound x hx
  have h3 := hbound y hy
  have h4 : |x - y| ≤ |x| + |y| := abs_sub _ _
  have h5 : (5 : ℤ) ≤ D := by exact_mod_cast hD
  have h6 := mul_le_mul_of_nonneg_left (le_trans h1 h4) (Int.natCast_nonneg D)
  have h7 := mul_le_mul_of_nonneg_right h5 hpos.le
  rw [mul_add] at h6
  omega

/-- **The conductor masses of the digits of `q`.** -/
theorem qmass (q D n a k : ℕ) (hq : 2 ≤ q) (hD : 5 ≤ D) (hk : k < n) (hka : k ^ 2 < a)
    (hak : a ≤ (k + 1) ^ 2) :
    ∑ b ∈ range (q ^ a), power (q ^ a) (digitSet q D n) b / ((digitSet q D n).card : ℝ) ^ 2
      = (q ^ (k ^ 2) : ℝ) / ((digitSet q D k).card : ℝ)
        * (1 + ((((2 * J q D k + 1) % q ^ (a - k ^ 2) : ℕ)) : ℝ)
            * (((q ^ (a - k ^ 2) : ℕ) : ℝ) - (((2 * J q D k + 1) % q ^ (a - k ^ 2) : ℕ) : ℝ))
            / ((2 * J q D k + 1 : ℕ) : ℝ) ^ 2) := by
  have hq0 : 0 < q := by omega
  set w : ℕ := q ^ (k ^ 2) with hw
  set d : ℕ := q ^ (a - k ^ 2) with hd
  set Q : ℕ := q ^ a with hQd
  set N : ℕ := 2 * J q D k + 1 with hN
  set U := digitSet q D k with hU
  have hw0 : 0 < w := pow_pos hq0 _
  have hd0 : 0 < d := pow_pos hq0 _
  have hQ0 : 0 < Q := pow_pos hq0 _
  have hQwd : Q = w * d := by
    rw [hQd, hw, hd, ← pow_add]
    congr 1
    omega
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hUc : (0 : ℝ) < U.card := by
    have : U.Nonempty := Finset.Nonempty.image ⟨0, mem_vectors.mpr fun i => by simp⟩ _
    exact_mod_cast this.card_pos
  -- the factors above the level `k` are trivial
  have hprod : ∀ b : ℕ, power Q (digitSet q D n) b / ((digitSet q D n).card : ℝ) ^ 2
      = Complex.normSq (∑ p ∈ U ×ˢ range N, e ((b : ℝ) * ((p.1 + (w : ℤ) * p.2 : ℤ) : ℝ) / Q))
        / ((U.card : ℝ) * N) ^ 2 := by
    intro b
    rw [normSq_digitSet (l := q) (D := D) (n := n) hq hD Q b]
    set F : ℕ → ℝ := fun i =>
      Complex.normSq (factor (J q D i) ((b : ℝ) * (q : ℝ) ^ (i ^ 2) / Q)) with hF
    have h1 : ∏ i : Fin n, Complex.normSq (factor (J q D i) ((b : ℝ) * (q : ℝ) ^ ((i : ℕ) ^ 2) / Q))
        = ∏ i ∈ range n, F i := Fin.prod_univ_eq_prod_range F n
    have h2 : ∏ i ∈ range n, F i = ∏ i ∈ range (k + 1), F i := by
      refine (prod_subset (range_mono (by omega)) fun i _ hi => ?_).symm
      have hik : k + 1 ≤ i := by simpa using hi
      have hai : a ≤ i ^ 2 := le_trans hak (Nat.pow_le_pow_left hik 2)
      have harg : (b : ℝ) * (q : ℝ) ^ (i ^ 2) / Q = (((b * q ^ (i ^ 2 - a) : ℕ) : ℤ) : ℝ) := by
        have e1 : (q : ℝ) ^ (i ^ 2) = (q : ℝ) ^ (i ^ 2 - a) * (q : ℝ) ^ a := by
          rw [← pow_add]
          congr 1
          omega
        have hqa : (q : ℝ) ^ a ≠ 0 := by
          have : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
          exact pow_ne_zero _ this
        rw [e1, hQd, Nat.cast_pow]
        push_cast
        field_simp
      simp only [hF, harg]
      unfold factor
      have h3 : ∀ j ∈ Icc (-(J q D i : ℤ)) (J q D i),
          e (((((b * q ^ (i ^ 2 - a) : ℕ)) : ℤ) : ℝ) * j) = 1 := by
        intro j _
        have := e_int ((((b * q ^ (i ^ 2 - a) : ℕ)) : ℤ) * j)
        rwa [Int.cast_mul] at this
      rw [sum_congr rfl h3, sum_const, nsmul_eq_mul, mul_one, Int.card_Icc]
      have h4 : (((J q D i : ℤ) + 1 - -(J q D i : ℤ)).toNat : ℂ) = ((2 * J q D i + 1 : ℕ) : ℂ) := by
        congr 1
        omega
      rw [h4, div_self (Nat.cast_ne_zero.mpr (by omega)), map_one]
    have h5 : ∏ i ∈ range k, F i = power Q U b / (U.card : ℝ) ^ 2 := by
      rw [hU, normSq_digitSet (l := q) (D := D) (n := k) hq hD Q b]
      exact (Fin.prod_univ_eq_prod_range F k).symm
    have h6 : F k = Complex.normSq (∑ x ∈ range N, e ((x : ℝ) * ((b : ℝ) * w / Q))) / (N : ℝ) ^ 2 := by
      simp only [hF]
      rw [normSq_factor_eq, ← hN]
      have e1 : (b : ℝ) * (q : ℝ) ^ (k ^ 2) / Q = (b : ℝ) * w / Q := by
        rw [hw, Nat.cast_pow q (k ^ 2)]
      rw [e1]
    rw [h1, h2, prod_range_succ, h5, h6]
    have hsum : ∑ p ∈ U ×ˢ range N, e ((b : ℝ) * ((p.1 + (w : ℤ) * p.2 : ℤ) : ℝ) / Q)
        = (∑ y ∈ U, e ((b : ℝ) * y / Q)) * ∑ x ∈ range N, e ((x : ℝ) * ((b : ℝ) * w / Q)) := by
      rw [sum_mul_sum, sum_product]
      refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
      rw [← e_add]
      congr 1
      push_cast
      ring
    rw [hsum, map_mul]
    unfold power
    rw [mul_pow, div_mul_div_comm]
  -- count the pairs
  have hcount : (((U ×ˢ range N) ×ˢ (U ×ˢ range N)).filter fun p : (ℤ × ℕ) × (ℤ × ℕ) =>
        (Q : ℤ) ∣ (p.1.1 + (w : ℤ) * p.1.2) - (p.2.1 + (w : ℤ) * p.2.2)).card
      = U.card * ((range N ×ˢ range N).filter fun p : ℕ × ℕ => p.1 % d = p.2 % d).card := by
    have hiff : ∀ y ∈ U, ∀ y' ∈ U, ∀ x x' : ℕ,
        (Q : ℤ) ∣ (y + (w : ℤ) * x) - (y' + (w : ℤ) * x') ↔ y = y' ∧ x % d = x' % d := by
      intro y hy y' hy' x x'
      have hxx : (d : ℤ) ∣ (x : ℤ) - x' ↔ x % d = x' % d := by
        rw [← Int.modEq_iff_dvd, Int.natCast_modEq_iff]
        exact eq_comm
      have hwz : (w : ℤ) ≠ 0 := by exact_mod_cast hw0.ne'
      constructor
      · intro h
        have h1 : (w : ℤ) ∣ (y + (w : ℤ) * x) - (y' + (w : ℤ) * x') := by
          refine dvd_trans ?_ h
          rw [hQwd, Nat.cast_mul]
          exact dvd_mul_right _ _
        have h2 : (w : ℤ) ∣ y - y' := by
          have e1 : y - y' = (y + (w : ℤ) * x) - (y' + (w : ℤ) * x') - (w : ℤ) * ((x : ℤ) - x') := by
            ring
          rw [e1]
          exact dvd_sub h1 (dvd_mul_right _ _)
        have hyy : y = y' := distinct_mod hq hD hy hy' (hw ▸ h2)
        refine ⟨hyy, hxx.mp ?_⟩
        rw [hyy, hQwd, Nat.cast_mul] at h
        have e2 : (y' + (w : ℤ) * x) - (y' + (w : ℤ) * x') = (w : ℤ) * ((x : ℤ) - x') := by ring
        rw [e2] at h
        exact (mul_dvd_mul_iff_left hwz).mp h
      · rintro ⟨rfl, h⟩
        have e2 : (y + (w : ℤ) * x) - (y + (w : ℤ) * x') = (w : ℤ) * ((x : ℤ) - x') := by ring
        rw [e2, hQwd, Nat.cast_mul]
        exact mul_dvd_mul_left _ (hxx.mpr h)
    rw [← card_product]
    refine card_bij' (fun p _ => (p.1.1, (p.1.2, p.2.2))) (fun r _ => ((r.1, r.2.1), (r.1, r.2.2)))
      ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_filter] at hp
      obtain ⟨hm, hdv⟩ := hp
      rw [mem_product, mem_product, mem_product] at hm
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hm
      have h := (hiff _ h1 _ h3 _ _).mp hdv
      rw [mem_product, mem_filter, mem_product]
      exact ⟨h1, ⟨h2, h4⟩, h.2⟩
    · intro r hr
      rw [mem_product, mem_filter, mem_product] at hr
      obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hr
      rw [mem_filter, mem_product, mem_product, mem_product]
      exact ⟨⟨⟨h1, h2⟩, ⟨h1, h3⟩⟩, (hiff _ h1 _ h1 _ _).mpr ⟨rfl, h4⟩⟩
    · intro p hp
      rw [mem_filter] at hp
      obtain ⟨hm, hdv⟩ := hp
      rw [mem_product, mem_product, mem_product] at hm
      have h := (hiff _ hm.1.1 _ hm.2.1 _ _).mp hdv
      refine Prod.ext rfl (Prod.ext h.1 rfl)
    · intro r _
      rfl
  rw [sum_congr rfl fun b _ => hprod b, ← sum_div,
    sum_normSq_family (U ×ˢ range N) (fun p => p.1 + (w : ℤ) * p.2) Q hQ0, hcount,
    pairs_count N d hd0]
  have hdm : (N : ℝ) = ((N / d : ℕ) : ℝ) * d + ((N % d : ℕ) : ℝ) := by
    have : N = N / d * d + N % d := (Nat.div_add_mod' N d).symm
    exact_mod_cast this
  have hQr : (Q : ℝ) = (w : ℝ) * d := by exact_mod_cast hQwd
  have hwr : ((q : ℝ) ^ (k ^ 2)) = (w : ℝ) := by rw [hw, Nat.cast_pow]
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [hwr, hQr]
  have e1 : ((U.card * ((N / d) ^ 2 * d + 2 * (N % d) * (N / d) + N % d) : ℕ) : ℝ)
      = (U.card : ℝ) * (((N / d : ℕ) : ℝ) ^ 2 * d + 2 * ((N % d : ℕ) : ℝ) * ((N / d : ℕ) : ℝ)
        + ((N % d : ℕ) : ℝ)) := by
    push_cast
    ring
  rw [e1]
  have hU0 := hUc.ne'
  have hN1 := hN0.ne'
  have key : (d : ℝ) * (((N / d : ℕ) : ℝ) ^ 2 * d + 2 * ((N % d : ℕ) : ℝ) * ((N / d : ℕ) : ℝ)
        + ((N % d : ℕ) : ℝ))
      = (N : ℝ) ^ 2 + ((N % d : ℕ) : ℝ) * ((d : ℝ) - ((N % d : ℕ) : ℝ)) := by
    generalize ((N / d : ℕ) : ℝ) = κ at hdm ⊢
    generalize ((N % d : ℕ) : ℝ) = ρ at hdm ⊢
    rw [hdm]
    ring
  have e2 : (w : ℝ) * d * ((U.card : ℝ) * (((N / d : ℕ) : ℝ) ^ 2 * d
        + 2 * ((N % d : ℕ) : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ)))
      = (w : ℝ) * (U.card : ℝ) * ((N : ℝ) ^ 2 + ((N % d : ℕ) : ℝ)
        * ((d : ℝ) - ((N % d : ℕ) : ℝ))) := by
    rw [← key]
    ring
  rw [e2]
  field_simp


end TwoPrimesSum
