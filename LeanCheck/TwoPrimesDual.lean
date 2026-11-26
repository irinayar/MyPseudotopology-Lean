import Mathlib
import LeanCheck.TwoPrimesEffective

/-!
# A dual form of bounded representations

Let `w i` be integer weights and `J i` digit ranges.

* `dist_rep_le`: if `t = Σ w i * z i` with `|z i| ≤ H * J i`, then `‖t θ‖ ≤ H * Σ J i * ‖w i θ‖`.
* `rep_of_dual`: conversely, suppose that every `θ` with `‖t θ‖ > 1/10` has an index with
  `J i * ‖w i θ‖ ≥ c`.  Then `t = Σ w i * z i` with `|z i| ≤ 2 h * J i`, for every `h` with
  `log (7 h R) ≤ 16 c² h / 3`, where `R ≥ 1` bounds `Σ |w i| J i`.
* `witness_of_dual`: the case of the weights `q^(n^2)` and `p^(n^2)`, giving a witness for the
  target `t` at the radius `4h/D`.

This is a quantitative form of Kronecker's theorem (transference) proved by a finite Fourier
argument; no priority is claimed for the principle.
-/

namespace TwoPrimesDual

open Finset Real TwoPrimesEffective

/-- The distance to the nearest integer. -/
noncomputable def nd (x : ℝ) : ℝ := |x - round x|

lemma nd_le (x : ℝ) (z : ℤ) : nd x ≤ |x - z| := round_le x z

lemma nd_add_le (x y : ℝ) : nd (x + y) ≤ nd x + nd y := dist_add_le x y

lemma nd_zero : nd 0 = 0 := by simp [nd]

lemma nd_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) : nd (∑ i ∈ s, f i) ≤ ∑ i ∈ s, nd (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nd_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact le_trans (nd_add_le _ _) (by linarith)

lemma nd_int_mul_le (z : ℤ) (x : ℝ) : nd (z * x) ≤ |(z : ℝ)| * nd x := by
  refine le_trans (nd_le _ (z * round x)) (le_of_eq ?_)
  rw [nd, ← abs_mul]; congr 1; push_cast; ring

/-- A representation with bounded digits controls `‖t θ‖`. -/
theorem dist_rep_le {ι : Type*} [Fintype ι] (w : ι → ℤ) (J : ι → ℕ) (z : ι → ℤ) (t H : ℤ)
    (hz : ∀ i, |z i| ≤ H * J i) (ht : ∑ i, w i * z i = t) (θ : ℝ) :
    nd (t * θ) ≤ H * ∑ i, (J i : ℝ) * nd (w i * θ) := by
  have e : (t : ℝ) * θ = ∑ i, (z i : ℝ) * ((w i : ℝ) * θ) := by
    rw [← ht]; push_cast; rw [sum_mul]; exact sum_congr rfl (fun i _ => by ring)
  rw [e]
  refine le_trans (nd_sum_le _ _) ?_
  rw [mul_sum]
  refine sum_le_sum (fun i _ => ?_)
  refine le_trans (nd_int_mul_le _ _) ?_
  have h1 : |(z i : ℝ)| ≤ (H : ℝ) * J i := by exact_mod_cast hz i
  have h2 : 0 ≤ nd ((w i : ℝ) * θ) := abs_nonneg _
  calc |(z i : ℝ)| * nd ((w i : ℝ) * θ) ≤ ((H : ℝ) * J i) * nd ((w i : ℝ) * θ) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = H * ((J i : ℝ) * nd ((w i : ℝ) * θ)) := by ring

/-- The sum of `e(kx)` over one digit range. -/
lemma sum_digit (J : ℕ) (x : ℝ) :
    ∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x) = ((((2 * J + 1 : ℕ) : ℝ) * digit J x : ℝ) : ℂ) := by
  have hre : (∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x)).re = ((2 * J + 1 : ℕ) : ℝ) * digit J x := by
    rw [Complex.re_sum, digit]
    have hM : (2 * (J : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    rw [mul_div_cancel₀ _ hM]
    refine sum_congr rfl (fun k _ => ?_)
    rw [e_re]; congr 1; ring
  have him : (∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x)).im = 0 := by
    have hc : (starRingEnd ℂ) (∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x))
        = ∑ k ∈ Icc (-(J : ℤ)) J, e ((k : ℝ) * x) := by
      rw [map_sum]
      refine sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp only [mem_Icc] at hk ⊢; omega
      · intro k hk; simp only [mem_Icc] at hk ⊢; omega
      · intro k _; simp
      · intro k _; simp
      · intro k _
        rw [e_conj]; congr 1; push_cast; ring
    exact Complex.conj_eq_iff_im.mp hc
  apply Complex.ext
  · rw [hre, Complex.ofReal_re]
  · rw [him, Complex.ofReal_im]

lemma e_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : e (∑ i ∈ s, f i) = ∏ i ∈ s, e (f i) := by
  unfold e
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [mul_sum, sum_mul]

/-- **The dual criterion.** -/
theorem rep_of_dual {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℤ) (J : ι → ℕ) (t : ℤ)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) {R h : ℕ} (hR : ∑ i, |w i| * (J i : ℤ) ≤ R)
    (hR1 : 1 ≤ R) (h1 : 1 ≤ h) (hh : log (7 * h * R) ≤ 16 * c ^ 2 * h / 3)
    (hvis : ∀ θ : ℝ, 1 / 10 < nd (t * θ) → ∃ i, 1 ≤ J i ∧ c ≤ J i * nd (w i * θ)) :
    ∃ z : ι → ℤ, (∀ i, |z i| ≤ 2 * (h : ℤ) * J i) ∧ ∑ i, w i * z i = t := by
  classical
  set I : Finset (ι → ℤ) := Fintype.piFinset (fun i => Icc (-(J i : ℤ)) (J i)) with hI
  set val : (ι → ℤ) → ℤ := fun j => ∑ i, w i * j i with hval
  set Ih : Finset (Fin h → (ι → ℤ)) := Fintype.piFinset (fun _ : Fin h => I) with hIh
  set V : (Fin h → (ι → ℤ)) → ℤ := fun a => ∑ k, val (a k) with hV
  have hIne : I.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hI, Fintype.mem_piFinset]; intro i; simp
  have hIpos : (0 : ℝ) < I.card := by exact_mod_cast card_pos.mpr hIne
  have hIhcard : Ih.card = I.card ^ h := by
    rw [hIh, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
  -- bounds
  have hmemI : ∀ j ∈ I, ∀ i, |j i| ≤ (J i : ℤ) := by
    intro j hj i
    rw [hI, Fintype.mem_piFinset] at hj
    have := hj i
    rw [mem_Icc] at this
    exact abs_le.mpr this
  have hvalb : ∀ j ∈ I, |val j| ≤ (R : ℤ) := by
    intro j hj
    refine le_trans (abs_sum_le_sum_abs _ _) (le_trans (sum_le_sum (fun i _ => ?_)) hR)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hmemI j hj i) (abs_nonneg _)
  have hVb : ∀ a ∈ Ih, |V a| ≤ (h : ℤ) * R := by
    intro a ha
    rw [hIh, Fintype.mem_piFinset] at ha
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    refine le_trans (sum_le_sum (fun k _ => hvalb _ (ha k))) ?_
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the exponential sum
  set F : ℝ → ℝ := fun θ => (I.card : ℝ) * ∏ i, digit (J i) ((w i : ℝ) * θ) with hF
  have hsumI : ∀ θ : ℝ, ∑ j ∈ I, e ((val j : ℝ) * θ) = ((F θ : ℝ) : ℂ) := by
    intro θ
    have hprod : ∀ j : ι → ℤ, e ((val j : ℝ) * θ) = ∏ i, e ((j i : ℝ) * ((w i : ℝ) * θ)) := by
      intro j
      rw [← e_sum]
      congr 1
      simp only [hval]
      push_cast
      rw [sum_mul]
      exact sum_congr rfl (fun i _ => by ring)
    simp_rw [hprod]
    rw [hI, ← prod_univ_sum (fun i : ι => Icc (-(J i : ℤ)) (J i))
      (fun (i : ι) (k : ℤ) => e ((k : ℝ) * ((w i : ℝ) * θ)))]
    simp_rw [sum_digit]
    rw [← Complex.ofReal_prod]
    simp only [hF]
    congr 1
    rw [prod_mul_distrib, hI, Fintype.card_piFinset]
    push_cast
    congr 1
    refine prod_congr rfl (fun i _ => ?_)
    rw [card_digits]; push_cast; ring
  have hsumh : ∀ θ : ℝ, ∑ a ∈ Ih, e ((V a : ℝ) * θ) = (((F θ) ^ h : ℝ) : ℂ) := by
    intro θ
    have hprod : ∀ a : Fin h → (ι → ℤ), e ((V a : ℝ) * θ) = ∏ k, e ((val (a k) : ℝ) * θ) := by
      intro a
      rw [← e_sum]
      congr 1
      simp only [hV]
      push_cast
      rw [sum_mul]
    simp_rw [hprod]
    rw [hIh, ← prod_univ_sum (fun _ : Fin h => I) (fun (_ : Fin h) j => e ((val j : ℝ) * θ))]
    rw [prod_const, card_univ, Fintype.card_fin, hsumI, Complex.ofReal_pow]
  have hnorm : ∀ θ : ℝ, ∑ x ∈ Ih ×ˢ Ih, e (((V x.1 - V x.2 : ℤ) : ℝ) * θ)
      = ((((F θ) ^ h) ^ 2 : ℝ) : ℂ) := by
    intro θ
    have hc2 : ∑ b ∈ Ih, e (-((V b : ℝ) * θ)) = (((F θ) ^ h : ℝ) : ℂ) := by
      have h2 := congrArg (starRingEnd ℂ) (hsumh θ)
      rw [map_sum, Complex.conj_ofReal] at h2
      rw [← h2]
      exact sum_congr rfl (fun b _ => (e_conj _).symm)
    have h3 : ∑ x ∈ Ih ×ˢ Ih, e (((V x.1 - V x.2 : ℤ) : ℝ) * θ)
        = (∑ a ∈ Ih, e ((V a : ℝ) * θ)) * (∑ b ∈ Ih, e (-((V b : ℝ) * θ))) := by
      rw [sum_mul_sum, sum_product]
      refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
      rw [← e_add]; congr 1; push_cast; ring
    rw [h3, hsumh, hc2, ← Complex.ofReal_mul, sq]
  -- counting by orthogonality
  set N : ℕ := 2 * (h * R) + t.natAbs + 1 with hNdef
  have hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : ∀ x ∈ Ih ×ˢ Ih, |V x.1 - V x.2| ≤ 2 * ((h : ℤ) * R) := by
    intro x hx
    rw [mem_product] at hx
    have a1 := hVb _ hx.1
    have a2 := hVb _ hx.2
    have := abs_sub (V x.1) (V x.2)
    omega
  set Ct := ((Ih ×ˢ Ih).filter (fun x => V x.1 - V x.2 = t)).card with hCt
  set C0 := ((Ih ×ˢ Ih).filter (fun x => V x.1 - V x.2 = 0)).card with hC0
  have idt : ∑ r ∈ Finset.range N,
      ((F ((r : ℝ) / N)) ^ h) ^ 2 * Real.cos (2 * π * (t * ((r : ℝ) / N))) = N * Ct := by
    have hbt : ∀ x ∈ Ih ×ˢ Ih, |V x.1 - V x.2 - t| < N := by
      intro x hx
      have := hb x hx
      rw [abs_le] at this
      have u1 := le_abs_self t
      have u2 := neg_abs_le t
      rw [abs_lt]; push_cast [hNdef]; omega
    have hco := count_eq (Ih ×ˢ Ih) (fun x => V x.1 - V x.2) t hN hbt
    have : ∀ r : ℕ, ∑ x ∈ Ih ×ˢ Ih, e (((V x.1 - V x.2 - t : ℤ) : ℝ) * ((r : ℝ) / N))
        = (((((F ((r : ℝ) / N)) ^ h) ^ 2 : ℝ)) : ℂ) * e (-(t * ((r : ℝ) / N))) := by
      intro r
      rw [← hnorm, sum_mul]
      refine sum_congr rfl (fun x _ => ?_)
      rw [← e_add]; congr 1; push_cast; ring
    simp_rw [this] at hco
    have h4 := congrArg Complex.re hco
    rw [Complex.re_sum] at h4
    simp only [Complex.re_ofReal_mul, e_re] at h4
    have e2 : ((N : ℂ) * (Ct : ℂ)).re = (N : ℝ) * Ct := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    rw [← hCt, e2] at h4
    rw [← h4]
    refine sum_congr rfl (fun r _ => ?_)
    rw [mul_neg, Real.cos_neg]
  have id0 : ∑ r ∈ Finset.range N, ((F ((r : ℝ) / N)) ^ h) ^ 2 = N * C0 := by
    have hb0 : ∀ x ∈ Ih ×ˢ Ih, |V x.1 - V x.2 - 0| < N := by
      intro x hx
      have := hb x hx
      rw [abs_le] at this
      have u1 := le_abs_self t
      have u2 := neg_abs_le t
      rw [abs_lt]; push_cast [hNdef]; omega
    have hco := count_eq (Ih ×ˢ Ih) (fun x => V x.1 - V x.2) 0 hN hb0
    have : ∀ r : ℕ, ∑ x ∈ Ih ×ˢ Ih, e (((V x.1 - V x.2 - 0 : ℤ) : ℝ) * ((r : ℝ) / N))
        = (((((F ((r : ℝ) / N)) ^ h) ^ 2 : ℝ)) : ℂ) := by
      intro r
      simp only [sub_zero]
      rw [hnorm]
    simp_rw [this] at hco
    rw [← hC0] at hco
    exact_mod_cast hco
  -- Cauchy-Schwarz for the zero count
  have hC0low : ((Ih.card : ℝ)) ^ 2 ≤ (2 * (h * R) + 1 : ℕ) * C0 := by
    set img := Ih.image V with himg
    set rep : ℤ → ℕ := fun v => (Ih.filter (fun a => V a = v)).card with hrep
    have htot : ∑ v ∈ img, rep v = Ih.card := (card_eq_sum_card_image V Ih).symm
    have hsq : ∑ v ∈ img, rep v ^ 2 = C0 := by
      have hmaps : ∀ x ∈ (Ih ×ˢ Ih).filter (fun x => V x.1 - V x.2 = 0), V x.1 ∈ img := by
        intro x hx
        rw [mem_filter, mem_product] at hx
        exact mem_image_of_mem V hx.1.1
      rw [hC0, card_eq_sum_card_fiberwise (f := fun x => V x.1) (t := img)
        (fun x hx => hmaps x hx)]
      refine sum_congr rfl (fun v _ => ?_)
      have e3 : ((Ih ×ˢ Ih).filter (fun x => V x.1 - V x.2 = 0)).filter (fun x => V x.1 = v)
          = (Ih.filter (fun a => V a = v)) ×ˢ (Ih.filter (fun a => V a = v)) := by
        ext x
        simp only [mem_filter, mem_product]
        constructor
        · rintro ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩
          exact ⟨⟨a1, a4⟩, a2, by omega⟩
        · rintro ⟨⟨a1, a2⟩, a3, a4⟩
          exact ⟨⟨⟨a1, a3⟩, by omega⟩, a2⟩
      rw [e3, card_product, sq]
    have hcs := sq_sum_le_card_mul_sum_sq (s := img) (f := rep)
    rw [htot, hsq] at hcs
    have hcard : img.card ≤ 2 * (h * R) + 1 := by
      have hsub : img ⊆ Icc (-((h : ℤ) * R)) ((h : ℤ) * R) := by
        intro v hv
        rw [himg, mem_image] at hv
        obtain ⟨a, ha, rfl⟩ := hv
        rw [mem_Icc]
        exact abs_le.mp (hVb a ha)
      refine le_trans (card_le_card hsub) ?_
      rw [Int.card_Icc]
      have : ((h : ℤ) * R) = ((h * R : ℕ) : ℤ) := by push_cast; ring
      rw [this]; omega
    have := le_trans hcs (Nat.mul_le_mul_right C0 hcard)
    exact_mod_cast this
  -- the far frequencies
  set η : ℝ := exp (-(8 / 3 * c ^ 2)) with hη
  have hfar : ∀ θ : ℝ, 1 / 10 < nd (t * θ) → |F θ| ≤ I.card * η := by
    intro θ hθ
    obtain ⟨i0, hJ, hv⟩ := hvis θ hθ
    have hJr : (1 : ℝ) ≤ J i0 := by exact_mod_cast hJ
    have h2 : c / (J i0) ≤ |(w i0 : ℝ) * θ - round ((w i0 : ℝ) * θ)| := by
      rw [div_le_iff₀ (by linarith), mul_comm]
      exact hv
    have h3 := abs_digit_le_of_far hJ hc0 hc h2
    simp only [hF]
    rw [abs_mul, Nat.abs_cast, abs_prod]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [← mul_prod_erase univ (fun i => |digit (J i) ((w i : ℝ) * θ)|) (mem_univ i0)]
    refine le_trans (mul_le_mul h3 (prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun _ _ => abs_digit_le_one _ _)) (prod_nonneg (fun _ _ => abs_nonneg _))
      (exp_pos _).le) ?_
    rw [mul_one]
  have hpt : ∀ r ∈ Finset.range N,
      4 / 5 * ((F ((r : ℝ) / N)) ^ h) ^ 2 - 9 / 5 * (((I.card : ℝ) * η) ^ h) ^ 2
        ≤ ((F ((r : ℝ) / N)) ^ h) ^ 2 * Real.cos (2 * π * (t * ((r : ℝ) / N))) := by
    intro r _
    set x : ℝ := t * ((r : ℝ) / N) with hx
    have hsqnn : 0 ≤ ((F ((r : ℝ) / N)) ^ h) ^ 2 := sq_nonneg _
    have hbig : 0 ≤ (((I.card : ℝ) * η) ^ h) ^ 2 := sq_nonneg _
    by_cases hnear : nd x ≤ 1 / 10
    · have hcos : 4 / 5 ≤ Real.cos (2 * π * x) := by
        have e4 : Real.cos (2 * π * x) = Real.cos (2 * π * (x - round x)) := by
          have : 2 * π * x = 2 * π * (x - round x) + ((round x : ℤ) : ℝ) * (2 * π) := by
            ring
          rw [this, Real.cos_add_int_mul_two_pi]
        rw [e4]
        refine le_trans ?_ (Real.one_sub_sq_div_two_le_cos)
        have h6 : |2 * π * (x - round x)| ≤ 0.63 := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
          have h7 : |x - round x| ≤ 1 / 10 := hnear
          have := mul_le_mul_of_nonneg_left h7 (show (0 : ℝ) ≤ 2 * π by positivity)
          have hpi : π < 3.15 := pi_lt_d2
          linarith
        have h8 : (2 * π * (x - round x)) ^ 2 ≤ 0.63 ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h6 2
        linarith [show (0.63 : ℝ) ^ 2 ≤ 0.4 by norm_num]
      have := mul_le_mul_of_nonneg_left hcos hsqnn
      linarith
    · have hF' := hfar ((r : ℝ) / N) (not_le.mp hnear)
      have h9 : ((F ((r : ℝ) / N)) ^ h) ^ 2 ≤ (((I.card : ℝ) * η) ^ h) ^ 2 := by
        rw [← sq_abs, abs_pow]
        exact pow_le_pow_left₀ (pow_nonneg (abs_nonneg _) _)
          (pow_le_pow_left₀ (abs_nonneg _) hF' h) 2
      have h10 := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (2 * π * x)) hsqnn
      linarith
  have hsum := sum_le_sum hpt
  rw [sum_sub_distrib, ← mul_sum, id0, idt, sum_const, card_range, nsmul_eq_mul] at hsum
  have hmain : 4 / 5 * (C0 : ℝ) - 9 / 5 * (((I.card : ℝ) * η) ^ h) ^ 2 ≤ Ct := by
    have : (N : ℝ) * (4 / 5 * (C0 : ℝ) - 9 / 5 * (((I.card : ℝ) * η) ^ h) ^ 2) ≤ N * Ct := by
      calc (N : ℝ) * (4 / 5 * (C0 : ℝ) - 9 / 5 * (((I.card : ℝ) * η) ^ h) ^ 2)
          = 4 / 5 * (N * C0) - N * (9 / 5 * (((I.card : ℝ) * η) ^ h) ^ 2) := by ring
        _ ≤ _ := hsum
    exact le_of_mul_le_mul_left this hNr
  -- positivity
  have hpos : (0 : ℝ) < Ct := by
    set M : ℝ := ((2 * (h * R) + 1 : ℕ) : ℝ) with hM
    have hMpos : 0 < M := by rw [hM]; exact_mod_cast (show 0 < 2 * (h * R) + 1 by omega)
    set P : ℝ := ((I.card : ℝ) ^ h) ^ 2 with hP
    have hPpos : 0 < P := by positivity
    have h11 : P ≤ M * C0 := by
      have := hC0low
      rw [hIhcard, Nat.cast_pow] at this
      exact this
    have h12 : (((I.card : ℝ) * η) ^ h) ^ 2 = P * exp (-(16 * c ^ 2 * h / 3)) := by
      rw [hP, mul_pow, mul_pow, hη, ← exp_nat_mul, ← exp_nat_mul]
      congr 2
      push_cast; ring
    have h13 : exp (-(16 * c ^ 2 * h / 3)) ≤ 1 / (7 * h * R) := by
      have h14 : (0 : ℝ) < 7 * h * R := by
        have a1 : (0 : ℝ) < h := by exact_mod_cast h1
        have a2 : (0 : ℝ) < R := by exact_mod_cast hR1
        positivity
      rw [exp_neg, one_div]
      refine inv_anti₀ h14 ?_
      rw [← exp_log h14]
      exact exp_le_exp.mpr hh
    have h15 : 9 / 4 * M < 7 * h * R := by
      have a1 : (1 : ℝ) ≤ (h : ℝ) * R := by exact_mod_cast Nat.mul_le_mul h1 hR1
      rw [hM]; push_cast; nlinarith
    have h16 : 9 / 5 * (P * exp (-(16 * c ^ 2 * h / 3))) < 4 / 5 * (P / M) := by
      have h17 : exp (-(16 * c ^ 2 * h / 3)) < 4 / (9 * M) := by
        refine lt_of_le_of_lt h13 ?_
        have h18 : (0 : ℝ) < 7 * h * R := lt_trans (by positivity) h15
        rw [div_lt_div_iff₀ h18 (by positivity)]
        linarith
      have h19 := mul_lt_mul_of_pos_left h17 hPpos
      have e5 : 4 / 5 * (P / M) = 9 / 5 * (P * (4 / (9 * M))) := by field_simp
      rw [e5]
      linarith
    have h20 : P / M ≤ C0 := by rw [div_le_iff₀ hMpos]; linarith
    rw [h12] at hmain
    linarith
  have hpos' : 0 < Ct := by exact_mod_cast hpos
  obtain ⟨x, hx⟩ := card_pos.mp hpos'
  rw [mem_filter, mem_product] at hx
  obtain ⟨⟨ha, hb'⟩, heq⟩ := hx
  rw [hIh, Fintype.mem_piFinset] at ha hb'
  refine ⟨fun i => (∑ k, x.1 k i) - ∑ k, x.2 k i, fun i => ?_, ?_⟩
  · have bound : ∀ a : Fin h → (ι → ℤ), (∀ k, a k ∈ I) → |∑ k, a k i| ≤ (h : ℤ) * J i := by
      intro a ha'
      refine le_trans (abs_sum_le_sum_abs _ _) ?_
      refine le_trans (sum_le_sum (fun k _ => hmemI _ (ha' k) i)) ?_
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have b1 := bound x.1 ha
    have b2 := bound x.2 hb'
    have e6 : 2 * (h : ℤ) * J i = (h : ℤ) * J i + (h : ℤ) * J i := by ring
    rw [e6]
    exact le_trans (abs_sub _ _) (add_le_add b1 b2)
  · have e7 : ∀ a : Fin h → (ι → ℤ), ∑ i, w i * ∑ k, a k i = V a := by
      intro a
      simp only [hV, hval, mul_sum]
      exact sum_comm
    simp only [mul_sub, sum_sub_distrib]
    rw [e7, e7, heq]

/-! ## Two prime bases -/

/-- Digits bounded by `H p^(2n+1)/D` give a number which is small at the radius `2H/D`. -/
lemma small_of_digits {p D H N : ℕ} (hp : 2 ≤ p) (hD : 1 ≤ D) (hH : 1 ≤ H) (z : Fin N → ℤ)
    (hz : ∀ n : Fin N, (D : ℤ) * |z n| ≤ H * (p : ℤ) ^ (2 * (n : ℕ) + 1)) :
    Small p (2 * H / D) (value p z) := by
  intro m
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  set low : ℝ := ∑ n : Fin N, if (n : ℕ) < m then (p : ℝ) ^ ((n : ℕ) ^ 2) * (z n : ℝ) else 0
    with hlow
  set up : ℤ := ∑ n : Fin N,
    if (n : ℕ) < m then 0 else (p : ℤ) ^ ((n : ℕ) ^ 2 - m ^ 2) * z n with hup
  have hsplit : (value p z : ℝ) / (p : ℝ) ^ (m ^ 2) = low / (p : ℝ) ^ (m ^ 2) + up := by
    have h : (value p z : ℝ) = low + (p : ℝ) ^ (m ^ 2) * up := by
      rw [hlow, hup, value]
      push_cast
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl (fun n _ => ?_)
      split_ifs with h
      · ring
      · have hle : m ^ 2 ≤ (n : ℕ) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        rw [zero_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
    rw [h]; field_simp
  rw [hsplit]
  refine lt_of_le_of_lt (round_le _ up) ?_
  rw [add_sub_cancel_right, abs_div, abs_of_pos (pow_pos hp' _),
    div_lt_div_iff₀ (pow_pos hp' _) hD']
  have hterm : ∀ n : Fin N,
      (D : ℝ) * |if (n : ℕ) < m then (p : ℝ) ^ ((n : ℕ) ^ 2) * (z n : ℝ) else 0|
        ≤ (H : ℝ) * (if (n : ℕ) < m then (p : ℝ) ^ (((n : ℕ) + 1) ^ 2) else 0) := by
    intro n
    split_ifs with h
    · have h1 : (D : ℝ) * |(z n : ℝ)| ≤ H * (p : ℝ) ^ (2 * (n : ℕ) + 1) := by exact_mod_cast hz n
      have hpow : (p : ℝ) ^ (((n : ℕ) + 1) ^ 2)
          = (p : ℝ) ^ ((n : ℕ) ^ 2) * (p : ℝ) ^ (2 * (n : ℕ) + 1) := by
        rw [← pow_add]; congr 1; ring
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ ((n : ℕ) ^ 2)), hpow]
      have := mul_le_mul_of_nonneg_left h1
        (show (0 : ℝ) ≤ (p : ℝ) ^ ((n : ℕ) ^ 2) by positivity)
      linarith
    · simp
  have h1 : (D : ℝ) * |low| ≤ (H : ℝ) * ∑ n ∈ Finset.range m, (p : ℝ) ^ ((n + 1) ^ 2) := by
    have h2 : (D : ℝ) * |low| ≤ (H : ℝ) *
        ∑ n : Fin N, if (n : ℕ) < m then (p : ℝ) ^ (((n : ℕ) + 1) ^ 2) else 0 := by
      rw [hlow, mul_sum]
      refine le_trans (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hD'.le) ?_
      rw [mul_sum]
      exact sum_le_sum (fun n _ => hterm n)
    refine le_trans h2 (mul_le_mul_of_nonneg_left ?_ hH'.le)
    rw [Fin.sum_univ_eq_sum_range (fun n => if n < m then (p : ℝ) ^ ((n + 1) ^ 2) else 0),
      ← sum_filter]
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro n hn
    rw [mem_filter] at hn
    exact Finset.mem_range.mpr hn.2
  have h3 : ∑ n ∈ Finset.range m, (p : ℝ) ^ ((n + 1) ^ 2) < 2 * (p : ℝ) ^ (m ^ 2) := by
    exact_mod_cast sum_levels hp m
  have h4 := mul_lt_mul_of_pos_left h3 hH'
  nlinarith

/-- **Witnesses from the dual criterion.** -/
theorem witness_of_dual {p q D Np Nq R h : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hD : 1 ≤ D) (t : ℤ)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2)
    (hR : ∑ n : Fin Nq, (q : ℤ) ^ ((n : ℕ) ^ 2) * ((q ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℤ)
      + ∑ n : Fin Np, (p : ℤ) ^ ((n : ℕ) ^ 2) * ((p ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℤ) ≤ R)
    (hR1 : 1 ≤ R) (h1 : 1 ≤ h) (hh : log (7 * h * R) ≤ 16 * c ^ 2 * h / 3)
    (hvis : ∀ θ : ℝ, 1 / 10 < nd (t * θ) →
      (∃ n : Fin Nq, 1 ≤ q ^ (2 * (n : ℕ) + 1) / D ∧
          c ≤ ((q ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℝ) * nd ((q : ℝ) ^ ((n : ℕ) ^ 2) * θ))
      ∨ (∃ n : Fin Np, 1 ≤ p ^ (2 * (n : ℕ) + 1) / D ∧
          c ≤ ((p ^ (2 * (n : ℕ) + 1) / D : ℕ) : ℝ) * nd ((p : ℝ) ^ ((n : ℕ) ^ 2) * θ))) :
    ∃ k : ℤ, Small q (4 * h / D) k ∧ Small p (4 * h / D) (k - t) := by
  classical
  set w : Fin Nq ⊕ Fin Np → ℤ := Sum.elim (fun n => (q : ℤ) ^ ((n : ℕ) ^ 2))
    (fun n => (p : ℤ) ^ ((n : ℕ) ^ 2)) with hw
  set J : Fin Nq ⊕ Fin Np → ℕ := Sum.elim (fun n => q ^ (2 * (n : ℕ) + 1) / D)
    (fun n => p ^ (2 * (n : ℕ) + 1) / D) with hJ
  have hR' : ∑ i, |w i| * (J i : ℤ) ≤ R := by
    rw [Fintype.sum_sum_type]
    simp only [hw, hJ, Sum.elim_inl, Sum.elim_inr]
    refine le_trans (le_of_eq ?_) hR
    congr 1 <;> exact sum_congr rfl (fun n _ => by rw [abs_of_nonneg (by positivity)])
  have hvis' : ∀ θ : ℝ, 1 / 10 < nd (t * θ) → ∃ i, 1 ≤ J i ∧ c ≤ J i * nd (w i * θ) := by
    intro θ hθ
    rcases hvis θ hθ with ⟨n, a, b⟩ | ⟨n, a, b⟩
    · exact ⟨Sum.inl n, a, by simpa [hw, hJ] using b⟩
    · exact ⟨Sum.inr n, a, by simpa [hw, hJ] using b⟩
  obtain ⟨z, hz, hsum⟩ := rep_of_dual w J t hc0 hc hR' hR1 h1 hh hvis'
  have hdig : ∀ (r n : ℕ) (y : ℤ), |y| ≤ 2 * (h : ℤ) * ((r ^ (2 * n + 1) / D : ℕ) : ℤ) →
      (D : ℤ) * |y| ≤ ((2 * h : ℕ) : ℤ) * (r : ℤ) ^ (2 * n + 1) := by
    intro r n y hy
    have h2 : D * (r ^ (2 * n + 1) / D) ≤ r ^ (2 * n + 1) := Nat.mul_div_le _ _
    have h3 : (D : ℤ) * ((r ^ (2 * n + 1) / D : ℕ) : ℤ) ≤ (r : ℤ) ^ (2 * n + 1) := by
      exact_mod_cast h2
    calc (D : ℤ) * |y| ≤ D * (2 * (h : ℤ) * ((r ^ (2 * n + 1) / D : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_left hy (by positivity)
      _ = ((2 * h : ℕ) : ℤ) * (D * ((r ^ (2 * n + 1) / D : ℕ) : ℤ)) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have e1 : (2 * ((2 * h : ℕ) : ℝ) / D) = 4 * h / D := by push_cast; ring
  have sq' : Small q (2 * ((2 * h : ℕ) : ℝ) / D) (value q (fun n : Fin Nq => z (Sum.inl n))) :=
    small_of_digits hq hD (by omega) _ (fun n => hdig q n _ (by simpa [hJ] using hz (Sum.inl n)))
  have sp' : Small p (2 * ((2 * h : ℕ) : ℝ) / D) (value p (fun n : Fin Np => z (Sum.inr n))) :=
    small_of_digits hp hD (by omega) _ (fun n => hdig p n _ (by simpa [hJ] using hz (Sum.inr n)))
  rw [e1] at sq' sp'
  refine ⟨value q (fun n : Fin Nq => z (Sum.inl n)), sq', ?_⟩
  have e2 : value q (fun n : Fin Nq => z (Sum.inl n)) - t
      = -value p (fun n : Fin Np => z (Sum.inr n)) := by
    rw [Fintype.sum_sum_type] at hsum
    simp only [hw, Sum.elim_inl, Sum.elim_inr] at hsum
    unfold value
    linear_combination hsum
  rw [e2]
  exact sp'.neg

end TwoPrimesDual
