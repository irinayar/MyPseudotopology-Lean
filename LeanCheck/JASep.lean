import Mathlib
import LeanCheck.JAFarSep

/-!
# The central bound, step 6a: the separated-level estimate

For a level `p` whose next scale satisfies `Q_{p+1} ≥ t_p Q_p` (`t_p = sqrt (log Q_p) ≥ 2`) the factor
`f_p = H_p(0)/H_{p+1}(0)` of the product identity satisfies
`f_p - 1 ≤ 200 D^4 t_p^{-6} + B · 512 C_1 (t_p^{-3} + 4 (8B)^2 e^{-3 t_p})`   (`B = 30D/7`, `C_1 = 200 D^4 + 8B`),
i.e. the paper's (separated-factor) `f_i - 1 ≤ C_D (t_i^{-6} + t_i^{-3} + e^{-3 t_i})`.

Checked here (no axiom, no `sorry`):

* `atom_eq_zero`, `normK_zero_eq`: the only atom of the kernel at `0` is the origin one, and the unit-atom kernel has `K(0) = 1`;
* `support_cn`: a nonzero point of the support of `K` has `cn ≥ 1/Q` (the nonzero atoms are `r/Q`, `|r̃| ≥ 1`);
* `separated_factor`: the estimate above, assembled from `kernel_tail_le'` (atoms beyond `M = ⌈t^2⌉`) and `far_separated` (atoms
  with `1/Q ≤ cn ≤ M/Q`), plus the atom at the origin which contributes exactly `1`.
-/

namespace LeanCheck
namespace JASep

open Finset JATransfer JAMulti JAProduct JAProduct2 JACenter JAFar JAKernTail JAFarSep JAWindowQ

variable {N : ℕ} [NeZero N]

lemma atom_eq_zero (Q d : ℕ) [NeZero Q] (hd : 0 < d) (hN : N = Q * d) (r : ZMod Q)
    (h : (((r.val * d : ℕ)) : ZMod N) = 0) : r = 0 := by
  rw [ZMod.natCast_eq_zero_iff, hN] at h
  have h1 : Q ∣ r.val := (Nat.mul_dvd_mul_iff_right hd).mp h
  have h2 : r.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt r)
  exact (ZMod.val_eq_zero r).mp h2

lemma normK_zero_eq (D : ℝ) (Q : ℕ) [NeZero Q] (hQN : Q ∣ N) : normK N Q (wQ D Q) 0 = 1 := by
  classical
  obtain ⟨d, hd⟩ := hQN
  have hQpos : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exfalso; rw [h, mul_zero] at hd; exact NeZero.ne N hd
    · exact h
  have hNd : N / Q = d := by rw [hd]; exact Nat.mul_div_cancel_left d hQpos
  have hZ : 0 < ∑ x, wQ D Q x := JAFinal.sum_wQ_pos D
  have hk : kern N Q d (wQ D Q) 0 = (∑ x, wQ D Q x) ^ 2 := by
    set Z := ∑ x, wQ D Q x with hZdef
    unfold kern
    rw [Finset.sum_eq_single (0 : ZMod Q)]
    · have h0 : (∑ x, ((wQ D Q x : ℝ) : ℂ) * ZMod.stdAddChar (0 : ZMod Q)) = ((Z : ℝ) : ℂ) := by
        simp [hZdef]
      simp only [ZMod.val_zero, zero_mul, Nat.cast_zero, if_true]
      rw [h0, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · intro r _ hr
      rw [if_neg]
      intro h0
      exact hr (atom_eq_zero Q d hdpos hd r h0.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold normK kernq
  rw [hNd, hk]
  field_simp

/-- Nonzero points in the support of the kernel are at circle norm `≥ 1/Q`. -/
lemma support_cn (D : ℝ) (Q : ℕ) [NeZero Q] (hQN : Q ∣ N) (d : ZMod N) (hd0 : d ≠ 0)
    (hK : normK N Q (wQ D Q) d ≠ 0) : 1 / (Q : ℝ) ≤ cn d := by
  classical
  obtain ⟨e, hd⟩ := hQN
  have hQpos : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQpos
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exfalso; rw [h, mul_zero] at hd; exact NeZero.ne N hd
    · exact h
  have hNd : N / Q = e := by rw [hd]; exact Nat.mul_div_cancel_left e hQpos
  unfold normK kernq kern at hK
  rw [hNd] at hK
  have hsum : (∑ r : ZMod Q, if d = ((r.val * e : ℕ) : ZMod N) then
      ‖∑ x, ((wQ D Q x : ℝ) : ℂ) * ZMod.stdAddChar (r * x)‖ ^ 2 else 0) ≠ 0 := by
    intro h0; apply hK; rw [h0, mul_zero]
  obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hdr : d = ((r.val * e : ℕ) : ZMod N) := by
    by_contra h; exact hr (by rw [if_neg h])
  have hr0 : r ≠ 0 := by
    intro h; apply hd0; rw [hdr, h]; simp
  have hrm : (r.valMinAbs : ℝ) ≠ 0 := by
    have : r.valMinAbs ≠ 0 := fun h => hr0 ((ZMod.valMinAbs_eq_zero r).mp h)
    exact_mod_cast this
  rw [hdr, cn_atom (N := N) Q e hepos hd, nrm_val_eq]
  have h1 : (1 : ℝ) ≤ |(r.valMinAbs : ℝ)| := by
    have : (1 : ℤ) ≤ |r.valMinAbs| := Int.one_le_abs (fun h => hrm (by exact_mod_cast h))
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|r.valMinAbs| : ℤ) : ℝ) := by exact_mod_cast this
    rw [Int.cast_abs] at h2; simpa using h2
  exact div_le_div_of_nonneg_right h1 hQr.le

/-- **(separated-factor)**: the estimate of `f_p - 1` for a separated level. -/
theorem separated_factor (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (sc : ℕ → ℕ) [hsc : ∀ j, NeZero (sc j)]
    (hQ : ∀ j, j < L → 25 * D ≤ sc j) (hQN : ∀ j, j < L → sc j ∣ N)
    (hgrow : ∀ p k, p + k < L → (sc p : ℝ) * Real.exp (Real.sqrt (Real.log (sc p)) * ((k / 2 : ℕ) : ℝ)) ≤
      sc (p + k))
    (p : ℕ) (hp : p + 1 ≤ L)
    (htop : (8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))) ≤ 1 / 2)
    (hε : (2 * m : ℝ) / N ≤ 3 / (4 * sc p))
    (ht2 : 2 ≤ Real.sqrt (Real.log (sc p)))
    (hsep : Real.sqrt (Real.log (sc p)) * (sc p : ℝ) ≤ sc (p + 1)) :
    Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop p) 0 /
        Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 1)) 0 - 1 ≤
      200 * D ^ 4 / (Real.sqrt (Real.log (sc p))) ^ 6 +
        30 * D / 7 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
          ((1 / Real.sqrt (Real.log (sc p))) ^ 3 +
            4 * ((8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (Real.log (sc p))))))) := by
  classical
  set B : ℝ := 30 * D / 7 with hBdef
  set C₁ : ℝ := 200 * D ^ 4 + 8 * B with hC₁
  set t : ℝ := Real.sqrt (Real.log (sc p)) with ht
  set q : ℝ := (8 * B) ^ 2 * Real.exp (-(3 * t)) with hq
  set ks : List (ZMod N → ℝ) := (List.range L).map (fun j => normK N (sc j) (wQ D (sc j))) with hks
  set F := Ftri N m with hF
  have hD0 : 0 < D := by linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hC0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have ht0 : 0 < t := by linarith
  have hscpos : ∀ j, (0 : ℝ) < sc j := fun j => by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (sc j))
  have hpL : p < L := by omega
  have hlen : ks.length = L := by simp [hks]
  have hF0 : F 0 = 1 := Ftri_zero m hm h2m
  have hFPD : PD F := Ftri_PD m
  have hgetD : ∀ j, j < L → ks.getD j (fun _ => 0) = normK N (sc j) (wQ D (sc j)) := by
    intro j hj
    rw [hks, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    simp
  have hgood : ∀ K ∈ ks, PD K ∧ (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 ∧ ∑ x, K x ≤ B := by
    intro K hK
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hK
    have hjL : j < L := List.mem_range.mp hj
    obtain ⟨h1, h2, h3⟩ := normK_props (N := N) D hD (sc j) (hQ j hjL) (hQN j hjL)
    exact ⟨h1, normK_nonneg _ _, h2, h3⟩
  have hsub : ∀ i, ∀ K ∈ ks.drop i, K ∈ ks := fun i K hK => List.mem_of_mem_drop hK
  set H' := Hs F (ks.drop (p + 1)) with hH'
  have hHPD : PD H' := Hs_PD F hFPD _ (fun K hK => (hgood K (hsub _ K hK)).1)
  have hH1 : 1 ≤ H' 0 := (Hs_atom F hFPD.nonneg (by rw [hF0]) (ks.drop (p + 1))
    (fun K hK => ⟨(hgood K (hsub _ K hK)).2.1, (hgood K (hsub _ K hK)).2.2.1⟩)).2
  have hHpos : 0 < H' 0 := lt_of_lt_of_le one_pos hH1
  -- the kernel at level `p`
  set K : ZMod N → ℝ := normK N (sc p) (wQ D (sc p)) with hKdef
  have hKnn : ∀ x, 0 ≤ K x := fun x => normK_nonneg _ _ _
  have hKB : ∑ x, K x ≤ B := sum_normK_le D hD (sc p) (hQ p hpL)
  have hKp : ks[p]'(by rw [hlen]; exact hpL) = K := by
    rw [← List.getD_eq_getElem ks (fun _ => 0) (by rw [hlen]; exact hpL)]
    exact hgetD p hpL
  have hdrop : ks.drop p = K :: ks.drop (p + 1) := by
    rw [List.drop_eq_getElem_cons (by rw [hlen]; exact hpL), hKp]
  -- the factor as a sum over the atoms
  have hf : Hs F (ks.drop p) 0 / H' 0 = ∑ d, K d * (H' (0 - d) / H' 0) := by
    rw [hdrop]
    show conv K H' 0 / H' 0 = _
    unfold conv
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    ring
  -- the far-separated bound
  have hfar := far_separated (N := N) D hD m hm h2m L sc hQ hQN hgrow p hp htop hε
  set R : ℝ := 512 * C₁ * (((sc p : ℝ) / sc (p + 1)) ^ 3 + 4 * q) with hR
  have hR0 : 0 ≤ R := by
    have := hscpos p; have := hscpos (p + 1)
    rw [hR]; positivity
  have hfar' : ∀ y, 1 / (sc p : ℝ) ≤ cn y → H' y / H' 0 ≤ R := fun y hy => hfar y hy
  -- the atoms
  set M : ℕ := ⌈t ^ 2⌉₊ with hM
  have hM2 : (4 : ℝ) ≤ M := by
    have : t ^ 2 ≤ M := Nat.le_ceil _
    nlinarith
  set v : ℝ := (M : ℝ) / sc p with hv
  have hvQ : v * sc p = M := by rw [hv]; field_simp [(hscpos p).ne']
  have hterm : ∀ d, K d * (H' (0 - d) / H' 0) ≤
      (if d = 0 then K d else 0) + (if v < cn d then K d else 0) + R * K d := by
    intro d
    have h1 : 0 ≤ (if d = 0 then K d else 0) := by split_ifs <;> simp [hKnn d]
    have h2 : 0 ≤ (if v < cn d then K d else 0) := by split_ifs <;> simp [hKnn d]
    have h3 : 0 ≤ R * K d := mul_nonneg hR0 (hKnn d)
    have hh1 : H' (0 - d) / H' 0 ≤ 1 := by
      rw [div_le_one hHpos]; exact PD.apply_le hHPD _
    have hh0 : 0 ≤ H' (0 - d) / H' 0 := div_nonneg (hHPD.nonneg _) hHpos.le
    by_cases hd0 : d = 0
    · subst hd0
      have : K 0 * (H' (0 - 0) / H' 0) ≤ K 0 := by
        rw [sub_zero, div_self hHpos.ne', mul_one]
      calc K 0 * (H' (0 - 0) / H' 0) ≤ K 0 := this
        _ = (if (0 : ZMod N) = 0 then K 0 else 0) := by simp
        _ ≤ _ := by linarith
    · by_cases hKd : K d = 0
      · rw [hKd, zero_mul]; simp [hd0, hKd]
      · have hcn : 1 / (sc p : ℝ) ≤ cn d := support_cn D (sc p) (hQN p hpL) d hd0 hKd
        by_cases hvd : v < cn d
        · have : K d * (H' (0 - d) / H' 0) ≤ K d := by nlinarith [hKnn d]
          rw [if_pos hvd, if_neg hd0]
          linarith
        · have hcn' : 1 / (sc p : ℝ) ≤ cn (0 - d) := by rw [zero_sub, cn_neg]; exact hcn
          have := hfar' _ hcn'
          have : K d * (H' (0 - d) / H' 0) ≤ K d * R := mul_le_mul_of_nonneg_left this (hKnn d)
          rw [if_neg hd0, if_neg hvd]
          linarith
  have hsum : ∑ d, K d * (H' (0 - d) / H' 0) ≤
      K 0 + ∑ d, (if v < cn d then K d else 0) + R * ∑ d, K d := by
    calc ∑ d, K d * (H' (0 - d) / H' 0)
        ≤ ∑ d, ((if d = 0 then K d else 0) + (if v < cn d then K d else 0) + R * K d) :=
          Finset.sum_le_sum (fun d _ => hterm d)
      _ = K 0 + ∑ d, (if v < cn d then K d else 0) + R * ∑ d, K d := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          simp
  have hK0 : K 0 = 1 := normK_zero_eq D (sc p) (hQN p hpL)
  -- the tail beyond `M / Q`
  have htail : ∑ d, (if v < cn d then K d else 0) ≤ 200 * D ^ 4 / t ^ 6 := by
    have h := kernel_tail_le' (N := N) D hD (sc p) (hQ p hpL) (hQN p hpL) v (by rw [hvQ]; linarith)
    rw [hvQ] at h
    refine h.trans ?_
    have hM3 : t ^ 6 ≤ (M : ℝ) ^ 3 := by
      have : t ^ 2 ≤ M := Nat.le_ceil _
      calc t ^ 6 = (t ^ 2) ^ 3 := by ring
        _ ≤ (M : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hM3
  -- the ratio
  have hr0 : ((sc p : ℝ) / sc (p + 1)) ^ 3 ≤ (1 / t) ^ 3 := by
    have hpos1 := hscpos p
    have hpos2 := hscpos (p + 1)
    have h : (sc p : ℝ) / sc (p + 1) ≤ 1 / t := by
      rw [div_le_div_iff₀ hpos2 ht0]; linarith
    exact pow_le_pow_left₀ (by positivity) h 3
  have hRle : R ≤ 512 * C₁ * ((1 / t) ^ 3 + 4 * q) := by
    rw [hR]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  rw [hf]
  calc ∑ d, K d * (H' (0 - d) / H' 0) - 1
      ≤ K 0 + ∑ d, (if v < cn d then K d else 0) + R * ∑ d, K d - 1 := by linarith
    _ ≤ 200 * D ^ 4 / t ^ 6 + B * R := by
        rw [hK0]
        have : R * ∑ d, K d ≤ R * B := mul_le_mul_of_nonneg_left hKB hR0
        nlinarith
    _ ≤ 200 * D ^ 4 / t ^ 6 + B * (512 * C₁ * ((1 / t) ^ 3 + 4 * q)) := by
        have := mul_le_mul_of_nonneg_left hRle hB0
        linarith

#print axioms normK_zero_eq
#print axioms support_cn
#print axioms separated_factor

end JASep
end LeanCheck
