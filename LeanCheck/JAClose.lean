import Mathlib
import LeanCheck.JASep

/-!
# The central bound, step 6b: close levels and the two-term separation

For a close pair of levels (`Q_{p+1} < t_p Q_p`), the paper expands the factor `f_p` one convolution further:
`f_p - 1 ≤ A_D M^{-3} + B A_D N^{-3} + B^2 Φ(u)`, where the atoms of the two kernels with `0 < |r| ≤ M`, `|s| ≤ N` satisfy the
two-term separation `‖r/Q_p + s/Q_{p+1}‖ ≥ u` (Matveev), and `Φ(u)` bounds the normalized tail after the pair at circle norm `≥ u`.

Checked here (no axiom, no `sorry`): `atom_of_support`, `cn_atom_balanced`, `cn_add_atoms`, `far_beyond` (the far-field estimate for the
tail after TWO levels, for arbitrary `u > 0`), `close_factor` (the estimate of `f_p - 1`, with the two-term separation as a hypothesis
`hTT`), and the statement `TwoTermSeparation A` of the external input, with the easy cases proved (`two_term_easy`).
-/

namespace LeanCheck
namespace JAClose

open Finset JATransfer JAMulti JAProduct JAProduct2 JACenter JAFar JAKernTail JAFarSep JASep JAWindowQ MixedPrime

variable {N : ℕ} [NeZero N]

/-- A point of the support of the kernel is an atom `a_r = r · (N/Q)`. -/
lemma atom_of_support (D : ℝ) (Q : ℕ) [NeZero Q] (hQN : Q ∣ N) (d : ZMod N)
    (hK : normK N Q (wQ D Q) d ≠ 0) : ∃ r : ZMod Q, d = ((r.val * (N / Q) : ℕ) : ZMod N) := by
  classical
  obtain ⟨e, hd⟩ := hQN
  have hQpos : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hNd : N / Q = e := by rw [hd]; exact Nat.mul_div_cancel_left e hQpos
  unfold normK kernq kern at hK
  have hsum : (∑ r : ZMod Q, if d = ((r.val * (N / Q) : ℕ) : ZMod N) then
      ‖∑ x, ((wQ D Q x : ℝ) : ℂ) * ZMod.stdAddChar (r * x)‖ ^ 2 else 0) ≠ 0 := by
    intro h0; apply hK; rw [h0, mul_zero]
  obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨r, ?_⟩
  by_contra h; exact hr (by rw [if_neg h])

lemma val_div_eq (Q : ℕ) [NeZero Q] (r : ZMod Q) :
    ∃ k : ℤ, (r.val : ℝ) / Q = (r.valMinAbs : ℝ) / Q + (k : ℝ) := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hcong : (Q : ℤ) ∣ (r.val : ℤ) - r.valMinAbs :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub r.valMinAbs (r.val : ℤ) Q).mp
      (by rw [ZMod.coe_valMinAbs, Int.cast_natCast, ZMod.natCast_zmod_val])
  obtain ⟨k, hk⟩ := hcong
  refine ⟨k, ?_⟩
  have h1 : (r.val : ℤ) = r.valMinAbs + Q * k := by linarith
  have h2 : (r.val : ℝ) = r.valMinAbs + Q * k := by exact_mod_cast h1
  rw [h2]; field_simp

/-- The circle norm of the atom `a_r` is `|r̃|/Q`. -/
lemma cn_atom_balanced (Q : ℕ) [NeZero Q] (hQN : Q ∣ N) (r : ZMod Q) :
    cn (((r.val * (N / Q) : ℕ) : ZMod N)) = |(r.valMinAbs : ℝ)| / Q := by
  obtain ⟨e, hd⟩ := hQN
  have hQpos : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exfalso; rw [h, mul_zero] at hd; exact NeZero.ne N hd
    · exact h
  have hNd : N / Q = e := by rw [hd]; exact Nat.mul_div_cancel_left e hQpos
  rw [hNd, cn_atom (N := N) Q e hepos hd, nrm_val_eq]

/-- The circle norm of a sum of two atoms: `‖r̃/Q + s̃/Q'‖`. -/
lemma cn_add_atoms (Q Q' : ℕ) [NeZero Q] [NeZero Q'] (hQN : Q ∣ N) (hQN' : Q' ∣ N) (r : ZMod Q)
    (s : ZMod Q') :
    cn (((r.val * (N / Q) : ℕ) : ZMod N) + ((s.val * (N / Q') : ℕ) : ZMod N)) =
      nrm ((r.valMinAbs : ℝ) / Q + (s.valMinAbs : ℝ) / Q') := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hQ' : (0 : ℝ) < Q' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q')
  obtain ⟨e, hd⟩ := hQN
  obtain ⟨e', hd'⟩ := hQN'
  have hQpos : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have hQpos' : 0 < Q' := Nat.pos_of_ne_zero (NeZero.ne Q')
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exfalso; rw [h, mul_zero] at hd; exact NeZero.ne N hd
    · exact h
  have hepos' : 0 < e' := by
    rcases Nat.eq_zero_or_pos e' with h | h
    · exfalso; rw [h, mul_zero] at hd'; exact NeZero.ne N hd'
    · exact h
  have hNd : N / Q = e := by rw [hd]; exact Nat.mul_div_cancel_left e hQpos
  have hNd' : N / Q' = e' := by rw [hd']; exact Nat.mul_div_cancel_left e' hQpos'
  obtain ⟨k, hk⟩ := val_div_eq Q r
  obtain ⟨k', hk'⟩ := val_div_eq Q' s
  have e1 : (((r.val * e : ℕ) : ℝ) / N) = (r.val : ℝ) / Q := by
    rw [hd]; push_cast; field_simp
  have e2 : (((s.val * e' : ℕ) : ℝ) / N) = (s.val : ℝ) / Q' := by
    rw [hd']; push_cast; field_simp
  rw [hNd, hNd']
  unfold cn
  rw [map_add, ZMod.toAddCircle_natCast, ZMod.toAddCircle_natCast, e1, e2, ← AddCircle.coe_add]
  show nrm _ = _
  rw [hk, hk']
  have : (r.valMinAbs : ℝ) / Q + (k : ℝ) + ((s.valMinAbs : ℝ) / Q' + (k' : ℝ)) =
      ((r.valMinAbs : ℝ) / Q + (s.valMinAbs : ℝ) / Q') + ((k + k' : ℤ) : ℝ) := by push_cast; ring
  rw [this, nrm_add_int]

/-- **Far field after two levels**, for an arbitrary radius `u > 0`: all later scales are at least `Q_p e^{t_p}`, so no special
first term is needed. -/
theorem far_beyond (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (sc : ℕ → ℕ) [hsc : ∀ j, NeZero (sc j)]
    (hQ : ∀ j, j < L → 25 * D ≤ sc j) (hQN : ∀ j, j < L → sc j ∣ N)
    (hgrow : ∀ p k, p + k < L → (sc p : ℝ) * Real.exp (Real.sqrt (Real.log (sc p)) * ((k / 2 : ℕ) : ℝ)) ≤
      sc (p + k))
    (p : ℕ) (hp : p + 2 ≤ L)
    (htop : (8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))) ≤ 1 / 2)
    (u : ℝ) (hu : 0 < u) (hε : (2 * m : ℝ) / N ≤ 3 * u / 4) (y : ZMod N) (hy : u ≤ cn y) :
    Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 2)) y /
        Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 2)) 0 ≤
      2048 * (200 * D ^ 4 + 8 * (30 * D / 7)) * (1 / (u * sc p)) ^ 3 *
        ((8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (Real.log (sc p))))) := by
  classical
  set B : ℝ := 30 * D / 7 with hBdef
  set C₁ : ℝ := 200 * D ^ 4 + 8 * B with hC₁
  set t : ℝ := Real.sqrt (Real.log (sc p)) with ht
  set q : ℝ := (8 * B) ^ 2 * Real.exp (-(3 * t)) with hq
  set ks : List (ZMod N → ℝ) := (List.range L).map (fun j => normK N (sc j) (wQ D (sc j))) with hks
  have hD0 : 0 < D := by linarith
  have hB1 : 1 ≤ 8 * B := by rw [hBdef]; linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hq2 : q ≤ 1 / 2 := htop
  have hlen : ks.length = L := by simp [hks]
  have hscpos : ∀ j, (0 : ℝ) < sc j := fun j => by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (sc j))
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
  have key := far_field_ZN m hm h2m ks B hB0 hgood u hu.le hε (L - (p + 2)) (p + 2) (by omega) y hy
  refine key.trans ?_
  set W : ℝ := (1 / (u * sc p)) ^ 3 with hW
  have hW0 : 0 ≤ W := by have := hscpos p; positivity
  have hterm : ∀ j, j < L - (p + 2) →
      B ^ j * ∑ d : ZMod N, (if u / 2 ^ (j + 3) < cn d then ks.getD (p + 2 + j) (fun _ => 0) d else 0)
        ≤ 512 * C₁ * W * q ^ (j / 2 + 1) := by
    intro j hj
    have hjL : p + 2 + j < L := by omega
    rw [hgetD _ hjL]
    have hv : 0 < u / 2 ^ (j + 3) := by positivity
    have htail := kernel_tail_all (N := N) D hD (sc (p + 2 + j)) (hQ _ hjL) (hQN _ hjL) _ hv
    have hv' : u / 2 ^ (j + 3) = 1 / (1 / u) / 2 ^ (j + 3) := by rw [one_div_one_div]
    rw [hv'] at htail ⊢
    have hu' : (0 : ℝ) < 1 / u := by positivity
    have halg := term_algebra B C₁ (1 / u) (sc (p + 2 + j)) j hu' (hscpos _)
    have hb : B ^ j * ∑ d : ZMod N, (if 1 / (1 / u) / 2 ^ (j + 3) < cn d then
          normK N (sc (p + 2 + j)) (wQ D (sc (p + 2 + j))) d else 0) ≤
        512 * C₁ * ((8 * B) ^ j * ((1 / u) / sc (p + 2 + j)) ^ 3) := by
      rw [← halg]
      exact mul_le_mul_of_nonneg_left htail (pow_nonneg hB0 j)
    refine hb.trans ?_
    -- the ratio
    have hlt : p + (j + 2) < L := by omega
    have hg := hgrow p (j + 2) hlt
    have hc : ((j + 2) / 2 : ℕ) = j / 2 + 1 := by omega
    rw [hc] at hg
    have hratio := ratio_cube (sc p) (sc (p + (j + 2))) (t * ((j / 2 + 1 : ℕ) : ℝ)) (hscpos p) (hscpos _) hg
    have e : p + 2 + j = p + (j + 2) := by ring
    rw [e]
    have hl : Real.exp (-(3 * (t * ((j / 2 + 1 : ℕ) : ℝ)))) = Real.exp (-(3 * t)) ^ (j / 2 + 1) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hl] at hratio
    have hpow : (8 * B) ^ j ≤ (8 * B) ^ (2 * (j / 2 + 1)) := pow_le_pow_right₀ hB1 (by omega)
    have hsplit : ((1 / u) / (sc (p + (j + 2)) : ℝ)) ^ 3 = W * ((sc p : ℝ) / sc (p + (j + 2))) ^ 3 := by
      rw [hW, ← mul_pow]
      congr 1
      have := hscpos p
      field_simp
    rw [hsplit]
    have hqpow : q ^ (j / 2 + 1) = (8 * B) ^ (2 * (j / 2 + 1)) * Real.exp (-(3 * t)) ^ (j / 2 + 1) := by
      rw [hq, mul_pow, ← pow_mul]
    have hprod : (8 * B) ^ j * ((sc p : ℝ) / sc (p + (j + 2))) ^ 3 ≤ q ^ (j / 2 + 1) := by
      rw [hqpow]
      exact mul_le_mul hpow hratio (by positivity) (by positivity)
    have h512 : (0 : ℝ) ≤ 512 * C₁ := by rw [hC₁]; positivity
    calc 512 * C₁ * ((8 * B) ^ j * (W * ((sc p : ℝ) / sc (p + (j + 2))) ^ 3))
        = 512 * C₁ * W * ((8 * B) ^ j * ((sc p : ℝ) / sc (p + (j + 2))) ^ 3) := by ring
      _ ≤ 512 * C₁ * W * q ^ (j / 2 + 1) :=
          mul_le_mul_of_nonneg_left hprod (mul_nonneg h512 hW0)
  have hsum1 : ∑ j ∈ range (L - (p + 2)), B ^ j *
        ∑ d : ZMod N, (if u / 2 ^ (j + 3) < cn d then ks.getD (p + 2 + j) (fun _ => 0) d else 0)
      ≤ ∑ j ∈ range (L - (p + 2)), 512 * C₁ * W * q ^ (j / 2 + 1) :=
    Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range.mp hj))
  refine hsum1.trans ?_
  have hpair := pair_geom q hq0 hq2 (L - (p + 2))
  have hC0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  calc ∑ j ∈ range (L - (p + 2)), 512 * C₁ * W * q ^ (j / 2 + 1)
      = 512 * C₁ * W * (q * ∑ j ∈ range (L - (p + 2)), q ^ (j / 2)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ ≤ 512 * C₁ * W * (q * 4) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpair hq0) (by positivity)
    _ = 2048 * C₁ * W * q := by ring

#print axioms atom_of_support
#print axioms cn_atom_balanced
#print axioms cn_add_atoms
#print axioms far_beyond

set_option maxHeartbeats 1600000 in
/-- **(close-factor)**: the estimate of `f_p - 1` for a close pair of levels, given the two-term separation `hTT` for the
atoms `0 < |r| ≤ ⌈t^2⌉`, `|s| ≤ ⌈4 t^3⌉` of the two kernels. -/
theorem close_factor (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (sc : ℕ → ℕ) [hsc : ∀ j, NeZero (sc j)]
    (hQ : ∀ j, j < L → 25 * D ≤ sc j) (hQN : ∀ j, j < L → sc j ∣ N)
    (hgrow : ∀ p k, p + k < L → (sc p : ℝ) * Real.exp (Real.sqrt (Real.log (sc p)) * ((k / 2 : ℕ) : ℝ)) ≤
      sc (p + k))
    (p : ℕ) (hp : p + 2 ≤ L)
    (htop : (8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))) ≤ 1 / 2)
    (ht2 : 2 ≤ Real.sqrt (Real.log (sc p))) (a : ℝ → ℝ)
    (hε : (2 * m : ℝ) / N ≤
      3 * (Real.exp (-(a (Real.sqrt (Real.log (sc p))))) / sc p) / 4)
    (hTT : ∀ r s : ℤ, r ≠ 0 → |r| ≤ (⌈(Real.sqrt (Real.log (sc p))) ^ 2⌉₊ : ℤ) →
      |s| ≤ (⌈4 * (Real.sqrt (Real.log (sc p))) ^ 3⌉₊ : ℤ) →
      Real.exp (-(a (Real.sqrt (Real.log (sc p))))) / sc p ≤
        nrm ((r : ℝ) / sc p + (s : ℝ) / sc (p + 1))) :
    Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop p) 0 /
        Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 1)) 0 - 1 ≤
      200 * D ^ 4 / (Real.sqrt (Real.log (sc p))) ^ 6 +
        30 * D / 7 * (200 * D ^ 4 / (4 * (Real.sqrt (Real.log (sc p))) ^ 3) ^ 3) +
        (30 * D / 7) ^ 2 * (2048 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
          (1 / (Real.exp (-(a (Real.sqrt (Real.log (sc p))))) / sc p * sc p)) ^ 3 *
          ((8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))))) := by
  classical
  set B : ℝ := 30 * D / 7 with hBdef
  set C₁ : ℝ := 200 * D ^ 4 + 8 * B with hC₁
  set t : ℝ := Real.sqrt (Real.log (sc p)) with ht
  set q : ℝ := (8 * B) ^ 2 * Real.exp (-(3 * t)) with hq
  set u : ℝ := Real.exp (-(a t)) / sc p with hu
  set ks : List (ZMod N → ℝ) := (List.range L).map (fun j => normK N (sc j) (wQ D (sc j))) with hks
  set F := Ftri N m with hF
  have hD0 : 0 < D := by linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hC0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have ht0 : 0 < t := by linarith
  have hscpos : ∀ j, (0 : ℝ) < sc j := fun j => by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (sc j))
  have hpL : p < L := by omega
  have hp1L : p + 1 < L := by omega
  have hupos : 0 < u := by rw [hu]; have := hscpos p; positivity
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
  have hHPD : ∀ i, PD (Hs F (ks.drop i)) := fun i =>
    Hs_PD F hFPD _ (fun K hK => (hgood K (hsub _ K hK)).1)
  have hH1 : ∀ i, 1 ≤ Hs F (ks.drop i) 0 := fun i =>
    (Hs_atom F hFPD.nonneg (by rw [hF0]) (ks.drop i)
      (fun K hK => ⟨(hgood K (hsub _ K hK)).2.1, (hgood K (hsub _ K hK)).2.2.1⟩)).2
  have hHpos : ∀ i, 0 < Hs F (ks.drop i) 0 := fun i => lt_of_lt_of_le one_pos (hH1 i)
  set H1 := Hs F (ks.drop (p + 1)) with hH1def
  set H2 := Hs F (ks.drop (p + 2)) with hH2def
  set K0 : ZMod N → ℝ := normK N (sc p) (wQ D (sc p)) with hK0def
  set K1 : ZMod N → ℝ := normK N (sc (p + 1)) (wQ D (sc (p + 1))) with hK1def
  have hK0nn : ∀ x, 0 ≤ K0 x := fun x => normK_nonneg _ _ _
  have hK1nn : ∀ x, 0 ≤ K1 x := fun x => normK_nonneg _ _ _
  have hK0B : ∑ x, K0 x ≤ B := sum_normK_le D hD (sc p) (hQ p hpL)
  have hK1B : ∑ x, K1 x ≤ B := sum_normK_le D hD (sc (p + 1)) (hQ (p + 1) hp1L)
  have hdrop0 : ks.drop p = K0 :: ks.drop (p + 1) := by
    have hlt : p < ks.length := by rw [hlen]; exact hpL
    rw [List.drop_eq_getElem_cons hlt, ← List.getD_eq_getElem ks (fun _ => 0) hlt, hgetD p hpL]
  have hdrop1 : ks.drop (p + 1) = K1 :: ks.drop (p + 2) := by
    have hlt : p + 1 < ks.length := by rw [hlen]; exact hp1L
    rw [List.drop_eq_getElem_cons hlt, ← List.getD_eq_getElem ks (fun _ => 0) hlt, hgetD (p + 1) hp1L]
  have hH1eq : H1 = conv K1 H2 := by
    rw [hH1def, hdrop1]; rfl
  have hf : Hs F (ks.drop p) 0 / H1 0 = ∑ d, K0 d * (H1 (0 - d) / H1 0) := by
    rw [hdrop0]
    show conv K0 H1 0 / H1 0 = _
    unfold conv
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hHPD2 : PD H2 := hHPD (p + 2)
  have hH2pos : 0 < H2 0 := hHpos (p + 2)
  have hH1pos : 0 < H1 0 := hHpos (p + 1)
  have hratio : H2 0 ≤ H1 0 := by
    have := (factor_bounds K1 H2 hK1nn (hgood K1 (by rw [hks]; exact List.mem_map.mpr ⟨p + 1,
      List.mem_range.mpr hp1L, rfl⟩)).2.2.1 B hK1B hHPD2 hH2pos).1
    rw [hH1eq]
    rw [le_div_iff₀ hH2pos] at this
    linarith
  -- one more convolution
  have hh1 : ∀ y, H1 y / H1 0 ≤ ∑ e, K1 e * (H2 (y - e) / H2 0) := by
    intro y
    rw [hH1eq]
    show conv K1 H2 y / conv K1 H2 0 ≤ _
    have hnum : 0 ≤ conv K1 H2 y := JAFinal.conv_nonneg' _ _ hK1nn hHPD2.nonneg y
    have hden : H2 0 ≤ conv K1 H2 0 := by rw [← hH1eq]; exact hratio
    calc conv K1 H2 y / conv K1 H2 0 ≤ conv K1 H2 y / H2 0 :=
          div_le_div_of_nonneg_left hnum hH2pos hden
      _ = ∑ e, K1 e * (H2 (y - e) / H2 0) := by
          unfold conv
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro e _
          ring
  -- far field after the pair
  have hfar := far_beyond (N := N) D hD m hm h2m L sc hQ hQN hgrow p hp htop u hupos hε
  set Φ : ℝ := 2048 * C₁ * (1 / (u * sc p)) ^ 3 * q with hΦ
  have hΦ0 : 0 ≤ Φ := by
    have := hscpos p
    rw [hΦ]; positivity
  have hfarΦ : ∀ y, u ≤ cn y → H2 y / H2 0 ≤ Φ := fun y hy => hfar y hy
  -- radii
  set M : ℕ := ⌈t ^ 2⌉₊ with hM
  set Nn : ℕ := ⌈4 * t ^ 3⌉₊ with hNn
  have hM2 : (4 : ℝ) ≤ M := by
    have : t ^ 2 ≤ M := Nat.le_ceil _
    nlinarith
  have hNn2 : (4 * t ^ 3 : ℝ) ≤ Nn := Nat.le_ceil _
  have hNn32 : (2 : ℝ) ≤ Nn := by nlinarith [pow_pos ht0 3, pow_pos ht0 2]
  set v : ℝ := (M : ℝ) / sc p with hv
  set v' : ℝ := (Nn : ℝ) / sc (p + 1) with hv'
  have hvQ : v * sc p = M := by rw [hv]; field_simp [(hscpos p).ne']
  have hvQ' : v' * sc (p + 1) = Nn := by rw [hv']; field_simp [(hscpos (p + 1)).ne']
  set T' : ℝ := ∑ e, (if v' < cn e then K1 e else 0) with hT'
  have hT'0 : 0 ≤ T' := Finset.sum_nonneg (fun e _ => by split_ifs <;> simp [hK1nn e])
  have hT'le : T' ≤ 200 * D ^ 4 / (4 * t ^ 3) ^ 3 := by
    have h := kernel_tail_le' (N := N) D hD (sc (p + 1)) (hQ (p + 1) hp1L) (hQN (p + 1) hp1L) v'
      (by rw [hvQ']; exact hNn32)
    rw [hvQ'] at h
    refine h.trans ?_
    have hN3 : (4 * t ^ 3) ^ 3 ≤ (Nn : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hNn2 3
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hN3
  -- inner estimate
  have hinner : ∀ d, d ≠ 0 → K0 d ≠ 0 → cn d ≤ v →
      ∑ e, K1 e * (H2 ((0 - d) - e) / H2 0) ≤ T' + B * Φ := by
    intro d hd0 hKd hcnd
    calc ∑ e, K1 e * (H2 ((0 - d) - e) / H2 0)
        ≤ ∑ e, ((if v' < cn e then K1 e else 0) + K1 e * Φ) := by
          apply Finset.sum_le_sum
          intro e _
          have hh1' : H2 ((0 - d) - e) / H2 0 ≤ 1 := by
            rw [div_le_one hH2pos]; exact PD.apply_le hHPD2 _
          have hh0 : 0 ≤ H2 ((0 - d) - e) / H2 0 := div_nonneg (hHPD2.nonneg _) hH2pos.le
          have h2 : 0 ≤ (if v' < cn e then K1 e else 0) := by split_ifs <;> simp [hK1nn e]
          have h3 : 0 ≤ K1 e * Φ := mul_nonneg (hK1nn e) hΦ0
          by_cases hKe : K1 e = 0
          · rw [hKe, zero_mul]; simp [hKe]
          · by_cases hve : v' < cn e
            · have : K1 e * (H2 ((0 - d) - e) / H2 0) ≤ K1 e := by
                have := mul_le_mul_of_nonneg_left hh1' (hK1nn e)
                rwa [mul_one] at this
              rw [if_pos hve]; linarith
            · -- both atoms are retained: the two-term separation
              obtain ⟨r, hr⟩ := atom_of_support D (sc p) (hQN p hpL) d hKd
              obtain ⟨s, hs⟩ := atom_of_support D (sc (p + 1)) (hQN (p + 1) hp1L) e hKe
              have hr0 : r ≠ 0 := by
                intro h; apply hd0; rw [hr, h]; simp
              have hrm : r.valMinAbs ≠ 0 := fun h => hr0 ((ZMod.valMinAbs_eq_zero r).mp h)
              have hcr : cn d = |(r.valMinAbs : ℝ)| / sc p := by rw [hr]; exact cn_atom_balanced _ (hQN p hpL) r
              have hcs : cn e = |(s.valMinAbs : ℝ)| / sc (p + 1) := by
                rw [hs]; exact cn_atom_balanced _ (hQN (p + 1) hp1L) s
              have hrM : |r.valMinAbs| ≤ (M : ℤ) := by
                have h1 : |(r.valMinAbs : ℝ)| ≤ M := by
                  have := hcnd; rw [hcr, hv, div_le_div_iff_of_pos_right (hscpos p)] at this; exact this
                have h2 : ((|r.valMinAbs| : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by
                  rw [Int.cast_abs]; push_cast; exact h1
                exact_mod_cast h2
              have hsN : |s.valMinAbs| ≤ (Nn : ℤ) := by
                have hve' : cn e ≤ v' := not_lt.mp hve
                have h1 : |(s.valMinAbs : ℝ)| ≤ Nn := by
                  rw [hcs, hv', div_le_div_iff_of_pos_right (hscpos (p + 1))] at hve'; exact hve'
                have h2 : ((|s.valMinAbs| : ℤ) : ℝ) ≤ ((Nn : ℤ) : ℝ) := by
                  rw [Int.cast_abs]; push_cast; exact h1
                exact_mod_cast h2
              have hsep := hTT r.valMinAbs s.valMinAbs hrm hrM hsN
              have hcn : u ≤ cn ((0 - d) - e) := by
                have : (0 - d) - e = -(d + e) := by ring
                rw [this, cn_neg, hr, hs, cn_add_atoms (sc p) (sc (p + 1)) (hQN p hpL) (hQN (p + 1) hp1L)]
                exact hsep
              have := hfarΦ _ hcn
              have : K1 e * (H2 ((0 - d) - e) / H2 0) ≤ K1 e * Φ :=
                mul_le_mul_of_nonneg_left this (hK1nn e)
              rw [if_neg hve]; linarith
      _ = T' + Φ * ∑ e, K1 e := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← hT']; ring
      _ ≤ T' + B * Φ := by
          have := mul_le_mul_of_nonneg_left hK1B hΦ0
          linarith
  -- the sum over the first kernel
  have hterm : ∀ d, K0 d * (H1 (0 - d) / H1 0) ≤
      (if d = 0 then K0 d else 0) + (if v < cn d then K0 d else 0) + K0 d * (T' + B * Φ) := by
    intro d
    have h1 : 0 ≤ (if d = 0 then K0 d else 0) := by split_ifs <;> simp [hK0nn d]
    have h2 : 0 ≤ (if v < cn d then K0 d else 0) := by split_ifs <;> simp [hK0nn d]
    have hTB : 0 ≤ T' + B * Φ := by positivity
    have h3 : 0 ≤ K0 d * (T' + B * Φ) := mul_nonneg (hK0nn d) hTB
    have hh1' : H1 (0 - d) / H1 0 ≤ 1 := by
      rw [div_le_one hH1pos]; exact PD.apply_le (hHPD (p + 1)) _
    by_cases hd0 : d = 0
    · subst hd0
      have : K0 0 * (H1 (0 - 0) / H1 0) ≤ K0 0 := by
        rw [sub_zero, div_self hH1pos.ne', mul_one]
      calc K0 0 * (H1 (0 - 0) / H1 0) ≤ K0 0 := this
        _ = (if (0 : ZMod N) = 0 then K0 0 else 0) := by simp
        _ ≤ _ := by linarith
    · by_cases hKd : K0 d = 0
      · rw [hKd, zero_mul]; simp [hd0, hKd]
      · by_cases hvd : v < cn d
        · have : K0 d * (H1 (0 - d) / H1 0) ≤ K0 d := by
            have := mul_le_mul_of_nonneg_left hh1' (hK0nn d)
            rwa [mul_one] at this
          rw [if_pos hvd, if_neg hd0]; linarith
        · have hcnd : cn d ≤ v := not_lt.mp hvd
          have hin := hinner d hd0 hKd hcnd
          have := hh1 (0 - d)
          have : K0 d * (H1 (0 - d) / H1 0) ≤ K0 d * (T' + B * Φ) :=
            mul_le_mul_of_nonneg_left (this.trans hin) (hK0nn d)
          rw [if_neg hd0, if_neg hvd]; linarith
  have hsum : ∑ d, K0 d * (H1 (0 - d) / H1 0) ≤
      K0 0 + ∑ d, (if v < cn d then K0 d else 0) + (T' + B * Φ) * ∑ d, K0 d := by
    calc ∑ d, K0 d * (H1 (0 - d) / H1 0)
        ≤ ∑ d, ((if d = 0 then K0 d else 0) + (if v < cn d then K0 d else 0) + K0 d * (T' + B * Φ)) :=
          Finset.sum_le_sum (fun d _ => hterm d)
      _ = K0 0 + ∑ d, (if v < cn d then K0 d else 0) + (T' + B * Φ) * ∑ d, K0 d := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
          simp [mul_comm]
  have hK00 : K0 0 = 1 := normK_zero_eq D (sc p) (hQN p hpL)
  have htail : ∑ d, (if v < cn d then K0 d else 0) ≤ 200 * D ^ 4 / t ^ 6 := by
    have h := kernel_tail_le' (N := N) D hD (sc p) (hQ p hpL) (hQN p hpL) v (by rw [hvQ]; linarith)
    rw [hvQ] at h
    refine h.trans ?_
    have hM3 : t ^ 6 ≤ (M : ℝ) ^ 3 := by
      have : t ^ 2 ≤ M := Nat.le_ceil _
      calc t ^ 6 = (t ^ 2) ^ 3 := by ring
        _ ≤ (M : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hM3
  rw [hf]
  have hTB : 0 ≤ T' + B * Φ := by positivity
  calc ∑ d, K0 d * (H1 (0 - d) / H1 0) - 1
      ≤ K0 0 + ∑ d, (if v < cn d then K0 d else 0) + (T' + B * Φ) * ∑ d, K0 d - 1 := by linarith
    _ ≤ 200 * D ^ 4 / t ^ 6 + B * (T' + B * Φ) := by
        rw [hK00]
        have : (T' + B * Φ) * ∑ d, K0 d ≤ (T' + B * Φ) * B := mul_le_mul_of_nonneg_left hK0B hTB
        nlinarith
    _ ≤ 200 * D ^ 4 / t ^ 6 + B * (200 * D ^ 4 / (4 * t ^ 3) ^ 3) + B ^ 2 * Φ := by
        have := mul_le_mul_of_nonneg_left hT'le hB0
        nlinarith

#print axioms close_factor

/-! ### The external input: the two-term separation (Matveev) -/

/-- **The two-term separation (hypothesis; Matveev, Cor. 2.3 as used in the paper).**  For prime-square periods
`Q = b^{n^2}`, `Q' = b'^{n'^2}` of the two different primes `2, 3`, with `Q < Q' < t Q` (`t = sqrt (log Q)`, a close pair) and
`Q` large, for integers `0 < |r| ≤ ⌈t^2⌉`, `|s| ≤ ⌈4 t^3⌉` of opposite signs,
`‖r/Q + s/Q'‖ ≥ Q^{-1} exp(-A log^2(2+t))`. -/
def TwoTermSep (a : ℝ → ℝ) : Prop :=
  ∃ T₀ : ℝ, ∀ (b n b' n' : ℕ) (r s : ℤ), ((b = 2 ∧ b' = 3) ∨ (b = 3 ∧ b' = 2)) → 1 ≤ n → 1 ≤ n' →
    T₀ ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) →
    b ^ (n ^ 2) < b' ^ (n' ^ 2) →
    ((b' ^ (n' ^ 2) : ℕ) : ℝ) < Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) * ((b ^ (n ^ 2) : ℕ) : ℝ) →
    r ≠ 0 → |r| ≤ (⌈(Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 2⌉₊ : ℤ) →
    |s| ≤ (⌈4 * (Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 3⌉₊ : ℤ) → r * s < 0 →
    Real.exp (-(a (Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))))) / ((b ^ (n ^ 2) : ℕ) : ℝ) ≤
      nrm ((r : ℝ) / ((b ^ (n ^ 2) : ℕ) : ℝ) + (s : ℝ) / ((b' ^ (n' ^ 2) : ℕ) : ℝ))

/-- The original form of the hypothesis: the separation profile `a(t) = A log^2(2+t)`. -/
def TwoTermSeparation (A : ℝ) : Prop := TwoTermSep (fun t => A * (Real.log (2 + t)) ^ 2)

/-- The easy cases (`s = 0` or the same sign): no Diophantine input is needed. -/
lemma two_term_easy (Q Q' : ℝ) (hQ : 0 < Q) (hQQ : Q ≤ Q') (M Nn : ℝ) (hMN : 2 * (M + Nn) ≤ Q)
    (r s : ℤ) (hr0 : r ≠ 0) (hrM : |(r : ℝ)| ≤ M) (hsN : |(s : ℝ)| ≤ Nn) (hrs : 0 ≤ r * s) :
    1 / Q ≤ nrm ((r : ℝ) / Q + (s : ℝ) / Q') := by
  have hQ' : 0 < Q' := lt_of_lt_of_le hQ hQQ
  have hr1 : (1 : ℝ) ≤ |(r : ℝ)| := by
    have : (1 : ℤ) ≤ |r| := Int.one_le_abs hr0
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|r| : ℤ) : ℝ) := by exact_mod_cast this
    rw [Int.cast_abs] at h2; simpa using h2
  have hsign : (0 ≤ (r : ℝ) / Q ∧ 0 ≤ (s : ℝ) / Q') ∨ ((r : ℝ) / Q ≤ 0 ∧ (s : ℝ) / Q' ≤ 0) := by
    rcases lt_or_gt_of_ne hr0 with h | h
    · right
      refine ⟨div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h.le) hQ.le, ?_⟩
      have hs : s ≤ 0 := by
        by_contra hs; push Not at hs
        have : r * s < 0 := mul_neg_of_neg_of_pos h hs
        omega
      exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hs) hQ'.le
    · left
      refine ⟨div_nonneg (by exact_mod_cast h.le) hQ.le, ?_⟩
      have hs : 0 ≤ s := by
        by_contra hs; push Not at hs
        have : r * s < 0 := mul_neg_of_pos_of_neg h hs
        omega
      exact div_nonneg (by exact_mod_cast hs) hQ'.le
  have habs : |(r : ℝ) / Q + (s : ℝ) / Q'| = |(r : ℝ) / Q| + |(s : ℝ) / Q'| :=
    (abs_add_eq_add_abs_iff _ _).mpr hsign
  have hr' : |(r : ℝ) / Q| = |(r : ℝ)| / Q := by rw [abs_div, abs_of_pos hQ]
  have hs' : |(s : ℝ) / Q'| = |(s : ℝ)| / Q' := by rw [abs_div, abs_of_pos hQ']
  have hs'' : |(s : ℝ)| / Q' ≤ Nn / Q := by
    calc |(s : ℝ)| / Q' ≤ Nn / Q' := div_le_div_of_nonneg_right hsN hQ'.le
      _ ≤ Nn / Q := by
          have hNn : 0 ≤ Nn := le_trans (abs_nonneg _) hsN
          exact div_le_div_of_nonneg_left hNn hQ hQQ
  have hhalf : |(r : ℝ) / Q + (s : ℝ) / Q'| ≤ 1 / 2 := by
    rw [habs, hr', hs']
    have h1 : |(r : ℝ)| / Q ≤ M / Q := div_le_div_of_nonneg_right hrM hQ.le
    have h2 : M / Q + Nn / Q ≤ 1 / 2 := by
      rw [← add_div, div_le_iff₀ hQ]; linarith
    linarith
  rw [nrm_eq_abs hhalf, habs, hr', hs']
  have : 1 / Q ≤ |(r : ℝ)| / Q := div_le_div_of_nonneg_right hr1 hQ.le
  have h0 : 0 ≤ |(s : ℝ)| / Q' := div_nonneg (abs_nonneg _) hQ'.le
  linarith

#print axioms two_term_easy

/-- Numerics: for `t ≥ 18`, `2 (⌈t^2⌉ + ⌈4 t^3⌉) ≤ exp(t^2)`. -/
lemma radii_le_exp (t : ℝ) (ht : 18 ≤ t) :
    2 * ((⌈t ^ 2⌉₊ : ℝ) + (⌈4 * t ^ 3⌉₊ : ℝ)) ≤ Real.exp (t ^ 2) := by
  have ht0 : 0 < t := by linarith
  have h1 : (⌈t ^ 2⌉₊ : ℝ) ≤ t ^ 2 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h2 : (⌈4 * t ^ 3⌉₊ : ℝ) ≤ 4 * t ^ 3 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hexp : 1 + t ^ 2 + (t ^ 2) ^ 2 / 2 ≤ Real.exp (t ^ 2) :=
    Real.quadratic_le_exp_of_nonneg (by positivity)
  have h3 : (0 : ℝ) < t ^ 3 := pow_pos ht0 3
  have h4 : 18 * t ^ 3 ≤ t ^ 4 := by nlinarith [h3]
  have h5 : 18 * t ^ 2 ≤ t ^ 3 := by nlinarith [pow_pos ht0 2]
  have h6 : (0 : ℝ) < t ^ 2 := pow_pos ht0 2
  nlinarith [h4, h5, h6, h3]

/-- The hypothesis `hTT` of `close_factor` from `TwoTermSeparation`: the opposite-sign case is the external input, the other
cases are elementary. -/
theorem hTT_of_two_term_G (a : ℝ → ℝ) (ha : ∀ t, 0 ≤ t → 0 ≤ a t) (hP : TwoTermSep a) :
    ∃ T₁ : ℝ, ∀ (b n b' n' : ℕ), ((b = 2 ∧ b' = 3) ∨ (b = 3 ∧ b' = 2)) → 1 ≤ n → 1 ≤ n' →
      T₁ ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) → b ^ (n ^ 2) < b' ^ (n' ^ 2) →
      ((b' ^ (n' ^ 2) : ℕ) : ℝ) < Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) * ((b ^ (n ^ 2) : ℕ) : ℝ) →
      ∀ r s : ℤ, r ≠ 0 → |r| ≤ (⌈(Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 2⌉₊ : ℤ) →
        |s| ≤ (⌈4 * (Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 3⌉₊ : ℤ) →
        Real.exp (-(a (Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))))) /
            ((b ^ (n ^ 2) : ℕ) : ℝ) ≤
          nrm ((r : ℝ) / ((b ^ (n ^ 2) : ℕ) : ℝ) + (s : ℝ) / ((b' ^ (n' ^ 2) : ℕ) : ℝ)) := by
  obtain ⟨T₀, hT₀⟩ := hP
  refine ⟨max T₀ 18, ?_⟩
  intro b n b' n' hbb hn hn' hT hQQ hclose r s hr0 hrM hsN
  have hT0 : T₀ ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) := le_trans (le_max_left _ _) hT
  have hT18 : 18 ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) := le_trans (le_max_right _ _) hT
  by_cases hneg : r * s < 0
  · exact hT₀ b n b' n' r s hbb hn hn' hT0 hQQ hclose hr0 hrM hsN hneg
  · push Not at hneg
    set Q : ℝ := ((b ^ (n ^ 2) : ℕ) : ℝ) with hQdef
    set Q' : ℝ := ((b' ^ (n' ^ 2) : ℕ) : ℝ) with hQ'def
    set t : ℝ := Real.sqrt (Real.log Q) with htdef
    have hbpos : 0 < b := by rcases hbb with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have hQpos : 0 < Q := by rw [hQdef]; exact_mod_cast pow_pos hbpos _
    have hQQ' : Q ≤ Q' := by rw [hQdef, hQ'def]; exact_mod_cast hQQ.le
    have hlog : 0 ≤ Real.log Q := by
      have : (0 : ℝ) < t := by linarith
      by_contra h; push Not at h
      have := Real.sqrt_eq_zero_of_nonpos h.le
      linarith
    have ht2 : t ^ 2 = Real.log Q := Real.sq_sqrt hlog
    have hrad := radii_le_exp t hT18
    have hexpQ : Real.exp (t ^ 2) = Q := by rw [ht2, Real.exp_log hQpos]
    rw [hexpQ] at hrad
    have hrM' : |(r : ℝ)| ≤ (⌈t ^ 2⌉₊ : ℝ) := by
      have h2 : ((|r| : ℤ) : ℝ) ≤ (((⌈t ^ 2⌉₊ : ℤ)) : ℝ) := by exact_mod_cast hrM
      rw [Int.cast_abs] at h2; simpa using h2
    have hsN' : |(s : ℝ)| ≤ (⌈4 * t ^ 3⌉₊ : ℝ) := by
      have h2 : ((|s| : ℤ) : ℝ) ≤ (((⌈4 * t ^ 3⌉₊ : ℤ)) : ℝ) := by exact_mod_cast hsN
      rw [Int.cast_abs] at h2; simpa using h2
    clear_value t Q Q'
    have heasy := two_term_easy Q Q' hQpos hQQ' (⌈t ^ 2⌉₊ : ℝ) (⌈4 * t ^ 3⌉₊ : ℝ) hrad r s hr0 hrM' hsN' hneg
    refine le_trans ?_ heasy
    have hexp1 : Real.exp (-(a t)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ a t := ha t (by linarith)
      linarith
    exact div_le_div_of_nonneg_right hexp1 hQpos.le

/-- The original `A log^2(2+t)` form. -/
theorem hTT_of_two_term (A : ℝ) (hA : 0 ≤ A) (hP : TwoTermSeparation A) :
    ∃ T₁ : ℝ, ∀ (b n b' n' : ℕ), ((b = 2 ∧ b' = 3) ∨ (b = 3 ∧ b' = 2)) → 1 ≤ n → 1 ≤ n' →
      T₁ ≤ Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) → b ^ (n ^ 2) < b' ^ (n' ^ 2) →
      ((b' ^ (n' ^ 2) : ℕ) : ℝ) < Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)) * ((b ^ (n ^ 2) : ℕ) : ℝ) →
      ∀ r s : ℤ, r ≠ 0 → |r| ≤ (⌈(Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 2⌉₊ : ℤ) →
        |s| ≤ (⌈4 * (Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ))) ^ 3⌉₊ : ℤ) →
        Real.exp (-(A * (Real.log (2 + Real.sqrt (Real.log ((b ^ (n ^ 2) : ℕ) : ℝ)))) ^ 2)) /
            ((b ^ (n ^ 2) : ℕ) : ℝ) ≤
          nrm ((r : ℝ) / ((b ^ (n ^ 2) : ℕ) : ℝ) + (s : ℝ) / ((b' ^ (n' ^ 2) : ℕ) : ℝ)) :=
  hTT_of_two_term_G (fun t => A * (Real.log (2 + t)) ^ 2) (fun t _ => by positivity) hP

#print axioms radii_le_exp
#print axioms hTT_of_two_term_G
#print axioms hTT_of_two_term

end JAClose
end LeanCheck
