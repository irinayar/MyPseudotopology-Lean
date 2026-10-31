import Mathlib
import LeanCheck.JACenter
import LeanCheck.MixedPrimeProduct

/-!
# The central bound, step 4: the far-field recursion on `ZMod N`

`MixedPrimeProduct.farfield_geom` is the far-field recursion for an abstract group `G` with a seminorm.  We apply it to
`G = ZMod N` with the seminorm induced from the circle (`‖x‖ = ‖x/N‖_{ℝ/ℤ}`, via `ZMod.toAddCircle`), to the normalized tails
`h_k = H_k/H_k(0)`, `H_k = K_{k+1} ∗ ⋯ ∗ K_L ∗ F` (`F` the triangle of radius `2m/N`), and to the weights `w_j(d) = K_j(-d)`.

Checked here (no axiom, no `sorry`):

* `cn`: the circle norm on `ZMod N`; `cn_neg`, `cn_natCast_le`;
* `Ftri_vanish`: `F(y) = 0` if `cn y ≥ 2m/N`;
* `far_field_ZN`: for a list `ks` of good kernels (positive definite, `K ≥ 0`, `K(0) ≥ 1`, `∑K ≤ B`), `u ≥ 0` with
  `2m/N ≤ 3u/4`, `k + n = |ks|` and `cn y ≥ u`:
  `h_k(y) ≤ ∑_{j<n} B^j · ∑_{d : cn d > u/2^{j+3}} K_{k+j+1}(d)`,
  i.e. the paper's `(far-normalized)` with the tails of the kernels.
-/

namespace LeanCheck
namespace JAFar

open Finset JATransfer JAMulti JAProduct JAProduct2 JACenter JALocalize MixedPrime

variable {N : ℕ} [NeZero N]

/-- The circle norm of `d / N`. -/
noncomputable def cn (d : ZMod N) : ℝ := ‖ZMod.toAddCircle d‖

lemma cn_neg (d : ZMod N) : cn (-d) = cn d := by
  unfold cn; rw [map_neg, norm_neg]

lemma cn_natCast_le (k : ℕ) : cn (k : ZMod N) ≤ (k : ℝ) / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold cn
  rw [ZMod.toAddCircle_natCast]
  have := nrm_le_abs ((k : ℝ) / N)
  rw [abs_of_nonneg (by positivity)] at this
  exact this

/-- The seminorm on `ZMod N` induced from the circle. -/
noncomputable def zinst (N : ℕ) [NeZero N] : SeminormedAddCommGroup (ZMod N) :=
  SeminormedAddCommGroup.induced (ZMod N) UnitAddCircle ZMod.toAddCircle

lemma zinst_norm (d : ZMod N) : @norm (ZMod N) (zinst N).toNorm d = cn d := rfl

/-- The triangle vanishes outside the radius `2m/N`. -/
lemma Ftri_vanish (m : ℕ) (hm : 1 ≤ m) (y : ZMod N) (hy : (2 * m : ℝ) / N ≤ cn y) : Ftri N m y = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  by_cases harc : y ∈ arc N (2 * m - 1)
  · exfalso
    obtain ⟨k, hk, hy'⟩ := JABlocks.mem_arc_iff.mp harc
    have hkr : (k : ℝ) < 2 * m := by
      have : k < 2 * m := by omega
      exact_mod_cast this
    have hcn : cn y ≤ (k : ℝ) / N := by
      rcases hy' with rfl | rfl
      · exact cn_natCast_le k
      · rw [cn_neg]; exact cn_natCast_le k
    have : (k : ℝ) / N < (2 * m : ℝ) / N := by
      apply div_lt_div_of_pos_right _ hN
      linarith
    linarith
  · unfold Ftri
    rw [acorr_support (2 * m) y harc]
    simp

/-! ### The far-field recursion -/

lemma getD_props (ks : List (ZMod N → ℝ)) (B : ℝ) (hB : 0 ≤ B)
    (hks : ∀ K ∈ ks, PD K ∧ (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 ∧ ∑ x, K x ≤ B) (j : ℕ) :
    (∀ x, 0 ≤ ks.getD j (fun _ => 0) x) ∧ ∑ x, ks.getD j (fun _ => 0) x ≤ B := by
  by_cases hj : j < ks.length
  · have hmem : ks.getD j (fun _ => 0) ∈ ks := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    exact ⟨(hks _ hmem).2.1, (hks _ hmem).2.2.2⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨fun _ => le_rfl, by simpa using hB⟩

/-- **The far-field recursion on `ZMod N`.** -/
theorem far_field_ZN (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N) (ks : List (ZMod N → ℝ)) (B : ℝ) (hB : 0 ≤ B)
    (hks : ∀ K ∈ ks, PD K ∧ (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 ∧ ∑ x, K x ≤ B) (u : ℝ) (hu0 : 0 ≤ u)
    (hu : (2 * m : ℝ) / N ≤ 3 * u / 4) (n k : ℕ) (hk : k + n = ks.length) (y : ZMod N) (hy : u ≤ cn y) :
    Hs (Ftri N m) (ks.drop k) y / Hs (Ftri N m) (ks.drop k) 0 ≤
      ∑ j ∈ range n, B ^ j * ∑ d, (if u / 2 ^ (j + 3) < cn d then ks.getD (k + j) (fun _ => 0) d else 0) := by
  classical
  letI : SeminormedAddCommGroup (ZMod N) := zinst N
  set F := Ftri N m with hF
  have hF0 : F 0 = 1 := Ftri_zero m hm h2m
  have hFPD : PD F := Ftri_PD m
  -- facts about the tails
  have hsub : ∀ i, ∀ K ∈ ks.drop i, K ∈ ks := fun i K hK => List.mem_of_mem_drop hK
  have hHPD : ∀ i, PD (Hs F (ks.drop i)) := fun i =>
    Hs_PD F hFPD _ (fun K hK => (hks K (hsub i K hK)).1)
  have hH1 : ∀ i, 1 ≤ Hs F (ks.drop i) 0 := fun i =>
    (Hs_atom F hFPD.nonneg (by rw [hF0]) (ks.drop i)
      (fun K hK => ⟨(hks K (hsub i K hK)).2.1, (hks K (hsub i K hK)).2.2.1⟩)).2
  have hHpos : ∀ i, 0 < Hs F (ks.drop i) 0 := fun i => lt_of_lt_of_le one_pos (hH1 i)
  -- the data for `farfield_geom`
  let S : ℕ → Finset (ZMod N) := fun _ => Finset.univ
  let w : ℕ → ZMod N → ℝ := fun j d => ks.getD (j - 1) (fun _ => 0) (-d)
  let h : ℕ → ZMod N → ℝ := fun i y => Hs F (ks.drop i) y / Hs F (ks.drop i) 0
  have hw : ∀ j d, 0 ≤ w j d := fun j d => (getD_props ks B hB hks (j - 1)).1 (-d)
  have hmass : ∀ j, ∑ d ∈ S j, w j d ≤ B := by
    intro j
    have := (getD_props ks B hB hks (j - 1)).2
    calc ∑ d ∈ S j, w j d = ∑ d, ks.getD (j - 1) (fun _ => 0) d :=
          Fintype.sum_equiv (Equiv.neg _) _ _ (fun d => rfl)
      _ ≤ B := this
  have h0 : ∀ i y, 0 ≤ h i y := fun i y => div_nonneg
    ((Hs_atom F hFPD.nonneg (by rw [hF0]) (ks.drop i)
      (fun K hK => ⟨(hks K (hsub i K hK)).2.1, (hks K (hsub i K hK)).2.2.1⟩)).1 y) (hHpos i).le
  have h1 : ∀ i y, h i y ≤ 1 := fun i y => by
    show Hs F (ks.drop i) y / Hs F (ks.drop i) 0 ≤ 1
    rw [div_le_one (hHpos i)]
    exact PD.apply_le (hHPD i) y
  have hrec : ∀ i, i < ks.length → ∀ y, h i y ≤ ∑ d ∈ S (i + 1), w (i + 1) d * h (i + 1) (y + d) := by
    intro i hi y
    have hdrop : ks.drop i = ks[i] :: ks.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hmem : ks[i] ∈ ks := List.getElem_mem hi
    obtain ⟨hKPD, hKnn, hK0, hKB⟩ := hks _ hmem
    have hD := hHPD (i + 1)
    have hD0 := hHpos (i + 1)
    have hratio : Hs F (ks.drop (i + 1)) 0 ≤ Hs F (ks.drop i) 0 := by
      have := (factor_bounds ks[i] _ hKnn hK0 B hKB hD hD0).1
      rw [hdrop]
      show Hs F (ks.drop (i + 1)) 0 ≤ conv ks[i] (Hs F (ks.drop (i + 1))) 0
      rw [le_div_iff₀ hD0] at this
      linarith
    have hgetD : ks.getD (i + 1 - 1) (fun _ => 0) = ks[i] := by
      have e : i + 1 - 1 = i := by omega
      rw [e]
      exact List.getD_eq_getElem _ _ hi
    show Hs F (ks.drop i) y / Hs F (ks.drop i) 0 ≤
      ∑ d ∈ Finset.univ, ks.getD (i + 1 - 1) (fun _ => 0) (-d) *
        (Hs F (ks.drop (i + 1)) (y + d) / Hs F (ks.drop (i + 1)) 0)
    have hnum : Hs F (ks.drop i) y = ∑ e, ks[i] e * Hs F (ks.drop (i + 1)) (y - e) := by
      rw [hdrop]; rfl
    rw [hgetD, hnum]
    have hpos0 : 0 < Hs F (ks.drop i) 0 := hHpos i
    calc (∑ e, ks[i] e * Hs F (ks.drop (i + 1)) (y - e)) / Hs F (ks.drop i) 0
        ≤ (∑ e, ks[i] e * Hs F (ks.drop (i + 1)) (y - e)) / Hs F (ks.drop (i + 1)) 0 := by
          apply div_le_div_of_nonneg_left _ hD0 hratio
          exact Finset.sum_nonneg (fun e _ => mul_nonneg (hKnn e) (hD.nonneg _))
      _ = ∑ e, ks[i] e * (Hs F (ks.drop (i + 1)) (y - e) / Hs F (ks.drop (i + 1)) 0) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro e _
          ring
      _ = ∑ d ∈ Finset.univ, ks[i] (-d) * (Hs F (ks.drop (i + 1)) (y + d) /
            Hs F (ks.drop (i + 1)) 0) := by
          refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun e => ?_)
          simp only [Equiv.neg_apply, neg_neg, sub_eq_add_neg]
  have hL : ∀ y, (2 * m : ℝ) / N ≤ ‖y‖ → h ks.length y = 0 := by
    intro y hy
    show Hs F (ks.drop ks.length) y / Hs F (ks.drop ks.length) 0 = 0
    rw [List.drop_length]
    show F y / F 0 = 0
    rw [show F y = 0 from Ftri_vanish m hm y (by rw [← zinst_norm]; exact hy)]
    simp
  have key := MixedPrimeProduct.farfield_geom S w hw B hmass h h0 h1 ks.length ((2 * m : ℝ) / N) hrec hL u hu0
    hu n k hk y (by rw [zinst_norm]; exact hy)
  refine le_trans key (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold MixedPrimeProduct.tailMass
  have hgetD : ks.getD (k + j + 1 - 1) (fun _ => 0) = ks.getD (k + j) (fun _ => 0) := rfl
  refine Fintype.sum_equiv (Equiv.neg _) _ _ (fun d => ?_)
  simp only [S, w, Equiv.neg_apply, hgetD, neg_neg, zinst_norm, cn_neg]

#print axioms Ftri_vanish
#print axioms far_field_ZN

end JAFar
end LeanCheck
