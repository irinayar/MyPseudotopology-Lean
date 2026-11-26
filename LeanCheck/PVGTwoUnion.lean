import Mathlib
import LeanCheck.PVGTwoPoint

/-!
# PVGtwo, Section 7: rigidity of `A(δ)` and an unservable increasing union (Lean check)

Scope. Notation as in `PVGTwoPoint`: `Lv k = L_{k+1}` of the article, `dlt2 k = 2^{-Lv k}`, `sT m = 2^((m+1)^2)`.
`WinW w` is the union of the windows `[Lv k - w k, Lv k)` with widths `w k ≤ k + 1`.

* `inA_of_CdigW`, `YsetW_rep`, `YsetW_tb`, `near_YsetW` : the statements of `PVGTwoPoint` for narrower windows;
* `rigidity` : if all `aS`, `a ∈ A(δ)`, are totally bounded, then every neighbourhood `V` of `0` has an `ε > 0` such that
  `{x | ∀ k, dint (x / 2^{Lv k}) ≤ ε}` is covered by finitely many translates of `V`;
* `union_core`, `exists_union_unservable` : if moreover `(a / 2^m) S` are totally bounded for `a ∈ A(δ)` and
  arbitrarily large `m`, then the topology is precompact;
* `inA_div`, `inf_precompact_chain` : `a / 2^m ∈ A(2^m δ)`, and every group topology coarser than all `γ_{2^m δ}` is
  precompact.

Not formalized: the statement about maximal sets, and the theorem of Comfort and Ross.
A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set
open scoped Pointwise

namespace PVG
namespace Two
open Q95 Lac

/-! ## Narrower windows -/

def WinW (w : ℕ → ℕ) : Set ℕ := {p | ∃ k, Lv k ≤ p + w k ∧ p < Lv k}

def CdigW (w : ℕ → ℕ) (d : ℕ → Fin 2) : Prop := ∀ j n p : ℕ, p ∈ WinW w → j + 1 + p = n ^ 2 → d j = 0

def YsetW (w : ℕ → ℕ) : Set ℝ := {y | ∃ s : Finset ℕ, (∀ p ∈ s, p ∉ WinW w) ∧ y = ∑ p ∈ s, (2 : ℝ) ^ p}

lemma WinW_sub (w : ℕ → ℕ) (hw : ∀ k, w k ≤ k + 1) : WinW w ⊆ Win := by
  rintro p ⟨k, h1, h2⟩
  exact ⟨k, h1.trans (Nat.add_le_add_left (hw k) p), h2⟩

lemma CdigW_bound (w : ℕ → ℕ) (hw : ∀ k, w k ≤ k + 1) (d : ℕ → Fin 2) (hd : CdigW w d) (k n : ℕ) :
    dint (Real.ofDigits d * dlt2 k * 2 ^ (n ^ 2)) ≤ ((2 : ℝ) ^ (w k))⁻¹ := by
  have hLk := Lv_big k
  have hwk := hw k
  have hwin : ∀ p, Lv k ≤ p + w k → p < Lv k → p ∈ WinW w := fun p h1 h2 => ⟨k, h1, h2⟩
  by_cases hn : Lv k ≤ n ^ 2
  · set m := n ^ 2 - Lv k with hm
    obtain ⟨z, hz⟩ := shift_digits d m
    have e1 : Real.ofDigits d * dlt2 k * 2 ^ (n ^ 2) = Real.ofDigits (fun i => d (i + m)) - ((-z : ℤ) : ℝ) := by
      have e2 : (2 : ℝ) ^ (n ^ 2) = 2 ^ m * 2 ^ Lv k := by rw [← pow_add]; congr 1; omega
      have e3 : Real.ofDigits d * dlt2 k * 2 ^ (n ^ 2) = 2 ^ m * Real.ofDigits d := by
        unfold dlt2; rw [e2]; field_simp
      rw [e3, hz]; push_cast; ring
    rw [e1, dint_sub_int]
    refine (dint_le_abs _).trans ?_
    rw [abs_of_nonneg (Real.ofDigits_nonneg _)]
    refine ofDigits_le_of_zero _ _ fun i hi => ?_
    exact hd (i + m) n (Lv k - (i + 1)) (hwin _ (by omega) (by omega)) (by omega)
  · push Not at hn
    refine (dint_le_abs _).trans ?_
    have h0 := Real.ofDigits_nonneg d
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg h0 (by unfold dlt2; positivity)) (by positivity))]
    set J := n ^ 2 + w k - Lv k with hJ
    have hdig : Real.ofDigits d ≤ ((2 : ℝ) ^ J)⁻¹ := by
      refine ofDigits_le_of_zero _ _ fun i hi => ?_
      exact hd i n (n ^ 2 - (i + 1)) (hwin _ (by omega) (by omega)) (by omega)
    have hpow : (2 : ℝ) ^ (n ^ 2 + w k) ≤ 2 ^ J * 2 ^ Lv k := by
      rw [← pow_add]; exact pow_le_pow_right₀ one_le_two (by omega)
    unfold dlt2
    calc Real.ofDigits d * ((2 : ℝ) ^ Lv k)⁻¹ * 2 ^ (n ^ 2)
        ≤ ((2 : ℝ) ^ J)⁻¹ * ((2 : ℝ) ^ Lv k)⁻¹ * 2 ^ (n ^ 2) := by gcongr
      _ = 2 ^ (n ^ 2) * (2 ^ J * 2 ^ Lv k)⁻¹ := by rw [mul_inv]; ring
      _ ≤ 2 ^ (n ^ 2) * (2 ^ (n ^ 2 + w k))⁻¹ := by
          refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hpow) (by positivity)
      _ = ((2 : ℝ) ^ (w k))⁻¹ := by rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

lemma inA_of_CdigW (w : ℕ → ℕ) (hw : ∀ k, w k ≤ k + 1) (htop : Tendsto w atTop atTop) (d : ℕ → Fin 2)
    (hd : CdigW w d) : InA dlt2 sT (Real.ofDigits d) := by
  intro ε hε
  have h1 : Tendsto (fun v : ℕ => ((2 : ℝ)⁻¹) ^ v) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [htop.eventually (h1.eventually (Iio_mem_nhds hε))] with k hk m
  have e1 : sT m = (2 : ℝ) ^ ((m + 1) ^ 2) := rfl
  rw [e1]
  refine (CdigW_bound w hw d hd k (m + 1)).trans ?_
  rw [← inv_pow]; exact le_of_lt hk

/-- Every element of `Y_w` is `a s_n` with allowed digits of `a` that vanish at the first `M` places. -/
lemma YsetW_rep (w : ℕ → ℕ) (hw : ∀ k, w k ≤ k + 1) (y : ℝ) (hy : y ∈ YsetW w) (M : ℕ) :
    ∃ d : ℕ → Fin 2, CdigW w d ∧ (∀ j < M, d j = 0) ∧ ∃ m : ℕ, y = Real.ofDigits d * sT m := by
  classical
  obtain ⟨s, hs, rfl⟩ := hy
  set P := s.sup id + 1 with hP
  have hsP : ∀ p ∈ s, p < P := fun p hp => by
    have : p ≤ s.sup id := Finset.le_sup (f := id) hp
    omega
  set K := P + M with hK
  set n := Lv K with hn
  have hnK : 2 * K + 20 ≤ n := Lv_big K
  have hn2 : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero _
  set d : ℕ → Fin 2 := fun j => if ∃ p ∈ s, j + 1 + p = n ^ 2 then 1 else 0 with hd
  refine ⟨d, ?_, ?_, n - 1, ?_⟩
  · intro j m q hq hjq
    by_contra hne
    have hex : ∃ p ∈ s, j + 1 + p = n ^ 2 := by
      by_contra h
      exact hne (by simp only [hd]; rw [if_neg h])
    obtain ⟨p, hp, hjp⟩ := hex
    have hpP := hsP p hp
    have hbal : q + n ^ 2 = p + m ^ 2 := by omega
    rcases lt_trichotomy m n with hlt | rfl | hgt
    · have h1 : (m + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hlt 2
      have h2 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
      have h3 : m ^ 2 + (2 * n - 1) ≤ n ^ 2 := by
        have h4 : (n - 1 + 1) ^ 2 = n ^ 2 := by congr 1; omega
        have h5 : (n - 1 + 1) ^ 2 = (n - 1) ^ 2 + 2 * (n - 1) + 1 := by ring
        have h6 : m ^ 2 ≤ (n - 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega
      omega
    · have : q = p := by omega
      exact hs p hp (this ▸ hq)
    · obtain ⟨k, hk1, hk2⟩ := WinW_sub w hw hq
      have h1 : (n + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hgt 2
      have h2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      have hkK : K < k := by
        by_contra h
        have := Lv_mono (not_lt.1 h)
        omega
      have hmono : ∀ a b, a ≤ b → ell a ≤ ell b := by
        intro a b hab
        refine monotone_nat_of_le_succ (f := ell) (fun i => ?_) hab
        have h4 : ell i ≤ Lv i := by rw [Lv_def]; exact Nat.le_add_left _ _
        rw [ell_succ]
        exact h4.trans (Nat.le_self_pow two_ne_zero _)
      have hell : n ^ 2 ≤ ell k := by
        have h3 : ell (K + 1) ≤ ell k := hmono _ _ hkK
        rwa [ell_succ] at h3
      have hbig : ∀ i, 2 * i + 8 ≤ ell i := by
        intro i
        induction i with
        | zero => simp [ell]
        | succ i ih =>
          have h6 : ell i + 2 ≤ ell (i + 1) := by
            rw [ell_succ]
            have h8 := ell_ge i
            have h9 : ell i + 2 ≤ Lv i := by
              rw [Lv_def]
              have : 2 ≤ ell i ^ 2 := le_trans (by omega) (Nat.le_self_pow two_ne_zero _)
              omega
            exact h9.trans (Nat.le_self_pow two_ne_zero _)
          omega
      have hLk := Lv_def k
      have hk8 := hbig k
      have h11 : P < n := by omega
      have h12 : 2 * n ≤ n ^ 2 := by
        rw [sq]; exact Nat.mul_le_mul_right _ (by omega)
      have hlow : ell k ^ 2 < m ^ 2 := by omega
      have hupp : m ^ 2 < (ell k + 1) ^ 2 := by
        have h15 : (ell k + 1) ^ 2 = ell k ^ 2 + 2 * ell k + 1 := by ring
        omega
      have h16 := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hlow
      have h17 := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hupp
      omega
  · intro j hj
    simp only [hd]
    rw [if_neg]
    rintro ⟨p, hp, h⟩
    have := hsP p hp
    omega
  · have e1 : sT (n - 1) = (2 : ℝ) ^ (n ^ 2) := by
      show (2 : ℝ) ^ ((n - 1 + 1) ^ 2) = _
      congr 2; omega
    have hlt : ∀ p ∈ s, p < n ^ 2 := fun p hp => by have := hsP p hp; omega
    have hval : Real.ofDigits d = ∑ p ∈ s, (2 : ℝ) ^ p / 2 ^ (n ^ 2) := by
      unfold Real.ofDigits
      rw [tsum_eq_sum (s := s.image fun p => n ^ 2 - 1 - p)]
      · rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun p hp => ?_
          have hpn := hlt p hp
          have h1 : d (n ^ 2 - 1 - p) = 1 := by
            simp only [hd]
            rw [if_pos ⟨p, hp, by omega⟩]
          unfold Real.ofDigitsTerm
          rw [h1]
          have e2 : (2 : ℝ) ^ (n ^ 2) = 2 ^ p * 2 ^ (n ^ 2 - 1 - p + 1) := by
            rw [← pow_add]; congr 1; omega
          rw [e2]
          push_cast
          simp only [Fin.val_one, Nat.cast_one, one_mul]
          field_simp
        · intro a ha b hb hab
          have := hlt a ha
          have := hlt b hb
          simp only at hab
          omega
      · intro j hj
        have h0 : d j = 0 := by
          simp only [hd]
          rw [if_neg]
          rintro ⟨p, hp, h⟩
          exact hj (Finset.mem_image.2 ⟨p, hp, by omega⟩)
        simp [Real.ofDigitsTerm, h0]
    rw [hval, e1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    field_simp

lemma YsetW_tb (w : ℕ → ℕ) (hw : ∀ k, w k ≤ k + 1) (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : euclidNhds 0 ≤ N) (h : ∀ d : ℕ → Fin 2, CdigW w d → Tb N (dil (Real.ofDigits d) Sset)) :
    Tb N (YsetW w) := by
  classical
  intro W hW
  obtain ⟨V, hVN, hsym, hsum⟩ := eight N hhalf W hW
  have h0V : (0 : ℝ) ∈ V := mem_of_mem_nhds (heu hVN)
  obtain ⟨η, hη, hηV⟩ := Metric.mem_nhds_iff.1 (heu hVN)
  have hball : ∀ x : ℝ, |x| < η → x ∈ V := fun x hx => hηV (by simpa [Metric.mem_ball, Real.dist_eq] using hx)
  let Ω := {d : ℕ → Fin 2 // CdigW w d}
  have hΩc : IsClosed {d : ℕ → Fin 2 | CdigW w d} := by
    have e1 : {d : ℕ → Fin 2 | CdigW w d} =
        ⋂ (j : ℕ) (n : ℕ) (p : ℕ) (_ : p ∈ WinW w) (_ : j + 1 + p = n ^ 2), {d | d j = 0} := by
      ext d
      simp only [CdigW, mem_ofPred_eq, mem_iInter]
    rw [e1]
    exact isClosed_iInter fun j => isClosed_iInter fun n => isClosed_iInter fun p => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_eq (continuous_apply j) continuous_const
  haveI : CompactSpace Ω := isCompact_iff_compactSpace.1 hΩc.isCompact
  haveI : Nonempty Ω := ⟨⟨fun _ => 0, fun _ _ _ _ _ => rfl⟩⟩
  let T : Finset ℚ → Set ℝ := fun F => (fun q : ℚ => (q : ℝ)) '' (F : Set ℚ) + (V + V)
  let E : Finset ℚ → Set Ω := fun F => ⋂ s ∈ Sset, (fun d : Ω => Real.ofDigits d.1 * s) ⁻¹' closure (T F)
  have hEc : ∀ F, IsClosed (E F) := fun F => by
    refine isClosed_biInter fun s _ => isClosed_closure.preimage ?_
    exact (Real.continuous_ofDigits.comp continuous_subtype_val).mul continuous_const
  have hcover : ⋃ F, E F = univ := by
    refine eq_univ_of_forall fun d => mem_iUnion.2 ?_
    obtain ⟨F', hF'⟩ := h d.1 d.2 V hVN
    have hq : ∀ f : ℝ, ∃ q : ℚ, |f - q| < η := fun f => exists_rat_near f hη
    choose q hq using hq
    refine ⟨F'.image q, mem_iInter₂.2 fun s hs => subset_closure ?_⟩
    obtain ⟨f, hf, hfv⟩ := hF' (Real.ofDigits d.1 * s) ⟨s, hs, rfl⟩
    refine Set.mem_add.2 ⟨(q f : ℝ), ⟨q f, Finset.mem_image_of_mem _ hf, rfl⟩,
      (Real.ofDigits d.1 * s - f) + (f - q f), Set.add_mem_add hfv (hball _ (hq f)), by ring⟩
  obtain ⟨F, d0, hd0⟩ := nonempty_interior_of_iUnion_of_closed hEc hcover
  obtain ⟨O, hO, hOE⟩ := isOpen_induced_iff.1 (isOpen_interior (s := E F))
  have hd0O : d0.1 ∈ O := by
    have : d0 ∈ Subtype.val ⁻¹' O := by rw [hOE]; exact hd0
    exact this
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.1 hO d0.1 hd0O
  set M := I.sup id + 1 with hM
  have hIM : ∀ i ∈ I, i < M := fun i hi => by
    have : i ≤ I.sup id := Finset.le_sup (f := id) hi
    omega
  have hcyl : ∀ d : Ω, (∀ j < M, d.1 j = d0.1 j) → d ∈ E F := by
    intro d hd
    refine interior_subset (s := E F) ?_
    rw [← hOE]
    refine hIu fun i hi => ?_
    rw [hd i (hIM i hi)]
    exact (hu i hi).2
  have hclos : ∀ x ∈ closure (T F), ∃ q ∈ F, ∃ v1 ∈ V, ∃ v2 ∈ V, ∃ v3 ∈ V, x = (q : ℝ) + v1 + v2 + v3 := by
    intro x hx
    obtain ⟨x', hx', hd⟩ := Metric.mem_closure_iff.1 hx η hη
    obtain ⟨a, ⟨q, hq, rfl⟩, b, hb, hab⟩ := Set.mem_add.1 hx'
    obtain ⟨v1, hv1, v2, hv2, hv⟩ := Set.mem_add.1 hb
    refine ⟨q, hq, v1, hv1, v2, hv2, x - x', hball _ (by rwa [Real.dist_eq] at hd), ?_⟩
    rw [← hab, ← hv]; ring
  refine ⟨((F ×ˢ F).image fun p => (p.1 : ℝ) - (p.2 : ℝ)), fun y hy => ?_⟩
  obtain ⟨d, hd, hzero, m, hym⟩ := YsetW_rep w hw y hy M
  set d0' : ℕ → Fin 2 := fun j => if j < M then d0.1 j else 0 with hd0'
  set d1 : ℕ → Fin 2 := fun j => if j < M then d0.1 j else d j with hd1
  have hc0 : CdigW w d0' := by
    intro j n p hp hj
    simp only [hd0']
    split
    · exact d0.2 j n p hp hj
    · rfl
  have hc1 : CdigW w d1 := by
    intro j n p hp hj
    simp only [hd1]
    split
    · exact d0.2 j n p hp hj
    · exact hd j n p hp hj
  have hE0 := hcyl ⟨d0', hc0⟩ (fun j hj => by simp [hd0', hj])
  have hE1 := hcyl ⟨d1, hc1⟩ (fun j hj => by simp [hd1, hj])
  have hsum01 : Real.ofDigits d1 = Real.ofDigits d0' + Real.ofDigits d := by
    unfold Real.ofDigits
    rw [← Summable.tsum_add Real.summable_ofDigitsTerm Real.summable_ofDigitsTerm]
    refine tsum_congr fun j => ?_
    unfold Real.ofDigitsTerm
    by_cases hj : j < M
    · have e1 : d1 j = d0' j := by simp [hd1, hd0', hj]
      rw [e1, hzero j hj]; simp
    · have e1 : d1 j = d j := by simp [hd1, hj]
      have e2 : d0' j = 0 := by simp [hd0', hj]
      rw [e1, e2]; simp
  have hs : sT m ∈ Sset := by
    have := sign_mem_Sset (c := 1) (by simp) m
    rwa [one_mul] at this
  obtain ⟨q1, hq1, v1, hv1, v2, hv2, v3, hv3, h1⟩ := hclos _ (mem_iInter₂.1 hE1 (sT m) hs)
  obtain ⟨q0, hq0, w1, hw1, w2, hw2, w3, hw3, h0⟩ := hclos _ (mem_iInter₂.1 hE0 (sT m) hs)
  refine ⟨(q1 : ℝ) - q0, Finset.mem_image.2 ⟨(q1, q0), Finset.mem_product.2 ⟨hq1, hq0⟩, rfl⟩, ?_⟩
  have e1 : y - ((q1 : ℝ) - q0) = ((v1 + v2) + (v3 + -w1)) + ((-w2 + -w3) + (0 + 0)) := by
    have h2 : y = Real.ofDigits d1 * sT m - Real.ofDigits d0' * sT m := by rw [hym, hsum01]; ring
    rw [h2]
    have h1' : Real.ofDigits d1 * sT m = q1 + v1 + v2 + v3 := h1
    have h0' : Real.ofDigits d0' * sT m = q0 + w1 + w2 + w3 := h0
    rw [h1', h0']; ring
  rw [e1]
  exact hsum _ hv1 _ hv2 _ hv3 _ (hsym _ hw1) _ (hsym _ hw2) _ (hsym _ hw3) _ h0V _ h0V

/-- A real that is close enough to `2^{Lv k} ℤ` at every level lies near `Y_w - Y_w`. -/
lemma near_YsetW (w : ℕ → ℕ) (hw : ∀ k, w k ≤ k + 1) (z : ℝ)
    (hz : ∀ k, dint (z / 2 ^ Lv k) ≤ ((2 : ℝ) ^ (w k + 3))⁻¹) :
    ∃ y1 ∈ YsetW w, ∃ y2 ∈ YsetW w, |z - (y1 - y2)| ≤ 2 ^ Lv 0 + 1 := by
  classical
  set z' : ℤ := round z with hz'
  have hzz : |z - z'| ≤ 1 / 2 := abs_sub_round z
  set t : ℕ → ℤ := fun k => z' - round ((z' : ℝ) / 2 ^ Lv k) * 2 ^ Lv k with ht
  have hpos : ∀ k, (0 : ℝ) < 2 ^ Lv k := fun k => by positivity
  have htb : ∀ k, |t k| ≤ 2 ^ (Lv k - (w k + 2)) := by
    intro k
    have hL := Lv_big k
    have hwk := hw k
    have h1 : dint ((z' : ℝ) / 2 ^ Lv k) ≤ dint (z / 2 ^ Lv k) + (1 / 2) / 2 ^ Lv k := by
      have e1 : (z' : ℝ) / 2 ^ Lv k = z / 2 ^ Lv k + -((z - z') / 2 ^ Lv k) := by ring
      rw [e1]
      refine (dint_add_le _ _).trans ?_
      rw [dint_neg]
      refine add_le_add le_rfl ((dint_le_abs _).trans ?_)
      rw [abs_div, abs_of_pos (hpos k)]
      exact div_le_div_of_nonneg_right hzz (hpos k).le
    have h2 : (|t k| : ℝ) = 2 ^ Lv k * dint ((z' : ℝ) / 2 ^ Lv k) := by
      rw [dint_eq]
      have e1 : (t k : ℝ) = 2 ^ Lv k * ((z' : ℝ) / 2 ^ Lv k - round ((z' : ℝ) / 2 ^ Lv k)) := by
        rw [ht]; push_cast; field_simp
      rw [← Int.cast_abs, Int.cast_abs, e1, abs_mul, abs_of_pos (hpos k)]
    have h3 : (|t k| : ℝ) ≤ 2 ^ (Lv k - (w k + 2)) := by
      rw [h2]
      have h4 := mul_le_mul_of_nonneg_left (h1.trans (add_le_add (hz k) le_rfl)) (hpos k).le
      refine h4.trans ?_
      have e2 : (2 : ℝ) ^ Lv k = 2 ^ (Lv k - (w k + 2)) * 2 ^ (w k + 2) := by
        rw [← pow_add]; congr 1; omega
      have e3 : (2 : ℝ) ^ (w k + 3) = 2 ^ (w k + 2) * 2 := by rw [← pow_succ]
      have e4 : (2 : ℝ) ^ Lv k * (((2 : ℝ) ^ (w k + 3))⁻¹ + (1 / 2) / 2 ^ Lv k) =
          2 ^ (Lv k - (w k + 2)) / 2 + 1 / 2 := by
        rw [mul_add]
        congr 1
        · rw [e2, e3]; field_simp
        · field_simp
      rw [e4]
      have h5 : (1 : ℝ) ≤ 2 ^ (Lv k - (w k + 2)) := one_le_pow₀ one_le_two
      linarith
    exact_mod_cast h3
  set u : ℕ → ℤ := fun k => t (k + 1) - t k with hu
  have hudvd : ∀ k, (2 : ℤ) ^ Lv k ∣ u k := by
    intro k
    have h1 : (2 : ℤ) ^ Lv k ∣ 2 ^ Lv (k + 1) := pow_dvd_pow _ (Lv_mono (Nat.le_succ k))
    have e1 : u k = round ((z' : ℝ) / 2 ^ Lv k) * 2 ^ Lv k -
        round ((z' : ℝ) / 2 ^ Lv (k + 1)) * 2 ^ Lv (k + 1) := by
      rw [hu, ht]; ring
    rw [e1]
    exact dvd_sub (Dvd.intro_left _ rfl) (h1.mul_left _)
  have hult : ∀ k, (u k).natAbs < 2 ^ (Lv (k + 1) - (w (k + 1) + 1)) := by
    intro k
    have hgap : Lv k + (k + 1) + 20 ≤ Lv (k + 1) := Lv_gap (Nat.lt_succ_self k)
    have hw0 := hw k
    have hw1 := hw (k + 1)
    have h1 := htb (k + 1)
    have h2 := htb k
    have h3 : |u k| ≤ |t (k + 1)| + |t k| := abs_sub _ _
    have h4 : (2 : ℤ) ^ (Lv (k + 1) - (w (k + 1) + 2)) + 2 ^ (Lv k - (w k + 2)) <
        2 ^ (Lv (k + 1) - (w (k + 1) + 1)) := by
      have e1 : (2 : ℤ) ^ (Lv (k + 1) - (w (k + 1) + 1)) = 2 ^ (Lv (k + 1) - (w (k + 1) + 2)) * 2 := by
        rw [← pow_succ]; congr 1; omega
      have h5 : (2 : ℤ) ^ (Lv k - (w k + 2)) < 2 ^ (Lv (k + 1) - (w (k + 1) + 2)) :=
        pow_lt_pow_right₀ one_lt_two (by omega)
      rw [e1]; omega
    have h6 : ((u k).natAbs : ℤ) < 2 ^ (Lv (k + 1) - (w (k + 1) + 1)) := by
      rw [Int.natCast_natAbs]; omega
    exact_mod_cast h6
  have hblock : ∀ k, ∃ s : Finset ℕ, (∀ p ∈ s, Lv k ≤ p ∧ p < Lv (k + 1) - (w (k + 1) + 1)) ∧
      (u k).natAbs = ∑ p ∈ s, 2 ^ p := by
    intro k
    have hgap : Lv k + (k + 1) + 20 ≤ Lv (k + 1) := Lv_gap (Nat.lt_succ_self k)
    have hw1 := hw (k + 1)
    have hdvd : 2 ^ Lv k ∣ (u k).natAbs := by
      have := Int.natAbs_dvd_natAbs.2 (hudvd k)
      rwa [Int.natAbs_pow] at this
    obtain ⟨q, hq⟩ := hdvd
    have hlt := hult k
    rw [hq] at hlt
    have hqlt : q < 2 ^ (Lv (k + 1) - (w (k + 1) + 1) - Lv k) := by
      have e1 : 2 ^ (Lv (k + 1) - (w (k + 1) + 1)) =
          2 ^ Lv k * 2 ^ (Lv (k + 1) - (w (k + 1) + 1) - Lv k) := by
        rw [← pow_add]; congr 1; omega
      rw [e1] at hlt
      exact Nat.lt_of_mul_lt_mul_left hlt
    obtain ⟨s, hs, e⟩ := bits _ q hqlt
    refine ⟨s.image (fun p => Lv k + p), fun p hp => ?_, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
      have := Finset.mem_range.1 (hs hj)
      omega
    · rw [hq, Finset.sum_image (fun x _ y _ h => Nat.add_left_cancel h), e, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => (pow_add _ _ _).symm
  choose s hs hsum using hblock
  have hnot : ∀ k p, Lv k ≤ p → p < Lv (k + 1) - (w (k + 1) + 1) → p ∉ WinW w := by
    rintro k p h1 h2 ⟨j, hj1, hj2⟩
    rcases le_or_gt j k with h | h
    · have := Lv_mono h
      omega
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
      · rw [show j = k + 1 from h'.symm] at hj1
        omega
      · have := Lv_gap (show k + 1 < j from h')
        have := hw j
        omega
  set K := z'.natAbs with hK
  have htK : t K = z' := by
    have hL := Lv_big K
    have h1 : |(z' : ℝ) / 2 ^ Lv K| < 1 / 2 := by
      rw [abs_div, abs_of_pos (hpos K), div_lt_iff₀ (hpos K)]
      have h2 : |(z' : ℝ)| = (K : ℝ) := by rw [hK, Nat.cast_natAbs, Int.cast_abs]
      have h3 : K < 2 ^ K := Nat.lt_two_pow_self
      have h4 : (2 : ℝ) ^ (K + 1) ≤ 2 ^ Lv K := pow_le_pow_right₀ one_le_two (by omega)
      have h5 : (K : ℝ) < 2 ^ K := by exact_mod_cast h3
      rw [h2]
      rw [pow_succ] at h4
      linarith
    have h6 : round ((z' : ℝ) / 2 ^ Lv K) = 0 := by
      rw [round_eq, Int.floor_eq_zero_iff]
      rw [abs_lt] at h1
      constructor <;> linarith [h1.1, h1.2]
    rw [ht]; simp only [h6, zero_mul, sub_zero]
  have htel : z' - t 0 = ∑ k ∈ Finset.range K, u k := by
    rw [hu, Finset.sum_range_sub t, htK]
  have hdisj : ∀ A : Finset ℕ, Set.PairwiseDisjoint (A : Set ℕ) s := by
    intro A i _ j _ hij
    refine Finset.disjoint_left.2 fun p hpi hpj => hij ?_
    have h1 := hs i p hpi
    have h2 := hs j p hpj
    by_contra _
    rcases lt_or_gt_of_ne hij with h | h
    · have := Lv_mono (Nat.succ_le_of_lt h)
      rw [Nat.succ_eq_add_one] at this
      omega
    · have := Lv_mono (Nat.succ_le_of_lt h)
      rw [Nat.succ_eq_add_one] at this
      omega
  have hY : ∀ A : Finset ℕ, (∑ k ∈ A, (((u k).natAbs : ℕ) : ℝ)) ∈ YsetW w := by
    intro A
    refine ⟨A.biUnion s, fun p hp => ?_, ?_⟩
    · obtain ⟨k, _, hpk⟩ := Finset.mem_biUnion.1 hp
      exact hnot k p (hs k p hpk).1 (hs k p hpk).2
    · rw [Finset.sum_biUnion (hdisj A)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsum k]; push_cast; rfl
  set Ap := (Finset.range K).filter (fun k => 0 ≤ u k) with hAp
  set Am := (Finset.range K).filter (fun k => ¬ 0 ≤ u k) with hAm
  refine ⟨_, hY Ap, _, hY Am, ?_⟩
  have hdiff : (∑ k ∈ Ap, (((u k).natAbs : ℕ) : ℝ)) - ∑ k ∈ Am, (((u k).natAbs : ℕ) : ℝ) =
      ((z' - t 0 : ℤ) : ℝ) := by
    rw [htel]
    push_cast
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range K) (fun k => 0 ≤ u k) (fun k => (u k : ℝ)),
      ← hAp, ← hAm, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have h1 := (Finset.mem_filter.1 hk).2
      rw [Nat.cast_natAbs, abs_of_nonneg h1]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have h1 := (Finset.mem_filter.1 hk).2
      rw [Nat.cast_natAbs, abs_of_neg (not_le.1 h1)]
      push_cast; ring
  rw [hdiff]
  have h1 : |(t 0 : ℝ)| ≤ 2 ^ Lv 0 := by
    have h2 := htb 0
    have h3 : |(t 0 : ℝ)| ≤ 2 ^ (Lv 0 - (w 0 + 2)) := by exact_mod_cast h2
    exact h3.trans (pow_le_pow_right₀ one_le_two (Nat.sub_le _ _))
  have e1 : z - ((z' - t 0 : ℤ) : ℝ) = (z - z') + t 0 := by push_cast; ring
  rw [e1]
  refine (abs_add_le _ _).trans ?_
  linarith

/-! ## Rigidity -/

/-- **Rigidity.** If all dilates `aS`, `a ∈ A(δ)`, are totally bounded, then every neighbourhood of `0` covers, with
finitely many translates, a set `{x | ∀ k, dint (x / 2^{Lv k}) ≤ ε}`. -/
theorem rigidity (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : euclidNhds 0 ≤ N) (hA : ∀ a : ℝ, InA dlt2 sT a → Tb N (dil a Sset)) :
    ∀ W ∈ N, ∃ ε : ℝ, 0 < ε ∧ ∃ F : Finset ℝ, ∀ x : ℝ, (∀ k, dint (x / 2 ^ Lv k) ≤ ε) → ∃ f ∈ F, x - f ∈ W := by
  classical
  intro W hW
  by_contra hcon
  -- a sequence in smaller and smaller sets whose differences avoid `W`
  have hbad : ∀ (i : ℕ) (F : Finset ℝ), ∃ x : ℝ,
      (∀ k, dint (x / 2 ^ Lv k) ≤ (1 : ℝ) / (8 * (i + 1))) ∧ ∀ f ∈ F, x - f ∉ W := by
    intro i F
    by_contra h
    refine hcon ⟨1 / (8 * (i + 1)), by positivity, F, fun x hx => ?_⟩
    by_contra h'
    exact h ⟨x, hx, fun f hf hfW => h' ⟨f, hf, hfW⟩⟩
  choose h hh using hbad
  let g : ℕ → Finset ℝ := fun n => Nat.rec ∅ (fun n G => insert (h n G) G) n
  have hg : ∀ n, g (n + 1) = insert (h n (g n)) (g n) := fun n => rfl
  set x : ℕ → ℝ := fun n => h n (g n) with hx
  have hmono : Monotone g := monotone_nat_of_le_succ fun n => by rw [hg]; exact Finset.subset_insert _ _
  have hmem : ∀ j n, j < n → x j ∈ g n := by
    intro j n hjn
    refine hmono (Nat.succ_le_of_lt hjn) ?_
    rw [Nat.succ_eq_add_one, hg]
    exact Finset.mem_insert_self _ _
  have hsmall : ∀ i k, dint (x i / 2 ^ Lv k) ≤ (1 : ℝ) / (8 * (i + 1)) := fun i k => (hh i (g i)).1 k
  have hsep : ∀ j n, j < n → x n - x j ∉ W := fun j n hjn => (hh n (g n)).2 _ (hmem j n hjn)
  -- the widths
  let P : ℕ → ℕ → Prop := fun k v => ∀ i, dint (x i / 2 ^ Lv k) ≤ ((2 : ℝ) ^ (v + 3))⁻¹
  have hP0 : ∀ k, P k 0 := by
    intro k i
    refine (hsmall i k).trans ?_
    have h1 : (8 : ℝ) ≤ 8 * (i + 1) := by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have e1 : ((2 : ℝ) ^ (0 + 3))⁻¹ = 1 / 8 := by norm_num
    rw [e1]
    exact one_div_le_one_div_of_le (by norm_num) h1
  set w : ℕ → ℕ := fun k => Nat.findGreatest (P k) (k + 1) with hwdef
  have hw : ∀ k, w k ≤ k + 1 := fun k => Nat.findGreatest_le _
  have hPw : ∀ k, P k (w k) := fun k => Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (hP0 k)
  have htop : Tendsto w atTop atTop := by
    refine tendsto_atTop.2 fun v => ?_
    have h1 : ∀ᶠ k : ℕ in atTop, ∀ i ∈ Finset.range (2 ^ v), dint (x i / 2 ^ Lv k) ≤ ((2 : ℝ) ^ (v + 3))⁻¹ := by
      refine (eventually_all_finset _).2 fun i _ => ?_
      have h2 : Tendsto (fun k : ℕ => |x i| * ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).const_mul |x i|
        rwa [mul_zero] at this
      refine (h2.eventually_le_const (by positivity : (0 : ℝ) < ((2 : ℝ) ^ (v + 3))⁻¹)).mono fun k hk => ?_
      refine (dint_le_abs _).trans (le_trans ?_ hk)
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ Lv k), div_eq_mul_inv, inv_pow]
      refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two ?_)) (abs_nonneg _)
      have := Lv_big k; omega
    filter_upwards [h1, eventually_ge_atTop v] with k hk hkv
    refine Nat.le_findGreatest (by omega) fun i => ?_
    by_cases hi : i < 2 ^ v
    · exact hk i (Finset.mem_range.2 hi)
    · refine (hsmall i k).trans ?_
      have h2 : (2 : ℝ) ^ v ≤ i + 1 := by
        have : 2 ^ v ≤ i + 1 := by omega
        exact_mod_cast this
      rw [one_div]
      refine inv_anti₀ (by positivity) ?_
      rw [pow_add]
      have : (2 : ℝ) ^ 3 = 8 := by norm_num
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  -- the whole sequence is totally bounded
  obtain ⟨V, hVN, hsym, hsum⟩ := eight N hhalf W hW
  have h0V : (0 : ℝ) ∈ V := mem_of_mem_nhds (heu hVN)
  have hYtb := YsetW_tb w hw N hhalf heu (fun d hd => hA _ (inA_of_CdigW w hw htop d hd))
  obtain ⟨G, hG⟩ := hYtb V hVN
  obtain ⟨H, hH⟩ := tb_interval N heu (2 ^ Lv 0 + 1) V hVN
  set F : Finset ℝ := ((G ×ˢ G) ×ˢ H).image fun p => p.1.1 - p.1.2 + p.2 with hF
  have hcov : ∀ i, ∃ f ∈ F, ∃ v1 ∈ V, ∃ v2 ∈ V, ∃ v3 ∈ V, x i - f = v1 - v2 + v3 := by
    intro i
    obtain ⟨y1, hy1, y2, hy2, herr⟩ := near_YsetW w hw (x i) (fun k => hPw k i)
    obtain ⟨g1, hg1, h1⟩ := hG y1 hy1
    obtain ⟨g2, hg2, h2⟩ := hG y2 hy2
    obtain ⟨e, he, h3⟩ := hH (x i - (y1 - y2)) (abs_le.1 herr)
    refine ⟨g1 - g2 + e, Finset.mem_image.2 ⟨((g1, g2), e),
      Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨hg1, hg2⟩, he⟩, rfl⟩,
      y1 - g1, h1, y2 - g2, h2, x i - (y1 - y2) - e, h3, by ring⟩
  choose f hfF v1 hv1 v2 hv2 v3 hv3 hxf using hcov
  obtain ⟨j, n, hjn, hfe⟩ : ∃ j n : ℕ, j < n ∧ f j = f n := by
    obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => (⟨f i, hfF i⟩ : F))
    have he' : f a = f b := by simpa using congrArg Subtype.val he
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, he'⟩
    · exact ⟨b, a, h, he'.symm⟩
  refine hsep j n hjn ?_
  have e1 : x n - x j = ((v1 n + -v2 n) + (v3 n + -v1 j)) + ((v2 j + -v3 j) + (0 + 0)) := by
    have h1 := hxf n
    have h2 := hxf j
    rw [hfe] at h2
    have e2 : x n - x j = (x n - f n) - (x j - f n) := by ring
    rw [e2, h1, h2]; ring
  rw [e1]
  exact hsum _ (hv1 n) _ (hsym _ (hv2 n)) _ (hv3 n) _ (hsym _ (hv1 j)) _ (hv2 j) _ (hsym _ (hv3 j)) _ h0V _ h0V

/-! ## The union of the groups `2^{-m} A(δ)` -/

/-- Total boundedness of `Y / 2^m`, from that of the dilates `(a / 2^m) S`. -/
lemma Yset_div_tb (m : ℕ) (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : euclidNhds 0 ≤ N) (h : ∀ a : ℝ, InA dlt2 sT a → Tb N (dil (a / 2 ^ m) Sset)) :
    ∀ V ∈ N, ∃ F : Finset ℝ, ∀ y ∈ Yset, ∃ f ∈ F, y / 2 ^ m - f ∈ V := by
  classical
  set N' : Filter ℝ := Filter.map (fun x => 2 ^ m * x) N with hN'
  have h2 : (2 : ℝ) ^ m ≠ 0 := by positivity
  have hmem : ∀ A : Set ℝ, A ∈ N' ↔ (fun x => 2 ^ m * x) ⁻¹' A ∈ N := fun A => Iff.rfl
  have hhalf' : ∀ W ∈ N', ∃ V ∈ N', (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W := by
    intro W hW
    obtain ⟨V, hV, hs, ha⟩ := hhalf _ ((hmem W).1 hW)
    refine ⟨(fun x => x / 2 ^ m) ⁻¹' V, (hmem _).2 ?_, fun x hx => ?_, fun x hx y hy => ?_⟩
    · refine mem_of_superset hV fun x hx => ?_
      show 2 ^ m * x / 2 ^ m ∈ V
      rwa [mul_div_cancel_left₀ _ h2]
    · show -x / 2 ^ m ∈ V
      rw [neg_div]; exact hs _ hx
    · have h3 : 2 ^ m * (x / 2 ^ m + y / 2 ^ m) ∈ W := ha _ hx _ hy
      have e1 : 2 ^ m * (x / 2 ^ m + y / 2 ^ m) = x + y := by field_simp
      rwa [e1] at h3
  have heu' : euclidNhds 0 ≤ N' := by
    have h3 : Tendsto (fun x : ℝ => x / 2 ^ m) (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun x : ℝ => x / 2 ^ m) (𝓝 0) (𝓝 (0 / 2 ^ m)) := tendsto_id.div_const _
      rwa [zero_div] at this
    intro A hA
    have h4 : (fun x => 2 ^ m * x) ⁻¹' A ∈ 𝓝 (0 : ℝ) := heu ((hmem A).1 hA)
    refine mem_of_superset (h3 h4) fun x hx => ?_
    have h5 : 2 ^ m * (x / 2 ^ m) ∈ A := hx
    rwa [mul_div_cancel₀ _ h2] at h5
  have hC : ∀ d : ℕ → Fin 2, Cdig d → Tb N' (dil (Real.ofDigits d) Sset) := by
    intro d hd V hV
    obtain ⟨F, hF⟩ := h _ (inA_of_Cdig d hd) _ ((hmem V).1 hV)
    refine ⟨F.image fun f => 2 ^ m * f, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    obtain ⟨f, hf, h3⟩ := hF (Real.ofDigits d / 2 ^ m * s) ⟨s, hs, rfl⟩
    refine ⟨2 ^ m * f, Finset.mem_image_of_mem _ hf, ?_⟩
    have h4 : 2 ^ m * (Real.ofDigits d / 2 ^ m * s - f) ∈ V := h3
    have e1 : 2 ^ m * (Real.ofDigits d / 2 ^ m * s - f) = Real.ofDigits d * s - 2 ^ m * f := by field_simp
    rwa [e1] at h4
  intro V hV
  have hV' : (fun x => x / 2 ^ m) ⁻¹' V ∈ N' := by
    refine (hmem _).2 (mem_of_superset hV fun x hx => ?_)
    show 2 ^ m * x / 2 ^ m ∈ V
    rwa [mul_div_cancel_left₀ _ h2]
  obtain ⟨F, hF⟩ := Yset_tb N' hhalf' heu' hC _ hV'
  refine ⟨F.image fun f => f / 2 ^ m, fun y hy => ?_⟩
  obtain ⟨f, hf, h3⟩ := hF y hy
  refine ⟨f / 2 ^ m, Finset.mem_image_of_mem _ hf, ?_⟩
  have h4 : (y - f) / 2 ^ m ∈ V := h3
  rwa [sub_div] at h4

/-- Every real is a bounded number, plus an element of `Y / 2^m`, plus a number close to the lattices. -/
lemma split (m : ℕ) (x : ℝ) : ∃ g y r : ℝ, x = g + y / 2 ^ m + r ∧ |g| ≤ 2 ^ Lv m ∧ y ∈ Yset ∧
    ∀ k, dint (r / 2 ^ Lv k) ≤ 2 * ((2 : ℝ) ^ m)⁻¹ := by
  classical
  have hpos : ∀ k, (0 : ℝ) < 2 ^ Lv k := fun k => by positivity
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  set g : ℝ := 2 ^ Lv m * Int.fract (x / 2 ^ Lv m) with hg
  set z : ℝ := x - g with hz
  have hzint : z = (⌊x / 2 ^ Lv m⌋ : ℝ) * 2 ^ Lv m := by
    rw [hz, hg, Int.fract]
    field_simp
    ring
  obtain ⟨K, hK⟩ : ∃ K : ℕ, |z| ≤ K := exists_nat_ge _
  set K' := max (K + m) (m + 1) with hK'
  set a : ℕ → ℕ := fun k => ⌊Int.fract (z / 2 ^ Lv k) * 2 ^ m⌋₊ with ha
  have ha1 : ∀ k, a k < 2 ^ m := by
    intro k
    have h1 : Int.fract (z / 2 ^ Lv k) * 2 ^ m < 2 ^ m := by
      have := mul_lt_mul_of_pos_right (Int.fract_lt_one (z / 2 ^ Lv k)) h2m
      rwa [one_mul] at this
    have h3 : (a k : ℝ) ≤ Int.fract (z / 2 ^ Lv k) * 2 ^ m :=
      Nat.floor_le (mul_nonneg (Int.fract_nonneg _) h2m.le)
    have : (a k : ℝ) < 2 ^ m := lt_of_le_of_lt h3 h1
    exact_mod_cast this
  have haclose : ∀ k, |Int.fract (z / 2 ^ Lv k) - a k / 2 ^ m| ≤ ((2 : ℝ) ^ m)⁻¹ := by
    intro k
    have h1 : (a k : ℝ) ≤ Int.fract (z / 2 ^ Lv k) * 2 ^ m :=
      Nat.floor_le (mul_nonneg (Int.fract_nonneg _) h2m.le)
    have h3 : Int.fract (z / 2 ^ Lv k) * 2 ^ m < a k + 1 := Nat.lt_floor_add_one _
    have e1 : Int.fract (z / 2 ^ Lv k) - a k / 2 ^ m = (Int.fract (z / 2 ^ Lv k) * 2 ^ m - a k) * ((2 : ℝ) ^ m)⁻¹ := by
      field_simp
    rw [e1, abs_mul, abs_of_pos (inv_pos.2 h2m)]
    refine mul_le_of_le_one_left (inv_nonneg.2 h2m.le) ?_
    rw [abs_le]; constructor <;> linarith
  set I : Finset ℕ := Finset.Ico (m + 1) K' with hI
  set y : ℝ := ∑ k ∈ I, (a k : ℝ) * 2 ^ Lv k with hy
  -- facts on the levels
  have hLm : ∀ k, m + 1 ≤ k → m + Lv (k - 1) + (k + 2) + m ≤ Lv k := by
    intro k hk
    have h1 := Lv_pow4 (k - 1)
    have h3 : k - 1 + 1 = k := by omega
    rw [h3] at h1
    have h4 := Lv_two_pow (k - 1)
    have h5 : k ≤ 2 ^ (k - 1) := by
      have := Nat.lt_two_pow_self (n := k - 1)
      omega
    have h6 := Lv_ge (k - 1)
    have h7 : 8 * Lv (k - 1) ≤ Lv (k - 1) ^ 4 := by
      have h8 : 8 ≤ Lv (k - 1) ^ 3 := le_trans (by omega) (Nat.le_self_pow three_ne_zero _)
      calc 8 * Lv (k - 1) ≤ Lv (k - 1) ^ 3 * Lv (k - 1) := Nat.mul_le_mul_right _ h8
        _ = Lv (k - 1) ^ 4 := by ring
    omega
  have hmL : ∀ k, m + 1 ≤ k → m ≤ Lv k := fun k hk => by have := Lv_big k; omega
  -- `y` belongs to `Y`
  have hbits : ∀ k, ∃ s : Finset ℕ, s ⊆ Finset.range m ∧ a k = ∑ p ∈ s, 2 ^ p := fun k => bits m (a k) (ha1 k)
  choose s hs hsa using hbits
  set t : ℕ → Finset ℕ := fun k => (s k).image (fun p => Lv k + p) with ht
  have htmem : ∀ k p, p ∈ t k → Lv k ≤ p ∧ p < Lv k + m := by
    intro k p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
    have := Finset.mem_range.1 (hs k hj)
    omega
  have hstep : ∀ k, m + 1 ≤ k → Lv k + m + (k + 2) ≤ Lv (k + 1) := by
    intro k hk
    have h1 := hLm (k + 1) (by omega)
    have e1 : k + 1 - 1 = k := by omega
    rw [e1] at h1
    omega
  have hdisj : Set.PairwiseDisjoint (I : Set ℕ) t := by
    intro i hi j hj hij
    refine Finset.disjoint_left.2 fun p hpi hpj => hij ?_
    have h1 := htmem i p hpi
    have h2 := htmem j p hpj
    have hi' := (Finset.mem_Ico.1 hi).1
    have hj' := (Finset.mem_Ico.1 hj).1
    by_contra _
    rcases lt_or_gt_of_ne hij with h | h
    · have h3 := hstep i hi'
      have h4 := Lv_mono (Nat.succ_le_of_lt h)
      rw [Nat.succ_eq_add_one] at h4
      omega
    · have h3 := hstep j hj'
      have h4 := Lv_mono (Nat.succ_le_of_lt h)
      rw [Nat.succ_eq_add_one] at h4
      omega
  have hyY : y ∈ Yset := by
    refine ⟨I.biUnion t, fun p hp => ?_, ?_⟩
    · obtain ⟨k, hk, hpk⟩ := Finset.mem_biUnion.1 hp
      have hk' := (Finset.mem_Ico.1 hk).1
      have h1 := htmem k p hpk
      rintro ⟨j, hj1, hj2⟩
      rcases le_or_gt j k with h | h
      · have := Lv_mono h
        omega
      · have h3 := hstep k hk'
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
        · rw [show j = k + 1 from h'.symm] at hj1
          omega
        · have := Lv_gap (show k + 1 < j from h')
          omega
    · rw [hy, Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ht, Finset.sum_image (fun p _ q _ h => Nat.add_left_cancel h), hsa k]
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by rw [pow_add]; ring
  refine ⟨g, y, z - y / 2 ^ m, by rw [hz]; ring, ?_, hyY, fun k => ?_⟩
  · rw [hg, abs_mul, abs_of_pos (hpos m), abs_of_nonneg (Int.fract_nonneg _)]
    exact mul_le_of_le_one_right (hpos m).le (Int.fract_lt_one _).le
  -- the remainder at level `k`
  have hu : y / 2 ^ m = ∑ i ∈ I, (a i : ℝ) * 2 ^ (Lv i - m) := by
    rw [hy, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 := hmL i (Finset.mem_Ico.1 hi).1
    have e1 : (2 : ℝ) ^ Lv i = 2 ^ (Lv i - m) * 2 ^ m := by rw [← pow_add]; congr 1; omega
    rw [e1]; field_simp
  -- terms of a level at or above `Lv k` are integers after division
  have hhigh : ∀ i ∈ I, k < i → ∃ w : ℤ, (a i : ℝ) * 2 ^ (Lv i - m) / 2 ^ Lv k = w := by
    intro i hi hki
    have hi' := (Finset.mem_Ico.1 hi).1
    have h1 : Lv k + m ≤ Lv i := by
      have h2 := hLm i hi'
      have h3 : Lv k ≤ Lv (i - 1) := Lv_mono (by omega)
      omega
    refine ⟨(a i : ℤ) * 2 ^ (Lv i - m - Lv k), ?_⟩
    have e1 : (2 : ℝ) ^ (Lv i - m) = 2 ^ (Lv i - m - Lv k) * 2 ^ Lv k := by rw [← pow_add]; congr 1; omega
    rw [e1]; push_cast; field_simp
  -- the terms below level `k` are small
  have hlow : ∀ n : ℕ, m + 1 ≤ n → ∑ i ∈ Finset.Ico (m + 1) n, (a i : ℝ) * 2 ^ (Lv i - m) ≤ 2 ^ (Lv (n - 1) + 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top hn]
      have h1 : (a n : ℝ) * 2 ^ (Lv n - m) ≤ 2 ^ Lv n := by
        have h2 : (a n : ℝ) ≤ 2 ^ m := by exact_mod_cast (ha1 n).le
        refine (mul_le_mul_of_nonneg_right h2 (by positivity)).trans (le_of_eq ?_)
        rw [← pow_add]; congr 1; have := hmL n hn; omega
      have h3 : (2 : ℝ) ^ (Lv (n - 1) + 1) ≤ 2 ^ Lv n := by
        refine pow_le_pow_right₀ one_le_two ?_
        have := hLm n hn
        omega
      have e1 : n + 1 - 1 = n := by omega
      rw [e1, pow_succ]
      linarith
  have h2inv : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := inv_pos.2 h2m
  rcases lt_or_ge k (m + 1) with hk | hk
  · -- low levels: the remainder is a multiple of `2^{Lv k}`
    have h1 : ∃ w : ℤ, (z - y / 2 ^ m) / 2 ^ Lv k = w := by
      have hkm : Lv k ≤ Lv m := Lv_mono (by omega)
      have h2 : ∃ w : ℤ, z / 2 ^ Lv k = w := by
        generalize ⌊x / 2 ^ Lv m⌋ = n0 at hzint ⊢
        refine ⟨n0 * 2 ^ (Lv m - Lv k), ?_⟩
        have e1 : (2 : ℝ) ^ Lv m = 2 ^ (Lv m - Lv k) * 2 ^ Lv k := by rw [← pow_add]; congr 1; omega
        conv_lhs => rw [hzint, e1]
        push_cast
        field_simp
      have h3 : ∃ w : ℤ, (y / 2 ^ m) / 2 ^ Lv k = w := by
        have h4 : ∀ i ∈ I, ∃ w : ℤ, (a i : ℝ) * 2 ^ (Lv i - m) / 2 ^ Lv k = w :=
          fun i hi => hhigh i hi (by have := (Finset.mem_Ico.1 hi).1; omega)
        choose! wi hwi using h4
        refine ⟨∑ i ∈ I, wi i, ?_⟩
        rw [hu, Finset.sum_div]
        push_cast
        exact Finset.sum_congr rfl hwi
      obtain ⟨w1, hw1⟩ := h2
      obtain ⟨w2, hw2⟩ := h3
      refine ⟨w1 - w2, ?_⟩
      rw [sub_div, hw1, hw2]; push_cast; ring
    obtain ⟨w, hw⟩ := h1
    have e1 : (z - y / 2 ^ m) / 2 ^ Lv k = 0 - ((-w : ℤ) : ℝ) := by rw [hw]; push_cast; ring
    rw [e1, dint_sub_int, dint_zero]
    positivity
  rcases lt_or_ge k K' with hkK | hkK
  · -- middle levels
    have hkI : k ∈ I := Finset.mem_Ico.2 ⟨hk, hkK⟩
    have hsplit : ∑ i ∈ I, (a i : ℝ) * 2 ^ (Lv i - m) =
        ∑ i ∈ Finset.Ico (m + 1) k, (a i : ℝ) * 2 ^ (Lv i - m) + (a k : ℝ) * 2 ^ (Lv k - m) +
          ∑ i ∈ Finset.Ico (k + 1) K', (a i : ℝ) * 2 ^ (Lv i - m) := by
      rw [hI, ← Finset.sum_Ico_consecutive _ hk (le_of_lt hkK), Finset.sum_eq_sum_Ico_succ_bot hkK, add_assoc]
    have h4 : ∀ i ∈ Finset.Ico (k + 1) K', ∃ w : ℤ, (a i : ℝ) * 2 ^ (Lv i - m) / 2 ^ Lv k = w := by
      intro i hi
      have h5 := Finset.mem_Ico.1 hi
      exact hhigh i (Finset.mem_Ico.2 ⟨by omega, h5.2⟩) (by omega)
    choose! wi hwi using h4
    set low := ∑ i ∈ Finset.Ico (m + 1) k, (a i : ℝ) * 2 ^ (Lv i - m) with hlowdef
    have hlow0 : 0 ≤ low := Finset.sum_nonneg fun i _ => by positivity
    have e1 : (z - y / 2 ^ m) / 2 ^ Lv k = (Int.fract (z / 2 ^ Lv k) - a k / 2 ^ m - low / 2 ^ Lv k) -
        ((∑ i ∈ Finset.Ico (k + 1) K', wi i - ⌊z / 2 ^ Lv k⌋ : ℤ) : ℝ) := by
      have h6 : (a k : ℝ) * 2 ^ (Lv k - m) / 2 ^ Lv k = a k / 2 ^ m := by
        have e2 : (2 : ℝ) ^ Lv k = 2 ^ (Lv k - m) * 2 ^ m := by
          rw [← pow_add]; congr 1; have := hmL k hk; omega
        rw [e2]; field_simp
      have h7 : (∑ i ∈ Finset.Ico (k + 1) K', (a i : ℝ) * 2 ^ (Lv i - m)) / 2 ^ Lv k =
          ((∑ i ∈ Finset.Ico (k + 1) K', wi i : ℤ) : ℝ) := by
        rw [Finset.sum_div]; push_cast; exact Finset.sum_congr rfl hwi
      have h8 : z / 2 ^ Lv k = ⌊z / 2 ^ Lv k⌋ + Int.fract (z / 2 ^ Lv k) := (Int.floor_add_fract _).symm
      rw [sub_div, hu, hsplit, add_div, add_div, h6, h7]
      conv_lhs => rw [h8]
      push_cast
      ring
    rw [e1, dint_sub_int]
    refine (dint_le_abs _).trans ?_
    have h9 : low / 2 ^ Lv k ≤ ((2 : ℝ) ^ m)⁻¹ := by
      rw [div_le_iff₀ (hpos k), inv_mul_eq_div, le_div_iff₀ h2m]
      have h10 := hlow k hk
      refine (mul_le_mul_of_nonneg_right h10 h2m.le).trans ?_
      rw [← pow_add]
      refine pow_le_pow_right₀ one_le_two ?_
      have := hLm k hk
      omega
    have h11 := haclose k
    have h12 : 0 ≤ low / 2 ^ Lv k := div_nonneg hlow0 (hpos k).le
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg h12]
    linarith
  · -- high levels
    have hk1 : m + 1 ≤ k := hk
    refine (dint_le_abs _).trans ?_
    rw [abs_div, abs_of_pos (hpos k), div_le_iff₀ (hpos k)]
    have hy0 : 0 ≤ y / 2 ^ m := by
      rw [hu]; exact Finset.sum_nonneg fun i _ => by positivity
    have h1 : y / 2 ^ m ≤ 2 ^ (Lv (k - 1) + 1) := by
      rw [hu, hI]
      refine (hlow K' (by omega)).trans (pow_le_pow_right₀ one_le_two ?_)
      have : Lv (K' - 1) ≤ Lv (k - 1) := Lv_mono (by omega)
      omega
    have h2 : (2 : ℝ) ^ (Lv (k - 1) + 1) ≤ ((2 : ℝ) ^ m)⁻¹ * 2 ^ Lv k := by
      rw [inv_mul_eq_div, le_div_iff₀ h2m, ← pow_add]
      refine pow_le_pow_right₀ one_le_two ?_
      have := hLm k hk1
      omega
    have h3 : |z| ≤ ((2 : ℝ) ^ m)⁻¹ * 2 ^ Lv k := by
      have h4 : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast (Nat.lt_two_pow_self).le
      have h5 : (2 : ℝ) ^ K ≤ ((2 : ℝ) ^ m)⁻¹ * 2 ^ Lv k := by
        rw [inv_mul_eq_div, le_div_iff₀ h2m, ← pow_add]
        refine pow_le_pow_right₀ one_le_two ?_
        have := Lv_big k
        omega
      linarith
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hy0]
    have e1 : 2 * ((2 : ℝ) ^ m)⁻¹ * 2 ^ Lv k = ((2 : ℝ) ^ m)⁻¹ * 2 ^ Lv k + ((2 : ℝ) ^ m)⁻¹ * 2 ^ Lv k := by ring
    rw [e1]
    exact add_le_add h3 (h1.trans h2)

/-- **The union is not servable.** -/
theorem union_core (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : euclidNhds 0 ≤ N) (hA : ∀ a : ℝ, InA dlt2 sT a → Tb N (dil a Sset))
    (hm : ∀ M : ℕ, ∃ m, M ≤ m ∧ ∀ a : ℝ, InA dlt2 sT a → Tb N (dil (a / 2 ^ m) Sset)) :
    ∀ W ∈ N, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W := by
  classical
  intro W hW
  obtain ⟨V, hVN, hsym, hsum⟩ := eight N hhalf W hW
  have h0V : (0 : ℝ) ∈ V := mem_of_mem_nhds (heu hVN)
  obtain ⟨ε, hε, F, hF⟩ := rigidity N hhalf heu hA V hVN
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 2 * ((2 : ℝ) ^ M)⁻¹ ≤ ε := by
    have h1 : Tendsto (fun M : ℕ => 2 * ((2 : ℝ)⁻¹) ^ M) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).const_mul 2
      rwa [mul_zero] at this
    obtain ⟨M, hM⟩ := (h1.eventually_le_const hε).exists
    exact ⟨M, by rwa [inv_pow] at hM⟩
  obtain ⟨m, hMm, htb⟩ := hm M
  have hmε : 2 * ((2 : ℝ) ^ m)⁻¹ ≤ ε := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hM
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two hMm)
  obtain ⟨G, hG⟩ := Yset_div_tb m N hhalf heu htb V hVN
  obtain ⟨H, hH⟩ := tb_interval N heu (2 ^ Lv m) V hVN
  refine ⟨((H ×ˢ G) ×ˢ F).image fun p => p.1.1 + p.1.2 + p.2, fun x => ?_⟩
  obtain ⟨g, y, r, hx, hg, hy, hr⟩ := split m x
  obtain ⟨h, hh, h1⟩ := hH g (abs_le.1 hg)
  obtain ⟨g', hg', h2⟩ := hG y hy
  obtain ⟨f, hf, h3⟩ := hF r (fun k => (hr k).trans hmε)
  refine ⟨h + g' + f, Finset.mem_image.2 ⟨((h, g'), f),
    Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨hh, hg'⟩, hf⟩, rfl⟩, ?_⟩
  have e1 : x - (h + g' + f) = (((g - h) + (y / 2 ^ m - g')) + ((r - f) + 0)) + ((0 + 0) + (0 + 0)) := by
    rw [hx]; ring
  rw [e1]
  exact hsum _ h1 _ h2 _ h3 _ h0V _ h0V _ h0V _ h0V _ h0V

lemma inA_div (a : ℝ) (m : ℕ) (ha : InA dlt2 sT a) : InA (fun k => dlt2 k * 2 ^ m) sT (a / 2 ^ m) := by
  intro ε hε
  filter_upwards [ha ε hε] with k hk n
  have e1 : a / 2 ^ m * (dlt2 k * 2 ^ m) * sT n = a * dlt2 k * sT n := by field_simp
  rw [e1]; exact hk n

/-- **Theorem 7.12.** No non-precompact group topology below the usual one makes all `aS` totally bounded for
`a ∈ A(δ)` and all `(a / 2^m) S` for arbitrarily large `m`; and every group topology coarser than all the topologies
`γ_{2^m δ}` is precompact. -/
theorem exists_union_unservable :
    (∀ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ → euclidNhds 0 ≤ @nhds ℝ γ 0 →
      (∀ a : ℝ, InA dlt2 sT a → Tb (@nhds ℝ γ 0) (dil a Sset)) →
      (∀ M : ℕ, ∃ m, M ≤ m ∧ ∀ a : ℝ, InA dlt2 sT a → Tb (@nhds ℝ γ 0) (dil (a / 2 ^ m) Sset)) →
      ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W) ∧
    (∀ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ → (∀ m : ℕ, gamTop (fun k => dlt2 k * 2 ^ m) ≤ γ) →
      ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W) := by
  have hfirst : ∀ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ → euclidNhds 0 ≤ @nhds ℝ γ 0 →
      (∀ a : ℝ, InA dlt2 sT a → Tb (@nhds ℝ γ 0) (dil a Sset)) →
      (∀ M : ℕ, ∃ m, M ≤ m ∧ ∀ a : ℝ, InA dlt2 sT a → Tb (@nhds ℝ γ 0) (dil (a / 2 ^ m) Sset)) →
      ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W :=
    fun γ hg heu hA hm => union_core _ (group_half γ hg) heu hA hm
  have hd : ∀ m : ℕ, Tendsto (fun k => dlt2 k * 2 ^ m) atTop (𝓝 0) := by
    intro m
    have := dlt2_tendsto.mul_const ((2 : ℝ) ^ m)
    rwa [zero_mul] at this
  have hbound : ∀ k, |dlt2 k * 2 ^ 0| ≤ 1 := by
    intro k
    have h1 : dlt2 k ≤ 1 := by unfold dlt2; exact inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
    have h2 : 0 ≤ dlt2 k := by unfold dlt2; positivity
    rw [pow_zero, mul_one, abs_of_nonneg h2]; exact h1
  refine ⟨hfirst, fun γ hg hle => ?_⟩
  have heu : euclidNhds 0 ≤ @nhds ℝ γ 0 :=
    (gam_coarser_euclid _ 1 hbound 0).trans (nhds_mono (hle 0))
  have hmono : ∀ (m : ℕ) (a : ℝ), Tb (@nhds ℝ (gamTop (fun k => dlt2 k * 2 ^ m)) 0) (dil a Sset) →
      Tb (@nhds ℝ γ 0) (dil a Sset) :=
    fun m a h V hV => h V (nhds_mono (hle m) hV)
  have hserve : ∀ (m : ℕ) (a : ℝ), InA dlt2 sT a → Tb (@nhds ℝ γ 0) (dil (a / 2 ^ m) Sset) :=
    fun m a ha => hmono m _ (tb_gam _ (hd m) _ (inA_div a m ha))
  refine hfirst γ hg heu (fun a ha => ?_) (fun M => ⟨M, le_rfl, hserve M⟩)
  have h1 := hserve 0 a ha
  rwa [pow_zero, div_one] at h1

end Two
end PVG
