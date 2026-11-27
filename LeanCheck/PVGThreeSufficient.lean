import LeanCheck.PVGThreeDyadic
import LeanCheck.PVGTwoUnion

/-!
# PVGthree: a sufficient condition for rigidity

`δ_k = 2^(-L_k)`. Suppose there are widths `w_k → ∞` such that for every `p0` there are arbitrarily large `n`
with no `m² - n² + p` (`m > n`, `p < p0`) in any `[L_k - w_k, L_k)`. Then `δ` is rigid (`rig_of_avoids_seq`).

The proof is the proof of the rigidity theorem of `PVGTwoUnion`, with the sequence made a field of the class
`SW`; the one step that used the growth of the sparse sequence (`YsetW_rep`) uses the condition instead.
Sequences are indexed from `0`.
-/

open Filter Topology Set
open scoped Pointwise

namespace PVG
namespace Three
open Two Q95 Lac

/-- A dyadic sequence with widths. -/
class SW where
  L : ℕ → ℕ
  w0 : ℕ → ℕ
  mono : StrictMono L
  two : 2 ≤ L 0
  w0_top : Tendsto w0 atTop atTop

variable [S : SW]

/-- For every `p0` there are arbitrarily large `n` such that no `m² - n² + p` with `m > n`, `p < p0`
lies in an interval `[L_k - w_k, L_k)`. -/
def Avoids : Prop :=
  ∀ p0 N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∀ k m p q : ℕ, p < p0 → n < m → q + n ^ 2 = m ^ 2 + p →
    SW.L k ≤ q + SW.w0 k → q < SW.L k → False

lemma L_big (k : ℕ) : k + 2 ≤ SW.L k := by
  induction k with
  | zero => exact SW.two
  | succ k ih =>
    have := SW.mono (Nat.lt_succ_self k)
    simp only [Nat.succ_eq_add_one] at this
    omega

/-- Admissible narrower widths. -/
structure Adm (w : ℕ → ℕ) : Prop where
  le_w0 : ∀ k, w k ≤ SW.w0 k
  le_self : ∀ k, w k ≤ k
  step : ∀ k, w (k + 1) ≤ w k + 1

lemma Adm.add_two {w : ℕ → ℕ} (hw : Adm w) (k : ℕ) : w k + 2 ≤ SW.L k := by
  have := hw.le_self k
  have := L_big k
  omega

lemma Adm.low_mono {w : ℕ → ℕ} (hw : Adm w) {a b : ℕ} (h : a ≤ b) : SW.L a - w a ≤ SW.L b - w b := by
  induction h with
  | refl => exact le_rfl
  | @step b _ ih =>
    refine ih.trans ?_
    have h1 := hw.step b
    have h2 := SW.mono (Nat.lt_succ_self b)
    have h3 := hw.add_two b
    simp only [Nat.succ_eq_add_one] at h2 ⊢
    omega

def WinW (w : ℕ → ℕ) : Set ℕ := {p | ∃ k, SW.L k ≤ p + w k ∧ p < SW.L k}

def CdigW (w : ℕ → ℕ) (d : ℕ → Fin 2) : Prop := ∀ j n p : ℕ, p ∈ WinW w → j + 1 + p = n ^ 2 → d j = 0

def YsetW (w : ℕ → ℕ) : Set ℝ := {y | ∃ s : Finset ℕ, (∀ p ∈ s, p ∉ WinW w) ∧ y = ∑ p ∈ s, (2 : ℝ) ^ p}

lemma CdigW_bound (w : ℕ → ℕ) (hw : Adm w) (d : ℕ → Fin 2) (hd : CdigW w d) (k n : ℕ) :
    dint (Real.ofDigits d * dyseq SW.L k * 2 ^ (n ^ 2)) ≤ ((2 : ℝ) ^ (w k))⁻¹ := by
  have hwk := hw.add_two k
  have hwin : ∀ p, SW.L k ≤ p + w k → p < SW.L k → p ∈ WinW w := fun p h1 h2 => ⟨k, h1, h2⟩
  by_cases hn : SW.L k ≤ n ^ 2
  · set m := n ^ 2 - SW.L k with hm
    obtain ⟨z, hz⟩ := shift_digits d m
    have e1 : Real.ofDigits d * dyseq SW.L k * 2 ^ (n ^ 2) = Real.ofDigits (fun i => d (i + m)) - ((-z : ℤ) : ℝ) := by
      have e2 : (2 : ℝ) ^ (n ^ 2) = 2 ^ m * 2 ^ SW.L k := by rw [← pow_add]; congr 1; omega
      have e3 : Real.ofDigits d * dyseq SW.L k * 2 ^ (n ^ 2) = 2 ^ m * Real.ofDigits d := by
        unfold dyseq; rw [e2]; field_simp
      rw [e3, hz]; push_cast; ring
    rw [e1, dint_sub_int]
    refine (dint_le_abs _).trans ?_
    rw [abs_of_nonneg (Real.ofDigits_nonneg _)]
    refine ofDigits_le_of_zero _ _ fun i hi => ?_
    exact hd (i + m) n (SW.L k - (i + 1)) (hwin _ (by omega) (by omega)) (by omega)
  · push Not at hn
    refine (dint_le_abs _).trans ?_
    have h0 := Real.ofDigits_nonneg d
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg h0 (by unfold dyseq; positivity)) (by positivity))]
    set J := n ^ 2 + w k - SW.L k with hJ
    have hdig : Real.ofDigits d ≤ ((2 : ℝ) ^ J)⁻¹ := by
      refine ofDigits_le_of_zero _ _ fun i hi => ?_
      exact hd i n (n ^ 2 - (i + 1)) (hwin _ (by omega) (by omega)) (by omega)
    have hpow : (2 : ℝ) ^ (n ^ 2 + w k) ≤ 2 ^ J * 2 ^ SW.L k := by
      rw [← pow_add]; exact pow_le_pow_right₀ one_le_two (by omega)
    unfold dyseq
    calc Real.ofDigits d * ((2 : ℝ) ^ SW.L k)⁻¹ * 2 ^ (n ^ 2)
        ≤ ((2 : ℝ) ^ J)⁻¹ * ((2 : ℝ) ^ SW.L k)⁻¹ * 2 ^ (n ^ 2) := by gcongr
      _ = 2 ^ (n ^ 2) * (2 ^ J * 2 ^ SW.L k)⁻¹ := by rw [mul_inv]; ring
      _ ≤ 2 ^ (n ^ 2) * (2 ^ (n ^ 2 + w k))⁻¹ := by
          refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hpow) (by positivity)
      _ = ((2 : ℝ) ^ (w k))⁻¹ := by rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

lemma inA_of_CdigW (w : ℕ → ℕ) (hw : Adm w) (htop : Tendsto w atTop atTop) (d : ℕ → Fin 2)
    (hd : CdigW w d) : InA (dyseq SW.L) sT (Real.ofDigits d) := by
  intro ε hε
  have h1 : Tendsto (fun v : ℕ => ((2 : ℝ)⁻¹) ^ v) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [htop.eventually (h1.eventually (Iio_mem_nhds hε))] with k hk m
  have e1 : sT m = (2 : ℝ) ^ ((m + 1) ^ 2) := rfl
  rw [e1]
  refine (CdigW_bound w hw d hd k (m + 1)).trans ?_
  rw [← inv_pow]; exact le_of_lt hk

/-- Every element of `Y_w` is `a s_n` with allowed digits of `a` that vanish at the first `M` places. -/
lemma YsetW_rep (hS : Avoids) (w : ℕ → ℕ) (hw : Adm w) (y : ℝ) (hy : y ∈ YsetW w) (M : ℕ) :
    ∃ d : ℕ → Fin 2, CdigW w d ∧ (∀ j < M, d j = 0) ∧ ∃ m : ℕ, y = Real.ofDigits d * sT m := by
  classical
  obtain ⟨s, hs, rfl⟩ := hy
  set P := s.sup id + 1 with hP
  have hsP : ∀ p ∈ s, p < P := fun p hp => by
    have : p ≤ s.sup id := Finset.le_sup (f := id) hp
    omega
  obtain ⟨n, hnN, hn⟩ := hS P (P + M + 1)
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
    · obtain ⟨k, hk1, hk2⟩ := hq
      have hwk := hw.le_w0 k
      exact hn k m p q hpP hgt (by omega) (by omega) hk2
  · intro j hj
    simp only [hd]
    refine if_neg ?_
    rintro ⟨p, hp, h⟩
    have := hsP p hp
    omega
  · have hpn : ∀ p ∈ s, p < n := fun p hp => by
      have := hsP p hp
      omega
    have hsT : sT (n - 1) = (2 : ℝ) ^ (n ^ 2) := by
      show (2 : ℝ) ^ ((n - 1 + 1) ^ 2) = _
      congr 2
      omega
    have hval : Real.ofDigits d = ∑ p ∈ s, (2 : ℝ) ^ p / 2 ^ (n ^ 2) := by
      have hinj : ∀ p ∈ s, ∀ q ∈ s, n ^ 2 - 1 - p = n ^ 2 - 1 - q → p = q := by
        intro p hp q hq h
        have := hpn p hp
        have := hpn q hq
        omega
      have e1 : ∑ p ∈ s, (2 : ℝ) ^ p / 2 ^ (n ^ 2) =
          ∑ j ∈ s.image (fun p => n ^ 2 - 1 - p), ((1 : ℝ) / 2) ^ (j + 1) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun p hp => ?_
        have := hpn p hp
        have e2 : (2 : ℝ) ^ (n ^ 2) = 2 ^ p * 2 ^ (n ^ 2 - 1 - p + 1) := by
          rw [← pow_add]
          congr 1
          omega
        rw [e2, one_div, inv_pow]
        field_simp
      rw [e1]
      unfold Real.ofDigits
      rw [tsum_eq_sum (s := s.image (fun p => n ^ 2 - 1 - p))]
      · refine Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
        have := hpn p hp
        have h1 : d (n ^ 2 - 1 - p) = 1 := by
          simp only [hd]
          exact if_pos ⟨p, hp, by omega⟩
        unfold Real.ofDigitsTerm
        rw [h1]
        push_cast
        simp only [Fin.val_one, Nat.cast_one, one_mul, one_div, inv_pow]
      · intro j hj
        have h0 : d j = 0 := by
          simp only [hd]
          refine if_neg ?_
          rintro ⟨p, hp, h⟩
          exact hj (Finset.mem_image.2 ⟨p, hp, by omega⟩)
        simp [Real.ofDigitsTerm, h0]
    rw [hval, hsT, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    field_simp

lemma YsetW_tb (hS : Avoids) (w : ℕ → ℕ) (hw : Adm w) (N : Filter ℝ)
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
  obtain ⟨d, hd, hzero, m, hym⟩ := YsetW_rep hS w hw y hy M
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

/-- A real that is close enough to `2^{SW.L k} ℤ` at every level lies near `Y_w - Y_w`. -/
lemma near_YsetW (w : ℕ → ℕ) (hw : Adm w) (z : ℝ)
    (hz : ∀ k, dint (z / 2 ^ SW.L k) ≤ ((2 : ℝ) ^ (w k + 3))⁻¹) :
    ∃ y1 ∈ YsetW w, ∃ y2 ∈ YsetW w, |z - (y1 - y2)| ≤ 2 ^ SW.L 0 + 1 := by
  classical
  set z' : ℤ := round z with hz'
  have hzz : |z - z'| ≤ 1 / 2 := abs_sub_round z
  set t : ℕ → ℤ := fun k => z' - round ((z' : ℝ) / 2 ^ SW.L k) * 2 ^ SW.L k with ht
  have hpos : ∀ k, (0 : ℝ) < 2 ^ SW.L k := fun k => by positivity
  have htb : ∀ k, |t k| ≤ 2 ^ (SW.L k - (w k + 2)) := by
    intro k
    have hwk := hw.add_two k
    have h1 : dint ((z' : ℝ) / 2 ^ SW.L k) ≤ dint (z / 2 ^ SW.L k) + (1 / 2) / 2 ^ SW.L k := by
      have e1 : (z' : ℝ) / 2 ^ SW.L k = z / 2 ^ SW.L k + -((z - z') / 2 ^ SW.L k) := by ring
      rw [e1]
      refine (dint_add_le _ _).trans ?_
      rw [dint_neg]
      refine add_le_add le_rfl ((dint_le_abs _).trans ?_)
      rw [abs_div, abs_of_pos (hpos k)]
      exact div_le_div_of_nonneg_right hzz (hpos k).le
    have h2 : (|t k| : ℝ) = 2 ^ SW.L k * dint ((z' : ℝ) / 2 ^ SW.L k) := by
      rw [Two.dint_eq]
      have e1 : (t k : ℝ) = 2 ^ SW.L k * ((z' : ℝ) / 2 ^ SW.L k - round ((z' : ℝ) / 2 ^ SW.L k)) := by
        rw [ht]; push_cast; field_simp
      rw [← Int.cast_abs, Int.cast_abs, e1, abs_mul, abs_of_pos (hpos k)]
    have h3 : (|t k| : ℝ) ≤ 2 ^ (SW.L k - (w k + 2)) := by
      rw [h2]
      have h4 := mul_le_mul_of_nonneg_left (h1.trans (add_le_add (hz k) le_rfl)) (hpos k).le
      refine h4.trans ?_
      have e2 : (2 : ℝ) ^ SW.L k = 2 ^ (SW.L k - (w k + 2)) * 2 ^ (w k + 2) := by
        rw [← pow_add]; congr 1; omega
      have e3 : (2 : ℝ) ^ (w k + 3) = 2 ^ (w k + 2) * 2 := by rw [← pow_succ]
      have e4 : (2 : ℝ) ^ SW.L k * (((2 : ℝ) ^ (w k + 3))⁻¹ + (1 / 2) / 2 ^ SW.L k) =
          2 ^ (SW.L k - (w k + 2)) / 2 + 1 / 2 := by
        rw [mul_add]
        congr 1
        · rw [e2, e3]; field_simp
        · field_simp
      rw [e4]
      have h5 : (1 : ℝ) ≤ 2 ^ (SW.L k - (w k + 2)) := one_le_pow₀ one_le_two
      linarith
    exact_mod_cast h3
  set u : ℕ → ℤ := fun k => t (k + 1) - t k with hu
  have hudvd : ∀ k, (2 : ℤ) ^ SW.L k ∣ u k := by
    intro k
    have h1 : (2 : ℤ) ^ SW.L k ∣ 2 ^ SW.L (k + 1) := pow_dvd_pow _ (SW.mono.monotone (Nat.le_succ k))
    have e1 : u k = round ((z' : ℝ) / 2 ^ SW.L k) * 2 ^ SW.L k -
        round ((z' : ℝ) / 2 ^ SW.L (k + 1)) * 2 ^ SW.L (k + 1) := by
      rw [hu, ht]; ring
    rw [e1]
    exact dvd_sub (Dvd.intro_left _ rfl) (h1.mul_left _)
  have hult : ∀ k, (u k).natAbs ≤ 2 ^ (SW.L (k + 1) - (w (k + 1) + 1)) := by
    intro k
    have hw0 := hw.add_two k
    have hw1 := hw.add_two (k + 1)
    have hM := hw.low_mono (Nat.le_succ k)
    have h1 := htb (k + 1)
    have h2 := htb k
    have h3 : |u k| ≤ |t (k + 1)| + |t k| := abs_sub _ _
    have h4 : (2 : ℤ) ^ (SW.L (k + 1) - (w (k + 1) + 2)) + 2 ^ (SW.L k - (w k + 2)) ≤
        2 ^ (SW.L (k + 1) - (w (k + 1) + 1)) := by
      have e1 : (2 : ℤ) ^ (SW.L (k + 1) - (w (k + 1) + 1)) = 2 ^ (SW.L (k + 1) - (w (k + 1) + 2)) * 2 := by
        rw [← pow_succ]; congr 1; omega
      have h5 : (2 : ℤ) ^ (SW.L k - (w k + 2)) ≤ 2 ^ (SW.L (k + 1) - (w (k + 1) + 2)) := by
        refine pow_le_pow_right₀ one_le_two ?_
        simp only [Nat.succ_eq_add_one] at hM
        omega
      rw [e1]; omega
    have h6 : ((u k).natAbs : ℤ) ≤ 2 ^ (SW.L (k + 1) - (w (k + 1) + 1)) := by
      rw [Int.natCast_natAbs]; omega
    exact_mod_cast h6
  have hblock : ∀ k, ∃ s : Finset ℕ, (∀ p ∈ s, SW.L k ≤ p ∧ p < SW.L (k + 1) - w (k + 1)) ∧
      (u k).natAbs = ∑ p ∈ s, 2 ^ p := by
    intro k
    have hw1 := hw.add_two (k + 1)
    have hdvd : 2 ^ SW.L k ∣ (u k).natAbs := by
      have := Int.natAbs_dvd_natAbs.2 (hudvd k)
      rwa [Int.natAbs_pow] at this
    obtain ⟨q, hq⟩ := hdvd
    have hlt : (u k).natAbs < 2 ^ (SW.L (k + 1) - w (k + 1)) :=
      lt_of_le_of_lt (hult k) (Nat.pow_lt_pow_right one_lt_two (by omega))
    rw [hq] at hlt
    have hqlt : q < 2 ^ (SW.L (k + 1) - w (k + 1) - SW.L k) := by
      rcases le_or_gt (SW.L k) (SW.L (k + 1) - w (k + 1)) with h | h
      · have e1 : 2 ^ (SW.L (k + 1) - w (k + 1)) = 2 ^ SW.L k * 2 ^ (SW.L (k + 1) - w (k + 1) - SW.L k) := by
          rw [← pow_add]; congr 1; omega
        rw [e1] at hlt
        exact Nat.lt_of_mul_lt_mul_left hlt
      · have h2 : 2 ^ (SW.L (k + 1) - w (k + 1)) ≤ 2 ^ SW.L k := Nat.pow_le_pow_right two_pos h.le
        have h3 : q = 0 := by
          by_contra hq0
          have h4 : 2 ^ SW.L k * 1 ≤ 2 ^ SW.L k * q := Nat.mul_le_mul_left _ (Nat.pos_of_ne_zero hq0)
          omega
        rw [h3]
        positivity
    obtain ⟨s, hs, e⟩ := bits _ q hqlt
    refine ⟨s.image (fun p => SW.L k + p), fun p hp => ?_, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
      have := Finset.mem_range.1 (hs hj)
      omega
    · rw [hq, Finset.sum_image (fun x _ y _ h => Nat.add_left_cancel h), e, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => (pow_add _ _ _).symm
  choose s hs hsum using hblock
  have hnot : ∀ k p, SW.L k ≤ p → p < SW.L (k + 1) - w (k + 1) → p ∉ WinW w := by
    rintro k p h1 h2 ⟨j, hj1, hj2⟩
    rcases le_or_gt j k with h | h
    · have := SW.mono.monotone h
      omega
    · have := hw.low_mono (Nat.succ_le_of_lt h)
      simp only [Nat.succ_eq_add_one] at this
      omega
  set K := z'.natAbs with hK
  have htK : t K = z' := by
    have hL := L_big K
    have h1 : |(z' : ℝ) / 2 ^ SW.L K| < 1 / 2 := by
      rw [abs_div, abs_of_pos (hpos K), div_lt_iff₀ (hpos K)]
      have h2 : |(z' : ℝ)| = (K : ℝ) := by rw [hK, Nat.cast_natAbs, Int.cast_abs]
      have h3 : K < 2 ^ K := Nat.lt_two_pow_self
      have h4 : (2 : ℝ) ^ (K + 1) ≤ 2 ^ SW.L K := pow_le_pow_right₀ one_le_two (by omega)
      have h5 : (K : ℝ) < 2 ^ K := by exact_mod_cast h3
      rw [h2]
      rw [pow_succ] at h4
      linarith
    have h6 : round ((z' : ℝ) / 2 ^ SW.L K) = 0 := by
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
    · have := SW.mono.monotone (Nat.succ_le_of_lt h)
      rw [Nat.succ_eq_add_one] at this
      omega
    · have := SW.mono.monotone (Nat.succ_le_of_lt h)
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
  have h1 : |(t 0 : ℝ)| ≤ 2 ^ SW.L 0 := by
    have h2 := htb 0
    have h3 : |(t 0 : ℝ)| ≤ 2 ^ (SW.L 0 - (w 0 + 2)) := by exact_mod_cast h2
    exact h3.trans (pow_le_pow_right₀ one_le_two (Nat.sub_le _ _))
  have e1 : z - ((z' - t 0 : ℤ) : ℝ) = (z - z') + t 0 := by push_cast; ring
  rw [e1]
  refine (abs_add_le _ _).trans ?_
  linarith

/-! ## Rigidity -/

/-- Rigidity under the avoidance condition. -/
theorem rig_of_avoids (hS : Avoids) (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : euclidNhds 0 ≤ N) (hA : ∀ a : ℝ, InA (dyseq SW.L) sT a → Tb N (dil a Sset)) :
    ∀ W ∈ N, ∃ ε : ℝ, 0 < ε ∧ ∃ F : Finset ℝ, ∀ x : ℝ, (∀ k, dint (x / 2 ^ SW.L k) ≤ ε) → ∃ f ∈ F, x - f ∈ W := by
  classical
  intro W hW
  by_contra hcon
  -- a sequence in smaller and smaller sets whose differences avoid `W`
  have hbad : ∀ (i : ℕ) (F : Finset ℝ), ∃ x : ℝ,
      (∀ k, dint (x / 2 ^ SW.L k) ≤ (1 : ℝ) / (8 * (i + 1))) ∧ ∀ f ∈ F, x - f ∉ W := by
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
  have hsmall : ∀ i k, dint (x i / 2 ^ SW.L k) ≤ (1 : ℝ) / (8 * (i + 1)) := fun i k => (hh i (g i)).1 k
  have hsep : ∀ j n, j < n → x n - x j ∉ W := fun j n hjn => (hh n (g n)).2 _ (hmem j n hjn)
  -- the widths
  let P : ℕ → ℕ → Prop := fun k v => ∀ i, dint (x i / 2 ^ SW.L k) ≤ ((2 : ℝ) ^ (v + 3))⁻¹
  have hP0 : ∀ k, P k 0 := by
    intro k i
    refine (hsmall i k).trans ?_
    have h1 : (8 : ℝ) ≤ 8 * (i + 1) := by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have e1 : ((2 : ℝ) ^ (0 + 3))⁻¹ = 1 / 8 := by norm_num
    rw [e1]
    exact one_div_le_one_div_of_le (by norm_num) h1
  have hPmono : ∀ k a b, a ≤ b → P k b → P k a := by
    intro k a b hab h i
    refine (h i).trans (inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (by omega)))
  set v : ℕ → ℕ := fun k => Nat.findGreatest (P k) (min (SW.w0 k) k) with hvdef
  have hv : ∀ k, v k ≤ min (SW.w0 k) k := fun k => Nat.findGreatest_le _
  have hPv : ∀ k, P k (v k) := fun k => Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (hP0 k)
  have hvtop : ∀ t : ℕ, ∀ᶠ k in atTop, t ≤ v k := by
    intro t
    have h1 : ∀ᶠ k : ℕ in atTop, ∀ i ∈ Finset.range (2 ^ t), dint (x i / 2 ^ SW.L k) ≤ ((2 : ℝ) ^ (t + 3))⁻¹ := by
      refine (eventually_all_finset _).2 fun i _ => ?_
      have h2 : Tendsto (fun k : ℕ => |x i| * ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).const_mul |x i|
        rwa [mul_zero] at this
      refine (h2.eventually_le_const (by positivity : (0 : ℝ) < ((2 : ℝ) ^ (t + 3))⁻¹)).mono fun k hk => ?_
      refine (dint_le_abs _).trans (le_trans ?_ hk)
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ SW.L k), div_eq_mul_inv, inv_pow]
      refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two ?_)) (abs_nonneg _)
      have := L_big k; omega
    filter_upwards [h1, eventually_ge_atTop t, SW.w0_top.eventually (eventually_ge_atTop t)] with k hk hkt hkw
    refine Nat.le_findGreatest (le_min hkw hkt) fun i => ?_
    by_cases hi : i < 2 ^ t
    · exact hk i (Finset.mem_range.2 hi)
    · refine (hsmall i k).trans ?_
      have h2 : (2 : ℝ) ^ t ≤ i + 1 := by
        have : 2 ^ t ≤ i + 1 := by omega
        exact_mod_cast this
      rw [one_div]
      refine inv_anti₀ (by positivity) ?_
      rw [pow_add]
      have : (2 : ℝ) ^ 3 = 8 := by norm_num
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  -- widths that grow by at most one at a time
  obtain ⟨w, hw0, hwS⟩ : ∃ w : ℕ → ℕ, w 0 = 0 ∧ ∀ k, w (k + 1) = min (w k + 1) (v (k + 1)) :=
    ⟨fun k => Nat.rec 0 (fun j prev => min (prev + 1) (v (j + 1))) k, rfl, fun _ => rfl⟩
  have hwv : ∀ k, w k ≤ v k := by
    intro k
    cases k with
    | zero => rw [hw0]; exact Nat.zero_le _
    | succ k => rw [hwS]; exact min_le_right _ _
  have hw : Adm w := by
    refine ⟨fun k => (hwv k).trans ((hv k).trans (min_le_left _ _)),
      fun k => (hwv k).trans ((hv k).trans (min_le_right _ _)), fun k => ?_⟩
    rw [hwS]; exact min_le_left _ _
  have hPw : ∀ k, P k (w k) := fun k => hPmono k _ _ (hwv k) (hPv k)
  have htop : Tendsto w atTop atTop := by
    refine tendsto_atTop.2 fun t => ?_
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hvtop t)
    have hstep : ∀ i, min i t ≤ w (K + i) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have e : K + (i + 1) = K + i + 1 := by omega
        rw [e, hwS]
        have := hK (K + i + 1) (by omega)
        omega
    refine eventually_atTop.2 ⟨K + t, fun k hk => ?_⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (show K ≤ k by omega)
    have := hstep i
    omega
  -- the whole sequence is totally bounded
  obtain ⟨V, hVN, hsym, hsum⟩ := eight N hhalf W hW
  have h0V : (0 : ℝ) ∈ V := mem_of_mem_nhds (heu hVN)
  have hYtb := YsetW_tb hS w hw N hhalf heu (fun d hd => hA _ (inA_of_CdigW w hw htop d hd))
  obtain ⟨G, hG⟩ := hYtb V hVN
  obtain ⟨H, hH⟩ := tb_interval N heu (2 ^ SW.L 0 + 1) V hVN
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

omit S

/-- **A sufficient condition for rigidity.** -/
theorem rig_of_avoids_seq (L w : ℕ → ℕ) (hL : StrictMono L) (h2 : 2 ≤ L 0) (hw : Tendsto w atTop atTop)
    (hS : ∀ p0 N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∀ k m p q : ℕ, p < p0 → n < m → q + n ^ 2 = m ^ 2 + p →
      L k ≤ q + w k → q < L k → False) :
    Rig (dyseq L) := by
  intro γ hg heu htb W hW
  letI : SW := ⟨L, w, hL, h2, hw⟩
  have h := rig_of_avoids hS (@nhds ℝ γ 0) (group_half γ hg) heu htb W hW
  obtain ⟨ε, hε, F, hF⟩ := h
  refine ⟨ε, hε, F, fun x hx => hF x fun k => ?_⟩
  rw [← dyseq_mul]
  exact hx k

end Three
end PVG
