import Mathlib
import LeanCheck.PVGTwoServed

/-!
# PVGtwo, Section 7: a servable set together with one point (Lean check)

Scope. `Lv k = L_{k+1}` of the article, `dlt2 k = 2^{-Lv k}`, the window at level `k` is `[Lv k - (k+1), Lv k)`, and
`sT m = 2^((m+1)^2)`. `Cdig d` says that the binary digits `d` vanish at the forced positions; the digit with index `j` has
weight `2^{-(j+1)}`. `Yset` is the set of finite sums of powers of two whose exponents avoid all windows.

* `inA_of_Cdig` : the numbers with allowed digits belong to `A(δ)`;
* `Yset_rep` : every element of `Yset` equals `a s_n` with `a` having allowed digits that vanish at the first `M` places;
* `Yset_tb` : if `aS` is totally bounded for all these `a`, then `Yset` is totally bounded;
* `near_Yset` : a real whose distances to the integers after division by `2^{Lv k}` are small enough lies near `Y - Y`;
* `exists_cover` : there is `c` such that every real `x` is within such distances of some `c s_n`;
* `exists_point_unservable` : no non-precompact group topology below the usual one makes `aS`, `a ∈ A(δ)`, and `cS`
  totally bounded.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set
open scoped Pointwise

namespace PVG
namespace Two
open Q95 Lac

/-! ## The sequence -/

def ell : ℕ → ℕ
  | 0 => 8
  | k + 1 => (ell k ^ 2 + ell k) ^ 2

def Lv (k : ℕ) : ℕ := ell k ^ 2 + ell k

lemma ell_succ (k : ℕ) : ell (k + 1) = Lv k ^ 2 := rfl

lemma Lv_def (k : ℕ) : Lv k = ell k ^ 2 + ell k := rfl

lemma ell_ge (k : ℕ) : 8 ≤ ell k := by
  induction k with
  | zero => simp [ell]
  | succ k ih =>
    have h1 : 8 ≤ ell k ^ 2 + ell k := le_trans ih (Nat.le_add_left _ _)
    show 8 ≤ (ell k ^ 2 + ell k) ^ 2
    exact h1.trans (Nat.le_self_pow two_ne_zero _)

lemma Lv_ge (k : ℕ) : 72 ≤ Lv k := by
  have h := ell_ge k
  rw [Lv_def]; nlinarith

lemma Lv_pow4 (k : ℕ) : Lv k ^ 4 ≤ Lv (k + 1) := by
  rw [Lv_def (k + 1), ell_succ]
  have e : Lv k ^ 4 = (Lv k ^ 2) ^ 2 := by ring
  rw [e]; exact Nat.le_add_right _ _

lemma Lv_double (k : ℕ) : 2 * Lv k ≤ Lv (k + 1) := by
  refine le_trans ?_ (Lv_pow4 k)
  have h := Lv_ge k
  have h3 : 2 ≤ Lv k ^ 3 := le_trans (by omega) (Nat.le_self_pow three_ne_zero _)
  calc 2 * Lv k ≤ Lv k ^ 3 * Lv k := Nat.mul_le_mul_right _ h3
    _ = Lv k ^ 4 := by ring

lemma Lv_mono : Monotone Lv :=
  monotone_nat_of_le_succ fun k => le_trans (by omega) (Lv_double k)

lemma Lv_two_pow (k : ℕ) : 72 * 2 ^ k ≤ Lv k := by
  induction k with
  | zero => simpa using Lv_ge 0
  | succ k ih =>
    have := Lv_double k
    rw [pow_succ]; omega

lemma Lv_big (k : ℕ) : 2 * k + 20 ≤ Lv k := by
  have h1 := Lv_two_pow k
  have h2 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  omega

/-- `Lv j - (j+1)` increases with `j`. -/
lemma Lv_gap {i j : ℕ} (h : i < j) : Lv i + j + 20 ≤ Lv j := by
  have h1 : Lv i ≤ Lv (j - 1) := Lv_mono (by omega)
  have h2 := Lv_double (j - 1)
  have h3 : j - 1 + 1 = j := by omega
  rw [h3] at h2
  have h4 := Lv_big (j - 1)
  have h5 := Lv_ge (j - 1)
  omega

noncomputable def dlt2 (k : ℕ) : ℝ := ((2 : ℝ) ^ Lv k)⁻¹

lemma dlt2_ne (k : ℕ) : dlt2 k ≠ 0 := by unfold dlt2; positivity

lemma dlt2_tendsto : Tendsto dlt2 atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero (fun k => by unfold dlt2; positivity) (fun k => ?_) h1
  unfold dlt2
  rw [inv_pow]
  have : k ≤ Lv k := by have := Lv_big k; omega
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two this)

/-- The forced digit positions: the windows. -/
def Win : Set ℕ := {p | ∃ k, Lv k ≤ p + (k + 1) ∧ p < Lv k}

/-- The digits of `a` vanish where a window is hit by some `s_n`. -/
def Cdig (d : ℕ → Fin 2) : Prop := ∀ j n p : ℕ, p ∈ Win → j + 1 + p = n ^ 2 → d j = 0

lemma ofDigits_le_of_zero (d : ℕ → Fin 2) (J : ℕ) (h : ∀ i < J, d i = 0) : Real.ofDigits d ≤ ((2 : ℝ) ^ J)⁻¹ := by
  rw [Real.ofDigits_eq_sum_add_ofDigits d J]
  have h0 : ∑ i ∈ Finset.range J, Real.ofDigitsTerm d i = 0 :=
    Finset.sum_eq_zero fun i hi => by simp [Real.ofDigitsTerm, h i (Finset.mem_range.1 hi)]
  rw [h0, zero_add]
  exact_mod_cast mul_le_of_le_one_right (by positivity) (Real.ofDigits_le_one _)

lemma shift_digits (d : ℕ → Fin 2) (m : ℕ) :
    ∃ z : ℤ, (2 : ℝ) ^ m * Real.ofDigits d = z + Real.ofDigits (fun i => d (i + m)) := by
  obtain ⟨z, hz⟩ := sum_digits_int d m
  refine ⟨z, ?_⟩
  rw [Real.ofDigits_eq_sum_add_ofDigits d m, mul_add, hz]
  push_cast
  field_simp

lemma Cdig_bound (d : ℕ → Fin 2) (hd : Cdig d) (k n : ℕ) :
    dint (Real.ofDigits d * dlt2 k * 2 ^ (n ^ 2)) ≤ ((2 : ℝ) ^ (k + 1))⁻¹ := by
  have hLk := Lv_big k
  have hw : ∀ p, Lv k ≤ p + (k + 1) → p < Lv k → p ∈ Win := fun p h1 h2 => ⟨k, h1, h2⟩
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
    refine hd (i + m) n (Lv k - (i + 1)) (hw _ (by omega) (by omega)) (by omega)
  · push Not at hn
    refine (dint_le_abs _).trans ?_
    have h0 := Real.ofDigits_nonneg d
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg h0 (by unfold dlt2; positivity)) (by positivity))]
    -- the first `J` digits vanish
    set J := n ^ 2 + (k + 1) - Lv k with hJ
    have hdig : Real.ofDigits d ≤ ((2 : ℝ) ^ J)⁻¹ := by
      refine ofDigits_le_of_zero _ _ fun i hi => ?_
      exact hd i n (n ^ 2 - (i + 1)) (hw _ (by omega) (by omega)) (by omega)
    have hpow : (2 : ℝ) ^ (n ^ 2 + (k + 1)) ≤ 2 ^ J * 2 ^ Lv k := by
      rw [← pow_add]; exact pow_le_pow_right₀ one_le_two (by omega)
    unfold dlt2
    calc Real.ofDigits d * ((2 : ℝ) ^ Lv k)⁻¹ * 2 ^ (n ^ 2)
        ≤ ((2 : ℝ) ^ J)⁻¹ * ((2 : ℝ) ^ Lv k)⁻¹ * 2 ^ (n ^ 2) := by gcongr
      _ = 2 ^ (n ^ 2) * (2 ^ J * 2 ^ Lv k)⁻¹ := by rw [mul_inv]; ring
      _ ≤ 2 ^ (n ^ 2) * (2 ^ (n ^ 2 + (k + 1)))⁻¹ := by
          refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hpow) (by positivity)
      _ = ((2 : ℝ) ^ (k + 1))⁻¹ := by rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

lemma inA_of_Cdig (d : ℕ → Fin 2) (hd : Cdig d) : InA dlt2 sT (Real.ofDigits d) := by
  intro ε hε
  have h1 : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [h1.eventually (Iio_mem_nhds hε)] with k hk m
  have e1 : sT m = (2 : ℝ) ^ ((m + 1) ^ 2) := rfl
  rw [e1]
  refine (Cdig_bound d hd k (m + 1)).trans ?_
  have h2 : ((2 : ℝ) ^ (k + 1))⁻¹ ≤ ((2 : ℝ)⁻¹) ^ k := by
    rw [inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (by omega))
  exact h2.trans (le_of_lt hk)

/-! ## The set `Y` -/

def Yset : Set ℝ := {y | ∃ s : Finset ℕ, (∀ p ∈ s, p ∉ Win) ∧ y = ∑ p ∈ s, (2 : ℝ) ^ p}

/-- Every element of `Y` is `a s_n` with allowed digits of `a` that vanish at the first `M` places. -/
lemma Yset_rep (y : ℝ) (hy : y ∈ Yset) (M : ℕ) :
    ∃ d : ℕ → Fin 2, Cdig d ∧ (∀ j < M, d j = 0) ∧ ∃ m : ℕ, y = Real.ofDigits d * sT m := by
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
    · obtain ⟨k, hk1, hk2⟩ := hq
      have h1 : (n + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hgt 2
      have h2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      have hkK : K < k := by
        by_contra h
        have := Lv_mono (not_lt.1 h)
        omega
      have hell : n ^ 2 ≤ ell k := by
        have h3 : ell (K + 1) ≤ ell k := by
          have : ∀ a b, a ≤ b → ell a ≤ ell b := by
            intro a b hab
            refine monotone_nat_of_le_succ (f := ell) (fun i => ?_) hab
            have h4 : ell i ≤ Lv i := by rw [Lv_def]; exact Nat.le_add_left _ _
            rw [ell_succ]
            exact h4.trans (Nat.le_self_pow two_ne_zero _)
          exact this _ _ hkK
        rwa [ell_succ] at h3
      have hLk := Lv_def k
      have hkell : k + 1 + P < ell k := by
        have h5 : k + 1 ≤ ell k := by
          have : ∀ i, i + 8 ≤ ell i := by
            intro i
            induction i with
            | zero => simp [ell]
            | succ i ih =>
              have h6 : ell i + 1 ≤ ell (i + 1) := by
                rw [ell_succ]
                have h7 := Lv_def i
                have h8 := ell_ge i
                have h9 : ell i + 1 ≤ Lv i := by
                  rw [h7]
                  have : 1 ≤ ell i ^ 2 := Nat.one_le_pow _ _ (by omega)
                  omega
                exact h9.trans (Nat.le_self_pow two_ne_zero _)
              omega
          have := this k
          omega
        have h10 : P + k + 1 < n ^ 2 + 1 ∨ n ^ 2 < P + k + 1 := by omega
        have h11 : P < n := by omega
        have h12 : 2 * n ≤ n ^ 2 := by
          rw [sq]; exact Nat.mul_le_mul_right _ (by omega)
        rcases lt_or_ge k n with h13 | h13
        · omega
        · have : k + 1 + P < ell k := by
            have h14 : ∀ i, 2 * i + 8 ≤ ell i := by
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
            have := h14 k
            omega
          omega
      -- `m ^ 2` lies strictly between two consecutive squares
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

/-! ## `Y` is totally bounded -/

lemma Yset_tb (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : euclidNhds 0 ≤ N) (h : ∀ d : ℕ → Fin 2, Cdig d → Tb N (dil (Real.ofDigits d) Sset)) :
    Tb N Yset := by
  classical
  intro W hW
  obtain ⟨V, hVN, hsym, hsum⟩ := eight N hhalf W hW
  have h0V : (0 : ℝ) ∈ V := mem_of_mem_nhds (heu hVN)
  obtain ⟨η, hη, hηV⟩ := Metric.mem_nhds_iff.1 (heu hVN)
  have hball : ∀ x : ℝ, |x| < η → x ∈ V := fun x hx => hηV (by simpa [Metric.mem_ball, Real.dist_eq] using hx)
  let Ω := {d : ℕ → Fin 2 // Cdig d}
  have hΩc : IsClosed {d : ℕ → Fin 2 | Cdig d} := by
    have e1 : {d : ℕ → Fin 2 | Cdig d} =
        ⋂ (j : ℕ) (n : ℕ) (p : ℕ) (_ : p ∈ Win) (_ : j + 1 + p = n ^ 2), {d | d j = 0} := by
      ext d
      simp only [Cdig, mem_ofPred_eq, mem_iInter]
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
  obtain ⟨d, hd, hzero, m, hym⟩ := Yset_rep y hy M
  set d0' : ℕ → Fin 2 := fun j => if j < M then d0.1 j else 0 with hd0'
  set d1 : ℕ → Fin 2 := fun j => if j < M then d0.1 j else d j with hd1
  have hc0 : Cdig d0' := by
    intro j n p hp hj
    simp only [hd0']
    split
    · exact d0.2 j n p hp hj
    · rfl
  have hc1 : Cdig d1 := by
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

/-! ## Reals near `Y - Y` -/

lemma bits (W q : ℕ) (h : q < 2 ^ W) : ∃ s : Finset ℕ, s ⊆ Finset.range W ∧ q = ∑ p ∈ s, 2 ^ p := by
  induction W generalizing q with
  | zero => exact ⟨∅, Finset.empty_subset _, by simpa using h⟩
  | succ W ih =>
    by_cases hq : q < 2 ^ W
    · obtain ⟨s, hs, e⟩ := ih q hq
      exact ⟨s, hs.trans (Finset.range_mono (Nat.le_succ W)), e⟩
    · have h2 : q - 2 ^ W < 2 ^ W := by rw [pow_succ] at h; omega
      obtain ⟨s, hs, e⟩ := ih _ h2
      have hW : W ∉ s := fun hc => by simpa using Finset.mem_range.1 (hs hc)
      refine ⟨insert W s, Finset.insert_subset (Finset.mem_range.2 (Nat.lt_succ_self W))
        (hs.trans (Finset.range_mono (Nat.le_succ W))), ?_⟩
      rw [Finset.sum_insert hW, ← e]; omega

/-- A multiple of `2^{Lv k}` below `2^{Lv (k+1) - (k+3)}` is a sum of powers of two outside the windows. -/
lemma block (k a : ℕ) (hdvd : 2 ^ Lv k ∣ a) (hlt : a < 2 ^ (Lv (k + 1) - (k + 3))) :
    ∃ s : Finset ℕ, (∀ p ∈ s, Lv k ≤ p ∧ p < Lv (k + 1) - (k + 3)) ∧ a = ∑ p ∈ s, 2 ^ p := by
  obtain ⟨q, rfl⟩ := hdvd
  have hgap : Lv k + (k + 1) + 20 ≤ Lv (k + 1) := Lv_gap (Nat.lt_succ_self k)
  have hq : q < 2 ^ (Lv (k + 1) - (k + 3) - Lv k) := by
    have e1 : 2 ^ (Lv (k + 1) - (k + 3)) = 2 ^ Lv k * 2 ^ (Lv (k + 1) - (k + 3) - Lv k) := by
      rw [← pow_add]; congr 1; omega
    rw [e1] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  obtain ⟨s, hs, e⟩ := bits _ q hq
  refine ⟨s.image (fun p => Lv k + p), fun p hp => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
    have := Finset.mem_range.1 (hs hj)
    omega
  · rw [Finset.sum_image (fun x _ y _ h => Nat.add_left_cancel h), e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => (pow_add _ _ _).symm

lemma block_notWin (k p : ℕ) (h1 : Lv k ≤ p) (h2 : p < Lv (k + 1) - (k + 3)) : p ∉ Win := by
  rintro ⟨j, hj1, hj2⟩
  rcases le_or_gt j k with h | h
  · have := Lv_mono h
    omega
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
    · rw [show j = k + 1 from h'.symm] at hj1
      omega
    · have := Lv_gap (show k + 1 < j from h')
      omega

/-- A real that is close enough to `2^{Lv k} ℤ` at every level lies near `Y - Y`. -/
lemma near_Yset (z : ℝ) (hz : ∀ k, dint (z / 2 ^ Lv k) ≤ ((2 : ℝ) ^ (k + 4))⁻¹) :
    ∃ y1 ∈ Yset, ∃ y2 ∈ Yset, |z - (y1 - y2)| ≤ 2 ^ Lv 0 + 1 := by
  classical
  set z' : ℤ := round z with hz'
  have hzz : |z - z'| ≤ 1 / 2 := abs_sub_round z
  set t : ℕ → ℤ := fun k => z' - round ((z' : ℝ) / 2 ^ Lv k) * 2 ^ Lv k with ht
  have hpos : ∀ k, (0 : ℝ) < 2 ^ Lv k := fun k => by positivity
  have htb : ∀ k, |t k| ≤ 2 ^ (Lv k - (k + 3)) := by
    intro k
    have hL := Lv_big k
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
    have h3 : (|t k| : ℝ) ≤ 2 ^ (Lv k - (k + 3)) := by
      rw [h2]
      have h4 := mul_le_mul_of_nonneg_left (h1.trans (add_le_add (hz k) le_rfl)) (hpos k).le
      refine h4.trans ?_
      have e2 : (2 : ℝ) ^ Lv k = 2 ^ (Lv k - (k + 3)) * 2 ^ (k + 3) := by
        rw [← pow_add]; congr 1; omega
      have e3 : (2 : ℝ) ^ (k + 4) = 2 ^ (k + 3) * 2 := by rw [← pow_succ]
      have e4 : (2 : ℝ) ^ Lv k * (((2 : ℝ) ^ (k + 4))⁻¹ + (1 / 2) / 2 ^ Lv k) =
          2 ^ (Lv k - (k + 3)) / 2 + 1 / 2 := by
        rw [mul_add]
        congr 1
        · rw [e2, e3]; field_simp
        · field_simp
      rw [e4]
      have h5 : (1 : ℝ) ≤ 2 ^ (Lv k - (k + 3)) := one_le_pow₀ one_le_two
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
  have hult : ∀ k, (u k).natAbs < 2 ^ (Lv (k + 1) - (k + 3)) := by
    intro k
    have hgap : Lv k + (k + 1) + 20 ≤ Lv (k + 1) := Lv_gap (Nat.lt_succ_self k)
    have h1 := htb (k + 1)
    have h2 := htb k
    have h3 : |u k| ≤ |t (k + 1)| + |t k| := abs_sub _ _
    have h4 : (2 : ℤ) ^ (Lv (k + 1) - (k + 1 + 3)) + 2 ^ (Lv k - (k + 3)) < 2 ^ (Lv (k + 1) - (k + 3)) := by
      have e1 : (2 : ℤ) ^ (Lv (k + 1) - (k + 3)) = 2 ^ (Lv (k + 1) - (k + 1 + 3)) * 2 := by
        rw [← pow_succ]; congr 1; omega
      have h5 : (2 : ℤ) ^ (Lv k - (k + 3)) < 2 ^ (Lv (k + 1) - (k + 1 + 3)) :=
        pow_lt_pow_right₀ one_lt_two (by omega)
      rw [e1]; omega
    have h6 : ((u k).natAbs : ℤ) < 2 ^ (Lv (k + 1) - (k + 3)) := by
      rw [Int.natCast_natAbs]; omega
    exact_mod_cast h6
  have hblock : ∀ k, ∃ s : Finset ℕ, (∀ p ∈ s, Lv k ≤ p ∧ p < Lv (k + 1) - (k + 3)) ∧
      (u k).natAbs = ∑ p ∈ s, 2 ^ p := by
    intro k
    refine block k _ ?_ (hult k)
    have := Int.natAbs_dvd_natAbs.2 (hudvd k)
    rwa [Int.natAbs_pow] at this
  choose s hs hsum using hblock
  -- a level beyond which `t` equals `z'`
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
  have hY : ∀ A : Finset ℕ, (∑ k ∈ A, (((u k).natAbs : ℕ) : ℝ)) ∈ Yset := by
    intro A
    refine ⟨A.biUnion s, fun p hp => ?_, ?_⟩
    · obtain ⟨k, _, hpk⟩ := Finset.mem_biUnion.1 hp
      exact block_notWin k p (hs k p hpk).1 (hs k p hpk).2
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
    have h3 : |(t 0 : ℝ)| ≤ 2 ^ (Lv 0 - (0 + 3)) := by exact_mod_cast h2
    exact h3.trans (pow_le_pow_right₀ one_le_two (Nat.sub_le _ _))
  have e1 : z - ((z' - t 0 : ℤ) : ℝ) = (z - z') + t 0 := by push_cast; ring
  rw [e1]
  refine (abs_add_le _ _).trans ?_
  linarith

/-! ## The point `c` -/

/-- Offset of the bits that belong to level `k`. -/
def off : ℕ → ℕ
  | 0 => 0
  | k + 1 => off k + (k + 5)

lemma any_bits (N : ℕ) (f : ℕ → Bool) : ∃ t < 2 ^ N, ∀ i < N, t.testBit i = f i := by
  induction N with
  | zero => exact ⟨0, by simp, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ N ih =>
    obtain ⟨t, ht, h⟩ := ih
    refine ⟨2 ^ N * (f N).toNat + t, ?_, fun i hi => ?_⟩
    · have h1 : (f N).toNat ≤ 1 := Bool.toNat_le _
      have h2 : 2 ^ N * (f N).toNat ≤ 2 ^ N * 1 := Nat.mul_le_mul_left _ h1
      rw [pow_succ]; omega
    · rw [Nat.testBit_two_pow_mul_add _ ht]
      by_cases hiN : i < N
      · rw [if_pos hiN, h i hiN]
      · have : i = N := by omega
        subst this
        rw [if_neg hiN, Nat.sub_self]
        cases f i <;> rfl

lemma level_bits (K : ℕ) (f : ℕ → ℕ → Bool) :
    ∃ τ < 2 ^ off (K + 1), ∀ k ≤ K, ∀ i < k + 5, τ.testBit (off k + i) = f k i := by
  induction K with
  | zero =>
    obtain ⟨t, ht, h⟩ := any_bits 5 (f 0)
    refine ⟨t, by simpa [off] using ht, fun k hk i hi => ?_⟩
    have : k = 0 := by omega
    subst this
    simpa [off] using h i (by omega)
  | succ K ih =>
    obtain ⟨τ, hτ, h⟩ := ih
    obtain ⟨t, ht, ht'⟩ := any_bits (K + 6) (f (K + 1))
    have e1 : off (K + 1 + 1) = off (K + 1) + (K + 6) := by
      show off (K + 1) + (K + 1 + 5) = _
      omega
    refine ⟨2 ^ off (K + 1) * t + τ, ?_, fun k hk i hi => ?_⟩
    · rw [e1, pow_add]
      calc 2 ^ off (K + 1) * t + τ < 2 ^ off (K + 1) * t + 2 ^ off (K + 1) := by omega
        _ = 2 ^ off (K + 1) * (t + 1) := by ring
        _ ≤ 2 ^ off (K + 1) * 2 ^ (K + 6) := Nat.mul_le_mul_left _ ht
    · rw [Nat.testBit_two_pow_mul_add _ hτ]
      have hmono : ∀ a b, a ≤ b → off a ≤ off b := fun a b hab =>
        monotone_nat_of_le_succ (f := off) (fun n => Nat.le_add_right _ _) hab
      rcases eq_or_lt_of_le hk with rfl | hlt
      · rw [if_neg (by omega), show off (K + 1) + i - off (K + 1) = i by omega]
        exact ht' i (by omega)
      · have h1 : off k + i < off (K + 1) := by
          have h2 : off (k + 1) = off k + (k + 5) := rfl
          have h3 := hmono (k + 1) (K + 1) (by omega)
          omega
        rw [if_pos h1]
        exact h k (by omega) i hi

lemma few (K : ℕ) : 2 ^ off (K + 1) ≤ Lv K := by
  induction K with
  | zero =>
    have h := Lv_ge 0
    have e1 : off (0 + 1) = 5 := rfl
    rw [e1]; omega
  | succ K ih =>
    have e1 : off (K + 1 + 1) = off (K + 1) + (K + 6) := by
      show off (K + 1) + (K + 1 + 5) = _
      omega
    have h1 := Lv_two_pow K
    have h2 := Lv_ge K
    have h3 : 2 ^ (K + 6) ≤ Lv K ^ 3 := by
      have h4 : 2 ^ (K + 6) ≤ Lv K * Lv K := by
        have e2 : 2 ^ (K + 6) = 64 * 2 ^ K := by rw [pow_add]; ring
        rw [e2]
        exact Nat.mul_le_mul (by omega) (by omega)
      have e3 : Lv K ^ 3 = Lv K * Lv K * Lv K := by ring
      rw [e3]
      exact h4.trans (Nat.le_mul_of_pos_right _ (by omega))
    rw [e1, pow_add]
    refine le_trans (Nat.mul_le_mul ih h3) (le_trans (le_of_eq ?_) (Lv_pow4 K))
    ring

/-- The digit with index `j` of `c` is `1`. -/
def Cone (j : ℕ) : Prop :=
  ∃ K τ k i, τ < 2 ^ off (K + 1) ∧ k ≤ K ∧ i < k + 5 ∧ j + Lv k = (Lv K + τ) ^ 2 + i ∧ τ.testBit (off k + i) = true

/-- The blocks do not collide. -/
lemma blocks_unique {j K τ k i K' τ' k' i' : ℕ} (hτ : τ < 2 ^ off (K + 1)) (hk : k ≤ K) (hi : i < k + 5)
    (h : j + Lv k = (Lv K + τ) ^ 2 + i) (hτ' : τ' < 2 ^ off (K' + 1)) (hk' : k' ≤ K') (hi' : i' < k' + 5)
    (h' : j + Lv k' = (Lv K' + τ') ^ 2 + i') : K = K' ∧ τ = τ' ∧ k = k' ∧ i = i' := by
  have hsep : ∀ {K τ k i K' τ' k' i' : ℕ}, τ < 2 ^ off (K + 1) → k ≤ K → i < k + 5 →
      j + Lv k = (Lv K + τ) ^ 2 + i → k' ≤ K' → j + Lv k' = (Lv K' + τ') ^ 2 + i' → K < K' → False := by
    intro K τ k i K' τ' k' i' hτ hk hi h hk' h' hlt
    have hf := few K
    have hL := Lv_ge K
    have hLK := Lv_big K
    have hn : (Lv K + τ) ^ 2 ≤ 4 * Lv K ^ 2 := by
      have : Lv K + τ ≤ 2 * Lv K := by omega
      have := Nat.pow_le_pow_left this 2
      rw [mul_pow] at this
      simpa using this
    have h1 : Lv K ^ 4 ≤ Lv K' := (Lv_pow4 K).trans (Lv_mono (Nat.succ_le_of_lt hlt))
    have h2 : Lv K' ^ 2 ≤ (Lv K' + τ') ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right _ _) 2
    have h3 : Lv k' ≤ Lv K' := Lv_mono hk'
    have h4 : 2 * Lv K' ≤ Lv K' ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul_right _ (le_trans (by omega) (Lv_ge K'))
    have h5 : 4 * Lv K ^ 2 + K + 5 < Lv K ^ 4 := by
      have e1 : Lv K ^ 4 = Lv K ^ 2 * Lv K ^ 2 := by ring
      have h6 : 72 * 72 ≤ Lv K ^ 2 := by rw [sq]; exact Nat.mul_le_mul hL hL
      have h7 : 5 * Lv K ^ 2 ≤ Lv K ^ 2 * Lv K ^ 2 := Nat.mul_le_mul_right _ (le_trans (by omega) h6)
      have h8 : Lv K ≤ Lv K ^ 2 := Nat.le_self_pow two_ne_zero _
      omega
    omega
  have hKK : K = K' := by
    rcases lt_trichotomy K K' with h0 | h0 | h0
    · exact absurd (hsep hτ hk hi h hk' h' h0) id
    · exact h0
    · exact absurd (hsep hτ' hk' hi' h' hk h h0) id
  subst hKK
  have hf := few K
  have hLK := Lv_big K
  have h1 : Lv k ≤ Lv K := Lv_mono hk
  have h2 : Lv k' ≤ Lv K := Lv_mono hk'
  have hsame : ∀ a b : ℕ, a < b → (Lv K + a) ^ 2 + (2 * Lv K + 1) ≤ (Lv K + b) ^ 2 := by
    intro a b hab
    have h3 : (Lv K + a + 1) ^ 2 ≤ (Lv K + b) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h4 : (Lv K + a + 1) ^ 2 = (Lv K + a) ^ 2 + 2 * (Lv K + a) + 1 := by ring
    omega
  have hττ : τ = τ' := by
    rcases lt_trichotomy τ τ' with h0 | h0 | h0
    · have := hsame τ τ' h0
      omega
    · exact h0
    · have := hsame τ' τ h0
      omega
  subst hττ
  have hkk : k = k' := by
    rcases lt_trichotomy k k' with h0 | h0 | h0
    · have := Lv_gap h0
      omega
    · exact h0
    · have := Lv_gap h0
      omega
  subst hkk
  exact ⟨rfl, rfl, rfl, by omega⟩

/-- There is `c` such that every real is, at every level, close to a point `c s_n`. -/
theorem exists_cover : ∃ c : ℝ, ∀ x : ℝ, ∃ m : ℕ, ∀ k, dint ((x - c * sT m) / 2 ^ Lv k) ≤ ((2 : ℝ) ^ (k + 4))⁻¹ := by
  classical
  set e : ℕ → Fin 2 := fun j => if Cone j then 1 else 0 with he
  refine ⟨Real.ofDigits e, fun x => ?_⟩
  set c := Real.ofDigits e with hc
  have hc0 : 0 ≤ c := Real.ofDigits_nonneg _
  have hc1 : c ≤ 1 := Real.ofDigits_le_one _
  obtain ⟨K, hK⟩ : ∃ K : ℕ, |x| ≤ K := exists_nat_ge _
  set θ : ℕ → ℝ := fun k => Int.fract (x / 2 ^ Lv k) with hθ
  set f : ℕ → ℕ → Bool := fun k i => decide (Real.digits (θ k) 2 i = 1) with hf
  obtain ⟨τ, hτ, hbit⟩ := level_bits K f
  set n := Lv K + τ with hn
  have hLK := Lv_big K
  have hfew := few K
  have hn1 : 1 ≤ n := by omega
  have hsT : sT (n - 1) = (2 : ℝ) ^ (n ^ 2) := by
    show (2 : ℝ) ^ ((n - 1 + 1) ^ 2) = _
    congr 2; omega
  have hn2 : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero _
  refine ⟨n - 1, fun k => ?_⟩
  rw [hsT]
  have hpos : (0 : ℝ) < 2 ^ Lv k := by positivity
  rcases le_or_gt k K with hk | hk
  · have hLk : Lv k ≤ Lv K := Lv_mono hk
    set M := n ^ 2 - Lv k with hM
    have hMn : (2 : ℝ) ^ (n ^ 2) = 2 ^ M * 2 ^ Lv k := by rw [← pow_add]; congr 1; omega
    obtain ⟨z, hz⟩ := shift_digits e M
    have hθ01 : θ k ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    have hθd : Real.ofDigits (Real.digits (θ k) 2) = θ k := Real.ofDigits_digits one_lt_two hθ01
    have hagree : ∀ i < k + 5, (fun i => e (i + M)) i = Real.digits (θ k) 2 i := by
      intro i hi
      have hpos' : i + M + Lv k = (Lv K + τ) ^ 2 + i := by rw [← hn]; omega
      have hiff : Cone (i + M) ↔ τ.testBit (off k + i) = true := by
        constructor
        · rintro ⟨K', τ', k', i', h1, h2, h3, h4, h5⟩
          obtain ⟨rfl, rfl, rfl, rfl⟩ := blocks_unique hτ hk hi hpos' h1 h2 h3 h4
          exact h5
        · intro h
          exact ⟨K, τ, k, i, hτ, hk, hi, hpos', h⟩
      have htwo : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
      have hb := hbit k hk i hi
      show e (i + M) = _
      simp only [he]
      rcases htwo (Real.digits (θ k) 2 i) with h | h
      · rw [h, if_neg]
        rw [hiff, hb, hf]
        simp [h]
      · rw [h, if_pos]
        rw [hiff, hb, hf]
        simp [h]
    have hclose : |θ k - Real.ofDigits (fun i => e (i + M))| ≤ ((2 : ℝ) ^ (k + 5))⁻¹ := by
      have h1 := Real.abs_ofDigits_sub_ofDigits_le (b := 2) (x := Real.digits (θ k) 2)
        (y := fun i => e (i + M)) (n := k + 5) (fun i hi => (hagree i hi).symm)
      rw [hθd] at h1
      exact_mod_cast h1
    have e1 : (x - c * 2 ^ (n ^ 2)) / 2 ^ Lv k =
        (θ k - Real.ofDigits (fun i => e (i + M))) - ((z - ⌊x / 2 ^ Lv k⌋ : ℤ) : ℝ) := by
      have h1 : (x - c * 2 ^ (n ^ 2)) / 2 ^ Lv k = x / 2 ^ Lv k - 2 ^ M * c := by
        rw [hMn]; field_simp
      have h2 : x / 2 ^ Lv k = ⌊x / 2 ^ Lv k⌋ + θ k := (Int.floor_add_fract _).symm
      rw [h1, hc, hz]
      conv_lhs => rw [h2]
      push_cast
      ring
    rw [e1, dint_sub_int]
    refine (dint_le_abs _).trans (hclose.trans ?_)
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (by omega))
  · have hLk := Lv_big k
    have h4 : Lv K ^ 4 ≤ Lv k := (Lv_pow4 K).trans (Lv_mono (Nat.succ_le_of_lt hk))
    have hL72 := Lv_ge K
    have hn4 : n ^ 2 ≤ 4 * Lv K ^ 2 := by
      have : n ≤ 2 * Lv K := by omega
      have := Nat.pow_le_pow_left this 2
      rw [mul_pow] at this
      simpa using this
    have h8 : 8 * Lv K ^ 2 ≤ Lv K ^ 4 := by
      have e1 : Lv K ^ 4 = Lv K ^ 2 * Lv K ^ 2 := by ring
      have h6 : 72 * 72 ≤ Lv K ^ 2 := by rw [sq]; exact Nat.mul_le_mul hL72 hL72
      rw [e1]
      exact Nat.mul_le_mul_right _ (le_trans (by omega) h6)
    have hbig : n ^ 2 + (k + 5) ≤ Lv k := by omega
    have hxk : K + (k + 5) ≤ Lv k := by omega
    refine (dint_le_abs _).trans ?_
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have h1 : |x - c * 2 ^ (n ^ 2)| ≤ |x| + 2 ^ (n ^ 2) := by
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      rw [abs_of_nonneg (mul_nonneg hc0 (by positivity))]
      exact mul_le_of_le_one_left (by positivity) hc1
    have h2 : |x| ≤ 2 ^ K := by
      have h3 : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast (Nat.lt_two_pow_self).le
      linarith
    have h5 : ∀ a : ℕ, a + (k + 5) ≤ Lv k → (2 : ℝ) ^ a ≤ ((2 : ℝ) ^ (k + 4))⁻¹ * 2 ^ Lv k / 2 := by
      intro a ha
      have e1 : (2 : ℝ) ^ (a + (k + 5)) ≤ 2 ^ Lv k := pow_le_pow_right₀ one_le_two ha
      have e2 : (2 : ℝ) ^ (a + (k + 5)) = 2 ^ a * (2 ^ (k + 4) * 2) := by
        rw [← pow_succ, ← pow_add]
      rw [e2] at e1
      rw [le_div_iff₀ two_pos, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      nlinarith
    have h6 := h5 K hxk
    have h7 := h5 (n ^ 2) hbig
    linarith

/-! ## Conclusion -/

lemma tb_interval (N : Filter ℝ) (heu : euclidNhds 0 ≤ N) (B : ℝ) : Tb N (Icc (-B) B) := by
  intro W hW
  obtain ⟨η, hη, hηW⟩ := Metric.mem_nhds_iff.1 (heu hW)
  have hcov : Icc (-B) B ⊆ ⋃ f : ℝ, Metric.ball f η :=
    fun x _ => mem_iUnion.2 ⟨x, Metric.mem_ball_self hη⟩
  obtain ⟨F, hF⟩ := isCompact_Icc.elim_finite_subcover (fun f : ℝ => Metric.ball f η)
    (fun _ => Metric.isOpen_ball) hcov
  refine ⟨F, fun y hy => ?_⟩
  obtain ⟨f, hf, h⟩ := mem_iUnion₂.1 (hF hy)
  refine ⟨f, hf, hηW ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  rwa [Metric.mem_ball, Real.dist_eq] at h

/-- The core: total boundedness of `aS`, `a ∈ C`, and of `cS` forces precompactness. -/
theorem point_core (c : ℝ)
    (hc : ∀ x : ℝ, ∃ m : ℕ, ∀ k, dint ((x - c * sT m) / 2 ^ Lv k) ≤ ((2 : ℝ) ^ (k + 4))⁻¹)
    (N : Filter ℝ) (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : euclidNhds 0 ≤ N) (hC : ∀ d : ℕ → Fin 2, Cdig d → Tb N (dil (Real.ofDigits d) Sset))
    (hcS : Tb N (dil c Sset)) : ∀ W ∈ N, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W := by
  classical
  intro W hW
  obtain ⟨V, hVN, hsym, hsum⟩ := eight N hhalf W hW
  have h0V : (0 : ℝ) ∈ V := mem_of_mem_nhds (heu hVN)
  obtain ⟨G, hG⟩ := Yset_tb N hhalf heu hC V hVN
  obtain ⟨F, hF⟩ := hcS V hVN
  obtain ⟨H, hH⟩ := tb_interval N heu (2 ^ Lv 0 + 1) V hVN
  refine ⟨(((H ×ˢ F) ×ˢ (G ×ˢ G)).image fun p => p.1.1 + p.1.2 + p.2.1 - p.2.2), fun x => ?_⟩
  obtain ⟨m, hm⟩ := hc x
  obtain ⟨y1, hy1, y2, hy2, herr⟩ := near_Yset (x - c * sT m) hm
  have hs : sT m ∈ Sset := by
    have := sign_mem_Sset (c := 1) (by simp) m
    rwa [one_mul] at this
  set err := x - c * sT m - (y1 - y2) with he
  obtain ⟨h, hh, v1, rfl⟩ : ∃ h ∈ H, ∃ v : V, h = err - v.1 := by
    obtain ⟨h, hh, hv⟩ := hH err (abs_le.1 herr)
    exact ⟨h, hh, ⟨err - h, hv⟩, by simp⟩
  obtain ⟨f, hf, hfv⟩ := hF (c * sT m) ⟨sT m, hs, rfl⟩
  obtain ⟨g1, hg1, hg1v⟩ := hG y1 hy1
  obtain ⟨g2, hg2, hg2v⟩ := hG y2 hy2
  refine ⟨(err - v1.1) + f + g1 - g2, Finset.mem_image.2 ⟨(((err - v1.1), f), (g1, g2)),
    Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨hh, hf⟩, Finset.mem_product.2 ⟨hg1, hg2⟩⟩, rfl⟩, ?_⟩
  have e1 : x - ((err - v1.1) + f + g1 - g2) =
      ((v1.1 + (c * sT m - f)) + ((y1 - g1) + -(y2 - g2))) + ((0 + 0) + (0 + 0)) := by
    rw [he]; ring
  rw [e1]
  exact hsum _ v1.2 _ hfv _ hg1v _ (hsym _ hg2v) _ h0V _ h0V _ h0V _ h0V

/-- **Theorem 7.8.** There is `c` such that no non-precompact group topology below the usual one makes all `aS`,
`a ∈ A(δ)`, and `cS` totally bounded; `A(δ)` itself is served by the locally quasi-convex topology `γ_δ`. -/
theorem exists_point_unservable : ∃ c : ℝ,
    (∀ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ → euclidNhds 0 ≤ @nhds ℝ γ 0 →
      (∀ a : ℝ, InA dlt2 sT a → Tb (@nhds ℝ γ 0) (dil a Sset)) → Tb (@nhds ℝ γ 0) (dil c Sset) →
      ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W) ∧
    (∀ a : ℝ, InA dlt2 sT a → Tb (@nhds ℝ (gamTop dlt2) 0) (dil a Sset)) ∧ Tendsto dlt2 atTop (euclidNhds 0) ∧
    gamTop dlt2 ≠ bohrTop := by
  obtain ⟨c, hc⟩ := exists_cover
  have h3 : Tendsto dlt2 atTop (euclidNhds 0) := dlt2_tendsto
  have h2 : ∀ a : ℝ, InA dlt2 sT a → Tb (@nhds ℝ (gamTop dlt2) 0) (dil a Sset) :=
    fun a ha => tb_gam dlt2 dlt2_tendsto a ha
  have h4 : gamTop dlt2 ≠ bohrTop :=
    gam_ne_bohr _ (infinite_range_of_tendsto dlt2 dlt2_ne dlt2_tendsto)
  refine ⟨c, fun γ hg heu hA hcS => ?_, h2, h3, h4⟩
  exact point_core c hc _ (group_half γ hg) heu (fun d hd => hA _ (inA_of_Cdig d hd)) hcS

end Two
end PVG
