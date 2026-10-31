import Mathlib
import LeanCheck.JACentral

/-!
# `CentralBound` from the two-term separation (final assembly)

`central_bound`: for `D ≥ 3`, `A ≥ 0` and `TwoTermSeparation A` there is `C > 0` with `CentralBound D C`.
-/

namespace LeanCheck
namespace JACentral2

open Finset JATransfer JAProduct JAProduct2 JAMulti JAFinal2 JAWindowQ JACenter JAAssemble JACentral

/-- The total mass of the seed kernel is `Q`. -/
lemma sum_kernq_delta (N Q : ℕ) [NeZero N] [NeZero Q] :
    ∑ x : ZMod N, kernq N Q (deltaSeed Q) x = (Q : ℝ) := by
  unfold kernq
  rw [JACenter.sum_kern]
  have h : ∀ r : ZMod Q, ‖∑ x : ZMod Q, ((deltaSeed Q x : ℝ) : ℂ) * ZMod.stdAddChar (r * x)‖ ^ 2 = 1 := by
    intro r
    have h0 : ∀ x : ZMod Q, ((deltaSeed Q x : ℝ) : ℂ) * ZMod.stdAddChar (r * x) = if x = 0 then 1 else 0 := by
      intro x
      by_cases hx : x = 0
      · subst hx; simp [deltaSeed]
      · simp [deltaSeed, hx]
    have h1 : ∑ x : ZMod Q, ((deltaSeed Q x : ℝ) : ℂ) * ZMod.stdAddChar (r * x) = 1 := by
      rw [Finset.sum_congr rfl (fun x _ => h0 x)]
      simp
    rw [h1]; simp
  simp [h, ZMod.card]

/-- The seed factor `S_0` is nonnegative and bounded by the total mass of the seeds. -/
lemma S0_le {N : ℕ} [NeZero N] (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (b n : ℕ → ℕ) [inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2))]
    (hQ : ∀ j, j < L → 25 * D ≤ (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ))
    (hQN : ∀ j, j < L → (b j) ^ ((n j) ^ 2) ∣ N) (A B : ZMod N → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x) :
    0 ≤ conv (conv A B) (Hs (Ftri N m) (klist N D L b n)) 0 / Hs (Ftri N m) (klist N D L b n) 0 ∧
      conv (conv A B) (Hs (Ftri N m) (klist N D L b n)) 0 / Hs (Ftri N m) (klist N D L b n) 0 ≤
        (∑ x, A x) * ∑ x, B x := by
  have hgood : ∀ K ∈ klist N D L b n, PD K ∧ (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 ∧ ∑ x, K x ≤ 30 * D / 7 := by
    intro K hK
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hK
    have hjL : j < L := List.mem_range.mp hj
    obtain ⟨h1, h2, h3⟩ := normK_props (N := N) D hD ((b j) ^ ((n j) ^ 2)) (hQ j hjL) (hQN j hjL)
    exact ⟨h1, normK_nonneg _ _, h2, h3⟩
  have hF0 : 1 ≤ Ftri N m 0 := by rw [Ftri_zero m hm h2m]
  have hH : PD (Hs (Ftri N m) (klist N D L b n)) :=
    Hs_PD (Ftri N m) (Ftri_PD m) _ (fun K hK => (hgood K hK).1)
  have hH1 := (Hs_atom (Ftri N m) (Ftri_nonneg m) hF0 (klist N D L b n)
    (fun K hK => ⟨(hgood K hK).2.1, (hgood K hK).2.2.1⟩)).2
  have hH0 : 0 < Hs (Ftri N m) (klist N D L b n) 0 := by linarith
  have hμ : ∀ x, 0 ≤ conv A B x := fun x => JAFinal.conv_nonneg' A B hA hB x
  have key := S0_bounds (conv A B) _ hμ hH hH0
  rw [sum_conv_total] at key
  exact key

lemma big_period (D : ℝ) (hD : 3 ≤ D) (β n : ℕ) (hβ : 2 ≤ β) (hn : ⌈D⌉₊ < n) :
    25 * D ≤ ((β ^ (n ^ 2) : ℕ) : ℝ) := by
  have h3 : 3 ≤ ⌈D⌉₊ := by
    have : (3 : ℝ) ≤ (⌈D⌉₊ : ℝ) := le_trans hD (Nat.le_ceil D)
    exact_mod_cast this
  have hDn : D ≤ (n : ℝ) := by
    have h1 : D ≤ (⌈D⌉₊ : ℝ) := Nat.le_ceil D
    have h2 : (⌈D⌉₊ : ℝ) ≤ n := by exact_mod_cast hn.le
    linarith
  have hn4 : 4 ≤ n := by omega
  have h1 : n < 2 ^ n := Nat.lt_pow_self (by norm_num)
  have h2 : 2 ^ (n + 5) ≤ 2 ^ (n ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h3' : 2 ^ (n ^ 2) ≤ β ^ (n ^ 2) := Nat.pow_le_pow_left hβ _
  have h4 : 25 * n ≤ β ^ (n ^ 2) := by
    have : 2 ^ (n + 5) = 32 * 2 ^ n := by rw [pow_add]; ring
    omega
  have h5 : (25 : ℝ) * n ≤ ((β ^ (n ^ 2) : ℕ) : ℝ) := by exact_mod_cast h4
  nlinarith

lemma pow_succ_sq_le (β : ℝ) (hβ : 1 ≤ β) (a : ℕ) (ha : 3 ≤ a) :
    β ^ ((a + 1) ^ 2) ≤ (β ^ (a ^ 2)) ^ 2 := by
  rw [← pow_mul]
  exact pow_le_pow_right₀ hβ (by nlinarith)

lemma final_arith (SA SB S0 F a b cs Cp E : ℝ) (hSA : SA ≤ E * a ^ 2) (hSB : SB ≤ E * b ^ 2)
    (hSA0 : 0 ≤ SA) (hSB0 : 0 ≤ SB) (hS0 : S0 ≤ cs) (hS00 : 0 ≤ S0) (hF : F ≤ Cp) (hF0 : 0 ≤ F)
    (hE : 0 ≤ E) (hcs : 0 ≤ cs) (hCp : 0 ≤ Cp) :
    2 * (SA * SB) * (S0 * F) ≤ 2 * (E * E) * cs * Cp * (a * b) ^ 2 := by
  have h1 : SA * SB ≤ (E * a ^ 2) * (E * b ^ 2) :=
    mul_le_mul hSA hSB hSB0 (by positivity)
  have h2 : S0 * F ≤ cs * Cp := mul_le_mul hS0 hF hF0 hcs
  have h3 : (SA * SB) * (S0 * F) ≤ ((E * a ^ 2) * (E * b ^ 2)) * (cs * Cp) :=
    mul_le_mul h1 h2 (mul_nonneg hS00 hF0) (by positivity)
  nlinarith [h3]

/-- **`CentralBound` from the two-term separation.** -/
theorem central_bound (D A : ℝ) (hD : 3 ≤ D) (hA : 0 ≤ A) (hP : JAClose.TwoTermSeparation A) :
    ∃ C : ℝ, 0 < C ∧ JAHeights.CentralBound D C := by
  classical
  obtain ⟨Cp, X₀, hCp, hprod⟩ := prod_f_bound D A hD hA hP
  have hD0 : 0 < D := by linarith
  have hsa3 : 3 ≤ JAHeights.sD D := by
    have : (3 : ℝ) ≤ (JAHeights.sD D : ℝ) := le_trans hD (Nat.le_ceil D)
    exact_mod_cast this
  refine ⟨2 * Real.exp (32 / 3) * ((((2 ^ ((JAHeights.sD D) ^ 2) : ℕ)) : ℝ) *
      (((3 ^ ((JAHeights.sD D) ^ 2) : ℕ)) : ℝ)) * Cp, by positivity, ?_⟩
  refine ⟨⌈X₀⌉₊, ?_⟩
  intro X na nb hX hbuf
  obtain ⟨hB2, hB3, h4a, h4b⟩ := hbuf
  unfold JAFinal2.CentralAt
  set sa : ℕ := JAHeights.sD D with hsa
  set Pa : ℕ := 2 ^ ((sa + na) ^ 2) with hPa
  set Pb : ℕ := 3 ^ ((sa + nb) ^ 2) with hPb
  have hPa4 : 4 ≤ Pa := by
    have : 2 ^ 2 ≤ 2 ^ ((sa + na) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by have h3 : 3 ≤ sa + na := (by omega); nlinarith)
    omega
  have hPb4 : 4 ≤ Pb := by
    have h1 : 2 ^ 2 ≤ 3 ^ 2 := by norm_num
    have h2 : 3 ^ 2 ≤ 3 ^ ((sa + nb) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by have h3 : 3 ≤ sa + nb := (by omega); nlinarith)
    omega
  have hPpos : 0 < Pa * Pb := by positivity
  haveI hNZ : NeZero (Pa * Pb) := ⟨hPpos.ne'⟩
  have hP16 : 16 ≤ Pa * Pb := by nlinarith
  have hY4 : 4 ≤ X + 1 + Pa + Pb := by omega
  have hY0 : 0 < X + 1 + Pa + Pb := by omega
  have hqY : (Pa * Pb / (X + 1 + Pa + Pb)) * (X + 1 + Pa + Pb) ≤ Pa * Pb := Nat.div_mul_le_self _ _
  obtain ⟨q, hq⟩ : ∃ q, q = Pa * Pb / (X + 1 + Pa + Pb) := ⟨_, rfl⟩
  rw [← hq] at hqY
  have hq4 : 4 * q ≤ Pa * Pb := by nlinarith
  have hPlt : Pa * Pb < (X + 1 + Pa + Pb) * (q + 1) := by rw [hq]; exact Nat.lt_mul_div_succ _ hY0
  have hm_le : q + 1 ≤ Pa * Pb := by omega
  have h2m : 2 * (q + 1) ≤ Pa * Pb := by omega
  -- real inequalities
  have hXr : (0 : ℝ) < X := by
    have : 4 * Pa ≤ X := h4a
    have : 0 < X := by omega
    exact_mod_cast this
  have hPar : ((Pa : ℕ) : ℝ) = (2 : ℝ) ^ ((sa + na) ^ 2) := by rw [hPa]; push_cast; ring
  have hPbr : ((Pb : ℕ) : ℝ) = (3 : ℝ) ^ ((sa + nb) ^ 2) := by rw [hPb]; push_cast; ring
  have hDXa : D * X < ((Pa : ℕ) : ℝ) ^ 2 := by
    have := pow_succ_sq_le 2 (by norm_num) (sa + na) (by omega)
    rw [hPar]
    exact lt_of_lt_of_le hB2 this
  have hDXb : D * X < ((Pb : ℕ) : ℝ) ^ 2 := by
    have := pow_succ_sq_le 3 (by norm_num) (sa + nb) (by omega)
    rw [hPbr]
    exact lt_of_lt_of_le hB3 this
  have hDXpos : 0 < D * X := by positivity
  have hDXP : D * X < (((Pa * Pb : ℕ)) : ℝ) := by
    push_cast
    have h1 : (D * X) * (D * X) < (((Pa : ℕ) : ℝ) ^ 2) * (((Pb : ℕ) : ℝ) ^ 2) :=
      mul_lt_mul'' hDXa hDXb hDXpos.le hDXpos.le
    by_contra hh
    push Not at hh
    have hPr : 0 ≤ ((Pa : ℕ) : ℝ) * ((Pb : ℕ) : ℝ) := by positivity
    nlinarith
  have h2XP : 2 * (X : ℝ) ≤ (((Pa * Pb : ℕ)) : ℝ) := by nlinarith
  have hqYr : (q : ℝ) * ((X : ℝ) + 1 + (Pa : ℝ) + (Pb : ℝ)) ≤ ((Pa * Pb : ℕ) : ℝ) := by
    have : ((q * (X + 1 + Pa + Pb) : ℕ) : ℝ) ≤ ((Pa * Pb : ℕ) : ℝ) := by exact_mod_cast hqY
    push_cast at this ⊢
    exact this
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hmN : (2 * ((q + 1 : ℕ) : ℝ)) / ((Pa * Pb : ℕ) : ℝ) ≤ 3 / (X : ℝ) := by
    have hPr : (0 : ℝ) < ((Pa * Pb : ℕ) : ℝ) := by exact_mod_cast hPpos
    rw [div_le_div_iff₀ hPr hXr]
    have hPa0 : (0 : ℝ) ≤ Pa := Nat.cast_nonneg _
    have hPb0 : (0 : ℝ) ≤ Pb := Nat.cast_nonneg _
    have hXY : (X : ℝ) ≤ (X : ℝ) + 1 + Pa + Pb := by linarith
    have h1 := mul_le_mul_of_nonneg_left hXY hq0
    have h2 := le_trans h1 hqYr
    have hq1 : ((q + 1 : ℕ) : ℝ) = q + 1 := by push_cast; ring
    rw [hq1]
    nlinarith [h2, h2XP]
  -- seeds
  set N : ℕ := Pa * Pb with hN
  have hAn : ∀ x : ZMod N, 0 ≤ kernq N (2 ^ ((sa + 0) ^ 2)) (deltaSeed (2 ^ ((sa + 0) ^ 2))) x :=
    fun x => JAFinal.kern_nonneg' _ _ _ x
  have hBn : ∀ x : ZMod N, 0 ≤ kernq N (3 ^ ((sa + 0) ^ 2)) (deltaSeed (3 ^ ((sa + 0) ^ 2))) x :=
    fun x => JAFinal.kern_nonneg' _ _ _ x
  obtain ⟨b, n, hb, hmono, hmem, hbound⟩ := JASorted.arc_mass_sorted N D sa na sa nb _ _ hAn hBn
    (q + 1) (by omega) h2m
  haveI inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2)) :=
    fun j => ⟨pow_ne_zero _ (by rcases hb j with h | h <;> omega)⟩
  have h := @hbound inst
  -- hypotheses of prod_f_bound
  have hn1 : ∀ i, i < na + nb → 1 ≤ n i := by
    intro i hi
    rcases hmem i hi with ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;> omega
  have hQ' : ∀ j, j < na + nb → 25 * D ≤ (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ) := by
    intro j hj
    rcases hmem j hj with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · rw [h1]; exact big_period D hD 2 (n j) le_rfl h2
    · rw [h1]; exact big_period D hD 3 (n j) (by norm_num) h2
  have hQN' : ∀ j, j < na + nb → (b j) ^ ((n j) ^ 2) ∣ N := by
    intro j hj
    rcases hmem j hj with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1, hN]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (Nat.pow_le_pow_left h3 2)) _
    · rw [h1, hN]
      exact Dvd.dvd.mul_left (pow_dvd_pow 3 (Nat.pow_le_pow_left h3 2)) _
  have hQX' : ∀ j, j < na + nb → (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ) ≤ D * X := by
    intro j hj
    have hXr' : (4 : ℝ) * Pa ≤ X := by exact_mod_cast h4a
    have hXr'' : (4 : ℝ) * Pb ≤ X := by exact_mod_cast h4b
    have hX0 : (0 : ℝ) ≤ X := hXr.le
    rcases hmem j hj with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1]
      have : (2 : ℕ) ^ ((n j) ^ 2) ≤ Pa := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left h3 2)
      have h' : (((2 : ℕ) ^ ((n j) ^ 2) : ℕ) : ℝ) ≤ Pa := by exact_mod_cast this
      nlinarith
    · rw [h1]
      have : (3 : ℕ) ^ ((n j) ^ 2) ≤ Pb := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left h3 2)
      have h' : (((3 : ℕ) ^ ((n j) ^ 2) : ℕ) : ℝ) ≤ Pb := by exact_mod_cast this
      nlinarith
  have hX' : X₀ ≤ (X : ℝ) := le_trans (Nat.le_ceil X₀) (by exact_mod_cast hX)
  have hF := hprod X N (q + 1) (na + nb) b n hX' hb hn1 hmono (by omega) h2m hQ' hQN' hQX'
    (by simpa using hmN)
  have hS0 := S0_le (N := N) D hD (q + 1) (by omega) h2m (na + nb) b n hQ' hQN' _ _ hAn hBn
  have hfb := fac_bounds (N := N) D hD (q + 1) (by omega) h2m (na + nb) b n hQ' hQN'
  have hF0 : 0 ≤ ∏ i ∈ range (na + nb), (Hs (Ftri N (q + 1)) ((klist N D (na + nb) b n).drop i) 0 /
      Hs (Ftri N (q + 1)) ((klist N D (na + nb) b n).drop (i + 1)) 0) :=
    Finset.prod_nonneg (fun i hi => by linarith [(hfb i (Finset.mem_range.mp hi)).1])
  rw [sum_kernq_delta, sum_kernq_delta] at hS0
  refine ⟨q + 1, by omega, hm_le, hPlt.le.trans_eq (by ring), ?_⟩
  refine le_trans h ?_
  -- scalar factors
  have hSA := JAScalar.chainP_scalar_bound 2 le_rfl D hD na
  have hSB := JAScalar.chainP_scalar_bound 3 (by norm_num) D hD nb
  have hSA0 : 0 ≤ ∏ k ∈ range na, ((∑ y, (chainP 2 sa D).w (k + 1) y) ^ 2 /
      (((chainP 2 sa D).q k : ℕ) : ℝ) ^ 2) :=
    Finset.prod_nonneg (fun k _ => by positivity)
  have hSB0 : 0 ≤ ∏ k ∈ range nb, ((∑ y, (chainP 3 sa D).w (k + 1) y) ^ 2 /
      (((chainP 3 sa D).q k : ℕ) : ℝ) ^ 2) :=
    Finset.prod_nonneg (fun k _ => by positivity)
  rw [← hsa] at hSA hSB
  simp only [add_zero] at hS0
  have hcs : 0 ≤ (((2 ^ (sa ^ 2) : ℕ)) : ℝ) * (((3 ^ (sa ^ 2) : ℕ)) : ℝ) := by positivity
  have key := final_arith _ _ _ _ _ _ _ _ _ hSA hSB hSA0 hSB0 hS0.2 hS0.1 hF hF0 (Real.exp_pos _).le hcs hCp.le
  refine le_trans key (le_of_eq ?_)
  have he : Real.exp (16 / 3) * Real.exp (16 / 3) = Real.exp (32 / 3) := by
    rw [← Real.exp_add]; norm_num
  rw [he]

#print axioms sum_kernq_delta
#print axioms S0_le
#print axioms big_period
#print axioms final_arith
#print axioms central_bound

end JACentral2
end LeanCheck
