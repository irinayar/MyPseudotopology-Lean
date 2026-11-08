import Mathlib
import LeanCheck.DD3Assemble
import LeanCheck.DD3Sorted
import LeanCheck.DD3Heights
import LeanCheck.JACentral2
import LeanCheck.JAScalar

/-!
# Diagonal density for three primes: the central bound for three chains (Lean check)

Scope. First half of phase 5f of the Lean version of the conditional proof of `DD({2,3,5})` (research note
`TVGplus_conditional_DD235_2026-11-07.md`). It is the three-prime counterpart of `JACentral2.central_bound`, with `JAFinal2.CentralAt`,
`JAHeights.CentralBound`.

* `NN sa na sb nb sc nc = 2^{(sa+na)²} 3^{(sb+nb)²} 5^{(sc+nc)²}`, `CentralAt3 D C X sa na sb nb sc nc`: for some `m` with
  `N ≤ (X+1+Q_a+Q_b+Q_c) m` the central arc mass of `Mavg_a ∗ (Mavg_b ∗ Mavg_c)` (seeds: the kernels of the `δ`-seeds) is at
  most `C (∏_a (α_k I₁ - 2) ∏_b ∏_c)²`;
* `CentralBound3 D C`: `CentralAt3` at every large buffered height (`DD3Heights.Buffered3`, start level `⌈D⌉`);
* `S0_le3`, `final_arith3`, and `central_bound3`: for `D ≥ 3`, a window profile `a` with `CloseGrowth`, `HTT3 a T₁` and `HFin a K₁`
  there is `C > 0` with `CentralBound3 D C` (the three-prime counterpart of `central_bound`, using `DD3Assemble.prod_f_bound3`,
  `DD3Sorted.arc_mass_sorted3`, `JAScalar.chainP_scalar_bound`, `JACentral2.sum_kernq_delta`).

A Lean proof verifies its formal statement under its hypotheses (here `HTT3`, `HFin`); the correspondence with the research note
requires mathematical review.
-/

namespace LeanCheck
namespace DD3Central

open Finset JATransfer JAProduct JAProduct2 JAMulti JAFinal2 JAWindowQ JACenter JAAssemble JACentral JACentral2 DD3Heights
  JAHeights JALocalize

/-- The common period `2^{(sa+na)²} 3^{(sb+nb)²} 5^{(sc+nc)²}`. -/
def NN (sa na sb nb sc nc : ℕ) : ℕ := 2 ^ ((sa + na) ^ 2) * 3 ^ ((sb + nb) ^ 2) * 5 ^ ((sc + nc) ^ 2)

instance (sa na sb nb sc nc : ℕ) : NeZero (NN sa na sb nb sc nc) := ⟨by unfold NN; positivity⟩

/-- **The deterministic central bound for three chains (not proved here; see `central_bound3`).** -/
def CentralAt3 (D C : ℝ) (X sa na sb nb sc nc : ℕ) : Prop :=
  ∃ m : ℕ,
    1 ≤ m ∧ m ≤ NN sa na sb nb sc nc ∧
    NN sa na sb nb sc nc ≤
      (X + 1 + 2 ^ ((sa + na) ^ 2) + 3 ^ ((sb + nb) ^ 2) + 5 ^ ((sc + nc) ^ 2)) * m ∧
    ∑ t ∈ arc (NN sa na sb nb sc nc) (m - 1),
        conv (Mavg (NN sa na sb nb sc nc) na (chainP 2 sa D)
            (kernq (NN sa na sb nb sc nc) (2 ^ ((sa + 0) ^ 2)) (deltaSeed (2 ^ ((sa + 0) ^ 2)))))
          (conv (Mavg (NN sa na sb nb sc nc) nb (chainP 3 sb D)
            (kernq (NN sa na sb nb sc nc) (3 ^ ((sb + 0) ^ 2)) (deltaSeed (3 ^ ((sb + 0) ^ 2)))))
          (Mavg (NN sa na sb nb sc nc) nc (chainP 5 sc D)
            (kernq (NN sa na sb nb sc nc) (5 ^ ((sc + 0) ^ 2)) (deltaSeed (5 ^ ((sc + 0) ^ 2)))))) t ≤
      C * ((∏ k ∈ range na, (((2 ^ (2 * (sa + k) + 1) : ℕ) : ℝ) * (16 / (15 * D)) - 2)) *
        (∏ k ∈ range nb, (((3 ^ (2 * (sb + k) + 1) : ℕ) : ℝ) * (16 / (15 * D)) - 2)) *
        (∏ k ∈ range nc, (((5 ^ (2 * (sc + k) + 1) : ℕ) : ℝ) * (16 / (15 * D)) - 2))) ^ 2

/-- **The remaining hypothesis (three chains)**: at all large buffered heights the deterministic central bound holds
with a constant `C` independent of the height. -/
def CentralBound3 (D C : ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ X na nb nc : ℕ, X₀ ≤ X → Buffered3 D X na nb nc →
    CentralAt3 D C X (sD D) na (sD D) nb (sD D) nc

/-- The seed factor `S_0` is nonnegative and bounded by the total mass of the three seeds. -/
lemma S0_le3 {N : ℕ} [NeZero N] (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (b n : ℕ → ℕ) [inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2))]
    (hQ : ∀ j, j < L → 25 * D ≤ (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ))
    (hQN : ∀ j, j < L → (b j) ^ ((n j) ^ 2) ∣ N) (A B C : ZMod N → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x) (hC : ∀ x, 0 ≤ C x) :
    0 ≤ conv (conv A (conv B C)) (Hs (Ftri N m) (klist N D L b n)) 0 / Hs (Ftri N m) (klist N D L b n) 0 ∧
      conv (conv A (conv B C)) (Hs (Ftri N m) (klist N D L b n)) 0 / Hs (Ftri N m) (klist N D L b n) 0 ≤
        (∑ x, A x) * ((∑ x, B x) * ∑ x, C x) := by
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
  have hμ : ∀ x, 0 ≤ conv A (conv B C) x := fun x =>
    JAFinal.conv_nonneg' A (conv B C) hA (fun y => JAFinal.conv_nonneg' B C hB hC y) x
  have key := S0_bounds (conv A (conv B C)) _ hμ hH hH0
  rw [sum_conv_total, sum_conv_total] at key
  exact key

lemma final_arith3 (SA SB SC S0 F a b c cs Cp E : ℝ) (hSA : SA ≤ E * a ^ 2) (hSB : SB ≤ E * b ^ 2)
    (hSC : SC ≤ E * c ^ 2) (hSA0 : 0 ≤ SA) (hSB0 : 0 ≤ SB) (hSC0 : 0 ≤ SC) (hS0 : S0 ≤ cs) (hS00 : 0 ≤ S0)
    (hF : F ≤ Cp) (hF0 : 0 ≤ F) (hE : 0 ≤ E) (hcs : 0 ≤ cs) (hCp : 0 ≤ Cp) :
    2 * (SA * SB * SC) * (S0 * F) ≤ 2 * (E * E * E) * cs * Cp * (a * b * c) ^ 2 := by
  have h1 : SA * SB ≤ (E * a ^ 2) * (E * b ^ 2) :=
    mul_le_mul hSA hSB hSB0 (by positivity)
  have h1' : SA * SB * SC ≤ (E * a ^ 2) * (E * b ^ 2) * (E * c ^ 2) :=
    mul_le_mul h1 hSC hSC0 (by positivity)
  have h2 : S0 * F ≤ cs * Cp := mul_le_mul hS0 hF hF0 hcs
  have h3 : (SA * SB * SC) * (S0 * F) ≤ ((E * a ^ 2) * (E * b ^ 2) * (E * c ^ 2)) * (cs * Cp) :=
    mul_le_mul h1' h2 (mul_nonneg hS00 hF0) (by positivity)
  nlinarith [h3]

set_option maxHeartbeats 1600000 in
/-- **`CentralBound3` from the two-term separations and the finiteness hypothesis.** -/
theorem central_bound3 (D : ℝ) (a : ℝ → ℝ) (hD : 3 ≤ D) (ha : WindowProfile a) (hG : CloseGrowth a)
    (T₁ : ℝ) (htt : DD3Assemble.HTT3 a T₁) (K₁ : ℕ) (hH : DD3Assemble.HFin a K₁) :
    ∃ C : ℝ, 0 < C ∧ CentralBound3 D C := by
  classical
  obtain ⟨Cp, X₀, hCp, hprod⟩ := DD3Assemble.prod_f_bound3 D a hD ha hG T₁ htt K₁ hH
  have hD0 : 0 < D := by linarith
  have hsa3 : 3 ≤ sD D := by
    have : (3 : ℝ) ≤ (sD D : ℝ) := le_trans hD (Nat.le_ceil D)
    exact_mod_cast this
  refine ⟨2 * Real.exp 16 * ((((2 ^ ((sD D) ^ 2) : ℕ)) : ℝ) * (((3 ^ ((sD D) ^ 2) : ℕ)) : ℝ) *
      (((5 ^ ((sD D) ^ 2) : ℕ)) : ℝ)) * Cp, by positivity, ?_⟩
  refine ⟨⌈X₀⌉₊, ?_⟩
  intro X na nb nc hX hbuf
  obtain ⟨hB2, hB3, hB5, h4a, h4b, h4c⟩ := hbuf
  unfold CentralAt3
  set sa : ℕ := sD D with hsa
  set Pa : ℕ := 2 ^ ((sa + na) ^ 2) with hPa
  set Pb : ℕ := 3 ^ ((sa + nb) ^ 2) with hPb
  set Pc : ℕ := 5 ^ ((sa + nc) ^ 2) with hPc
  have hNN : NN sa na sa nb sa nc = Pa * Pb * Pc := rfl
  have hPa4 : 4 ≤ Pa := by
    have : 2 ^ 2 ≤ 2 ^ ((sa + na) ^ 2) :=
      Nat.pow_le_pow_right (by norm_num) (by have h3 : 3 ≤ sa + na := (by omega); nlinarith)
    omega
  have hPb4 : 4 ≤ Pb := by
    have h1 : 2 ^ 2 ≤ 3 ^ 2 := by norm_num
    have h2 : 3 ^ 2 ≤ 3 ^ ((sa + nb) ^ 2) :=
      Nat.pow_le_pow_right (by norm_num) (by have h3 : 3 ≤ sa + nb := (by omega); nlinarith)
    omega
  have hPc4 : 4 ≤ Pc := by
    have h1 : 2 ^ 2 ≤ 5 ^ 2 := by norm_num
    have h2 : 5 ^ 2 ≤ 5 ^ ((sa + nc) ^ 2) :=
      Nat.pow_le_pow_right (by norm_num) (by have h3 : 3 ≤ sa + nc := (by omega); nlinarith)
    omega
  have hPpos : 0 < Pa * Pb * Pc := by positivity
  haveI hNZ : NeZero (Pa * Pb * Pc) := ⟨hPpos.ne'⟩
  have hP64 : 64 ≤ Pa * Pb * Pc :=
    calc 64 = 4 * 4 * 4 := by norm_num
      _ ≤ Pa * Pb * Pc := Nat.mul_le_mul (Nat.mul_le_mul hPa4 hPb4) hPc4
  have hY4 : 4 ≤ X + 1 + Pa + Pb + Pc := by omega
  have hY0 : 0 < X + 1 + Pa + Pb + Pc := by omega
  have hqY : (Pa * Pb * Pc / (X + 1 + Pa + Pb + Pc)) * (X + 1 + Pa + Pb + Pc) ≤ Pa * Pb * Pc :=
    Nat.div_mul_le_self _ _
  obtain ⟨q, hq⟩ : ∃ q, q = Pa * Pb * Pc / (X + 1 + Pa + Pb + Pc) := ⟨_, rfl⟩
  rw [← hq] at hqY
  have hq4 : 4 * q ≤ Pa * Pb * Pc := by nlinarith
  have hPlt : Pa * Pb * Pc < (X + 1 + Pa + Pb + Pc) * (q + 1) := by
    rw [hq]; exact Nat.lt_mul_div_succ _ hY0
  have hm_le : q + 1 ≤ Pa * Pb * Pc := by omega
  have h2m : 2 * (q + 1) ≤ Pa * Pb * Pc := by omega
  -- real inequalities
  have hXr : (0 : ℝ) < X := by
    have : 4 * Pa ≤ X := h4a
    have : 0 < X := by omega
    exact_mod_cast this
  have hX1 : (1 : ℝ) ≤ X := by
    have : 4 * Pa ≤ X := h4a
    have : 1 ≤ X := by omega
    exact_mod_cast this
  have hPar : ((Pa : ℕ) : ℝ) = (2 : ℝ) ^ ((sa + na) ^ 2) := by rw [hPa]; push_cast; ring
  have hPbr : ((Pb : ℕ) : ℝ) = (3 : ℝ) ^ ((sa + nb) ^ 2) := by rw [hPb]; push_cast; ring
  have hPcr : ((Pc : ℕ) : ℝ) = (5 : ℝ) ^ ((sa + nc) ^ 2) := by rw [hPc]; push_cast; ring
  have hDXa : D * X < ((Pa : ℕ) : ℝ) ^ 2 := by
    have := pow_succ_sq_le 2 (by norm_num) (sa + na) (by omega)
    rw [hPar]
    exact lt_of_lt_of_le hB2 this
  have hDXb : D * X < ((Pb : ℕ) : ℝ) ^ 2 := by
    have := pow_succ_sq_le 3 (by norm_num) (sa + nb) (by omega)
    rw [hPbr]
    exact lt_of_lt_of_le hB3 this
  have hDXc : D * X < ((Pc : ℕ) : ℝ) ^ 2 := by
    have := pow_succ_sq_le 5 (by norm_num) (sa + nc) (by omega)
    rw [hPcr]
    exact lt_of_lt_of_le hB5 this
  have hDXpos : 0 < D * X := by positivity
  have h2XP : 2 * (X : ℝ) ≤ (((Pa * Pb * Pc : ℕ)) : ℝ) := by
    have h1 : (D * X) * (D * X) < (((Pa : ℕ) : ℝ) ^ 2) * (((Pb : ℕ) : ℝ) ^ 2) :=
      mul_lt_mul'' hDXa hDXb hDXpos.le hDXpos.le
    have h2 : ((D * X) * (D * X)) * (D * X) <
        ((((Pa : ℕ) : ℝ) ^ 2) * (((Pb : ℕ) : ℝ) ^ 2)) * (((Pc : ℕ) : ℝ) ^ 2) :=
      mul_lt_mul'' h1 hDXc (by positivity) hDXpos.le
    push_cast
    by_contra hh
    push Not at hh
    have hPr : 0 ≤ ((Pa : ℕ) : ℝ) * ((Pb : ℕ) : ℝ) * ((Pc : ℕ) : ℝ) := by positivity
    have h3 : (((Pa : ℕ) : ℝ) * ((Pb : ℕ) : ℝ) * ((Pc : ℕ) : ℝ)) ^ 2 < (2 * (X : ℝ)) ^ 2 :=
      pow_lt_pow_left₀ hh hPr (by norm_num)
    have h4 : (3 * (X : ℝ)) ^ 3 ≤ (D * X) ^ 3 := pow_le_pow_left₀ (by positivity) (by nlinarith) 3
    nlinarith [h2, h3, h4, sq_nonneg (X : ℝ), mul_pos hXr hXr]
  have hqYr : (q : ℝ) * ((X : ℝ) + 1 + (Pa : ℝ) + (Pb : ℝ) + (Pc : ℝ)) ≤ ((Pa * Pb * Pc : ℕ) : ℝ) := by
    have : ((q * (X + 1 + Pa + Pb + Pc) : ℕ) : ℝ) ≤ ((Pa * Pb * Pc : ℕ) : ℝ) := by exact_mod_cast hqY
    push_cast at this ⊢
    exact this
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hmN : (2 * ((q + 1 : ℕ) : ℝ)) / ((Pa * Pb * Pc : ℕ) : ℝ) ≤ 3 / (X : ℝ) := by
    have hPr : (0 : ℝ) < ((Pa * Pb * Pc : ℕ) : ℝ) := by exact_mod_cast hPpos
    rw [div_le_div_iff₀ hPr hXr]
    have hPa0 : (0 : ℝ) ≤ Pa := Nat.cast_nonneg _
    have hPb0 : (0 : ℝ) ≤ Pb := Nat.cast_nonneg _
    have hPc0 : (0 : ℝ) ≤ Pc := Nat.cast_nonneg _
    have hXY : (X : ℝ) ≤ (X : ℝ) + 1 + Pa + Pb + Pc := by linarith
    have h1 := mul_le_mul_of_nonneg_left hXY hq0
    have h2 := le_trans h1 hqYr
    have hq1 : ((q + 1 : ℕ) : ℝ) = q + 1 := by push_cast; ring
    rw [hq1]
    nlinarith [h2, h2XP]
  -- seeds
  set N : ℕ := Pa * Pb * Pc with hN
  have hAn : ∀ x : ZMod N, 0 ≤ kernq N (2 ^ ((sa + 0) ^ 2)) (deltaSeed (2 ^ ((sa + 0) ^ 2))) x :=
    fun x => JAFinal.kern_nonneg' _ _ _ x
  have hBn : ∀ x : ZMod N, 0 ≤ kernq N (3 ^ ((sa + 0) ^ 2)) (deltaSeed (3 ^ ((sa + 0) ^ 2))) x :=
    fun x => JAFinal.kern_nonneg' _ _ _ x
  have hCn : ∀ x : ZMod N, 0 ≤ kernq N (5 ^ ((sa + 0) ^ 2)) (deltaSeed (5 ^ ((sa + 0) ^ 2))) x :=
    fun x => JAFinal.kern_nonneg' _ _ _ x
  obtain ⟨b, n, hb, hmono, hmem, hbound⟩ := DD3Sorted.arc_mass_sorted3 (N := N) D sa na sa nb sa nc _ _ _
    hAn hBn hCn (q + 1) (by omega) h2m
  haveI inst : ∀ j, NeZero ((b j) ^ ((n j) ^ 2)) :=
    fun j => ⟨pow_ne_zero _ (by rcases hb j with h | h | h <;> omega)⟩
  have h := @hbound inst
  -- hypotheses of prod_f_bound3
  have hn1 : ∀ i, i < na + nb + nc → 1 ≤ n i := by
    intro i hi
    rcases hmem i hi with ⟨_, h1, _⟩ | ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;> omega
  have hQ' : ∀ j, j < na + nb + nc → 25 * D ≤ (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ) := by
    intro j hj
    rcases hmem j hj with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · rw [h1]; exact big_period D hD 2 (n j) le_rfl h2
    · rw [h1]; exact big_period D hD 3 (n j) (by norm_num) h2
    · rw [h1]; exact big_period D hD 5 (n j) (by norm_num) h2
  have hQN' : ∀ j, j < na + nb + nc → (b j) ^ ((n j) ^ 2) ∣ N := by
    intro j hj
    rcases hmem j hj with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1, hN]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow 2 (Nat.pow_le_pow_left h3 2)) _) _
    · rw [h1, hN]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow 3 (Nat.pow_le_pow_left h3 2)) _) _
    · rw [h1, hN]
      exact Dvd.dvd.mul_left (pow_dvd_pow 5 (Nat.pow_le_pow_left h3 2)) _
  have hQX' : ∀ j, j < na + nb + nc → (((b j) ^ ((n j) ^ 2) : ℕ) : ℝ) ≤ D * X := by
    intro j hj
    have hXr' : (4 : ℝ) * Pa ≤ X := by exact_mod_cast h4a
    have hXr'' : (4 : ℝ) * Pb ≤ X := by exact_mod_cast h4b
    have hXr''' : (4 : ℝ) * Pc ≤ X := by exact_mod_cast h4c
    have hX0 : (0 : ℝ) ≤ X := hXr.le
    have hDX3 : 3 * (X : ℝ) ≤ D * X := by
      have := mul_nonneg (sub_nonneg.2 hD) hX0
      linarith
    rcases hmem j hj with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1]
      have : (2 : ℕ) ^ ((n j) ^ 2) ≤ Pa := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left h3 2)
      have h' : (((2 : ℕ) ^ ((n j) ^ 2) : ℕ) : ℝ) ≤ Pa := by exact_mod_cast this
      linarith
    · rw [h1]
      have : (3 : ℕ) ^ ((n j) ^ 2) ≤ Pb := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left h3 2)
      have h' : (((3 : ℕ) ^ ((n j) ^ 2) : ℕ) : ℝ) ≤ Pb := by exact_mod_cast this
      linarith
    · rw [h1]
      have : (5 : ℕ) ^ ((n j) ^ 2) ≤ Pc := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left h3 2)
      have h' : (((5 : ℕ) ^ ((n j) ^ 2) : ℕ) : ℝ) ≤ Pc := by exact_mod_cast this
      linarith
  have hX' : X₀ ≤ (X : ℝ) := le_trans (Nat.le_ceil X₀) (by exact_mod_cast hX)
  have hF := hprod X N (q + 1) (na + nb + nc) b n hX' hb hn1 hmono (by omega) h2m hQ' hQN' hQX'
    hmN
  have hS0 := S0_le3 (N := N) D hD (q + 1) (by omega) h2m (na + nb + nc) b n hQ' hQN' _ _ _ hAn hBn hCn
  have hfb := fac_bounds (N := N) D hD (q + 1) (by omega) h2m (na + nb + nc) b n hQ' hQN'
  have hF0 : 0 ≤ ∏ i ∈ range (na + nb + nc), (Hs (Ftri N (q + 1)) ((klist N D (na + nb + nc) b n).drop i) 0 /
      Hs (Ftri N (q + 1)) ((klist N D (na + nb + nc) b n).drop (i + 1)) 0) :=
    Finset.prod_nonneg (fun i hi => by linarith [(hfb i (Finset.mem_range.mp hi)).1])
  rw [sum_kernq_delta, sum_kernq_delta, sum_kernq_delta] at hS0
  refine ⟨q + 1, by omega, hm_le, hPlt.le.trans_eq (by ring), ?_⟩
  refine le_trans h ?_
  -- scalar factors
  have hSA := JAScalar.chainP_scalar_bound 2 le_rfl D hD na
  have hSB := JAScalar.chainP_scalar_bound 3 (by norm_num) D hD nb
  have hSC := JAScalar.chainP_scalar_bound 5 (by norm_num) D hD nc
  have hSA0 : 0 ≤ ∏ k ∈ range na, ((∑ y, (chainP 2 sa D).w (k + 1) y) ^ 2 /
      (((chainP 2 sa D).q k : ℕ) : ℝ) ^ 2) :=
    Finset.prod_nonneg (fun k _ => by positivity)
  have hSB0 : 0 ≤ ∏ k ∈ range nb, ((∑ y, (chainP 3 sa D).w (k + 1) y) ^ 2 /
      (((chainP 3 sa D).q k : ℕ) : ℝ) ^ 2) :=
    Finset.prod_nonneg (fun k _ => by positivity)
  have hSC0 : 0 ≤ ∏ k ∈ range nc, ((∑ y, (chainP 5 sa D).w (k + 1) y) ^ 2 /
      (((chainP 5 sa D).q k : ℕ) : ℝ) ^ 2) :=
    Finset.prod_nonneg (fun k _ => by positivity)
  rw [← hsa] at hSA hSB hSC
  simp only [add_zero] at hS0
  have hcs : 0 ≤ (((2 ^ (sa ^ 2) : ℕ)) : ℝ) * ((((3 ^ (sa ^ 2) : ℕ)) : ℝ) * (((5 ^ (sa ^ 2) : ℕ)) : ℝ)) := by
    positivity
  have key := final_arith3 _ _ _ _ _ _ _ _ _ _ _ hSA hSB hSC hSA0 hSB0 hSC0 hS0.2 hS0.1 hF hF0
    (Real.exp_pos _).le hcs hCp.le
  refine le_trans key (le_of_eq ?_)
  have he : Real.exp (16 / 3) * Real.exp (16 / 3) * Real.exp (16 / 3) = Real.exp 16 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [he]
  ring

#print axioms S0_le3
#print axioms final_arith3
#print axioms central_bound3

end DD3Central
end LeanCheck
