import Mathlib
import LeanCheck.DD3Central
import LeanCheck.DD3GenAssemble
import LeanCheck.DD3GenScalar

/-!
# Three chains with general exponents: the central bound (Lean check)

Scope. Counterpart of `DD3Central` (phase 5f, first half) for the chains with general exponents `Ex b k` satisfying `Mod3 Ex`
(`DD3GenScalar`: the log-gap hypothesis, `Ex b n ≥ n²`, `Ex b (n+1) ≤ 2 Ex b n` for `n ≥ 3`), with the start level
`sE D = max(⌈D⌉, 30)`:

* `NNE`, `CentralAt3E`, `CentralBound3E`: the common period `2^{Ex 2 (sa+na)} 3^{Ex 3 (sb+nb)} 5^{Ex 5 (sc+nc)}`, the central
  arc mass of `Mavg_a ∗ (Mavg_b ∗ Mavg_c)` at a buffered height (`DD3GenHeights.Buffered3E`), the normalization
  `C (∏ (α_k I₁ - 2))²` with `α_k = p^{Ex p (s+k+1) - Ex p (s+k)}`;
* `pow_dbl`, `big_periodE`: `p^{Ex p (j+1)} ≤ (p^{Ex p j})²` and `25 D ≤ p^{Ex p n}` for `n > ⌈D⌉` (from `Mod3`);
* `S0_le3E`: the seed factor `S₀` is nonnegative and bounded by the total mass of the three seeds;
* `central_bound3E`: for `D ≥ 3`, a window profile `a` with `CloseGrowth`, `HTT3E Ex a T₁` and `HFinE Ex a K₁` there is
  `C > 0` with `CentralBound3E` (the counterpart of `central_bound3`, using `prod_f_bound3E`, `arc_mass_sorted3E`,
  `chainE_scalar_bound`, `JACentral2.sum_kernq_delta`).

A Lean proof verifies its formal statement under its hypotheses (here `HTT3E`, `HFinE`); the correspondence with the research note
requires mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open Finset JATransfer JAProduct JAProduct2 JAMulti JAFinal2 JAWindowQ JACenter JAAssemble JACentral JACentral2
  JAHeights JALocalize

lemma Mod3.ok2 {E : ℕ → ℕ → ℕ} (hE : Mod3 E) : StrictMono (E 2) := (hE.ok 2 (Or.inl rfl)).1
lemma Mod3.ok3 {E : ℕ → ℕ → ℕ} (hE : Mod3 E) : StrictMono (E 3) := (hE.ok 3 (by simp)).1
lemma Mod3.ok5 {E : ℕ → ℕ → ℕ} (hE : Mod3 E) : StrictMono (E 5) := (hE.ok 5 (by simp)).1

lemma Mod3.mono2 {E : ℕ → ℕ → ℕ} (hE : Mod3 E) : Monotone (E 2) := (hE.ok 2 (Or.inl rfl)).1.monotone
lemma Mod3.mono3 {E : ℕ → ℕ → ℕ} (hE : Mod3 E) : Monotone (E 3) := (hE.ok 3 (by simp)).1.monotone
lemma Mod3.mono5 {E : ℕ → ℕ → ℕ} (hE : Mod3 E) : Monotone (E 5) := (hE.ok 5 (by simp)).1.monotone

/-- The common period. -/
def NNE (Ex : ℕ → ℕ → ℕ) (sa na sb nb sc nc : ℕ) : ℕ :=
  2 ^ (Ex 2 (sa + na)) * 3 ^ (Ex 3 (sb + nb)) * 5 ^ (Ex 5 (sc + nc))

instance (Ex : ℕ → ℕ → ℕ) (sa na sb nb sc nc : ℕ) : NeZero (NNE Ex sa na sb nb sc nc) :=
  ⟨by unfold NNE; positivity⟩

/-- **The deterministic central bound for three chains with general exponents (see `central_bound3E`).** -/
def CentralAt3E (Ex : ℕ → ℕ → ℕ) (hm2 : Monotone (Ex 2)) (hm3 : Monotone (Ex 3)) (hm5 : Monotone (Ex 5))
    (D C : ℝ) (X sa na sb nb sc nc : ℕ) : Prop :=
  ∃ m : ℕ,
    1 ≤ m ∧ m ≤ NNE Ex sa na sb nb sc nc ∧
    NNE Ex sa na sb nb sc nc ≤
      (X + 1 + 2 ^ (Ex 2 (sa + na)) + 3 ^ (Ex 3 (sb + nb)) + 5 ^ (Ex 5 (sc + nc))) * m ∧
    ∑ t ∈ arc (NNE Ex sa na sb nb sc nc) (m - 1),
        conv (Mavg (NNE Ex sa na sb nb sc nc) na (chainE 2 (Ex 2) hm2 sa D)
            (kernq (NNE Ex sa na sb nb sc nc) (2 ^ (Ex 2 (sa + 0))) (deltaSeed (2 ^ (Ex 2 (sa + 0))))))
          (conv (Mavg (NNE Ex sa na sb nb sc nc) nb (chainE 3 (Ex 3) hm3 sb D)
            (kernq (NNE Ex sa na sb nb sc nc) (3 ^ (Ex 3 (sb + 0))) (deltaSeed (3 ^ (Ex 3 (sb + 0))))))
          (Mavg (NNE Ex sa na sb nb sc nc) nc (chainE 5 (Ex 5) hm5 sc D)
            (kernq (NNE Ex sa na sb nb sc nc) (5 ^ (Ex 5 (sc + 0))) (deltaSeed (5 ^ (Ex 5 (sc + 0))))))) t ≤
      C * ((∏ k ∈ range na, (((2 ^ (Ex 2 (sa + k + 1) - Ex 2 (sa + k)) : ℕ) : ℝ) * (16 / (15 * D)) - 2)) *
        (∏ k ∈ range nb, (((3 ^ (Ex 3 (sb + k + 1) - Ex 3 (sb + k)) : ℕ) : ℝ) * (16 / (15 * D)) - 2)) *
        (∏ k ∈ range nc, (((5 ^ (Ex 5 (sc + k + 1) - Ex 5 (sc + k)) : ℕ) : ℝ) * (16 / (15 * D)) - 2))) ^ 2

/-- **The remaining hypothesis (three chains, general exponents)**. -/
def CentralBound3E (Ex : ℕ → ℕ → ℕ) (hm2 : Monotone (Ex 2)) (hm3 : Monotone (Ex 3)) (hm5 : Monotone (Ex 5))
    (D C : ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ X na nb nc : ℕ, X₀ ≤ X → Buffered3E Ex D X na nb nc →
    CentralAt3E Ex hm2 hm3 hm5 D C X (sE D) na (sE D) nb (sE D) nc

lemma pow_dbl {E : ℕ → ℕ → ℕ} (hE : Mod3 E) {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5) (j : ℕ) (hj : 3 ≤ j) :
    (p : ℝ) ^ (E p (j + 1)) ≤ ((p : ℝ) ^ (E p j)) ^ 2 := by
  have hp1 : (1 : ℝ) ≤ p := by rcases hp with rfl | rfl | rfl <;> norm_num
  rw [← pow_mul, mul_comm]
  exact pow_le_pow_right₀ hp1 (hE.dbl p hp j hj)

lemma big_periodE {E : ℕ → ℕ → ℕ} (hE : Mod3 E) (D : ℝ) (hD : 3 ≤ D) (β n : ℕ) (hβ : β = 2 ∨ β = 3 ∨ β = 5)
    (hn : ⌈D⌉₊ < n) : 25 * D ≤ ((β ^ (E β n) : ℕ) : ℝ) := by
  have hβ2 : 2 ≤ β := by rcases hβ with rfl | rfl | rfl <;> norm_num
  have h1 := JACentral2.big_period D hD β n hβ2 hn
  have h2 : β ^ (n ^ 2) ≤ β ^ (E β n) := Nat.pow_le_pow_right (by omega) (hE.quad β hβ n)
  have h3 : ((β ^ (n ^ 2) : ℕ) : ℝ) ≤ ((β ^ (E β n) : ℕ) : ℝ) := by exact_mod_cast h2
  linarith

lemma S0_le3E {Ex : ℕ → ℕ → ℕ} {N : ℕ} [NeZero N] (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (b n : ℕ → ℕ) [inst : ∀ j, NeZero ((b j) ^ (Ex (b j) (n j)))]
    (hQ : ∀ j, j < L → 25 * D ≤ (((b j) ^ (Ex (b j) (n j)) : ℕ) : ℝ))
    (hQN : ∀ j, j < L → (b j) ^ (Ex (b j) (n j)) ∣ N) (A B C : ZMod N → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x) (hC : ∀ x, 0 ≤ C x) :
    0 ≤ conv (conv A (conv B C)) (Hs (Ftri N m) (klistE Ex N D L b n)) 0 / Hs (Ftri N m) (klistE Ex N D L b n) 0 ∧
      conv (conv A (conv B C)) (Hs (Ftri N m) (klistE Ex N D L b n)) 0 / Hs (Ftri N m) (klistE Ex N D L b n) 0 ≤
        (∑ x, A x) * ((∑ x, B x) * ∑ x, C x) := by
  have hgood : ∀ K ∈ klistE Ex N D L b n, PD K ∧ (∀ x, 0 ≤ K x) ∧ 1 ≤ K 0 ∧ ∑ x, K x ≤ 30 * D / 7 := by
    intro K hK
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hK
    have hjL : j < L := List.mem_range.mp hj
    obtain ⟨h1, h2, h3⟩ := normK_props (N := N) D hD ((b j) ^ (Ex (b j) (n j))) (hQ j hjL) (hQN j hjL)
    exact ⟨h1, normK_nonneg _ _, h2, h3⟩
  have hF0 : 1 ≤ Ftri N m 0 := by rw [Ftri_zero m hm h2m]
  have hH : PD (Hs (Ftri N m) (klistE Ex N D L b n)) :=
    Hs_PD (Ftri N m) (Ftri_PD m) _ (fun K hK => (hgood K hK).1)
  have hH1 := (Hs_atom (Ftri N m) (Ftri_nonneg m) hF0 (klistE Ex N D L b n)
    (fun K hK => ⟨(hgood K hK).2.1, (hgood K hK).2.2.1⟩)).2
  have hH0 : 0 < Hs (Ftri N m) (klistE Ex N D L b n) 0 := by linarith
  have hμ : ∀ x, 0 ≤ conv A (conv B C) x := fun x =>
    JAFinal.conv_nonneg' A (conv B C) hA (fun y => JAFinal.conv_nonneg' B C hB hC y) x
  have key := S0_bounds (conv A (conv B C)) _ hμ hH hH0
  rw [sum_conv_total, sum_conv_total] at key
  exact key

set_option maxHeartbeats 1600000 in
/-- **`CentralBound3` from the two-term separations and the finiteness hypothesis.** -/
theorem central_bound3E {Ex : ℕ → ℕ → ℕ} (hEx : Mod3 Ex) (D : ℝ) (a : ℝ → ℝ) (hD : 3 ≤ D) (ha : WindowProfile a) (hG : CloseGrowth a)
    (T₁ : ℝ) (htt : HTT3E Ex a T₁) (K₁ : ℕ) (hH : HFinE Ex a K₁) :
    ∃ C : ℝ, 0 < C ∧ CentralBound3E Ex hEx.mono2 hEx.mono3 hEx.mono5 D C := by
  classical
  have hm2 : Monotone (Ex 2) := hEx.mono2
  have hm3 : Monotone (Ex 3) := hEx.mono3
  have hm5 : Monotone (Ex 5) := hEx.mono5
  obtain ⟨Cp, X₀, hCp, hprod⟩ := prod_f_bound3E hEx.ok D a hD ha hG T₁ htt K₁ hH
  have hD0 : 0 < D := by linarith
  have hsa3 : 3 ≤ sE D := by
    have : (3 : ℝ) ≤ (sE D : ℝ) := le_trans hD (le_trans (Nat.le_ceil D) (Nat.cast_le.2 (le_max_left _ _)))
    exact_mod_cast this
  refine ⟨2 * Real.exp (135 * D) * ((((2 ^ (Ex 2 (sE D)) : ℕ)) : ℝ) * (((3 ^ (Ex 3 (sE D)) : ℕ)) : ℝ) *
      (((5 ^ (Ex 5 (sE D)) : ℕ)) : ℝ)) * Cp, by positivity, ?_⟩
  refine ⟨⌈X₀⌉₊, ?_⟩
  intro X na nb nc hX hbuf
  obtain ⟨hB2, hB3, hB5, h4a, h4b, h4c⟩ := hbuf
  unfold CentralAt3E
  set sa : ℕ := sE D with hsa
  have hsEc : ⌈D⌉₊ ≤ sa := le_max_left _ _
  have hsa30 : 30 ≤ sa := le_max_right _ _
  set Pa : ℕ := 2 ^ (Ex 2 (sa + na)) with hPa
  set Pb : ℕ := 3 ^ (Ex 3 (sa + nb)) with hPb
  set Pc : ℕ := 5 ^ (Ex 5 (sa + nc)) with hPc
  have hNN : NNE Ex sa na sa nb sa nc = Pa * Pb * Pc := rfl
  have hPa4 : 4 ≤ Pa := by
    have : 2 ^ 2 ≤ 2 ^ (Ex 2 (sa + na)) :=
      Nat.pow_le_pow_right (by norm_num) (by have h3 : 3 ≤ sa + na := (by omega); have := hEx.quad 2 (Or.inl rfl) (sa + na); nlinarith)
    omega
  have hPb4 : 4 ≤ Pb := by
    have h1 : 2 ^ 2 ≤ 3 ^ 2 := by norm_num
    have h2 : 3 ^ 2 ≤ 3 ^ (Ex 3 (sa + nb)) :=
      Nat.pow_le_pow_right (by norm_num) (by have h3 : 3 ≤ sa + nb := (by omega); have := hEx.quad 3 (by simp) (sa + nb); nlinarith)
    omega
  have hPc4 : 4 ≤ Pc := by
    have h1 : 2 ^ 2 ≤ 5 ^ 2 := by norm_num
    have h2 : 5 ^ 2 ≤ 5 ^ (Ex 5 (sa + nc)) :=
      Nat.pow_le_pow_right (by norm_num) (by have h3 : 3 ≤ sa + nc := (by omega); have := hEx.quad 5 (by simp) (sa + nc); nlinarith)
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
  have hPar : ((Pa : ℕ) : ℝ) = (2 : ℝ) ^ (Ex 2 (sa + na)) := by rw [hPa]; push_cast; ring
  have hPbr : ((Pb : ℕ) : ℝ) = (3 : ℝ) ^ (Ex 3 (sa + nb)) := by rw [hPb]; push_cast; ring
  have hPcr : ((Pc : ℕ) : ℝ) = (5 : ℝ) ^ (Ex 5 (sa + nc)) := by rw [hPc]; push_cast; ring
  have hDXa : D * X < ((Pa : ℕ) : ℝ) ^ 2 := by
    have := pow_dbl hEx (p := 2) (Or.inl rfl) (sa + na) (by omega)
    push_cast at this
    rw [hPar]
    exact lt_of_lt_of_le hB2 this
  have hDXb : D * X < ((Pb : ℕ) : ℝ) ^ 2 := by
    have := pow_dbl hEx (p := 3) (by simp) (sa + nb) (by omega)
    push_cast at this
    rw [hPbr]
    exact lt_of_lt_of_le hB3 this
  have hDXc : D * X < ((Pc : ℕ) : ℝ) ^ 2 := by
    have := pow_dbl hEx (p := 5) (by simp) (sa + nc) (by omega)
    push_cast at this
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
  have hAn : ∀ x : ZMod N, 0 ≤ kernq N (2 ^ (Ex 2 (sa + 0))) (deltaSeed (2 ^ (Ex 2 (sa + 0)))) x :=
    fun x => JAFinal.kern_nonneg' _ _ _ x
  have hBn : ∀ x : ZMod N, 0 ≤ kernq N (3 ^ (Ex 3 (sa + 0))) (deltaSeed (3 ^ (Ex 3 (sa + 0)))) x :=
    fun x => JAFinal.kern_nonneg' _ _ _ x
  have hCn : ∀ x : ZMod N, 0 ≤ kernq N (5 ^ (Ex 5 (sa + 0))) (deltaSeed (5 ^ (Ex 5 (sa + 0)))) x :=
    fun x => JAFinal.kern_nonneg' _ _ _ x
  obtain ⟨b, n, hb, hmono, hmem, hbound⟩ := arc_mass_sorted3E (N := N) hEx.ok2 hEx.ok3 hEx.ok5 D sa na sa nb sa nc _ _ _
    hAn hBn hCn (q + 1) (by omega) h2m
  haveI inst : ∀ j, NeZero ((b j) ^ (Ex (b j) (n j))) :=
    fun j => ⟨pow_ne_zero _ (by rcases hb j with h | h | h <;> omega)⟩
  have h := @hbound inst
  -- hypotheses of prod_f_bound3
  have hn1 : ∀ i, i < na + nb + nc → 1 ≤ n i := by
    intro i hi
    rcases hmem i hi with ⟨_, h1, _⟩ | ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;> omega
  have hQ' : ∀ j, j < na + nb + nc → 25 * D ≤ (((b j) ^ (Ex (b j) (n j)) : ℕ) : ℝ) := by
    intro j hj
    rcases hmem j hj with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · rw [h1]; exact big_periodE hEx D hD 2 (n j) (by simp) (by omega)
    · rw [h1]; exact big_periodE hEx D hD 3 (n j) (by simp) (by omega)
    · rw [h1]; exact big_periodE hEx D hD 5 (n j) (by simp) (by omega)
  have hQN' : ∀ j, j < na + nb + nc → (b j) ^ (Ex (b j) (n j)) ∣ N := by
    intro j hj
    rcases hmem j hj with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1, hN]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow 2 (hm2 h3)) _) _
    · rw [h1, hN]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow 3 (hm3 h3)) _) _
    · rw [h1, hN]
      exact Dvd.dvd.mul_left (pow_dvd_pow 5 (hm5 h3)) _
  have hQX' : ∀ j, j < na + nb + nc → (((b j) ^ (Ex (b j) (n j)) : ℕ) : ℝ) ≤ D * X := by
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
      have : (2 : ℕ) ^ (Ex 2 (n j)) ≤ Pa := Nat.pow_le_pow_right (by norm_num) (hm2 h3)
      have h' : (((2 : ℕ) ^ (Ex 2 (n j)) : ℕ) : ℝ) ≤ Pa := by exact_mod_cast this
      linarith
    · rw [h1]
      have : (3 : ℕ) ^ (Ex 3 (n j)) ≤ Pb := Nat.pow_le_pow_right (by norm_num) (hm3 h3)
      have h' : (((3 : ℕ) ^ (Ex 3 (n j)) : ℕ) : ℝ) ≤ Pb := by exact_mod_cast this
      linarith
    · rw [h1]
      have : (5 : ℕ) ^ (Ex 5 (n j)) ≤ Pc := Nat.pow_le_pow_right (by norm_num) (hm5 h3)
      have h' : (((5 : ℕ) ^ (Ex 5 (n j)) : ℕ) : ℝ) ≤ Pc := by exact_mod_cast this
      linarith
  have hX' : X₀ ≤ (X : ℝ) := le_trans (Nat.le_ceil X₀) (by exact_mod_cast hX)
  have hF := hprod X N (q + 1) (na + nb + nc) b n hX' hb hn1 hmono (by omega) h2m hQ' hQN' hQX'
    hmN
  have hS0 := S0_le3E (N := N) D hD (q + 1) (by omega) h2m (na + nb + nc) b n hQ' hQN' _ _ _ hAn hBn hCn
  have hfb := fac_boundsE (N := N) D hD (q + 1) (by omega) h2m (na + nb + nc) b n hQ' hQN'
  have hF0 : 0 ≤ ∏ i ∈ range (na + nb + nc), (Hs (Ftri N (q + 1)) ((klistE Ex N D (na + nb + nc) b n).drop i) 0 /
      Hs (Ftri N (q + 1)) ((klistE Ex N D (na + nb + nc) b n).drop (i + 1)) 0) :=
    Finset.prod_nonneg (fun i hi => by linarith [(hfb i (Finset.mem_range.mp hi)).1])
  rw [sum_kernq_delta, sum_kernq_delta, sum_kernq_delta] at hS0
  refine ⟨q + 1, by omega, hm_le, hPlt.le.trans_eq (by ring), ?_⟩
  refine le_trans h ?_
  -- scalar factors
  have hSA := chainE_scalar_bound hEx (Or.inl rfl) D hD na
  have hSB := chainE_scalar_bound hEx (Or.inr (Or.inl rfl)) D hD nb
  have hSC := chainE_scalar_bound hEx (Or.inr (Or.inr rfl)) D hD nc
  have hSA0 : 0 ≤ ∏ k ∈ range na, ((∑ y, (chainE 2 (Ex 2) hm2 sa D).w (k + 1) y) ^ 2 /
      (((chainE 2 (Ex 2) hm2 sa D).q k : ℕ) : ℝ) ^ 2) :=
    Finset.prod_nonneg (fun k _ => by positivity)
  have hSB0 : 0 ≤ ∏ k ∈ range nb, ((∑ y, (chainE 3 (Ex 3) hm3 sa D).w (k + 1) y) ^ 2 /
      (((chainE 3 (Ex 3) hm3 sa D).q k : ℕ) : ℝ) ^ 2) :=
    Finset.prod_nonneg (fun k _ => by positivity)
  have hSC0 : 0 ≤ ∏ k ∈ range nc, ((∑ y, (chainE 5 (Ex 5) hm5 sa D).w (k + 1) y) ^ 2 /
      (((chainE 5 (Ex 5) hm5 sa D).q k : ℕ) : ℝ) ^ 2) :=
    Finset.prod_nonneg (fun k _ => by positivity)
  rw [← hsa] at hSA hSB hSC
  simp only [add_zero] at hS0
  have hcs : 0 ≤ (((2 ^ (Ex 2 sa) : ℕ)) : ℝ) * ((((3 ^ (Ex 3 sa) : ℕ)) : ℝ) * (((5 ^ (Ex 5 sa) : ℕ)) : ℝ)) := by
    positivity
  have key := DD3Central.final_arith3 _ _ _ _ _ _ _ _ _ _ _ hSA hSB hSC hSA0 hSB0 hSC0 hS0.2 hS0.1 hF hF0
    (Real.exp_pos _).le hcs hCp.le
  refine le_trans key (le_of_eq ?_)
  have he : Real.exp (45 * D) * Real.exp (45 * D) * Real.exp (45 * D) = Real.exp (135 * D) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [he]
  ring


end DD3Gen
end LeanCheck
