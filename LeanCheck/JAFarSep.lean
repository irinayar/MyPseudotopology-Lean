import Mathlib
import LeanCheck.JAKernTail
import LeanCheck.JAMerged

/-!
# The central bound, step 5: merged growth and the far-separated estimate

* `merged_gap_fin`, `merged_growth_fin`: the merged growth `Q_{p+m} ≥ Q_p exp(t_p ⌊m/2⌋)` (`t_p = sqrt(log Q_p)`) for a strictly
  increasing selection of prime-square periods `b_i^{n_i^2}` (`b_i ∈ {2,3}`) **of finite length** (the finite-prefix form of
  `JAMerged.merged_gap_seq_odd`);
* `kernel_tail_all`: for every `v > 0`, `∑_{d : v < cn d} K(d) ≤ C_1/(v Q)^3` with `C_1 = 200 D^4 + 8·(30D/7)`;
* `pair_geom`: `∑_{j<M} q^{⌊j/2⌋} ≤ 4` for `0 ≤ q ≤ 1/2`;
* `far_separated`: **(far-separated) of the paper.**  For a list of kernels `K_j = normK(Q_j)` with `Q_j ≥ 25 D`, `Q_j ∣ N`, whose scales
  satisfy the merged growth, `2m/N ≤ 3/(4 Q_p)` and `(8B)^2 e^{-3 t_p} ≤ 1/2` (`B = 30D/7`):
  `h_{p+1}(y) ≤ 512 C_1 ((Q_p/Q_{p+1})^3 + 4 (8B)^2 e^{-3 t_p})` for every `y` with `cn y ≥ 1/Q_p`,
  where `h_{p+1} = H_{p+1}/H_{p+1}(0)` is the normalized tail after the `p`-th kernel.
-/

namespace LeanCheck
namespace JAFarSep

open Finset JATransfer JAMulti JAProduct JAProduct2 JACenter JAFar JAKernTail JAMerged JAWindowQ

/-! ### Merged growth for a finite prefix -/

theorem merged_gap_fin (b n : ℕ → ℕ) (L : ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3)
    (hmono : ∀ a c, a < c → c < L → lp (b a) (n a) < lp (b c) (n c)) (i j : ℕ) (hij : i + 2 * j < L) :
    (j : ℝ) * Real.sqrt (lp (b i) (n i)) ≤ lp (b (i + 2 * j)) (n (i + 2 * j)) - lp (b i) (n i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hij' : i + 2 * j < L := by omega
    have ih' := ih hij'
    have hstep := merged_gap3 (fun k : Fin 3 => b (i + 2 * j + k)) (fun k : Fin 3 => n (i + 2 * j + k))
      (fun k => hb _) (hmono _ _ (by simp) (by simp; omega)) (hmono _ _ (by simp) (by simp; omega))
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, add_zero] at hstep
    have hge : lp (b i) (n i) ≤ lp (b (i + 2 * j)) (n (i + 2 * j)) := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; simp
      · exact (hmono i (i + 2 * j) (by omega) hij').le
    have hge' : Real.sqrt (lp (b i) (n i)) ≤ Real.sqrt (lp (b (i + 2 * j)) (n (i + 2 * j))) :=
      Real.sqrt_le_sqrt hge
    have e : i + 2 * (j + 1) = i + 2 * j + 2 := by ring
    rw [e]
    push_cast
    nlinarith

theorem merged_growth_fin (b n : ℕ → ℕ) (L : ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3)
    (hmono : ∀ a c, a < c → c < L → lp (b a) (n a) < lp (b c) (n c)) (i m : ℕ) (him : i + m < L) :
    Real.exp (lp (b i) (n i)) * Real.exp (Real.sqrt (lp (b i) (n i)) * ((m / 2 : ℕ) : ℝ)) ≤
      Real.exp (lp (b (i + m)) (n (i + m))) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := merged_gap_fin b n L hb hmono i (m / 2) (by omega)
  have h2 : lp (b (i + 2 * (m / 2))) (n (i + 2 * (m / 2))) ≤ lp (b (i + m)) (n (i + m)) := by
    by_cases h : 2 * (m / 2) = m
    · rw [h]
    · exact (hmono _ _ (by omega) him).le
  linarith

/-! ### Tails of the kernels, for all `v` -/

variable {N : ℕ} [NeZero N]

lemma kernel_tail_all (D : ℝ) (hD : 3 ≤ D) (Q : ℕ) [NeZero Q] (hQ : 25 * D ≤ Q) (hQN : Q ∣ N) (v : ℝ)
    (hv : 0 < v) :
    ∑ x : ZMod N, (if v < cn x then normK N Q (wQ D Q) x else 0) ≤
      (200 * D ^ 4 + 8 * (30 * D / 7)) / (v * Q) ^ 3 := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hD0 : 0 < D := by linarith
  have hvQ : 0 < v * Q := by positivity
  by_cases h2 : 2 ≤ v * Q
  · refine (kernel_tail_le' D hD Q hQ hQN v h2).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ 8 * (30 * D / 7) := by positivity
    linarith
  · push Not at h2
    have hB : ∑ x : ZMod N, normK N Q (wQ D Q) x ≤ 30 * D / 7 := sum_normK_le D hD Q hQ
    have htail : ∑ x : ZMod N, (if v < cn x then normK N Q (wQ D Q) x else 0) ≤
        ∑ x : ZMod N, normK N Q (wQ D Q) x :=
      Finset.sum_le_sum (fun x _ => by
        split_ifs
        · exact le_rfl
        · exact normK_nonneg _ _ _)
    have hcube : (v * Q) ^ 3 < 8 := by
      have : v * Q < 2 := h2
      nlinarith [pow_pos hvQ 2]
    have hBnn : 0 ≤ 30 * D / 7 := by positivity
    calc ∑ x : ZMod N, (if v < cn x then normK N Q (wQ D Q) x else 0) ≤ 30 * D / 7 := htail.trans hB
      _ ≤ 8 * (30 * D / 7) / (v * Q) ^ 3 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith
      _ ≤ (200 * D ^ 4 + 8 * (30 * D / 7)) / (v * Q) ^ 3 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have : 0 ≤ 200 * D ^ 4 := by positivity
          linarith

/-! ### A geometric sum -/

lemma pair_geom (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (M : ℕ) :
    ∑ j ∈ range M, q ^ (j / 2) ≤ 4 := by
  have hpair : ∀ M : ℕ, ∑ j ∈ range (2 * M), q ^ (j / 2) = 2 * ∑ l ∈ range M, q ^ l := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      have e1 : (2 * M) / 2 = M := by omega
      have e2 : (2 * M + 1) / 2 = M := by omega
      rw [e1, e2]
      ring
  have hgeom : ∀ M : ℕ, ∑ l ∈ range M, q ^ l ≤ 2 := by
    intro M
    have h : ∑ l ∈ range M, q ^ l * (1 - q) = 1 - q ^ M := by
      rw [← Finset.sum_mul, geom_sum_mul_neg]
    have hM : q ^ M ≤ 1 := pow_le_one₀ hq0 (by linarith)
    have hM0 : 0 ≤ q ^ M := pow_nonneg hq0 M
    have : (∑ l ∈ range M, q ^ l) * (1 - q) ≤ 1 := by
      rw [← Finset.sum_mul] at h; linarith
    nlinarith [Finset.sum_nonneg (fun l (_ : l ∈ range M) => pow_nonneg hq0 l)]
  calc ∑ j ∈ range M, q ^ (j / 2) ≤ ∑ j ∈ range (2 * M), q ^ (j / 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun j _ _ => pow_nonneg hq0 _)
    _ = 2 * ∑ l ∈ range M, q ^ l := hpair M
    _ ≤ 4 := by linarith [hgeom M]

/-! ### The far-separated estimate -/

lemma ratio_cube (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a * Real.exp x ≤ b) :
    (a / b) ^ 3 ≤ Real.exp (-(3 * x)) := by
  have h1 : a / b ≤ Real.exp (-x) := by
    rw [div_le_iff₀ hb]
    have hE : 0 < Real.exp (-x) := Real.exp_pos _
    calc a = a * Real.exp x * Real.exp (-x) := by rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ b * Real.exp (-x) := mul_le_mul_of_nonneg_right h hE.le
      _ = Real.exp (-x) * b := by ring
  calc (a / b) ^ 3 ≤ (Real.exp (-x)) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    _ = Real.exp (-(3 * x)) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

lemma term_algebra (B C₁ sp sl : ℝ) (j : ℕ) (hsp : 0 < sp) (hsl : 0 < sl) :
    B ^ j * (C₁ / ((1 / sp / 2 ^ (j + 3)) * sl) ^ 3) = 512 * C₁ * ((8 * B) ^ j * (sp / sl) ^ 3) := by
  have h8 : ((2 : ℝ) ^ (j + 3)) ^ 3 = 512 * 8 ^ j := by
    rw [← pow_mul, show (j + 3) * 3 = 3 * j + 9 by ring, pow_add, pow_mul]
    norm_num
    ring
  have h2 : (0 : ℝ) < 2 ^ (j + 3) := by positivity
  have e : ((1 / sp / 2 ^ (j + 3)) * sl) ^ 3 = sl ^ 3 / (sp ^ 3 * (512 * 8 ^ j)) := by
    rw [← h8]
    field_simp
  rw [e, mul_pow]
  field_simp

/-- **(far-separated)**. -/
theorem far_separated (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (sc : ℕ → ℕ) [hsc : ∀ j, NeZero (sc j)]
    (hQ : ∀ j, j < L → 25 * D ≤ sc j) (hQN : ∀ j, j < L → sc j ∣ N)
    (hgrow : ∀ p k, p + k < L → (sc p : ℝ) * Real.exp (Real.sqrt (Real.log (sc p)) * ((k / 2 : ℕ) : ℝ)) ≤
      sc (p + k))
    (p : ℕ) (hp : p + 1 ≤ L)
    (htop : (8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))) ≤ 1 / 2)
    (hε : (2 * m : ℝ) / N ≤ 3 / (4 * sc p)) (y : ZMod N) (hy : 1 / (sc p : ℝ) ≤ cn y) :
    Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 1)) y /
        Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 1)) 0 ≤
      512 * (200 * D ^ 4 + 8 * (30 * D / 7)) * (((sc p : ℝ) / sc (p + 1)) ^ 3 +
        4 * ((8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))))) := by
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
  have hu0 : (0 : ℝ) ≤ 1 / (sc p : ℝ) := by have := hscpos p; positivity
  have hu : (2 * m : ℝ) / N ≤ 3 * (1 / (sc p : ℝ)) / 4 := by
    have : 3 * (1 / (sc p : ℝ)) / 4 = 3 / (4 * sc p) := by field_simp
    rw [this]; exact hε
  have key := far_field_ZN m hm h2m ks B hB0 hgood (1 / (sc p : ℝ)) hu0 hu (L - (p + 1)) (p + 1)
    (by omega) y hy
  refine key.trans ?_
  -- bound the terms
  have hterm : ∀ j, j < L - (p + 1) →
      B ^ j * ∑ d : ZMod N, (if 1 / (sc p : ℝ) / 2 ^ (j + 3) < cn d then ks.getD (p + 1 + j) (fun _ => 0) d else 0)
        ≤ 512 * C₁ * ((8 * B) ^ j * ((sc p : ℝ) / sc (p + 1 + j)) ^ 3) := by
    intro j hj
    have hjL : p + 1 + j < L := by omega
    rw [hgetD _ hjL]
    have hv : 0 < 1 / (sc p : ℝ) / 2 ^ (j + 3) := by have := hscpos p; positivity
    have htail := kernel_tail_all (N := N) D hD (sc (p + 1 + j)) (hQ _ hjL) (hQN _ hjL) _ hv
    rw [← term_algebra B C₁ (sc p) (sc (p + 1 + j)) j (hscpos p) (hscpos _)]
    exact mul_le_mul_of_nonneg_left htail (pow_nonneg hB0 j)
  have hsum1 : ∑ j ∈ range (L - (p + 1)), B ^ j *
        ∑ d : ZMod N, (if 1 / (sc p : ℝ) / 2 ^ (j + 3) < cn d then ks.getD (p + 1 + j) (fun _ => 0) d else 0)
      ≤ ∑ j ∈ range (L - (p + 1)), 512 * C₁ * ((8 * B) ^ j * ((sc p : ℝ) / sc (p + 1 + j)) ^ 3) :=
    Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range.mp hj))
  refine hsum1.trans ?_
  rw [← Finset.mul_sum]
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have h512 : (0 : ℝ) ≤ 512 * C₁ := by positivity
  -- split off the first term
  rcases Nat.eq_zero_or_pos (L - (p + 1)) with h0 | hpos
  · rw [h0]
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    have : 0 ≤ ((sc p : ℝ) / sc (p + 1)) ^ 3 := by have := hscpos p; have := hscpos (p + 1); positivity
    have : 0 ≤ q := hq0
    positivity
  · obtain ⟨n', hn'⟩ : ∃ n', L - (p + 1) = n' + 1 := ⟨L - (p + 1) - 1, by omega⟩
    rw [hn', Finset.sum_range_succ']
    -- the later terms
    have hlater : ∑ j ∈ range n', (8 * B) ^ (j + 1) * ((sc p : ℝ) / sc (p + 1 + (j + 1))) ^ 3 ≤ 4 * q := by
      have hj : ∀ j ∈ range n', (8 * B) ^ (j + 1) * ((sc p : ℝ) / sc (p + 1 + (j + 1))) ^ 3 ≤ q * q ^ (j / 2) := by
        intro j hj'
        have hjn : j < n' := Finset.mem_range.mp hj'
        have hlt : p + (j + 2) < L := by omega
        have hg := hgrow p (j + 2) hlt
        have hc : ((j + 2) / 2 : ℕ) = j / 2 + 1 := by omega
        rw [hc] at hg
        have hratio := ratio_cube (sc p) (sc (p + (j + 2))) (t * ((j / 2 + 1 : ℕ) : ℝ)) (hscpos p) (hscpos _) hg
        have e : p + 1 + (j + 1) = p + (j + 2) := by ring
        rw [e]
        have hl : Real.exp (-(3 * (t * ((j / 2 + 1 : ℕ) : ℝ)))) = Real.exp (-(3 * t)) ^ (j / 2 + 1) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        rw [hl] at hratio
        have hpow : (8 * B) ^ (j + 1) ≤ (8 * B) ^ (2 * (j / 2 + 1)) :=
          pow_le_pow_right₀ hB1 (by omega)
        calc (8 * B) ^ (j + 1) * ((sc p : ℝ) / sc (p + (j + 2))) ^ 3
            ≤ (8 * B) ^ (2 * (j / 2 + 1)) * Real.exp (-(3 * t)) ^ (j / 2 + 1) :=
              mul_le_mul hpow hratio (by positivity) (by positivity)
          _ = q * q ^ (j / 2) := by
              rw [hq, ← pow_succ', mul_pow ((8 * B) ^ 2) (Real.exp (-(3 * t))) (j / 2 + 1), ← pow_mul]
      calc ∑ j ∈ range n', (8 * B) ^ (j + 1) * ((sc p : ℝ) / sc (p + 1 + (j + 1))) ^ 3
          ≤ ∑ j ∈ range n', q * q ^ (j / 2) := Finset.sum_le_sum hj
        _ = q * ∑ j ∈ range n', q ^ (j / 2) := by rw [Finset.mul_sum]
        _ ≤ q * 4 := mul_le_mul_of_nonneg_left (pair_geom q hq0 hq2 n') hq0
        _ = 4 * q := by ring
    have hfirst : (8 * B) ^ 0 * ((sc p : ℝ) / sc (p + 1 + 0)) ^ 3 = ((sc p : ℝ) / sc (p + 1)) ^ 3 := by
      simp
    rw [hfirst]
    calc 512 * C₁ * (∑ j ∈ range n', (8 * B) ^ (j + 1) * ((sc p : ℝ) / sc (p + 1 + (j + 1))) ^ 3 +
          ((sc p : ℝ) / sc (p + 1)) ^ 3)
        ≤ 512 * C₁ * (4 * q + ((sc p : ℝ) / sc (p + 1)) ^ 3) :=
          mul_le_mul_of_nonneg_left (by linarith) h512
      _ = _ := by ring

#print axioms merged_growth_fin
#print axioms kernel_tail_all
#print axioms pair_geom
#print axioms far_separated

/-! ### The scales are prime squares: the growth hypothesis holds -/

lemma exp_lp (b n : ℕ) (hb : 2 ≤ b) : Real.exp (lp b n) = ((b ^ (n ^ 2) : ℕ) : ℝ) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have h1 : Real.log (((b : ℝ)) ^ (n ^ 2)) = (n : ℝ) ^ 2 * Real.log b := by
    rw [Real.log_pow]; push_cast; ring
  unfold JAMerged.lp
  rw [← h1, Real.exp_log (by positivity)]
  push_cast; ring

lemma log_scale (b n : ℕ) (hb : 2 ≤ b) : Real.log ((b ^ (n ^ 2) : ℕ) : ℝ) = lp b n := by
  rw [← exp_lp b n hb, Real.log_exp]

/-- **Merged growth for the scales `b_i^{n_i^2}`** (strictly increasing, finite prefix): the hypothesis `hgrow` of
`far_separated`. -/
theorem hgrow_of_merged (b n : ℕ → ℕ) (L : ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3)
    (hmono : ∀ a c, a < c → c < L → lp (b a) (n a) < lp (b c) (n c)) :
    ∀ p k, p + k < L →
      (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) * Real.exp (Real.sqrt (Real.log (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)) *
        ((k / 2 : ℕ) : ℝ)) ≤ (((b (p + k)) ^ ((n (p + k)) ^ 2) : ℕ) : ℝ) := by
  intro p k hpk
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h <;> omega
  have h := merged_growth_fin b n L hb hmono p k hpk
  rw [exp_lp _ _ (hb2 p), exp_lp _ _ (hb2 (p + k))] at h
  rw [log_scale _ _ (hb2 p)]
  exact h

/-- **(far-separated) for a sorted selection of prime-square scales.** -/
theorem far_separated_primes (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3) (hn : ∀ i, 1 ≤ n i)
    (hmono : ∀ a c, a < c → c < L → lp (b a) (n a) < lp (b c) (n c))
    (hQ : ∀ j, j < L → 25 * D ≤ ((b j) ^ ((n j) ^ 2) : ℕ)) (hQN : ∀ j, j < L → (b j) ^ ((n j) ^ 2) ∣ N)
    (p : ℕ) (hp : p + 1 ≤ L)
    (htop : (8 * (30 * D / 7)) ^ 2 *
      Real.exp (-(3 * Real.sqrt (lp (b p) (n p)))) ≤ 1 / 2)
    (hε : (2 * m : ℝ) / N ≤ 3 / (4 * (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)))
    (y : ZMod N) (hy : 1 / (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) ≤ cn y) :
    haveI : ∀ j, NeZero ((b j) ^ ((n j) ^ 2)) := fun j =>
      ⟨pow_ne_zero _ (by rcases hb j with h | h <;> omega)⟩
    Hs (Ftri N m) (((List.range L).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
        (wQ D ((b j) ^ ((n j) ^ 2))))).drop (p + 1)) y /
      Hs (Ftri N m) (((List.range L).map (fun j => normK N ((b j) ^ ((n j) ^ 2))
        (wQ D ((b j) ^ ((n j) ^ 2))))).drop (p + 1)) 0 ≤
      512 * (200 * D ^ 4 + 8 * (30 * D / 7)) * (((((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) /
          (((b (p + 1)) ^ ((n (p + 1)) ^ 2) : ℕ) : ℝ)) ^ 3 +
        4 * ((8 * (30 * D / 7)) ^ 2 * Real.exp (-(3 * Real.sqrt (lp (b p) (n p)))))) := by
  haveI : ∀ j, NeZero ((b j) ^ ((n j) ^ 2)) := fun j =>
    ⟨pow_ne_zero _ (by rcases hb j with h | h <;> omega)⟩
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h <;> omega
  have hlog : Real.sqrt (Real.log (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)) = Real.sqrt (lp (b p) (n p)) := by
    rw [log_scale _ _ (hb2 p)]
  have := far_separated (N := N) D hD m hm h2m L (fun j => (b j) ^ ((n j) ^ 2)) hQ hQN
    (hgrow_of_merged b n L hb hmono) p hp (by rw [hlog]; exact htop) hε y hy
  rw [hlog] at this
  exact this

#print axioms hgrow_of_merged
#print axioms far_separated_primes

end JAFarSep
end LeanCheck
