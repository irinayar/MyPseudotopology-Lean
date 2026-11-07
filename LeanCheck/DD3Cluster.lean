import Mathlib
import LeanCheck.JAClose
import LeanCheck.JAProductFinal
import LeanCheck.DD3Reduction

/-!
# Diagonal density for three primes: the cluster estimates (Lean check)

Scope. Second phase of the Lean version of the conditional proof of `DD({2,3,5})` (research note
`TVGplus_conditional_DD235_2026-11-07.md`, items 1 and 3). The factor estimates of the normalized product argument
(`JAFarSep`, `JASep`, `JAClose`, `JAProductFinal`) are re-proved for scales that come from **three** chains
`2^(a^2), 3^(b^2), 5^(c^2)`, where only the growth `Q_{p+k} ≥ Q_p exp(t_p ⌊k/3⌋)` (period three) is available:

* `geom_three`, `sum_tau3`, `sum_tau3b`: the summation of the far-field terms with period-three growth;
* `far_separated3`, `far_beyond3`: the far-field bounds after one level (with monotone scales) and after two levels
  (with the extra hypothesis that the third level satisfies `Q_{p+2} ≥ Q_p exp c`);
* `separated_factor_abs`, `close_factor_abs`: copies of `JASep.separated_factor` and `JAClose.close_factor` in which the
  far-field bound is a hypothesis;
* `separated_factor3`: for a separated level (`Q_{p+1} ≥ t_p Q_p`)
  `f_p - 1 ≤ 200 D⁴ t⁻⁶ + B · 512 C₁ ((1 + 8B) t⁻³ + 48 B q₃)`, `q₃ = (8B)³ e^{-3t}`;
* `close_factor3`: for a close pair, with the third level beyond `Q_p exp(a(t) + log t)` (this is the place where the
  hypothesis `H(2,3,5)` of the note enters) and the two-term separation `hTT` as a hypothesis;
* `sep_cube3`, `close_cube3_G`: both right-hand sides are at most a constant times `t⁻³` (for `t ≥ 1`, resp. `t ≥ T`
  for a close-growth profile), so that `∑ t_i⁻³ < ∞` makes the product converge;
* `merged_gap_fin3`, `hgrow3_of_merged`, `hmon_of_merged`: for a strictly increasing selection of prime-square periods
  of the bases `2, 3, 5` the growth hypothesis (period three) and the monotonicity of the scales hold.

Not formalized: the final product bound for three chains (`product_final` uses the summability for two bases), the assembly
of the central bound, the Fourier step, the hypothesis `H(2,3,5)` itself and its use for the sorted list of all levels,
the compact-quotient step, the separation for the pairs `(2,5)`, `(3,5)`. The deprecation and unused-argument warnings of
the Lean linter come from proofs copied from `JASep` and `JAClose`. A Lean proof verifies its formal statement under its
hypotheses; the correspondence with the research note requires mathematical review.
-/


namespace LeanCheck
namespace DD3Cluster

open Finset JATransfer JAMulti JAProduct JAProduct2 JACenter JAFar JAKernTail JAFarSep JASep JAClose JAWindowQ MixedPrime

variable {N : ℕ} [NeZero N]

/-! ### Geometric sums and the two summation lemmas -/

lemma geom_three (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (M : ℕ) :
    ∑ j ∈ range M, q ^ (j / 3) ≤ 6 := by
  have hpair : ∀ M : ℕ, ∑ j ∈ range (3 * M), q ^ (j / 3) = 3 * ∑ l ∈ range M, q ^ l := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show 3 * (M + 1) = 3 * M + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have e1 : (3 * M) / 3 = M := by omega
      have e2 : (3 * M + 1) / 3 = M := by omega
      have e3 : (3 * M + 1 + 1) / 3 = M := by omega
      rw [e1, e2, e3]
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
  calc ∑ j ∈ range M, q ^ (j / 3) ≤ ∑ j ∈ range (3 * M), q ^ (j / 3) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun j _ _ => pow_nonneg hq0 _)
    _ = 3 * ∑ l ∈ range M, q ^ l := hpair M
    _ ≤ 6 := by linarith [hgeom M]

/-- Summation of the terms of the far-field expansion after one level: the first term is bounded by `r`, the second by
`8 B r` (monotone scales), the later ones by `8 B q^(j/3+1)` (growth with period three). -/
lemma sum_tau3 (B q3 r : ℝ) (hB : 0 ≤ B) (hq0 : 0 ≤ q3) (hq2 : q3 ≤ 1 / 2) (hr : 0 ≤ r) (n : ℕ)
    (τ : ℕ → ℝ) (h0 : 0 < n → τ 0 ≤ r) (h1 : 1 < n → τ 1 ≤ 8 * B * r)
    (hl : ∀ j, j + 2 < n → τ (j + 2) ≤ 8 * B * q3 ^ (j / 3 + 1)) :
    ∑ j ∈ range n, τ j ≤ (1 + 8 * B) * r + 48 * B * q3 := by
  have hBr : 0 ≤ B * r := mul_nonneg hB hr
  have hBq : 0 ≤ B * q3 := mul_nonneg hB hq0
  rcases n with _ | _ | n'
  · simp only [Finset.range_zero, Finset.sum_empty]
    nlinarith
  · rw [Finset.sum_range_one]
    have := h0 one_pos
    nlinarith
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hsum : ∑ j ∈ range n', τ (j + 1 + 1) ≤ 48 * B * q3 := by
      calc ∑ j ∈ range n', τ (j + 1 + 1) ≤ ∑ j ∈ range n', 8 * B * q3 ^ (j / 3 + 1) :=
            Finset.sum_le_sum (fun j hj => hl j (by have := Finset.mem_range.mp hj; omega))
        _ = 8 * B * q3 * ∑ j ∈ range n', q3 ^ (j / 3) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun j _ => by rw [pow_succ']; ring)
        _ ≤ 8 * B * q3 * 6 :=
            mul_le_mul_of_nonneg_left (geom_three q3 hq0 hq2 n') (by positivity)
        _ = 48 * B * q3 := by ring
    have h0' := h0 (by omega)
    have h1' := h1 (by omega)
    simp only [zero_add]
    nlinarith

/-- The same for the far field after two levels: the first term is bounded by `e3`, the later ones by `q3^(j/3+1)`. -/
lemma sum_tau3b (q3 e3 : ℝ) (hq0 : 0 ≤ q3) (hq2 : q3 ≤ 1 / 2) (he : 0 ≤ e3) (n : ℕ)
    (σ : ℕ → ℝ) (h0 : 0 < n → σ 0 ≤ e3) (hl : ∀ j, j + 1 < n → σ (j + 1) ≤ q3 ^ (j / 3 + 1)) :
    ∑ j ∈ range n, σ j ≤ e3 + 6 * q3 := by
  rcases n with _ | n'
  · simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · rw [Finset.sum_range_succ']
    have hsum : ∑ j ∈ range n', σ (j + 1) ≤ 6 * q3 := by
      calc ∑ j ∈ range n', σ (j + 1) ≤ ∑ j ∈ range n', q3 ^ (j / 3 + 1) :=
            Finset.sum_le_sum (fun j hj => hl j (by have := Finset.mem_range.mp hj; omega))
        _ = q3 * ∑ j ∈ range n', q3 ^ (j / 3) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun j _ => by rw [pow_succ'])
        _ ≤ q3 * 6 := mul_le_mul_of_nonneg_left (geom_three q3 hq0 hq2 n') hq0
        _ = 6 * q3 := by ring
    have := h0 (Nat.succ_pos _)
    linarith

/-! ### Far field with growth of period three -/

/-- **(far-separated), three chains.** Scales are monotone and satisfy the growth `Q_{p+k} ≥ Q_p exp(t_p ⌊k/3⌋)`. -/
theorem far_separated3 (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (sc : ℕ → ℕ) [hsc : ∀ j, NeZero (sc j)]
    (hQ : ∀ j, j < L → 25 * D ≤ sc j) (hQN : ∀ j, j < L → sc j ∣ N)
    (hmon : ∀ i j, i ≤ j → j < L → sc i ≤ sc j)
    (hgrow : ∀ p k, p + k < L →
      (sc p : ℝ) * Real.exp (Real.sqrt (Real.log (sc p)) * ((k / 3 : ℕ) : ℝ)) ≤ sc (p + k))
    (p : ℕ) (hp : p + 1 ≤ L)
    (htop : (8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))) ≤ 1 / 2)
    (hε : (2 * m : ℝ) / N ≤ 3 / (4 * sc p)) (y : ZMod N) (hy : 1 / (sc p : ℝ) ≤ cn y) :
    Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 1)) y /
        Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 1)) 0 ≤
      512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
        ((1 + 8 * (30 * D / 7)) * ((sc p : ℝ) / sc (p + 1)) ^ 3 +
          48 * (30 * D / 7) * ((8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))))) := by
  classical
  set B : ℝ := 30 * D / 7 with hBdef
  set C₁ : ℝ := 200 * D ^ 4 + 8 * B with hC₁
  set t : ℝ := Real.sqrt (Real.log (sc p)) with ht
  set q3 : ℝ := (8 * B) ^ 3 * Real.exp (-(3 * t)) with hq3
  set ks : List (ZMod N → ℝ) := (List.range L).map (fun j => normK N (sc j) (wQ D (sc j))) with hks
  have hD0 : 0 < D := by linarith
  have hB1 : 1 ≤ 8 * B := by rw [hBdef]; linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hq0 : 0 ≤ q3 := by rw [hq3]; positivity
  have hq2 : q3 ≤ 1 / 2 := htop
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
  set r : ℝ := ((sc p : ℝ) / sc (p + 1)) ^ 3 with hr
  have hr0 : 0 ≤ r := by have := hscpos p; have := hscpos (p + 1); rw [hr]; positivity
  have htau := sum_tau3 B q3 r hB0 hq0 hq2 hr0 (L - (p + 1))
    (fun j => (8 * B) ^ j * ((sc p : ℝ) / sc (p + 1 + j)) ^ 3)
    (by intro _; simp [hr])
    (by
      intro h1
      have hmon' : sc (p + 1) ≤ sc (p + 1 + 1) := hmon _ _ (by omega) (by omega)
      have hcast : (sc (p + 1) : ℝ) ≤ sc (p + 1 + 1) := by exact_mod_cast hmon'
      have hdiv : (sc p : ℝ) / sc (p + 1 + 1) ≤ (sc p : ℝ) / sc (p + 1) :=
        div_le_div_of_nonneg_left (hscpos p).le (hscpos _) hcast
      have hpow := pow_le_pow_left₀ (by have := hscpos p; have := hscpos (p + 1 + 1); positivity) hdiv 3
      simp only [pow_one]
      rw [hr]
      have : 0 ≤ 8 * B := by linarith
      nlinarith [pow_le_pow_left₀ (by have := hscpos p; have := hscpos (p + 1 + 1); positivity) hdiv 3])
    (by
      intro j hj
      have hlt : p + (j + 3) < L := by omega
      have hg := hgrow p (j + 3) hlt
      have hc : ((j + 3) / 3 : ℕ) = j / 3 + 1 := by omega
      rw [hc] at hg
      have hratio := ratio_cube (sc p) (sc (p + (j + 3))) (t * ((j / 3 + 1 : ℕ) : ℝ)) (hscpos p) (hscpos _) hg
      have e : p + 1 + (j + 2) = p + (j + 3) := by ring
      show (8 * B) ^ (j + 2) * ((sc p : ℝ) / sc (p + 1 + (j + 2))) ^ 3 ≤ 8 * B * q3 ^ (j / 3 + 1)
      rw [e]
      have hl : Real.exp (-(3 * (t * ((j / 3 + 1 : ℕ) : ℝ)))) = Real.exp (-(3 * t)) ^ (j / 3 + 1) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      rw [hl] at hratio
      have hpow : (8 * B) ^ (j + 2) ≤ (8 * B) ^ (1 + 3 * (j / 3 + 1)) :=
        pow_le_pow_right₀ hB1 (by omega)
      have hq3pow : 8 * B * q3 ^ (j / 3 + 1) = (8 * B) ^ (1 + 3 * (j / 3 + 1)) * Real.exp (-(3 * t)) ^ (j / 3 + 1) := by
        rw [hq3, mul_pow, ← pow_mul, pow_add, pow_one]; ring
      rw [hq3pow]
      exact mul_le_mul hpow hratio (by positivity) (by positivity))
  calc 512 * C₁ * ∑ j ∈ range (L - (p + 1)), (8 * B) ^ j * ((sc p : ℝ) / sc (p + 1 + j)) ^ 3
      ≤ 512 * C₁ * ((1 + 8 * B) * r + 48 * B * q3) := mul_le_mul_of_nonneg_left htau h512
    _ = _ := by rw [hr, hq3]

/-- **Far field after two levels, three chains**: the scale `p + 2` is beyond `Q_p exp c`, all later ones grow with period three. -/
theorem far_beyond3 (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (sc : ℕ → ℕ) [hsc : ∀ j, NeZero (sc j)]
    (hQ : ∀ j, j < L → 25 * D ≤ sc j) (hQN : ∀ j, j < L → sc j ∣ N)
    (hgrow : ∀ p k, p + k < L →
      (sc p : ℝ) * Real.exp (Real.sqrt (Real.log (sc p)) * ((k / 3 : ℕ) : ℝ)) ≤ sc (p + k))
    (p : ℕ) (hp : p + 2 ≤ L)
    (htop : (8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))) ≤ 1 / 2)
    (c : ℝ) (hthird : p + 2 < L → (sc p : ℝ) * Real.exp c ≤ sc (p + 2))
    (u : ℝ) (hu : 0 < u) (hε : (2 * m : ℝ) / N ≤ 3 * u / 4) (y : ZMod N) (hy : u ≤ cn y) :
    Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 2)) y /
        Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 2)) 0 ≤
      512 * (200 * D ^ 4 + 8 * (30 * D / 7)) * (1 / (u * sc p)) ^ 3 *
        (Real.exp (-(3 * c)) +
          6 * ((8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))))) := by
  classical
  set B : ℝ := 30 * D / 7 with hBdef
  set C₁ : ℝ := 200 * D ^ 4 + 8 * B with hC₁
  set t : ℝ := Real.sqrt (Real.log (sc p)) with ht
  set q3 : ℝ := (8 * B) ^ 3 * Real.exp (-(3 * t)) with hq3
  set ks : List (ZMod N → ℝ) := (List.range L).map (fun j => normK N (sc j) (wQ D (sc j))) with hks
  have hD0 : 0 < D := by linarith
  have hB1 : 1 ≤ 8 * B := by rw [hBdef]; linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hq0 : 0 ≤ q3 := by rw [hq3]; positivity
  have hq2 : q3 ≤ 1 / 2 := htop
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
        ≤ 512 * C₁ * W * ((8 * B) ^ j * ((sc p : ℝ) / sc (p + 2 + j)) ^ 3) := by
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
    have hsplit : ((1 / u) / (sc (p + 2 + j) : ℝ)) ^ 3 = W * ((sc p : ℝ) / sc (p + 2 + j)) ^ 3 := by
      rw [hW, ← mul_pow]
      congr 1
      have := hscpos p
      field_simp
    rw [hsplit]
    have : 512 * C₁ * ((8 * B) ^ j * (W * ((sc p : ℝ) / sc (p + 2 + j)) ^ 3)) =
        512 * C₁ * W * ((8 * B) ^ j * ((sc p : ℝ) / sc (p + 2 + j)) ^ 3) := by ring
    rw [this]
  have hsum1 : ∑ j ∈ range (L - (p + 2)), B ^ j *
        ∑ d : ZMod N, (if u / 2 ^ (j + 3) < cn d then ks.getD (p + 2 + j) (fun _ => 0) d else 0)
      ≤ ∑ j ∈ range (L - (p + 2)), 512 * C₁ * W * ((8 * B) ^ j * ((sc p : ℝ) / sc (p + 2 + j)) ^ 3) :=
    Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range.mp hj))
  refine hsum1.trans ?_
  rw [← Finset.mul_sum]
  have hC0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hsig := sum_tau3b q3 (Real.exp (-(3 * c))) hq0 hq2 (Real.exp_pos _).le (L - (p + 2))
    (fun j => (8 * B) ^ j * ((sc p : ℝ) / sc (p + 2 + j)) ^ 3)
    (by
      intro h0
      have hlt : p + 2 < L := by omega
      have h := hthird hlt
      have hratio := ratio_cube (sc p) (sc (p + 2)) c (hscpos p) (hscpos _) h
      simpa using hratio)
    (by
      intro j hj
      have hlt : p + (j + 3) < L := by omega
      have hg := hgrow p (j + 3) hlt
      have hc3 : ((j + 3) / 3 : ℕ) = j / 3 + 1 := by omega
      rw [hc3] at hg
      have hratio := ratio_cube (sc p) (sc (p + (j + 3))) (t * ((j / 3 + 1 : ℕ) : ℝ)) (hscpos p) (hscpos _) hg
      have e : p + 2 + (j + 1) = p + (j + 3) := by ring
      show (8 * B) ^ (j + 1) * ((sc p : ℝ) / sc (p + 2 + (j + 1))) ^ 3 ≤ q3 ^ (j / 3 + 1)
      rw [e]
      have hl : Real.exp (-(3 * (t * ((j / 3 + 1 : ℕ) : ℝ)))) = Real.exp (-(3 * t)) ^ (j / 3 + 1) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      rw [hl] at hratio
      have hpow : (8 * B) ^ (j + 1) ≤ (8 * B) ^ (3 * (j / 3 + 1)) :=
        pow_le_pow_right₀ hB1 (by omega)
      have hq3pow : q3 ^ (j / 3 + 1) = (8 * B) ^ (3 * (j / 3 + 1)) * Real.exp (-(3 * t)) ^ (j / 3 + 1) := by
        rw [hq3, mul_pow, ← pow_mul]
      rw [hq3pow]
      exact mul_le_mul hpow hratio (by positivity) (by positivity))
  have h512 : (0 : ℝ) ≤ 512 * C₁ * W := by positivity
  calc 512 * C₁ * W * ∑ j ∈ range (L - (p + 2)), (8 * B) ^ j * ((sc p : ℝ) / sc (p + 2 + j)) ^ 3
      ≤ 512 * C₁ * W * (Real.exp (-(3 * c)) + 6 * q3) := mul_le_mul_of_nonneg_left hsig h512
    _ = _ := by rw [hW, hq3]
/-! ### The separated-level estimate with an abstract far-field bound -/

/-- **Separated level**, with the far-field bound `R` for the tail after the level as a hypothesis (copy of
`JASep.separated_factor` in which the call of `far_separated` is replaced by the hypotheses `hR0`, `hfar'`). -/
theorem separated_factor_abs (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (sc : ℕ → ℕ) [hsc : ∀ j, NeZero (sc j)]
    (hQ : ∀ j, j < L → 25 * D ≤ sc j) (hQN : ∀ j, j < L → sc j ∣ N)
    (p : ℕ) (hp : p + 1 ≤ L)
    (ht2 : 2 ≤ Real.sqrt (Real.log (sc p))) (R : ℝ) (hR0 : 0 ≤ R)
    (hfar' : ∀ y : ZMod N, 1 / (sc p : ℝ) ≤ cn y →
      Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 1)) y /
        Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 1)) 0 ≤ R) :
    Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop p) 0 /
        Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 1)) 0 - 1 ≤
      200 * D ^ 4 / (Real.sqrt (Real.log (sc p))) ^ 6 + 30 * D / 7 * R := by
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
  rw [hf]
  calc ∑ d, K d * (H' (0 - d) / H' 0) - 1
      ≤ K 0 + ∑ d, (if v < cn d then K d else 0) + R * ∑ d, K d - 1 := by linarith
    _ ≤ 200 * D ^ 4 / t ^ 6 + B * R := by
        rw [hK0]
        have : R * ∑ d, K d ≤ R * B := mul_le_mul_of_nonneg_left hKB hR0
        nlinarith

/-! ### The close-pair estimate with an abstract far-field bound -/

set_option maxHeartbeats 1600000 in
/-- **Close pair**, with the far-field bound `Φ` for the tail after the pair as a hypothesis (copy of `JAClose.close_factor`
in which the call of `far_beyond` is replaced by the hypotheses `hΦ0`, `hfarΦ`). -/
theorem close_factor_abs (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (sc : ℕ → ℕ) [hsc : ∀ j, NeZero (sc j)]
    (hQ : ∀ j, j < L → 25 * D ≤ sc j) (hQN : ∀ j, j < L → sc j ∣ N)
    (p : ℕ) (hp : p + 2 ≤ L)
    (ht2 : 2 ≤ Real.sqrt (Real.log (sc p))) (a : ℝ → ℝ)
    (hTT : ∀ r s : ℤ, r ≠ 0 → |r| ≤ (⌈(Real.sqrt (Real.log (sc p))) ^ 2⌉₊ : ℤ) →
      |s| ≤ (⌈4 * (Real.sqrt (Real.log (sc p))) ^ 3⌉₊ : ℤ) →
      Real.exp (-(a (Real.sqrt (Real.log (sc p))))) / sc p ≤
        nrm ((r : ℝ) / sc p + (s : ℝ) / sc (p + 1)))
    (Φ : ℝ) (hΦ0 : 0 ≤ Φ)
    (hfarΦ : ∀ y : ZMod N, Real.exp (-(a (Real.sqrt (Real.log (sc p))))) / sc p ≤ cn y →
      Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 2)) y /
        Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 2)) 0 ≤ Φ) :
    Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop p) 0 /
        Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 1)) 0 - 1 ≤
      200 * D ^ 4 / (Real.sqrt (Real.log (sc p))) ^ 6 +
        30 * D / 7 * (200 * D ^ 4 / (4 * (Real.sqrt (Real.log (sc p))) ^ 3) ^ 3) +
        (30 * D / 7) ^ 2 * Φ := by
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

/-! ### The cluster estimates for three chains -/

/-- **(separated-factor), three chains.** -/
theorem separated_factor3 (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (sc : ℕ → ℕ) [hsc : ∀ j, NeZero (sc j)]
    (hQ : ∀ j, j < L → 25 * D ≤ sc j) (hQN : ∀ j, j < L → sc j ∣ N)
    (hmon : ∀ i j, i ≤ j → j < L → sc i ≤ sc j)
    (hgrow : ∀ p k, p + k < L →
      (sc p : ℝ) * Real.exp (Real.sqrt (Real.log (sc p)) * ((k / 3 : ℕ) : ℝ)) ≤ sc (p + k))
    (p : ℕ) (hp : p + 1 ≤ L)
    (htop : (8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))) ≤ 1 / 2)
    (hε : (2 * m : ℝ) / N ≤ 3 / (4 * sc p))
    (ht2 : 2 ≤ Real.sqrt (Real.log (sc p)))
    (hsep : Real.sqrt (Real.log (sc p)) * (sc p : ℝ) ≤ sc (p + 1)) :
    Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop p) 0 /
        Hs (Ftri N m) (((List.range L).map (fun j => normK N (sc j) (wQ D (sc j)))).drop (p + 1)) 0 - 1 ≤
      200 * D ^ 4 / (Real.sqrt (Real.log (sc p))) ^ 6 +
        30 * D / 7 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
          ((1 + 8 * (30 * D / 7)) * (1 / Real.sqrt (Real.log (sc p))) ^ 3 +
            48 * (30 * D / 7) *
              ((8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (Real.log (sc p))))))) := by
  classical
  set B : ℝ := 30 * D / 7 with hBdef
  set C₁ : ℝ := 200 * D ^ 4 + 8 * B with hC₁
  set t : ℝ := Real.sqrt (Real.log (sc p)) with ht
  set q3 : ℝ := (8 * B) ^ 3 * Real.exp (-(3 * t)) with hq3
  have hD0 : 0 < D := by linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hC0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hq0 : 0 ≤ q3 := by rw [hq3]; positivity
  have ht0 : 0 < t := by linarith
  have hscpos : ∀ j, (0 : ℝ) < sc j := fun j => by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (sc j))
  have hfar := far_separated3 (N := N) D hD m hm h2m L sc hQ hQN hmon hgrow p hp htop hε
  set r : ℝ := ((sc p : ℝ) / sc (p + 1)) ^ 3 with hr
  have hr0 : r ≤ (1 / t) ^ 3 := by
    have hpos1 := hscpos p
    have hpos2 := hscpos (p + 1)
    have h : (sc p : ℝ) / sc (p + 1) ≤ 1 / t := by
      rw [div_le_div_iff₀ hpos2 ht0]; linarith
    exact pow_le_pow_left₀ (by positivity) h 3
  have hrnn : 0 ≤ r := by have := hscpos p; have := hscpos (p + 1); rw [hr]; positivity
  set R : ℝ := 512 * C₁ * ((1 + 8 * B) * r + 48 * B * q3) with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have habs := separated_factor_abs (N := N) D hD m hm h2m L sc hQ hQN p hp ht2 R hR0
    (fun y hy => hfar y hy)
  refine habs.trans ?_
  show 200 * D ^ 4 / t ^ 6 + B * R ≤
    200 * D ^ 4 / t ^ 6 + B * (512 * C₁ * ((1 + 8 * B) * (1 / t) ^ 3 + 48 * B * q3))
  have hle : R ≤ 512 * C₁ * ((1 + 8 * B) * (1 / t) ^ 3 + 48 * B * q3) := by
    rw [hR]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (1 + 8 * B) * r ≤ (1 + 8 * B) * (1 / t) ^ 3 :=
      mul_le_mul_of_nonneg_left hr0 (by linarith)
    linarith
  have := mul_le_mul_of_nonneg_left hle hB0
  linarith

/-- **(close-factor), three chains.** The third level beyond the close pair satisfies
`Q_{p+2} ≥ Q_p exp(a(t) + log t)` (`t = sqrt (log Q_p)`); this is where the finiteness hypothesis `H(2,3,5)` enters. -/
theorem close_factor3 (D : ℝ) (hD : 3 ≤ D) (m : ℕ) (hm : 1 ≤ m) (h2m : 2 * m ≤ N)
    (L : ℕ) (sc : ℕ → ℕ) [hsc : ∀ j, NeZero (sc j)]
    (hQ : ∀ j, j < L → 25 * D ≤ sc j) (hQN : ∀ j, j < L → sc j ∣ N)
    (hgrow : ∀ p k, p + k < L →
      (sc p : ℝ) * Real.exp (Real.sqrt (Real.log (sc p)) * ((k / 3 : ℕ) : ℝ)) ≤ sc (p + k))
    (p : ℕ) (hp : p + 2 ≤ L)
    (htop : (8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))) ≤ 1 / 2)
    (ht2 : 2 ≤ Real.sqrt (Real.log (sc p))) (a : ℝ → ℝ)
    (hthird : p + 2 < L → (sc p : ℝ) *
      Real.exp (a (Real.sqrt (Real.log (sc p))) + Real.log (Real.sqrt (Real.log (sc p)))) ≤ sc (p + 2))
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
        (30 * D / 7) ^ 2 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
          (1 / (Real.exp (-(a (Real.sqrt (Real.log (sc p))))) / sc p * sc p)) ^ 3 *
          (Real.exp (-(3 * (a (Real.sqrt (Real.log (sc p))) + Real.log (Real.sqrt (Real.log (sc p)))))) +
            6 * ((8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (Real.log (sc p))))))) := by
  classical
  have hscpos : ∀ j, (0 : ℝ) < sc j := fun j => by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (sc j))
  have hupos : 0 < Real.exp (-(a (Real.sqrt (Real.log (sc p))))) / sc p := by
    have := hscpos p; positivity
  have hfar := far_beyond3 (N := N) D hD m hm h2m L sc hQ hQN hgrow p hp htop
    (a (Real.sqrt (Real.log (sc p))) + Real.log (Real.sqrt (Real.log (sc p)))) hthird _ hupos hε
  have hΦ0 : 0 ≤ 512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
      (1 / (Real.exp (-(a (Real.sqrt (Real.log (sc p))))) / sc p * sc p)) ^ 3 *
      (Real.exp (-(3 * (a (Real.sqrt (Real.log (sc p))) + Real.log (Real.sqrt (Real.log (sc p)))))) +
        6 * ((8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * Real.sqrt (Real.log (sc p)))))) := by
    have := hscpos p
    have hD0 : 0 < D := by linarith
    positivity
  exact close_factor_abs (N := N) D hD m hm h2m L sc hQ hQN p hp ht2 a hTT _ hΦ0
    (fun y hy => hfar y hy)

/-! ### Cubes -/

/-- The right-hand side of `separated_factor3` is at most `Cs (1/t)^3` for `t ≥ 1`. -/
lemma sep_cube3 (D t : ℝ) (hD : 3 ≤ D) (ht : 1 ≤ t) :
    200 * D ^ 4 / t ^ 6 +
        30 * D / 7 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
          ((1 + 8 * (30 * D / 7)) * (1 / t) ^ 3 +
            48 * (30 * D / 7) * ((8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * t))))) ≤
      (200 * D ^ 4 + 30 * D / 7 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
        ((1 + 8 * (30 * D / 7)) + 48 * (30 * D / 7) * (8 * (30 * D / 7)) ^ 3))) * (1 / t) ^ 3 := by
  have hD0 : 0 < D := by linarith
  set B : ℝ := 30 * D / 7 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hC0 : 0 ≤ 200 * D ^ 4 + 8 * B := by positivity
  have hs0 : 0 ≤ (1 / t) ^ 3 := by positivity
  have he := JAProductFinal.exp_neg3_le t ht
  have h6 := JAProductFinal.inv_pow6_le t ht
  have e1 : 200 * D ^ 4 / t ^ 6 = 200 * D ^ 4 * (1 / t ^ 6) := by ring
  have h8 : 0 ≤ 48 * B * (8 * B) ^ 3 := by positivity
  have h9 : 48 * B * ((8 * B) ^ 3 * Real.exp (-(3 * t))) ≤ 48 * B * (8 * B) ^ 3 * (1 / t) ^ 3 := by
    have := mul_le_mul_of_nonneg_left he h8
    nlinarith
  have h10 : (1 + 8 * B) * (1 / t) ^ 3 + 48 * B * ((8 * B) ^ 3 * Real.exp (-(3 * t))) ≤
      ((1 + 8 * B) + 48 * B * (8 * B) ^ 3) * (1 / t) ^ 3 := by nlinarith
  have h11 := mul_le_mul_of_nonneg_left h10 (by positivity : 0 ≤ 512 * (200 * D ^ 4 + 8 * B))
  have h12 := mul_le_mul_of_nonneg_left h11 hB0
  have h13 : 200 * D ^ 4 * (1 / t ^ 6) ≤ 200 * D ^ 4 * (1 / t) ^ 3 :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  rw [e1]
  nlinarith [h12, h13]

/-- The right-hand side of `close_factor3` is at most `Cc (1/t)^3` for `t ≥ T`, for a close-growth profile `a`. -/
lemma close_cube3_G (D : ℝ) (a : ℝ → ℝ) (hD : 3 ≤ D) (hG : CloseGrowth a) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t q : ℝ, T ≤ t → 0 < q →
      200 * D ^ 4 / t ^ 6 +
          30 * D / 7 * (200 * D ^ 4 / (4 * t ^ 3) ^ 3) +
          (30 * D / 7) ^ 2 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
            (1 / (Real.exp (-(a t)) / q * q)) ^ 3 *
            (Real.exp (-(3 * (a t + Real.log t))) +
              6 * ((8 * (30 * D / 7)) ^ 3 * Real.exp (-(3 * t))))) ≤
        (200 * D ^ 4 + 30 * D / 7 * (200 * D ^ 4) +
          (30 * D / 7) ^ 2 * (512 * (200 * D ^ 4 + 8 * (30 * D / 7)) *
            (1 + 6 * (8 * (30 * D / 7)) ^ 3))) * (1 / t) ^ 3 := by
  obtain ⟨T₀, hT₀⟩ := hG
  have hD0 : 0 < D := by linarith
  refine ⟨max 1 T₀, le_max_left _ _, ?_⟩
  intro t q hT hq
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) hT
  have htA : T₀ ≤ t := le_trans (le_max_right _ _) hT
  have ht0 : 0 < t := by linarith
  set B : ℝ := 30 * D / 7 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hs0 : 0 ≤ (1 / t) ^ 3 := by positivity
  have hsimp : (1 / (Real.exp (-(a t)) / q * q)) ^ 3 = Real.exp (3 * a t) := by
    rw [div_mul_cancel₀ _ hq.ne', one_div, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul]
    norm_num
  have hexp := JAProductFinal.exp_close_le_G (a t) t ht0 (hT₀ t htA ht1)
  have hprod : Real.exp (3 * a t) * Real.exp (-(3 * t)) ≤ (1 / t) ^ 3 := by
    rw [← Real.exp_add]
    have : 3 * a t + -(3 * t) = 3 * a t - 3 * t := by ring
    rw [this]; exact hexp
  have h3log : Real.exp (3 * Real.log t) = t ^ 3 := by
    have := Real.exp_log (pow_pos ht0 3)
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hthird : Real.exp (3 * a t) * Real.exp (-(3 * (a t + Real.log t))) = (1 / t) ^ 3 := by
    rw [← Real.exp_add]
    have : 3 * a t + -(3 * (a t + Real.log t)) = -(3 * Real.log t) := by ring
    rw [this, Real.exp_neg, h3log, one_div_pow]
    simp
  have hC : 0 ≤ 200 * D ^ 4 + 8 * B := by positivity
  have hB3 : 0 ≤ 6 * (8 * B) ^ 3 := by positivity
  have h3 : B ^ 2 * (512 * (200 * D ^ 4 + 8 * B) * Real.exp (3 * a t) *
        (Real.exp (-(3 * (a t + Real.log t))) + 6 * ((8 * B) ^ 3 * Real.exp (-(3 * t))))) ≤
      B ^ 2 * (512 * (200 * D ^ 4 + 8 * B) * (1 + 6 * (8 * B) ^ 3)) * (1 / t) ^ 3 := by
    have e : B ^ 2 * (512 * (200 * D ^ 4 + 8 * B) * Real.exp (3 * a t) *
        (Real.exp (-(3 * (a t + Real.log t))) + 6 * ((8 * B) ^ 3 * Real.exp (-(3 * t))))) =
        B ^ 2 * (512 * (200 * D ^ 4 + 8 * B)) *
          (Real.exp (3 * a t) * Real.exp (-(3 * (a t + Real.log t))) +
            6 * (8 * B) ^ 3 * (Real.exp (3 * a t) * Real.exp (-(3 * t)))) := by ring
    rw [e]
    have hin : Real.exp (3 * a t) * Real.exp (-(3 * (a t + Real.log t))) +
        6 * (8 * B) ^ 3 * (Real.exp (3 * a t) * Real.exp (-(3 * t))) ≤
        (1 + 6 * (8 * B) ^ 3) * (1 / t) ^ 3 := by
      rw [hthird]
      have := mul_le_mul_of_nonneg_left hprod hB3
      nlinarith
    have := mul_le_mul_of_nonneg_left hin (by positivity : 0 ≤ B ^ 2 * (512 * (200 * D ^ 4 + 8 * B)))
    nlinarith
  have h6 := JAProductFinal.inv_pow6_le t ht1
  have e1 : 200 * D ^ 4 / t ^ 6 = 200 * D ^ 4 * (1 / t ^ 6) := by ring
  have h13 : 200 * D ^ 4 * (1 / t ^ 6) ≤ 200 * D ^ 4 * (1 / t) ^ 3 :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  have h4 : 200 * D ^ 4 / (4 * t ^ 3) ^ 3 ≤ 200 * D ^ 4 * (1 / t) ^ 3 := by
    rw [div_eq_mul_one_div, one_div_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply one_div_le_one_div_of_le (pow_pos ht0 3)
    have h1 : 1 ≤ t ^ 3 := one_le_pow₀ ht1
    nlinarith [pow_pos ht0 3, pow_pos ht0 9, pow_nonneg ht0.le 6]
  have h14 := mul_le_mul_of_nonneg_left h4 hB0
  rw [hsimp, e1]
  nlinarith [h3, h13, h14]

/-! ### The scales are prime squares of the bases `2, 3, 5`: the hypotheses `hgrow`, `hmon` hold -/

section Primes

open JAMerged

/-- Merged growth with period three for a finite strictly increasing selection of prime-square periods. -/
theorem merged_gap_fin3 (b n : ℕ → ℕ) (L : ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : ∀ a c, a < c → c < L → lp (b a) (n a) < lp (b c) (n c)) (i j : ℕ) (hij : i + 3 * j < L) :
    (j : ℝ) * Real.sqrt (lp (b i) (n i)) ≤ lp (b (i + 3 * j)) (n (i + 3 * j)) - lp (b i) (n i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hij' : i + 3 * j < L := by omega
    have ih' := ih hij'
    have hstep : Real.sqrt (lp (b (i + 3 * j)) (n (i + 3 * j))) ≤
        lp (b (i + 3 * j + 3)) (n (i + 3 * j + 3)) - lp (b (i + 3 * j)) (n (i + 3 * j)) :=
      DD3.merged_gap4 (fun k : Fin 4 => b (i + 3 * j + k)) (fun k : Fin 4 => n (i + 3 * j + k))
        (fun k => hb _)
        (fun a a' haa => hmono _ _ (Nat.add_lt_add_left (Fin.lt_def.1 haa) _)
          (by have := a'.isLt; omega))
    have hge : Real.sqrt (lp (b i) (n i)) ≤ Real.sqrt (lp (b (i + 3 * j)) (n (i + 3 * j))) := by
      apply Real.sqrt_le_sqrt
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; simp
      · exact (hmono i (i + 3 * j) (by omega) hij').le
    have e : i + 3 * (j + 1) = i + 3 * j + 3 := by ring
    rw [e]
    push_cast
    nlinarith

/-- The hypothesis `hgrow` of the cluster estimates, for a finite strictly increasing selection of periods
`b_i^(n_i^2)`, `b_i ∈ {2,3,5}`. -/
theorem hgrow3_of_merged (b n : ℕ → ℕ) (L : ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : ∀ a c, a < c → c < L → lp (b a) (n a) < lp (b c) (n c)) :
    ∀ p k, p + k < L →
      (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ) * Real.exp (Real.sqrt (Real.log (((b p) ^ ((n p) ^ 2) : ℕ) : ℝ)) *
        ((k / 3 : ℕ) : ℝ)) ≤ (((b (p + k)) ^ ((n (p + k)) ^ 2) : ℕ) : ℝ) := by
  intro p k hpk
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h | h <;> omega
  have h1 := merged_gap_fin3 b n L hb hmono p (k / 3) (by omega)
  have h2 : lp (b (p + 3 * (k / 3))) (n (p + 3 * (k / 3))) ≤ lp (b (p + k)) (n (p + k)) := by
    rcases Nat.eq_or_lt_of_le (show p + 3 * (k / 3) ≤ p + k by omega) with h | h
    · rw [h]
    · exact (hmono _ _ h hpk).le
  have hexp : Real.exp (lp (b p) (n p)) * Real.exp (Real.sqrt (lp (b p) (n p)) * ((k / 3 : ℕ) : ℝ)) ≤
      Real.exp (lp (b (p + k)) (n (p + k))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [exp_lp _ _ (hb2 p), exp_lp _ _ (hb2 (p + k))] at hexp
  rw [log_scale _ _ (hb2 p)]
  exact hexp

/-- The scales `b_i^(n_i^2)` of a strictly increasing selection are monotone. -/
theorem hmon_of_merged (b n : ℕ → ℕ) (L : ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : ∀ a c, a < c → c < L → lp (b a) (n a) < lp (b c) (n c)) :
    ∀ i j, i ≤ j → j < L → (b i) ^ ((n i) ^ 2) ≤ (b j) ^ ((n j) ^ 2) := by
  intro i j hij hj
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h | h <;> omega
  have hle : lp (b i) (n i) ≤ lp (b j) (n j) := by
    rcases Nat.eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact (hmono _ _ h hj).le
  have := Real.exp_le_exp.mpr hle
  rw [exp_lp _ _ (hb2 i), exp_lp _ _ (hb2 j)] at this
  exact_mod_cast this

end Primes

end DD3Cluster
end LeanCheck
