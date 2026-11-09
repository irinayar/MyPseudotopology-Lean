import LeanCheck.PVGLacMain
import LeanCheck.PVGClusters

/-!
# PVG: the cluster bound (Lean check)

Scope. Theorem `clusterbound` of `PVG_v19`: with `M_i = 2^(4 i²)` and `P_i = {M_i h : 1 ≤ h ≤ i}`, every `J ∈ I_S` satisfies
`#(J ∩ P_i) ≤ q(J)` for all `i`. The proof follows the article, with the representation `σ = ∑ d_n s_n`, `d_n` in the finite set
`Cset l` of `PVGLacCount`:

* `ClHyp`, `exists_ClHyp`: the constants `c₀, c₁, N₀, a, b`;
* `exists_clrep`: for large `i` an element `M_i h = e + σ` of `[-m,m] + Σ` has a representation with top index `T` satisfying
  `4 i² ≤ T² + a` and `T² ≤ 4 i² + b + i` (the index `T` is "admissible");
* `clrep_T_unique`: there is at most one admissible index for large `i`;
* `clrep_inj`: two multiples with the same admissible index and the same top coefficient coincide;
* `cluster_label`: a labelling of the elements of `J ∩ P_i` by the finite set `Cset l`, injective on each `P_i` (`i ≥ i₀`);
* `clusterbound`: the bound.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Finset Set
open scoped Classical

namespace PVG
namespace Lac

/-- `M_i = 2^(4 i²)`. -/
def Mi (i : ℕ) : ℝ := 2 ^ (4 * i ^ 2)

lemma Mi_pos (i : ℕ) : 0 < Mi i := by unfold Mi; positivity

lemma two_pow_le_Mi (i : ℕ) : (2 : ℝ) ^ i ≤ Mi i := by
  unfold Mi; exact pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le i])

/-- The constants of the cluster bound. -/
structure ClHyp (l : List ℝ) (c0 c1 : ℝ) (N0 a b : ℕ) : Prop where
  hc0 : 0 < c0
  hc1 : 1 ≤ c1
  hlow : ∀ c ∈ Cset l, c ≠ 0 → c0 ≤ |c|
  hup : ∀ c ∈ Cset l, |c| ≤ c1
  hN0 : 1 ≤ N0
  hN0big : ∀ T, N0 ≤ T → 4 * c1 ≤ c0 * 2 ^ (2 * T - 1)
  ha : 4 * c1 ≤ 2 ^ a
  hb : 4 / c0 ≤ 2 ^ b

lemma exists_ClHyp (l : List ℝ) : ∃ c0 c1 : ℝ, ∃ N0 a b : ℕ, ClHyp l c0 c1 N0 a b := by
  obtain ⟨c0, c1, hc0, hc1, hlow, hup⟩ := exists_consts (Cset l)
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (4 * c1 / c0) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨a, ha⟩ := pow_unbounded_of_one_lt (4 * c1) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨b, hb⟩ := pow_unbounded_of_one_lt (4 / c0) (by norm_num : (1 : ℝ) < 2)
  refine ⟨c0, c1, n1 + 1, a, b, ⟨hc0, hc1, hlow, hup, by omega, ?_, ha.le, hb.le⟩⟩
  intro T hT
  have h1 : (2 : ℝ) ^ n1 ≤ 2 ^ (2 * T - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [div_lt_iff₀ hc0] at hn1
  nlinarith

/-- A representation of the multiple `M_i h`. -/
def ClRep (l : List ℝ) (m : ℝ) (a b i h : ℕ) : Prop :=
  ∃ (T : ℕ) (d : ℕ → ℝ) (e : ℝ), (∀ n, d n ∈ Cset l) ∧ (∀ n, T < n → d n = 0) ∧ |e| ≤ m ∧
    Mi i * h = e + ∑ n ∈ Finset.range (T + 1), d n * sS n ∧ 4 * i ^ 2 ≤ T ^ 2 + a ∧
    T ^ 2 ≤ 4 * i ^ 2 + b + i

lemma exists_clrep {l : List ℝ} {c0 c1 : ℝ} {N0 a b : ℕ} (D : ClHyp l c0 c1 N0 a b) {m : ℝ} {i : ℕ}
    (hiN : N0 ≤ i) (hia : a ≤ 3 * i ^ 2) (hM : 2 * m ≤ Mi i) (hm : 0 ≤ m) {h : ℕ} (h1 : 1 ≤ h) (hh : h ≤ i)
    {e σ : ℝ} (he : |e| ≤ m) (hσ : σ ∈ sumSet l) (hx : Mi i * h = e + σ) : ClRep l m a b i h := by
  have hi1 : 1 ≤ i := le_trans D.hN0 hiN
  have hMpos := Mi_pos i
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast h1
  have hhiR : (h : ℝ) ≤ i := by exact_mod_cast hh
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have heb := abs_le.1 he
  have hMh1 : Mi i ≤ Mi i * h := by nlinarith
  have hMh2 : Mi i * h ≤ Mi i * i := by nlinarith
  have hMi_i : Mi i ≤ Mi i * i := by nlinarith
  have hσlow : Mi i / 2 ≤ σ := by linarith
  have hσup : σ ≤ 2 * i * Mi i := by nlinarith
  obtain ⟨N, d, hd, hd0, hxd⟩ := rep_of_mem_sumSet l σ hσ
  have hdb : ∀ n, d n = 0 ∨ (c0 ≤ |d n| ∧ |d n| ≤ c1) := fun n => by
    by_cases hz : d n = 0
    · exact Or.inl hz
    · exact Or.inr ⟨D.hlow _ (hd n) hz, D.hup _ (hd n)⟩
  have hex : ∃ n, d n ≠ 0 := by
    by_contra hno
    push Not at hno
    have : σ = 0 := by rw [hxd]; exact Finset.sum_eq_zero (fun n _ => by rw [hno n]; simp)
    linarith
  obtain ⟨n0, hn0⟩ := hex
  have hn0N : n0 < N := by
    by_contra hc; exact hn0 (hd0 n0 (not_lt.1 hc))
  have hTspec : d (Nat.findGreatest (fun n => d n ≠ 0) N) ≠ 0 :=
    Nat.findGreatest_spec (P := fun n => d n ≠ 0) (m := n0) hn0N.le hn0
  set T := Nat.findGreatest (fun n => d n ≠ 0) N with hTdef
  have hTN : T < N := by
    have hle : T ≤ N := Nat.findGreatest_le N
    rcases hle.lt_or_eq with hh' | hh'
    · exact hh'
    · exfalso; apply hTspec; rw [hh']; exact hd0 N le_rfl
  have hupT : ∀ n, T < n → d n = 0 := by
    intro n hn
    by_cases hnN : n ≤ N
    · have := Nat.findGreatest_is_greatest (P := fun n => d n ≠ 0) hn hnN
      simpa using this
    · exact hd0 n (by omega)
  have hσeq : σ = ∑ n ∈ Finset.range (T + 1), d n * sS n := by
    rw [hxd, ← Finset.sum_range_add_sum_Ico _ (show T + 1 ≤ N from hTN)]
    have : ∑ n ∈ Finset.Ico (T + 1) N, d n * sS n = 0 :=
      Finset.sum_eq_zero (fun n hn => by rw [hupT n (Finset.mem_Ico.1 hn).1]; simp)
    rw [this, add_zero]
  -- upper bound `σ ≤ 2 c1 s_T`
  have hσc1 : σ ≤ 2 * c1 * sS T := by
    have h1' : σ ≤ |∑ n ∈ Finset.range (T + 1), d n * sS n| := by rw [← hσeq]; exact le_abs_self _
    refine h1'.trans ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
    have h2' : ∑ n ∈ Finset.range (T + 1), |d n * sS n| ≤ ∑ n ∈ Finset.range (T + 1), c1 * sS n := by
      refine Finset.sum_le_sum (fun n _ => ?_)
      rw [abs_mul, abs_of_pos (sS_pos n)]
      exact mul_le_mul_of_nonneg_right (D.hup _ (hd n)) (sS_pos n).le
    refine h2'.trans ?_
    rw [← Finset.mul_sum]
    have := geom_sS T
    nlinarith [D.hc1]
  have hMa : Mi i ≤ 2 ^ a * sS T := by
    have : Mi i ≤ 4 * c1 * sS T := by linarith
    exact this.trans (mul_le_mul_of_nonneg_right D.ha (sS_pos T).le)
  have hT1 : 4 * i ^ 2 ≤ T ^ 2 + a := by
    have h3 : (2 : ℝ) ^ (4 * i ^ 2) ≤ 2 ^ (a + T ^ 2) := by
      unfold Mi sS at hMa; rw [pow_add]; exact hMa
    have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h3
    omega
  have hiT : i ≤ T := by
    by_contra hc
    push Not at hc
    nlinarith
  have hTN0 : N0 ≤ T := le_trans hiN hiT
  have hlb := lower_bound D.hc0 (by linarith [D.hc1]) N0 D.hN0 D.hN0big d hdb T hTN0 hTspec hupT N hTN
  rw [← hxd, abs_of_nonneg (by linarith)] at hlb
  have hs1 : c0 * sS T ≤ 4 * i * Mi i := by linarith
  have hb4 : 4 ≤ c0 * 2 ^ b := by
    have := D.hb
    rw [div_le_iff₀ D.hc0] at this; linarith
  have hs2 : sS T ≤ 2 ^ b * (i * Mi i) := by
    have h4 : c0 * sS T ≤ c0 * (2 ^ b * (i * Mi i)) := by
      have hip : 0 ≤ (i : ℝ) * Mi i := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hb4 hip]
    exact le_of_mul_le_mul_left h4 D.hc0
  have hiP : (i : ℝ) ≤ 2 ^ i := by exact_mod_cast (Nat.lt_two_pow_self (n := i)).le
  have hs3 : sS T ≤ 2 ^ (b + i + 4 * i ^ 2) := by
    have h5 : sS T ≤ 2 ^ b * (2 ^ i * Mi i) := by
      refine hs2.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right hiP hMpos.le
    refine h5.trans (le_of_eq ?_)
    unfold Mi; rw [pow_add, pow_add]; ring
  have hT2 : T ^ 2 ≤ 4 * i ^ 2 + b + i := by
    have h6 : (2 : ℝ) ^ (T ^ 2) ≤ 2 ^ (b + i + 4 * i ^ 2) := by unfold sS at hs3; exact hs3
    have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h6
    omega
  refine ⟨T, d, e, hd, hupT, he, ?_, hT1, hT2⟩
  rw [hx, ← hσeq]

/-- There is at most one admissible index for large `i`. -/
lemma clrep_T_unique {l : List ℝ} {m : ℝ} {a b i h h' : ℕ} (hia : a ≤ 3 * i ^ 2) (hab : a + b ≤ i)
    (r : ClRep l m a b i h) (r' : ClRep l m a b i h') :
    ∃ T : ℕ, (∃ (d : ℕ → ℝ) (e : ℝ), (∀ n, d n ∈ Cset l) ∧ (∀ n, T < n → d n = 0) ∧ |e| ≤ m ∧
        Mi i * h = e + ∑ n ∈ Finset.range (T + 1), d n * sS n) ∧
      (∃ (d : ℕ → ℝ) (e : ℝ), (∀ n, d n ∈ Cset l) ∧ (∀ n, T < n → d n = 0) ∧ |e| ≤ m ∧
        Mi i * h' = e + ∑ n ∈ Finset.range (T + 1), d n * sS n) ∧ i ≤ T ∧ T ^ 2 ≤ 4 * i ^ 2 + b + i := by
  obtain ⟨T, d, e, hd, hd0, he, hx, ha1, hb1⟩ := r
  obtain ⟨T', d', e', hd', hd0', he', hx', ha1', hb1'⟩ := r'
  have hiT : i ≤ T := by
    by_contra hc; push Not at hc; nlinarith
  have hiT' : i ≤ T' := by
    by_contra hc; push Not at hc; nlinarith
  have hTT : T = T' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (T + 1) ^ 2 ≤ T' ^ 2 := Nat.pow_le_pow_left hlt 2
      nlinarith
    · have : (T' + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hlt 2
      nlinarith
  subst hTT
  exact ⟨T, ⟨d, e, hd, hd0, he, hx⟩, ⟨d', e', hd', hd0', he', hx'⟩, hiT, hb1⟩

/-- Two multiples with the same admissible index and the same top coefficient coincide. -/
lemma clrep_inj {l : List ℝ} {c0 c1 : ℝ} {N0 a b : ℕ} (D : ClHyp l c0 c1 N0 a b) {m : ℝ} (hm : 0 ≤ m) {i T : ℕ}
    (hiT : i ≤ T) (hi1 : 1 ≤ i) (hTb : T ^ 2 ≤ 4 * i ^ 2 + b + i) (hM4 : 4 * m < Mi i)
    (hbig : 16 * c1 * 2 ^ b < 2 ^ i) {h h' : ℕ}
    {d d' : ℕ → ℝ} {e e' : ℝ} (hd : ∀ n, d n ∈ Cset l) (hd' : ∀ n, d' n ∈ Cset l)
    (he : |e| ≤ m) (he' : |e'| ≤ m)
    (hx : Mi i * h = e + ∑ n ∈ Finset.range (T + 1), d n * sS n)
    (hx' : Mi i * h' = e' + ∑ n ∈ Finset.range (T + 1), d' n * sS n) (hdT : d T = d' T) : h = h' := by
  have hMpos := Mi_pos i
  have hT1 : 1 ≤ T := le_trans hi1 hiT
  have hsplit : (Mi i * h - Mi i * h') = (e - e') + ∑ n ∈ Finset.range T, (d n - d' n) * sS n := by
    rw [hx, hx', Finset.sum_range_succ, Finset.sum_range_succ, hdT]
    have : ∑ n ∈ Finset.range T, (d n - d' n) * sS n =
        ∑ n ∈ Finset.range T, d n * sS n - ∑ n ∈ Finset.range T, d' n * sS n := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [this]; ring
  have hsum : |∑ n ∈ Finset.range T, (d n - d' n) * sS n| ≤ 4 * c1 * sS (T - 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h2 : ∑ n ∈ Finset.range T, |(d n - d' n) * sS n| ≤ ∑ n ∈ Finset.range T, 2 * c1 * sS n := by
      refine Finset.sum_le_sum (fun n _ => ?_)
      rw [abs_mul, abs_of_pos (sS_pos n)]
      have h3 : |d n - d' n| ≤ 2 * c1 := by
        have := abs_sub (d n) (d' n)
        have h4 := D.hup _ (hd n)
        have h5 := D.hup _ (hd' n)
        linarith
      exact mul_le_mul_of_nonneg_right h3 (sS_pos n).le
    refine h2.trans ?_
    rw [← Finset.mul_sum]
    have := geom_sS (T - 1)
    rw [Nat.sub_add_cancel hT1] at this
    nlinarith [D.hc1]
  -- the size of `s_{T-1}`
  have hsT : sS T = sS (T - 1) * 2 ^ (2 * T - 1) := by
    have := sS_succ (T - 1)
    rw [Nat.sub_add_cancel hT1] at this
    rw [this]; congr 2; omega
  have hsTb : sS T ≤ 2 ^ b * 2 ^ i * Mi i := by
    have h6 : (2 : ℝ) ^ (T ^ 2) ≤ 2 ^ (b + i + 4 * i ^ 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    unfold sS; unfold Mi
    calc (2 : ℝ) ^ (T ^ 2) ≤ 2 ^ (b + i + 4 * i ^ 2) := h6
      _ = 2 ^ b * 2 ^ i * 2 ^ (4 * i ^ 2) := by rw [pow_add, pow_add]
  have hP : (2 : ℝ) ^ (2 * i - 1) ≤ 2 ^ (2 * T - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hX : (2 : ℝ) ^ (2 * i) = 2 ^ i * 2 ^ i := by rw [← pow_add]; congr 1; omega
  have hX2 : (2 : ℝ) ^ (2 * i) = 2 * 2 ^ (2 * i - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hXpos : (0 : ℝ) < 2 ^ i := by positivity
  have hs1pos := sS_pos (T - 1)
  have hkey : 2 ^ (2 * i - 1) * sS (T - 1) ≤ 2 ^ b * 2 ^ i * Mi i := by
    calc (2 : ℝ) ^ (2 * i - 1) * sS (T - 1) ≤ 2 ^ (2 * T - 1) * sS (T - 1) :=
          mul_le_mul_of_nonneg_right hP hs1pos.le
      _ = sS T := by rw [hsT]; ring
      _ ≤ _ := hsTb
  -- `8 c1 s_{T-1} < M`
  have h8 : 8 * c1 * sS (T - 1) < Mi i := by
    have hA : (2 : ℝ) ^ i * (2 ^ i * sS (T - 1)) ≤ 2 * (2 ^ b * 2 ^ i * Mi i) := by
      have e1 : (2 : ℝ) ^ i * 2 ^ i = 2 * 2 ^ (2 * i - 1) := by rw [← hX, hX2]
      calc (2 : ℝ) ^ i * (2 ^ i * sS (T - 1)) = (2 ^ i * 2 ^ i) * sS (T - 1) := by ring
        _ = 2 * (2 ^ (2 * i - 1) * sS (T - 1)) := by rw [e1]; ring
        _ ≤ 2 * (2 ^ b * 2 ^ i * Mi i) := by linarith [hkey]
    have hB : (2 : ℝ) ^ i * sS (T - 1) ≤ 2 * (2 ^ b * Mi i) := by
      have : (2 : ℝ) ^ i * (2 ^ i * sS (T - 1)) ≤ 2 ^ i * (2 * (2 ^ b * Mi i)) := by nlinarith [hA]
      exact le_of_mul_le_mul_left this hXpos
    have hC : 2 ^ i * (8 * c1 * sS (T - 1)) < 2 ^ i * Mi i := by
      have h16 : 16 * c1 * 2 ^ b * Mi i < 2 ^ i * Mi i := mul_lt_mul_of_pos_right hbig hMpos
      nlinarith [mul_le_mul_of_nonneg_left hB (by linarith [D.hc1] : (0 : ℝ) ≤ 8 * c1)]
    exact lt_of_mul_lt_mul_left hC hXpos.le
  have hdiff : |Mi i * h - Mi i * h'| < Mi i := by
    rw [hsplit]
    have h1 := abs_add_le (e - e') (∑ n ∈ Finset.range T, (d n - d' n) * sS n)
    have h2 := abs_sub e e'
    linarith
  have : |((h : ℝ) - h')| < 1 := by
    have e1 : Mi i * h - Mi i * h' = Mi i * ((h : ℝ) - h') := by ring
    rw [e1, abs_mul, abs_of_pos hMpos] at hdiff
    by_contra hc; push Not at hc
    nlinarith
  have hint : |((h : ℤ) - h')| < 1 := by exact_mod_cast this
  have h7 := abs_lt.1 hint
  omega

lemma T_eq_of_bounds {a b i T T' : ℕ} (hia : a ≤ 3 * i ^ 2) (hab : a + b ≤ i)
    (ha1 : 4 * i ^ 2 ≤ T ^ 2 + a) (hb1 : T ^ 2 ≤ 4 * i ^ 2 + b + i)
    (ha1' : 4 * i ^ 2 ≤ T' ^ 2 + a) (hb1' : T' ^ 2 ≤ 4 * i ^ 2 + b + i) : T = T' := by
  have hiT : i ≤ T := by
    by_contra hc; push Not at hc; nlinarith
  have hiT' : i ≤ T' := by
    by_contra hc; push Not at hc; nlinarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : (T + 1) ^ 2 ≤ T' ^ 2 := Nat.pow_le_pow_left hlt 2
    nlinarith
  · have : (T' + 1) ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hlt 2
    nlinarith

lemma exists_i0 (N0 a b : ℕ) (m c1 : ℝ) : ∃ i0 : ℕ, ∀ i, i0 ≤ i →
    N0 ≤ i ∧ 1 ≤ i ∧ a ≤ 3 * i ^ 2 ∧ a + b ≤ i ∧ 4 * m < Mi i ∧ 16 * c1 * 2 ^ b < 2 ^ i := by
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (4 * m) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨n2, hn2⟩ := pow_unbounded_of_one_lt (16 * c1 * 2 ^ b) (by norm_num : (1 : ℝ) < 2)
  refine ⟨max (max (max N0 1) (a + b)) (max n1 n2), fun i hi => ?_⟩
  have hN : N0 ≤ i := by omega
  have h1 : 1 ≤ i := by omega
  have hab : a + b ≤ i := by omega
  refine ⟨hN, h1, by nlinarith [Nat.zero_le i], hab, ?_, ?_⟩
  · calc 4 * m < 2 ^ n1 := hn1
      _ ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ Mi i := two_pow_le_Mi i
  · calc 16 * c1 * 2 ^ b < 2 ^ n2 := hn2
      _ ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) (by omega)

/-- A labelling of the elements of `J ∩ P_i` by a finite set, injective on each `P_i` for large `i`. -/
theorem cluster_label {J : Set ℝ} (hJ : J ∈ IS) :
    ∃ (i0 : ℕ) (Cf : Finset ℝ) (lab : ℕ → ℕ → ℝ),
      (∀ i, i0 ≤ i → ∀ h : ℕ, 1 ≤ h → h ≤ i → Mi i * h ∈ J → lab i h ∈ Cf) ∧
      (∀ i, i0 ≤ i → ∀ h h' : ℕ, 1 ≤ h → h ≤ i → 1 ≤ h' → h' ≤ i → Mi i * h ∈ J → Mi i * h' ∈ J →
        lab i h = lab i h' → h = h') := by
  rw [mem_IS_iff] at hJ
  obtain ⟨m0, l, hJ'⟩ := hJ
  set m : ℝ := |m0| with hm
  have hm0 : 0 ≤ m := abs_nonneg _
  obtain ⟨c0, c1, N0, a, b, D⟩ := exists_ClHyp l
  obtain ⟨i0, hi0⟩ := exists_i0 N0 a b m c1
  have hrep : ∀ i h : ℕ, i0 ≤ i ∧ 1 ≤ h ∧ h ≤ i ∧ Mi i * h ∈ J →
      ∃ (T : ℕ) (d : ℕ → ℝ) (e : ℝ), (∀ n, d n ∈ Cset l) ∧ (∀ n, T < n → d n = 0) ∧ |e| ≤ m ∧
        Mi i * h = e + ∑ n ∈ Finset.range (T + 1), d n * sS n ∧ 4 * i ^ 2 ≤ T ^ 2 + a ∧
        T ^ 2 ≤ 4 * i ^ 2 + b + i := by
    rintro i h ⟨hi, h1, hh, hmem⟩
    obtain ⟨hN, hi1, hia, hab, hM4, hbig⟩ := hi0 i hi
    obtain ⟨y, σ, hy, hσ, hz⟩ := hJ' _ hmem
    have hM2 : 2 * m ≤ Mi i := by linarith
    exact exists_clrep D hN hia hM2 hm0 h1 hh (hy.trans (le_abs_self m0)) hσ hz
  choose! T d e hT using hrep
  refine ⟨i0, Cset l, fun i h => d i h (T i h), ?_, ?_⟩
  · intro i hi h h1 hh hmem
    exact (hT i h ⟨hi, h1, hh, hmem⟩).1 _
  · intro i hi h h' h1 hh h1' hh' hmem hmem' hlab
    obtain ⟨hN, hi1, hia, hab, hM4, hbig⟩ := hi0 i hi
    obtain ⟨hd, hd0, he, hx, ha1, hb1⟩ := hT i h ⟨hi, h1, hh, hmem⟩
    obtain ⟨hd', hd0', he', hx', ha1', hb1'⟩ := hT i h' ⟨hi, h1', hh', hmem'⟩
    have hTT : T i h = T i h' := T_eq_of_bounds hia hab ha1 hb1 ha1' hb1'
    have hiT : i ≤ T i h := by
      by_contra hc; push Not at hc; nlinarith
    have hlab' : d i h (T i h) = d i h' (T i h) := by
      have : d i h (T i h) = d i h' (T i h') := hlab
      rw [hTT] at this ⊢; exact this
    rw [← hTT] at hx' hb1' ha1'
    exact clrep_inj D hm0 hiT hi1 hb1 hM4 hbig hd hd' he he' hx hx' hlab'

/-- **Theorem `clusterbound`.** `#(J ∩ P_i) ≤ q(J)` for all `i`. -/
theorem clusterbound {J : Set ℝ} (hJ : J ∈ IS) :
    ∃ q : ℕ, ∀ i : ℕ, ((Finset.Icc (1 : ℕ) i).filter (fun h : ℕ => Mi i * (h : ℝ) ∈ J)).card ≤ q := by
  obtain ⟨i0, Cf, lab, hmap, hinj⟩ := cluster_label hJ
  refine ⟨max i0 Cf.card, fun i => ?_⟩
  by_cases hi : i0 ≤ i
  · have : ((Finset.Icc (1 : ℕ) i).filter (fun h : ℕ => Mi i * (h : ℝ) ∈ J)).card ≤ Cf.card := by
      refine Finset.card_le_card_of_injOn (lab i) (fun h hh => ?_) (fun h hh h' hh' hl => ?_)
      · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hh
        exact hmap i hi h hh.1.1 hh.1.2 hh.2
      · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hh hh'
        exact hinj i hi h h' hh.1.1 hh.1.2 hh'.1.1 hh'.1.2 hh.2 hh'.2 hl
    exact this.trans (le_max_right _ _)
  · push Not at hi
    have : ((Finset.Icc (1 : ℕ) i).filter (fun h : ℕ => Mi i * (h : ℝ) ∈ J)).card ≤ i := by
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    exact this.trans (le_trans hi.le (le_max_left _ _))

#print axioms exists_clrep
#print axioms clrep_inj
#print axioms cluster_label
#print axioms clusterbound

end Lac
end PVG
