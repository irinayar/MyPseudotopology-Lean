import Mathlib
import LeanCheck.DD3GenSorted
import LeanCheck.DD3Cluster

/-!
# Three chains with general exponents: the merged growth under the log-gap hypothesis (Lean check)

Scope. Second piece of the Lean version of the modified chains `5^{e_n}` of `TVGplus_v29` (Section 10). In `DD3GenSorted` the chains
with general exponents `E b k` were set up, with the gap hypothesis `GapE b (E b)`: `sqrt(lp_n) < lp_{n+1} - lp_n`,
`lpE E b n = E b n * log b`. Here the analytic facts used by the cluster estimates are proved from it (counterparts of the
lemmas of `JAMerged`, `DD3Reduction` section D and `DD3Cluster` section `Primes`, in which the scales are the squares):

* `OK3 E`: for `b ∈ {2,3,5}` the exponent sequence `E b` is strictly increasing and satisfies `GapE`; `OK3_sq`: the original
  chains `E b k = k²` satisfy it;
* `same_chain_gapE'`: two distinct levels of one chain: the logarithms differ by more than the square root of the smaller;
* `merged_gap4E`, `merged_gap_fin3E`: among four increasing scales of the three chains two have the same base, hence the span is
  at least `sqrt(lp)` of the smallest; the growth with period three;
* `hgrow3_of_mergedE`, `hmon_of_mergedE`: the hypotheses `hgrow` (`Q_{p+k} ≥ Q_p exp(sqrt(log Q_p) ⌊k/3⌋)`) and `hmon` (monotone
  scales) of the generic cluster estimates (`DD3Cluster.far_separated3`, `far_beyond3`, which are stated for an arbitrary scale
  sequence `sc`), for a strictly increasing selection of levels of the three chains;
* `window_card_le_threeE`: at most three levels in a window `[u, v]` with `v - u ≤ sqrt u`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open DD3Sorted

/-- The exponent family of three chains satisfies the log-gap hypothesis. -/
def OK3 (E : ℕ → ℕ → ℕ) : Prop :=
  ∀ b, (b = 2 ∨ b = 3 ∨ b = 5) → StrictMono (E b) ∧ GapE b (E b)

lemma log_nonneg_of_two {b : ℕ} (hb : 2 ≤ b) : 0 ≤ Real.log b :=
  Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b))

lemma lpE_mono_le {E : ℕ → ℕ → ℕ} {b : ℕ} (hb : 2 ≤ b) (he : StrictMono (E b)) {n m : ℕ} (h : n ≤ m) :
    lpE E b n ≤ lpE E b m := by
  unfold lpE
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast he.monotone h) (log_nonneg_of_two hb)

lemma lpE_strict {E : ℕ → ℕ → ℕ} {b : ℕ} (hb : 2 ≤ b) (he : StrictMono (E b)) {n m : ℕ}
    (h : lpE E b n < lpE E b m) : n < m := by
  by_contra hnm
  push Not at hnm
  exact absurd (lpE_mono_le hb he hnm) (not_le.mpr h)

lemma same_chain_gapE' {E : ℕ → ℕ → ℕ} {b : ℕ} (hb : 2 ≤ b) (he : StrictMono (E b)) (hg : GapE b (E b)) {n m : ℕ}
    (hnm : n < m) : Real.sqrt (lpE E b n) < lpE E b m - lpE E b n := by
  have h1 := hg n
  have h2 : lpE E b (n + 1) ≤ lpE E b m := lpE_mono_le hb he (by omega)
  unfold lpE at h1 h2 ⊢
  linarith

lemma OK3_sq : OK3 (fun _ k => k ^ 2) := by
  intro b hb
  have hb2 : 2 ≤ b := by rcases hb with rfl | rfl | rfl <;> norm_num
  refine ⟨fun a c h => Nat.pow_lt_pow_left h (by norm_num), GapE_sq hb2⟩

lemma exp_lpE (E : ℕ → ℕ → ℕ) (b n : ℕ) (hb : 2 ≤ b) : Real.exp (lpE E b n) = ((b ^ (E b n) : ℕ) : ℝ) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  unfold lpE
  rw [← Real.log_pow, Real.exp_log (by positivity)]
  push_cast; ring

/-- **Among four increasing scales of the three chains two share a base.** -/
theorem merged_gap4E {E : ℕ → ℕ → ℕ} (hE : OK3 E) (b n : Fin 4 → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : StrictMono (fun i => lpE E (b i) (n i))) :
    Real.sqrt (lpE E (b 0) (n 0)) ≤ lpE E (b 3) (n 3) - lpE E (b 0) (n 0) := by
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h | h <;> omega
  have hcard : ({2, 3, 5} : Finset ℕ).card < (Finset.univ : Finset (Fin 4)).card := by decide
  obtain ⟨x, -, y, -, hxy, hbxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset (Fin 4))) (t := ({2, 3, 5} : Finset ℕ)) hcard (f := b)
    (fun i _ => by rcases hb i with h | h | h <;> simp [h])
  have key : ∀ i j : Fin 4, i < j → b i = b j →
      Real.sqrt (lpE E (b 0) (n 0)) ≤ lpE E (b 3) (n 3) - lpE E (b 0) (n 0) := by
    intro i j hij hbij
    have hlt : lpE E (b i) (n i) < lpE E (b j) (n j) := hmono hij
    rw [← hbij] at hlt
    have hnm : n i < n j := lpE_strict (hb2 i) (hE (b i) (hb i)).1 hlt
    have hgap := same_chain_gapE' (E := E) (hb2 i) (hE (b i) (hb i)).1 (hE (b i) (hb i)).2 hnm
    have hle0 : lpE E (b 0) (n 0) ≤ lpE E (b i) (n i) := hmono.monotone (Fin.zero_le i)
    have hle3 : lpE E (b j) (n j) ≤ lpE E (b 3) (n 3) := hmono.monotone (Fin.le_last j)
    have hs : Real.sqrt (lpE E (b 0) (n 0)) ≤ Real.sqrt (lpE E (b i) (n i)) := Real.sqrt_le_sqrt hle0
    have hbj : lpE E (b i) (n j) = lpE E (b j) (n j) := by rw [hbij]
    rw [hbj] at hgap
    linarith
  rcases lt_or_gt_of_ne hxy with h | h
  · exact key x y h hbxy
  · exact key y x h hbxy.symm

/-- Merged growth with period three. -/
theorem merged_gap_fin3E {E : ℕ → ℕ → ℕ} (hE : OK3 E) (b n : ℕ → ℕ) (L : ℕ)
    (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : ∀ a c, a < c → c < L → lpE E (b a) (n a) < lpE E (b c) (n c)) (i j : ℕ) (hij : i + 3 * j < L) :
    (j : ℝ) * Real.sqrt (lpE E (b i) (n i)) ≤ lpE E (b (i + 3 * j)) (n (i + 3 * j)) - lpE E (b i) (n i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hij' : i + 3 * j < L := by omega
    have ih' := ih hij'
    have hstep : Real.sqrt (lpE E (b (i + 3 * j)) (n (i + 3 * j))) ≤
        lpE E (b (i + 3 * j + 3)) (n (i + 3 * j + 3)) - lpE E (b (i + 3 * j)) (n (i + 3 * j)) :=
      merged_gap4E hE (fun k : Fin 4 => b (i + 3 * j + k)) (fun k : Fin 4 => n (i + 3 * j + k))
        (fun k => hb _)
        (fun a a' haa => hmono _ _ (Nat.add_lt_add_left (Fin.lt_def.1 haa) _)
          (by have := a'.isLt; omega))
    have hge : Real.sqrt (lpE E (b i) (n i)) ≤ Real.sqrt (lpE E (b (i + 3 * j)) (n (i + 3 * j))) := by
      apply Real.sqrt_le_sqrt
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; simp
      · exact (hmono i (i + 3 * j) (by omega) hij').le
    have e : i + 3 * (j + 1) = i + 3 * j + 3 := by ring
    rw [e]
    push_cast
    nlinarith

/-- **The hypothesis `hgrow` of the cluster estimates** for a finite strictly increasing selection of levels of the three chains. -/
theorem hgrow3_of_mergedE {E : ℕ → ℕ → ℕ} (hE : OK3 E) (b n : ℕ → ℕ) (L : ℕ)
    (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : ∀ a c, a < c → c < L → lpE E (b a) (n a) < lpE E (b c) (n c)) :
    ∀ p k, p + k < L →
      (((b p) ^ (E (b p) (n p)) : ℕ) : ℝ) * Real.exp (Real.sqrt (Real.log (((b p) ^ (E (b p) (n p)) : ℕ) : ℝ)) *
        ((k / 3 : ℕ) : ℝ)) ≤ (((b (p + k)) ^ (E (b (p + k)) (n (p + k))) : ℕ) : ℝ) := by
  intro p k hpk
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h | h <;> omega
  have h1 := merged_gap_fin3E hE b n L hb hmono p (k / 3) (by omega)
  have h2 : lpE E (b (p + 3 * (k / 3))) (n (p + 3 * (k / 3))) ≤ lpE E (b (p + k)) (n (p + k)) := by
    rcases Nat.eq_or_lt_of_le (show p + 3 * (k / 3) ≤ p + k by omega) with h | h
    · rw [h]
    · exact (hmono _ _ h hpk).le
  have hexp : Real.exp (lpE E (b p) (n p)) * Real.exp (Real.sqrt (lpE E (b p) (n p)) * ((k / 3 : ℕ) : ℝ)) ≤
      Real.exp (lpE E (b (p + k)) (n (p + k))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [exp_lpE E _ _ (hb2 p), exp_lpE E _ _ (hb2 (p + k))] at hexp
  rw [log_scaleE E (b p) (n p)]
  exact hexp

/-- The scales of a strictly increasing selection are monotone. -/
theorem hmon_of_mergedE {E : ℕ → ℕ → ℕ} (b n : ℕ → ℕ) (L : ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hmono : ∀ a c, a < c → c < L → lpE E (b a) (n a) < lpE E (b c) (n c)) :
    ∀ i j, i ≤ j → j < L → (b i) ^ (E (b i) (n i)) ≤ (b j) ^ (E (b j) (n j)) := by
  intro i j hij hj
  have hb2 : ∀ i, 2 ≤ b i := fun i => by rcases hb i with h | h | h <;> omega
  have hle : lpE E (b i) (n i) ≤ lpE E (b j) (n j) := by
    rcases Nat.eq_or_lt_of_le hij with h | h
    · rw [h]
    · exact (hmono _ _ h hj).le
  have := Real.exp_le_exp.mpr hle
  rw [exp_lpE E _ _ (hb2 i), exp_lpE E _ _ (hb2 j)] at this
  exact_mod_cast this

/-- Two distinct levels of one chain in a window `[u, v]`: `v - u > sqrt u`. -/
lemma chain_window_oneE {E : ℕ → ℕ → ℕ} {b n m : ℕ} (hb : 2 ≤ b) (he : StrictMono (E b)) (hg : GapE b (E b))
    (u v : ℝ) (hu : u ≤ lpE E b n) (hm : lpE E b m ≤ v) (hnm : n < m) : Real.sqrt u < v - u := by
  have h1 := same_chain_gapE' (E := E) hb he hg hnm
  have h2 : Real.sqrt u ≤ Real.sqrt (lpE E b n) := Real.sqrt_le_sqrt hu
  linarith

/-- **At most three levels in a window** `[u, v]` with `v - u ≤ sqrt u`. -/
theorem window_card_le_threeE {E : ℕ → ℕ → ℕ} (hE : OK3 E) (s : Finset (ℕ × ℕ)) (u v : ℝ)
    (hw : v - u ≤ Real.sqrt u)
    (hs : ∀ p ∈ s, (p.1 = 2 ∨ p.1 = 3 ∨ p.1 = 5) ∧ u ≤ lpE E p.1 p.2 ∧ lpE E p.1 p.2 ≤ v) :
    s.card ≤ 3 := by
  have hcard : s.card ≤ ({2, 3, 5} : Finset ℕ).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      have := (hs p hp).1
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact this
    · intro p hp q hq hpq
      have hp' := hs p hp
      have hq' := hs q hq
      have hb2 : 2 ≤ p.1 := by rcases hp'.1 with h | h | h <;> omega
      by_contra hne
      have hn : p.2 ≠ q.2 := fun h => hne (Prod.ext hpq h)
      rcases lt_or_gt_of_ne hn with h | h
      · have := chain_window_oneE (E := E) (b := p.1) (n := p.2) (m := q.2) hb2 (hE p.1 hp'.1).1 (hE p.1 hp'.1).2
          u v hp'.2.1 (by rw [hpq]; exact hq'.2.2) h
        linarith
      · have := chain_window_oneE (E := E) (b := q.1) (n := q.2) (m := p.2) (by rw [← hpq]; exact hb2)
          (hE q.1 hq'.1).1 (hE q.1 hq'.1).2 u v hq'.2.1 (by rw [← hpq]; exact hp'.2.2) h
        linarith
  have h3 : ({2, 3, 5} : Finset ℕ).card = 3 := by decide
  omega

end DD3Gen
end LeanCheck
