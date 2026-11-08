import Mathlib
import LeanCheck.DD3GenSorted
import LeanCheck.DD3GenDense

/-!
# Three chains with general exponents: the scale sets and the tail argument (Lean check)

Scope. Third piece of the Lean version of the modified chains `5^{e_n}` of `TVGplus_v29` (Section 10). The endgame module
`DD3GenDense` is stated for an arbitrary family of scale sets `S p`; here the family of the chains with general exponents
`E p k` is defined and the tail argument is proved for it (counterparts of `JAFinal.Pn_of_levels` and
`JAFinal2.Pn_of_chainP`, in which the scales are `p^(k²)`):

* `scalesE E p = {p^(E p n) : n ≥ 1}`; `scalesE_sq`: for `E p k = k²` it is `sqScales p`;
* `Pn_of_levelsE`: if the levels `1, …, L` have small differences (`nrm (d / p^(E p i)) < 2/D`) and the next scale exceeds `D X`
  (`D X < p^(E p (L+1))`) for two integers `a, a' ∈ [0,X]`, then `Pn (scalesE E p) (a - a') < 2/D` (monotone exponents);
* `Pn_of_chainE`: the same from the levels `s + j`, `1 ≤ j ≤ n`, of the chain `chainE p (E p) s D`, with the coarse levels
  `i ≤ s` handled by divisibility by `p^(E p s)`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open Finset MixedPrime JAFinal JASupport

/-- The scale sets of the chains with exponents `E p k`. -/
def scalesE (E : ℕ → ℕ → ℕ) (p : ℕ) : Set ℕ := {q | ∃ n : ℕ, 1 ≤ n ∧ q = p ^ E p n}

/-- The original scale sets are the case `E p k = k²`. -/
lemma scalesE_sq : scalesE (fun _ k => k ^ 2) = sqScales := rfl

lemma mem_scalesE {E : ℕ → ℕ → ℕ} {p n : ℕ} (hn : 1 ≤ n) : p ^ E p n ∈ scalesE E p := ⟨n, hn, rfl⟩

/-- **The tail argument** (counterpart of `JAFinal.Pn_of_levels`). -/
lemma Pn_of_levelsE {E : ℕ → ℕ → ℕ} {p : ℕ} [NeZero p] (hp : 2 ≤ p) (he : Monotone (E p)) (D : ℝ) (hD : 0 < D)
    (X L : ℕ) (hL : D * X < (p : ℝ) ^ (E p (L + 1))) (a a' : ℤ) (haX : 0 ≤ a ∧ a ≤ X) (ha'X : 0 ≤ a' ∧ a' ≤ X)
    (hlev : ∀ i : ℕ, 1 ≤ i → i ≤ L → nrm (((a - a' : ℤ) : ℝ) / ((p ^ (E p i) : ℕ) : ℝ)) < 2 / D) :
    Pn (scalesE E p) (a - a') < 2 / D := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  obtain ⟨c₁, hc₁, hc₁'⟩ := exists_lt_bound (Finset.Icc 1 L)
    (fun i => nrm (((a - a' : ℤ) : ℝ) / ((p ^ (E p i) : ℕ) : ℝ))) (2 / D)
    (fun i hi => hlev i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2)
  have hXD : (X : ℝ) / (p : ℝ) ^ (E p (L + 1)) < 1 / D := by
    rw [div_lt_div_iff₀ (by positivity) hD]
    linarith
  have hc₂ : (X : ℝ) / (p : ℝ) ^ (E p (L + 1)) < 2 / D := by
    have : 1 / D < 2 / D := div_lt_div_of_pos_right (by norm_num) hD
    linarith
  have hS : (scalesE E p).Nonempty := ⟨p ^ E p 1, mem_scalesE (le_refl 1)⟩
  have hle : Pn (scalesE E p) (a - a') ≤ max c₁ ((X : ℝ) / (p : ℝ) ^ (E p (L + 1))) := by
    apply Pn_le hS
    rintro s ⟨n, hn, rfl⟩
    by_cases hnL : n ≤ L
    · exact (hc₁' n (Finset.mem_Icc.mpr ⟨hn, hnL⟩)).trans (le_max_left _ _)
    · push Not at hnL
      refine le_trans ?_ (le_max_right _ _)
      refine (nrm_le_abs _).trans ?_
      have hpn : (0 : ℝ) < ((p ^ (E p n) : ℕ) : ℝ) := by positivity
      rw [abs_div, abs_of_pos hpn]
      have habs : |((a - a' : ℤ) : ℝ)| ≤ X := by
        have h1 : ((a - a' : ℤ) : ℝ) ≤ X := by
          have : a - a' ≤ (X : ℤ) := by omega
          exact_mod_cast this
        have h2 : -(X : ℝ) ≤ ((a - a' : ℤ) : ℝ) := by
          have : -(X : ℤ) ≤ a - a' := by omega
          exact_mod_cast this
        exact abs_le.mpr ⟨h2, h1⟩
      have hmono : (p : ℝ) ^ (E p (L + 1)) ≤ ((p ^ (E p n) : ℕ) : ℝ) := by
        push_cast
        exact pow_le_pow_right₀ hp1 (he (by omega))
      calc |((a - a' : ℤ) : ℝ)| / ((p ^ (E p n) : ℕ) : ℝ) ≤ (X : ℝ) / ((p ^ (E p n) : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right habs hpn.le
        _ ≤ (X : ℝ) / (p : ℝ) ^ (E p (L + 1)) :=
            div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hmono
  exact lt_of_le_of_lt hle (max_lt hc₁ hc₂)

/-- **`P_p(a - a') < 2/D` from the levels of a `chainE` cascade** (counterpart of `JAFinal2.Pn_of_chainP`). -/
lemma Pn_of_chainE {E : ℕ → ℕ → ℕ} {p : ℕ} [NeZero p] (hp : 2 ≤ p) (he : Monotone (E p)) (s n X : ℕ) (D : ℝ)
    (hD : 0 < D) (hL : D * X < (p : ℝ) ^ (E p (s + n + 1))) (a a' : ℤ) (haX : 0 ≤ a ∧ a ≤ X)
    (ha'X : 0 ≤ a' ∧ a' ≤ X) (hdv : ((p ^ (E p s) : ℕ) : ℤ) ∣ a - a')
    (hlev : ∀ j : ℕ, 1 ≤ j → j ≤ n → nrm (((a - a' : ℤ) : ℝ) / ((p ^ (E p (s + j)) : ℕ) : ℝ)) < 2 / D) :
    Pn (scalesE E p) (a - a') < 2 / D := by
  refine Pn_of_levelsE hp he D hD X (s + n) hL a a' haX ha'X ?_
  intro i hi1 hi2
  by_cases his : i ≤ s
  · have hd1 : ((p ^ (E p i) : ℕ) : ℤ) ∣ a - a' :=
      (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (he his))).trans hdv
    obtain ⟨c, hc⟩ := hd1
    have hpos : (0 : ℝ) < ((p ^ (E p i) : ℕ) : ℝ) := by
      have : 0 < p := by omega
      positivity
    have e : ((a - a' : ℤ) : ℝ) / ((p ^ (E p i) : ℕ) : ℝ) = (c : ℝ) := by
      rw [hc]
      push_cast
      field_simp
    rw [e, nrm_int]
    positivity
  · have hj : i = s + (i - s) := by omega
    have := hlev (i - s) (by omega) (by omega)
    rwa [← hj] at this

end DD3Gen
end LeanCheck
