import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Analytic estimates for the joint-approximation formalization

These are proved analytic components, not a complete JA theorem. In particular this
file does not postulate Matveev's theorem or assume JA as a new axiom.
-/

namespace LeanCheck.MixedPrimeAnalytic

open scoped BigOperators

/-- Absolute summability permits the center-maximum argument for an infinite cosine
series, extending the earlier finite-sum lemma. -/
theorem cosine_series_summable {ι : Type*} (a θ : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (x : ℝ) :
    Summable (fun i => a i * Real.cos (θ i * x)) := by
  apply hs.of_norm_bounded
  intro i
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (ha i), Real.norm_eq_abs]
  exact mul_le_of_le_one_right (ha i) (Real.abs_cos_le_one _)

theorem cosine_series_center_max {ι : Type*} (a θ : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (x : ℝ) :
    (∑' i, a i * Real.cos (θ i * x)) ≤ ∑' i, a i := by
  apply (cosine_series_summable a θ ha hs x).tsum_le_tsum _ hs
  intro i
  exact mul_le_of_le_one_right (ha i) (Real.cos_le_one _)

/-- Uniformly many exceptional factors and a uniformly bounded sum of all other
excesses give a uniform finite-product bound. The later arithmetic argument must
establish these explicit hypotheses for the actual cascade. -/
theorem product_bound_with_exceptions {ι : Type*} [DecidableEq ι]
    (s bad : Finset ι) (hbad : bad ⊆ s) (f a : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (ha : ∀ i, 0 ≤ a i)
    (B C : ℝ) (K : ℕ) (hB : 1 ≤ B)
    (hcard : bad.card ≤ K)
    (hexception : ∀ i ∈ bad, f i ≤ B)
    (hgood : ∀ i ∈ s \ bad, f i ≤ 1 + a i)
    (hsum : ∑ i ∈ s \ bad, a i ≤ C) :
    ∏ i ∈ s, f i ≤ B ^ K * Real.exp C := by
  have hg0 : 0 ≤ ∏ i ∈ s \ bad, f i :=
    Finset.prod_nonneg (fun i hi => hf i (Finset.mem_sdiff.mp hi).1)
  have hb0 : 0 ≤ ∏ i ∈ bad, f i :=
    Finset.prod_nonneg (fun i hi => hf i (hbad hi))
  have hg : ∏ i ∈ s \ bad, f i ≤ Real.exp C := by
    calc
      _ ≤ ∏ i ∈ s \ bad, (1 + a i) :=
        Finset.prod_le_prod₀ (fun i hi => hf i (Finset.mem_sdiff.mp hi).1) hgood
      _ ≤ Real.exp (∑ i ∈ s \ bad, a i) := Real.prod_one_add_le_exp_sum _ ha
      _ ≤ Real.exp C := Real.exp_le_exp.mpr hsum
  have hb : ∏ i ∈ bad, f i ≤ B ^ K := by
    calc
      _ ≤ ∏ i ∈ bad, B := Finset.prod_le_prod₀ (fun i hi => hf i (hbad hi)) hexception
      _ = B ^ bad.card := by simp
      _ ≤ B ^ K := by gcongr
  calc
    ∏ i ∈ s, f i = (∏ i ∈ s \ bad, f i) * (∏ i ∈ bad, f i) :=
      (Finset.prod_sdiff hbad).symm
    _ ≤ Real.exp C * B ^ K := mul_le_mul hg hb hb0 (Real.exp_pos _).le
    _ = B ^ K * Real.exp C := by ring

/-- The elementary lower product estimate used to keep random period masses
away from zero. -/
theorem one_sub_sum_le_product (e : ℕ → ℝ)
    (he : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1) (n : ℕ) :
    1 - ∑ i ∈ Finset.range n, e i ≤ ∏ i ∈ Finset.range n, (1 - e i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hn : 0 ≤ ∑ i ∈ Finset.range n, e i := Finset.sum_nonneg (fun i _ => he i)
    have hmul := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr (he1 n))
    have hcross := mul_nonneg hn (he n)
    nlinarith

theorem product_lower_half (e : ℕ → ℝ)
    (he : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1) (n : ℕ)
    (hsum : ∑ i ∈ Finset.range n, e i ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ ∏ i ∈ Finset.range n, (1 - e i) := by
  have := one_sub_sum_le_product e he he1 n
  linarith

/-- A finite geometric bound with constants uniform in the depth. -/
theorem geometric_sum_le_two (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ 2 := by
  have hsharp : ∀ n : ℕ, (∑ i ∈ Finset.range n, r ^ i) ≤ 2 - 2 * r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hh := mul_nonneg (pow_nonneg hr0 n) (show 0 ≤ 1 - 2 * r by linarith)
      nlinarith
  have hn := hsharp n
  have hp := pow_nonneg hr0 n
  linarith

/-- Group the finite far-field sum in consecutive pairs, without a depth factor.
This is the summation mechanism behind the merged two-prime gap estimate. -/
theorem paired_geometric_sum (f : ℕ → ℝ) (C r : ℝ)
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (heven : ∀ i, f (2 * i) ≤ C * r ^ i)
    (hodd : ∀ i, f (2 * i + 1) ≤ C * r ^ i) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i ≤ 4 * C := by
  have heq : ∀ n : ℕ, (∑ i ∈ Finset.range (2 * n), f i) =
      ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring
  rw [heq]
  calc
    _ ≤ ∑ j ∈ Finset.range n, (2 * C) * r ^ j := by
      apply Finset.sum_le_sum
      intro j _
      linarith [heven j, hodd j]
    _ = (2 * C) * ∑ j ∈ Finset.range n, r ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * C) * 2 := mul_le_mul_of_nonneg_left (geometric_sum_le_two r hr0 hr n) (by positivity)
    _ = 4 * C := by ring

/-- The same paired estimate for an arbitrary finite prefix. -/
theorem paired_geometric_prefix (f : ℕ → ℝ) (C r : ℝ)
    (hf : ∀ i, 0 ≤ f i) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (heven : ∀ i, f (2 * i) ≤ C * r ^ i)
    (hodd : ∀ i, f (2 * i + 1) ≤ C * r ^ i) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i ≤ 4 * C := by
  calc
    _ ≤ ∑ i ∈ Finset.range (2 * n), f i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (by omega)
      · intro i _ _
        exact hf i
    _ ≤ 4 * C := paired_geometric_sum f C r hC hr0 hr heven hodd n

/-- Uniform two-sided mass bounds from a summably small relative-error budget. -/
theorem relative_mass_product_bounds (e u : ℕ → ℝ)
    (he : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i ≤ 1)
    (hlo : ∀ i, 1 - e i ≤ u i) (hhi : ∀ i, u i ≤ 1 + e i)
    (n : ℕ) (hsum : ∑ i ∈ Finset.range n, e i ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ ∏ i ∈ Finset.range n, u i ∧
      (∏ i ∈ Finset.range n, u i) ≤ Real.exp (1 / 2) := by
  constructor
  · exact (product_lower_half e he he1 n hsum).trans
      (Finset.prod_le_prod₀ (fun i _ => sub_nonneg.mpr (he1 i)) (fun i _ => hlo i))
  · calc
      _ ≤ ∏ i ∈ Finset.range n, (1 + e i) :=
        Finset.prod_le_prod₀ (fun i _ => (sub_nonneg.mpr (he1 i)).trans (hlo i))
          (fun i _ => hhi i)
      _ ≤ Real.exp (∑ i ∈ Finset.range n, e i) := Real.prod_one_add_le_exp_sum _ he
      _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hsum

/-- Logarithmic square-level spacing, with the base logarithm supplied as `a`.
The hypothesis `a ≥ 1/4` is weaker than needed for every prime base. -/
theorem square_level_gap (a : ℝ) (ha : 1 / 4 ≤ a) (n : ℕ) :
    (n : ℝ) * Real.sqrt a < (((n : ℝ) + 1) ^ 2 - (n : ℝ) ^ 2) * a := by
  have ha0 : 0 ≤ a := by linarith
  have hs0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsq := Real.sq_sqrt ha0
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt a := by nlinarith
  have htw : Real.sqrt a ≤ 2 * a := by nlinarith
  have hn := mul_le_mul_of_nonneg_left htw (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

/-- Three levels from two colours contain a same-colour pair. Consequently a
spacing bound within each colour bounds the span of every three merged levels. -/
theorem two_colour_three_level_span (c : Fin 3 → Bool) (x : Fin 3 → ℝ) (t : ℝ)
    (h01 : x 0 ≤ x 1) (h12 : x 1 ≤ x 2)
    (hgap : ∀ i j : Fin 3, i < j → c i = c j → t ≤ x j - x i) :
    t ≤ x 2 - x 0 := by
  by_cases h : c 0 = c 1
  · have hg := hgap 0 1 (by decide) h
    linarith
  by_cases h' : c 1 = c 2
  · have hg := hgap 1 2 (by decide) h'
    linarith
  have h02 : c 0 = c 2 := by
    cases h0 : c 0 <;> cases h1 : c 1 <;> cases h2 : c 2 <;> simp_all
  exact hgap 0 2 (by decide) h02

/-- The finite packing-to-cover step used after the weighted-energy estimate.
It is purely combinatorial and does not assume joint approximation. -/
theorem finite_cover_of_bounded_packing {G : Type*} (R : G → G → Prop)
    (hsymm : ∀ a b, R a b → R b a) (hirr : ∀ x, ¬ R x x) (N : ℕ)
    (hbound : ∀ s : Finset G, (s : Set G).Pairwise R → s.card ≤ N) :
    ∃ s : Finset G, ∀ x, ∃ y ∈ s, ¬ R x y := by
  classical
  by_contra h
  push Not at h
  have build : ∀ n : ℕ, ∃ s : Finset G, s.card = n ∧ (s : Set G).Pairwise R := by
    intro n
    induction n with
    | zero => exact ⟨∅, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨s, hcard, hpair⟩ := ih
      obtain ⟨x, hx⟩ := h s
      have hnot : x ∉ s := by
        intro hmem
        exact hirr x (hx x hmem)
      refine ⟨insert x s, by simp [hnot, hcard], ?_⟩
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hax | has
      · subst a
        rcases Finset.mem_insert.mp hb with hbx | hbs
        · exact (hab hbx.symm).elim
        · exact hx b hbs
      · rcases Finset.mem_insert.mp hb with hbx | hbs
        · subst b
          exact hsymm x a (hx a has)
        · exact hpair has hbs hab
  obtain ⟨s, hs, hp⟩ := build (N + 1)
  have := hbound s hp
  omega

end LeanCheck.MixedPrimeAnalytic

#print axioms LeanCheck.MixedPrimeAnalytic.cosine_series_summable
#print axioms LeanCheck.MixedPrimeAnalytic.cosine_series_center_max
#print axioms LeanCheck.MixedPrimeAnalytic.product_bound_with_exceptions
#print axioms LeanCheck.MixedPrimeAnalytic.one_sub_sum_le_product
#print axioms LeanCheck.MixedPrimeAnalytic.product_lower_half
#print axioms LeanCheck.MixedPrimeAnalytic.geometric_sum_le_two
#print axioms LeanCheck.MixedPrimeAnalytic.paired_geometric_sum
#print axioms LeanCheck.MixedPrimeAnalytic.paired_geometric_prefix
#print axioms LeanCheck.MixedPrimeAnalytic.relative_mass_product_bounds
#print axioms LeanCheck.MixedPrimeAnalytic.square_level_gap
#print axioms LeanCheck.MixedPrimeAnalytic.two_colour_three_level_span
#print axioms LeanCheck.MixedPrimeAnalytic.finite_cover_of_bounded_packing
