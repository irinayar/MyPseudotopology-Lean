import LeanCheck.PVGThreeDyadic

/-!
# Bounded dyadic gaps: the Euclidean topology and the zero coefficient group

For strictly increasing dyadic exponents with bounded gaps, this module proves
the remaining conclusions of the bounded-gap proposition:

* `gam_eq_euclid_of_bounded`: the topology `γ_δ` is the Euclidean topology;
* `inA_iff_zero_of_bounded` and `A_eq_singleton_zero_of_bounded`: `A(δ) = {0}`.

The intermediate result `gam_le_euclid_of_bounded_U` applies to any sequence:
a single Euclidean-bounded set `U(ε)`, with `ε > 0`, makes `γ_δ` finer than
the Euclidean topology. Multiplying by a positive integer shrinks its basic
neighbourhoods sufficiently. No Kalton--Roberts hypothesis is used.

Topological order is Mathlib's: a smaller topology is finer.
-/

open Filter Topology Set
open scoped Pointwise

namespace PVG
namespace Three
open Two Q95 Lac

/-- A bounded uniform-character neighbourhood makes `γ_δ` finer than Euclidean.
This direction does not require a bound or a convergence assumption on `δ`. -/
theorem gam_le_euclid_of_bounded_U (δ : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (B : ℝ) (hB : ∀ x : ℝ, (∀ k, dint (δ k * x) ≤ ε) → |x| ≤ B) :
    gamTop δ ≤ (inferInstance : TopologicalSpace ℝ) := by
  have hB0 : 0 ≤ B := by
    simpa using hB 0 (fun _ => by simpa [dint_zero] using hε.le)
  refine le_of_nhds_zero _ _ (gam_group δ) (by infer_instance) fun W hW => ?_
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 hW
  obtain ⟨n, hn⟩ := exists_nat_gt (B / η + 1)
  have hn0 : (0 : ℝ) < n := by
    have : 0 ≤ B / η := div_nonneg hB0 hη.le
    linarith
  have hBn : B < (n : ℝ) * η := by
    apply (div_lt_iff₀ hη).1
    linarith
  refine (mem_nhds_gam δ W).2 ⟨univ, Filter.univ_mem, ε / n, div_pos hε hn0,
    fun x _ hx => hball ?_⟩
  have hnx : |(n : ℝ) * x| ≤ B := hB _ fun k => by
    rw [mul_left_comm]
    calc
      dint ((n : ℝ) * (δ k * x)) ≤ n * dint (δ k * x) := dint_natmul_le n _
      _ ≤ n * (ε / n) := mul_le_mul_of_nonneg_left (hx k) hn0.le
      _ = ε := mul_div_cancel₀ ε hn0.ne'
  rw [abs_mul, abs_of_pos hn0] at hnx
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
  exact lt_of_mul_lt_mul_left (hnx.trans_lt hBn) hn0.le

/-- For a strictly increasing dyadic sequence with bounded gaps, `γ_δ = τ_E`. -/
theorem gam_eq_euclid_of_bounded (L : ℕ → ℕ) (hL : StrictMono L) (G : ℕ)
    (hG : ∀ k, L (k + 1) ≤ L k + G) :
    gamTop (dyseq L) = (inferInstance : TopologicalSpace ℝ) := by
  obtain ⟨ε, hε, B, hB⟩ := (rig_of_bounded L hL G hG).1
  refine le_antisymm (gam_le_euclid_of_bounded_U _ ε hε B hB) ?_
  exact le_of_nhds_zero _ _ (by infer_instance) (gam_group _)
    (gam_coarser_euclid _ 1 (dyseq_le_one L) 0)

/-- A nonzero dilate of the lacunary set is not totally bounded in Euclidean
topology. The formulation uses the project's finite-cover definition `Tb`. -/
lemma eq_zero_of_euclidean_tb_dilate (a : ℝ)
    (htb : Tb (𝓝 (0 : ℝ)) (dil a Sset)) : a = 0 := by
  classical
  by_contra ha
  have ha0 : 0 < |a| := abs_pos.2 ha
  obtain ⟨F, hF⟩ := htb (Ioo (-1 : ℝ) 1) (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨t, ht, hlarge⟩ := Sset_unbounded (((∑ f ∈ F, |f|) + 1) / |a|)
  obtain ⟨f, hf, hnear⟩ := hF (a * t) ⟨t, ht, rfl⟩
  have hfbound : |f| ≤ ∑ g ∈ F, |g| :=
    Finset.single_le_sum (fun _ _ => abs_nonneg _) hf
  have hnear' : |a * t - f| < 1 := abs_lt.2 hnear
  have hupper : |a * t| < (∑ g ∈ F, |g|) + 1 := by
    have htriangle : |a * t| ≤ |a * t - f| + |f| := by
      simpa only [sub_add_cancel] using abs_add_le (a * t - f) f
    linarith
  have hlower : (∑ g ∈ F, |g|) + 1 < |a * t| := by
    rw [abs_mul, mul_comm]
    exact (div_lt_iff₀ ha0).1 hlarge
  exact (not_lt_of_ge hlower.le) hupper

/-- For bounded dyadic gaps, membership of `A(δ)` is equivalent to being zero. -/
theorem inA_iff_zero_of_bounded (L : ℕ → ℕ) (hL : StrictMono L) (G : ℕ)
    (hG : ∀ k, L (k + 1) ≤ L k + G) (a : ℝ) :
    InA (dyseq L) sT a ↔ a = 0 := by
  constructor
  · intro ha
    apply eq_zero_of_euclidean_tb_dilate
    have htb := tb_gam (dyseq L) (dyseq_tendsto L hL) a ha
    rwa [gam_eq_euclid_of_bounded L hL G hG] at htb
  · rintro rfl
    intro ε hε
    exact Filter.Eventually.of_forall fun _ _ => by simpa [dint_zero] using hε.le

/-- The coefficient set of a bounded-gap dyadic sequence is exactly `{0}`. -/
theorem A_eq_singleton_zero_of_bounded (L : ℕ → ℕ) (hL : StrictMono L) (G : ℕ)
    (hG : ∀ k, L (k + 1) ≤ L k + G) :
    {a : ℝ | InA (dyseq L) sT a} = {0} := by
  ext a
  exact inA_iff_zero_of_bounded L hL G hG a

end Three
end PVG
