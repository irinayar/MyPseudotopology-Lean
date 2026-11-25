import LeanCheck.PVGSec8Rest

/-!
# PVG: open sets of the topological modification are unbounded above and below (Lean check)

Scope. Sharper form of part (b) of the proposition on the structure of the topological modification `τ_ξ` of the lacunary PVG:
every nonempty `τ_ξ`-open set has points above every bound and points below every bound. (`tau_unbounded` of `PVGSec8Rest` states
only unboundedness in absolute value.) Consequently no nonempty open set is contained in a ray, and in particular no nonempty
proper interval is open (a proper interval is bounded above or below; that last remark is not formalized).

* `tau_unbounded_side` : the two one-sided statements for a sign `σ = ±1`;
* `tau_unbounded_above`, `tau_unbounded_below`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Set Filter Topology Pointwise

namespace PVG
namespace Lac

open Q95

/-- For `σ = 1` or `σ = -1`: a nonempty open set of the modification has points `u` with `σ u > r`. -/
theorem tau_unbounded_side {U : Set ℝ} (hU : @IsOpen ℝ (modTop lacConv) U) (hne : U.Nonempty) (r σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) : ∃ u ∈ U, r < σ * u := by
  by_contra hno
  push Not at hno
  obtain ⟨x, hx⟩ := hne
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |r| + |x| + 1 := ⟨_, rfl⟩
  have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσx : -|x| ≤ σ * x := by
    rcases hσ with h | h <;> rw [h]
    · linarith [neg_abs_le x]
    · linarith [le_abs_self x]
  obtain ⟨A, hA⟩ : ∃ A : Set ℝ, A = Set.Icc (-M) M := ⟨_, rfl⟩
  have hAI : A ∈ IS := by
    rw [hA]; exact bounded_mem_IS (M := M) (fun a ha => abs_le.2 ha)
  obtain ⟨c, hc, hfin⟩ := exists_dilation hAI
  have hDI := Dset_mem_IS c A
  -- the translated difference set, reflected if `σ = -1`
  obtain ⟨J, hJ⟩ : ∃ J : Set ℝ, J = (fun d : ℝ => x + σ * d) '' Dset c A := ⟨_, rfl⟩
  have hJI : J ∈ IS := by
    have h1 : J = {x} + σ • Dset c A := by
      rw [hJ, Set.singleton_add, ← Set.image_smul, Set.image_image]
      rfl
    rw [h1]
    exact IS_isIdeal.add (IS_isIdeal.single x) (IS_isIdeal.smul σ hDI)
  have hdisj : J \ U = J := by
    ext z
    constructor
    · exact fun h => h.1
    · intro hz
      refine ⟨hz, fun hzU => ?_⟩
      rw [hJ] at hz
      obtain ⟨d, hd, hdz⟩ := hz
      obtain ⟨n, l, hl1, hln, hdx, hdA⟩ := hd
      have hd0 : 0 ≤ d := by
        rw [hdx]
        exact mul_nonneg (le_trans zero_le_one hc.1) (sub_nonneg.2 (sS_mono hln.le))
      have hdM : M < d := by
        by_contra hcon
        push Not at hcon
        apply hdA
        rw [hA]
        exact ⟨by linarith [abs_nonneg r, abs_nonneg x], hcon⟩
      have h1 := hno _ hzU
      rw [← hdz, mul_add, ← mul_assoc, hσσ, one_mul] at h1
      linarith [le_abs_self r]
  have hcl : x ∈ @closure ℝ bohrTop J := by
    letI : TopologicalSpace ℝ := bohrTop
    haveI := bohr_isTopologicalAddGroup
    haveI := bohr_constSMul
    have h0 := zero_mem_closure_D hc.1 hfin
    have hcont : Continuous fun d : ℝ => x + σ * d := by
      have : Continuous fun d : ℝ => σ • d := continuous_const_smul σ
      exact (continuous_const_add x).comp (by simpa [smul_eq_mul] using this)
    have := map_mem_closure (f := fun d : ℝ => x + σ * d) hcont h0 (t := J)
      (fun d hd => by rw [hJ]; exact ⟨d, hd, rfl⟩)
    simpa using this
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_isTopologicalAddGroup
  haveI := bohr_constSMul
  have hmod := (mem_modTop_iff (I := IS) U).1 hU J hJI
  rw [hdisj] at hmod
  have : x ∈ closure J ∩ U := ⟨hcl, hx⟩
  rw [hmod] at this
  exact this

/-- Every nonempty open set of the topological modification is unbounded above. -/
theorem tau_unbounded_above {U : Set ℝ} (hU : @IsOpen ℝ (modTop lacConv) U) (hne : U.Nonempty) (r : ℝ) :
    ∃ u ∈ U, r < u := by
  simpa using tau_unbounded_side hU hne r 1 (Or.inl rfl)

/-- Every nonempty open set of the topological modification is unbounded below. -/
theorem tau_unbounded_below {U : Set ℝ} (hU : @IsOpen ℝ (modTop lacConv) U) (hne : U.Nonempty) (r : ℝ) :
    ∃ u ∈ U, u < r := by
  obtain ⟨u, hu, h⟩ := tau_unbounded_side hU hne (-r) (-1) (Or.inr rfl)
  exact ⟨u, hu, by linarith⟩

end Lac
end PVG
