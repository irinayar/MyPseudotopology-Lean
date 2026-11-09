import Mathlib

/-!
# PVG: no unbounded sequence is null for a Hausdorff group topology inside the Euclidean one with continuous dilations (Lean check)

Scope. A generalization of the statement that Bohr-convergent sequences of reals are Euclidean convergent
(`PVGSeqFU.bohrseq`) to every Hausdorff group topology `β ⊆ τ_E` on `ℝ` with continuous dilations. In the abstract form below `X` is a
real vector space with a Hausdorff group topology in which every fixed dilation is continuous, and `ι : ℝ → X` is an `ℝ`-linear
continuous injection (for `X = (ℝ, β)` and `ι = id` the hypotheses say `β ⊆ τ_E`):

* `no_unbounded_null_seq`: if `|x_k| → ∞` then `ι(x_k)` does not tend to `0`.

Proof (Baire category): for a closed neighbourhood `V` of `0`, the sets `A_N = {a : ι(a x_k) ∈ V for all k ≥ N}` are closed, and
cover `ℝ` because `a • ι(x_k) → 0`; one of them contains an interval of length `η`, so `ι(s x_k) ∈ V − V` for `|s| < η` and `k ≥ N`;
since `|x_k| → ∞`, `ι(ℝ) ⊆ V − V ⊆ W` for every neighbourhood `W` of `0`, so `ι = 0` by the Hausdorff property.

Consequence (see the research note): for such `β`, the `β`-convergent sequences are the Euclidean convergent ones, and a monothetic
such `β` cannot be first countable.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires mathematical
review.
-/

open Filter Topology

namespace PVG
namespace Gen

theorem exists_closed_nhds_sub {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    {W : Set X} (hW : W ∈ 𝓝 (0 : X)) :
    ∃ V ∈ 𝓝 (0 : X), IsClosed V ∧ ∀ v ∈ V, ∀ w ∈ V, v - w ∈ W := by
  have h1 : Tendsto (fun p : X × X => p.1 - p.2) (𝓝 ((0 : X), (0 : X))) (𝓝 ((0 : X) - 0)) :=
    (continuous_sub.tendsto ((0 : X), (0 : X)))
  rw [sub_zero] at h1
  have h2 := h1 hW
  rw [nhds_prod_eq, Filter.mem_map, mem_prod_self_iff] at h2
  obtain ⟨V1, hV1, hV1s⟩ := h2
  obtain ⟨V, hV, hVc, hVV1⟩ := exists_mem_nhds_isClosed_subset hV1
  exact ⟨V, hV, hVc, fun v hv w hw => hV1s (Set.mk_mem_prod (hVV1 hv) (hVV1 hw))⟩

/-- **No unbounded null sequence.** -/
theorem no_unbounded_null_seq
    {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [ContinuousConstSMul ℝ X]
    (ι : ℝ →ₗ[ℝ] X) (hι : Continuous ι) (hinj : Function.Injective ι)
    (x : ℕ → ℝ) (hx : Tendsto (fun k => |x k|) atTop atTop)
    (h0 : Tendsto (fun k => ι (x k)) atTop (𝓝 0)) : False := by
  -- every real number is mapped into every neighbourhood of `0`
  have key : ∀ W ∈ 𝓝 (0 : X), ∀ y : ℝ, ι y ∈ W := by
    intro W hW y
    obtain ⟨V, hV, hVc, hVW⟩ := exists_closed_nhds_sub hW
    set A : ℕ → Set ℝ := fun N => {a : ℝ | ∀ k, N ≤ k → ι (a * x k) ∈ V} with hA
    have hAc : ∀ N, IsClosed (A N) := by
      intro N
      have : A N = ⋂ k ∈ {k : ℕ | N ≤ k}, (fun a : ℝ => ι (a * x k)) ⁻¹' V := by
        ext a; simp [hA]
      rw [this]
      refine isClosed_biInter (fun k _ => hVc.preimage ?_)
      exact hι.comp (continuous_id.mul continuous_const)
    have hAu : (⋃ N, A N) = Set.univ := by
      refine Set.eq_univ_of_forall (fun a => ?_)
      have h1 : Tendsto (fun k => a • ι (x k)) atTop (𝓝 (a • (0 : X))) :=
        ((continuous_const_smul a).tendsto 0).comp h0
      rw [smul_zero] at h1
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h1.eventually hV)
      refine Set.mem_iUnion.2 ⟨N, fun k hk => ?_⟩
      have h5 : a • ι (x k) ∈ V := hN k hk
      have e : ι (a * x k) = a • ι (x k) := by rw [← smul_eq_mul, map_smul]
      show ι (a * x k) ∈ V
      rw [e]; exact h5
    obtain ⟨N, a0, ha0⟩ := nonempty_interior_of_iUnion_of_closed hAc hAu
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 isOpen_interior a0 ha0
    -- choose `k ≥ N` with `|y| < η |x_k|`
    obtain ⟨k, hk1, hk2⟩ :=
      ((hx.eventually_gt_atTop (|y| / η)).and (Filter.eventually_ge_atTop N)).exists
    have hxk : 0 < |x k| := lt_of_le_of_lt (by positivity) hk1
    have hxk0 : x k ≠ 0 := abs_pos.1 hxk
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = y / x k := ⟨_, rfl⟩
    have hh : |y| < |x k| * η := (div_lt_iff₀ hη).1 hk1
    have hsη : |s| < η := by
      rw [hs, abs_div, div_lt_iff₀ hxk]
      linarith [mul_comm η |x k|]
    have hmem1 : a0 + s ∈ interior (A N) := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      simpa using hsη
    have h1 : a0 + s ∈ A N := interior_subset hmem1
    have h2 : a0 ∈ A N := interior_subset ha0
    simp only [hA, Set.mem_ofPred_eq] at h1 h2
    have h3 := hVW _ (h1 k hk2) _ (h2 k hk2)
    have e0 : (a0 + s) * x k - a0 * x k = y := by
      have : (a0 + s) * x k - a0 * x k = s * x k := by ring
      rw [this, hs, div_mul_cancel₀ _ hxk0]
    rw [← map_sub, e0] at h3
    exact h3
  have h1 : ι 1 = 0 := by
    by_contra hne
    have hW : ({ι 1}ᶜ : Set X) ∈ 𝓝 (0 : X) := isOpen_compl_singleton.mem_nhds (Ne.symm hne)
    exact key _ hW 1 rfl
  have h2 : ι 1 = ι 0 := by rw [h1, map_zero]
  exact one_ne_zero (hinj h2)

end Gen
end PVG
