import Mathlib
import LeanCheck.PVGSeqGen

/-!
# PVG: half-integers in every neighbourhood make `ℤ` dense (Lean check)

Scope. The last step of the proof of Theorem `thm:betaexists` (PVG_v22), in the abstract form of `PVGSeqGen`: `X` is a real vector space
with a group topology in which every fixed dilation is continuous and `ι : ℝ →ₗ[ℝ] X` is a Euclidean-continuous linear map (for
`X = (ℝ, β)` and `ι = id` the hypotheses say that `β` is a group topology inside the Euclidean topology with continuous dilations).
Write `R = {ι(k) : k ∈ ℤ}`.

* `half_mem_closure`: if every neighbourhood of `0` in `X` contains `ι(k + 1/2)` for some integer `k`, then `ι(1/2) ∈ closure R`.
* `dyadic_mem_closure`: then `ι(j / 2^n) ∈ closure R` for all integers `j` and natural numbers `n`.
* `range_subset_closure`: then `ι(x) ∈ closure R` for every real `x`, that is, `ι(ℤ)` is dense in `ι(ℝ)`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Gen

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousConstSMul ℝ X]

/-- If every neighbourhood of `0` contains `ι(k + 1/2)` for some integer `k`, then `ι(1/2)` is in the closure of `ι(ℤ)`. -/
theorem half_mem_closure (ι : ℝ →ₗ[ℝ] X)
    (h : ∀ V ∈ 𝓝 (0 : X), ∃ k : ℤ, ι ((k : ℝ) + 1 / 2) ∈ V) :
    ι (1 / 2) ∈ closure (Set.range (fun k : ℤ => ι (k : ℝ))) := by
  rw [mem_closure_iff_nhds]
  intro N hN
  have hN0 : (fun z => ι (1 / 2) - z) ⁻¹' N ∈ 𝓝 (0 : X) := by
    have hc : Continuous (fun z : X => ι (1 / 2) - z) := continuous_const.sub continuous_id
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hN)
  obtain ⟨k, hk⟩ := h _ hN0
  refine ⟨ι ((-k : ℤ) : ℝ), ?_, ⟨-k, rfl⟩⟩
  have e : ι (1 / 2) - ι ((k : ℝ) + 1 / 2) = ι ((-k : ℤ) : ℝ) := by
    rw [← map_sub]; congr 1; push_cast; ring
  simpa [e] using hk

/-- The closure of `ι(ℤ)` as an additive subgroup. -/
noncomputable def clZ (ι : ℝ →ₗ[ℝ] X) : AddSubgroup X :=
  (AddMonoidHom.range ((ι.toAddMonoidHom).comp (Int.castAddHom ℝ))).topologicalClosure

theorem coe_clZ (ι : ℝ →ₗ[ℝ] X) :
    (clZ ι : Set X) = closure (Set.range (fun k : ℤ => ι (k : ℝ))) := by
  unfold clZ
  rw [AddSubgroup.topologicalClosure_coe]
  congr 1

theorem dyadic_mem_closure (ι : ℝ →ₗ[ℝ] X)
    (h : ∀ V ∈ 𝓝 (0 : X), ∃ k : ℤ, ι ((k : ℝ) + 1 / 2) ∈ V) (n : ℕ) :
    ∀ j : ℤ, ι ((j : ℝ) / 2 ^ n) ∈ closure (Set.range (fun k : ℤ => ι (k : ℝ))) := by
  have hhalf : ι (1 / 2) ∈ clZ ι := by rw [← SetLike.mem_coe, coe_clZ]; exact half_mem_closure ι h
  have hZ : ∀ i : ℤ, ι (i : ℝ) ∈ clZ ι := fun i => by
    rw [← SetLike.mem_coe, coe_clZ]; exact subset_closure ⟨i, rfl⟩
  -- `ι(k/2) ∈ clZ`
  have hk2 : ∀ k : ℤ, ι ((k : ℝ) / 2) ∈ clZ ι := by
    intro k
    obtain ⟨i, hi | hi⟩ := Int.even_or_odd' k
    · have : (k : ℝ) / 2 = i := by rw [hi]; push_cast; ring
      rw [this]; exact hZ i
    · have : (k : ℝ) / 2 = (i : ℝ) + 1 / 2 := by rw [hi]; push_cast; ring
      rw [this, map_add]; exact add_mem (hZ i) hhalf
  have hclosed : IsClosed (clZ ι : Set X) := AddSubgroup.isClosed_topologicalClosure _
  have hD : Continuous (fun z : X => (1 / 2 : ℝ) • z) := continuous_const_smul _
  -- dilation by `1/2` maps `clZ` into `clZ`
  have hmap : ∀ z ∈ clZ ι, (1 / 2 : ℝ) • z ∈ clZ ι := by
    intro z hz
    rw [← SetLike.mem_coe, coe_clZ] at hz
    have h1 : (fun z : X => (1 / 2 : ℝ) • z) '' closure (Set.range (fun k : ℤ => ι (k : ℝ))) ⊆
        closure ((fun z : X => (1 / 2 : ℝ) • z) '' Set.range (fun k : ℤ => ι (k : ℝ))) :=
      image_closure_subset_closure_image hD
    have h2 : (fun z : X => (1 / 2 : ℝ) • z) '' Set.range (fun k : ℤ => ι (k : ℝ)) ⊆ (clZ ι : Set X) := by
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      have : (1 / 2 : ℝ) • ι (k : ℝ) = ι ((k : ℝ) / 2) := by rw [← map_smul]; congr 1; simp [div_eq_inv_mul]
      show (1 / 2 : ℝ) • ι (k : ℝ) ∈ clZ ι
      rw [this]; exact hk2 k
    exact closure_minimal h2 hclosed (h1 ⟨z, hz, rfl⟩)
  induction n with
  | zero => intro j; have := hZ j; rw [← SetLike.mem_coe, coe_clZ] at this; simpa using this
  | succ n ih =>
    intro j
    have hj : ι ((j : ℝ) / 2 ^ n) ∈ clZ ι := by rw [← SetLike.mem_coe, coe_clZ]; exact ih j
    have := hmap _ hj
    have e : (1 / 2 : ℝ) • ι ((j : ℝ) / 2 ^ n) = ι ((j : ℝ) / 2 ^ (n + 1)) := by
      rw [← map_smul]; congr 1; simp [pow_succ]; ring
    rw [e, ← SetLike.mem_coe, coe_clZ] at this
    exact this

/-- If every neighbourhood of `0` in `X` contains some `ι(k + 1/2)`, then `ι(ℤ)` is dense in `ι(ℝ)`. -/
theorem range_subset_closure (ι : ℝ →ₗ[ℝ] X) (hι : Continuous ι)
    (h : ∀ V ∈ 𝓝 (0 : X), ∃ k : ℤ, ι ((k : ℝ) + 1 / 2) ∈ V) (x : ℝ) :
    ι x ∈ closure (Set.range (fun k : ℤ => ι (k : ℝ))) := by
  have hP : IsClosed (ι ⁻¹' closure (Set.range (fun k : ℤ => ι (k : ℝ)))) := isClosed_closure.preimage hι
  have ht : Tendsto (fun n : ℕ => ((⌊x * 2 ^ n⌋ : ℤ) : ℝ) / 2 ^ n) atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    have h1 := Int.floor_le (x * 2 ^ n)
    have h2 := Int.lt_floor_add_one (x * 2 ^ n)
    rw [Real.dist_eq, abs_le]
    have e : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by rw [one_div_pow]
    rw [e]
    have ha1 : ((⌊x * 2 ^ n⌋ : ℤ) : ℝ) / 2 ^ n ≤ x := by rw [div_le_iff₀ hpos]; exact h1
    have ha3 : x < (((⌊x * 2 ^ n⌋ : ℤ) : ℝ) + 1) / 2 ^ n := by rw [lt_div_iff₀ hpos]; exact h2
    have ha4 : (((⌊x * 2 ^ n⌋ : ℤ) : ℝ) + 1) / 2 ^ n = ((⌊x * 2 ^ n⌋ : ℤ) : ℝ) / 2 ^ n + 1 / 2 ^ n := by ring
    have hp1 : (0 : ℝ) < 1 / 2 ^ n := by positivity
    constructor <;> linarith
  exact hP.mem_of_tendsto ht (Filter.Eventually.of_forall fun n => dyadic_mem_closure ι h n _)

end Gen
end PVG
