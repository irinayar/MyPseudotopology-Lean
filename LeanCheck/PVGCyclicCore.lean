import Mathlib
import LeanCheck.PVGNoLqcCore

/-!
# PVG: cyclic subgroups and locally quasi-convex topologies, the core (Lean check)

Scope. The proof of Proposition 8.97 of `PVG_v43` (Part II), conditional on Step 1 of Proposition 8.88 (as in `PVGNoLqcCore`: `hV`,
`hcE`, `hC` are the hypotheses that a locally quasi-convex `γ` with `τ_B ⊊ γ ⊆ τ_E` provides). For `x ∈ ℝ` let `xℤ` (`Zmul x`) be the cyclic
subgroup. If `γ` induces the Bohr topology on `xℤ`, then `xℤ` is `γ`-totally bounded (the Bohr topology is precompact), and the argument of
Step 5 gives `‖n θ‖ < 1/4` for all integers `n`, `θ = (c_{K+1} - c_K) x`, hence `θ ∈ ℤ`.

* `bohr_precompact` : every subset `A` of `ℝ` is totally bounded for the Bohr topology (with the centres taken in `A`), by compactness of `K`;
* `int_of_dint` : if `‖n θ‖ < 1/4` for all `n ∈ ℤ` then `θ ∈ ℤ`;
* `cyclic_core` : if `γ` induces the Bohr topology on `xℤ`, then `(c_{K+1} - c_K) x ∈ ℤ` for some `K`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set

namespace PVG
namespace Lac
open Q95

/-- The cyclic subgroup `xℤ`. -/
def Zmul (x : ℝ) : Set ℝ := {y | ∃ n : ℤ, y = n * x}

lemma zero_mem_Zmul (x : ℝ) : (0 : ℝ) ∈ Zmul x := ⟨0, by simp⟩

lemma sub_mem_Zmul {x y z : ℝ} (hy : y ∈ Zmul x) (hz : z ∈ Zmul x) : y - z ∈ Zmul x := by
  obtain ⟨n, rfl⟩ := hy
  obtain ⟨m, rfl⟩ := hz
  exact ⟨n - m, by push_cast; ring⟩

/-- Every subset of `ℝ` is totally bounded for the Bohr topology, with centres in the subset. -/
theorem bohr_precompact (A : Set ℝ) (V : Set ℝ) (hV : V ∈ @nhds ℝ bohrTop 0) :
    ∃ F : Set ℝ, F.Finite ∧ F ⊆ A ∧ ∀ z ∈ A, ∃ f ∈ F, z - f ∈ V := by
  classical
  rw [nhds_bohr] at hV
  obtain ⟨O, hO, hOV⟩ := Filter.mem_comap.1 hV
  have hO0 : O ∈ 𝓝 (0 : K) := by rwa [show (0 : K) = e 0 from e_zero.symm]
  -- a neighbourhood `O'` of `0` in `K` with `O' - O' ⊆ O`
  have hcont : Tendsto (fun p : K × K => p.1 - p.2) (𝓝 ((0 : K), (0 : K))) (𝓝 ((0 : K) - 0)) :=
    continuous_subK.tendsto (0, 0)
  rw [sub_self] at hcont
  have hpre : (fun p : K × K => p.1 - p.2) ⁻¹' O ∈ 𝓝 ((0 : K), (0 : K)) := hcont hO0
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hpre
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := hpre
  set O' : Set K := t1 ∩ t2 with hO'
  have hO'0 : O' ∈ 𝓝 (0 : K) := Filter.inter_mem ht1 ht2
  have hO'O : ∀ u ∈ O', ∀ v ∈ O', u - v ∈ O := fun u hu v hv => hsub (show (u, v) ∈ t1 ×ˢ t2 from ⟨hu.1, hv.2⟩)
  -- cover `K` by the translates `{y | y - κ ∈ O'}`
  have hcov : ∀ κ ∈ (Set.univ : Set K), (fun y : K => y - κ) ⁻¹' O' ∈ 𝓝 κ := by
    intro κ _
    have : Tendsto (fun y : K => y - κ) (𝓝 κ) (𝓝 (κ - κ)) :=
      (continuous_subK.comp (continuous_id.prodMk continuous_const)).tendsto κ
    rw [sub_self] at this
    exact this hO'0
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover _ hcov
  -- pick centres in `A`
  let pick : K → Set ℝ := fun κ => if h : ∃ a ∈ A, e a - κ ∈ O' then {Classical.choose h} else ∅
  refine ⟨⋃ κ ∈ t, pick κ, t.finite_toSet.biUnion fun κ _ => ?_, ?_, ?_⟩
  · simp only [pick]; split_ifs <;> simp
  · intro f hf
    simp only [mem_iUnion] at hf
    obtain ⟨κ, -, hfκ⟩ := hf
    simp only [pick] at hfκ
    split_ifs at hfκ with h
    · rw [Set.mem_singleton_iff] at hfκ
      rw [hfκ]
      exact (Classical.choose_spec h).1
    · exact absurd hfκ (Set.notMem_empty _)
  · intro z hz
    have hz' : e z ∈ ⋃ κ ∈ t, (fun y : K => y - κ) ⁻¹' O' := by
      have := ht (Set.mem_univ (e z))
      simpa using this
    simp only [mem_iUnion] at hz'
    obtain ⟨κ, hκt, hzκ⟩ := hz'
    have hex : ∃ a ∈ A, e a - κ ∈ O' := ⟨z, hz, hzκ⟩
    refine ⟨Classical.choose hex, ?_, ?_⟩
    · simp only [mem_iUnion]
      refine ⟨κ, hκt, ?_⟩
      simp only [pick, dif_pos hex]
      exact Set.mem_singleton _
    · have hf := (Classical.choose_spec hex).2
      apply hOV
      show e (z - Classical.choose hex) ∈ O
      rw [e_sub']
      have := hO'O _ hzκ _ hf
      simpa using this

lemma dint_eq (t : ℝ) : dint t = |t - round t| := by
  unfold dint
  have h := AddCircle.norm_eq (p := (1 : ℝ)) (x := t)
  simpa using h

lemma dint_abs_of_lt (v : ℝ) (hv : |v| < 1 / 2) : dint v = |v| := by
  rw [dint_eq]
  have : round v = 0 := by
    rw [round_eq_zero_iff]
    constructor <;> linarith [abs_lt.1 hv]
  simp [this]

lemma dint_add_int (t : ℝ) (k : ℤ) : dint (t + k) = dint t := by
  unfold dint
  have hk : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  rw [AddCircle.coe_add, hk, add_zero]

/-- If `‖n θ‖ < 1/4` for every integer `n`, then `θ` is an integer. -/
lemma int_of_dint (θ : ℝ) (h : ∀ n : ℤ, dint (n * θ) < 1 / 4) : ∃ m : ℤ, θ = m := by
  set m : ℤ := round θ with hm
  set u : ℝ := θ - m with hu
  by_cases hu0 : u = 0
  · exact ⟨m, by linarith⟩
  have habs : 0 < |u| := abs_pos.2 hu0
  have h1 : |u| < 1 / 4 := by
    have := h 1
    rw [dint_eq] at this
    simpa [hu, hm] using this
  set N : ℕ := ⌈1 / (4 * |u|)⌉₊ with hN
  have hN1 : 1 / (4 * |u|) ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) < 1 / (4 * |u|) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlow : 1 / 4 ≤ N * |u| := by
    have := mul_le_mul_of_nonneg_right hN1 habs.le
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at this
    nlinarith
  have hup : (N : ℝ) * |u| < 1 / 2 := by
    have := mul_lt_mul_of_pos_right hN2 habs
    have e1 : (1 / (4 * |u|) + 1) * |u| = 1 / 4 + |u| := by field_simp
    rw [e1] at this
    linarith
  have hNθ : ((N : ℤ) : ℝ) * θ = (N : ℝ) * u + ((N : ℤ) * m : ℤ) := by
    push_cast; rw [hu]; ring
  have hcontr := h (N : ℤ)
  rw [hNθ, dint_add_int, dint_abs_of_lt (N * u) (by rw [abs_mul, Nat.abs_cast]; exact hup)] at hcontr
  rw [abs_mul, Nat.abs_cast] at hcontr
  linarith

/-- Splitting used in Step 5: `(p - q) x = p (x - f) - q (x - f) + (p - q) f`. -/
lemma dint_split (p q x f : ℝ) (h1 : dint (p * (x - f)) < 1 / 12) (h2 : dint (q * (x - f)) < 1 / 12)
    (h3 : dint ((p - q) * f) < 1 / 12) : dint ((p - q) * x) < 1 / 4 := by
  have hsplit : (p - q) * x = p * (x - f) + (-(q * (x - f))) + (p - q) * f := by ring
  rw [hsplit]
  have a1 : dint (p * (x - f) + -(q * (x - f)) + (p - q) * f) ≤
      dint (p * (x - f) + -(q * (x - f))) + dint ((p - q) * f) := dint_add_le _ _
  have a2 : dint (p * (x - f) + -(q * (x - f))) ≤ dint (p * (x - f)) + dint (-(q * (x - f))) :=
    dint_add_le _ _
  rw [dint_neg] at a2
  linarith

set_option maxHeartbeats 800000 in
/-- Proposition 8.97, core: if `γ` induces the Bohr topology on the cyclic subgroup `xℤ`, then `(c_{K+1} - c_K) x ∈ ℤ` for some `K`. -/
theorem cyclic_core (γ : TopologicalSpace ℝ) (E : Set ℝ)
    (hV : ∀ ε : ℝ, 0 < ε → {y : ℝ | ∀ c ∈ E, dint (c * y) < ε} ∈ @nhds ℝ γ 0)
    (c : ℕ → ℝ) (hcE : ∀ k, c k ∈ E)
    (hC : ∀ ε > 0, ∃ K : ℕ, ∀ k k' : ℕ, K ≤ k → K ≤ k' → |c k - c k'| < ε)
    (x : ℝ)
    (hind : TopologicalSpace.induced (Subtype.val : Zmul x → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Zmul x → ℝ) bohrTop) :
    ∃ K : ℕ, ∃ m : ℤ, (c (K + 1) - c K) * x = m := by
  -- the trace condition at `0`
  obtain ⟨W, hW⟩ : ∃ W : Set ℝ, W = {y : ℝ | ∀ c ∈ E, dint (c * y) < 1 / 12} := ⟨_, rfl⟩
  have hWnhds : W ∈ @nhds ℝ γ 0 := by rw [hW]; exact hV (1 / 12) (by norm_num)
  set z0 : Zmul x := ⟨0, zero_mem_Zmul x⟩ with hz0
  have h1 : (Subtype.val : Zmul x → ℝ) ⁻¹' W ∈ @nhds (Zmul x) (TopologicalSpace.induced Subtype.val γ) z0 := by
    rw [@nhds_induced ℝ (Zmul x) γ Subtype.val z0]
    exact Filter.preimage_mem_comap hWnhds
  rw [hind, @nhds_induced ℝ (Zmul x) bohrTop Subtype.val z0] at h1
  obtain ⟨V, hV0, hVW⟩ := Filter.mem_comap.1 h1
  obtain ⟨F, hFfin, hFA, hFcov⟩ := bohr_precompact (Zmul x) V hV0
  obtain ⟨Fs, hFs⟩ := hFfin.exists_finset_coe
  -- Step 5 for the finite set `Fs`
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ f ∈ Fs, |f| ≤ M := by
    refine ⟨1 + ∑ f ∈ Fs, |f|, by positivity, fun f hf => ?_⟩
    have := Finset.single_le_sum (fun g _ => abs_nonneg g) hf
    linarith
  obtain ⟨K, hK⟩ := hC (1 / (12 * M)) (by positivity)
  have hdiff : |c (K + 1) - c K| < 1 / (12 * M) := hK (K + 1) K (by omega) le_rfl
  have hcover : ∀ n : ℤ, dint ((c (K + 1) - c K) * (n * x)) < 1 / 4 := by
    intro n
    have hn : (n : ℝ) * x ∈ Zmul x := ⟨n, rfl⟩
    obtain ⟨f, hfF, hfV⟩ := hFcov _ hn
    have hfA : f ∈ Zmul x := hFA hfF
    have hfFs : f ∈ Fs := by rw [← Finset.mem_coe, hFs]; exact hfF
    have hmemW : ∀ c ∈ E, dint (c * ((n : ℝ) * x - f)) < 1 / 12 := by
      have hmemJ : (n : ℝ) * x - f ∈ Zmul x := sub_mem_Zmul hn hfA
      have hmemV : (⟨(n : ℝ) * x - f, hmemJ⟩ : Zmul x) ∈ (Subtype.val : Zmul x → ℝ) ⁻¹' V := hfV
      have hmemW0 : (⟨(n : ℝ) * x - f, hmemJ⟩ : Zmul x) ∈ (Subtype.val : Zmul x → ℝ) ⁻¹' W := hVW hmemV
      have hmemW1 : (n : ℝ) * x - f ∈ W := hmemW0
      rw [hW] at hmemW1
      exact hmemW1
    have h3 : dint ((c (K + 1) - c K) * f) < 1 / 12 := by
      calc dint ((c (K + 1) - c K) * f) ≤ |(c (K + 1) - c K) * f| := dint_le_abs _
        _ = |c (K + 1) - c K| * |f| := abs_mul _ _
        _ ≤ |c (K + 1) - c K| * M := mul_le_mul_of_nonneg_left (hM f hfFs) (abs_nonneg _)
        _ < 1 / (12 * M) * M := mul_lt_mul_of_pos_right hdiff hM0
        _ = 1 / 12 := by field_simp
    exact dint_split (c (K + 1)) (c K) ((n : ℝ) * x) f (hmemW (c (K + 1)) (hcE (K + 1))) (hmemW (c K) (hcE K)) h3
  refine ⟨K, ?_⟩
  have : ∀ n : ℤ, dint ((n : ℝ) * ((c (K + 1) - c K) * x)) < 1 / 4 := by
    intro n
    have := hcover n
    rwa [show (n : ℝ) * ((c (K + 1) - c K) * x) = (c (K + 1) - c K) * ((n : ℝ) * x) by ring]
  exact int_of_dint _ this

end Lac
end PVG
