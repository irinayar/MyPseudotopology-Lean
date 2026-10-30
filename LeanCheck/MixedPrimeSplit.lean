import LeanCheck.MixedPrimeColoured

/-!
# Joint approximation implies splitting of continuous characters

Let `S2, S3` be nonempty scale sets (the two chains), `S = S2 ∪ S3`.  Suppose `x` satisfies the Lipschitz bound
`nrm (k x) ≤ C * Pn S k`, and suppose there are integers `k_j` with `Pn S3 (k_j) → 0` and `Pn S2 (k_j - 1) → 0`
("the element `(1,0)` lies in the closure of the diagonal").  Then `x = y + (x - y)` where `y` satisfies the
Lipschitz bound for `S2` alone and `x - y` for `S3` alone, with the same constant `C`.
The element `y` is a cluster point of `k_j x` in the circle.
-/

namespace LeanCheck
namespace MixedPrime

lemma Pn_zsmul_le {S : Set ℕ} (hS : S.Nonempty) (m k : ℤ) : Pn S (m * k) ≤ |(m : ℝ)| * Pn S k := by
  have h1 := Pn_nsmul_le hS m.natAbs k
  by_cases hm : 0 ≤ m
  · have : ((m.natAbs : ℤ)) = m := Int.natAbs_of_nonneg hm
    rw [this] at h1
    have e : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by simp [Nat.cast_natAbs]
    rwa [e] at h1
  · have hneg : ((m.natAbs : ℤ)) = -m := Int.ofNat_natAbs_of_nonpos (by omega)
    rw [hneg] at h1
    have e : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by simp [Nat.cast_natAbs]
    rw [e] at h1
    have : (-m) * k = -(m * k) := by ring
    rw [this, Pn_neg] at h1
    exact h1

lemma nrm_mul_eq (m : ℤ) (a : ℝ) : nrm ((m : ℝ) * a) = ‖m • (a : Circ)‖ := by
  unfold nrm; rw [← zsmul_eq_mul, AddCircle.coe_zsmul]

theorem split_of_joint {S2 S3 : Set ℕ} (h2 : S2.Nonempty) (h3 : S3.Nonempty) {x C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k : ℤ, nrm ((k : ℝ) * x) ≤ C * Pn (S2 ∪ S3) k) (kk : ℕ → ℤ)
    (ha : Filter.Tendsto (fun j => Pn S3 (kk j)) Filter.atTop (nhds 0))
    (hb : Filter.Tendsto (fun j => Pn S2 (kk j - 1)) Filter.atTop (nhds 0)) :
    ∃ y : ℝ, (∀ m : ℤ, nrm ((m : ℝ) * y) ≤ C * Pn S2 m) ∧
      (∀ m : ℤ, nrm ((m : ℝ) * (x - y)) ≤ C * Pn S3 m) := by
  have hSne : (S2 ∪ S3).Nonempty := h2.mono Set.subset_union_left
  -- cluster point of k_j x in the circle
  obtain ⟨z, -, φ, hφ, hz⟩ := (isCompact_univ (X := Circ)).tendsto_subseq
    (x := fun j : ℕ => ((((kk j : ℤ) : ℝ) * x : ℝ) : Circ)) (fun _ => Set.mem_univ _)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hφtop : Filter.Tendsto φ Filter.atTop Filter.atTop := hφ.tendsto_atTop
  have ha' := ha.comp hφtop
  have hb' := hb.comp hφtop
  have hcont : ∀ m : ℤ, Continuous fun c : Circ => ‖m • c‖ := fun m => continuous_norm.comp (continuous_zsmul m)
  refine ⟨y, ?_, ?_⟩
  · intro m
    have hlim : Filter.Tendsto (fun i => nrm ((m : ℝ) * (((kk (φ i) : ℤ) : ℝ) * x))) Filter.atTop
        (nhds (nrm ((m : ℝ) * y))) := by
      simp only [nrm_mul_eq]
      exact ((hcont m).tendsto _).comp hz
    have hbound : ∀ i, nrm ((m : ℝ) * (((kk (φ i) : ℤ) : ℝ) * x)) ≤
        C * max (Pn S2 m + |(m : ℝ)| * Pn S2 (kk (φ i) - 1)) (|(m : ℝ)| * Pn S3 (kk (φ i))) := by
      intro i
      have e : (m : ℝ) * (((kk (φ i) : ℤ) : ℝ) * x) = (((m * kk (φ i) : ℤ)) : ℝ) * x := by push_cast; ring
      rw [e]
      refine (hC _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
      refine (Pn_union_le hSne _).trans (max_le_max ?_ ?_)
      · have hsplit : m * kk (φ i) = m + m * (kk (φ i) - 1) := by ring
        rw [hsplit]
        exact (Pn_add_le h2 _ _).trans (add_le_add le_rfl (Pn_zsmul_le h2 _ _))
      · exact Pn_zsmul_le h3 _ _
    have hlim2 : Filter.Tendsto (fun i => C * max (Pn S2 m + |(m : ℝ)| * Pn S2 (kk (φ i) - 1))
        (|(m : ℝ)| * Pn S3 (kk (φ i)))) Filter.atTop (nhds (C * max (Pn S2 m + |(m : ℝ)| * 0) (|(m : ℝ)| * 0))) :=
      (((tendsto_const_nhds.add (hb'.const_mul _)).max (ha'.const_mul _))).const_mul C
    have := le_of_tendsto_of_tendsto hlim hlim2 (Filter.Eventually.of_forall hbound)
    simpa [max_eq_left (Pn_nonneg S2 m)] using this
  · intro m
    have h1 : Filter.Tendsto (fun i => ((x - ((kk (φ i) : ℤ) : ℝ) * x : ℝ) : Circ)) Filter.atTop
        (nhds ((x - y : ℝ) : Circ)) := by
      simp only [AddCircle.coe_sub]
      exact tendsto_const_nhds.sub hz
    have hlim : Filter.Tendsto (fun i => nrm ((m : ℝ) * (x - ((kk (φ i) : ℤ) : ℝ) * x))) Filter.atTop
        (nhds (nrm ((m : ℝ) * (x - y)))) := by
      simp only [nrm_mul_eq]
      exact ((hcont m).tendsto _).comp h1
    have hbound : ∀ i, nrm ((m : ℝ) * (x - ((kk (φ i) : ℤ) : ℝ) * x)) ≤
        C * max (|(m : ℝ)| * Pn S2 (kk (φ i) - 1)) (Pn S3 m + |(m : ℝ)| * Pn S3 (kk (φ i))) := by
      intro i
      have e : (m : ℝ) * (x - ((kk (φ i) : ℤ) : ℝ) * x) = (((m * (1 - kk (φ i)) : ℤ)) : ℝ) * x := by
        push_cast; ring
      rw [e]
      refine (hC _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
      refine (Pn_union_le hSne _).trans (max_le_max ?_ ?_)
      · have : m * (1 - kk (φ i)) = -(m * (kk (φ i) - 1)) := by ring
        rw [this, Pn_neg]
        exact Pn_zsmul_le h2 _ _
      · have hsplit : m * (1 - kk (φ i)) = m + (-m) * kk (φ i) := by ring
        rw [hsplit]
        refine (Pn_add_le h3 _ _).trans (add_le_add le_rfl ?_)
        have := Pn_zsmul_le h3 (-m) (kk (φ i))
        simpa using this
    have hlim2 : Filter.Tendsto (fun i => C * max (|(m : ℝ)| * Pn S2 (kk (φ i) - 1))
        (Pn S3 m + |(m : ℝ)| * Pn S3 (kk (φ i)))) Filter.atTop (nhds (C * max (|(m : ℝ)| * 0) (Pn S3 m + |(m : ℝ)| * 0))) :=
      (((hb'.const_mul _).max (tendsto_const_nhds.add (ha'.const_mul _)))).const_mul C
    have := le_of_tendsto_of_tendsto hlim hlim2 (Filter.Eventually.of_forall hbound)
    simpa [max_eq_right (Pn_nonneg S3 m)] using this

end MixedPrime
end LeanCheck
