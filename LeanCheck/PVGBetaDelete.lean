import Mathlib

/-!
# PVG: deleting centers (Lean check)

Scope. Lemma `lem:deletion` of PVG_v22. Let `x₁, …, x_N` be real numbers that are algebraically independent over `ℚ` and let
`c₁, …, c_m` be arbitrary reals. Then there is a set `E` of at most `m` indices such that `1` is not in the rational linear span of the
numbers `c_i x_j`, `j ∉ E`.

* `one_not_mem_span`: if the numbers `x_j`, `j ∈ T`, are algebraically independent over the subring `ℚ[c₁, …, c_m]`, then `1` is not in
  the rational linear span of `c_i x_j`, `j ∈ T`.
* `exists_indep_subfamily`: such a set `T` with `N ≤ m + |T|` exists (additivity of the transcendence degree in a tower).
* `deletion`: the lemma.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Cardinal

namespace PVG
namespace Beta

/-- If the `x_j`, `j ∈ T`, are algebraically independent over `ℚ[c]`, then `1` is not in the rational span of the products. -/
theorem one_not_mem_span {N m : ℕ} (x : Fin N → ℝ) (c : Fin m → ℝ) (T : Finset (Fin N))
    (hT : AlgebraicIndependent (Algebra.adjoin ℚ (Set.range c)) (fun j : T => x j)) :
    (1 : ℝ) ∉ Submodule.span ℚ (Set.range fun p : Fin m × T => c p.1 * x p.2) := by
  intro h
  rw [Submodule.mem_span_range_iff_exists_fun] at h
  obtain ⟨q, hq⟩ := h
  set S := Algebra.adjoin ℚ (Set.range c) with hS
  let cS : Fin m → S := fun i => ⟨c i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let a : T → S := fun j => ∑ i : Fin m, q (i, j) • cS i
  let P : MvPolynomial T S := ∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1
  have hP : MvPolynomial.aeval (R := S) (fun j : T => (x j : ℝ)) P = MvPolynomial.aeval (R := S) (fun j : T => (x j : ℝ)) 0 := by
    simp only [P, map_sub, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_one, map_zero]
    have h1 : ∀ j : T, (algebraMap S ℝ (a j)) = ∑ i : Fin m, q (i, j) • c i := by
      intro j
      simp [a, cS, map_sum, Rat.smul_def]
    have hsum : ∑ j : T, algebraMap S ℝ (a j) * (x j : ℝ) = 1 := by
      rw [← hq, Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [h1 j, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [smul_mul_assoc]
    rw [hsum, sub_self]
  have hz : P = 0 := hT hP
  have hc := congrArg MvPolynomial.constantCoeff hz
  have hc2 : MvPolynomial.constantCoeff P = -1 := by
    simp [P]
  rw [hc2, map_zero] at hc
  exact one_ne_zero (neg_eq_zero.mp hc)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- A subfamily of size at least `N - m` stays algebraically independent over `ℚ[c₁, …, c_m]`. -/
theorem exists_indep_subfamily {N m : ℕ} (x : Fin N → ℝ) (hx : AlgebraicIndependent ℚ x) (c : Fin m → ℝ) :
    ∃ T : Finset (Fin N), N ≤ m + T.card ∧
      AlgebraicIndependent (Algebra.adjoin ℚ (Set.range c)) (fun j : T => x j) := by
  classical
  set S : Subalgebra ℚ ℝ := Algebra.adjoin ℚ (Set.range c) with hS
  set A : Subalgebra S ℝ := Algebra.adjoin S (Set.range x) with hA
  -- (1) the transcendence degree of `S` over `ℚ` is at most `m`
  have h1 : Algebra.trdeg ℚ S ≤ (m : Cardinal) := by
    let cS : Fin m → S := fun i => ⟨c i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
    have hsurj : Function.Surjective (MvPolynomial.aeval cS : MvPolynomial (Fin m) ℚ →ₐ[ℚ] S) := by
      rintro ⟨s, hs⟩
      rw [hS, Algebra.adjoin_range_eq_range_aeval] at hs
      obtain ⟨p, rfl⟩ := hs
      refine ⟨p, Subtype.ext ?_⟩
      have := AlgHom.congr_fun (MvPolynomial.comp_aeval (R := ℚ) (σ := Fin m) (f := cS) S.val) p
      simpa [cS] using this
    have := trdeg_le_of_surjective _ hsurj
    simpa [MvPolynomial.trdeg_of_isDomain] using this
  -- (2) the transcendence degree of `A` over `ℚ` is at least `N`
  let x'' : Fin N → A := fun j => ⟨x j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
  have hx'' : AlgebraicIndependent ℚ x'' := by
    refine AlgebraicIndependent.of_comp ((A.val).restrictScalars ℚ) ?_
    simpa [Function.comp_def, x''] using hx
  have h2 : (N : Cardinal) ≤ Algebra.trdeg ℚ A := by
    simpa using hx''.cardinalMk_le_trdeg
  -- (3) the tower law
  have hfQS : FaithfulSMul ℚ S := (faithfulSMul_iff_algebraMap_injective ℚ S).2 (fun a b h =>
    (algebraMap ℚ ℝ).injective (by simpa using congrArg Subtype.val h))
  have hfSA : FaithfulSMul S A := (faithfulSMul_iff_algebraMap_injective S A).2 (fun a b h =>
    Subtype.val_injective (by simpa using congrArg Subtype.val h))
  have h3 := trdeg_add_eq ℚ S (A := A)
  -- (4) a transcendence basis of `A` over `S` among the `x_j`
  let s : Set A := ((↑) : A → ℝ) ⁻¹' (Set.range x)
  have hgen : Algebra.adjoin S s = ⊤ := Algebra.adjoin_adjoin_coe_preimage
  haveI : Algebra.IsAlgebraic (Algebra.adjoin S s) A := by
    rw [hgen]
    exact ⟨fun a => by simpa using isAlgebraic_algebraMap (R := (⊤ : Subalgebra S A)) (A := A) ⟨a, trivial⟩⟩
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := S) (A := A) s
  have h5 : Cardinal.mk t = Algebra.trdeg S A := ht.cardinalMk_eq_trdeg
  -- (5) the indices
  let T : Finset (Fin N) := Finset.univ.filter (fun j => x'' j ∈ t)
  have hxinj : Function.Injective x := hx.injective
  let e : T ≃ t := Equiv.ofBijective (fun j => ⟨x'' j.1, (Finset.mem_filter.1 j.2).2⟩) ⟨by
      intro j k hjk
      have : x'' j.1 = x'' k.1 := congrArg Subtype.val hjk
      have : x j.1 = x k.1 := congrArg Subtype.val this
      exact Subtype.ext (hxinj this), by
      rintro ⟨a, ha⟩
      obtain ⟨j, hj⟩ := hts ha
      have haj : a = x'' j := Subtype.ext hj.symm
      subst haj
      exact ⟨⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩, rfl⟩⟩
  have hcardT : Cardinal.mk t = T.card := by
    rw [← Cardinal.mk_coe_finset]; exact (Cardinal.mk_congr e).symm
  refine ⟨T, ?_, ?_⟩
  · have : (N : Cardinal) ≤ (m : Cardinal) + (T.card : Cardinal) := by
      calc (N : Cardinal) ≤ Algebra.trdeg ℚ A := h2
        _ = Algebra.trdeg ℚ S + Algebra.trdeg S A := h3.symm
        _ ≤ (m : Cardinal) + Cardinal.mk t := add_le_add h1 (le_of_eq h5.symm)
        _ = (m : Cardinal) + (T.card : Cardinal) := by rw [hcardT]
    exact_mod_cast this
  · have hind : AlgebraicIndependent S (fun j : T => x'' j.1) := by
      have := ht.1.comp (fun j : T => (⟨x'' j.1, (Finset.mem_filter.1 j.2).2⟩ : t)) e.injective
      exact this
    have := hind.map' (f := A.val) (Subtype.val_injective)
    exact this


/-- **Deleting centers.** There is a set `T` of indices with `N ≤ m + |T|` (so the complement `E` has at most `m` elements) such that
`1` is not in the rational linear span of the products `c_i x_j`, `j ∈ T`. -/
theorem deletion {N m : ℕ} (x : Fin N → ℝ) (hx : AlgebraicIndependent ℚ x) (c : Fin m → ℝ) :
    ∃ T : Finset (Fin N), N ≤ m + T.card ∧
      (1 : ℝ) ∉ Submodule.span ℚ (Set.range fun p : Fin m × T => c p.1 * x p.2) := by
  obtain ⟨T, hT, hind⟩ := exists_indep_subfamily x hx c
  exact ⟨T, hT, one_not_mem_span x c T hind⟩

end Beta
end PVG
