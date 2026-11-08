import LeanCheck.PVGIndependence

/-!
# PVG: independence for finitely many jointly lacunary sequences (Lean check)

Scope. Formal counterpart of Theorem 8.36 of `PVG_v17` in the concrete setting of `PVGSequences` and
`PVGIndependence` (`K = Hom(ℝ, 𝕋)`, `e`, the limits `L y U` along free ultrafilters).

* `free_map`, `L_comp`: the image of a free ultrafilter under an injective map is free, and `L (y ∘ f) U = L y (f_* U)`;
* `independence_merged` (Theorem 8.36): let `y¹, …, yᵐ` be real sequences all of whose terms occur in one sequence `z` with
  nonzero terms and `|z (k+1)| / |z k| → ∞` (formally: injective maps `ι j : ℕ → ℕ` with pairwise disjoint ranges and
  `y j k = z (ι j k)`; the sorted list of all terms of the `yʲ` is such a `z`). Then for pairwise distinct free ultrafilters
  `W₁, …, Wₙ` and real coefficients `γ j l` not all zero, `∑ j l, γ j l • L (yʲ) (W l)` is not of the form `e x`.

The proof reduces to the one-sequence theorem `independence` for the merged sequence `z`. The paper's hypothesis (the numbers
`|y^j_k|`, listed in increasing order, have consecutive ratios tending to infinity) gives such a `z`; the sorted enumeration is
not formalized here. A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note
requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Q95

lemma free_map {f : ℕ → ℕ} (hf : Function.Injective f) {U : Ultrafilter ℕ} (hU : Free U) :
    Free (U.map f) := by
  intro s hs
  rw [Ultrafilter.coe_map, Filter.mem_map]
  have hfin : sᶜ.Finite := Filter.mem_cofinite.mp hs
  have : (f ⁻¹' s)ᶜ.Finite := by
    rw [← Set.preimage_compl]
    exact hfin.preimage hf.injOn
  exact hU (Filter.mem_cofinite.mpr this)

lemma map_injective' {f : ℕ → ℕ} (hf : Function.Injective f) {U U' : Ultrafilter ℕ}
    (h : U.map f = U'.map f) : U = U' := by
  symm
  apply Ultrafilter.eq_of_le
  intro s hs
  have h1 : f '' s ∈ U.map f := by
    rw [Ultrafilter.mem_map]
    exact Filter.mem_of_superset hs (fun x hx => ⟨x, hx, rfl⟩)
  rw [h, Ultrafilter.mem_map] at h1
  have : f ⁻¹' (f '' s) = s := Set.preimage_image_eq s hf
  rwa [this] at h1

lemma L_comp (y : ℕ → ℝ) (f : ℕ → ℕ) (U : Ultrafilter ℕ) :
    L (fun k => y (f k)) U = L y (U.map f) := by
  apply L_eq_of_tendsto
  have h1 := tendsto_L y (U.map f)
  have h2 : Tendsto f (U : Filter ℕ) ((U.map f : Ultrafilter ℕ) : Filter ℕ) := by
    rw [Ultrafilter.coe_map]; exact Filter.tendsto_map
  exact h1.comp h2

lemma range_mem_map (f : ℕ → ℕ) (U : Ultrafilter ℕ) : Set.range f ∈ U.map f := by
  rw [Ultrafilter.mem_map]
  exact Filter.univ_mem' (fun x => ⟨x, rfl⟩)

/-- **Theorem 8.36, formal form (merged sequence).** -/
theorem independence_merged {m n : ℕ} (y : Fin m → ℕ → ℝ) (z : ℕ → ℝ) (hz0 : ∀ k, z k ≠ 0)
    (hz : Tendsto (fun k => |z (k + 1)| / |z k|) atTop atTop) (ι : Fin m → ℕ → ℕ)
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j' k k', ι j k = ι j' k' → j = j')
    (hyz : ∀ j k, y j k = z (ι j k)) (W : Fin n → Ultrafilter ℕ) (hWi : Function.Injective W)
    (hWf : ∀ l, Free (W l)) (γ : Fin m → Fin n → ℝ) (hγ : ∃ j l, γ j l ≠ 0) (x : ℝ) :
    ∑ j, ∑ l, γ j l • L (y j) (W l) ≠ e x := by
  classical
  have hy : ∀ j, y j = fun k => z (ι j k) := fun j => funext (hyz j)
  set V : Fin m × Fin n → Ultrafilter ℕ := fun p => (W p.2).map (ι p.1) with hV
  have hVf : ∀ p, Free (V p) := fun p => free_map (hι p.1) (hWf p.2)
  have hVi : Function.Injective V := by
    intro p q hpq
    have hj : p.1 = q.1 := by
      by_contra hne
      have h1 : Set.range (ι p.1) ∈ V p := range_mem_map _ _
      have h2 : Set.range (ι q.1) ∈ V q := range_mem_map _ _
      rw [hpq] at h1
      have h3 : Set.range (ι p.1) ∩ Set.range (ι q.1) ∈ V q := Filter.inter_mem h1 h2
      have : Set.range (ι p.1) ∩ Set.range (ι q.1) = ∅ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false, iff_false, not_and]
        rintro ⟨a, rfl⟩ ⟨b, hb⟩
        exact hne (hdisj _ _ _ _ hb.symm)
      rw [this] at h3
      exact (V q).empty_notMem h3
    have hW' : W p.2 = W q.2 := by
      apply map_injective' (hι p.1)
      have : V q = (W q.2).map (ι p.1) := by rw [hV]; simp only; rw [← hj]
      rw [← this]
      exact hpq
    exact Prod.ext hj (hWi hW')
  have hsum : ∑ j, ∑ l, γ j l • L (y j) (W l) = ∑ p : Fin m × Fin n, γ p.1 p.2 • L z (V p) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hy j, L_comp]
  rw [hsum]
  let e₀ : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  have hrw : ∑ p : Fin m × Fin n, γ p.1 p.2 • L z (V p) =
      ∑ i : Fin (m * n), γ (e₀.symm i).1 (e₀.symm i).2 • L z (V (e₀.symm i)) :=
    (Equiv.sum_comp e₀.symm (fun p => γ p.1 p.2 • L z (V p))).symm
  rw [hrw]
  obtain ⟨j0, l0, h0⟩ := hγ
  exact independence z hz0 hz (fun i => V (e₀.symm i)) (hVi.comp e₀.symm.injective)
    (fun i => hVf _) (fun i => γ (e₀.symm i).1 (e₀.symm i).2) ⟨e₀ (j0, l0), by simpa using h0⟩ x

#print axioms free_map
#print axioms L_comp
#print axioms independence_merged

end Q95
end PVG
