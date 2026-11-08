import LeanCheck.PVGIndependence

/-!
# PVG: some uncountable families with admissible span, and one retraction for them (Lean check)

Scope. Formal counterpart of Proposition 8.38 and Corollary 8.39 of `PVG_v17` in the concrete setting of `PVGSequences` and
`PVGIndependence` (`K = Hom(ℝ, 𝕋)`, `e`, the limits `L y U`, the criterion `SC π a`).

* `FiniteToOne f`, `free_map_fto`, `L_comp'`: a finite-to-one map sends a free ultrafilter to a free ultrafilter, and
  `L (y ∘ σ) U = L y (σ_* U)`;
* `L_rep`: if `y k = ∑ j, r j * y0 (c j) (σ j k) + z k` with `z` convergent to `a` along a set `B`, then for free `U ∋ B`,
  `L y U = ∑ j, r j • L (y0 (c j)) (σ_j* U) + e a`;
* `prop_uncountable_gen` (Proposition 8.38, general form): for a base family `y0 : I → ℕ → ℝ` whose limits span a subspace
  meeting `ℝ e(1)` only in `0` (`hind`), and any family of sequences `y i` of the form above (finite combinations of
  finite-to-one reindexings of the base sequences plus a bounded sequence convergent along `B i`), the real span of all
  `L (y i) U - L (y i) V`, `U, V` free containing `B i`, meets `ℝ e(1)` only in `0`;
* `disjoint_span_L` (the one-base case of `hind`, from `independence_finset`), `prop_uncountable` (Proposition 8.38 for one
  base sequence);
* `exists_retraction_of_family` (Corollary 8.39): if the sets `B i` are infinite there is a real linear `π` with
  `π (e 1) = 1` and `SC π (y i)` for every `i` (so `π` is good for every member).

The version with a family of jointly lacunary bases uses the finite-subfamily independence (`PVGMerged.independence_merged`);
it is not formalized here. A Lean proof verifies its formal statement under its hypotheses; the correspondence with the
research note requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Q95

/-- A map `ℕ → ℕ` is finite-to-one if every fibre is finite. -/
def FiniteToOne (f : ℕ → ℕ) : Prop := ∀ n, (f ⁻¹' {n}).Finite

lemma free_map_fto {f : ℕ → ℕ} (hf : FiniteToOne f) {U : Ultrafilter ℕ} (hU : Free U) :
    Free (U.map f) := by
  intro s hs
  rw [Ultrafilter.coe_map, Filter.mem_map]
  have hfin : sᶜ.Finite := Filter.mem_cofinite.mp hs
  have : (f ⁻¹' s)ᶜ.Finite := by
    rw [← Set.preimage_compl]
    have : f ⁻¹' sᶜ = ⋃ n ∈ sᶜ, f ⁻¹' {n} := by
      ext k; simp
    rw [this]
    exact hfin.biUnion (fun n _ => hf n)
  exact hU (Filter.mem_cofinite.mpr this)

lemma L_comp' (y : ℕ → ℝ) (f : ℕ → ℕ) (U : Ultrafilter ℕ) :
    L (fun k => y (f k)) U = L y (U.map f) := by
  apply L_eq_of_tendsto
  have h1 := tendsto_L y (U.map f)
  have h2 : Tendsto f (U : Filter ℕ) ((U.map f : Ultrafilter ℕ) : Filter ℕ) := by
    rw [Ultrafilter.coe_map]; exact Filter.tendsto_map
  exact h1.comp h2

lemma e_zero : e 0 = 0 := by ext b; simp [e]

lemma L_zero (U : Ultrafilter ℕ) : L (fun _ => (0 : ℝ)) U = 0 := by
  have := L_const 0 U
  rwa [e_zero] at this

lemma L_finset_sum {J : Type*} (s : Finset J) (f : J → ℕ → ℝ) (U : Ultrafilter ℕ) :
    L (fun k => ∑ j ∈ s, f j k) U = ∑ j ∈ s, L (f j) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using L_zero U
  | insert a s ha ih =>
    have : (fun k => ∑ j ∈ insert a s, f j k) = f a + fun k => ∑ j ∈ s, f j k := by
      funext k; simp [Finset.sum_insert ha]
    rw [this, L_add, ih, Finset.sum_insert ha]

lemma tendsto_of_conv_along {z : ℕ → ℝ} {a : ℝ} {B : Set ℕ} (hz : ∀ ε > 0, ∃ N, ∀ k ∈ B, N ≤ k → |z k - a| < ε)
    {U : Ultrafilter ℕ} (hU : Free U) (hB : B ∈ U) : Tendsto z U (𝓝 a) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := hz ε hε
  have h1 : {k | N ≤ k} ∈ (U : Filter ℕ) := by
    apply hU
    rw [Filter.mem_cofinite]
    have : {k | N ≤ k}ᶜ ⊆ Set.Iio N := fun k hk => by simpa using hk
    exact (Set.finite_Iio N).subset this
  filter_upwards [hB, h1] with k hkB hkN
  rw [Real.dist_eq]
  exact hN k hkB hkN

lemma L_conv_const {z : ℕ → ℝ} {a : ℝ} {B : Set ℕ} (hz : ∀ ε > 0, ∃ N, ∀ k ∈ B, N ≤ k → |z k - a| < ε)
    {U : Ultrafilter ℕ} (hU : Free U) (hB : B ∈ U) : L z U = e a := by
  apply L_eq_of_tendsto
  exact (continuous_e.tendsto a).comp (tendsto_of_conv_along hz hU hB)

/-- The limit of a finite combination of reindexed base sequences plus a convergent remainder. -/
lemma L_rep {I : Type*} (y0 : I → ℕ → ℝ) {m : ℕ} (c : Fin m → I) (r : Fin m → ℝ) (σ : Fin m → ℕ → ℕ)
    (hσ : ∀ j, FiniteToOne (σ j)) (z : ℕ → ℝ) (a : ℝ) (B : Set ℕ)
    (hz : ∀ ε > 0, ∃ N, ∀ k ∈ B, N ≤ k → |z k - a| < ε) (y : ℕ → ℝ)
    (hy : ∀ k, y k = ∑ j, r j * y0 (c j) (σ j k) + z k) {U : Ultrafilter ℕ} (hU : Free U) (hB : B ∈ U) :
    L y U = ∑ j, r j • L (y0 (c j)) (U.map (σ j)) + e a := by
  have hy' : y = (fun k => ∑ j, (r j • (fun k => y0 (c j) (σ j k))) k) + z := by
    funext k; simp [hy k]
  have hsum := L_finset_sum Finset.univ (fun j => r j • (fun k => y0 (c j) (σ j k))) U
  rw [hy', L_add, hsum, L_conv_const hz hU hB]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [L_smul, L_comp']

/-- **Proposition 8.38, general form.** -/
theorem prop_uncountable_gen {I ι : Type*} (y0 : I → ℕ → ℝ)
    (hind : Disjoint (Submodule.span ℝ {v : K | ∃ (i : I) (U : Ultrafilter ℕ), Free U ∧ v = L (y0 i) U}) (ℝ ∙ e 1))
    (m : ι → ℕ) (c : (i : ι) → Fin (m i) → I) (r : (i : ι) → Fin (m i) → ℝ)
    (σ : (i : ι) → Fin (m i) → ℕ → ℕ) (hσ : ∀ i j, FiniteToOne (σ i j))
    (z : ι → ℕ → ℝ) (a : ι → ℝ) (B : ι → Set ℕ)
    (hz : ∀ i, ∀ ε > 0, ∃ N, ∀ k ∈ B i, N ≤ k → |z i k - a i| < ε) (y : ι → ℕ → ℝ)
    (hy : ∀ i k, y i k = ∑ j, r i j * y0 (c i j) (σ i j k) + z i k) :
    Disjoint (Submodule.span ℝ {v : K | ∃ i, ∃ U V : Ultrafilter ℕ, Free U ∧ Free V ∧ B i ∈ U ∧ B i ∈ V ∧
      v = L (y i) U - L (y i) V}) (ℝ ∙ e 1) := by
  refine Disjoint.mono_left ?_ hind
  apply Submodule.span_le.mpr
  rintro v ⟨i, U, V, hU, hV, hBU, hBV, rfl⟩
  rw [L_rep y0 (c i) (r i) (σ i) (hσ i) (z i) (a i) (B i) (hz i) (y i) (hy i) hU hBU,
    L_rep y0 (c i) (r i) (σ i) (hσ i) (z i) (a i) (B i) (hz i) (y i) (hy i) hV hBV]
  have : (∑ j, r i j • L (y0 (c i j)) (U.map (σ i j)) + e (a i)) -
      (∑ j, r i j • L (y0 (c i j)) (V.map (σ i j)) + e (a i)) =
      ∑ j, r i j • (L (y0 (c i j)) (U.map (σ i j)) - L (y0 (c i j)) (V.map (σ i j))) := by
    rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_sub]
  rw [this]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · exact Submodule.subset_span ⟨c i j, _, free_map_fto (hσ i j) hU, rfl⟩
  · exact Submodule.subset_span ⟨c i j, _, free_map_fto (hσ i j) hV, rfl⟩

/-- The limits `L y0 U`, `U` free, of a sequence with nonzero terms and ratios tending to infinity span a subspace meeting
`ℝ e(1)` only in `0`. -/
theorem disjoint_span_L (y0 : ℕ → ℝ) (hy0 : ∀ k, y0 k ≠ 0)
    (hy : Tendsto (fun k => |y0 (k + 1)| / |y0 k|) atTop atTop) :
    Disjoint (Submodule.span ℝ {v : K | ∃ (_ : Unit) (U : Ultrafilter ℕ), Free U ∧ v = L y0 U}) (ℝ ∙ e 1) := by
  classical
  rw [Submodule.disjoint_def]
  intro x hx hx1
  have hx' : x ∈ Submodule.span ℝ (Set.range (fun U : {U : Ultrafilter ℕ // Free U} => L y0 U.1)) := by
    refine Submodule.span_mono ?_ hx
    rintro v ⟨_, U, hU, rfl⟩
    exact ⟨⟨U, hU⟩, rfl⟩
  obtain ⟨g, hg⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hx'
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx1
  have hxe : x = e b := by rw [← hb, e_eq_smul b]
  have hs : ∀ U ∈ g.support.map (Function.Embedding.subtype (fun U : Ultrafilter ℕ => Free U)), Free U := by
    intro U hU
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.1 hU
    exact u.2
  have hsum : ∑ U ∈ g.support.map (Function.Embedding.subtype (fun U : Ultrafilter ℕ => Free U)),
      (fun U => if h : Free U then g ⟨U, h⟩ else 0) U • L y0 U = e b := by
    rw [Finset.sum_map, ← hxe, ← hg, Finsupp.sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [u.2]
  have hall := independence_finset y0 hy0 hy _ hs _ b hsum
  have hg0 : g = 0 := by
    ext u
    by_cases hu : u ∈ g.support
    · have := hall u.1 (Finset.mem_map.2 ⟨u, hu, rfl⟩)
      simpa [u.2] using this
    · simpa using Finsupp.notMem_support_iff.1 hu
  rw [← hg, hg0]; simp

/-- **Proposition 8.38** for one base sequence `y0` (nonzero terms, ratios tending to infinity). -/
theorem prop_uncountable (y0 : ℕ → ℝ) (hy0 : ∀ k, y0 k ≠ 0)
    (hy : Tendsto (fun k => |y0 (k + 1)| / |y0 k|) atTop atTop) {ι : Type*}
    (m : ι → ℕ) (r : (i : ι) → Fin (m i) → ℝ) (σ : (i : ι) → Fin (m i) → ℕ → ℕ)
    (hσ : ∀ i j, FiniteToOne (σ i j)) (z : ι → ℕ → ℝ) (a : ι → ℝ) (B : ι → Set ℕ)
    (hz : ∀ i, ∀ ε > 0, ∃ N, ∀ k ∈ B i, N ≤ k → |z i k - a i| < ε) (yy : ι → ℕ → ℝ)
    (hyy : ∀ i k, yy i k = ∑ j, r i j * y0 (σ i j k) + z i k) :
    Disjoint (Submodule.span ℝ {v : K | ∃ i, ∃ U V : Ultrafilter ℕ, Free U ∧ Free V ∧ B i ∈ U ∧ B i ∈ V ∧
      v = L (yy i) U - L (yy i) V}) (ℝ ∙ e 1) :=
  prop_uncountable_gen (fun _ : Unit => y0) (disjoint_span_L y0 hy0 hy) m (fun _ _ => ()) r σ hσ z a B hz yy hyy

/-- **Corollary 8.39** (one retraction for the whole family). -/
theorem exists_retraction_of_family {I ι : Type*} (y0 : I → ℕ → ℝ)
    (hind : Disjoint (Submodule.span ℝ {v : K | ∃ (i : I) (U : Ultrafilter ℕ), Free U ∧ v = L (y0 i) U}) (ℝ ∙ e 1))
    (m : ι → ℕ) (c : (i : ι) → Fin (m i) → I) (r : (i : ι) → Fin (m i) → ℝ)
    (σ : (i : ι) → Fin (m i) → ℕ → ℕ) (hσ : ∀ i j, FiniteToOne (σ i j))
    (z : ι → ℕ → ℝ) (a : ι → ℝ) (B : ι → Set ℕ) (hBinf : ∀ i, (B i).Infinite)
    (hz : ∀ i, ∀ ε > 0, ∃ N, ∀ k ∈ B i, N ≤ k → |z i k - a i| < ε) (y : ι → ℕ → ℝ)
    (hy : ∀ i k, y i k = ∑ j, r i j * y0 (c i j) (σ i j k) + z i k) :
    ∃ π : K →ₗ[ℝ] ℝ, π (e 1) = 1 ∧ ∀ i, SC π (y i) := by
  classical
  have hdis := prop_uncountable_gen y0 hind m c r σ hσ z a B hz y hy
  let Lac : Set (ℕ → ℝ) := Set.range y
  let Bsel : (ℕ → ℝ) → Set ℕ := fun w => if h : ∃ i, y i = w then B (Classical.choose h) else ∅
  have hBsel : ∀ i, ∃ i0, y i0 = y i ∧ Bsel (y i) = B i0 := by
    intro i
    have h : ∃ i', y i' = y i := ⟨i, rfl⟩
    exact ⟨Classical.choose h, Classical.choose_spec h, by simp only [Bsel]; rw [dif_pos h]⟩
  have hR4 := (R4 (e 1) e_one_ne_zero Lac L Free).2 ⟨Bsel, ?_, ?_⟩
  · obtain ⟨π, h1, hπ⟩ := hR4
    exact ⟨π, h1, fun i => hπ (y i) ⟨i, rfl⟩⟩
  · rintro w ⟨i, rfl⟩
    obtain ⟨i0, _, hi0⟩ := hBsel i
    rw [hi0]; exact hBinf i0
  · refine Disjoint.mono_left ?_ hdis
    apply Submodule.span_mono
    rintro v ⟨w, ⟨i, rfl⟩, U, V, hU, hV, hBU, hBV, rfl⟩
    obtain ⟨i0, hyi0, hi0⟩ := hBsel i
    rw [hi0] at hBU hBV
    exact ⟨i0, U, V, hU, hV, hBU, hBV, by rw [hyi0]⟩

#print axioms free_map_fto
#print axioms L_rep
#print axioms prop_uncountable_gen
#print axioms disjoint_span_L
#print axioms prop_uncountable
#print axioms exists_retraction_of_family

end Q95
end PVG
