import LeanCheck.PVGMinimal

/-!
# PVG: cardinalities and convergent sequences below the Bohr topology (Lean check)

Scope. Formal counterpart of Lemma `interp` (c) and Proposition `seqG` (Proposition 8.28) of `PVG_v19`: the count of free
ultrafilters on `ℕ`, the cardinality `2^𝔠` and the dimension `2^𝔠` of `K = Hom(ℝ, 𝕋)`, and the properties of sequences convergent
for `η_G`.

* `card_free_ultra`: there are `2^𝔠` free ultrafilters on `ℕ` (from `Cardinal.mk_ultrafilter_of_infinite`);
* `card_K`: `#K = 2^𝔠` (upper bound from `K ⊆ 𝕋^ℝ`, lower bound from the injective map `U ↦ L_y(U)` for a lacunary `y`, `L_sub_ne_e`);
  `rank_K`: `dim_ℝ K = 2^𝔠` (`PVG.rank_eq_of_card`);
* `seqG_bounded` (Proposition 8.28(a)): a bounded sequence converging for a Hausdorff PVG coarser than the Bohr topology converges in
  the Euclidean topology to the same limit;
* `seqG_unbounded` (Proposition 8.28(b)): if an unbounded sequence converges for `η_G`, then `dim_ℝ G = 2^𝔠`;
* `card_retractions_K`, `card_minimal`, `minimal_antichain` (Corollary 8.27(c)): `2^(2^𝔠)` linear retractions, `2^(2^𝔠)` complements of the line, and the
  minimal PVGs `η_{ker π}` are pairwise incomparable;
* `block_sum_inverse`: the identity `y'_{t+1} - 2 y'_t = y_{t+1}` of Remark 8.42.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology Cardinal

namespace PVG
namespace Q95

lemma principal_of_not_free (U : Ultrafilter ℕ) (h : ¬ Free U) : ∃ n, U = pure n := by
  unfold Free at h
  rw [Filter.le_def] at h
  push Not at h
  obtain ⟨s, hs, hsU⟩ := h
  have hfin : sᶜ.Finite := Filter.mem_cofinite.1 hs
  have hmem : sᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.2 hsU
  obtain ⟨n, _, hn⟩ := Ultrafilter.eq_pure_of_finite_mem hfin hmem
  exact ⟨n, hn⟩

/-- There are `2^𝔠` free ultrafilters on `ℕ`. -/
theorem card_free_ultra : #{U : Ultrafilter ℕ // Free U} = 2 ^ #ℝ := by
  classical
  have hU : #(Ultrafilter ℕ) = 2 ^ #ℝ := by
    rw [Cardinal.mk_ultrafilter_of_infinite, Cardinal.mk_nat, Cardinal.two_power_aleph0, Cardinal.mk_real]
  have hup : #{U : Ultrafilter ℕ // Free U} ≤ 2 ^ #ℝ := by
    rw [← hU]; exact Cardinal.mk_subtype_le _
  refine le_antisymm hup ?_
  by_contra hlt
  push Not at hlt
  have hcont : ℵ₀ < 2 ^ #ℝ := by
    rw [Cardinal.mk_real]
    exact lt_trans Cardinal.aleph0_lt_continuum (Cardinal.cantor _)
  have hlt2 : #{U : Ultrafilter ℕ // Free U} + ℵ₀ < 2 ^ #ℝ :=
    Cardinal.add_lt_of_lt hcont.le hlt hcont
  let f : Ultrafilter ℕ → {U : Ultrafilter ℕ // Free U} ⊕ ℕ := fun U =>
    if h : Free U then Sum.inl ⟨U, h⟩ else Sum.inr (Classical.choose (principal_of_not_free U h))
  have hf : Function.Injective f := by
    intro U V hUV
    by_cases hu : Free U <;> by_cases hv : Free V
    · simp only [f, dif_pos hu, dif_pos hv] at hUV
      exact congrArg Subtype.val (Sum.inl_injective hUV)
    · simp [f, dif_pos hu, dif_neg hv] at hUV
    · simp [f, dif_neg hu, dif_pos hv] at hUV
    · simp only [f, dif_neg hu, dif_neg hv] at hUV
      have h1 := Classical.choose_spec (principal_of_not_free U hu)
      have h2 := Classical.choose_spec (principal_of_not_free V hv)
      rw [h1, h2]
      exact congrArg pure (Sum.inr_injective hUV)
  have := Cardinal.mk_le_of_injective hf
  rw [hU, Cardinal.mk_sum] at this
  simp at this
  exact absurd (lt_of_le_of_lt this hlt2) (lt_irrefl _)

/-- `#K ≤ 2^𝔠`. -/
lemma card_K_le : #K ≤ 2 ^ #ℝ := by
  have h1 : #K ≤ #(ℝ → AddCircle (1 : ℝ)) :=
    Cardinal.mk_le_of_injective (f := fun κ : K => (κ : ℝ → AddCircle (1 : ℝ))) DFunLike.coe_injective
  have h2 : #(AddCircle (1 : ℝ)) ≤ #ℝ :=
    Cardinal.mk_le_of_surjective (f := ((↑) : ℝ → AddCircle (1 : ℝ))) QuotientAddGroup.mk_surjective
  have h3 : #(ℝ → AddCircle (1 : ℝ)) = #(AddCircle (1 : ℝ)) ^ #ℝ := by
    rw [Cardinal.mk_arrow]; simp
  have hinf : ℵ₀ ≤ #ℝ := by rw [Cardinal.mk_real]; exact Cardinal.aleph0_le_continuum
  calc #K ≤ #(ℝ → AddCircle (1 : ℝ)) := h1
    _ = #(AddCircle (1 : ℝ)) ^ #ℝ := h3
    _ ≤ #ℝ ^ #ℝ := Cardinal.power_le_power_right h2
    _ = 2 ^ #ℝ := Cardinal.power_self_eq hinf

/-- The limits `L_y(U)` of a lacunary sequence along free ultrafilters are pairwise different. -/
lemma injective_L_lac : Function.Injective (fun U : {U : Ultrafilter ℕ // Free U} => L (fun k => (4 : ℝ) ^ k) U.1) := by
  intro U V h
  by_contra hne
  have hne' : U.1 ≠ V.1 := fun h' => hne (Subtype.ext h')
  have h0 : (fun k : ℕ => (4 : ℝ) ^ k) 0 ≠ 0 := by simp
  have hr : ∀ k, 4 * |(fun k : ℕ => (4 : ℝ) ^ k) k| ≤ |(fun k : ℕ => (4 : ℝ) ^ k) (k + 1)| := by
    intro k; simp [pow_succ, abs_of_pos, mul_comm]
  have := L_sub_ne_e _ h0 hr U.2 V.2 hne' 0
  apply this
  simp only at h
  rw [h, sub_self, e_zero]

/-- **`#K = 2^𝔠`.** -/
theorem card_K : #K = 2 ^ #ℝ := by
  refine le_antisymm card_K_le ?_
  rw [← card_free_ultra]
  exact Cardinal.mk_le_of_injective injective_L_lac

/-- **`dim_ℝ K = 2^𝔠`** (Lemma 8.26(c)). -/
theorem rank_K : Module.rank ℝ K = 2 ^ #ℝ := rank_eq_of_card K card_K

/-! ### Convergent sequences below the Bohr topology -/

/-- **Proposition 8.28(a).** A bounded sequence converging for a Hausdorff PVG coarser than the Bohr topology converges in the
Euclidean topology to the same limit. -/
theorem seqG_bounded {conv : Filter ℝ → ℝ → Prop} (hp : IsPVG conv) (hH : PHausdorff conv)
    (hc : ∀ F x, bohrConv F x → conv F x) (a : ℕ → ℝ) (x : ℝ) (hb : ∃ M, ∀ n, |a n| ≤ M)
    (h : conv (Filter.map a Filter.atTop) x) : Tendsto a atTop (𝓝 x) := by
  obtain ⟨M, hM⟩ := hb
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  have hbd : ∀ n, a (ns n) ∈ Set.Icc (-M) M := fun n => abs_le.1 (hM (ns n))
  obtain ⟨y, _, ms, hms, hlim⟩ := (isCompact_Icc (a := -M) (b := M)).tendsto_subseq hbd
  refine ⟨ms, ?_⟩
  have hy : y = x := by
    have hsub : Filter.map (fun n => a (ns (ms n))) Filter.atTop ≤ Filter.map a Filter.atTop := by
      have h1 : Filter.map (fun n => ns (ms n)) Filter.atTop ≤ Filter.atTop := hns.comp hms.tendsto_atTop
      have h2 := Filter.map_mono (m := a) h1
      rw [Filter.map_map] at h2
      exact h2
    have hconvx : conv (Filter.map (fun n => a (ns (ms n))) Filter.atTop) x := hp.p2 h hsub
    have hbohr : bohrConv (Filter.map (fun n => a (ns (ms n))) Filter.atTop) y := by
      unfold bohrConv
      rw [Filter.tendsto_map'_iff]
      exact (continuous_e.tendsto y).comp hlim
    have hconvy := hc _ _ hbohr
    haveI : (Filter.map (fun n => a (ns (ms n))) Filter.atTop).NeBot := Filter.map_neBot
    exact hH _ y x hconvy hconvx
  rw [← hy]
  exact hlim

/-- **Proposition 8.28(b).** If an unbounded sequence converges for `η_G`, then `dim_ℝ G = 2^𝔠`. -/
theorem seqG_unbounded (G : Submodule ℝ K) (a : ℕ → ℝ) (x : ℝ) (hunb : ∀ M : ℝ, ∃ k, M < |a k|)
    (h : etaConv G (Filter.map a Filter.atTop) x) : Module.rank ℝ G = 2 ^ #ℝ := by
  obtain ⟨φ, hφ, h0, hr⟩ := exists_lacunary_subseq a hunb
  set y : ℕ → ℝ := fun k => a (φ k) with hy
  have hmem : ∀ V : {V : Ultrafilter ℕ // Free V}, L y V.1 - e x ∈ G := by
    intro V
    have hVle : (V.1 : Filter ℕ) ≤ Filter.atTop := (free_iff_le_atTop V.1).1 V.2
    have hT : ((Ultrafilter.map y V.1 : Ultrafilter ℝ) : Filter ℝ) ≤ Filter.map a Filter.atTop := by
      rw [Ultrafilter.coe_map]
      have h1 : Filter.map φ Filter.atTop ≤ Filter.atTop := hφ.tendsto_atTop
      have h2 := Filter.map_mono (m := a) h1
      rw [Filter.map_map] at h2
      calc Filter.map y (V.1 : Filter ℕ) ≤ Filter.map y Filter.atTop := Filter.map_mono hVle
        _ ≤ Filter.map a Filter.atTop := h2
    have := h _ hT
    rwa [Lr_map] at this
  let g : {V : Ultrafilter ℕ // Free V} → G := fun V => ⟨L y V.1 - e x, hmem V⟩
  have hinj : Function.Injective g := by
    intro V W hVW
    have h1 : L y V.1 - e x = L y W.1 - e x := congrArg Subtype.val hVW
    have h2 : L y V.1 = L y W.1 := sub_left_injective h1
    by_contra hne
    have hne' : V.1 ≠ W.1 := fun h' => hne (Subtype.ext h')
    exact L_sub_ne_e y h0 hr V.2 W.2 hne' 0 (by rw [h2, sub_self, e_zero])
  have hle : 2 ^ #ℝ ≤ #G := by
    rw [← card_free_ultra]; exact Cardinal.mk_le_of_injective hinj
  have hge : #G ≤ 2 ^ #ℝ := by
    rw [← card_K]; exact Cardinal.mk_le_of_injective Subtype.val_injective
  exact rank_eq_of_card G (le_antisymm hge hle)

/-! ### The family of minimal Hausdorff PVGs (Corollary 8.27(c)) -/

/-- There are exactly `2^(2^𝔠)` real linear maps `π : K → ℝ` with `π (e 1) = 1`. -/
theorem card_retractions_K : #{π : K →ₗ[ℝ] ℝ // π (e 1) = 1} = (2 : Cardinal.{0}) ^ ((2 : Cardinal.{0}) ^ #ℝ) :=
  card_retractions e_one_ne_zero rank_K

/-- There are exactly `2^(2^𝔠)` complements of the line `ℝ e(1)` in `K`, hence `2^(2^𝔠)` minimal Hausdorff PVGs below the Bohr
topology. -/
theorem card_minimal : #{H : Submodule ℝ K // IsCompl (ℝ ∙ e 1) H} = (2 : Cardinal.{0}) ^ ((2 : Cardinal.{0}) ^ #ℝ) := by
  rw [Cardinal.mk_congr (retractionEquiv (e1 := e 1) e_one_ne_zero)]
  exact card_retractions_K

/-- The minimal PVGs `η_{ker π}` are pairwise incomparable. -/
theorem minimal_antichain (hdense : DenseRange e) (π π' : K →ₗ[ℝ] ℝ) (h1 : π (e 1) = 1) (h1' : π' (e 1) = 1)
    (h : ∀ (F : Filter ℝ) (x : ℝ), etaConv (LinearMap.ker π') F x → etaConv (LinearMap.ker π) F x) :
    LinearMap.ker π = LinearMap.ker π' := by
  have hle : LinearMap.ker π' ≤ LinearMap.ker π := (etaConv_le_iff hdense (LinearMap.ker π) (LinearMap.ker π')).1 h
  have hmax := (maximal_admissible_iff (ℝ ∙ e 1) (LinearMap.ker π') (ker_admissible π' h1')).2
    ((ker_isCompl π' h1').symm.codisjoint)
  exact le_antisymm (hmax _ (ker_admissible π h1) hle) hle

/-! ### The identity of Remark 8.42 -/

/-- For `y'_t = ∑_{s ≤ t} 2^(t-s) y_s` one has `y'_{t+1} - 2 y'_t = y_{t+1}`. -/
theorem block_sum_inverse (y : ℕ → ℝ) (t : ℕ) :
    (∑ s ∈ Finset.range (t + 2), (2 : ℝ) ^ (t + 1 - s) * y s) - 2 * (∑ s ∈ Finset.range (t + 1), (2 : ℝ) ^ (t - s) * y s) =
      y (t + 1) := by
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have h : ∀ s ∈ Finset.range (t + 1), (2 : ℝ) ^ (t + 1 - s) * y s = 2 * ((2 : ℝ) ^ (t - s) * y s) := by
    intro s hs
    have hst : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
    rw [show t + 1 - s = (t - s) + 1 by omega, pow_succ]; ring
  rw [Finset.sum_congr rfl h]
  simp

#print axioms card_free_ultra
#print axioms card_K
#print axioms rank_K
#print axioms seqG_bounded
#print axioms seqG_unbounded
#print axioms card_retractions_K
#print axioms card_minimal
#print axioms minimal_antichain
#print axioms block_sum_inverse

end Q95
end PVG
