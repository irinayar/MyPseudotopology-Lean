import Mathlib
import LeanCheck.PVGTwoDimension
import LeanCheck.PVGTotBdd

/-!
# PVGtwo, Section 5: condition (N) fails (Lean check)

Scope. A group topology on `ℝ` that is coarser than the usual one and not precompact can make `aT` totally bounded, for an
unbounded set `T`, only for `a` in a Lebesgue-null countable union of closed sets.

* `null_cover` : the statement, for a filter `N` of neighbourhoods of `0` (only `V + V ⊆ W`, symmetry and "coarser than
  Euclidean" are used);
* `tb_of_dilates` : if `aT` is totally bounded for every `a`, then `ℝ` is totally bounded;
* `group_null_cover`, `group_tb_of_dilates` : the same for a group topology `γ`;
* `trace_null` : for a non-precompact group topology the `a` for which `γ` induces on `J_a` the Bohr topology lie in such a set;
* `no_witness` : a group topology coarser than the usual one that induces the Bohr topology on every `J_a` is precompact;
* `Agroup_null` : the group `A(δ)` of the dimension theorem is contained in such a null set.

Not formalized here: the classical fact that a precompact group topology is the initial topology of its continuous characters,
which turns `no_witness` into "`γ` is contained in the Bohr topology" (so condition (N) fails).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set MeasureTheory
open scoped Pointwise

namespace PVG
namespace Two
open Q95 Lac

/-- Closed for the usual topology, named outside the scope of any variable topology on `ℝ`. -/
def EClosed (s : Set ℝ) : Prop := IsClosed s

/-- `Y` is totally bounded for the neighbourhood filter `N` of `0`. -/
def Tb (N : Filter ℝ) (Y : Set ℝ) : Prop := ∀ V ∈ N, ∃ F : Finset ℝ, ∀ y ∈ Y, ∃ f ∈ F, y - f ∈ V

/-- The dilate `aT`. -/
def dil (a : ℝ) (T : Set ℝ) : Set ℝ := (fun t => a * t) '' T

/-- Three halvings: a symmetric member whose eightfold sums lie in `W`. -/
lemma eight (N : Filter ℝ) (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (W : Set ℝ) (hW : W ∈ N) :
    ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧
      ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, ∀ d ∈ V, ∀ e ∈ V, ∀ f ∈ V, ∀ g ∈ V, ∀ h ∈ V,
        ((a + b) + (c + d)) + ((e + f) + (g + h)) ∈ W := by
  obtain ⟨V1, h1, _, a1⟩ := hhalf W hW
  obtain ⟨V2, h2, _, a2⟩ := hhalf V1 h1
  obtain ⟨V3, h3, s3, a3⟩ := hhalf V2 h2
  exact ⟨V3, h3, s3, fun a ha b hb c hc d hd e he f hf g hg h hh =>
    a1 _ (a2 _ (a3 a ha b hb) _ (a3 c hc d hd)) _ (a2 _ (a3 e he f hf) _ (a3 g hg h hh))⟩

/-- The main statement. -/
theorem null_cover (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : 𝓝 (0 : ℝ) ≤ N) (T : Set ℝ) (hT : ∀ M : ℝ, ∃ t ∈ T, M < |t|)
    (W : Set ℝ) (hW : W ∈ N) (hnp : ∀ F : Finset ℝ, ∃ x : ℝ, ∀ f ∈ F, x - f ∉ W) :
    ∃ C : Finset ℤ → Set ℝ, (∀ G, IsClosed (C G)) ∧ (∀ G, volume (C G) = 0) ∧
      {a : ℝ | Tb N (dil a T)} ⊆ ⋃ G, C G := by
  obtain ⟨V, hVN, hsym, hsum⟩ := eight N hhalf W hW
  have hV : V ∈ 𝓝 (0 : ℝ) := heu hVN
  have h0 : (0 : ℝ) ∈ V := mem_of_mem_nhds hV
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hsmall : ∀ x : ℝ, |x| < η → x ∈ V := fun x hx => hball (by simpa [Real.dist_eq] using hx)
  set S : Finset ℤ → Set ℝ :=
    fun G => {a | ∀ t ∈ T, ∃ k ∈ G, ∃ u ∈ V, ∃ v ∈ V, a * t - η * (k : ℝ) = u + v} with hS
  have hprop : ∀ G, ∀ a ∈ closure (S G), ∀ t ∈ T, ∃ k ∈ G, ∃ u ∈ V, ∃ v ∈ V, ∃ w ∈ V,
      a * t - η * (k : ℝ) = u + v + w := by
    intro G a ha t ht
    have hpos : 0 < η / (|t| + 1) := div_pos hη (by positivity)
    obtain ⟨a', ha', hd⟩ := Metric.mem_closure_iff.1 ha _ hpos
    obtain ⟨k, hk, u, hu, v, hv, he⟩ := ha' t ht
    have hw : (a - a') * t ∈ V := by
      refine hsmall _ ?_
      rw [Real.dist_eq] at hd
      rw [abs_mul]
      have h1 : |a - a'| * |t| ≤ η / (|t| + 1) * |t| := mul_le_mul_of_nonneg_right hd.le (abs_nonneg _)
      have h2 : η / (|t| + 1) * |t| < η := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg t]
      linarith
    refine ⟨k, hk, u, hu, v, hv, (a - a') * t, hw, ?_⟩
    linear_combination he
  refine ⟨fun G => closure (S G), fun G => isClosed_closure, ?_, ?_⟩
  · intro G
    show volume (closure (S G)) = 0
    by_contra hne
    have hst : closure (S G) - closure (S G) ∈ 𝓝 (0 : ℝ) :=
      MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos volume _ isClosed_closure.measurableSet
        (pos_iff_ne_zero.2 hne)
    obtain ⟨ℓ, hℓ, hℓball⟩ := Metric.mem_nhds_iff.1 hst
    obtain ⟨x, hx⟩ := hnp ((G ×ˢ G).image (fun p : ℤ × ℤ => η * (p.1 : ℝ) - η * (p.2 : ℝ)))
    obtain ⟨t, ht, htx⟩ := hT (|x| / ℓ)
    have htpos : 0 < |t| := lt_of_le_of_lt (div_nonneg (abs_nonneg _) hℓ.le) htx
    have ht0 : t ≠ 0 := abs_pos.1 htpos
    have hxt : x / t ∈ Metric.ball (0 : ℝ) ℓ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_div, div_lt_iff₀ htpos]
      rw [div_lt_iff₀ hℓ] at htx
      linarith [mul_comm |t| ℓ]
    obtain ⟨a, ha, a', ha', haa⟩ := Set.mem_sub.1 (hℓball hxt)
    obtain ⟨k, hk, u, hu, v, hv, w, hw, e1⟩ := hprop G a ha t ht
    obtain ⟨k', hk', u', hu', v', hv', w', hw', e2⟩ := hprop G a' ha' t ht
    have hxe : x = a * t - a' * t := by
      rw [← sub_mul, haa, div_mul_cancel₀ x ht0]
    refine hx (η * (k : ℝ) - η * (k' : ℝ))
      (Finset.mem_image.2 ⟨(k, k'), Finset.mem_product.2 ⟨hk, hk'⟩, rfl⟩) ?_
    have key : x - (η * (k : ℝ) - η * (k' : ℝ)) = ((u + v) + (w + 0)) + ((-u' + -v') + (-w' + 0)) := by
      linear_combination hxe + e1 - e2
    rw [key]
    exact hsum u hu v hv w hw 0 h0 _ (hsym _ hu') _ (hsym _ hv') _ (hsym _ hw') 0 h0
  · intro a ha
    obtain ⟨F, hF⟩ := ha V hVN
    refine mem_iUnion.2 ⟨F.image (fun f => round (f / η)), subset_closure ?_⟩
    intro t ht
    obtain ⟨f, hf, hfV⟩ := hF (a * t) ⟨t, ht, rfl⟩
    refine ⟨round (f / η), Finset.mem_image_of_mem _ hf, a * t - f, hfV,
      f - η * (round (f / η) : ℝ), hsmall _ ?_, by ring⟩
    have h1 : f - η * (round (f / η) : ℝ) = η * (f / η - round (f / η)) := by
      field_simp
    rw [h1, abs_mul, abs_of_pos hη]
    have h2 := abs_sub_round (f / η)
    calc η * |f / η - round (f / η)| ≤ η * (1 / 2) := mul_le_mul_of_nonneg_left h2 hη.le
      _ < η := by linarith

/-- If `aT` is totally bounded for every `a`, then `ℝ` is totally bounded. -/
theorem tb_of_dilates (N : Filter ℝ)
    (hhalf : ∀ W ∈ N, ∃ V ∈ N, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W)
    (heu : 𝓝 (0 : ℝ) ≤ N) (T : Set ℝ) (hT : ∀ M : ℝ, ∃ t ∈ T, M < |t|)
    (h : ∀ a : ℝ, Tb N (dil a T)) : ∀ W ∈ N, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W := by
  intro W hW
  by_contra hcon
  have hnp : ∀ F : Finset ℝ, ∃ x : ℝ, ∀ f ∈ F, x - f ∉ W := by
    intro F
    by_contra h'
    refine hcon ⟨F, fun x => ?_⟩
    by_contra h''
    exact h' ⟨x, fun f hf hfW => h'' ⟨f, hf, hfW⟩⟩
  obtain ⟨C, _, hnull, hsub⟩ := null_cover N hhalf heu T hT W hW hnp
  have huniv : volume (univ : Set ℝ) = 0 :=
    measure_mono_null (fun a _ => hsub (h a)) (measure_iUnion_null hnull)
  rw [Real.volume_univ] at huniv
  exact ENNReal.top_ne_zero huniv

/-- The halving property of a group topology. -/
lemma group_half (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _) :
    ∀ W ∈ @nhds ℝ γ 0, ∃ V ∈ @nhds ℝ γ 0, (∀ x ∈ V, -x ∈ V) ∧ ∀ x ∈ V, ∀ y ∈ V, x + y ∈ W := by
  letI : TopologicalSpace ℝ := γ
  haveI : IsTopologicalAddGroup ℝ := hg
  intro W hW
  obtain ⟨V, hV, h⟩ := exists_nhds_zero_half hW
  refine ⟨V ∩ -V, inter_mem hV (neg_mem_nhds_zero ℝ hV), fun x hx => ?_, fun x hx y hy => h x hx.1 y hy.1⟩
  exact ⟨hx.2, by simpa using hx.1⟩

lemma Sset_unbounded : ∀ M : ℝ, ∃ t ∈ Sset, M < |t| := by
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt M
  refine ⟨sS (n + 1), sS_mem_Sset (by omega), ?_⟩
  have h1 : (n : ℝ) < sS (n + 1) := by
    unfold sS
    have h2 : n < 2 ^ ((n + 1) ^ 2) :=
      lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
    exact_mod_cast h2
  exact hn.trans (h1.trans_le (le_abs_self _))

/-- `null_cover` for a group topology. -/
theorem group_null_cover (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (T : Set ℝ) (hT : ∀ M : ℝ, ∃ t ∈ T, M < |t|)
    (hnp : ¬ ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W) :
    ∃ C : Finset ℤ → Set ℝ, (∀ G, EClosed (C G)) ∧ (∀ G, volume (C G) = 0) ∧
      {a : ℝ | Tb (@nhds ℝ γ 0) (dil a T)} ⊆ ⋃ G, C G := by
  by_cases h : ∃ W ∈ @nhds ℝ γ 0, ∀ F : Finset ℝ, ∃ x : ℝ, ∀ f ∈ F, x - f ∉ W
  · obtain ⟨W, hW, hW'⟩ := h
    exact null_cover _ (group_half γ hg) heu T hT W hW hW'
  · refine absurd (fun W hW => ?_) hnp
    by_contra hcon
    refine h ⟨W, hW, fun F => ?_⟩
    by_contra h'
    refine hcon ⟨F, fun x => ?_⟩
    by_contra h''
    exact h' ⟨x, fun f hf hfW => h'' ⟨f, hf, hfW⟩⟩

/-- `tb_of_dilates` for a group topology. -/
theorem group_tb_of_dilates (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (T : Set ℝ) (hT : ∀ M : ℝ, ∃ t ∈ T, M < |t|)
    (h : ∀ a : ℝ, Tb (@nhds ℝ γ 0) (dil a T)) :
    ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W :=
  tb_of_dilates _ (group_half γ hg) heu T hT h

/-- The Bohr trace on `J_a` makes `aS` totally bounded. -/
lemma tb_of_trace (γ : TopologicalSpace ℝ) (a : ℝ)
    (hind : TopologicalSpace.induced (Subtype.val : Ja a → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Ja a → ℝ) bohrTop) : Tb (@nhds ℝ γ 0) (dil a Sset) := by
  intro W hW
  obtain ⟨F, hF⟩ := totbdd γ a hind W hW
  refine ⟨F, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  exact hF s hs

/-- For a non-precompact group topology the Bohr trace on `J_a` holds only for `a` in a null set. -/
theorem trace_null (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0)
    (hnp : ¬ ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W) :
    ∃ C : Finset ℤ → Set ℝ, (∀ G, EClosed (C G)) ∧ (∀ G, volume (C G) = 0) ∧
      {a : ℝ | TopologicalSpace.induced (Subtype.val : Ja a → ℝ) γ =
        TopologicalSpace.induced (Subtype.val : Ja a → ℝ) bohrTop} ⊆ ⋃ G, C G := by
  obtain ⟨C, hc, hn, hsub⟩ := group_null_cover γ hg heu Sset Sset_unbounded hnp
  exact ⟨C, hc, hn, fun a ha => hsub (tb_of_trace γ a ha)⟩

/-- A group topology coarser than the usual one with the Bohr trace on every `J_a` is precompact. -/
theorem no_witness (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0)
    (htr : ∀ a : ℝ, TopologicalSpace.induced (Subtype.val : Ja a → ℝ) γ =
      TopologicalSpace.induced (Subtype.val : Ja a → ℝ) bohrTop) :
    ∀ W ∈ @nhds ℝ γ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W :=
  group_tb_of_dilates γ hg heu Sset Sset_unbounded fun a => tb_of_trace γ a (htr a)

/-- The group `A(δ)` of the dimension theorem is a subset of a null countable union of closed sets. -/
theorem Agroup_null : ∃ C : Finset ℤ → Set ℝ, (∀ G, EClosed (C G)) ∧ (∀ G, volume (C G) = 0) ∧
    {a : ℝ | a ∈ Agroup} ⊆ ⋃ G, C G := by
  have hinf := infinite_range_of_tendsto dlt (fun k => (dlt_pos k).ne') dlt_tendsto
  have hM : ∀ k, |dlt k| ≤ 1 := by
    intro k
    rw [abs_of_pos (dlt_pos k)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hnp : ¬ ∀ W ∈ @nhds ℝ (gamTop dlt) 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W :=
    gam_not_precompact dlt hinf
  obtain ⟨C, hc, hn, hsub⟩ := group_null_cover (gamTop dlt) (gam_group dlt)
    (gam_coarser_euclid dlt 1 hM 0) Sset Sset_unbounded hnp
  refine ⟨C, hc, hn, fun a ha => hsub ?_⟩
  intro W hW
  obtain ⟨F, hF⟩ := dilates_totally_bounded a ha W hW
  refine ⟨F, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  exact hF s hs

end Two
end PVG
