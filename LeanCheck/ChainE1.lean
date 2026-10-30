import LeanCheck.ChainD7

/-!
# Maximal nondiscrete TVG topologies (the elementary part), and torsion-freeness of `Hom(ℚ, 𝕋)`
(HamelCharactersTVG_v18 §17: Lemma 17.1 (countable neighbourhoods), Lemma 17.2 (`lem:joins`), the Zorn part of
 Theorem 17.3 (`thm:maximal`); Lemma 21.3 `lem:roots-v8`)

* `discrete_of_countable_nhd`   : a TVG topology on `ℝ` with a countable zero-neighbourhood is discrete;
* `join_usual_nondiscrete`, `join_precompact_nondiscrete` : joins of a nondiscrete topology with the usual topology or
                                  with a precompact one are nondiscrete;
* `exists_maximal_nondiscrete`  : every Hausdorff nondiscrete TVG topology has a maximal such extension (Zorn);
                                  every maximal member is finer than the usual topology and than the Bohr topology of the
                                  discrete line, so all algebraic characters are continuous for it;
* `torsionfree_Q`, `torsionfree_Hf` : if `m ψ ∈ Γ` (resp. `∈ H_f`) then `ψ ∈ Γ` (resp. `∈ H_f`).
(Glicksberg's theorem, used in the paper for "compact subsets are finite", is not formalized.)
-/

namespace LeanCheck

open Filter Topology

section Countable

/-- A subset of `ℝ` whose distinct points are at distance `≥ δ` is countable. -/
lemma countable_of_separated (W : Set ℝ) (δ : ℝ) (hδ : 0 < δ) (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → δ ≤ |x - y|) :
    W.Countable := by
  have hinj : Set.InjOn (fun x : ℝ => ⌊2 * x / δ⌋) W := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hsep x hx y hy hne
    have h2 : |2 * x / δ - 2 * y / δ| < 1 := by
      have a1 := Int.floor_le (2 * x / δ)
      have a2 := Int.lt_floor_add_one (2 * x / δ)
      have b1 := Int.floor_le (2 * y / δ)
      have b2 := Int.lt_floor_add_one (2 * y / δ)
      have hc : ((⌊2 * x / δ⌋ : ℤ) : ℝ) = ((⌊2 * y / δ⌋ : ℤ) : ℝ) := by
        have hxy' : ⌊2 * x / δ⌋ = ⌊2 * y / δ⌋ := hxy
        rw [hxy']
      rw [abs_lt]
      constructor <;> linarith
    have h3 : 2 * x / δ - 2 * y / δ = 2 * (x - y) / δ := by ring
    rw [h3, abs_div, abs_mul, abs_of_pos hδ, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      div_lt_one hδ] at h2
    linarith
  exact Set.MapsTo.countable_of_injOn (f := fun x : ℝ => ⌊2 * x / δ⌋) (t := (Set.univ : Set ℤ))
    (fun _ _ => Set.mem_univ _) hinj Set.countable_univ

/-- Hausdorff TVG topologies on `ℝ`. -/
def TVGcls : Set (TopologicalSpace ℝ) :=
  {η | @IsTopologicalAddGroup ℝ η _ ∧ @T2Space ℝ η ∧ ∀ a : ℝ, Continuous[η, η] (fun x : ℝ => a * x)}

/-- Hausdorff nondiscrete TVG topologies on `ℝ`. -/
def NDcls : Set (TopologicalSpace ℝ) := {η | η ∈ TVGcls ∧ ({0} : Set ℝ) ∉ @nhds ℝ η 0}

/-- **Lemma 17.1.**  A TVG topology on `ℝ` with a countable zero-neighbourhood is discrete. -/
theorem discrete_of_countable_nhd (η : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ η _)
    (hdil : ∀ a : ℝ, Continuous[η, η] (fun x : ℝ => a * x)) (V : Set ℝ) (hV : V ∈ @nhds ℝ η 0)
    (hc : V.Countable) : ({0} : Set ℝ) ∈ @nhds ℝ η 0 := by
  letI := η
  haveI := hg
  haveI : Countable V := hc.to_subtype
  set E : Submodule ℚ ℝ := Submodule.span ℚ V with hE
  have hEc : (E : Set ℝ).Countable := by
    have h1 : Countable (Submodule.span ℚ (Set.range (Subtype.val : V → ℝ))) := inferInstance
    rw [Subtype.range_coe] at h1
    exact Set.countable_coe_iff.1 h1
  have hEmem : (E : Set ℝ) ∈ 𝓝 (0 : ℝ) := Filter.mem_of_superset hV (Submodule.subset_span)
  have hEopen : IsOpen (E : Set ℝ) := by
    have := AddSubgroup.isOpen_of_mem_nhds E.toAddSubgroup hEmem
    exact this
  -- a scalar outside the countable set of ratios
  have hR : (Set.image2 (fun h k : ℝ => h / k) (E : Set ℝ) (E : Set ℝ)).Countable := hEc.image2 hEc _
  obtain ⟨a, haR, ha0⟩ : ∃ a : ℝ, a ∉ Set.image2 (fun h k : ℝ => h / k) (E : Set ℝ) (E : Set ℝ) ∧ a ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsub : (Set.univ : Set ℝ) ⊆ Set.image2 (fun h k : ℝ => h / k) (E : Set ℝ) (E : Set ℝ) ∪ {0} := by
      intro x _
      by_cases hx : x ∈ Set.image2 (fun h k : ℝ => h / k) (E : Set ℝ) (E : Set ℝ)
      · exact Or.inl hx
      · exact Or.inr (hall x hx)
    exact Cardinal.not_countable_real ((hR.union (Set.countable_singleton 0)).mono hsub)
  have hAopen : IsOpen {x : ℝ | a⁻¹ * x ∈ (E : Set ℝ)} := hEopen.preimage (hdil a⁻¹)
  have hset : ({0} : Set ℝ) = (E : Set ℝ) ∩ {x : ℝ | a⁻¹ * x ∈ (E : Set ℝ)} := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro rfl
      exact ⟨E.zero_mem, by simpa using E.zero_mem⟩
    · rintro ⟨hx, hy⟩
      by_contra hne
      have hy0 : a⁻¹ * x ≠ 0 := mul_ne_zero (inv_ne_zero ha0) hne
      apply haR
      exact ⟨x, hx, a⁻¹ * x, hy, by field_simp⟩
  rw [hset]
  exact (hEopen.inter hAopen).mem_nhds ⟨E.zero_mem, by simpa using E.zero_mem⟩

end Countable

section Joins

lemma uR_group : @IsTopologicalAddGroup ℝ uR _ := by unfold uR; infer_instance

lemma uR_dil (a : ℝ) : Continuous[uR, uR] (fun x : ℝ => a * x) := by
  unfold uR; exact continuous_const.mul continuous_id

/-- **Lemma 17.2, first part.**  For a Hausdorff nondiscrete TVG topology `η`, `η ∨ tu` is nondiscrete. -/
theorem join_usual_nondiscrete (η : TopologicalSpace ℝ) (hη : η ∈ NDcls) :
    ({0} : Set ℝ) ∉ @nhds ℝ (η ⊓ uR) 0 := by
  intro h
  rw [@nhds_inf ℝ η uR 0] at h
  obtain ⟨U, hU, S, hS, hUS⟩ := Filter.mem_inf_iff.1 h
  unfold uR at hS
  obtain ⟨δ, hδ, hball⟩ := (Metric.mem_nhds_iff (α := ℝ)).1 hS
  have hg := hη.1.1
  obtain ⟨V, hV, hVU⟩ := @exists_nhds_zero_half ℝ η _ _ U hU
  letI := η
  haveI := hg
  set W : Set ℝ := V ∩ (fun x : ℝ => -x) ⁻¹' V with hW
  have hWmem : W ∈ @nhds ℝ η 0 := by
    refine Filter.inter_mem hV ?_
    exact continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV)
  have hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hxy
    by_contra hlt
    push Not at hlt
    have h1 : x - y ∈ U := by
      have := hVU x hx.1 (-y) hy.2
      simpa [sub_eq_add_neg] using this
    have h2 : x - y ∈ S := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      simpa using hlt)
    have h3 : x - y ∈ ({0} : Set ℝ) := by rw [hUS]; exact ⟨h1, h2⟩
    exact hxy (sub_eq_zero.1 h3)
  have hcount : W.Countable := countable_of_separated W δ hδ hsep
  exact hη.2 (discrete_of_countable_nhd η hg hη.1.2.2 W hWmem hcount)

/-- **Lemma 17.2, second part.**  For a Hausdorff nondiscrete topology `η` and a precompact group topology `π`,
`η ∨ π` is nondiscrete. -/
theorem join_precompact_nondiscrete (η π : TopologicalSpace ℝ) (hη : η ∈ NDcls)
    (hπg : @IsTopologicalAddGroup ℝ π _) (hπ : Precompact π) :
    ({0} : Set ℝ) ∉ @nhds ℝ (η ⊓ π) 0 := by
  intro h
  rw [@nhds_inf ℝ η π 0] at h
  obtain ⟨U, hU, V', hV', hUV⟩ := Filter.mem_inf_iff.1 h
  have hg := hη.1.1
  obtain ⟨W1, hW1, hW1U⟩ := @exists_nhds_zero_half ℝ η _ _ U hU
  obtain ⟨Z1, hZ1, hZ1V⟩ := @exists_nhds_zero_half ℝ π _ _ V' hV'
  have hWmem : (W1 ∩ (fun x : ℝ => -x) ⁻¹' W1) ∈ @nhds ℝ η 0 := by
    letI := η; haveI := hg
    refine Filter.inter_mem hW1 ?_
    exact continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hW1)
  have hZmem : (Z1 ∩ (fun x : ℝ => -x) ⁻¹' Z1) ∈ @nhds ℝ π 0 := by
    letI := π; haveI := hπg
    refine Filter.inter_mem hZ1 ?_
    exact continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hZ1)
  set W : Set ℝ := W1 ∩ (fun x : ℝ => -x) ⁻¹' W1 with hW
  set Z : Set ℝ := Z1 ∩ (fun x : ℝ => -x) ⁻¹' Z1 with hZ
  obtain ⟨F, hF⟩ := hπ Z hZmem
  choose! t ht using hF
  have hinj : Set.InjOn t W := by
    intro x hx y hy hxy
    have h1 : x - y ∈ U := by
      have := hW1U x hx.1 (-y) hy.2
      simpa [sub_eq_add_neg] using this
    have h2 : x - y ∈ V' := by
      have hx' : x - t x ∈ Z := (ht x).2
      have hy' : y - t y ∈ Z := (ht y).2
      have := hZ1V (x - t x) hx'.1 (-(y - t y)) hy'.2
      have e : x - t x + -(y - t y) = x - y := by rw [hxy]; ring
      rwa [e] at this
    have h3 : x - y ∈ ({0} : Set ℝ) := by rw [hUV]; exact ⟨h1, h2⟩
    exact sub_eq_zero.1 h3
  have hWfin : W.Finite := by
    refine Set.Finite.of_injOn (f := t) (t := (F : Set ℝ)) (fun x _ => ?_) hinj F.finite_toSet
    exact (ht x).1
  -- a finite neighbourhood of `0` in a `T1` group gives `{0} ∈ 𝓝 0`
  letI := η
  haveI := hη.1.2.1
  have hcl : IsClosed (W \ {0}) := (hWfin.diff).isClosed
  have hmem : ({0} : Set ℝ) ∈ 𝓝 (0 : ℝ) := by
    refine Filter.mem_of_superset (Filter.inter_mem hWmem (hcl.isOpen_compl.mem_nhds (by simp))) ?_
    intro x hx
    by_contra hne
    exact hx.2 ⟨hx.1, hne⟩
  exact hη.2 hmem

end Joins

section Maximal

lemma NDcls_iInf {ι : Type*} [Nonempty ι] (τ : ι → TopologicalSpace ℝ) (hdir : Directed (· ≥ ·) τ)
    (hτ : ∀ i, τ i ∈ NDcls) : (⨅ i, τ i) ∈ NDcls := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  refine ⟨⟨isTopologicalAddGroup_iInf (fun i => (hτ i).1.1), t2_of_le' (iInf_le τ i0) (hτ i0).1.2.1,
    fun a => dil_iInf τ _ (fun i => (hτ i).1.2.2 a)⟩, ?_⟩
  intro h
  rw [nhds_iInf] at h
  have hdirF : Directed (· ≥ ·) (fun i => @nhds ℝ (τ i) 0) := by
    intro i j
    obtain ⟨k, hk1, hk2⟩ := hdir i j
    exact ⟨k, nhds_mono hk1, nhds_mono hk2⟩
  rw [Filter.mem_iInf_of_directed hdirF] at h
  obtain ⟨k, hk⟩ := h
  exact (hτ k).2 hk

/-- Every Hausdorff nondiscrete TVG topology has a maximal Hausdorff nondiscrete TVG extension. -/
theorem exists_minimal_nd (η : TopologicalSpace ℝ) (hη : η ∈ NDcls) :
    ∃ μ : TopologicalSpace ℝ, μ ≤ η ∧ Minimal (· ∈ NDcls) μ := by
  refine zorn_ge_nonempty₀ NDcls (fun c hcs hc y hy => ?_) η hη
  have hne : Nonempty c := ⟨⟨y, hy⟩⟩
  have hdir : Directed (· ≥ ·) (fun z : c => (z : TopologicalSpace ℝ)) := by
    intro a b
    rcases hc.total a.2 b.2 with h | h
    · exact ⟨b, h, le_rfl⟩
    · exact ⟨a, le_rfl, h⟩
  refine ⟨⨅ z : c, (z : TopologicalSpace ℝ), NDcls_iInf _ hdir (fun z => hcs z.2), ?_⟩
  intro z hz
  exact iInf_le (fun z : c => (z : TopologicalSpace ℝ)) ⟨z, hz⟩

lemma Bohr_separates : Separates (Set.univ : Set Chars) := by
  intro x hx
  refine ⟨scalChar (1 / (2 * x)), Set.mem_univ _, ?_⟩
  rw [scalChar_apply]
  have : (1 / (2 * x) * x : ℝ) = 1 / 2 := by field_simp
  rw [this]
  exact half_ne_zero_circ

/-- **Theorem 17.3 (existence and common properties; the part not using Glicksberg).**  Every Hausdorff nondiscrete
TVG topology has a maximal nondiscrete TVG extension `μ`; every maximal member is finer than the usual topology and
than the Bohr topology of the discrete line, so every algebraic character of `ℝ` is `μ`-continuous. -/
theorem exists_maximal_nondiscrete (η : TopologicalSpace ℝ) (hη : η ∈ NDcls) :
    ∃ μ : TopologicalSpace ℝ, μ ≤ η ∧ Minimal (· ∈ NDcls) μ ∧ μ ≤ uR ∧
      μ ≤ theta (Set.univ : Set Chars) ∧ ∀ χ : Chars, @Continuous ℝ Circ μ circTop χ := by
  obtain ⟨μ, hμη, hμ⟩ := exists_minimal_nd η hη
  have hμnd := hμ.1
  -- `μ ⊓ uR`
  have hu : μ ⊓ uR ∈ NDcls :=
    ⟨⟨isTopologicalAddGroup_inf hμnd.1.1 uR_group, t2_of_le' inf_le_left hμnd.1.2.1,
      fun a => dil_inf μ uR _ (hμnd.1.2.2 a) (uR_dil a)⟩, join_usual_nondiscrete μ hμnd⟩
  have hμu : μ ≤ uR := (hμ.2 hu inf_le_left).trans inf_le_right
  -- `μ ⊓ B`
  have hB := theta_ptvg (Set.univ : Set Chars) Bohr_separates (fun χ _ a => Set.mem_univ _)
  have hBnd : μ ⊓ theta (Set.univ : Set Chars) ∈ NDcls :=
    ⟨⟨isTopologicalAddGroup_inf hμnd.1.1 hB.1, t2_of_le' inf_le_left hμnd.1.2.1,
      fun a => dil_inf μ _ _ (hμnd.1.2.2 a) (hB.2.2.2 a)⟩,
      join_precompact_nondiscrete μ _ hμnd hB.1 hB.2.2.1⟩
  have hμB : μ ≤ theta (Set.univ : Set Chars) := (hμ.2 hBnd inf_le_left).trans inf_le_right
  exact ⟨μ, hμη, hμ, hμu, hμB, fun χ => continuous_le_dom hμB (theta_cont_of_mem _ χ (Set.mem_univ _))⟩

end Maximal

section Torsionfree

/-- **Lemma 21.3, first part** (`ℚ`): `Hom(ℚ, 𝕋)` is torsion-free. -/
lemma torsionfree_zero_Q (m : ℕ) (hm : 0 < m) (ψ : ℚ →+ Circ) (h : ∀ q, m • ψ q = 0) : ∀ q, ψ q = 0 := by
  intro q
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have e : q = m • (q / m) := by rw [nsmul_eq_mul]; field_simp
  conv_lhs => rw [e]
  rw [map_nsmul]
  exact h _

/-- **Lemma 21.3** (`ℚ`): if `m ψ ∈ Γ` then `ψ ∈ Γ`. -/
theorem torsionfree_Q (m : ℕ) (hm : 0 < m) (ψ : ℚ →+ Circ) (h : m • ψ ∈ Gam) : ψ ∈ Gam := by
  obtain ⟨r, hr⟩ := h
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have key : ∀ q, m • (ψ q - rchar (r / m) q) = 0 := by
    intro q
    rw [smul_sub]
    have h1 : m • ψ q = ((r * q : ℚ) : ℝ) := by
      have := hr q
      simpa [AddMonoidHom.nsmul_apply] using this
    have h2 : m • rchar (r / m) q = (((r * q : ℚ) : ℝ) : Circ) := by
      rw [rchar_apply, nsmul_coe_circ]
      congr 1
      push_cast
      field_simp
    rw [h1, h2, sub_self]
  have h0 := torsionfree_zero_Q m hm (ψ - rchar (r / m)) (fun q => by simpa using key q)
  refine ⟨r / m, fun s => ?_⟩
  have := h0 s
  simp only [AddMonoidHom.sub_apply] at this
  rw [sub_eq_zero] at this
  rw [this, rchar_apply]

/-- **Lemma 21.3** (`ℝ`): if `m ψ ∈ H_f` then `ψ ∈ H_f`. -/
theorem torsionfree_Hf (f : ℝ →+ ℚ) (m : ℕ) (hm : 0 < m) (ψ : Chars)
    (h : ∃ c a : ℝ, ∀ x : ℝ, m • ψ x = chiH f c a x) : ∃ c a : ℝ, ∀ x : ℝ, ψ x = chiH f c a x := by
  obtain ⟨c, a, hca⟩ := h
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨c / m, a / m, fun x => ?_⟩
  -- ψ x - chiH ... x is killed by `m`
  have hmul : m • (ψ x - chiH f (c / m) (a / m) x) = 0 := by
    rw [smul_sub, hca x]
    unfold chiH
    rw [nsmul_coe_circ]
    have e : (m : ℝ) * (c / m * x + ((f (a / m * x) : ℚ) : ℝ)) = c * x + ((f (a * x) : ℚ) : ℝ) := by
      have h1 : f (a * x) = m * f (a / m * x) := by
        have := f_natmul f m (a / m * x)
        rw [show (m : ℝ) * (a / m * x) = a * x by field_simp] at this
        exact this
      rw [h1]; push_cast; field_simp
    rw [e, sub_self]
  -- divide by `m` using divisibility of `ℝ`
  have key : ∀ y : ℝ, ψ y - chiH f (c / m) (a / m) y = 0 := by
    intro y
    have hy : y = m • (y / m) := by rw [nsmul_eq_mul]; field_simp
    have hψ : ∀ z, m • (ψ z - chiH f (c / m) (a / m) z) = 0 := by
      intro z
      have hmulz : m • (ψ z - chiH f (c / m) (a / m) z) = 0 := by
        rw [smul_sub, hca z]
        unfold chiH
        rw [nsmul_coe_circ]
        have e : (m : ℝ) * (c / m * z + ((f (a / m * z) : ℚ) : ℝ)) = c * z + ((f (a * z) : ℚ) : ℝ) := by
          have h1 : f (a * z) = m * f (a / m * z) := by
            have := f_natmul f m (a / m * z)
            rw [show (m : ℝ) * (a / m * z) = a * z by field_simp] at this
            exact this
          rw [h1]; push_cast; field_simp
        rw [e, sub_self]
      exact hmulz
    -- ψ - χ is a homomorphism; apply to y = m • (y/m)
    let D : ℝ →+ Circ := ψ - (AddMonoidHom.mk' (fun z => chiH f (c / m) (a / m) z) (by
      intro u v
      unfold chiH
      rw [← AddCircle.coe_add]
      congr 1
      rw [mul_add, mul_add, map_add]; push_cast; ring))
    have hD : D y = m • D (y / m) := by
      rw [← map_nsmul, ← hy]
    have hDz : D (y / m) = ψ (y / m) - chiH f (c / m) (a / m) (y / m) := rfl
    have hDy : D y = ψ y - chiH f (c / m) (a / m) y := rfl
    rw [← hDy, hD, hDz]
    exact hψ _
  exact sub_eq_zero.1 (key x)

end Torsionfree

end LeanCheck
