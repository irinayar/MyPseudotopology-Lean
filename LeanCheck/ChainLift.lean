import LeanCheck.ChainHom

/-!
# The lift to `ℚ` (Theorem 24.3 of HamelCharactersTVG)

For a group topology `λ` on `A = ℚ/ℤ = TorsA`, let `γ_λ` be the initial topology on `ℚ` of the maps
`t ↦ π(r t)` (`r ∈ ℚ`), where `π : ℚ → ℚ/ℤ` is the quotient map.  We show:

* `γ_λ` is a group topology on `ℚ` and every rational multiplication is continuous (`gam_scalar`);
* if the continuous characters of `λ` are exactly `x ↦ u • x`, then the continuous characters of `γ_λ` are
  exactly `t ↦ r t mod 1`, `r ∈ ℚ` (the set `Γ`): `dual_gam`;
* if `λ₁, λ₂` both have dual `ℤι` and `λ₁ ∨ λ₂` has a continuous character outside `ℤι`, then
  `γ_{λ₁} ∨ γ_{λ₂}` has a continuous character outside `Γ` (`lift_incompatible`).
-/

namespace LeanCheck

open Filter Topology

/-- The quotient map `π : ℚ → ℚ/ℤ`. -/
noncomputable def piHom : ℚ →+ TorsA where
  toFun t := ⟨(((t : ℝ)) : Circ), by
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨t.den, t.den_pos, ?_⟩
    rw [nsmul_coe_circ, AddCircle.coe_eq_zero_iff]
    refine ⟨t.num, ?_⟩
    have h : (t.den : ℝ) * (t : ℝ) = t.num := by
      have := Rat.mul_den_eq_num t
      have h2 : ((t * t.den : ℚ) : ℝ) = (t.num : ℝ) := by exact_mod_cast this
      push_cast at h2
      linarith
    rw [h]; simp⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' := by intro a b; apply Subtype.ext; simp [AddCircle.coe_add]

lemma piHom_coe (t : ℚ) : ((piHom t : TorsA) : Circ) = (((t : ℝ)) : Circ) := rfl

lemma piHom_surjective : Function.Surjective piHom := by
  intro x
  have hx : IsOfFinAddOrder (x : Circ) := x.2
  obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hx
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (x : Circ)
  rw [← ht] at hnx
  change n • ((t : ℝ) : Circ) = 0 at hnx
  rw [nsmul_coe_circ, AddCircle.coe_eq_zero_iff] at hnx
  obtain ⟨m, hm⟩ := hnx
  rw [zsmul_eq_mul, mul_one] at hm
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨(m : ℚ) / n, ?_⟩
  apply Subtype.ext
  rw [piHom_coe, ← ht]
  have : (((m : ℚ) / n : ℚ) : ℝ) = t := by
    push_cast
    rw [hm]; field_simp
  rw [this]

/-- `t ↦ π(r t)`. -/
noncomputable def hq (r : ℚ) : ℚ →+ TorsA := piHom.comp (AddMonoidHom.mulLeft r)

lemma hq_apply (r t : ℚ) : hq r t = piHom (r * t) := rfl

/-- The lifted topology `γ_λ`. -/
noncomputable def gam (t : TopologicalSpace TorsA) : TopologicalSpace ℚ :=
  ⨅ r : ℚ, TopologicalSpace.induced (hq r) t

lemma gam_group (t : TopologicalSpace TorsA) (h : @IsTopologicalAddGroup TorsA t _) :
    @IsTopologicalAddGroup ℚ (gam t) _ := by
  unfold gam
  letI : TopologicalSpace TorsA := t
  haveI : IsTopologicalAddGroup TorsA := h
  exact isTopologicalAddGroup_iInf (fun r => isTopologicalAddGroup_induced (hq r))

lemma hq_continuous (t : TopologicalSpace TorsA) (r : ℚ) :
    Continuous[gam t, t] (hq r) :=
  continuous_iff_le_induced.mpr (iInf_le _ r)

lemma gam_scalar (t : TopologicalSpace TorsA) (s : ℚ) :
    Continuous[gam t, gam t] (fun x : ℚ => s * x) := by
  unfold gam
  rw [continuous_iInf_rng]
  intro r
  rw [continuous_induced_rng]
  have : (hq r) ∘ (fun x : ℚ => s * x) = hq (r * s) := by
    funext x; simp [hq_apply, mul_assoc]
  rw [this]
  exact hq_continuous t (r * s)

/-- General quarter-arc criterion: a character bounded by `1/4` on a neighbourhood of `0` in a topological
group is continuous. -/
lemma continuous_of_quarter_gen {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (ψ : G →+ Circ) {W : Set G} (hW : W ∈ 𝓝 (0 : G))
    (hq : ∀ x ∈ W, ‖ψ x‖ < 1 / 4) : Continuous ψ := by
  apply continuous_of_continuousAt_zero ψ
  rw [ContinuousAt, map_zero, NormedAddGroup.nhds_zero_basis_norm_lt.tendsto_right_iff]
  intro ε hε
  obtain ⟨R, hR1, hRε⟩ := exists_R ε hε
  have hV : (⋂ j ∈ Finset.range (R + 1), (fun x : G => j • x) ⁻¹' W) ∈ 𝓝 (0 : G) := by
    rw [Filter.biInter_finset_mem]
    intro j _
    exact (continuous_nsmul j).continuousAt.preimage_mem_nhds (by simpa using hW)
  filter_upwards [hV] with x hx
  have hj : ∀ j : ℕ, j ≤ R → ‖j • ψ x‖ < 1 / 4 := by
    intro j hj
    rw [← map_nsmul]
    apply hq
    exact (Set.mem_iInter₂.mp hx) j (Finset.mem_range.mpr (by omega))
  exact lt_of_le_of_lt (norm_le_of_multiples (ψ x) R hR1 hj) hRε

lemma eq_zero_of_multiples (y : Circ) (h : ∀ j : ℕ, ‖j • y‖ < 1 / 4) : y = 0 := by
  by_contra hy
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  obtain ⟨R, hR1, hRε⟩ := exists_R ‖y‖ hpos
  have := norm_le_of_multiples y R hR1 (fun j _ => h j)
  linarith

lemma exists_k_of_den_dvd (r : ℚ) (d : ℕ) (h : r.den ∣ d) : ∃ k : ℤ, r * d = k := by
  obtain ⟨m, hm⟩ := h
  refine ⟨r.num * m, ?_⟩
  have := Rat.mul_den_eq_num r
  rw [hm]; push_cast
  calc r * ((r.den : ℚ) * m) = (r * r.den) * m := by ring
    _ = r.num * m := by rw [this]

lemma hq_zsmul (r : ℚ) (d : ℕ) (hd : d ≠ 0) (k : ℤ) (hk : r * d = k) (t : ℚ) :
    hq r t = k • hq (1 / (d : ℚ)) t := by
  rw [hq_apply, hq_apply, ← map_zsmul]
  congr 1
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [zsmul_eq_mul, ← hk]
  field_simp

/-- Every `γ_λ`-continuous character of `ℚ` is `t ↦ r t mod 1` for a rational `r`, provided the continuous
characters of `λ` are exactly `x ↦ u • x`. -/
theorem dual_gam_mp (t : TopologicalSpace TorsA) (ht : @IsTopologicalAddGroup TorsA t _)
    (hdual : ∀ χ : TorsA →+ Circ, @Continuous TorsA Circ t _ χ ↔
      ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ))
    (ψ : ℚ →+ Circ) (hψ : @Continuous ℚ Circ (gam t) _ ψ) :
    ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ) := by
  letI : TopologicalSpace TorsA := t
  haveI : IsTopologicalAddGroup TorsA := ht
  have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (ψ 0) := by
    rw [map_zero]
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  have hpre : ψ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} ∈ @nhds ℚ (gam t) 0 :=
    (@Continuous.continuousAt ℚ Circ (gam t) _ ψ 0 hψ) hS
  unfold gam at hpre
  rw [nhds_iInf] at hpre
  obtain ⟨I, hI, V, hV, hVuniv, hs⟩ := Filter.mem_iInf'.mp hpre
  have hex : ∀ r : ℚ, ∃ U : Set TorsA, U ∈ 𝓝 (0 : TorsA) ∧ hq r ⁻¹' U ⊆ V r := by
    intro r
    have h := hV r
    rw [nhds_induced, map_zero] at h
    exact Filter.mem_comap.mp h
  choose U hU hUV using hex
  obtain ⟨d, hdd⟩ : ∃ d : ℕ, d = ∏ r ∈ hI.toFinset, r.den := ⟨_, rfl⟩
  have hdpos : 0 < d := by
    rw [hdd]; exact Finset.prod_pos (fun r _ => r.den_pos)
  have hden : ∀ r ∈ I, r.den ∣ d := fun r hr => by
    rw [hdd]; exact Finset.dvd_prod_of_mem _ (hI.mem_toFinset.mpr hr)
  have hk : ∀ r : ℚ, ∃ k : ℤ, r ∈ I → r * d = k := by
    intro r
    by_cases hr : r ∈ I
    · obtain ⟨k, hk⟩ := exists_k_of_den_dvd r d (hden r hr)
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose k hk using hk
  obtain ⟨hd, hhd⟩ : ∃ hd : ℚ →+ TorsA, hd = hq (1 / (d : ℚ)) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : Set TorsA,
      W = ⋂ r ∈ hI.toFinset, (fun x : TorsA => k r • x) ⁻¹' U r := ⟨_, rfl⟩
  have hW : W ∈ 𝓝 (0 : TorsA) := by
    rw [hWdef, Filter.biInter_finset_mem]
    intro r _
    exact (continuous_zsmul (k r)).continuousAt.preimage_mem_nhds (by simpa using hU r)
  have hbound : ∀ x : ℚ, hd x ∈ W → ‖ψ x‖ < 1 / 4 := by
    intro x hx
    have hxs : x ∈ ψ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} := by
      rw [hs.1]
      refine Set.mem_iInter₂.mpr (fun r hr => ?_)
      rw [hWdef] at hx
      have hr' : r ∈ hI.toFinset := hI.mem_toFinset.mpr hr
      have h1 : k r • hd x ∈ U r := Set.mem_iInter₂.mp hx r hr'
      have h2 : hq r x = k r • hd x := by
        rw [hhd]; exact hq_zsmul r d hdpos.ne' (k r) (hk r hr) x
      apply hUV r
      show hq r x ∈ U r
      rw [h2]; exact h1
    exact hxs
  have hker : ∀ x : ℚ, hd x = 0 → ψ x = 0 := by
    intro x hx
    apply eq_zero_of_multiples
    intro j
    have hj : hd (j • x) ∈ W := by
      rw [map_nsmul, hx, smul_zero]; exact mem_of_mem_nhds hW
    have := hbound (j • x) hj
    rwa [map_nsmul] at this
  have hsurj : Function.Surjective hd := by
    intro y
    obtain ⟨q, hq'⟩ := piHom_surjective y
    refine ⟨q * d, ?_⟩
    rw [hhd, hq_apply]
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
    have : 1 / (d : ℚ) * (q * d) = q := by field_simp
    rw [this]; exact hq'
  obtain ⟨ψbar, hψbar⟩ : ∃ ψbar : TorsA →+ Circ, ∀ x, ψbar (hd x) = ψ x :=
    ⟨AddMonoidHom.liftOfSurjective hd hsurj ⟨ψ, fun x hx => hker x hx⟩, fun x => by
      simp⟩
  have hcont : Continuous ψbar := by
    refine continuous_of_quarter_gen ψbar hW ?_
    intro y hy
    obtain ⟨x, rfl⟩ := hsurj y
    rw [hψbar]; exact hbound x hy
  obtain ⟨u, hu⟩ := (hdual ψbar).mp hcont
  refine ⟨(u : ℚ) / d, fun s => ?_⟩
  rw [← hψbar, hu, hhd, hq_apply, piHom_coe, zsmul_coe_circ]
  congr 1
  push_cast
  ring

/-- Conversely every `t ↦ r t mod 1` is `γ_λ`-continuous. -/
theorem dual_gam_mpr (t : TopologicalSpace TorsA) (ht : @IsTopologicalAddGroup TorsA t _)
    (hdual : ∀ χ : TorsA →+ Circ, @Continuous TorsA Circ t _ χ ↔
      ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ))
    (r : ℚ) :
    @Continuous ℚ Circ (gam t) _ (fun s : ℚ => (((r * s : ℚ) : ℝ) : Circ)) := by
  letI : TopologicalSpace TorsA := t
  haveI : IsTopologicalAddGroup TorsA := ht
  have hχ : Continuous ((AddCommGroup.torsion Circ).subtype : TorsA →+ Circ) :=
    (hdual _).mpr ⟨1, fun x => by simp⟩
  exact @Continuous.comp ℚ TorsA Circ (gam t) t _ _ _ hχ (hq_continuous t r)

/-- The dual of `γ_λ` is exactly `Γ = {t ↦ r t mod 1}`. -/
theorem dual_gam (t : TopologicalSpace TorsA) (ht : @IsTopologicalAddGroup TorsA t _)
    (hdual : ∀ χ : TorsA →+ Circ, @Continuous TorsA Circ t _ χ ↔
      ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ))
    (ψ : ℚ →+ Circ) :
    @Continuous ℚ Circ (gam t) _ ψ ↔ ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ) := by
  constructor
  · exact dual_gam_mp t ht hdual ψ
  · rintro ⟨r, hr⟩
    have : (ψ : ℚ → Circ) = fun s : ℚ => (((r * s : ℚ) : ℝ) : Circ) := funext hr
    rw [this]
    exact dual_gam_mpr t ht hdual r

lemma hq_one_continuous (t1 t2 : TopologicalSpace TorsA) :
    Continuous[gam t1 ⊓ gam t2, t1 ⊓ t2] (hq 1) := by
  have a1 : Continuous[gam t1 ⊓ gam t2, t1] (hq 1) :=
    continuous_inf_dom_left (t₂ := gam t2) (hq_continuous t1 1)
  have a2 : Continuous[gam t1 ⊓ gam t2, t2] (hq 1) :=
    continuous_inf_dom_right (t₁ := gam t1) (hq_continuous t2 1)
  exact (continuous_inf_rng (t₁ := gam t1 ⊓ gam t2) (t₂ := t1) (t₃ := t2)).2 ⟨a1, a2⟩

/-- Lifting an obstruction from `ℚ/ℤ` to `ℚ`. -/
theorem lift_incompatible (t1 t2 : TopologicalSpace TorsA)
    (ζ : TorsA →+ Circ) (hζ : @Continuous TorsA Circ (t1 ⊓ t2) _ ζ)
    (hne : ∀ u : ℤ, ∃ x : TorsA, ζ x ≠ u • (x : Circ)) :
    ∃ ψ : ℚ →+ Circ, @Continuous ℚ Circ (gam t1 ⊓ gam t2) _ ψ ∧
      ∀ r : ℚ, ∃ s : ℚ, ψ s ≠ (((r * s : ℚ) : ℝ) : Circ) := by
  refine ⟨ζ.comp (hq 1), ?_, ?_⟩
  · exact @Continuous.comp ℚ TorsA Circ (gam t1 ⊓ gam t2) (t1 ⊓ t2) _ _ _ hζ
      (hq_one_continuous t1 t2)
  · intro r
    by_contra hcon
    push_neg at hcon
    have hr := hcon
    have h1 := hr 1
    have h0 : ζ (hq 1 1) = 0 := by
      have : hq 1 1 = 0 := by
        apply Subtype.ext
        rw [hq_apply, piHom_coe]
        simp
      rw [this, map_zero]
    simp only [AddMonoidHom.comp_apply] at h1
    rw [h0, mul_one] at h1
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := ((r : ℚ) : ℝ))).mp h1.symm
    rw [zsmul_eq_mul, mul_one] at hm
    have hrm : r = m := by exact_mod_cast hm.symm
    obtain ⟨x, hx⟩ := hne m
    obtain ⟨s, rfl⟩ := piHom_surjective x
    apply hx
    have := hr s
    simp only [AddMonoidHom.comp_apply, hq_apply, one_mul] at this
    rw [this, hrm, piHom_coe, zsmul_coe_circ]
    congr 1
    push_cast; ring

lemma piHom_half_ne : piHom (1 / 2) ≠ 0 := by
  intro h
  have h2 : ((piHom (1 / 2) : TorsA) : Circ) = 0 := by rw [h]; rfl
  rw [piHom_coe] at h2
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := (((1 / 2 : ℚ)) : ℝ))).mp h2
  rw [zsmul_eq_mul, mul_one] at hn
  push_cast at hn
  have h3 : (2 : ℝ) * n = 1 := by linarith
  have h4 : (2 : ℤ) * n = 1 := by exact_mod_cast h3
  omega

/-- If `λ` is Hausdorff then so is `γ_λ`. -/
theorem gam_t2 (t : TopologicalSpace TorsA) [@T2Space TorsA t] : @T2Space ℚ (gam t) := by
  letI : TopologicalSpace TorsA := t
  letI : TopologicalSpace ℚ := gam t
  have hinj : Function.Injective (fun (x : ℚ) (r : ℚ) => hq r x) := by
    intro x y hxy
    by_contra hne
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h := congrFun hxy (1 / (2 * (x - y)))
    simp only at h
    have h0 : hq (1 / (2 * (x - y))) (x - y) = 0 := by
      rw [map_sub, h, sub_self]
    rw [hq_apply] at h0
    have : 1 / (2 * (x - y)) * (x - y) = 1 / 2 := by field_simp
    rw [this] at h0
    exact piHom_half_ne h0
  have hcont : Continuous (fun (x : ℚ) (r : ℚ) => hq r x) :=
    continuous_pi (fun r => hq_continuous t r)
  exact T2Space.of_injective_continuous hinj hcont

/-- **Theorem 24.3 lifted, formal capstone.**  There are two Hausdorff group topologies `γ₁, γ₂` on `ℚ`, each
with dual exactly `Γ = {t ↦ r t mod 1}`, whose join `γ₁ ⊔ γ₂` (the topology `⊓` in Mathlib's order) carries a
continuous character not in `Γ`. -/
theorem lift_capstone :
    ∃ (g1 g2 : TopologicalSpace ℚ),
      @IsTopologicalAddGroup ℚ g1 _ ∧ @IsTopologicalAddGroup ℚ g2 _ ∧
      @T2Space ℚ g1 ∧ @T2Space ℚ g2 ∧
      (∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ g1 _ ψ ↔ ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ)) ∧
      (∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ g2 _ ψ ↔ ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ)) ∧
      ∃ ψ : ℚ →+ Circ, @Continuous ℚ Circ (g1 ⊓ g2) _ ψ ∧
        ∀ r : ℚ, ∃ s : ℚ, ψ s ≠ (((r * s : ℚ) : ℝ) : Circ) := by
  obtain ⟨M1, M2, ζ, h1, h2, ht1, ht2, hd1, hd2, hζ, hne⟩ := final_capstone
  have g1 := (basisOf (Set.range M1)).isTopologicalAddGroup
  have g2 := (basisOf (Set.range M2)).isTopologicalAddGroup
  obtain ⟨ψ, hψ, hψne⟩ := lift_incompatible (basisOf (Set.range M1)).topology
    (basisOf (Set.range M2)).topology ζ hζ hne
  refine ⟨gam (basisOf (Set.range M1)).topology, gam (basisOf (Set.range M2)).topology,
    gam_group _ g1, gam_group _ g2, @gam_t2 _ ht1, @gam_t2 _ ht2,
    dual_gam _ g1 hd1, dual_gam _ g2 hd2, ψ, hψ, hψne⟩

end LeanCheck
