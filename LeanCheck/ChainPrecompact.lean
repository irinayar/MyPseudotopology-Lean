import LeanCheck.ChainHamelFinal

/-!
# Classification of precompact TVGQ topologies (TVGQ-v7, Theorem `classification`, Proposition `minimal`)

`𝒜 = Hom(ℝ, 𝕋)` (here `Chars`).  For `H ⊆ 𝒜`, `θ_H` is the initial topology of the characters in `H`.

Unconditional part (proved from scratch here):
* `θ_H` is a group topology, it is Hausdorff iff `H` separates points, it is precompact for every `H`,
  the characters in `H` are `θ_H`-continuous, `H ⊆ H' ⇒ θ_{H'} ≤ θ_H`;
* if `H` is invariant under rational rescaling of arguments then `θ_H` is TVGQ, and conversely the dual of a
  TVGQ group topology is rationally invariant;
* `β_{f,S} = θ_{H_{f,S}}`.

Conditional part: the two standard facts quoted by the paper from compact duality (Weil / Comfort–Ross)
-- (F1) the dual of `θ_H` is exactly `H` for point-separating `H`, (F2) every Hausdorff precompact group topology
is `θ` of its dual -- are not available in Mathlib (no Pontryagin duality / Peter–Weyl) and are taken as the
hypothesis `PrecompactDuality`.  Under it we prove the bijection, order isomorphism, scalar-ring formula, and
Proposition `minimal`.
-/

namespace LeanCheck

open Filter Topology

/-- The circle topology, as a reducible abbreviation (so that instances see through it even when a
topology on `ℝ` is a local instance). -/
abbrev circTop' : TopologicalSpace Circ := inferInstance

/-- The group `𝒜` of all algebraic characters of `ℝ`. -/
abbrev Chars : Type := ℝ →+ Circ

/-- `θ_H`: the initial topology of the characters in `H`. -/
noncomputable def theta (H : Set Chars) : TopologicalSpace ℝ :=
  ⨅ χ : H, TopologicalSpace.induced ((χ : Chars) : ℝ → Circ) circTop'

/-- `H` separates the points of `ℝ`. -/
def Separates (H : Set Chars) : Prop := ∀ x : ℝ, x ≠ 0 → ∃ χ ∈ H, χ x ≠ 0

/-- Precompactness of a group topology: finitely many translates of every neighbourhood of `0` cover. -/
def Precompact (τ : TopologicalSpace ℝ) : Prop :=
  ∀ U ∈ @nhds ℝ τ 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ t ∈ F, x - t ∈ U

/-- A Hausdorff precompact TVGQ topology on `ℝ`. -/
def PTVGQ (τ : TopologicalSpace ℝ) : Prop :=
  @IsTopologicalAddGroup ℝ τ _ ∧ @T2Space ℝ τ ∧ Precompact τ ∧
    ∀ q : ℚ, Continuous[τ, τ] (mq q : ℝ → ℝ)

/-! ### Elementary properties of `θ_H` -/

lemma theta_cont_of_mem (H : Set Chars) (χ : Chars) (h : χ ∈ H) :
    @Continuous ℝ Circ (theta H) circTop χ :=
  continuous_iff_le_induced.mpr
    (iInf_le (fun χ : H => TopologicalSpace.induced ((χ : Chars) : ℝ → Circ) circTop) ⟨χ, h⟩)

lemma theta_group (H : Set Chars) : @IsTopologicalAddGroup ℝ (theta H) _ := by
  unfold theta
  exact isTopologicalAddGroup_iInf (fun χ : H => isTopologicalAddGroup_induced (χ : Chars))

/-- `H ⊆ H'` gives `θ_H ⊆ θ_{H'}` as families of open sets (`θ_{H'} ≤ θ_H` in Mathlib's order). -/
lemma theta_mono {H H' : Set Chars} (h : H ⊆ H') : theta H' ≤ theta H :=
  le_iInf fun χ : H => iInf_le (fun χ : H' => TopologicalSpace.induced ((χ : Chars) : ℝ → Circ) circTop)
    ⟨χ.1, h χ.2⟩

lemma theta_t2 (H : Set Chars) (hH : Separates H) : @T2Space ℝ (theta H) := by
  have hc : Continuous[theta H, Pi.topologicalSpace]
      (fun x : ℝ => fun χ : H => (χ : Chars) x) :=
    @continuous_pi ℝ H (fun _ : H => Circ) (theta H) (fun _ => circTop) _
      (fun χ => theta_cont_of_mem H χ.1 χ.2)
  have hinj : Function.Injective (fun x : ℝ => fun χ : H => (χ : Chars) x) := by
    intro x y hxy
    by_contra hne
    obtain ⟨χ, hχ, hne'⟩ := hH (x - y) (sub_ne_zero.mpr hne)
    apply hne'
    have hh := congrFun hxy ⟨χ, hχ⟩
    simp only at hh
    rw [map_sub, hh, sub_self]
  exact @T2Space.of_injective_continuous ℝ _ (theta H) _ _ _ hinj hc

lemma theta_nhds_sub (H : Set Chars) (V : Set ℝ) (hV : V ∈ @nhds ℝ (theta H) 0) :
    ∃ (I : Finset H) (W : H → Set Circ), (∀ i, W i ∈ 𝓝 (0 : Circ)) ∧
      {x : ℝ | ∀ i ∈ I, (i : Chars) x ∈ W i} ⊆ V :=
  nhds_iInf_induced_circ (fun (χ : H) (x : ℝ) => (χ : Chars) x) (fun χ => map_zero _) V hV

/-- Conversely, a Hausdorff `θ_H` forces `H` to separate points. -/
lemma sep_of_theta_t2 (H : Set Chars) (h : @T2Space ℝ (theta H)) : Separates H := by
  intro x hx
  obtain ⟨I, W, hW, hsub⟩ := theta_nhds_sub H {x}ᶜ (by
    have : IsOpen[theta H] ({x}ᶜ : Set ℝ) := (@isClosed_singleton ℝ (theta H) _ x).isOpen_compl
    exact @IsOpen.mem_nhds ℝ (theta H) _ _ this (by simpa using hx.symm))
  by_contra hno
  push_neg at hno
  apply hsub (show x ∈ {y : ℝ | ∀ i ∈ I, (i : Chars) y ∈ W i} from fun i _ => ?_)
  · rfl
  · rw [hno i.1 i.2]; exact mem_of_mem_nhds (hW i)

/-! ### Precompactness of `θ_H` -/

theorem theta_precompact (H : Set Chars) : Precompact (theta H) := by
  classical
  intro V hV
  obtain ⟨I, W, hW, hsub⟩ := theta_nhds_sub H V hV
  let Φ : ℝ →+ (I → Circ) :=
    { toFun := fun x i => (i.1 : Chars) x
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let U : Set (I → Circ) := Set.pi Set.univ (fun i : I => W i.1)
  have hU : U ∈ 𝓝 (0 : I → Circ) := set_pi_mem_nhds Set.finite_univ (fun i _ => hW i.1)
  obtain ⟨U', hU', hUU⟩ := exists_nhds_zero_half hU
  let U'' : Set (I → Circ) := U' ∩ (fun z => -z) ⁻¹' U'
  have hU'' : U'' ∈ 𝓝 (0 : I → Circ) :=
    Filter.inter_mem hU' (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hU'))
  have hdiff : ∀ v ∈ U'', ∀ w ∈ U'', v - w ∈ U := fun v hv w hw => by
    rw [sub_eq_add_neg]; exact hUU v hv.1 (-w) hw.2
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun y : I → Circ => (fun z => z - y) ⁻¹' U'') (fun y _ => by
      refine (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds ?_
      simpa using hU'')
  let rep : (I → Circ) → ℝ := fun y => if h : ∃ x, Φ x - y ∈ U'' then h.choose else 0
  refine ⟨t.image rep, fun x => ?_⟩
  obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (Φ x)))
  have hex : ∃ x', Φ x' - y ∈ U'' := ⟨x, hy⟩
  have hrep : Φ (rep y) - y ∈ U'' := by
    have : rep y = hex.choose := by simp only [rep, dif_pos hex]
    rw [this]; exact hex.choose_spec
  refine ⟨rep y, Finset.mem_image_of_mem _ hyt, ?_⟩
  apply hsub
  intro i hi
  have h1 : Φ (x - rep y) ∈ U := by
    have : Φ (x - rep y) = (Φ x - y) - (Φ (rep y) - y) := by rw [map_sub]; abel
    rw [this]; exact hdiff _ hy _ hrep
  exact h1 ⟨i, hi⟩ (Set.mem_univ _)

/-- A coarser group topology of a precompact one is precompact. -/
lemma precompact_of_le {τ τ' : TopologicalSpace ℝ} (h : τ ≤ τ') (hτ : Precompact τ) : Precompact τ' := by
  intro U hU
  exact hτ U ((nhds_mono h) hU)

/-! ### TVGQ and rational invariance -/

/-- Rationally invariant character sets give TVGQ character topologies. -/
theorem theta_ratdil (H : Set Chars) (hH : RatInv H) (q : ℚ) :
    Continuous[theta H, theta H] (mq q : ℝ → ℝ) := by
  unfold theta
  refine continuous_iInf_rng.2 (fun χ => continuous_induced_rng.2 ?_)
  have : (((χ : Chars) : ℝ → Circ) ∘ (mq q : ℝ → ℝ)) = ((χ : Chars).comp (mq q) : ℝ → Circ) := rfl
  rw [this]
  exact theta_cont_of_mem H _ (hH _ χ.2 q)

theorem theta_ptvgq (H : Set Chars) (hs : Separates H) (hH : RatInv H) : PTVGQ (theta H) :=
  ⟨theta_group H, theta_t2 H hs, theta_precompact H, theta_ratdil H hH⟩

/-- The dual of a group topology on `ℝ`, as a subgroup of `𝒜`. -/
def dualGroup (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _) : AddSubgroup Chars where
  carrier := {χ | @Continuous ℝ Circ τ circTop' χ}
  zero_mem' := by
    show @Continuous ℝ Circ τ circTop' (0 : Chars)
    exact @continuous_const ℝ Circ τ circTop' 0
  add_mem' := by
    intro a b ha hb
    show @Continuous ℝ Circ τ circTop' (a + b : Chars)
    exact @Continuous.add Circ circTop' _ _ ℝ τ _ _ ha hb
  neg_mem' := by
    intro a ha
    show @Continuous ℝ Circ τ circTop' (-a : Chars)
    exact @Continuous.comp ℝ Circ Circ τ circTop' circTop' (a : ℝ → Circ) (fun y : Circ => -y) continuous_neg ha

lemma mem_dualGroup (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _) (χ : Chars) :
    χ ∈ dualGroup τ hτ ↔ @Continuous ℝ Circ τ circTop' χ := Iff.rfl

/-- The dual of a TVGQ group topology is rationally invariant. -/
theorem dualGroup_ratInv (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _)
    (hq : ∀ q : ℚ, Continuous[τ, τ] (mq q : ℝ → ℝ)) : RatInv (dualGroup τ hτ : Set Chars) := by
  intro χ hχ q
  have hχ' : @Continuous ℝ Circ τ circTop χ := (mem_dualGroup τ hτ χ).1 hχ
  exact (mem_dualGroup τ hτ _).2
    (@Continuous.comp ℝ ℝ Circ τ τ circTop (mq q : ℝ → ℝ) (χ : ℝ → Circ) hχ' (hq q))

/-! ### The conditional classification -/

/- The two standard facts from compact duality quoted in TVGQ-v7 (Weil; Comfort–Ross): (F1) the dual of `θ_H`
is `H`; (F2) Hausdorff precompact group topologies are generated by their characters.  (F1) is proved in
`ChainDuality`; (F2) is still assumed (it needs Peter–Weyl). -/

/-- (F1): the dual of `θ_H` is `H`.  (Proved in `ChainDuality` as `dualThetaFact`.) -/
def DualThetaFact : Prop := ∀ H : AddSubgroup Chars, Separates (H : Set Chars) → ∀ χ : Chars,
  @Continuous ℝ Circ (theta (H : Set Chars)) circTop χ ↔ χ ∈ H

/-- (F2): every Hausdorff precompact group topology is the character topology of its dual. -/
def GeneratedFact : Prop := ∀ (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _), @T2Space ℝ τ →
  Precompact τ → τ = theta (dualGroup τ hτ : Set Chars)

/-- Both standard facts together. -/
structure PrecompactDuality : Prop where
  dual_theta : DualThetaFact
  generated : GeneratedFact

/-- Point-separating rational vector subspaces of `𝒜`. -/
def SepSub (H : AddSubgroup Chars) : Prop := Separates (H : Set Chars) ∧ RatInv (H : Set Chars)

/-- `θ_H` determines `H`. -/
theorem theta_injective (hD : DualThetaFact) (H H' : AddSubgroup Chars)
    (hs : Separates (H : Set Chars)) (hs' : Separates (H' : Set Chars))
    (h : theta (H : Set Chars) = theta (H' : Set Chars)) : H = H' := by
  ext χ
  rw [← hD H hs, ← hD H' hs', h]

/-- **Order**: `H ⊆ H'` iff `θ_H ⊆ θ_{H'}` (i.e. `θ_{H'} ≤ θ_H`). -/
theorem theta_le_iff (hD : DualThetaFact) (H H' : AddSubgroup Chars)
    (hs : Separates (H : Set Chars)) (hs' : Separates (H' : Set Chars)) :
    theta (H' : Set Chars) ≤ theta (H : Set Chars) ↔ H ≤ H' := by
  constructor
  · intro hle χ hχ
    rw [← hD H' hs']
    exact continuous_le_dom hle (theta_cont_of_mem _ χ hχ)
  · intro h
    exact theta_mono (fun χ hχ => h hχ)

/-- The dual of `θ_H` is `H`, as subgroups. -/
theorem dualGroup_theta (hD : DualThetaFact) (H : AddSubgroup Chars) (hs : Separates (H : Set Chars)) :
    dualGroup (theta (H : Set Chars)) (theta_group _) = H := by
  ext χ
  rw [mem_dualGroup]
  exact hD H hs χ

/-- **Theorem `classification`** (under the standard duality facts).
(1) every point-separating rational subspace `H` gives a Hausdorff precompact TVGQ topology `θ_H`;
(2) every Hausdorff precompact TVGQ topology is `θ_H` for such an `H`;
(3) `H ↦ θ_H` is injective and an order isomorphism. -/
theorem classification (hD : PrecompactDuality) :
    (∀ H : AddSubgroup Chars, SepSub H → PTVGQ (theta (H : Set Chars))) ∧
    (∀ τ : TopologicalSpace ℝ, PTVGQ τ → ∃ H : AddSubgroup Chars, SepSub H ∧ τ = theta (H : Set Chars)) ∧
    (∀ H H' : AddSubgroup Chars, SepSub H → SepSub H' →
      (theta (H : Set Chars) = theta (H' : Set Chars) ↔ H = H')) ∧
    (∀ H H' : AddSubgroup Chars, SepSub H → SepSub H' →
      (theta (H' : Set Chars) ≤ theta (H : Set Chars) ↔ H ≤ H')) := by
  refine ⟨fun H hH => theta_ptvgq _ hH.1 hH.2, ?_, ?_, ?_⟩
  · rintro τ ⟨hg, ht, hp, hq⟩
    have hgen := hD.generated τ hg ht hp
    refine ⟨dualGroup τ hg, ⟨?_, dualGroup_ratInv τ hg hq⟩, hgen⟩
    apply sep_of_theta_t2
    rw [← hgen]; exact ht
  · intro H H' hH hH'
    constructor
    · exact theta_injective hD.dual_theta H H' hH.1 hH'.1
    · rintro rfl; rfl
  · intro H H' hH hH'
    exact theta_le_iff hD.dual_theta H H' hH.1 hH'.1

/-- **The bijection**: point-separating rational subspaces of `𝒜` correspond to Hausdorff precompact TVGQ
topologies on `ℝ` (under the standard duality facts). -/
noncomputable def classificationEquiv (hD : PrecompactDuality) :
    {H : AddSubgroup Chars // SepSub H} ≃ {τ : TopologicalSpace ℝ // PTVGQ τ} where
  toFun H := ⟨theta (H.1 : Set Chars), theta_ptvgq _ H.2.1 H.2.2⟩
  invFun τ := ⟨dualGroup τ.1 τ.2.1, by
    have hgen := hD.generated τ.1 τ.2.1 τ.2.2.1 τ.2.2.2.1
    refine ⟨?_, dualGroup_ratInv τ.1 τ.2.1 τ.2.2.2.2⟩
    apply sep_of_theta_t2
    rw [← hgen]; exact τ.2.2.1⟩
  left_inv H := by
    apply Subtype.ext
    exact dualGroup_theta hD.dual_theta H.1 H.2.1
  right_inv τ := by
    apply Subtype.ext
    exact (hD.generated τ.1 τ.2.1 τ.2.2.1 τ.2.2.2.1).symm

/-- **Scalar formula**: `m_a` is continuous for `θ_H` iff `χ ∘ m_a ∈ H` for every `χ ∈ H`
(the `⇒` direction uses (F1)). -/
theorem theta_scalar (hD : DualThetaFact) (H : AddSubgroup Chars) (hs : Separates (H : Set Chars))
    (a : ℝ) :
    Continuous[theta (H : Set Chars), theta (H : Set Chars)] (fun x : ℝ => a * x) ↔
      ∀ χ ∈ H, χ.comp (AddMonoidHom.mulLeft a) ∈ H := by
  constructor
  · intro h χ hχ
    rw [← hD H hs]
    exact @Continuous.comp ℝ ℝ Circ (theta (H : Set Chars)) (theta (H : Set Chars)) circTop
      (fun x : ℝ => a * x) (χ : ℝ → Circ) (theta_cont_of_mem _ χ hχ) h
  · intro h
    unfold theta
    refine continuous_iInf_rng.2 (fun χ => continuous_induced_rng.2 ?_)
    exact theta_cont_of_mem (H : Set Chars) (χ.1.comp (AddMonoidHom.mulLeft a)) (h _ χ.2)

/-! ### Proposition `minimal` -/

/-- `x ↦ p(c x)` vanishing identically forces `c = 0`. -/
lemma pc_zero (c : ℝ) (h : ∀ x : ℝ, ((c * x : ℝ) : Circ) = 0) : c = 0 := by
  by_contra hc
  have h0 := h (1 / (2 * c))
  have : c * (1 / (2 * c)) = 1 / 2 := by field_simp
  rw [this] at h0
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h0
  rw [zsmul_eq_mul, mul_one] at hn
  have h3 : (2 : ℝ) * n = 1 := by linarith
  have h4 : (2 : ℤ) * n = 1 := by exact_mod_cast h3
  omega

/-- `H_ℚ = { x ↦ p(q x) : q ∈ ℚ }`. -/
def HQ : AddSubgroup Chars where
  carrier := {χ | ∃ q : ℚ, ∀ x : ℝ, χ x = (((q : ℝ) * x : ℝ) : Circ)}
  zero_mem' := ⟨0, fun x => by simp⟩
  add_mem' := by
    rintro a b ⟨q, hq⟩ ⟨r, hr⟩
    refine ⟨q + r, fun x => ?_⟩
    simp only [AddMonoidHom.add_apply]
    rw [hq, hr, ← AddCircle.coe_add]
    congr 1; push_cast; ring
  neg_mem' := by
    rintro a ⟨q, hq⟩
    refine ⟨-q, fun x => ?_⟩
    simp only [AddMonoidHom.neg_apply]
    rw [hq, ← AddCircle.coe_neg]
    congr 1; push_cast; ring

/-- `H_ℝ = { x ↦ p(b x) : b ∈ ℝ }` (the ordinary characters). -/
def HR : AddSubgroup Chars where
  carrier := {χ | ∃ b : ℝ, ∀ x : ℝ, χ x = ((b * x : ℝ) : Circ)}
  zero_mem' := ⟨0, fun x => by simp⟩
  add_mem' := by
    rintro a b ⟨q, hq⟩ ⟨r, hr⟩
    refine ⟨q + r, fun x => ?_⟩
    simp only [AddMonoidHom.add_apply]
    rw [hq, hr, ← AddCircle.coe_add]
    congr 1; ring
  neg_mem' := by
    rintro a ⟨q, hq⟩
    refine ⟨-q, fun x => ?_⟩
    simp only [AddMonoidHom.neg_apply]
    rw [hq, ← AddCircle.coe_neg]
    congr 1; ring

lemma HQ_le_HR : HQ ≤ HR := by
  rintro χ ⟨q, hq⟩
  exact ⟨(q : ℝ), hq⟩

lemma HQ_separates : Separates (HQ : Set Chars) := by
  intro x hx
  have hxpos : 0 < |x| := abs_pos.mpr hx
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show 1 / (4 * |x|) < 1 / (2 * |x|) by
    apply one_div_lt_one_div_of_lt (by positivity); linarith)
  refine ⟨cmulHom (q : ℝ), ⟨q, fun y => rfl⟩, ?_⟩
  intro h0
  rw [cmulHom_apply] at h0
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h0
  rw [zsmul_eq_mul, mul_one] at hn
  have hqx1 : 1 / 4 < |(q : ℝ) * x| := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < q by
      have : 0 < 1 / (4 * |x|) := by positivity
      exact_mod_cast lt_trans this hq1)]
    have : 1 / (4 * |x|) < q := hq1
    rw [div_lt_iff₀ (by positivity)] at this
    nlinarith
  have hqx2 : |(q : ℝ) * x| < 1 / 2 := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < q by
      have : 0 < 1 / (4 * |x|) := by positivity
      exact_mod_cast lt_trans this hq1)]
    have : (q : ℝ) < 1 / (2 * |x|) := hq2
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  have hn0 : (n : ℝ) = (q : ℝ) * x := by linarith
  rw [← hn0] at hqx1 hqx2
  have h5 : |(n : ℝ)| < 1 / 2 := hqx2
  have : n = 0 := by
    have h6 : |(n : ℝ)| < 1 := by linarith
    have : |n| < 1 := by exact_mod_cast h6
    exact Int.abs_lt_one_iff.mp this
  rw [this] at hqx1
  simp at hqx1
  linarith

lemma HQ_ratInv : RatInv (HQ : Set Chars) := by
  rintro χ ⟨q, hq⟩ r
  refine ⟨q * r, fun x => ?_⟩
  show χ (mq r x) = _
  rw [show mq r x = (r : ℝ) * x from congrFun (mq_real r) x, hq]
  congr 1; push_cast; ring

lemma HR_separates : Separates (HR : Set Chars) := fun x hx => by
  obtain ⟨χ, hχ, h⟩ := HQ_separates x hx
  exact ⟨χ, HQ_le_HR hχ, h⟩

/-- `θ_ℚ`, the minimal rational character topology. -/
noncomputable abbrev thetaQ : TopologicalSpace ℝ := theta (HQ : Set Chars)

/-- The product topology on `ℚ → 𝕋`. -/
abbrev piQ : TopologicalSpace (ℚ → Circ) := inferInstance

theorem thetaQ_ptvgq : PTVGQ thetaQ := theta_ptvgq _ HQ_separates HQ_ratInv

/-- `θ_ℚ` is the topology induced by the countable family `x ↦ (p(q x))_q`. -/
noncomputable def PsiQ : ℝ → (ℚ → Circ) := fun x q => (((q : ℝ) * x : ℝ) : Circ)

lemma thetaQ_eq : thetaQ = TopologicalSpace.induced PsiQ Pi.topologicalSpace := by
  apply le_antisymm
  · rw [← continuous_iff_le_induced]
    refine @continuous_pi ℝ ℚ (fun _ : ℚ => Circ) thetaQ (fun _ => circTop) _ (fun q => ?_)
    exact theta_cont_of_mem _ (cmulHom (q : ℝ)) ⟨q, fun y => rfl⟩
  · unfold thetaQ theta
    refine le_iInf fun χ => ?_
    obtain ⟨q, hq⟩ := χ.2
    have : ((χ : Chars) : ℝ → Circ) = (fun f : ℚ → Circ => f q) ∘ PsiQ := funext fun x => hq x
    rw [this, ← induced_compose]
    exact induced_mono (continuous_iff_le_induced.mp (continuous_apply q))

lemma metrizable_of_embedding {X : Type} (tX : TopologicalSpace X) (f : X → (ℚ → Circ))
    (hf : @Topology.IsEmbedding X (ℚ → Circ) tX piQ f) : @TopologicalSpace.MetrizableSpace X tX := by
  letI := tX
  haveI : TopologicalSpace.MetrizableSpace (ℚ → Circ) := inferInstance
  exact hf.metrizableSpace

theorem thetaQ_metrizable : @TopologicalSpace.MetrizableSpace ℝ thetaQ := by
  have hinj : Function.Injective PsiQ := by
    intro x y hxy
    by_contra hne
    obtain ⟨χ, ⟨q, hq⟩, hχ⟩ := HQ_separates (x - y) (sub_ne_zero.mpr hne)
    apply hχ
    rw [hq, mul_sub, AddCircle.coe_sub]
    have := congrFun hxy q
    simp only [PsiQ] at this
    rw [this, sub_self]
  have hind : @Topology.IsInducing ℝ (ℚ → Circ) thetaQ piQ PsiQ :=
    @Topology.IsInducing.mk ℝ (ℚ → Circ) thetaQ piQ PsiQ thetaQ_eq
  have hemb : @Topology.IsEmbedding ℝ (ℚ → Circ) thetaQ piQ PsiQ :=
    @Topology.IsEmbedding.mk ℝ (ℚ → Circ) thetaQ piQ PsiQ hind hinj
  exact metrizable_of_embedding thetaQ PsiQ hemb

/-- Under (F1): `C_{θ_ℚ} = ℚ`. -/
theorem thetaQ_scalar (hD : DualThetaFact) (a : ℝ) :
    Continuous[thetaQ, thetaQ] (fun x : ℝ => a * x) ↔ ∃ q : ℚ, a = q := by
  rw [theta_scalar hD HQ HQ_separates]
  constructor
  · intro h
    have hχ : (cmulHom 1 : Chars) ∈ HQ := ⟨1, fun y => by simp [cmulHom_apply]⟩
    obtain ⟨q, hq⟩ := h _ hχ
    refine ⟨q, ?_⟩
    have : ∀ x : ℝ, (((a - q) * x : ℝ) : Circ) = 0 := by
      intro x
      have hx := hq x
      have hx2 : ((a * x : ℝ) : Circ) = (((q : ℝ) * x : ℝ) : Circ) := by
        simpa [cmulHom_apply] using hx
      rw [sub_mul, AddCircle.coe_sub, hx2, sub_self]
    exact sub_eq_zero.mp (pc_zero _ this)
  · rintro ⟨q, rfl⟩ χ ⟨r, hr⟩
    refine ⟨r * q, fun x => ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft]
    rw [hr]; congr 1; push_cast; ring

/-- Under (F1)+(F2): `θ_ℚ` is minimal among Hausdorff TVGQ topologies. -/
theorem thetaQ_minimal (hD : PrecompactDuality) (τ : TopologicalSpace ℝ)
    (hg : @IsTopologicalAddGroup ℝ τ _) (ht : @T2Space ℝ τ) (hq : ∀ q : ℚ, Continuous[τ, τ] (mq q : ℝ → ℝ))
    (hle : thetaQ ≤ τ) : τ = thetaQ := by
  have hp : Precompact τ := precompact_of_le hle (theta_precompact _)
  obtain ⟨H', ⟨hs', hr'⟩, rfl⟩ := (classification hD).2.1 τ ⟨hg, ht, hp, hq⟩
  have hHle : H' ≤ HQ := (theta_le_iff hD.dual_theta H' HQ hs' HQ_separates).1 hle
  -- `H'` is nonzero, hence contains some `χ_q`, `q ≠ 0`, hence all of `H_ℚ`
  obtain ⟨χ, hχ, hne⟩ := hs' 1 one_ne_zero
  obtain ⟨q, hqχ⟩ := hHle hχ
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hne
    rw [hqχ]; simp
  have hHQle : HQ ≤ H' := by
    rintro ψ ⟨r, hr⟩
    have := hr' χ hχ (r / q)
    have e : ψ = χ.comp (mq (r / q)) := by
      ext x
      show ψ x = χ (mq (r / q) x)
      rw [show mq (r / q) x = ((r / q : ℚ) : ℝ) * x from congrFun (mq_real _) x, hqχ, hr]
      congr 1; push_cast; field_simp
    rw [e]; exact this
  have : H' = HQ := le_antisymm hHle hHQle
  rw [this]

/-- Under (F1): `θ_ℚ` is strictly coarser than the Bohr topology `θ_{H_ℝ} = init{p(b x)}`. -/
theorem thetaQ_lt_bohr (hD : DualThetaFact) : theta (HR : Set Chars) < thetaQ := by
  refine lt_of_le_of_ne ((theta_le_iff hD HQ HR HQ_separates HR_separates).2 HQ_le_HR) (fun heq => ?_)
  have := theta_injective hD HR HQ HR_separates HQ_separates heq
  have hmem : (cmulHom (Real.sqrt 2) : Chars) ∈ HR := ⟨Real.sqrt 2, fun y => rfl⟩
  rw [this] at hmem
  obtain ⟨q, hq⟩ := hmem
  have : ∀ x : ℝ, ((((Real.sqrt 2 - q) * x : ℝ)) : Circ) = 0 := by
    intro x
    have hx := hq x
    rw [cmulHom_apply] at hx
    rw [sub_mul, AddCircle.coe_sub, hx, sub_self]
  have h2 := sub_eq_zero.mp (pc_zero _ this)
  exact irrational_sqrt_two ⟨q, h2.symm⟩

/-! ### `β_{f,S} = θ_{H_{f,S}}` (an unconditional instance) -/

/-- `H_{f,S} = { x ↦ p(c x + f(a x)) : c ∈ ℝ, a ∈ S }` as a subgroup of `𝒜`. -/
def Hset (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) : AddSubgroup Chars where
  carrier := {χ | ∃ (c a : ℝ), a ∈ S ∧ ∀ x : ℝ, χ x = chiH f c a x}
  zero_mem' := ⟨0, 0, S.zero_mem, fun x => by simp [chiH]⟩
  add_mem' := by
    rintro χ χ' ⟨c, a, ha, h⟩ ⟨c', a', ha', h'⟩
    refine ⟨c + c', a + a', S.add_mem ha ha', fun x => ?_⟩
    simp only [AddMonoidHom.add_apply]
    rw [h, h']
    unfold chiH
    rw [← AddCircle.coe_add]
    congr 1; rw [add_mul, add_mul, map_add]; push_cast; ring
  neg_mem' := by
    rintro χ ⟨c, a, ha, h⟩
    refine ⟨-c, -a, S.neg_mem ha, fun x => ?_⟩
    simp only [AddMonoidHom.neg_apply]
    rw [h]
    unfold chiH
    rw [← AddCircle.coe_neg]
    congr 1; rw [neg_mul, neg_mul, map_neg]; push_cast; ring

/-- **`β_{f,S} = θ_{H_{f,S}}`.** -/
theorem betaT_eq_theta (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    betaT f S = theta (Hset f S : Set Chars) := by
  apply le_antisymm
  · -- `β ≤ θ`: every `χ ∈ H_{f,S}` is `β`-continuous
    unfold theta
    refine le_iInf fun χ => ?_
    obtain ⟨c, a, ha, h⟩ := χ.2
    have hc : @Continuous ℝ Circ (betaT f S) circTop (χ : Chars) := by
      have : ((χ : Chars) : ℝ → Circ) = chiH f c a := funext h
      rw [this]; exact chiH_cont_sigma f S c a ha
    exact continuous_iff_le_induced.mp hc
  · -- `θ ≤ β`: the generators of `β` are in `H_{f,S}`
    unfold betaT
    refine le_inf (le_iInf fun b => ?_) (le_iInf fun a => ?_)
    · have hmem : (cmulHom b : Chars) ∈ Hset f S := ⟨b, 0, S.zero_mem, fun x => by
        simp [cmulHom_apply, chiH]⟩
      exact iInf_le_of_le ⟨cmulHom b, hmem⟩ le_rfl
    · have hmem : (pfHom f (a : ℝ) : Chars) ∈ Hset f S := ⟨0, a, a.2, fun x => by
        simp [pfHom_apply, chiH]⟩
      exact iInf_le_of_le ⟨pfHom f (a : ℝ), hmem⟩ le_rfl

/-- An unconditional instance of (F1): the dual of `θ_{H_{f,S}} = β_{f,S}` is `H_{f,S}`. -/
theorem dual_theta_Hset (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (χ : Chars) :
    @Continuous ℝ Circ (theta (Hset f S : Set Chars)) circTop χ ↔ χ ∈ Hset f S := by
  rw [← betaT_eq_theta]
  exact dual_beta f S χ

end LeanCheck
