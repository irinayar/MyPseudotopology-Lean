import LeanCheck.ChainTransferOpen

/-!
# The TVGQ transfer (Theorem `transfer-q` of TVGQ-v7)

Here only rational dilations are required.  For a topology `δ` on `ℚ`,
`S_f(δ) = init{ id : ℝ → ℝ_usual, f : ℝ → (ℚ, δ) }` (called `Tq f δ`).  With `H_{f,ℚ} = { p(c x + r f(x)) }`:

* `Tq f δ` is a Hausdorff locally quasi-convex group topology with continuous rational dilations;
* its continuous characters are exactly `H_{f,ℚ}` when `δ` has dual `Γ`;
* `f : (ℝ, Tq f δ) → (ℚ, δ)` is an open quotient map; `δ ↦ Tq f δ` is an order embedding, preserving joins,
  and `Tq f γ₀ = σ_{f,ℚ}`;
* an extra character of `δ₁ ∨ δ₂` transfers to an extra character of `Tq f δ₁ ∨ Tq f δ₂` outside `H_{f,ℚ}`.
-/

namespace LeanCheck

open Filter Topology

/-- `S_f(δ) = init{id, f}`. -/
noncomputable def Tq (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) : TopologicalSpace ℝ :=
  (inferInstance : TopologicalSpace ℝ) ⊓ TopologicalSpace.induced f δ

lemma Tq_le_usual (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) : Tq f δ ≤ uR := inf_le_left

lemma f_cont_Tq (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) : Continuous[Tq f δ, δ] f :=
  continuous_iff_le_induced.mpr inf_le_right

lemma Tq_group (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (h : @IsTopologicalAddGroup ℚ δ _) :
    @IsTopologicalAddGroup ℝ (Tq f δ) _ := by
  unfold Tq
  letI : TopologicalSpace ℚ := δ
  haveI : IsTopologicalAddGroup ℚ := h
  exact isTopologicalAddGroup_inf inferInstance (isTopologicalAddGroup_induced f)

lemma Tq_t2 (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) : @T2Space ℝ (Tq f δ) := by
  have hc : Continuous[Tq f δ, (inferInstance : TopologicalSpace ℝ)] (id : ℝ → ℝ) :=
    continuous_iff_le_induced.mpr (by rw [induced_id]; exact Tq_le_usual f δ)
  exact @T2Space.of_injective_continuous ℝ ℝ (Tq f δ) _ _ id Function.injective_id hc

/-- Rational dilations are `Tq f δ`-continuous (the TVGQ property). -/
lemma Tq_rat_dilation (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ)
    (hs : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x)) (q : ℚ) :
    Continuous[Tq f δ, Tq f δ] (fun x : ℝ => (q : ℝ) * x) := by
  have h1 : Continuous[Tq f δ, (inferInstance : TopologicalSpace ℝ)] (fun x : ℝ => (q : ℝ) * x) :=
    continuous_inf_dom_left (continuous_const.mul continuous_id)
  have h2 : Continuous[Tq f δ, TopologicalSpace.induced f δ] (fun x : ℝ => (q : ℝ) * x) := by
    rw [continuous_induced_rng]
    have : (f ∘ fun x : ℝ => (q : ℝ) * x) = (fun s : ℚ => q * s) ∘ f := by
      funext x; simp [f_ratmul]
    rw [this]
    exact @Continuous.comp ℝ ℚ ℚ (Tq f δ) δ δ _ _ (hs q) (f_cont_Tq f δ)
  exact continuous_inf_rng.2 ⟨h1, h2⟩

lemma Tq_mono (f : ℝ →+ ℚ) {δ δ' : TopologicalSpace ℚ} (h : δ ≤ δ') : Tq f δ ≤ Tq f δ' :=
  inf_le_inf_left _ (induced_mono h)

lemma Tq_inf (f : ℝ →+ ℚ) (δ₁ δ₂ : TopologicalSpace ℚ) :
    Tq f (δ₁ ⊓ δ₂) = Tq f δ₁ ⊓ Tq f δ₂ := by
  unfold Tq
  rw [induced_inf]
  apply le_antisymm
  · exact le_inf (inf_le_inf_left _ inf_le_left) (inf_le_inf_left _ inf_le_right)
  · exact le_inf (inf_le_left.trans inf_le_left) (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))

lemma lqc_Tq (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (h : LocQC δ) : LocQC (Tq f δ) :=
  lqc_inf _ _ lqc_uR (lqc_induced f δ h)

/-! ### Kernel of `f` and neighbourhoods -/

/-- The one-element family `b = (1)`, so that `Hmap f b` is `x ↦ f x`. -/
def b1 : Unit → ℝ := fun _ => 1

lemma mem_ker_b1 (f : ℝ →+ ℚ) (x : ℝ) : x ∈ (Hmap f b1).ker ↔ f x = 0 := by
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h
    have := congrFun h ()
    simpa [Hmap_apply, b1] using this
  · intro h
    funext j
    simp [Hmap_apply, b1, h]

/-- Every `t` is `f`-attained by a `usual`-small real number. -/
lemma exists_small_pre (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (ε : ℝ) (hε : 0 < ε) (t : ℚ) :
    ∃ n : ℝ, f n = 0 ∧ |(t : ℝ) * u + n| < ε := by
  obtain ⟨n, hnN, hn⟩ := (Hker_dense f b1).exists_mem_open
    (isOpen_Ioo : IsOpen (Set.Ioo (-((t : ℝ) * u) - ε) (-((t : ℝ) * u) + ε)))
    ⟨-((t : ℝ) * u), by constructor <;> linarith⟩
  refine ⟨n, (mem_ker_b1 f n).1 hnN, ?_⟩
  rw [abs_lt]; constructor <;> linarith [hn.1, hn.2]

theorem tq_nhds_sub (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (S : Set ℝ)
    (hS : S ∈ @nhds ℝ (Tq f δ) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ U : Set ℚ, U ∈ @nhds ℚ δ 0 ∧ {x : ℝ | |x| < ε ∧ f x ∈ U} ⊆ S := by
  unfold Tq at hS
  rw [nhds_inf] at hS
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_inf_iff_superset.mp hS
  rw [nhds_induced, map_zero] at ht2
  obtain ⟨U, hU, hUt⟩ := Filter.mem_comap.mp ht2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht1
  refine ⟨ε, hε, U, hU, ?_⟩
  rintro x ⟨hx, hxU⟩
  exact hsub ⟨hball (by simpa [Metric.mem_ball, dist_zero_right] using hx), hUt hxU⟩

/-- The `f`-image of a `Tq f δ`-neighbourhood of `0` is a `δ`-neighbourhood of `0`. -/
theorem Tq_image_nhds (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ : TopologicalSpace ℚ)
    (S : Set ℝ) (hS : S ∈ @nhds ℝ (Tq f δ) 0) : (f : ℝ → ℚ) '' S ∈ @nhds ℚ δ 0 := by
  obtain ⟨ε, hε, U, hU, hsub⟩ := tq_nhds_sub f δ S hS
  refine Filter.mem_of_superset hU ?_
  intro t ht
  obtain ⟨n, hn, hlt⟩ := exists_small_pre f u hu ε hε t
  have hft : f ((t : ℝ) * u + n) = t := by rw [map_add, hn, add_zero, f_ratmul, hu, mul_one]
  exact ⟨(t : ℝ) * u + n, hsub ⟨hlt, by rw [hft]; exact ht⟩, hft⟩

/-- A homomorphism of topological groups that maps neighbourhoods of `0` to neighbourhoods of `0` is open. -/
theorem isOpenMap_of_image_nhds {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (tX : TopologicalSpace X) (tY : TopologicalSpace Y)
    (hX : @IsTopologicalAddGroup X tX _) (hY : @IsTopologicalAddGroup Y tY _) (g : X →+ Y)
    (h : ∀ S ∈ @nhds X tX 0, (g : X → Y) '' S ∈ @nhds Y tY 0) : @IsOpenMap X Y tX tY g := by
  letI := tX
  letI := tY
  haveI := hX
  haveI := hY
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hxO, rfl⟩
  have hnh : (fun z : X => z + x) ⁻¹' O ∈ 𝓝 (0 : X) :=
    (continuous_id.add continuous_const : Continuous fun z : X => z + x).continuousAt.preimage_mem_nhds
      (by simpa using hO.mem_nhds hxO)
  have himg := h _ hnh
  have h2 : (fun t : Y => t - g x) ⁻¹' ((g : X → Y) '' ((fun z : X => z + x) ⁻¹' O)) ∈ 𝓝 (g x) :=
    (continuous_id.sub continuous_const : Continuous fun t : Y => t - g x).continuousAt.preimage_mem_nhds
      (by simpa using himg)
  refine Filter.mem_of_superset h2 ?_
  rintro t ⟨z, hz, hzt⟩
  refine ⟨z + x, hz, ?_⟩
  rw [map_add, hzt]; simp

/-- **`f : (ℝ, S_f δ) → (ℚ, δ)` is an open continuous surjection.** -/
theorem Tq_isOpenMap (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ : TopologicalSpace ℚ)
    (hg : @IsTopologicalAddGroup ℚ δ _) : @IsOpenMap ℝ ℚ (Tq f δ) δ f :=
  isOpenMap_of_image_nhds (Tq f δ) δ (Tq_group f δ hg) hg f (Tq_image_nhds f u hu δ)

/-- `δ` is the quotient topology of `S_f δ` along `f`. -/
theorem Tq_coinduced (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ : TopologicalSpace ℚ)
    (hg : @IsTopologicalAddGroup ℚ δ _) : δ = TopologicalSpace.coinduced f (Tq f δ) := by
  have hopen := Tq_isOpenMap f u hu δ hg
  have hsurj := f_surjective f u hu
  apply le_antisymm
  · intro W hW
    have hpre : IsOpen[Tq f δ] (f ⁻¹' W) := hW
    have : W = f '' (f ⁻¹' W) := (hsurj.image_preimage W).symm
    rw [this]
    exact hopen _ hpre
  · rw [← continuous_iff_coinduced_le]
    exact f_cont_Tq f δ

/-- **Order embedding**: `S_f δ₁ ≤ S_f δ₂ ↔ δ₁ ≤ δ₂`. -/
theorem Tq_le_iff (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ₁ δ₂ : TopologicalSpace ℚ)
    (hg₁ : @IsTopologicalAddGroup ℚ δ₁ _) (hg₂ : @IsTopologicalAddGroup ℚ δ₂ _) :
    Tq f δ₁ ≤ Tq f δ₂ ↔ δ₁ ≤ δ₂ := by
  constructor
  · intro h
    rw [Tq_coinduced f u hu δ₁ hg₁, Tq_coinduced f u hu δ₂ hg₂]
    exact coinduced_mono h
  · exact Tq_mono f

/-! ### The dual of `S_f δ` is exactly `H_{f,ℚ}` -/

/-- `H_{f,ℚ}`-characters are `S_f δ`-continuous if `s ↦ p(r s)` is `δ`-continuous. -/
theorem chiHQ_continuous (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (r : ℚ)
    (hr : @Continuous ℚ Circ δ _ (fun s : ℚ => (((r * s : ℚ) : ℝ) : Circ))) (c : ℝ) :
    @Continuous ℝ Circ (Tq f δ) circTop (chiH f c (r : ℝ)) := by
  have h1 : Continuous[Tq f δ, _] (fun x : ℝ => ((c * x : ℝ) : Circ)) :=
    continuous_inf_dom_left (continuous_coe_circ.comp (continuous_const.mul continuous_id))
  have h2 : Continuous[Tq f δ, _] (fun x : ℝ => (((r * f x : ℚ) : ℝ) : Circ)) :=
    @Continuous.comp ℝ ℚ Circ (Tq f δ) δ _ _ _ hr (f_cont_Tq f δ)
  have : chiH f c (r : ℝ) = fun x : ℝ => ((c * x : ℝ) : Circ) + (((r * f x : ℚ) : ℝ) : Circ) := by
    funext x
    simp only [chiH, f_ratmul]
    rw [AddCircle.coe_add]
  rw [this]
  exact @Continuous.add Circ _ _ _ ℝ (Tq f δ) _ _ h1 h2

/-- **The dual of `S_f δ` is contained in `H_{f,ℚ}`** (δ a group topology with dual `Γ`). -/
theorem dual_Tq_mp (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ : TopologicalSpace ℚ)
    (hg : @IsTopologicalAddGroup ℚ δ _)
    (hdual : ∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ δ _ ψ →
      ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ))
    (χ : ℝ →+ Circ) (hχ : @Continuous ℝ Circ (Tq f δ) circTop χ) :
    ∃ (c : ℝ) (r : ℚ), ∀ x : ℝ, χ x = chiH f c (r : ℝ) x := by
  have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (χ 0) := by
    rw [map_zero]
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  obtain ⟨ε, hε, U, hU, hsub⟩ := tq_nhds_sub f δ _
    ((@Continuous.continuousAt ℝ Circ (Tq f δ) circTop χ 0 hχ) hS)
  have hsmall : ∀ x ∈ (Hmap f b1).ker, |x| < ε → ‖χ x‖ < 1 / 4 := by
    intro x hx hxε
    have : f x = 0 := (mem_ker_b1 f x).1 hx
    exact hsub ⟨hxε, by rw [this]; exact mem_of_mem_nhds hU⟩
  obtain ⟨c, hc⟩ := linearize χ (Hmap f b1).ker ε hε (Hker_qmul f b1) hsmall (Hker_dense f b1)
  let χ' : ℝ →+ Circ := χ + cmulHom (-c)
  have hχ'x : ∀ x, χ' x = χ x - ((c * x : ℝ) : Circ) := by
    intro x
    show χ x + ((-c * x : ℝ) : Circ) = _
    rw [neg_mul, AddCircle.coe_neg, sub_eq_add_neg]
  have hχ' : @Continuous ℝ Circ (Tq f δ) circTop χ' :=
    @Continuous.add Circ _ _ _ ℝ (Tq f δ) _ _ hχ
      (continuous_inf_dom_left (continuous_coe_circ.comp (continuous_const.mul continuous_id)))
  have hker0 : ∀ x, f x = 0 → χ' x = 0 := by
    intro x hx
    rw [hχ'x, hc x ((mem_ker_b1 f x).2 hx), sub_self]
  obtain ⟨ε', hε', U', hU', hsub'⟩ := tq_nhds_sub f δ _
    ((@Continuous.continuousAt ℝ Circ (Tq f δ) circTop χ' 0 hχ')
      (show {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (χ' 0) by
        rw [map_zero]
        exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)))
  let θ : ℚ →+ Circ := AddMonoidHom.mk' (fun t : ℚ => χ' ((t : ℝ) * u)) (by intro s t; simp [add_mul])
  have hθ : ∀ t, θ t = χ' ((t : ℝ) * u) := fun t => rfl
  have hθcont : @Continuous ℚ Circ δ _ θ := by
    letI : TopologicalSpace ℚ := δ
    haveI : IsTopologicalAddGroup ℚ := hg
    refine continuous_of_quarter_gen θ hU' ?_
    intro t ht
    obtain ⟨n, hn, hlt⟩ := exists_small_pre f u hu ε' hε' t
    have hft : f ((t : ℝ) * u + n) = t := by rw [map_add, hn, add_zero, f_ratmul, hu, mul_one]
    have := hsub' ⟨hlt, by rw [hft]; exact ht⟩
    have e : χ' ((t : ℝ) * u + n) = θ t := by rw [map_add, hker0 n hn, add_zero, hθ]
    simpa [e] using this
  obtain ⟨r, hr⟩ := hdual θ hθcont
  refine ⟨c, r, fun x => ?_⟩
  have hz : f (x - ((f x : ℚ) : ℝ) * u) = 0 := f_fiber f u hu x
  have hx : χ' x = θ (f x) := by
    have h0 := hker0 _ hz
    rw [map_sub] at h0
    rw [hθ]; exact sub_eq_zero.mp h0
  have h1 : χ x = χ' x + ((c * x : ℝ) : Circ) := by rw [hχ'x]; abel
  rw [h1, hx, hr]
  unfold chiH
  rw [f_ratmul, AddCircle.coe_add, add_comm]

theorem dual_Tq (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ : TopologicalSpace ℚ)
    (hg : @IsTopologicalAddGroup ℚ δ _)
    (hdual : ∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ δ _ ψ ↔
      ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ))
    (χ : ℝ →+ Circ) :
    @Continuous ℝ Circ (Tq f δ) circTop χ ↔ ∃ (c : ℝ) (r : ℚ), ∀ x : ℝ, χ x = chiH f c (r : ℝ) x := by
  constructor
  · exact dual_Tq_mp f u hu δ hg (fun ψ hψ => (hdual ψ).mp hψ) χ
  · rintro ⟨c, r, h⟩
    have hr : @Continuous ℚ Circ δ _ (fun s : ℚ => (((r * s : ℚ) : ℝ) : Circ)) := by
      have := (hdual ((AddCommGroup.torsion Circ).subtype.comp (piHom.comp (AddMonoidHom.mulLeft r)))).mpr
        ⟨r, fun s => by simp [piHom_coe]⟩
      exact this
    have : (χ : ℝ → Circ) = chiH f c (r : ℝ) := funext h
    rw [this]
    exact chiHQ_continuous f δ r hr c

/-- **Obstruction transfer for `S_f`.** -/
theorem transferQ_obstruction (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ₁ δ₂ : TopologicalSpace ℚ)
    (ψ : ℚ →+ Circ) (hψ : @Continuous ℚ Circ (δ₁ ⊓ δ₂) _ ψ)
    (hne : ∀ r : ℚ, ∃ s : ℚ, ψ s ≠ (((r * s : ℚ) : ℝ) : Circ)) :
    ∃ φ : ℝ →+ Circ, @Continuous ℝ Circ (Tq f δ₁ ⊓ Tq f δ₂) circTop φ ∧
      ¬ ∃ (c : ℝ) (r : ℚ), ∀ x : ℝ, φ x = chiH f c (r : ℝ) x := by
  refine ⟨ψ.comp f, ?_, ?_⟩
  · rw [← Tq_inf]
    exact @Continuous.comp ℝ ℚ Circ (Tq f (δ₁ ⊓ δ₂)) (δ₁ ⊓ δ₂) _ _ _ hψ (f_cont_Tq f _)
  · rintro ⟨c, r, h⟩
    have hE : ∀ x : ℝ, f x = 0 → c * x = 0 := by
      intro x hx
      apply int_of_all_div
      intro n hn
      have hy : f (((1 / (n : ℚ) : ℚ) : ℝ) * x) = 0 := by rw [f_ratmul, hx, mul_zero]
      have h0 := h (((1 / (n : ℚ) : ℚ) : ℝ) * x)
      simp only [AddMonoidHom.comp_apply, hy, map_zero] at h0
      have h0' := h0.symm
      unfold chiH at h0'
      have hfy : f ((r : ℝ) * (((1 / (n : ℚ) : ℚ) : ℝ) * x)) = 0 := by
        rw [f_ratmul, hy, mul_zero]
      have hsum : c * (((1 / (n : ℚ) : ℚ) : ℝ) * x) + ((f ((r : ℝ) * (((1 / (n : ℚ) : ℚ) : ℝ) * x)) : ℚ) : ℝ)
          = c * (((1 / (n : ℚ) : ℚ) : ℝ) * x) := by rw [hfy]; simp
      have h0'' : ((c * (((1 / (n : ℚ) : ℚ) : ℝ) * x) : ℝ) : Circ) = 0 := by
        rw [hsum] at h0'; exact h0'
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h0''
      refine ⟨k, ?_⟩
      rw [zsmul_eq_mul, mul_one] at hk
      push_cast at hk
      have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [hk]
      field_simp
    have hc : c = 0 := by
      by_contra hc
      apply ker_uncountable f u hu
      refine (Set.countable_singleton (0 : ℝ)).mono ?_
      intro x hx
      have := hE x hx
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hc
      · exact h
    subst hc
    obtain ⟨s, hs⟩ := hne r
    apply hs
    have hx : f (((s : ℚ) : ℝ) * u) = s := by rw [f_ratmul, hu, mul_one]
    have h1 := h (((s : ℚ) : ℝ) * u)
    simp only [AddMonoidHom.comp_apply, hx] at h1
    rw [h1]
    unfold chiH
    rw [f_ratmul, hx]
    congr 1
    push_cast; ring

/-! ### `S_f(γ₀) = σ_{f,ℚ}`, join compatibility, and the capstone -/

/-- `γ₀ = init{ q ↦ p(r q) : r ∈ ℚ }` on `ℚ`. -/
noncomputable def gamma0 : TopologicalSpace ℚ :=
  ⨅ r : ℚ, TopologicalSpace.induced (fun s : ℚ => (((r * s : ℚ) : ℝ) : Circ)) circTop

/-- `σ_{f,ℚ} = tu ∨ β_{f,ℚ}`, with `β_{f,ℚ} = init{ x ↦ p(b x), x ↦ p(f(a x)) : b ∈ ℝ, a ∈ ℚ }`. -/
noncomputable def sigmaQ (f : ℝ →+ ℚ) : TopologicalSpace ℝ :=
  (inferInstance : TopologicalSpace ℝ) ⊓
    ((⨅ b : ℝ, TopologicalSpace.induced (fun x : ℝ => ((b * x : ℝ) : Circ)) circTop) ⊓
      ⨅ a : ℚ, TopologicalSpace.induced (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop)

/-- **`S_f(γ₀) = σ_{f,ℚ}`.** -/
theorem Tq_gamma0 (f : ℝ →+ ℚ) : Tq f gamma0 = sigmaQ f := by
  have hB : (inferInstance : TopologicalSpace ℝ) ≤
      ⨅ b : ℝ, TopologicalSpace.induced (fun x : ℝ => ((b * x : ℝ) : Circ)) circTop :=
    le_iInf fun b => continuous_iff_le_induced.mp
      (continuous_coe_circ.comp (continuous_const.mul continuous_id))
  have hA : TopologicalSpace.induced f gamma0 =
      ⨅ a : ℚ, TopologicalSpace.induced (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop := by
    unfold gamma0
    rw [induced_iInf]
    refine iInf_congr fun a => ?_
    rw [induced_compose]
    congr 1
    funext x
    simp [f_ratmul]
  unfold sigmaQ Tq
  rw [hA, ← inf_assoc, inf_eq_left.mpr hB]

/-- **Join compatibility for the TVGQ transfer**: `S_f δ₁ ∨ S_f δ₂` has dual exactly `H_{f,ℚ}`
iff `δ₁ ∨ δ₂` has dual exactly `Γ`. -/
theorem Tq_join_compat (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ₁ δ₂ : TopologicalSpace ℚ)
    (hg₁ : @IsTopologicalAddGroup ℚ δ₁ _) (hg₂ : @IsTopologicalAddGroup ℚ δ₂ _)
    (hd₁ : ∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ δ₁ _ ψ ↔ ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ))
    (hd₂ : ∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ δ₂ _ ψ ↔ ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ)) :
    (∀ χ : ℝ →+ Circ, @Continuous ℝ Circ (Tq f δ₁ ⊓ Tq f δ₂) circTop χ ↔
        ∃ (c : ℝ) (r : ℚ), ∀ x : ℝ, χ x = chiH f c (r : ℝ) x) ↔
    (∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ (δ₁ ⊓ δ₂) _ ψ ↔
        ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ)) := by
  constructor
  · intro H ψ
    constructor
    · intro hψ
      by_contra hnot
      push_neg at hnot
      obtain ⟨φ, hφ, hφne⟩ := transferQ_obstruction f u hu δ₁ δ₂ ψ hψ hnot
      exact hφne ((H φ).mp hφ)
    · rintro ⟨r, hr⟩
      have h1 : @Continuous ℚ Circ δ₁ _ ψ := (hd₁ ψ).mpr ⟨r, hr⟩
      exact continuous_inf_dom_left h1
  · intro H χ
    have hg : @IsTopologicalAddGroup ℚ (δ₁ ⊓ δ₂) _ := isTopologicalAddGroup_inf hg₁ hg₂
    rw [← Tq_inf]
    exact dual_Tq f u hu (δ₁ ⊓ δ₂) hg H χ

/-- **The TVGQ transfer, formal capstone.**  For every coefficient function `f` there are two Hausdorff, locally
quasi-convex group topologies on `ℝ`, finer than usual, with continuous rational dilations, with continuous
character group exactly `H_{f,ℚ}`, whose join has a continuous character outside `H_{f,ℚ}`.  Hence no greatest
compatible TVGQ topology exists for `(ℝ, H_{f,ℚ})`. -/
theorem transfer_capstone_Q (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    ∃ T₁ T₂ : TopologicalSpace ℝ,
      @IsTopologicalAddGroup ℝ T₁ _ ∧ @IsTopologicalAddGroup ℝ T₂ _ ∧
      @T2Space ℝ T₁ ∧ @T2Space ℝ T₂ ∧ LocQC T₁ ∧ LocQC T₂ ∧
      T₁ ≤ uR ∧ T₂ ≤ uR ∧
      (∀ q : ℚ, Continuous[T₁, T₁] (fun x : ℝ => (q : ℝ) * x)) ∧
      (∀ q : ℚ, Continuous[T₂, T₂] (fun x : ℝ => (q : ℝ) * x)) ∧
      (∀ χ : ℝ →+ Circ, @Continuous ℝ Circ T₁ circTop χ ↔
        ∃ (c : ℝ) (r : ℚ), ∀ x : ℝ, χ x = chiH f c (r : ℝ) x) ∧
      (∀ χ : ℝ →+ Circ, @Continuous ℝ Circ T₂ circTop χ ↔
        ∃ (c : ℝ) (r : ℚ), ∀ x : ℝ, χ x = chiH f c (r : ℝ) x) ∧
      ∃ φ : ℝ →+ Circ, @Continuous ℝ Circ (T₁ ⊓ T₂) circTop φ ∧
        ¬ ∃ (c : ℝ) (r : ℚ), ∀ x : ℝ, φ x = chiH f c (r : ℝ) x := by
  obtain ⟨g1, g2, hg1, hg2, -, -, hl1, hl2, hs1, hs2, hd1, hd2, ψ, hψ, hne⟩ := lift_capstone_lqc
  obtain ⟨φ, hφ, hφne⟩ := transferQ_obstruction f u hu g1 g2 ψ hψ hne
  exact ⟨Tq f g1, Tq f g2, Tq_group f g1 hg1, Tq_group f g2 hg2, Tq_t2 f g1, Tq_t2 f g2,
    lqc_Tq f g1 hl1, lqc_Tq f g2 hl2, Tq_le_usual f g1, Tq_le_usual f g2,
    Tq_rat_dilation f g1 hs1, Tq_rat_dilation f g2 hs2,
    dual_Tq f u hu g1 hg1 hd1, dual_Tq f u hu g2 hg2 hd2, φ, hφ, hφne⟩

end LeanCheck
