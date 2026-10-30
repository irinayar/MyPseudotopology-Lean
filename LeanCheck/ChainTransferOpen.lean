import LeanCheck.ChainLQC

/-!
# Openness of `f` and order reflection (second half of `transfer-v8`)

For `δ` a group topology on `ℚ` with continuous rational multiplications and `f u = 1`:

* `Tf_isOpenMap`   : `f : (ℝ, T_f δ) → (ℚ, δ)` is an open map (and surjective, continuous);
* `Tf_coinduced`   : `δ` is exactly the quotient topology of `T_f δ` along `f`;
* `Tf_le_iff`      : `T_f δ₁ ≤ T_f δ₂ ↔ δ₁ ≤ δ₂` (the assignment `δ ↦ T_f δ` is an order embedding).
-/

namespace LeanCheck

open Filter Topology

/-- Basic neighbourhoods of `0` in `T_f(δ)`. -/
theorem tf_nhds_sub (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (S : Set ℝ)
    (hS : S ∈ @nhds ℝ (Tf f δ) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ I : Finset ℝ, ∃ U : ℝ → Set ℚ, (∀ a ∈ I, U a ∈ @nhds ℚ δ 0) ∧
      {x : ℝ | |x| < ε ∧ ∀ a ∈ I, f (a * x) ∈ U a} ⊆ S := by
  classical
  unfold Tf at hS
  rw [nhds_inf] at hS
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_inf_iff_superset.mp hS
  rw [nhds_iInf] at ht2
  obtain ⟨I, hI, V, hV, -, hs⟩ := Filter.mem_iInf'.mp ht2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht1
  have hex : ∀ a : ℝ, ∃ U : Set ℚ, U ∈ @nhds ℚ δ 0 ∧ fa f a ⁻¹' U ⊆ V a := by
    intro a
    have h := hV a
    rw [nhds_induced, map_zero] at h
    exact Filter.mem_comap.mp h
  choose U hU hUV using hex
  refine ⟨ε, hε, hI.toFinset, U, fun a _ => hU a, ?_⟩
  rintro x ⟨hx, hxU⟩
  apply hsub
  refine ⟨hball (by simpa [Metric.mem_ball, dist_zero_right] using hx), ?_⟩
  rw [hs.1]
  refine Set.mem_iInter₂.mpr (fun a ha => ?_)
  exact hUV a (hxU a (hI.mem_toFinset.mpr ha))

/-- The image under `f` of a `T_f(δ)`-neighbourhood of `0` is a `δ`-neighbourhood of `0`. -/
theorem Tf_image_nhds (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ : TopologicalSpace ℚ)
    (hg : @IsTopologicalAddGroup ℚ δ _) (hs : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x))
    (S : Set ℝ) (hS : S ∈ @nhds ℝ (Tf f δ) 0) : (f : ℝ → ℚ) '' S ∈ @nhds ℚ δ 0 := by
  classical
  obtain ⟨ε, hε, I, U, hU, hsub⟩ := tf_nhds_sub f δ S hS
  obtain ⟨κ, hκ, b, hli, hq⟩ := indep_reduction f (insert 1 I)
  have hq' : ∀ a : ℝ, ∃ q : κ → ℚ, a ∈ insert 1 I → ∀ x : ℝ, f (a * x) = ∑ j, q j * f (b j * x) := by
    intro a
    by_cases ha : a ∈ insert 1 I
    · obtain ⟨q, hq⟩ := hq a ha
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose Q hQ using hq'
  obtain ⟨W, hW, hbox⟩ := pi_box δ hg hs I U hU Q
  have hQ1 : ∀ x : ℝ, f x = ∑ j, Q 1 j * f (b j * x) := fun x => by
    have := hQ 1 (Finset.mem_insert_self _ _) x
    simpa using this
  obtain ⟨j0, hj0⟩ : ∃ j0, Q 1 j0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    have := hQ1 u
    simp [hall] at this
    rw [hu] at this
    exact one_ne_zero this
  letI : TopologicalSpace ℚ := δ
  haveI : IsTopologicalAddGroup ℚ := hg
  have hN' : (fun t : ℚ => (Q 1 j0)⁻¹ * t) ⁻¹' W j0 ∈ 𝓝 (0 : ℚ) := by
    have hc := (hs (Q 1 j0)⁻¹).continuousAt (x := 0)
    exact hc.preimage_mem_nhds (by simpa using hW j0)
  refine Filter.mem_of_superset hN' ?_
  intro t ht
  set y : κ → ℚ := Pi.single j0 ((Q 1 j0)⁻¹ * t) with hy
  have hyW : ∀ j, y j ∈ W j := by
    intro j
    by_cases hj : j = j0
    · subst hj; simpa [hy] using ht
    · simp only [hy, Pi.single_apply, hj, if_false]; exact mem_of_mem_nhds (hW j)
  obtain ⟨x0, hx0⟩ := Hmap_surj f b hli y
  obtain ⟨n, hnN, hn⟩ := (Hker_dense f b).exists_mem_open
    (isOpen_Ioo : IsOpen (Set.Ioo (-x0 - ε) (-x0 + ε))) ⟨-x0, by constructor <;> linarith⟩
  have hHx : ∀ j, f (b j * (x0 + n)) = y j := by
    intro j
    have h0 : f (b j * n) = 0 := by
      have := congrFun (AddMonoidHom.mem_ker.mp hnN) j
      simpa [Hmap_apply] using this
    have h1 : f (b j * x0) = y j := by
      have := congrFun hx0 j
      simpa [Hmap_apply] using this
    rw [mul_add, map_add, h0, add_zero, h1]
  refine ⟨x0 + n, hsub ⟨?_, ?_⟩, ?_⟩
  · rw [abs_lt]; constructor <;> linarith [hn.1, hn.2]
  · intro a ha
    rw [hQ a (Finset.mem_insert_of_mem ha) (x0 + n)]
    simp_rw [hHx]
    exact hbox y hyW a ha
  · show f (x0 + n) = t
    rw [hQ1]
    simp_rw [hHx]
    simp [hy, Pi.single_apply, hj0]

/-- **`f : (ℝ, T_f δ) → (ℚ, δ)` is an open map.** -/
theorem Tf_isOpenMap (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ : TopologicalSpace ℚ)
    (hg : @IsTopologicalAddGroup ℚ δ _) (hs : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x)) :
    @IsOpenMap ℝ ℚ (Tf f δ) δ f := by
  have hgT := Tf_group f δ hg
  letI : TopologicalSpace ℝ := Tf f δ
  haveI : IsTopologicalAddGroup ℝ := hgT
  letI : TopologicalSpace ℚ := δ
  haveI : IsTopologicalAddGroup ℚ := hg
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hxO, rfl⟩
  have hnh : (fun z : ℝ => z + x) ⁻¹' O ∈ 𝓝 (0 : ℝ) :=
    (continuous_id.add continuous_const : Continuous fun z : ℝ => z + x).continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hxO)
  have himg := Tf_image_nhds f u hu δ hg hs _ hnh
  have h2 : (fun t : ℚ => t - f x) ⁻¹' ((f : ℝ → ℚ) '' ((fun z : ℝ => z + x) ⁻¹' O)) ∈ 𝓝 (f x) :=
    (continuous_id.sub continuous_const : Continuous fun t : ℚ => t - f x).continuousAt.preimage_mem_nhds (by simpa using himg)
  refine Filter.mem_of_superset h2 ?_
  rintro t ⟨z, hz, hzt⟩
  refine ⟨z + x, hz, ?_⟩
  rw [map_add, hzt]; ring

lemma f_surjective (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) : Function.Surjective f := by
  intro q
  refine ⟨(q : ℝ) * u, ?_⟩
  rw [f_ratmul, hu, mul_one]

/-- `δ` is the quotient topology of `T_f δ` along `f`. -/
theorem Tf_coinduced (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ : TopologicalSpace ℚ)
    (hg : @IsTopologicalAddGroup ℚ δ _) (hs : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x)) :
    δ = TopologicalSpace.coinduced f (Tf f δ) := by
  have hopen := Tf_isOpenMap f u hu δ hg hs
  have hsurj := f_surjective f u hu
  apply le_antisymm
  · intro W hW
    -- `W` is open in the coinduced topology: `f ⁻¹' W` is `T_f δ`-open
    have hpre : IsOpen[Tf f δ] (f ⁻¹' W) := hW
    have : W = f '' (f ⁻¹' W) := (hsurj.image_preimage W).symm
    rw [this]
    exact hopen _ hpre
  · rw [← continuous_iff_coinduced_le]
    exact fa_cont f δ 1 |> fun h => by
      have : (f : ℝ → ℚ) = fa f 1 := by funext x; simp [fa_apply]
      rw [this]; exact h

/-- **Order embedding**: `T_f δ₁ ≤ T_f δ₂ ↔ δ₁ ≤ δ₂` (finer topologies on `ℚ` give finer topologies on `ℝ`,
and conversely). -/
theorem Tf_le_iff (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ₁ δ₂ : TopologicalSpace ℚ)
    (hg₁ : @IsTopologicalAddGroup ℚ δ₁ _) (hs₁ : ∀ s : ℚ, Continuous[δ₁, δ₁] (fun x : ℚ => s * x))
    (hg₂ : @IsTopologicalAddGroup ℚ δ₂ _) (hs₂ : ∀ s : ℚ, Continuous[δ₂, δ₂] (fun x : ℚ => s * x)) :
    Tf f δ₁ ≤ Tf f δ₂ ↔ δ₁ ≤ δ₂ := by
  constructor
  · intro h
    rw [Tf_coinduced f u hu δ₁ hg₁ hs₁, Tf_coinduced f u hu δ₂ hg₂ hs₂]
    exact coinduced_mono h
  · exact Tf_mono f

/-- `δ ↦ T_f δ` is injective on rationally scalar-continuous group topologies. -/
theorem Tf_injective (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (δ₁ δ₂ : TopologicalSpace ℚ)
    (hg₁ : @IsTopologicalAddGroup ℚ δ₁ _) (hs₁ : ∀ s : ℚ, Continuous[δ₁, δ₁] (fun x : ℚ => s * x))
    (hg₂ : @IsTopologicalAddGroup ℚ δ₂ _) (hs₂ : ∀ s : ℚ, Continuous[δ₂, δ₂] (fun x : ℚ => s * x))
    (h : Tf f δ₁ = Tf f δ₂) : δ₁ = δ₂ :=
  le_antisymm ((Tf_le_iff f u hu δ₁ δ₂ hg₁ hs₁ hg₂ hs₂).1 h.le)
    ((Tf_le_iff f u hu δ₂ δ₁ hg₂ hs₂ hg₁ hs₁).1 h.ge)

lemma scalar_inf (g1 g2 : TopologicalSpace ℚ) (hs1 : ∀ s : ℚ, Continuous[g1, g1] (fun x : ℚ => s * x))
    (hs2 : ∀ s : ℚ, Continuous[g2, g2] (fun x : ℚ => s * x)) (s : ℚ) :
    Continuous[g1 ⊓ g2, g1 ⊓ g2] (fun x : ℚ => s * x) := by
  have a1 : Continuous[g1 ⊓ g2, g1] (fun x : ℚ => s * x) :=
    continuous_inf_dom_left (t₂ := g2) (hs1 s)
  have a2 : Continuous[g1 ⊓ g2, g2] (fun x : ℚ => s * x) :=
    continuous_inf_dom_right (t₁ := g1) (hs2 s)
  exact (continuous_inf_rng (t₁ := g1 ⊓ g2) (t₂ := g1) (t₃ := g2)).2 ⟨a1, a2⟩

/-- **Transferred join and its quotient.**  For the incompatible pair `γ₁, γ₂` of `lift_capstone_lqc` on `ℚ`:
`f` is an open map from `T_f γ_i` onto `(ℚ, γ_i)`, `T_f γ₁ ∨ T_f γ₂ = T_f (γ₁ ∨ γ₂)`, `f` is an open map from
this join onto `(ℚ, γ₁ ∨ γ₂)`, and the rational join carries a continuous character outside `Γ`. -/
theorem transfer_join_quotient (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    ∃ g1 g2 : TopologicalSpace ℚ,
      @IsOpenMap ℝ ℚ (Tf f g1) g1 f ∧ @IsOpenMap ℝ ℚ (Tf f g2) g2 f ∧
      Tf f (g1 ⊓ g2) = Tf f g1 ⊓ Tf f g2 ∧
      @IsOpenMap ℝ ℚ (Tf f g1 ⊓ Tf f g2) (g1 ⊓ g2) f ∧
      ∃ ψ : ℚ →+ Circ, @Continuous ℚ Circ (g1 ⊓ g2) _ ψ ∧
        ∀ r : ℚ, ∃ s : ℚ, ψ s ≠ (((r * s : ℚ) : ℝ) : Circ) := by
  obtain ⟨g1, g2, hg1, hg2, -, -, -, -, hs1, hs2, -, -, ψ, hψ, hne⟩ := lift_capstone_lqc
  have hg12 : @IsTopologicalAddGroup ℚ (g1 ⊓ g2) _ := isTopologicalAddGroup_inf hg1 hg2
  have hopen := Tf_isOpenMap f u hu (g1 ⊓ g2) hg12 (scalar_inf g1 g2 hs1 hs2)
  rw [Tf_inf] at hopen
  exact ⟨g1, g2, Tf_isOpenMap f u hu g1 hg1 hs1, Tf_isOpenMap f u hu g2 hg2 hs2, Tf_inf f g1 g2,
    hopen, ψ, hψ, hne⟩

end LeanCheck
