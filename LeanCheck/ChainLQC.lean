import LeanCheck.ChainTransferDual

/-!
# Local quasi-convexity

Definition used in HamelCharactersTVG (Section "Compatible topologies and the Mackey question"):
a subset `U` of an abelian topological group is *quasi-convex* if every `x ∉ U` can be separated from `U` by a
continuous character `χ` with `χ(U) ⊆ [-1/4, 1/4] + ℤ` and `χ(x) ∉ [-1/4, 1/4] + ℤ`; a topology is *locally
quasi-convex* if it has a zero-neighbourhood base of quasi-convex sets.

We prove: `λ_C` (on `ℚ/ℤ`), the usual topology of `ℝ`, and every topology obtained from locally quasi-convex ones by
induced topologies, joins and infima are locally quasi-convex.  Hence `γ_λ` and `T_f(δ)` are locally quasi-convex,
so the topologies of `transfer_capstone_exact` lie in the class `𝒞_f` of the paper.
-/

namespace LeanCheck

open Filter Topology

section LQC

variable {G : Type*} [AddCommGroup G]

/-- Quasi-convex sets (with respect to the continuous characters of the topology `τ`). -/
def QuasiConvex (τ : TopologicalSpace G) (U : Set G) : Prop :=
  ∀ x, x ∉ U → ∃ χ : G →+ Circ, @Continuous G Circ τ circTop χ ∧
    (∀ y ∈ U, ‖χ y‖ ≤ 1 / 4) ∧ 1 / 4 < ‖χ x‖

/-- Locally quasi-convex topologies. -/
def LocQC (τ : TopologicalSpace G) : Prop :=
  ∀ V ∈ @nhds G τ 0, ∃ U ∈ @nhds G τ 0, U ⊆ V ∧ QuasiConvex τ U

lemma qc_mono {τ τ' : TopologicalSpace G} (h : τ ≤ τ') {U : Set G} (hU : QuasiConvex τ' U) :
    QuasiConvex τ U := by
  intro x hx
  obtain ⟨χ, hc, h1, h2⟩ := hU x hx
  exact ⟨χ, continuous_le_dom h hc, h1, h2⟩

lemma qc_biInter {τ : TopologicalSpace G} {ι : Type*} (S : Set ι) (U : ι → Set G)
    (h : ∀ a ∈ S, QuasiConvex τ (U a)) : QuasiConvex τ (⋂ a ∈ S, U a) := by
  intro x hx
  simp only [Set.mem_iInter, not_forall] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  obtain ⟨χ, hc, h1, h2⟩ := h a ha x hxa
  exact ⟨χ, hc, fun y hy => h1 y (Set.mem_iInter₂.mp hy a ha), h2⟩

lemma qc_inter {τ : TopologicalSpace G} {U V : Set G} (hU : QuasiConvex τ U) (hV : QuasiConvex τ V) :
    QuasiConvex τ (U ∩ V) := by
  intro x hx
  by_cases h : x ∈ U
  · obtain ⟨χ, hc, h1, h2⟩ := hV x (fun hv => hx ⟨h, hv⟩)
    exact ⟨χ, hc, fun y hy => h1 y hy.2, h2⟩
  · obtain ⟨χ, hc, h1, h2⟩ := hU x h
    exact ⟨χ, hc, fun y hy => h1 y hy.1, h2⟩

lemma qc_preimage {H : Type*} [AddCommGroup H] (g : G →+ H) {τ : TopologicalSpace G}
    {τ' : TopologicalSpace H} (hg : Continuous[τ, τ'] g) {U : Set H} (hU : QuasiConvex τ' U) :
    QuasiConvex τ (g ⁻¹' U) := by
  intro x hx
  obtain ⟨χ, hc, h1, h2⟩ := hU (g x) hx
  exact ⟨χ.comp g, @Continuous.comp G H Circ τ τ' circTop _ _ hc hg, fun y hy => h1 (g y) hy, h2⟩

lemma lqc_induced {H : Type*} [AddCommGroup H] (g : G →+ H) (τ' : TopologicalSpace H)
    (h : LocQC τ') : LocQC (TopologicalSpace.induced g τ') := by
  intro V hV
  rw [nhds_induced, map_zero] at hV
  obtain ⟨V', hV', hsub⟩ := Filter.mem_comap.mp hV
  obtain ⟨U', hU', hU'V, hqc⟩ := h V' hV'
  refine ⟨g ⁻¹' U', ?_, fun x hx => hsub (hU'V hx), ?_⟩
  · rw [nhds_induced, map_zero]; exact Filter.preimage_mem_comap hU'
  · exact qc_preimage g (continuous_induced_dom) hqc

lemma lqc_inf (τ₁ τ₂ : TopologicalSpace G) (h₁ : LocQC τ₁) (h₂ : LocQC τ₂) : LocQC (τ₁ ⊓ τ₂) := by
  intro V hV
  rw [@nhds_inf G τ₁ τ₂ 0] at hV
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_inf_iff_superset.mp hV
  obtain ⟨U₁, hU₁, hU₁t, hq₁⟩ := h₁ t₁ ht₁
  obtain ⟨U₂, hU₂, hU₂t, hq₂⟩ := h₂ t₂ ht₂
  refine ⟨U₁ ∩ U₂, ?_, fun x hx => hsub ⟨hU₁t hx.1, hU₂t hx.2⟩, ?_⟩
  · rw [@nhds_inf G τ₁ τ₂ 0]; exact Filter.inter_mem_inf hU₁ hU₂
  · exact qc_inter (qc_mono inf_le_left hq₁) (qc_mono inf_le_right hq₂)

lemma lqc_iInf {ι : Type*} (τ : ι → TopologicalSpace G) (h : ∀ a, LocQC (τ a)) :
    LocQC (⨅ a, τ a) := by
  intro V hV
  rw [nhds_iInf] at hV
  obtain ⟨I, hI, W, hW, -, hs⟩ := Filter.mem_iInf'.mp hV
  have hex : ∀ a, ∃ U ∈ @nhds G (τ a) 0, U ⊆ W a ∧ QuasiConvex (τ a) U :=
    fun a => h a (W a) (hW a)
  choose U hU hUW hUq using hex
  refine ⟨⋂ a ∈ I, U a, ?_, ?_, ?_⟩
  · rw [nhds_iInf]
    exact (Filter.biInter_mem hI).2 (fun a _ => by
      have := @nhds_mono G (⨅ a, τ a) (τ a) 0 (iInf_le τ a)
      rw [nhds_iInf] at this
      exact this (hU a))
  · intro x hx
    rw [hs.1]
    exact Set.mem_iInter₂.2 (fun a ha => hUW a ((Set.mem_iInter₂.1 hx) a ha))
  · exact qc_biInter I U (fun a _ => qc_mono (iInf_le τ a) (hUq a))

/-! ### Base case: the usual topology of `ℝ` -/

/-- The interval `[-e, e]` is quasi-convex in `ℝ`. -/
lemma lqc_uR : LocQC uR := by
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (show V ∈ 𝓝 (0 : ℝ) from hV)
  refine ⟨Metric.closedBall 0 (ε / 2), ?_, ?_, ?_⟩
  · exact Metric.closedBall_mem_nhds (0 : ℝ) (by positivity)
  · intro x hx
    apply hball
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hx
    linarith
  · intro x hx
    have hxe : ε / 2 < |x| := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    set e : ℝ := ε / 2 with he
    have hepos : 0 < e := by positivity
    have hxpos : 0 < |x| := lt_trans hepos hxe
    have hx0 : x ≠ 0 := abs_pos.mp hxpos
    set y0 : ℝ := min (|x| / (4 * e)) (1 / 2) with hy0def
    have hy0 : 1 / 4 < y0 := by
      refine lt_min ?_ (by norm_num)
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    have hy0le : y0 ≤ |x| / (4 * e) := min_le_left _ _
    have hy0half : y0 ≤ 1 / 2 := min_le_right _ _
    refine ⟨cmulHom (y0 / x), ?_, ?_, ?_⟩
    · exact continuous_coe_circ.comp (continuous_const.mul continuous_id)
    · intro t ht
      have ht' : |t| ≤ e := by simpa [Metric.mem_closedBall, dist_zero_right] using ht
      rw [cmulHom_apply]
      refine (norm_coe_le (y0 / x * t) 0).trans ?_
      rw [Int.cast_zero, sub_zero, abs_mul, abs_div, abs_of_pos (lt_trans (by norm_num) hy0)]
      calc y0 / |x| * |t| ≤ y0 / |x| * e := by gcongr
        _ ≤ (|x| / (4 * e)) / |x| * e := by gcongr
        _ = 1 / 4 := by field_simp
    · rw [cmulHom_apply]
      have : y0 / x * x = y0 := by field_simp
      rw [this, (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2
        (by rw [abs_of_pos (lt_trans (by norm_num) hy0)]; simpa using hy0half),
        abs_of_pos (lt_trans (by norm_num) hy0)]
      exact hy0

/-! ### Base case: `λ_C` on `ℚ/ℤ` -/

lemma mult_le (t : Circ) (n : ℕ) (h : ∀ j : ℕ, j ≤ n → ‖j • t‖ ≤ 1 / 4) :
    (n : ℝ) * ‖t‖ ≤ 1 / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => h j (by omega))
    have h1 : ‖t‖ ≤ 1 / 4 := by simpa using h 1 (by omega)
    obtain ⟨θ, rfl, -, hn⟩ := exists_centered t
    rw [hn] at ih' h1 ⊢
    have hmul : ((n + 1 : ℕ) • (θ : Circ)) = (((n + 1 : ℕ) * θ : ℝ) : Circ) := nsmul_coe_circ _ _
    have hb : |((n + 1 : ℕ) : ℝ) * θ| ≤ 1 / 2 := by
      rw [abs_mul, Nat.abs_cast]; push_cast; nlinarith
    have := h (n + 1) le_rfl
    rw [hmul, (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by simpa using hb),
      abs_mul, Nat.abs_cast] at this
    exact this

/-- The character `y ↦ k • y` of `ℚ/ℤ`. -/
def kHom (k : ℕ) : TorsA →+ Circ :=
  AddMonoidHom.mk' (fun y : TorsA => k • (y : Circ)) (by intro a b; simp)

lemma kHom_apply (k : ℕ) (y : TorsA) : kHom k y = k • (y : Circ) := rfl

lemma kHom_cont (C : Set ℕ) (c : ℕ) (hc : c ∈ C) (m : ℕ) :
    @Continuous TorsA Circ (basisOf C).topology _ (kHom (m * c)) := by
  apply continuous_of_quarter C
  refine ⟨1 / (4 * ((m : ℝ) + 1)), by positivity, fun y hy => ?_⟩
  have h1 := hy c hc
  rw [kHom_apply, mul_smul]
  have h2 : ‖c • (y : Circ)‖ ≤ 1 / (4 * ((m : ℝ) + 1)) := h1.le
  calc ‖m • (c • (y : Circ))‖ ≤ m * ‖c • (y : Circ)‖ := norm_nsmul_le
    _ ≤ m * (1 / (4 * ((m : ℝ) + 1))) := by gcongr
    _ < 1 / 4 := by
      rw [← mul_div_assoc, mul_one, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

lemma lqc_basisOf (C : Set ℕ) : LocQC (basisOf C).topology := by
  intro V hV
  obtain ⟨s, ⟨δ, hδ, rfl⟩, hs⟩ := ((basisOf C).nhds_zero_hasBasis).mem_iff.mp hV
  obtain ⟨n, hn1, hnδ⟩ := exists_R δ hδ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  refine ⟨{x : TorsA | ∀ c ∈ C, ∀ m : ℕ, m ≤ n → ‖(m * c) • (x : Circ)‖ ≤ 1 / 4}, ?_, ?_, ?_⟩
  · refine Filter.mem_of_superset
      (((basisOf C).nhds_zero_hasBasis).mem_of_mem (mem_basisOf (show 0 < 1 / (4 * (n : ℝ)) by positivity)))
      ?_
    intro x hx c hc m hm
    have h1 := hx c hc
    rw [mul_smul]
    calc ‖m • (c • (x : Circ))‖ ≤ m * ‖c • (x : Circ)‖ := norm_nsmul_le
      _ ≤ n * (1 / (4 * (n : ℝ))) :=
        mul_le_mul (by exact_mod_cast hm) h1.le (norm_nonneg _) (Nat.cast_nonneg n)
      _ = 1 / 4 := by field_simp
  · intro x hx
    apply hs
    intro c hc
    have hall : ∀ j : ℕ, j ≤ n → ‖j • (c • (x : Circ))‖ ≤ 1 / 4 := by
      intro j hj
      have := hx c hc j hj
      rwa [mul_smul] at this
    have := mult_le _ n hall
    have h2 : ‖c • (x : Circ)‖ ≤ 1 / (4 * n) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    exact lt_of_le_of_lt h2 hnδ
  · intro x hx
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hx
    obtain ⟨c, hc, m, hm, hlt⟩ := hx
    exact ⟨kHom (m * c), kHom_cont C c hc m, fun y hy => hy c hc m hm, hlt⟩

/-! ### Consequences -/

lemma lqc_gam (t : TopologicalSpace TorsA) (h : LocQC t) : LocQC (gam t) :=
  lqc_iInf _ (fun r => lqc_induced (hq r) t h)

lemma lqc_Tf (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (h : LocQC δ) : LocQC (Tf f δ) :=
  lqc_inf _ _ lqc_uR (lqc_iInf _ (fun a => lqc_induced (fa f a) δ h))

end LQC

/-- **Final capstone on `ℚ/ℤ`, with local quasi-convexity**: the two chain topologies are Hausdorff, locally
quasi-convex, have dual exactly `ℤι`, and their join has a continuous character outside `ℤι`. -/
theorem final_capstone_lqc :
    ∃ (M1 M2 : ℕ → ℕ) (ζ : TorsA →+ Circ),
      @T2Space TorsA (basisOf (Set.range M1)).topology ∧
      @T2Space TorsA (basisOf (Set.range M2)).topology ∧
      LocQC (basisOf (Set.range M1)).topology ∧ LocQC (basisOf (Set.range M2)).topology ∧
      (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (Set.range M1)).topology _ χ ↔
        ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) ∧
      (∀ χ : TorsA →+ Circ, @Continuous TorsA Circ (basisOf (Set.range M2)).topology _ χ ↔
        ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ)) ∧
      @Continuous TorsA Circ
        ((basisOf (Set.range M1)).topology ⊓ (basisOf (Set.range M2)).topology) _ ζ ∧
      (∀ u : ℤ, ∃ x : TorsA, ζ x ≠ u • (x : Circ)) := by
  obtain ⟨M1, M2, ζ, -, -, ht1, ht2, hd1, hd2, hζ, hne⟩ := final_capstone
  exact ⟨M1, M2, ζ, ht1, ht2, lqc_basisOf _, lqc_basisOf _, hd1, hd2, hζ, hne⟩

/-- **The lift to `ℚ`, with local quasi-convexity** (the class `ℒ_Γ`, with rational scalars: `𝒬_Γ`). -/
theorem lift_capstone_lqc :
    ∃ (g1 g2 : TopologicalSpace ℚ),
      @IsTopologicalAddGroup ℚ g1 _ ∧ @IsTopologicalAddGroup ℚ g2 _ ∧
      @T2Space ℚ g1 ∧ @T2Space ℚ g2 ∧ LocQC g1 ∧ LocQC g2 ∧
      (∀ s : ℚ, Continuous[g1, g1] (fun x : ℚ => s * x)) ∧
      (∀ s : ℚ, Continuous[g2, g2] (fun x : ℚ => s * x)) ∧
      (∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ g1 _ ψ ↔ ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ)) ∧
      (∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ g2 _ ψ ↔ ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ)) ∧
      ∃ ψ : ℚ →+ Circ, @Continuous ℚ Circ (g1 ⊓ g2) _ ψ ∧
        ∀ r : ℚ, ∃ s : ℚ, ψ s ≠ (((r * s : ℚ) : ℝ) : Circ) := by
  obtain ⟨M1, M2, ζ, ht1, ht2, hl1, hl2, hd1, hd2, hζ, hne⟩ := final_capstone_lqc
  have g1 := (basisOf (Set.range M1)).isTopologicalAddGroup
  have g2 := (basisOf (Set.range M2)).isTopologicalAddGroup
  obtain ⟨ψ, hψ, hψne⟩ := lift_incompatible (basisOf (Set.range M1)).topology
    (basisOf (Set.range M2)).topology ζ hζ hne
  exact ⟨gam (basisOf (Set.range M1)).topology, gam (basisOf (Set.range M2)).topology,
    gam_group _ g1, gam_group _ g2, @gam_t2 _ ht1, @gam_t2 _ ht2,
    lqc_gam _ hl1, lqc_gam _ hl2, gam_scalar _, gam_scalar _,
    dual_gam _ g1 hd1, dual_gam _ g2 hd2, ψ, hψ, hψne⟩

/-- **The transfer theorem with membership in `𝒞_f`.**  For every coefficient function `f` there are two
topologies `T₁, T₂` on `ℝ` that are Hausdorff, locally quasi-convex, TVG (group topologies with all real dilations
continuous), finer than the usual topology, with continuous character group exactly `H_f` -- i.e. members of
`𝒞_f` -- whose join has a continuous character outside `H_f`; so the join is not in `𝒞_f`. -/
theorem transfer_capstone_Cf (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    ∃ T₁ T₂ : TopologicalSpace ℝ,
      @IsTopologicalAddGroup ℝ T₁ _ ∧ @IsTopologicalAddGroup ℝ T₂ _ ∧
      @T2Space ℝ T₁ ∧ @T2Space ℝ T₂ ∧ LocQC T₁ ∧ LocQC T₂ ∧
      T₁ ≤ uR ∧ T₂ ≤ uR ∧
      (∀ c : ℝ, Continuous[T₁, T₁] (fun x : ℝ => c * x)) ∧
      (∀ c : ℝ, Continuous[T₂, T₂] (fun x : ℝ => c * x)) ∧
      (∀ χ : ℝ →+ Circ, @Continuous ℝ Circ T₁ circTop χ ↔ ∃ c a : ℝ, ∀ x : ℝ, χ x = chiH f c a x) ∧
      (∀ χ : ℝ →+ Circ, @Continuous ℝ Circ T₂ circTop χ ↔ ∃ c a : ℝ, ∀ x : ℝ, χ x = chiH f c a x) ∧
      ∃ φ : ℝ →+ Circ, @Continuous ℝ Circ (T₁ ⊓ T₂) circTop φ ∧
        ¬ ∃ c a : ℝ, ∀ x : ℝ, φ x = chiH f c a x := by
  obtain ⟨g1, g2, hg1, hg2, -, -, hl1, hl2, hs1, hs2, hd1, hd2, ψ, hψ, hne⟩ := lift_capstone_lqc
  obtain ⟨φ, hφ, hφne⟩ := transfer_obstruction f u hu g1 g2 ψ hψ hne
  exact ⟨Tf f g1, Tf f g2, Tf_group f g1 hg1, Tf_group f g2 hg2, Tf_t2 f g1, Tf_t2 f g2,
    lqc_Tf f g1 hl1, lqc_Tf f g2 hl2,
    Tf_le_usual f g1, Tf_le_usual f g2, Tf_dilation f g1, Tf_dilation f g2,
    dual_Tf f g1 hg1 hs1 hd1, dual_Tf f g2 hg2 hs2 hd2, φ, hφ, hφne⟩

end LeanCheck
