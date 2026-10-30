import LeanCheck.ChainHamel

/-!
# Characters of `β_{f,S}`, `σ_{f,S}` (TVGQ-v7 Theorem `characters`)

The continuous characters of `σ_{f,S}` and of `β_{f,S}` are exactly `H_{f,S} = { x ↦ p(c x + f(a x)) : c ∈ ℝ, a ∈ S }`,
with unique parameters (Lemma `mixed`).
-/

namespace LeanCheck

open Filter Topology

/-! ### The circle subspace topology on `ℚ/ℤ` and `γ₀` -/

/-- Continuous characters of `ℚ/ℤ` with the circle topology are the integer multiples of the inclusion. -/
theorem circ_dual (χ : TorsA →+ Circ) :
    @Continuous TorsA Circ circT circTop χ ↔ ∃ u : ℤ, ∀ x : TorsA, χ x = u • (x : Circ) := by
  constructor
  · intro h
    obtain ⟨M1, M2, ζ, h1, h2, ht1, ht2, hd1, hd2, hζ, hne⟩ := final_capstone
    have hle : (basisOf (Set.range M1)).topology ≤ circT := by
      unfold circT
      refine continuous_iff_le_induced.mp ?_
      have := kHom_cont (Set.range M1) 1 h1 1
      have e : (Subtype.val : TorsA → Circ) = (kHom (1 * 1) : TorsA → Circ) := by
        funext y; simp [kHom_apply]
      rw [e]; exact this
    exact (hd1 χ).mp (continuous_le_dom hle h)
  · rintro ⟨u, hu⟩
    have : (χ : TorsA → Circ) = fun x : TorsA => u • (x : Circ) := funext hu
    rw [this]
    exact (show Continuous (fun x : TorsA => u • (x : Circ)) from
      (continuous_zsmul u).comp continuous_subtype_val)

/-- The dual of `γ₀` (the topology of the characters `p(r ·)` on `ℚ`) is `Γ`. -/
theorem gamma0_dual (ψ : ℚ →+ Circ) :
    @Continuous ℚ Circ gamma0 _ ψ ↔ ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ) := by
  rw [gamma0_eq_gam]
  exact dual_gam circT circT_group circ_dual ψ

/-! ### Reduction to an independent family inside `S` -/

lemma indep_reduction_mem (f : ℝ →+ ℚ) (I : Finset ℝ) :
    ∃ (κ : Type) (_ : Fintype κ) (b : κ → ℝ), (∀ j, b j ∈ I) ∧
      LinearIndependent ℚ (fun j => Fa f (b j)) ∧
      ∀ a ∈ I, ∃ q : κ → ℚ, ∀ x : ℝ, f (a * x) = ∑ j, q j * f (b j * x) := by
  obtain ⟨κ, t, hinj, hsp, hli⟩ := exists_linearIndependent' ℚ (fun a : I => Fa f (a : ℝ))
  haveI : Finite κ := Finite.of_injective t hinj
  letI : Fintype κ := Fintype.ofFinite κ
  refine ⟨κ, inferInstance, fun j => ((t j : I) : ℝ), fun j => (t j).2, hli, ?_⟩
  intro a ha
  have hmem : Fa f a ∈ Submodule.span ℚ (Set.range ((fun a : I => Fa f (a : ℝ)) ∘ t)) := by
    rw [hsp]; exact Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
  refine ⟨q, fun x => ?_⟩
  have := congrArg (fun m : ℝ →ₗ[ℚ] ℚ => m x) hq
  rw [LinearMap.sum_apply] at this
  simp only [LinearMap.smul_apply, Function.comp, Fa_apply, smul_eq_mul] at this
  exact this.symm

/-- Basic neighbourhoods of `0` in `TfS f S δ`. -/
theorem tfS_nhds_sub (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ) (T : Set ℝ)
    (hT : T ∈ @nhds ℝ (TfS f S δ) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ I : Finset ℝ, (∀ a ∈ I, a ∈ S) ∧ ∃ U : ℝ → Set ℚ,
      (∀ a ∈ I, U a ∈ @nhds ℚ δ 0) ∧
      {x : ℝ | |x| < ε ∧ ∀ a ∈ I, f (a * x) ∈ U a} ⊆ T := by
  classical
  unfold TfS at hT
  rw [nhds_inf] at hT
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_inf_iff_superset.mp hT
  rw [nhds_iInf] at ht2
  obtain ⟨I, hI, V, hV, -, hs⟩ := Filter.mem_iInf'.mp ht2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht1
  have hex : ∀ a : S, ∃ U : Set ℚ, U ∈ @nhds ℚ δ 0 ∧ fa f (a : ℝ) ⁻¹' U ⊆ V a := by
    intro a
    have h := hV a
    rw [nhds_induced, map_zero] at h
    exact Filter.mem_comap.mp h
  choose U hU hUV using hex
  refine ⟨ε, hε, hI.toFinset.image (fun a : S => (a : ℝ)), ?_,
    fun a => if h : a ∈ S then U ⟨a, h⟩ else Set.univ, ?_, ?_⟩
  · intro a ha
    obtain ⟨a0, -, rfl⟩ := Finset.mem_image.mp ha
    exact a0.2
  · intro a ha
    obtain ⟨a0, -, rfl⟩ := Finset.mem_image.mp ha
    simpa using hU a0
  · rintro x ⟨hx, hxU⟩
    apply hsub
    refine ⟨hball (by simpa [Metric.mem_ball, dist_zero_right] using hx), ?_⟩
    rw [hs.1]
    refine Set.mem_iInter₂.mpr (fun a ha => ?_)
    apply hUV a
    have := hxU (a : ℝ) (Finset.mem_image.mpr ⟨a, hI.mem_toFinset.mpr ha, rfl⟩)
    simpa [fa_apply] using this

/-- Neighbourhood data in independent form, inside `S`. -/
theorem packagedS_set (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ)
    (hg : @IsTopologicalAddGroup ℚ δ _) (hs : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x))
    (T : Set ℝ) (hT : T ∈ @nhds ℝ (TfS f S δ) 0) (I0 : Finset ℝ) (hI0 : ∀ a ∈ I0, a ∈ S) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (κ : Type) (_ : Fintype κ) (b : κ → ℝ) (W : κ → Set ℚ),
      (∀ j, b j ∈ S) ∧ LinearIndependent ℚ (fun j => Fa f (b j)) ∧
      (∀ a ∈ I0, ∃ q : κ → ℚ, ∀ x : ℝ, f (a * x) = ∑ j, q j * f (b j * x)) ∧
      (∀ j, W j ∈ @nhds ℚ δ 0) ∧
      {x : ℝ | |x| < ε ∧ ∀ j, f (b j * x) ∈ W j} ⊆ T := by
  classical
  obtain ⟨ε, hε, I, hIS, U, hU, hsub⟩ := tfS_nhds_sub f S δ T hT
  obtain ⟨κ, hκ, b, hbI, hli, hq⟩ := indep_reduction_mem f (I ∪ I0)
  have hq' : ∀ a : ℝ, ∃ q : κ → ℚ, a ∈ I ∪ I0 → ∀ x : ℝ, f (a * x) = ∑ j, q j * f (b j * x) := by
    intro a
    by_cases ha : a ∈ I ∪ I0
    · obtain ⟨q, hq⟩ := hq a ha
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose Q hQ using hq'
  obtain ⟨W, hW, hbox⟩ := pi_box δ hg hs I U hU Q
  refine ⟨ε, hε, κ, hκ, b, W, fun j => ?_, hli, fun a ha => ⟨Q a, hQ a (Finset.mem_union_right _ ha)⟩, hW, ?_⟩
  · have := hbI j
    rcases Finset.mem_union.mp this with h | h
    · exact hIS _ h
    · exact hI0 _ h
  · rintro x ⟨hx, hxW⟩
    apply hsub
    refine ⟨hx, fun a ha => ?_⟩
    rw [hQ a (Finset.mem_union_left _ ha) x]
    exact hbox (fun j => f (b j * x)) hxW a ha

/-- **The dual of `TfS f S δ` is contained in `H_{f,S}`.** -/
theorem dual_TfS_mp (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ)
    (hg : @IsTopologicalAddGroup ℚ δ _) (hs : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x))
    (hdual : ∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ δ _ ψ →
      ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ))
    (χ : ℝ →+ Circ) (hχ : @Continuous ℝ Circ (TfS f S δ) circTop χ) :
    ∃ (c : ℝ) (a : ℝ), a ∈ S ∧ ∀ x : ℝ, χ x = chiH f c a x := by
  classical
  have hquarter : ∀ ψ : ℝ →+ Circ, @Continuous ℝ Circ (TfS f S δ) circTop ψ →
      (ψ ⁻¹' {y : Circ | ‖y‖ < 1 / 4}) ∈ @nhds ℝ (TfS f S δ) 0 := by
    intro ψ hψ
    have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (ψ 0) := by
      rw [map_zero]
      exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
    exact (@Continuous.continuousAt ℝ Circ (TfS f S δ) circTop ψ 0 hψ) hS
  -- Stage 1
  obtain ⟨ε, hε, κ, hκ, b, W, hbS, hli, -, hW, hsm⟩ :=
    packagedS_set f S δ hg hs _ (hquarter χ hχ) ∅ (by simp)
  have hsmall : ∀ x ∈ (Hmap f b).ker, |x| < ε → ‖χ x‖ < 1 / 4 := by
    intro x hx hxε
    have : x ∈ {x : ℝ | |x| < ε ∧ ∀ j, f (b j * x) ∈ W j} := by
      refine ⟨hxε, fun j => ?_⟩
      have h0 : f (b j * x) = 0 := by
        have := congrFun (AddMonoidHom.mem_ker.mp hx) j
        simpa [Hmap_apply] using this
      rw [h0]; exact mem_of_mem_nhds (hW j)
    exact hsm this
  obtain ⟨c, hc⟩ := linearize χ (Hmap f b).ker ε hε (Hker_qmul f b) hsmall (Hker_dense f b)
  -- Stage 2
  let χ' : ℝ →+ Circ := χ + cmulHom (-c)
  have hχ'x : ∀ x, χ' x = χ x - ((c * x : ℝ) : Circ) := by
    intro x
    show χ x + ((-c * x : ℝ) : Circ) = _
    rw [neg_mul, AddCircle.coe_neg, sub_eq_add_neg]
  have hχ' : @Continuous ℝ Circ (TfS f S δ) circTop χ' :=
    @Continuous.add Circ _ _ _ ℝ (TfS f S δ) _ _ hχ
      (continuous_inf_dom_left (continuous_coe_circ.comp (continuous_const.mul continuous_id)))
  obtain ⟨ε', hε', κ', hκ', b', W', hb'S, hli', hspan, hW', hsm'⟩ :=
    packagedS_set f S δ hg hs _ (hquarter χ' hχ') (Finset.univ.image b)
      (by intro a ha; obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha; exact hbS j)
  have hN2N : ∀ x ∈ (Hmap f b').ker, x ∈ (Hmap f b).ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    funext j
    obtain ⟨q, hq⟩ := hspan (b j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    have h0 : ∀ i, f (b' i * x) = 0 := fun i => by
      have := congrFun hx i
      simpa [Hmap_apply] using this
    simp only [Hmap_apply, Pi.zero_apply]
    rw [hq x]
    simp [h0]
  have hker0 : ∀ x ∈ (Hmap f b').ker, χ' x = 0 := by
    intro x hx
    rw [hχ'x, hc x (hN2N x hx), sub_self]
  choose xs hxs using fun j : κ' => Hmap_surj f b' hli' (Pi.single j (1 : ℚ))
  have hHx : ∀ (t : ℚ) (j i : κ'), Hmap f b' ((t : ℝ) * xs j) i = t * (Pi.single j (1 : ℚ) : κ' → ℚ) i := by
    intro t j i
    rw [Hmap_apply, mul_left_comm, f_ratmul, ← Hmap_apply, hxs j]
  let θ : κ' → (ℚ →+ Circ) := fun j =>
    AddMonoidHom.mk' (fun t : ℚ => χ' ((t : ℝ) * xs j)) (by intro s t; simp [add_mul])
  have hθ : ∀ j t, θ j t = χ' ((t : ℝ) * xs j) := fun j t => rfl
  have hθcont : ∀ j, @Continuous ℚ Circ δ _ (θ j) := by
    intro j
    letI : TopologicalSpace ℚ := δ
    haveI : IsTopologicalAddGroup ℚ := hg
    refine continuous_of_quarter_gen (θ j) (hW' j) ?_
    intro t ht
    obtain ⟨n, hnN, hn⟩ := (Hker_dense f b').exists_mem_open
      (isOpen_Ioo : IsOpen (Set.Ioo (-((t : ℝ) * xs j) - ε') (-((t : ℝ) * xs j) + ε')))
      ⟨-((t : ℝ) * xs j), by constructor <;> linarith⟩
    have hy : |(t : ℝ) * xs j + n| < ε' := by
      rw [abs_lt]; constructor <;> linarith [hn.1, hn.2]
    have hHy : ∀ i, f (b' i * ((t : ℝ) * xs j + n)) ∈ W' i := by
      intro i
      have hn0 : f (b' i * n) = 0 := by
        have := congrFun (AddMonoidHom.mem_ker.mp hnN) i
        simpa [Hmap_apply] using this
      have h1 := hHx t j i
      rw [Hmap_apply] at h1
      rw [mul_add, map_add, hn0, add_zero, h1]
      by_cases hij : i = j
      · subst hij; simpa using ht
      · simp [Pi.single_apply, hij]; exact mem_of_mem_nhds (hW' i)
    have := hsm' ⟨hy, hHy⟩
    have hχn : χ' ((t : ℝ) * xs j + n) = θ j t := by
      rw [map_add, hker0 n hnN, add_zero, hθ]
    have h3 : ‖χ' ((t : ℝ) * xs j + n)‖ < 1 / 4 := this
    rwa [hχn] at h3
  choose r hr using fun j => hdual (θ j) (hθcont j)
  have hdecomp : ∀ x : ℝ, χ' x = ∑ j, θ j (f (b' j * x)) := by
    intro x
    have hz : x - ∑ j, ((f (b' j * x) : ℚ) : ℝ) * xs j ∈ (Hmap f b').ker := by
      rw [AddMonoidHom.mem_ker]
      funext i
      rw [map_sub, map_sum]
      simp only [Pi.sub_apply, Finset.sum_apply, hHx, Pi.zero_apply]
      simp [Pi.single_apply, Hmap_apply]
    have h0 := hker0 _ hz
    rw [map_sub, map_sum] at h0
    have : χ' x = ∑ j, χ' (((f (b' j * x) : ℚ) : ℝ) * xs j) := sub_eq_zero.mp h0
    rw [this]
    exact Finset.sum_congr rfl (fun j _ => (hθ j _).symm)
  refine ⟨c, ∑ j, ((r j : ℚ) : ℝ) * b' j, ?_, fun x => ?_⟩
  · refine S.sum_mem (fun j _ => ?_)
    have := S.smul_mem (r j) (hb'S j)
    simpa [Rat.smul_def] using this
  have hfa : f ((∑ j, ((r j : ℚ) : ℝ) * b' j) * x) = ∑ j, r j * f (b' j * x) := by
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_assoc, f_ratmul]
  have h1 : χ x = χ' x + ((c * x : ℝ) : Circ) := by rw [hχ'x]; abel
  rw [h1, hdecomp]
  unfold chiH
  rw [hfa]
  have e1 : ∑ j, θ j (f (b' j * x)) = (((∑ j, r j * f (b' j * x) : ℚ) : ℝ) : Circ) :=
    calc ∑ j, θ j (f (b' j * x)) = ∑ j, psi0 (r j * f (b' j * x)) :=
          Finset.sum_congr rfl (fun j _ => by rw [hr j, psi0_apply])
      _ = psi0 (∑ j, r j * f (b' j * x)) := (map_sum psi0 _ _).symm
      _ = _ := psi0_apply _
  rw [e1, AddCircle.coe_add, add_comm]

/-! ### Lemma `mixed`, and the characters of `σ_{f,S}` and `β_{f,S}` -/

/-- **Lemma `mixed`**: if `p(c x + f(a x)) = 0` for all `x` then `c = a = 0`. -/
theorem mixed_zero (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (c a : ℝ)
    (h : ∀ x : ℝ, chiH f c a x = 0) : c = 0 ∧ a = 0 := by
  have hz : ∀ x : ℝ, c * x + ((f (a * x) : ℚ) : ℝ) = 0 := by
    intro x
    apply int_of_all_div
    intro n hn
    have h0 := h (((1 / (n : ℚ) : ℚ) : ℝ) * x)
    unfold chiH at h0
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h0
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one] at hk
    have h3 : f (a * (((1 / (n : ℚ) : ℚ) : ℝ) * x)) = (1 / (n : ℚ)) * f (a * x) := by
      rw [mul_left_comm, f_ratmul]
    rw [h3] at hk
    push_cast at hk
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [hk]
    field_simp
  have hc : c = 0 := by
    by_contra hc
    have h1 := hz (Real.sqrt 2 / c)
    have h2 : c * (Real.sqrt 2 / c) = Real.sqrt 2 := by field_simp
    rw [h2] at h1
    apply irrational_sqrt_two
    refine ⟨-(f (a * (Real.sqrt 2 / c))), ?_⟩
    push_cast
    linarith
  refine ⟨hc, ?_⟩
  by_contra ha
  have h1 := hz (u / a)
  rw [hc, zero_mul, zero_add, show a * (u / a) = u by field_simp, hu] at h1
  norm_num at h1

/-- Parameters of `H_{f,S}` are unique. -/
theorem chiH_unique (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (c a c' a' : ℝ)
    (h : ∀ x : ℝ, chiH f c a x = chiH f c' a' x) : c = c' ∧ a = a' := by
  have := mixed_zero f u hu (c - c') (a - a') (fun x => by
    have hx := h x
    unfold chiH at hx ⊢
    have e : ((c - c') * x + ((f ((a - a') * x) : ℚ) : ℝ)) =
        (c * x + ((f (a * x) : ℚ) : ℝ)) - (c' * x + ((f (a' * x) : ℚ) : ℝ)) := by
      rw [sub_mul, sub_mul, map_sub]; push_cast; ring
    rw [e, AddCircle.coe_sub, hx, sub_self])
  exact ⟨sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩

lemma chiH_cont_sigma (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (c a : ℝ) (ha : a ∈ S) :
    @Continuous ℝ Circ (betaT f S) circTop (chiH f c a) := by
  have h1 := cmulHom_cont_beta f S c
  have h2 := pfHom_cont_beta f S ⟨a, ha⟩
  have : chiH f c a = fun x : ℝ => cmulHom c x + pfHom f a x := by
    funext x
    simp only [cmulHom_apply, pfHom_apply, chiH]
    rw [AddCircle.coe_add]
  rw [this]
  exact @Continuous.add Circ _ _ _ ℝ (betaT f S) _ _ h1 h2

/-- **Characters of `σ_{f,S}`**: exactly `H_{f,S}`. -/
theorem dual_sigma (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (χ : ℝ →+ Circ) :
    @Continuous ℝ Circ (sigmaT f S) circTop χ ↔
      ∃ (c a : ℝ), a ∈ S ∧ ∀ x : ℝ, χ x = chiH f c a x := by
  constructor
  · intro h
    exact dual_TfS_mp f S gamma0 gamma0_group gamma0_scalar (fun ψ hψ => (gamma0_dual ψ).mp hψ) χ h
  · rintro ⟨c, a, ha, h⟩
    have : (χ : ℝ → Circ) = chiH f c a := funext h
    rw [this]
    exact continuous_le_dom (sigmaT_le_betaT f S) (chiH_cont_sigma f S c a ha)

/-- **Characters of `β_{f,S}`**: exactly `H_{f,S}`. -/
theorem dual_beta (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (χ : ℝ →+ Circ) :
    @Continuous ℝ Circ (betaT f S) circTop χ ↔
      ∃ (c a : ℝ), a ∈ S ∧ ∀ x : ℝ, χ x = chiH f c a x := by
  constructor
  · intro h
    exact (dual_sigma f S χ).mp (continuous_le_dom (sigmaT_le_betaT f S) h)
  · rintro ⟨c, a, ha, h⟩
    have : (χ : ℝ → Circ) = chiH f c a := funext h
    rw [this]
    exact chiH_cont_sigma f S c a ha

end LeanCheck
