import LeanCheck.ChainT2

/-!
# Families of rational-valued observations
(HamelCharactersTVG_v18 Theorem 5.1 `vanishing`, Corollary 5.3 `representation`, Proposition 8.1 `family`)

For an indexed family `φ : ι → (ℝ →+ ℚ)` of rational-valued additive functions put

* `σ_φ = sigmaI φ = tu ∨ init{ p ∘ φ i }`   (circle-valued observations),
* `τ_φ = tauI φ = tu ∨ init{ φ i : ℝ → ℚ_usual }` (usual rational-valued observations).

No invariance under scalars is needed for Theorem 5.1.  For a family closed under rescaling and containing a
nonzero function we prove Proposition 8.1.
-/

namespace LeanCheck

open Filter Topology

/-- `σ_φ`. -/
noncomputable def sigmaI {ι : Type} (φ : ι → ℝ →+ ℚ) : TopologicalSpace ℝ :=
  uR ⊓ ⨅ i, TopologicalSpace.induced (fun x : ℝ => (((φ i x : ℚ) : ℝ) : Circ)) circTop

/-- `τ_φ`. -/
noncomputable def tauI {ι : Type} (φ : ι → ℝ →+ ℚ) : TopologicalSpace ℝ :=
  uR ⊓ ⨅ i, TopologicalSpace.induced (φ i) usualQ

lemma induced_circ_group {G : Type} [AddCommGroup G] (g : G →+ Circ) :
    @IsTopologicalAddGroup G (TopologicalSpace.induced g circTop) _ := by
  unfold circTop
  exact isTopologicalAddGroup_induced g

section Basic

variable {ι : Type} (φ : ι → ℝ →+ ℚ)

noncomputable def pcomp_hom (s : ℝ →+ ℚ) : ℝ →+ Circ :=
  (cmulHom 1).comp ((Rat.castHom ℝ).toAddMonoidHom.comp s)

lemma pcomp_hom_apply (s : ℝ →+ ℚ) (x : ℝ) : pcomp_hom s x = (((s x : ℚ) : ℝ) : Circ) := by
  simp [pcomp_hom, cmulHom_apply]

lemma sigmaI_group : @IsTopologicalAddGroup ℝ (sigmaI φ) _ := by
  unfold sigmaI
  refine isTopologicalAddGroup_inf (show @IsTopologicalAddGroup ℝ uR _ from (inferInstance : IsTopologicalAddGroup ℝ))
    (isTopologicalAddGroup_iInf (fun i => ?_))
  have : (fun x : ℝ => (((φ i x : ℚ) : ℝ) : Circ)) = ⇑(pcomp_hom (φ i)) := by
    funext x; rw [pcomp_hom_apply]
  rw [this]
  exact induced_circ_group (pcomp_hom (φ i))

lemma tauI_group : @IsTopologicalAddGroup ℝ (tauI φ) _ := by
  unfold tauI
  refine isTopologicalAddGroup_inf (show @IsTopologicalAddGroup ℝ uR _ from (inferInstance : IsTopologicalAddGroup ℝ))
    (isTopologicalAddGroup_iInf (fun i => ?_))
  letI : TopologicalSpace ℚ := usualQ
  haveI : IsTopologicalAddGroup ℚ := usualQ_group
  exact isTopologicalAddGroup_induced (φ i)

lemma sigmaI_le_usual : sigmaI φ ≤ uR := inf_le_left
lemma tauI_le_usual : tauI φ ≤ uR := inf_le_left

lemma sigmaI_t2 : @T2Space ℝ (sigmaI φ) :=
  @T2Space.of_injective_continuous ℝ ℝ (sigmaI φ) uR (by unfold uR; infer_instance) id
    Function.injective_id (continuous_id_iff_le.2 (sigmaI_le_usual φ))

lemma tauI_t2 : @T2Space ℝ (tauI φ) :=
  @T2Space.of_injective_continuous ℝ ℝ (tauI φ) uR (by unfold uR; infer_instance) id
    Function.injective_id (continuous_id_iff_le.2 (tauI_le_usual φ))

/-- `τ_φ` is finer than `σ_φ`. -/
lemma tauI_le_sigmaI : tauI φ ≤ sigmaI φ := by
  unfold tauI sigmaI
  refine inf_le_inf_left _ (iInf_mono (fun i => ?_))
  have hc : Continuous[usualQ, circTop] (fun s : ℚ => (((s : ℚ) : ℝ) : Circ)) :=
    continuous_coe_circ.comp Rat.continuous_coe_real
  have := induced_mono (g := φ i) (continuous_iff_le_induced.1 hc)
  rw [induced_compose] at this
  exact this

/-- The character `p ∘ φ i` is `σ_φ`-continuous (and `τ_φ`-continuous). -/
lemma pcomp_cont_sigmaI (i : ι) : @Continuous ℝ Circ (sigmaI φ) circTop (pcomp_hom (φ i)) := by
  have : (⇑(pcomp_hom (φ i)) : ℝ → Circ) = fun x : ℝ => (((φ i x : ℚ) : ℝ) : Circ) := by
    funext x; rw [pcomp_hom_apply]
  rw [this]
  exact continuous_iff_le_induced.2 (inf_le_right.trans
    (iInf_le (fun i => TopologicalSpace.induced (fun x : ℝ => (((φ i x : ℚ) : ℝ) : Circ)) circTop) i))

/-- Neighbourhoods of zero in `σ_φ`. -/
theorem sigmaI_nhds_sub (V : Set ℝ) (hV : V ∈ @nhds ℝ (sigmaI φ) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ I : Finset ι, ∃ W : ι → Set Circ,
      (∀ i ∈ I, W i ∈ 𝓝 (0 : Circ)) ∧
      {x : ℝ | |x| < ε ∧ ∀ i ∈ I, (((φ i x : ℚ) : ℝ) : Circ) ∈ W i} ⊆ V := by
  classical
  unfold sigmaI at hV
  rw [@nhds_inf ℝ uR (⨅ i, TopologicalSpace.induced (fun x : ℝ => (((φ i x : ℚ) : ℝ) : Circ)) circTop) 0] at hV
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_inf_iff_superset.mp hV
  rw [nhds_iInf] at ht2
  obtain ⟨I, hI, T, hT, -, hs⟩ := Filter.mem_iInf'.mp ht2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht1
  have hex : ∀ i : ι, ∃ W : Set Circ, W ∈ 𝓝 (0 : Circ) ∧
      (fun x : ℝ => (((φ i x : ℚ) : ℝ) : Circ)) ⁻¹' W ⊆ T i := by
    intro i
    have h := hT i
    rw [nhds_induced] at h
    obtain ⟨W, hW, hWT⟩ := Filter.mem_comap.mp h
    refine ⟨W, ?_, hWT⟩
    have e : (((φ i 0 : ℚ) : ℝ) : Circ) = 0 := by simp
    rw [e] at hW
    exact hW
  choose W hW hWT using hex
  refine ⟨ε, hε, hI.toFinset, W, fun i _ => hW i, ?_⟩
  rintro x ⟨hx, hxW⟩
  apply hsub
  refine ⟨hball (by simpa [Metric.mem_ball, dist_zero_right] using hx), ?_⟩
  rw [hs.1]
  refine Set.mem_iInter₂.mpr (fun i hi => ?_)
  exact hWT i (hxW i (hI.mem_toFinset.mpr hi))

/-- **Theorem 5.1, first assertion.**  Every nonzero `g ∈ D` is unbounded on every `σ_φ`-neighbourhood of `0`. -/
theorem sigmaI_unbounded (g : ℝ →+ ℚ) (hg : g ≠ 0) (V : Set ℝ) (hV : V ∈ @nhds ℝ (sigmaI φ) 0) (B : ℝ) :
    ∃ x ∈ V, B < |((g x : ℚ) : ℝ)| := by
  classical
  obtain ⟨ε, hε, I, W, hW, hsub⟩ := sigmaI_nhds_sub φ V hV
  obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hg (AddMonoidHom.ext hall)
  let d : ℕ := ∏ i ∈ I, (φ i y).den
  have hdpos : 0 < d := Finset.prod_pos (fun i _ => (φ i y).den_pos)
  have hint : ∀ i ∈ I, ∃ m : ℤ, φ i y * d = m := fun i hi =>
    exists_k_of_den_dvd _ _ (Finset.dvd_prod_of_mem _ hi)
  let fam : Option I → (ℝ →+ ℚ) := fun j => match j with
    | none => g
    | some i => φ i
  obtain ⟨K, hK⟩ := exists_nat_gt (B / |((g y : ℚ) : ℝ)|)
  have hgy : (0 : ℝ) < |((g y : ℚ) : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast hy
  set k : ℕ := K + 1 with hk
  have hkpos : (1 : ℝ) ≤ k := by simp [hk]
  obtain ⟨z, hzN, hz⟩ := (HkerG_dense fam).exists_mem_open
    (isOpen_Ioo : IsOpen (Set.Ioo (-(((k * d : ℕ) : ℝ) * y) - ε) (-(((k * d : ℕ) : ℝ) * y) + ε)))
    ⟨-(((k * d : ℕ) : ℝ) * y), by constructor <;> linarith⟩
  have hz0 : g z = 0 ∧ ∀ i : I, φ i z = 0 := by
    have h := AddMonoidHom.mem_ker.mp hzN
    refine ⟨?_, fun i => ?_⟩
    · simpa [HmapG_apply, fam] using congrFun h none
    · simpa [HmapG_apply, fam] using congrFun h (some i)
  set x : ℝ := ((k * d : ℕ) : ℝ) * y + z with hx
  have hxabs : |x| < ε := by
    rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]
  have hgx : g x = ((k * d : ℕ) : ℚ) * g y := by
    rw [hx, map_add, hz0.1, add_zero]
    have := f_ratmul g ((k * d : ℕ) : ℚ) y
    simpa using this
  refine ⟨x, hsub ⟨hxabs, fun i hi => ?_⟩, ?_⟩
  · have : (((φ i x : ℚ) : ℝ) : Circ) = 0 := by
      obtain ⟨m, hm⟩ := hint i hi
      have hzero : φ i z = 0 := hz0.2 ⟨i, hi⟩
      have h1 : φ i x = (k : ℚ) * m := by
        rw [hx, map_add, hzero, add_zero]
        have := f_ratmul (φ i) ((k * d : ℕ) : ℚ) y
        simp only [Nat.cast_mul, Rat.cast_mul, Rat.cast_natCast] at this ⊢
        rw [this, ← hm]
        push_cast; ring
      rw [h1]
      have : (((k : ℚ) * m : ℚ) : ℝ) = ((k * m : ℤ) : ℝ) := by push_cast; ring
      rw [this, AddCircle.coe_eq_zero_iff]
      exact ⟨k * m, by simp⟩
    rw [this]
    exact mem_of_mem_nhds (hW i hi)
  · rw [hgx]
    push_cast
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * d)]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    have h2 : B < (K : ℝ) * |((g y : ℚ) : ℝ)| := by
      rw [div_lt_iff₀ hgy] at hK; exact hK
    have h3 : (K : ℝ) * |((g y : ℚ) : ℝ)| ≤ (k : ℝ) * d * |((g y : ℚ) : ℝ)| := by
      have : (K : ℝ) ≤ (k : ℝ) * d := by
        have : (K : ℝ) ≤ k := by simp [hk]
        nlinarith
      exact mul_le_mul_of_nonneg_right this hgy.le
    linarith

/-- **Theorem 5.1.**  `D_{σ_φ} = {0}`: the only continuous rational-valued additive map on `(ℝ, σ_φ)` is `0`. -/
theorem sigmaI_dual_rat (g : ℝ →+ ℚ) (hg : g ≠ 0) :
    ¬ Continuous[sigmaI φ, (inferInstance : TopologicalSpace ℝ)] (fun x : ℝ => ((g x : ℚ) : ℝ)) := by
  intro h
  have hpre : (fun x : ℝ => ((g x : ℚ) : ℝ)) ⁻¹' Set.Ioo (-1 : ℝ) 1 ∈ @nhds ℝ (sigmaI φ) 0 := by
    have h0 := (@Continuous.continuousAt ℝ ℝ (sigmaI φ) _ _ 0 h)
    have hI : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (((g 0 : ℚ) : ℝ)) := by
      simpa using Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)
    exact h0 hI
  obtain ⟨x, hxV, hxB⟩ := sigmaI_unbounded φ g hg _ hpre 1
  have h1 : |((g x : ℚ) : ℝ)| < 1 := abs_lt.mpr ⟨hxV.1, hxV.2⟩
  linarith

/-- Every `φ i` is `τ_φ`-continuous into `ℚ_usual`. -/
lemma tauI_cont_phi (i : ι) : Continuous[tauI φ, usualQ] (φ i) :=
  continuous_iff_le_induced.2 (inf_le_right.trans
    (iInf_le (fun i => TopologicalSpace.induced (φ i) usualQ) i))

/-- Neighbourhoods of zero in `τ_φ`. -/
theorem tauI_nhds_sub (V : Set ℝ) (hV : V ∈ @nhds ℝ (tauI φ) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ I : Finset ι, ∃ W : ι → Set ℚ,
      (∀ i ∈ I, W i ∈ @nhds ℚ usualQ 0) ∧
      {x : ℝ | |x| < ε ∧ ∀ i ∈ I, φ i x ∈ W i} ⊆ V := by
  classical
  unfold tauI at hV
  rw [@nhds_inf ℝ uR (⨅ i, TopologicalSpace.induced (φ i) usualQ) 0] at hV
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_inf_iff_superset.mp hV
  rw [nhds_iInf] at ht2
  obtain ⟨I, hI, T, hT, -, hs⟩ := Filter.mem_iInf'.mp ht2
  have ht1' : t1 ∈ @nhds ℝ uR 0 := ht1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (show t1 ∈ 𝓝 (0 : ℝ) from ht1')
  have hex : ∀ i : ι, ∃ W : Set ℚ, W ∈ @nhds ℚ usualQ 0 ∧ φ i ⁻¹' W ⊆ T i := by
    intro i
    have h := hT i
    rw [nhds_induced] at h
    obtain ⟨W, hW, hWT⟩ := Filter.mem_comap.mp h
    refine ⟨W, ?_, hWT⟩
    have e : φ i 0 = 0 := map_zero _
    rw [e] at hW
    exact hW
  choose W hW hWT using hex
  refine ⟨ε, hε, hI.toFinset, W, fun i _ => hW i, ?_⟩
  rintro x ⟨hx, hxW⟩
  apply hsub
  refine ⟨hball (by simpa [Metric.mem_ball, dist_zero_right] using hx), ?_⟩
  rw [hs.1]
  refine Set.mem_iInter₂.mpr (fun i hi => ?_)
  exact hWT i (hxW i (hI.mem_toFinset.mpr hi))

/-- There is a nonzero element of the joint kernel of finitely many maps in any interval around zero. -/
lemma exists_kernel_elt {ι' : Type} [Fintype ι'] (g : ι' → ℝ →+ ℚ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : ℝ, x ≠ 0 ∧ |x| < ε ∧ ∀ i, g i x = 0 := by
  have hd := HkerG_dense g
  have hopen : IsOpen (Set.Ioo (0 : ℝ) ε) := isOpen_Ioo
  obtain ⟨x, hxN, hx⟩ := hd.exists_mem_open hopen ⟨ε / 2, by constructor <;> linarith⟩
  refine ⟨x, hx.1.ne', by rw [abs_of_pos hx.1]; exact hx.2, fun i => ?_⟩
  have := AddMonoidHom.mem_ker.mp hxN
  simpa [HmapG_apply] using congrFun this i

lemma tauI_nondiscrete (i0 : ι) (h0 : φ i0 ≠ 0) : ({0} : Set ℝ) ∉ @nhds ℝ (tauI φ) 0 := by
  intro hV
  obtain ⟨ε, hε, I, W, hW, hsub⟩ := tauI_nhds_sub φ _ hV
  obtain ⟨x, hx0, hxε, hxk⟩ := exists_kernel_elt (fun i : I => φ i) ε hε
  have : x ∈ ({0} : Set ℝ) := hsub ⟨hxε, fun i hi => by
    rw [hxk ⟨i, hi⟩]; exact mem_of_mem_nhds (hW i hi)⟩
  exact hx0 (by simpa using this)

lemma sigmaI_nondiscrete (i0 : ι) (h0 : φ i0 ≠ 0) : ({0} : Set ℝ) ∉ @nhds ℝ (sigmaI φ) 0 := by
  intro hV
  obtain ⟨x, hx, hB⟩ := sigmaI_unbounded φ (φ i0) h0 {0} hV 0
  rw [Set.mem_singleton_iff.1 hx] at hB
  simp at hB

/-- `p ∘ s` is not usual-continuous for nonzero `s`. -/
lemma pcomp_not_usual (s : ℝ →+ ℚ) (hs : s ≠ 0) : ¬ Continuous (pcomp_hom s) := by
  obtain ⟨u, hu⟩ := exists_unit s hs
  intro h
  apply pfHom_not_usual s u hu 1 one_ne_zero
  have : (pfHom s 1 : ℝ → Circ) = pcomp_hom s := by
    funext x; rw [pfHom_apply, pcomp_hom_apply, one_mul]
  rw [this]; exact h

/-- Rescaling closure of an indexed family. -/
def Rescaled : Prop := ∀ (i : ι) (c : ℝ), ∃ j, ∀ x : ℝ, φ j x = φ i (c * x)

lemma sigmaI_dilation (h : Rescaled φ) (c : ℝ) :
    Continuous[sigmaI φ, sigmaI φ] (fun x : ℝ => c * x) := by
  have h1 : Continuous[sigmaI φ, uR] (fun x : ℝ => c * x) := by
    have hu : Continuous[uR, uR] (fun x : ℝ => c * x) := by
      unfold uR; exact continuous_const.mul continuous_id
    have hid : Continuous[sigmaI φ, uR] (id : ℝ → ℝ) := continuous_id_iff_le.2 (sigmaI_le_usual φ)
    exact @Continuous.comp ℝ ℝ ℝ (sigmaI φ) uR uR (id : ℝ → ℝ) (fun x : ℝ => c * x) hu hid
  refine (continuous_inf_rng (t₁ := sigmaI φ)).2 ⟨h1, ?_⟩
  refine continuous_iInf_rng.2 (fun i => continuous_induced_rng.2 ?_)
  obtain ⟨j, hj⟩ := h i c
  have : ((fun x : ℝ => (((φ i x : ℚ) : ℝ) : Circ)) ∘ fun x : ℝ => c * x) = pcomp_hom (φ j) := by
    funext x; simp only [Function.comp, pcomp_hom_apply, hj]
  rw [this]
  exact pcomp_cont_sigmaI φ j

lemma tauI_dilation (h : Rescaled φ) (c : ℝ) :
    Continuous[tauI φ, tauI φ] (fun x : ℝ => c * x) := by
  have h1 : Continuous[tauI φ, uR] (fun x : ℝ => c * x) := by
    have hu : Continuous[uR, uR] (fun x : ℝ => c * x) := by
      unfold uR; exact continuous_const.mul continuous_id
    have hid : Continuous[tauI φ, uR] (id : ℝ → ℝ) := continuous_id_iff_le.2 (tauI_le_usual φ)
    exact @Continuous.comp ℝ ℝ ℝ (tauI φ) uR uR (id : ℝ → ℝ) (fun x : ℝ => c * x) hu hid
  refine (continuous_inf_rng (t₁ := tauI φ)).2 ⟨h1, ?_⟩
  refine continuous_iInf_rng.2 (fun i => continuous_induced_rng.2 ?_)
  obtain ⟨j, hj⟩ := h i c
  have : ((φ i) ∘ fun x : ℝ => c * x) = φ j := by
    funext x; simp only [Function.comp, hj]
  rw [this]
  exact tauI_cont_phi φ j

/-- A topology finer than `σ_φ` for which the `p ∘ φ_j` are continuous is totally disconnected when the family is
rescaling invariant and contains a nonzero function. -/
lemma totallyDisconnected_family (η : TopologicalSpace ℝ) (hη : η ≤ sigmaI φ) (h : Rescaled φ) (i0 : ι)
    (h0 : φ i0 ≠ 0) : @TotallyDisconnectedSpace ℝ η := by
  obtain ⟨u, hu⟩ := exists_unit (φ i0) h0
  have key : TotallyDisconnectedSpace (RT η) :=
    totallyDisconnected_of_maps (X := RT η)
      (fun c : ℝ => fun x : RT η => pcomp_hom (φ i0) (c * x.val))
      (fun c => by
        obtain ⟨j, hj⟩ := h i0 c
        have e : (fun x : RT η => pcomp_hom (φ i0) (c * x.val)) =
            fun x : RT η => pcomp_hom (φ j) x.val := by
          funext x; rw [pcomp_hom_apply, pcomp_hom_apply, hj]
        rw [e]
        exact continuous_le_dom hη (pcomp_cont_sigmaI φ j))
      (fun c => by
        refine (Set.countable_range (fun q : ℚ => ((q : ℝ) : Circ))).mono ?_
        rintro _ ⟨z, rfl⟩
        exact ⟨φ i0 (c * z.val), (pcomp_hom_apply (φ i0) _).symm⟩)
      (fun x y hxy => by
        have hne : y.val - x.val ≠ 0 := sub_ne_zero.mpr (fun h' => hxy h'.symm)
        refine ⟨u / (2 * (y.val - x.val)), fun hh => ?_⟩
        have hh' : pcomp_hom (φ i0) (u / (2 * (y.val - x.val)) * x.val) =
            pcomp_hom (φ i0) (u / (2 * (y.val - x.val)) * y.val) := hh
        have h2 : pcomp_hom (φ i0) (u / (2 * (y.val - x.val)) * (y.val - x.val)) = 0 := by
          rw [mul_sub, map_sub, hh', sub_self]
        rw [pcomp_hom_apply] at h2
        have e3 : u / (2 * (y.val - x.val)) * (y.val - x.val) = (((1 / 2 : ℚ)) : ℝ) * u := by
          push_cast; field_simp
        rw [e3, f_ratmul, hu] at h2
        obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h2
        have h4 : ((n : ℝ)) = ((1 / 2 * 1 : ℚ) : ℝ) := by simpa using hn
        have h5 : (n : ℝ) = 1 / 2 := by rw [h4]; norm_num
        have h6 : (2 * n : ℝ) = 1 := by linarith
        have h7 : (2 * n : ℤ) = 1 := by exact_mod_cast h6
        omega)
  exact key

/-- **Proposition 8.1 (families).**  For a rescaling-invariant family containing a nonzero function, `σ_φ` and
`τ_φ` are Hausdorff nondiscrete totally disconnected TVG topologies with `tu ⊊ σ_φ ⊊ τ_φ` (in Mathlib's order:
`σ_φ < tu`, `τ_φ < σ_φ`) and `D_{σ_φ} = {0}`. -/
theorem family_properties (hresc : Rescaled φ) (i0 : ι) (h0 : φ i0 ≠ 0) :
    @IsTopologicalAddGroup ℝ (sigmaI φ) _ ∧ @IsTopologicalAddGroup ℝ (tauI φ) _ ∧
    @T2Space ℝ (sigmaI φ) ∧ @T2Space ℝ (tauI φ) ∧
    ({0} : Set ℝ) ∉ @nhds ℝ (sigmaI φ) 0 ∧ ({0} : Set ℝ) ∉ @nhds ℝ (tauI φ) 0 ∧
    (∀ c : ℝ, Continuous[sigmaI φ, sigmaI φ] (fun x : ℝ => c * x)) ∧
    (∀ c : ℝ, Continuous[tauI φ, tauI φ] (fun x : ℝ => c * x)) ∧
    @TotallyDisconnectedSpace ℝ (sigmaI φ) ∧ @TotallyDisconnectedSpace ℝ (tauI φ) ∧
    sigmaI φ < uR ∧ tauI φ < sigmaI φ ∧
    (∀ g : ℝ →+ ℚ, g ≠ 0 →
      ¬ Continuous[sigmaI φ, (inferInstance : TopologicalSpace ℝ)] (fun x : ℝ => ((g x : ℚ) : ℝ))) := by
  refine ⟨sigmaI_group φ, tauI_group φ, sigmaI_t2 φ, tauI_t2 φ, sigmaI_nondiscrete φ i0 h0,
    tauI_nondiscrete φ i0 h0, sigmaI_dilation φ hresc, tauI_dilation φ hresc,
    totallyDisconnected_family φ (sigmaI φ) le_rfl hresc i0 h0,
    totallyDisconnected_family φ (tauI φ) (tauI_le_sigmaI φ) hresc i0 h0, ?_, ?_,
    fun g hg => sigmaI_dual_rat φ g hg⟩
  · refine lt_of_le_of_ne (sigmaI_le_usual φ) (fun heq => ?_)
    apply pcomp_not_usual (φ i0) h0
    have := pcomp_cont_sigmaI φ i0
    rw [heq] at this
    exact this
  · refine lt_of_le_of_ne (tauI_le_sigmaI φ) (fun heq => ?_)
    have h1 : Continuous[tauI φ, (inferInstance : TopologicalSpace ℝ)] (fun x : ℝ => ((φ i0 x : ℚ) : ℝ)) :=
      @Continuous.comp ℝ ℚ ℝ (tauI φ) usualQ _ (φ i0) (fun s : ℚ => (s : ℝ)) Rat.continuous_coe_real
        (tauI_cont_phi φ i0)
    rw [heq] at h1
    exact sigmaI_dual_rat φ (φ i0) h0 h1

end Basic

end LeanCheck
