import LeanCheck.ChainHamelDual

/-!
# Strict separation (TVGQ-v7 Lemma `usual`, Theorem `strict`)

`tu ⊊ σ_{f,S} ⊊ τ_{f,S}`; every nonzero rational-valued additive map is unbounded on every `σ_{f,S}`-neighbourhood
of `0`, so the continuous rational-valued additive duals of `σ` and `β` are zero.
-/

namespace LeanCheck

open Filter Topology

/-! ### Usual-continuous characters -/

/-- A usual-continuous character of `ℝ` is `x ↦ p(c x)`. -/
theorem usual_char (χ : ℝ →+ Circ) (h : Continuous χ) : ∃ c : ℝ, ∀ x : ℝ, χ x = ((c * x : ℝ) : Circ) := by
  have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (χ 0) := by
    rw [map_zero]
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (h.continuousAt hS)
  have hsmall : ∀ x ∈ (⊤ : AddSubgroup ℝ), |x| < ε → ‖χ x‖ < 1 / 4 := by
    intro x _ hx
    exact hball (by simpa [Metric.mem_ball, dist_zero_right] using hx)
  obtain ⟨c, hc⟩ := linearize χ ⊤ ε hε (fun x _ q => AddSubgroup.mem_top _) hsmall (by simp)
  exact ⟨c, fun x => hc x (AddSubgroup.mem_top _)⟩

/-- **Lemma `usual`**: for `a ≠ 0`, `p ∘ f_a` is not usual-continuous. -/
theorem pfHom_not_usual (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (a : ℝ) (ha : a ≠ 0) :
    ¬ Continuous (pfHom f a) := by
  intro h
  obtain ⟨c, hc⟩ := usual_char (pfHom f a) h
  have := mixed_zero f u hu (-c) a (fun x => by
    unfold chiH
    have e : -c * x + ((f (a * x) : ℚ) : ℝ) = ((f (a * x) : ℚ) : ℝ) - c * x := by ring
    rw [e, AddCircle.coe_sub, ← pfHom_apply, hc, sub_self])
  exact ha this.2

/-- `tu ⊊ σ_{f,S}`: the topology `σ` is strictly finer than the usual one when `S ≠ 0`. -/
theorem sigmaT_lt_usual (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) (S : Submodule ℚ ℝ) (a : ℝ) (haS : a ∈ S)
    (ha : a ≠ 0) : sigmaT f S < (inferInstance : TopologicalSpace ℝ) := by
  refine lt_of_le_of_ne (sigmaT_le_usual f S) (fun heq => ?_)
  have h1 : @Continuous ℝ Circ (sigmaT f S) circTop (pfHom f a) := by
    have : (pfHom f a : ℝ → Circ) = chiH f 0 a := by
      funext x; simp [pfHom_apply, chiH]
    rw [this]
    exact continuous_le_dom (sigmaT_le_betaT f S) (chiH_cont_sigma f S 0 a haS)
  rw [heq] at h1
  exact pfHom_not_usual f u hu a ha h1

/-! ### Joint kernels of arbitrary rational-valued maps -/

/-- Joint map of finitely many additive maps `ℝ → ℚ`. -/
def HmapG {ι : Type} [Fintype ι] (g : ι → ℝ →+ ℚ) : ℝ →+ (ι → ℚ) where
  toFun x := fun i => g i x
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

lemma HmapG_apply {ι : Type} [Fintype ι] (g : ι → ℝ →+ ℚ) (x : ℝ) (i : ι) : HmapG g x i = g i x := rfl

/-- The joint kernel of finitely many additive maps `ℝ → ℚ` is dense. -/
theorem HkerG_dense {ι : Type} [Fintype ι] (g : ι → ℝ →+ ℚ) : Dense ((HmapG g).ker : Set ℝ) := by
  rcases AddSubgroup.dense_or_isCyclic (HmapG g).ker with h | h
  · exact h
  · exfalso
    have hc := countable_of_cyclic _ h
    classical
    let r : (ι → ℚ) → ℝ := fun v => if hv : ∃ x, HmapG g x = v then hv.choose else 0
    have hsub : (Set.univ : Set ℝ) ⊆ ⋃ v : ι → ℚ, (fun e : ℝ => e + r v) '' ((HmapG g).ker : Set ℝ) := by
      intro x _
      refine Set.mem_iUnion.2 ⟨HmapG g x, ⟨x - r (HmapG g x), ?_, by ring⟩⟩
      have hv : ∃ y, HmapG g y = HmapG g x := ⟨x, rfl⟩
      have : r (HmapG g x) = hv.choose := by simp only [r, dif_pos hv]
      rw [this]
      show HmapG g (x - hv.choose) = 0
      rw [map_sub, hv.choose_spec, sub_self]
    exact Cardinal.not_countable_real ((Set.countable_iUnion fun v => hc.image _).mono hsub)

/-! ### Neighbourhoods of `σ_{f,S}` and unboundedness -/

lemma sigmaT_eq_A (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    sigmaT f S = (inferInstance : TopologicalSpace ℝ) ⊓
      ⨅ a : S, TopologicalSpace.induced (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop := by
  unfold sigmaT TfS
  rw [iInf_gamma0_eq]

theorem sigma_nhds_sub (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (V : Set ℝ)
    (hV : V ∈ @nhds ℝ (sigmaT f S) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ I : Finset ℝ, (∀ a ∈ I, a ∈ S) ∧ ∃ W : ℝ → Set Circ,
      (∀ a ∈ I, W a ∈ 𝓝 (0 : Circ)) ∧
      {x : ℝ | |x| < ε ∧ ∀ a ∈ I, (((f (a * x) : ℚ) : ℝ) : Circ) ∈ W a} ⊆ V := by
  classical
  rw [sigmaT_eq_A] at hV
  rw [nhds_inf] at hV
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_inf_iff_superset.mp hV
  rw [nhds_iInf] at ht2
  obtain ⟨I, hI, T, hT, -, hs⟩ := Filter.mem_iInf'.mp ht2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht1
  have hex : ∀ a : S, ∃ W : Set Circ, W ∈ 𝓝 (0 : Circ) ∧
      (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) ⁻¹' W ⊆ T a := by
    intro a
    have h := hT a
    rw [nhds_induced] at h
    obtain ⟨W, hW, hWT⟩ := Filter.mem_comap.mp h
    refine ⟨W, ?_, hWT⟩
    have e : (((f ((a : ℝ) * 0) : ℚ) : ℝ) : Circ) = 0 := by simp
    rw [e] at hW
    exact hW
  choose W hW hWT using hex
  refine ⟨ε, hε, hI.toFinset.image (fun a : S => (a : ℝ)), ?_,
    fun a => if h : a ∈ S then W ⟨a, h⟩ else Set.univ, ?_, ?_⟩
  · intro a ha
    obtain ⟨a0, -, rfl⟩ := Finset.mem_image.mp ha
    exact a0.2
  · intro a ha
    obtain ⟨a0, -, rfl⟩ := Finset.mem_image.mp ha
    simpa using hW a0
  · rintro x ⟨hx, hxW⟩
    apply hsub
    refine ⟨hball (by simpa [Metric.mem_ball, dist_zero_right] using hx), ?_⟩
    rw [hs.1]
    refine Set.mem_iInter₂.mpr (fun a ha => ?_)
    apply hWT a
    have := hxW (a : ℝ) (Finset.mem_image.mpr ⟨a, hI.mem_toFinset.mpr ha, rfl⟩)
    simpa using this

/-- **Every nonzero rational-valued additive map is unbounded on every `σ_{f,S}`-neighbourhood of `0`.** -/
theorem sigma_unbounded (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (g : ℝ →+ ℚ) (hg : g ≠ 0) (V : Set ℝ)
    (hV : V ∈ @nhds ℝ (sigmaT f S) 0) (B : ℝ) : ∃ x ∈ V, B < |((g x : ℚ) : ℝ)| := by
  classical
  obtain ⟨ε, hε, I, hIS, W, hW, hsub⟩ := sigma_nhds_sub f S V hV
  obtain ⟨y, hy⟩ : ∃ y, g y ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hg (AddMonoidHom.ext hall)
  let d : ℕ := ∏ a ∈ I, (f (a * y)).den
  have hdpos : 0 < d := Finset.prod_pos (fun a _ => (f (a * y)).den_pos)
  have hint : ∀ a ∈ I, ∃ m : ℤ, f (a * y) * d = m := fun a ha =>
    exists_k_of_den_dvd _ _ (Finset.dvd_prod_of_mem _ ha)
  let fam : Option I → (ℝ →+ ℚ) := fun i => match i with
    | none => g
    | some a => fa f (a : ℝ)
  obtain ⟨K, hK⟩ := exists_nat_gt (B / |((g y : ℚ) : ℝ)|)
  have hgy : (0 : ℝ) < |((g y : ℚ) : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast hy
  set k : ℕ := K + 1 with hk
  have hkpos : (1 : ℝ) ≤ k := by simp [hk]
  obtain ⟨z, hzN, hz⟩ := (HkerG_dense fam).exists_mem_open
    (isOpen_Ioo : IsOpen (Set.Ioo (-(((k * d : ℕ) : ℝ) * y) - ε) (-(((k * d : ℕ) : ℝ) * y) + ε)))
    ⟨-(((k * d : ℕ) : ℝ) * y), by constructor <;> linarith⟩
  have hz0 : g z = 0 ∧ ∀ a : I, f ((a : ℝ) * z) = 0 := by
    have h := AddMonoidHom.mem_ker.mp hzN
    refine ⟨?_, fun a => ?_⟩
    · simpa [HmapG_apply, fam] using congrFun h none
    · simpa [HmapG_apply, fam, fa_apply] using congrFun h (some a)
  set x : ℝ := ((k * d : ℕ) : ℝ) * y + z with hx
  have hxabs : |x| < ε := by
    rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]
  have hgx : g x = ((k * d : ℕ) : ℚ) * g y := by
    rw [hx, map_add, hz0.1, add_zero]
    have := f_ratmul g ((k * d : ℕ) : ℚ) y
    simpa using this
  refine ⟨x, hsub ⟨hxabs, fun a ha => ?_⟩, ?_⟩
  · have : (((f (a * x) : ℚ) : ℝ) : Circ) = 0 := by
      obtain ⟨m, hm⟩ := hint a ha
      have hzero : f (a * z) = 0 := hz0.2 ⟨a, ha⟩
      have h1 : f (a * x) = (k : ℚ) * m := by
        rw [hx, mul_add, map_add, hzero, add_zero]
        have : a * (((k * d : ℕ) : ℝ) * y) = (((k * d : ℕ) : ℚ) : ℝ) * (a * y) := by
          push_cast; ring
        rw [this, f_ratmul, ← hm]
        push_cast; ring
      rw [h1]
      have : (((k : ℚ) * m : ℚ) : ℝ) = ((k * m : ℤ) : ℝ) := by push_cast; ring
      rw [this, AddCircle.coe_eq_zero_iff]
      exact ⟨k * m, by simp⟩
    rw [this]
    exact mem_of_mem_nhds (hW a ha)
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

/-- A nonzero rational-valued additive map is not `σ_{f,S}`-continuous (into `ℝ`). -/
theorem not_cont_sigma_rat (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (g : ℝ →+ ℚ) (hg : g ≠ 0) :
    ¬ Continuous[sigmaT f S, (inferInstance : TopologicalSpace ℝ)] (fun x : ℝ => ((g x : ℚ) : ℝ)) := by
  intro h
  have hpre : (fun x : ℝ => ((g x : ℚ) : ℝ)) ⁻¹' Set.Ioo (-1 : ℝ) 1 ∈ @nhds ℝ (sigmaT f S) 0 := by
    have h0 := (@Continuous.continuousAt ℝ ℝ (sigmaT f S) _ _ 0 h)
    have hI : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (((g 0 : ℚ) : ℝ)) := by
      simpa using Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)
    exact h0 hI
  obtain ⟨x, hxV, hxB⟩ := sigma_unbounded f S g hg _ hpre 1
  have h1 : |((g x : ℚ) : ℝ)| < 1 := abs_lt.mpr ⟨hxV.1, hxV.2⟩
  linarith

end LeanCheck
