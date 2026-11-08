import LeanCheck.PVGIdeal

/-!
# PVG: first examples on the real line and joint continuity (Lean check)

Scope. Formal counterpart of Sections 3 and 4 of `PVG_v19`. Convergence relations on `ℝ` are `conv : Filter ℝ → ℝ → Prop`;
"`F` converges to `x` for the Euclidean convergence" is `F ≤ 𝓝 x`.

* `discreteConv` (Example 3.1): `F → x` iff `{x} ∈ F`; `discrete_isPVG`, `discrete_hausdorff`, `discrete_not_coarser`;
* `countableConv` (Example 3.2): `F → x` iff `F ≤ 𝓝 x` and `F` has a countable member: the case of `xiConv` for the ideal of
  countable sets; `countable_isPVG`, `countable_hausdorff`, `countable_not_pretop`, `countable_not_topological`;
* `coarser_of_continuous_one` (Proposition 3.3): a PVG on `ℝ` for which `λ ↦ λ · 1` is continuous from the Euclidean line is
  coarser than the Euclidean convergence;
* `JointCont conv` and `joint_euclid` (Theorem 4.1): a Hausdorff PVG on `ℝ` with jointly continuous scalar multiplication is the
  Euclidean convergence.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology Pointwise Cardinal

namespace PVG
namespace Q95

/-! ### Example 3.1: the discrete pseudotopology -/

/-- `F → x` iff `{x} ∈ F`. -/
def discreteConv (F : Filter ℝ) (x : ℝ) : Prop := ({x} : Set ℝ) ∈ F

theorem discrete_isPVG : IsPVG discreteConv where
  p1 x := by simp [discreteConv]
  p2 := fun hF hGF => hGF hF
  p3 := by
    intro F _ x hU
    have : F ≤ pure x := Filter.le_iff_ultrafilter.2 (fun U hUF => by
      have := hU U hUF
      rw [Filter.le_pure_iff]; exact this)
    exact Filter.le_pure_iff.1 this
  add := by
    intro F G x y hF hG
    have := Filter.image2_mem_map₂ (m := fun a b : ℝ => a + b) hF hG
    simpa [discreteConv] using this
  smul := by
    intro a F x hF
    have h1 : (fun z : ℝ => a • z) '' ({x} : Set ℝ) ∈ F.map (fun z : ℝ => a • z) := Filter.image_mem_map hF
    rw [Set.image_singleton] at h1
    exact h1

theorem discrete_hausdorff : PHausdorff discreteConv := by
  intro F _ x y hx hy
  have := Filter.nonempty_of_mem (Filter.inter_mem hx hy)
  obtain ⟨z, hz1, hz2⟩ := this
  rw [Set.mem_singleton_iff] at hz1 hz2
  rw [← hz1, ← hz2]

/-- The discrete pseudotopology is not coarser than the Euclidean convergence. -/
theorem discrete_not_coarser : ¬ ∀ F x, F ≤ 𝓝 x → discreteConv F x := by
  intro h
  have := h (𝓝 0) 0 le_rfl
  unfold discreteConv at this
  have h2 : (({0} : Set ℝ)) ∈ 𝓝 (0 : ℝ) := this
  rw [mem_nhds_iff] at h2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_nhds_iff.2 h2)
  have hmem : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  have := hball hmem
  rw [Set.mem_singleton_iff] at this
  linarith

/-! ### Example 3.2: countable members -/

lemma exists_Ioo_not_mem {A : Set ℝ} (hA : A.Countable) {a b : ℝ} (hab : a < b) : ∃ d ∈ Set.Ioo a b, d ∉ A := by
  by_contra hno
  push Not at hno
  have hsub : Set.Ioo a b ⊆ A := hno
  have hc : (Set.Ioo a b).Countable := hA.mono hsub
  have h1 : #(Set.Ioo a b) ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.2 hc
  rw [Cardinal.mk_Ioo_real hab] at h1
  exact absurd (Cardinal.aleph0_lt_continuum) (not_lt.2 h1)

/-- The ideal of countable subsets of `ℝ`. -/
theorem countable_isIdeal : IsIdeal ({A : Set ℝ | A.Countable}) where
  mono := fun hA hB => hA.mono hB
  union := fun hA hB => hA.union hB
  single := fun x => Set.countable_singleton x
  ne_univ := by
    intro h
    obtain ⟨d, _, hd⟩ := exists_Ioo_not_mem (show (Set.univ : Set ℝ).Countable from h) (show (0 : ℝ) < 1 by norm_num)
    exact hd (Set.mem_univ d)
  add := fun hA hB => by
    have := hA.image2 hB (fun a b : ℝ => a + b)
    rwa [Set.image2_add] at this
  smul := fun a A hA => by
    have := hA.image (fun z : ℝ => a • z)
    rwa [Set.image_smul] at this

/-- `F → x` iff `F` contains the neighbourhood filter and has a countable member. -/
def countableConv : Filter ℝ → ℝ → Prop := xiConv {A : Set ℝ | A.Countable}

theorem countable_isPVG : IsPVG countableConv := xi_isPVG countable_isIdeal

theorem countable_hausdorff : PHausdorff countableConv := xi_hausdorff

/-- Finer than the Euclidean convergence. -/
theorem countable_finer {F : Filter ℝ} {x : ℝ} (h : countableConv F x) : F ≤ 𝓝 x := h.1

theorem countable_not_pretop : ¬ IsPretop countableConv := by
  refine xi_not_pretop countable_isIdeal (fun A hA => ?_)
  -- distinct points `d n ∈ (0, 1/(n+1)) \ A`
  have hex : ∀ n : ℕ, ∃ d ∈ Set.Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)), d ∉ A := fun n =>
    exists_Ioo_not_mem hA (by positivity)
  choose d hd using hex
  refine ⟨Set.range d, Set.countable_range d, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩
    exact (hd n).2
  · have hlim : Tendsto d atTop (𝓝 0) := by
      refine squeeze_zero (fun n => (hd n).1.1.le) (fun n => (hd n).1.2.le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    exact mem_closure_of_tendsto hlim (Eventually.of_forall (fun n => ⟨n, rfl⟩))

theorem countable_not_topological : ¬ IsTopological countableConv := fun h =>
  countable_not_pretop (topological_isPretop h)

/-! ### Proposition 3.3 -/

/-- If `λ ↦ λ · 1` is continuous from the Euclidean line, the PVG is coarser than the Euclidean convergence. -/
theorem coarser_of_continuous_one {conv : Filter ℝ → ℝ → Prop}
    (h : ∀ F x, F ≤ 𝓝 x → conv (F.map (fun l : ℝ => l * 1)) (x * 1)) : ∀ F x, F ≤ 𝓝 x → conv F x := by
  intro F x hF
  have := h F x hF
  simpa using this

/-! ### Theorem 4.1: joint continuity forces the Euclidean convergence -/

/-- Joint continuity of scalar multiplication: `G → x` Euclidean and `F → y` imply `G·F → x y`. -/
def JointCont (conv : Filter ℝ → ℝ → Prop) : Prop :=
  ∀ (G : Filter ℝ) (x : ℝ) (F : Filter ℝ) (y : ℝ), G ≤ 𝓝 x → conv F y →
    conv (Filter.map₂ (fun l a : ℝ => l * a) G F) (x * y)

lemma map₂_mul_pure_one (G : Filter ℝ) : Filter.map₂ (fun l a : ℝ => l * a) G (pure 1) = G := by
  rw [Filter.map₂_pure_right]; simp

theorem joint_step1 {conv : Filter ℝ → ℝ → Prop} (hp : IsPVG conv) (hj : JointCont conv) :
    ∀ F x, F ≤ 𝓝 x → conv F x := by
  intro F x hF
  have := hj F x (pure 1) 1 hF (hp.p1 1)
  rw [map₂_mul_pure_one, mul_one] at this
  exact this

/-- Step 2: a filter converging to `0` has a bounded member. -/
theorem joint_step2 {conv : Filter ℝ → ℝ → Prop} (hp : IsPVG conv) (hH : PHausdorff conv) (hj : JointCont conv)
    {F : Filter ℝ} (hF : conv F 0) : ∃ A ∈ F, ∃ M : ℝ, ∀ a ∈ A, |a| ≤ M := by
  by_contra hno
  push Not at hno
  -- every member of `F` is unbounded
  have hG : conv (Filter.map₂ (fun l a : ℝ => l * a) (𝓝 0) F) 0 := by
    have := hj (𝓝 0) 0 F 0 le_rfl hF
    simpa using this
  have hall : ∀ x : ℝ, conv (pure x) 0 := by
    intro x
    refine hp.p2 hG ?_
    intro t ht
    obtain ⟨s, hs, A, hA, hst⟩ := Filter.mem_map₂_iff.1 ht
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hs
    have hAu : ∀ M : ℝ, ∃ a ∈ A, M < |a| := by
      intro M
      obtain ⟨a, ha, hM⟩ := hno A hA M
      exact ⟨a, ha, hM⟩
    obtain ⟨a, haA, ha⟩ := hAu (|x| / δ)
    have ha0 : a ≠ 0 := by
      intro h0; rw [h0, abs_zero] at ha
      have : 0 ≤ |x| / δ := by positivity
      linarith
    have hl : x / a ∈ s := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_div]
      have hapos : 0 < |a| := abs_pos.2 ha0
      rw [div_lt_iff₀ hapos]
      rw [div_lt_iff₀ hδ] at ha
      linarith
    have : x / a * a ∈ t := hst ⟨x / a, hl, a, haA, rfl⟩
    rwa [div_mul_cancel₀ x ha0] at this
  have h1 := hH (pure 1) 0 1 (hall 1) (hp.p1 1)
  exact absurd h1 (by norm_num)

/-- Step 3: a filter converging to `0` that has a bounded member contains the Euclidean neighbourhoods of `0`. -/
theorem joint_step3 {conv : Filter ℝ → ℝ → Prop} (hp : IsPVG conv) (hH : PHausdorff conv) (hj : JointCont conv)
    {F : Filter ℝ} (hF : conv F 0) (hb : ∃ A ∈ F, ∃ M : ℝ, ∀ a ∈ A, |a| ≤ M) : F ≤ 𝓝 0 := by
  obtain ⟨B, hB, b, hbB⟩ := hb
  intro W hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
  by_contra hWF
  have hballF : Metric.ball (0 : ℝ) ε ∉ F := fun h => hWF (Filter.mem_of_superset h hball)
  have hne : (F ⊓ 𝓟 (Metric.ball (0 : ℝ) ε)ᶜ).NeBot := by
    rw [Filter.inf_neBot_iff]
    intro s hs t ht
    rw [Filter.mem_principal] at ht
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hballF
    refine Filter.mem_of_superset hs ?_
    intro y hy
    by_contra hyb
    have : y ∈ s ∩ t := ⟨hy, ht hyb⟩
    rw [hemp] at this
    exact this
  set F' := F ⊓ 𝓟 (Metric.ball (0 : ℝ) ε)ᶜ with hF'
  have hF'0 : conv F' 0 := hp.p2 hF inf_le_left
  set K : Set ℝ := Set.Icc (-b) b ∩ (Metric.ball (0 : ℝ) ε)ᶜ with hK
  have hKc : IsCompact K := isCompact_Icc.inter_right Metric.isOpen_ball.isClosed_compl
  have hIcc : Set.Icc (-b) b ∈ F := by
    refine Filter.mem_of_superset hB (fun a ha => ?_)
    have := abs_le.1 (hbB a ha)
    exact ⟨this.1, this.2⟩
  have hKF' : K ∈ F' :=
    Filter.inter_mem (Filter.mem_inf_of_left hIcc) (Filter.mem_inf_of_right (Filter.mem_principal_self _))
  set U : Ultrafilter ℝ := Ultrafilter.of F' with hU
  have hUF' : (U : Filter ℝ) ≤ F' := Ultrafilter.of_le _
  have hKU : K ∈ (U : Filter ℝ) := hUF' hKF'
  obtain ⟨y, hyK, hUy⟩ := hKc.ultrafilter_le_nhds (f := U) (Filter.le_principal_iff.2 hKU)
  have hc1 : conv U y := joint_step1 hp hj _ _ hUy
  have hc2 : conv U 0 := hp.p2 hF'0 hUF'
  have hy0 : y = 0 := hH U y 0 hc1 hc2
  have : y ∈ (Metric.ball (0 : ℝ) ε)ᶜ := hyK.2
  rw [hy0] at this
  exact this (Metric.mem_ball_self hε)

/-- **Theorem 4.1.** A Hausdorff PVG on `ℝ` with jointly continuous scalar multiplication is the Euclidean convergence. -/
theorem joint_euclid {conv : Filter ℝ → ℝ → Prop} (hp : IsPVG conv) (hH : PHausdorff conv) (hj : JointCont conv)
    (F : Filter ℝ) (x : ℝ) : conv F x ↔ F ≤ 𝓝 x := by
  refine ⟨fun h => ?_, joint_step1 hp hj F x⟩
  have h0 : conv (transl x F) 0 := (conv_iff_translate hp F x).1 h
  have h1 : transl x F ≤ 𝓝 0 :=
    joint_step3 hp hH hj h0 (joint_step2 hp hH hj h0)
  unfold transl at h1
  have h2 : F ≤ (F.map (fun z => z - x)).map (fun z => z + x) := by
    rw [Filter.map_map]
    have : ((fun z : ℝ => z + x) ∘ fun z => z - x) = id := by funext z; simp
    rw [this, Filter.map_id]
  refine h2.trans ((Filter.map_mono h1).trans ?_)
  have hc : Tendsto (fun z : ℝ => z + x) (𝓝 0) (𝓝 (0 + x)) := ((continuous_id.add continuous_const : Continuous fun z : ℝ => z + x)).tendsto 0
  simpa using hc

#print axioms discrete_isPVG
#print axioms discrete_hausdorff
#print axioms discrete_not_coarser
#print axioms countable_isPVG
#print axioms countable_not_pretop
#print axioms countable_not_topological
#print axioms coarser_of_continuous_one
#print axioms joint_euclid

end Q95
end PVG
