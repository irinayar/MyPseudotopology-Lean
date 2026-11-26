import Mathlib
import LeanCheck.PVGNoLqcCore
import LeanCheck.PVGCyclicTrace

/-!
# PVGtwo, Section 4: locally quasi-convex topologies for countably many coefficients (Lean check)

Scope. `gamTop δ` is the topology `γ_δ` of the article: the Bohr topology of `ℝ` together with uniform convergence on the characters
`x ↦ δ_k x mod 1`. It is defined as the topology induced by `x ↦ (e x, (δ_k x mod 1)_k)` into `K × (ℕ →ᵇ ℝ/ℤ)`. In Mathlib's order
`t₁ ≤ t₂` means that `t₁` is finer. `dint u` is the distance from `u` to the nearest integer. The sequence `t` is indexed from `0`.
`LQC t` says that every neighbourhood of `0` contains a neighbourhood of `0` that is an intersection of preimages of the arc
`{‖z‖ ≤ 1/4}` under continuous characters.

* `gam_group`, `gam_le_bohr`, `gam_coarser_euclid`, `gam_lqc` : Lemma 4.1, first part;
* `gam_not_precompact`, `gam_ne_bohr` : Lemma 4.1, second part (and the first claim of Corollary 4.8);
* `trace_eq` : Proposition 4.2 (a);
* `inA_of_trace` : Proposition 4.2 (b);
* `inA_of_step1` : the direction (a) ⇒ (b) of Corollary 4.3, **conditional on Step 1** of the proof of Proposition 16.1 of PVG_v57,
  which is the hypothesis `hV`, `hc` and is not proved in Lean;
* `syndetic` : Lemma 4.4;
* `small` : Lemma 4.5;
* `exists_seq`, `countable_witness` : Theorem 4.6.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set
open scoped Pointwise BoundedContinuousFunction

namespace PVG
namespace Two
open Q95 Lac

/-- The usual topology of the circle, named outside the scope of any variable topology on `ℝ`. -/
abbrev circleTop : TopologicalSpace (AddCircle (1 : ℝ)) := inferInstance

/-- The Euclidean neighbourhood filter of `x`, named outside the scope of any variable topology on `ℝ`. -/
def euclidNhds (x : ℝ) : Filter ℝ := 𝓝 x

lemma tendsto_sub_euclid (c : ℕ → ℝ) (c0 : ℝ) (h : Tendsto c atTop (euclidNhds c0)) :
    Tendsto (fun k => c k - c0) atTop (𝓝 0) := by
  have h' : Tendsto c atTop (𝓝 c0) := h
  have := h'.sub_const c0
  simpa using this

lemma mem_nhds_translate (τ : TopologicalSpace ℝ) (hτ : @IsTopologicalAddGroup ℝ τ _) (x0 : ℝ) (W : Set ℝ) :
    W ∈ @nhds ℝ τ x0 ↔ (fun y => x0 + y) ⁻¹' W ∈ @nhds ℝ τ 0 := by
  letI : TopologicalSpace ℝ := τ
  haveI : IsTopologicalAddGroup ℝ := hτ
  rw [← map_add_left_nhds_zero x0]
  rfl

/-! ## The distance to the nearest integer -/

lemma dint_nonneg (u : ℝ) : 0 ≤ dint u := norm_nonneg _

lemma dint_zero : dint 0 = 0 := by simp [dint]

lemma dint_eq (u : ℝ) : dint u = |u - round u| := by
  unfold dint; exact UnitAddCircle.norm_eq

lemma dint_le_half (u : ℝ) : dint u ≤ 1 / 2 := by
  rw [dint_eq]; exact abs_sub_round u

lemma dint_sub_le (u v : ℝ) : dint (u - v) ≤ dint u + dint v := by
  have h := dint_add_le u (-v)
  rwa [← sub_eq_add_neg, dint_neg] at h

lemma dint_natmul_le (i : ℕ) (u : ℝ) : dint (i * u) ≤ i * dint u := by
  induction i with
  | zero => simp [dint_zero]
  | succ n ih =>
    have h := dint_add_le (n * u) u
    have e1 : ((n + 1 : ℕ) : ℝ) * u = n * u + u := by push_cast; ring
    rw [e1]; push_cast; linarith

lemma dint_half : dint (1 / 2) = 1 / 2 := by
  unfold dint
  have h : ‖((1 / 2 : ℝ) : AddCircle (1 : ℝ))‖ = |(1 / 2 : ℝ)| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 (by norm_num)
  rw [h]; norm_num

lemma dint_sub_int (u : ℝ) (z : ℤ) : dint (u - z) = dint u := by
  rw [dint_eq, dint_eq, round_sub_intCast]
  congr 1; push_cast; ring

/-- If `‖i u‖ ≤ 1/4` for `i = 1, …, m`, then `‖u‖ ≤ 1/(4m)`. -/
lemma dint_le_of_multiples (m : ℕ) (hm : 0 < m) (u : ℝ)
    (h : ∀ i : ℕ, 1 ≤ i → i ≤ m → dint (i * u) ≤ 1 / 4) : dint u ≤ 1 / (4 * m) := by
  set r : ℝ := u - round u with hr
  have hur : dint u = |r| := dint_eq u
  have hir : ∀ i : ℕ, dint (i * u) = dint (i * r) := by
    intro i
    have e1 : (i : ℝ) * r = i * u - ((i * round u : ℤ) : ℝ) := by rw [hr]; push_cast; ring
    rw [e1, dint_sub_int]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [hur]
  by_contra hc
  push Not at hc
  have hr14 : |r| ≤ 1 / 4 := by
    have := h 1 le_rfl hm
    simpa [hur] using this
  have hex : ∃ i : ℕ, 1 / 4 < i * |r| := by
    refine ⟨m, ?_⟩
    have := mul_lt_mul_of_pos_left hc hm'
    have e2 : (m : ℝ) * (1 / (4 * m)) = 1 / 4 := by field_simp
    linarith
  classical
  set i := Nat.find hex with hi
  have hi1 : 1 / 4 < (i : ℝ) * |r| := Nat.find_spec hex
  have hi0 : i ≠ 0 := by
    intro h0; rw [h0] at hi1; norm_num at hi1
  have him : i ≤ m := by
    refine Nat.find_le ?_
    have := mul_lt_mul_of_pos_left hc hm'
    have e2 : (m : ℝ) * (1 / (4 * m)) = 1 / 4 := by field_simp
    linarith
  have hprev : ((i - 1 : ℕ) : ℝ) * |r| ≤ 1 / 4 := by
    have := Nat.find_min hex (show i - 1 < i by omega)
    exact not_lt.1 this
  have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast] at hprev
  have hle : (i : ℝ) * |r| ≤ 1 / 2 := by nlinarith
  have habs : |(i : ℝ) * r| = i * |r| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg i)]
  have hd : dint (i * r) = i * |r| := by
    unfold dint
    have h2 : ‖(((i : ℝ) * r : ℝ) : AddCircle (1 : ℝ))‖ = |(i : ℝ) * r| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 (by rw [habs]; simpa using hle)
    rw [h2, habs]
  have := h i (by omega) him
  rw [hir, hd] at this
  linarith

/-! ## Bohr neighbourhoods -/

/-- Basic Bohr neighbourhoods of `0`. -/
def bset (F : Finset ℝ) (η : ℝ) : Set ℝ := {x | ∀ b ∈ F, dint (b * x) < η}

lemma bset_mem (F : Finset ℝ) {η : ℝ} (hη : 0 < η) : bset F η ∈ @nhds ℝ bohrTop 0 := by
  have h : bset F η = ⋂ b ∈ F, {x : ℝ | dint (b * x) < η} := by
    ext x; simp [bset]
  rw [h]
  exact (Filter.biInter_finset_mem F).2 fun b _ => dint_mem_nhds_bohr b hη

lemma exists_bset_subset {B : Set ℝ} (hB : B ∈ @nhds ℝ bohrTop 0) :
    ∃ (F : Finset ℝ) (η : ℝ), 0 < η ∧ bset F η ⊆ B := by
  rw [nhds_bohr, e_zero] at hB
  obtain ⟨V, hV, hVB⟩ := Filter.mem_comap.1 hB
  rw [isEmbedding_coe.isInducing.nhds_eq_comap] at hV
  obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.1 hV
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, hI, t, ht, htW⟩ := hW
  have h1 : ∀ b, ∃ r > 0, Metric.ball (0 : AddCircle (1 : ℝ)) r ⊆ t b := fun b =>
    Metric.mem_nhds_iff.1 (by simpa using ht b)
  choose r hr0 hr using h1
  have hmin : ∀ s : Finset ℝ, ∃ η : ℝ, 0 < η ∧ ∀ b ∈ s, η ≤ r b := by
    intro s
    classical
    induction s using Finset.induction with
    | empty => exact ⟨1, one_pos, by simp⟩
    | insert a s _ ih =>
      obtain ⟨η, hη, h⟩ := ih
      refine ⟨min η (r a), lt_min hη (hr0 a), fun b hb => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h b hb)
  obtain ⟨η, hη0, hη⟩ := hmin hI.toFinset
  refine ⟨hI.toFinset, η, hη0, fun x hx => hVB (hWV (htW fun b hb => hr b ?_))⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hb' : b ∈ hI.toFinset := by simpa using hb
  have := lt_of_lt_of_le (hx b hb') (hη b hb')
  simpa [dint] using this

/-- The Bohr topology is precompact. -/
lemma bohr_tb (F : Finset ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ X : Finset ℝ, ∀ x : ℝ, ∃ x0 ∈ X, x - x0 ∈ bset F η := by
  set U : Set K := {κ | ∀ b ∈ F, ‖κ b‖ < η} with hU
  have hUo : IsOpen U := by
    have h : U = ⋂ b ∈ F, (fun κ : K => κ b) ⁻¹' {z | ‖z‖ < η} := by ext κ; simp [hU]
    rw [h]
    exact isOpen_biInter_finset fun b _ => (isOpen_lt continuous_norm continuous_const).preimage (continuous_eval b)
  have h0 : (0 : K) ∈ U := fun b _ => by simpa using hη
  have hcov : closure (range e) ⊆ ⋃ x0 : ℝ, (fun κ : K => κ - e x0) ⁻¹' U := by
    intro κ hκ
    have ho : IsOpen ((fun κ' : K => κ - κ') ⁻¹' U) := hUo.preimage (continuous_const.sub continuous_id)
    have hm : κ ∈ (fun κ' : K => κ - κ') ⁻¹' U := by simpa using h0
    obtain ⟨κ', h1, x0, rfl⟩ := mem_closure_iff.1 hκ _ ho hm
    exact mem_iUnion.2 ⟨x0, h1⟩
  obtain ⟨X, hX⟩ := isClosed_closure.isCompact.elim_finite_subcover _
    (fun x0 => hUo.preimage (continuous_id.sub continuous_const)) hcov
  refine ⟨X, fun x => ?_⟩
  have h := hX (subset_closure (mem_range_self x))
  simp only [mem_iUnion, exists_prop] at h
  obtain ⟨x0, hx0, h⟩ := h
  refine ⟨x0, hx0, fun b hb => ?_⟩
  have h' := h b hb
  unfold dint
  rw [mul_sub, AddCircle.coe_sub]
  simpa using h'

/-! ## The topology `γ_δ` -/

/-- `x ↦ (δ_k x mod 1)_k` as a homomorphism into bounded sequences with the supremum norm. -/
noncomputable def Phi (δ : ℕ → ℝ) : ℝ →+ (ℕ →ᵇ AddCircle (1 : ℝ)) where
  toFun x := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun k => ((δ k * x : ℝ) : AddCircle (1 : ℝ))) (1 / 2) (fun k => dint_le_half _)
  map_zero' := by
    ext k; simp
  map_add' x y := by
    ext k
    show ((δ k * (x + y) : ℝ) : AddCircle (1 : ℝ)) =
      ((δ k * x : ℝ) : AddCircle (1 : ℝ)) + ((δ k * y : ℝ) : AddCircle (1 : ℝ))
    rw [mul_add, AddCircle.coe_add]

lemma Phi_apply (δ : ℕ → ℝ) (x : ℝ) (k : ℕ) : Phi δ x k = ((δ k * x : ℝ) : AddCircle (1 : ℝ)) := rfl

lemma norm_Phi_le (δ : ℕ → ℝ) (x : ℝ) {η : ℝ} (hη : 0 ≤ η) : ‖Phi δ x‖ ≤ η ↔ ∀ k, dint (δ k * x) ≤ η := by
  rw [BoundedContinuousFunction.norm_le hη]; rfl

noncomputable def gamHom (δ : ℕ → ℝ) : ℝ →+ K × (ℕ →ᵇ AddCircle (1 : ℝ)) := eHom.prod (Phi δ)

set_option warn.classDefReducibility false in
/-- The topology `γ_δ`. -/
noncomputable def gamTop (δ : ℕ → ℝ) : TopologicalSpace ℝ := TopologicalSpace.induced (gamHom δ) inferInstance

theorem gam_group (δ : ℕ → ℝ) : @IsTopologicalAddGroup ℝ (gamTop δ) _ :=
  isTopologicalAddGroup_induced (gamHom δ)

lemma gamTop_eq (δ : ℕ → ℝ) : gamTop δ = bohrTop ⊓ TopologicalSpace.induced (Phi δ) inferInstance := by
  unfold gamTop bohrTop
  rw [instTopologicalSpaceProd, induced_inf, induced_compose, induced_compose]
  rfl

theorem gam_le_bohr (δ : ℕ → ℝ) : gamTop δ ≤ bohrTop := by
  rw [gamTop_eq]; exact inf_le_left

lemma mem_nhds_gam (δ : ℕ → ℝ) (W : Set ℝ) :
    W ∈ @nhds ℝ (gamTop δ) 0 ↔
      ∃ B ∈ @nhds ℝ bohrTop 0, ∃ η : ℝ, 0 < η ∧ ∀ x ∈ B, (∀ k, dint (δ k * x) ≤ η) → x ∈ W := by
  have h : @nhds ℝ (gamTop δ) 0 =
      @nhds ℝ bohrTop 0 ⊓ Filter.comap (Phi δ) (𝓝 (0 : ℕ →ᵇ AddCircle (1 : ℝ))) := by
    rw [gamTop_eq]
    have h1 := @nhds_inf ℝ bohrTop (TopologicalSpace.induced (Phi δ) inferInstance) 0
    have h2 := @nhds_induced _ _ (inferInstance : TopologicalSpace (ℕ →ᵇ AddCircle (1 : ℝ))) (Phi δ) (0 : ℝ)
    rw [map_zero] at h2
    exact h1.trans (congrArg _ h2)
  rw [h, Filter.mem_inf_iff_superset]
  constructor
  · rintro ⟨B, hB, C, hC, hBC⟩
    obtain ⟨V, hV, hVC⟩ := Filter.mem_comap.1 hC
    obtain ⟨η, hη, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
    refine ⟨B, hB, η, hη, fun x hx hk => hBC ⟨hx, hVC (hball ?_)⟩⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_Phi_le δ x hη.le]
    exact hk
  · rintro ⟨B, hB, η, hη, hW⟩
    refine ⟨B, hB, Phi δ ⁻¹' Metric.closedBall 0 η,
      Filter.preimage_mem_comap (Metric.closedBall_mem_nhds _ hη), fun x hx => hW x hx.1 ?_⟩
    have h2 := hx.2
    rwa [mem_preimage, Metric.mem_closedBall, dist_zero_right, norm_Phi_le δ x hη.le] at h2

/-- `γ_δ` is coarser than the Euclidean topology. -/
theorem gam_coarser_euclid (δ : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |δ k| ≤ M) (x : ℝ) : 𝓝 x ≤ @nhds ℝ (gamTop δ) x := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hPhi : Continuous (Phi δ) := by
    refine (LipschitzWith.of_dist_le_mul (K := ⟨M, hM0⟩) fun a b => ?_).continuous
    rw [dist_eq_norm, ← map_sub, Real.dist_eq]
    show ‖Phi δ (a - b)‖ ≤ M * |a - b|
    rw [norm_Phi_le δ _ (mul_nonneg hM0 (abs_nonneg _))]
    intro k
    refine (dint_le_abs _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hM k) (abs_nonneg _)
  have c : Continuous (gamHom δ) := continuous_e.prodMk hPhi
  have h : (inferInstance : TopologicalSpace ℝ) ≤ gamTop δ := c.le_induced
  exact nhds_mono h

/-- Every neighbourhood of `0` contains a neighbourhood that is an intersection of preimages of the quarter arc under continuous
characters. -/
def LQC (t : TopologicalSpace ℝ) : Prop :=
  ∀ W ∈ @nhds ℝ t 0, ∃ S : Set (ℝ →+ AddCircle (1 : ℝ)),
    (∀ χ ∈ S, @Continuous ℝ (AddCircle (1 : ℝ)) t circleTop χ) ∧ {x | ∀ χ ∈ S, ‖χ x‖ ≤ 1 / 4} ∈ @nhds ℝ t 0 ∧ {x | ∀ χ ∈ S, ‖χ x‖ ≤ 1 / 4} ⊆ W

lemma e_continuous_gam (δ : ℕ → ℝ) (c : ℝ) :
    @Continuous ℝ (AddCircle (1 : ℝ)) (gamTop δ) circleTop (e c) := by
  have h1 : Continuous (fun p : K × (ℕ →ᵇ AddCircle (1 : ℝ)) => p.1 c) := (continuous_eval c).comp continuous_fst
  have h2 : @Continuous ℝ (K × (ℕ →ᵇ AddCircle (1 : ℝ))) (gamTop δ) _ (gamHom δ) := continuous_induced_dom
  have h3 : (e c : ℝ → AddCircle (1 : ℝ)) = (fun p : K × (ℕ →ᵇ AddCircle (1 : ℝ)) => p.1 c) ∘ (gamHom δ) := by
    funext x
    show e c x = e x c
    simp [mul_comm]
  rw [h3]
  exact @Continuous.comp ℝ (K × (ℕ →ᵇ AddCircle (1 : ℝ))) (AddCircle (1 : ℝ)) (gamTop δ) _ circleTop
    (gamHom δ) (fun p => p.1 c) h1 h2

theorem gam_lqc (δ : ℕ → ℝ) : LQC (gamTop δ) := by
  intro W hW
  obtain ⟨B, hB, η, hη, hBW⟩ := (mem_nhds_gam δ W).1 hW
  obtain ⟨F, η', hη', hF⟩ := exists_bset_subset hB
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < min η η' from lt_min hη hη')
  set M : ℕ := m + 1 with hMdef
  have hM0 : 0 < M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hsmall : (1 : ℝ) / (4 * M) < min η η' := by
    refine lt_of_le_of_lt ?_ hm
    have e1 : (M : ℝ) = (m : ℝ) + 1 := by rw [hMdef]; push_cast; ring
    rw [e1]
    exact one_div_le_one_div_of_le (by positivity) (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  set Sb : Set ℝ := (F : Set ℝ) ∪ range δ with hSb
  set S : Set (ℝ →+ AddCircle (1 : ℝ)) := {χ | ∃ i : ℕ, 1 ≤ i ∧ i ≤ M ∧ ∃ b ∈ Sb, χ = e (i * b)} with hS
  have hval : ∀ (i : ℕ) (b x : ℝ), ‖e (i * b) x‖ = dint (i * (b * x)) := by
    intro i b x
    unfold dint
    rw [e_apply]
    congr 2; ring
  have hsub : ∀ x, (∀ χ ∈ S, ‖χ x‖ ≤ 1 / 4) → ∀ b ∈ Sb, dint (b * x) ≤ 1 / (4 * M) := by
    intro x hx b hb
    refine dint_le_of_multiples M hM0 _ fun i hi1 hiM => ?_
    rw [← hval]
    exact hx _ ⟨i, hi1, hiM, b, hb, rfl⟩
  refine ⟨S, ?_, ?_, ?_⟩
  · rintro χ ⟨i, _, _, b, _, rfl⟩
    exact e_continuous_gam δ _
  · refine (mem_nhds_gam δ _).2 ⟨bset F (1 / (4 * M)), bset_mem F (by positivity), 1 / (4 * M), by positivity, ?_⟩
    rintro x hx hk χ ⟨i, _, hiM, b, hb, rfl⟩
    have hb' : dint (b * x) ≤ 1 / (4 * M) := by
      rcases hb with hb | ⟨k, rfl⟩
      · exact (hx b hb).le
      · exact hk k
    rw [hval]
    refine (dint_natmul_le i _).trans ?_
    have h1 : (i : ℝ) * dint (b * x) ≤ M * (1 / (4 * M)) :=
      mul_le_mul (by exact_mod_cast hiM) hb' (dint_nonneg _) hMr.le
    have e2 : (M : ℝ) * (1 / (4 * M)) = 1 / 4 := by field_simp
    linarith
  · intro x hx
    have h := hsub x hx
    refine hBW x (hF fun b hb => ?_) fun k => ?_
    · exact lt_of_le_of_lt (h b (Or.inl hb)) (lt_of_lt_of_le hsmall (min_le_right _ _))
    · exact (h (δ k) (Or.inr ⟨k, rfl⟩)).trans (hsmall.le.trans (min_le_left _ _))

/-! ## `γ_δ` is not precompact -/

/-- If finitely many translates of `W` cover `ℝ` and `‖δ_k w‖ ≤ 1/8` for `w ∈ W`, then `δ` takes only finitely many values. -/
lemma finite_range_of_tb (δ : ℕ → ℝ) (W : Set ℝ) (X : Finset ℝ) (hX : ∀ x, ∃ x0 ∈ X, x - x0 ∈ W)
    (hW : ∀ w ∈ W, ∀ k, dint (δ k * w) ≤ 1 / 8) : (range δ).Finite := by
  by_contra hinf
  have hinf' : (range δ).Infinite := hinf
  set c : ℕ → ℝ := fun n => (Set.Infinite.natEmbedding _ hinf' n : ℝ) with hc
  have hcinj : Function.Injective c := fun a b h =>
    (Set.Infinite.natEmbedding _ hinf').injective (Subtype.ext h)
  have hcr : ∀ n, ∃ k, δ k = c n := fun n => (Set.Infinite.natEmbedding _ hinf' n).2
  set v : ℕ → (X → AddCircle (1 : ℝ)) := fun n x0 => ((c n * (x0 : ℝ) : ℝ) : AddCircle (1 : ℝ)) with hv
  obtain ⟨z, _, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := v) (fun _ => mem_univ _)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq (1 / 8) (by norm_num)
  have hdist := hN N le_rfl (N + 1) (by omega)
  set n := φ N with hn
  set n' := φ (N + 1) with hn'
  have hne : n ≠ n' := (hφ (show N < N + 1 by omega)).ne
  set d : ℝ := c n - c n' with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 fun h => hne (hcinj h)
  obtain ⟨x0, hx0, hw⟩ := hX (1 / (2 * d))
  have h1 : dint (d * x0) < 1 / 8 := by
    have h2 := (dist_pi_lt_iff (by norm_num : (0 : ℝ) < 1 / 8)).1 hdist ⟨x0, hx0⟩
    rw [Function.comp, Function.comp, dist_eq_norm] at h2
    unfold dint
    rw [hd, sub_mul, AddCircle.coe_sub]
    exact h2
  obtain ⟨k, hk⟩ := hcr n
  obtain ⟨k', hk'⟩ := hcr n'
  have h3 : dint (c n * (1 / (2 * d) - x0)) ≤ 1 / 8 := hk ▸ hW _ hw k
  have h4 : dint (c n' * (1 / (2 * d) - x0)) ≤ 1 / 8 := hk' ▸ hW _ hw k'
  have h5 : d * (1 / (2 * d)) =
      d * x0 + (c n * (1 / (2 * d) - x0) - c n' * (1 / (2 * d) - x0)) := by
    rw [hd]; ring
  have h6 : d * (1 / (2 * d)) = 1 / 2 := by field_simp
  have h7 := dint_add_le (d * x0) (c n * (1 / (2 * d) - x0) - c n' * (1 / (2 * d) - x0))
  have h8 := dint_sub_le (c n * (1 / (2 * d) - x0)) (c n' * (1 / (2 * d) - x0))
  rw [← h5, h6, dint_half] at h7
  linarith

/-- Lemma 4.1, second part: if `δ` takes infinitely many values, `γ_δ` is not precompact. -/
theorem gam_not_precompact (δ : ℕ → ℝ) (hinf : (range δ).Infinite) :
    ¬ ∀ W ∈ @nhds ℝ (gamTop δ) 0, ∃ X : Finset ℝ, ∀ x, ∃ x0 ∈ X, x - x0 ∈ W := by
  intro h
  have hW : {x : ℝ | ∀ k, dint (δ k * x) ≤ 1 / 8} ∈ @nhds ℝ (gamTop δ) 0 :=
    (mem_nhds_gam δ _).2 ⟨univ, Filter.univ_mem, 1 / 8, by norm_num, fun x _ hx => hx⟩
  obtain ⟨X, hX⟩ := h _ hW
  exact hinf (finite_range_of_tb δ _ X hX fun w hw => hw)

theorem gam_ne_bohr (δ : ℕ → ℝ) (hinf : (range δ).Infinite) : gamTop δ ≠ bohrTop := by
  intro heq
  refine gam_not_precompact δ hinf fun W hW => ?_
  rw [heq] at hW
  obtain ⟨F, η, hη, hF⟩ := exists_bset_subset hW
  obtain ⟨X, hX⟩ := bohr_tb F hη
  refine ⟨X, fun x => ?_⟩
  obtain ⟨x0, hx0, h⟩ := hX x
  exact ⟨x0, hx0, hF h⟩

/-! ## The trace on the pieces -/

/-- `T = {0} ∪ {± t_n}`. -/
def Tset (t : ℕ → ℝ) : Set ℝ := {x | x = 0 ∨ ∃ n, x = t n ∨ x = -t n}

/-- `a₁ T + ⋯ + a_r T`. -/
def sumT (t : ℕ → ℝ) : List ℝ → Set ℝ
  | [] => {0}
  | a :: l => a • Tset t + sumT t l

/-- `a ∈ A(δ)`. -/
def InA (δ t : ℕ → ℝ) (a : ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ n, dint (a * δ k * t n) ≤ ε

lemma sumT_bound (δ t : ℕ → ℝ) :
    ∀ l : List ℝ, (∀ a ∈ l, InA δ t a) → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ sumT t l, dint (δ k * x) ≤ ε := by
  intro l
  induction l with
  | nil =>
    intro _ ε hε
    refine Eventually.of_forall fun k x hx => ?_
    have : x = 0 := by simpa [sumT] using hx
    rw [this, mul_zero, dint_zero]; exact hε.le
  | cons a l ih =>
    intro hl ε hε
    have h1 := hl a List.mem_cons_self (ε / 2) (by linarith)
    have h2 := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)) (ε / 2) (by linarith)
    filter_upwards [h1, h2] with k hk1 hk2
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.1 hx
    obtain ⟨τ, hτ, rfl⟩ := Set.mem_smul_set.1 hu
    have hτb : dint (δ k * (a • τ)) ≤ ε / 2 := by
      rw [smul_eq_mul]
      rcases hτ with rfl | ⟨n, rfl | rfl⟩
      · rw [mul_zero, mul_zero, dint_zero]; linarith
      · have e1 : δ k * (a * t n) = a * δ k * t n := by ring
        rw [e1]; exact hk1 n
      · have e1 : δ k * (a * -t n) = -(a * δ k * t n) := by ring
        rw [e1, dint_neg]; exact hk1 n
    rw [mul_add]
    have := dint_add_le (δ k * (a • τ)) (δ k * v)
    have := hk2 v hv
    linarith

/-- Proposition 4.2 (a). -/
theorem trace_eq (δ t : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (m : ℝ) (l : List ℝ) (hl : ∀ a ∈ l, InA δ t a)
    (J : Set ℝ) (hJ : J ⊆ Icc (-m) m + sumT t l) :
    TopologicalSpace.induced (Subtype.val : J → ℝ) (gamTop δ) =
      TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop := by
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ J, dint (δ k * x) ≤ ε := by
    intro ε hε
    have h1 := sumT_bound δ t l hl (ε / 2) (by linarith)
    have h2 : Tendsto (fun k => |δ k| * |m|) atTop (𝓝 0) := by
      have := (hδ.abs).mul_const |m|
      simpa using this
    have h3 := h2.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
    filter_upwards [h1, h3] with k hk1 hk3
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.1 (hJ hx)
    have hu' : |u| ≤ |m| := (abs_le.2 ⟨hu.1, hu.2⟩).trans (le_abs_self m)
    have hub : dint (δ k * u) ≤ ε / 2 := by
      refine (dint_le_abs _).trans ?_
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hu' (abs_nonneg _)).trans hk3.le
    rw [mul_add]
    have := dint_add_le (δ k * u) (δ k * v)
    have := hk1 v hv
    linarith
  refine le_antisymm (induced_mono (gam_le_bohr δ)) ?_
  have hc : @Continuous J ℝ (TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop) (gamTop δ) Subtype.val := by
    letI : TopologicalSpace J := TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop
    refine (@continuous_iff_continuousAt J ℝ _ (gamTop δ) _).2 fun x0 => ?_
    intro W hW
    have hW0 : (fun y => (x0 : ℝ) + y) ⁻¹' W ∈ @nhds ℝ (gamTop δ) 0 :=
      (mem_nhds_translate _ (gam_group δ) _ _).1 hW
    obtain ⟨B, hB, η, hη, hBW⟩ := (mem_nhds_gam δ _).1 hW0
    obtain ⟨K0, hK0⟩ := eventually_atTop.1 (hbound (η / 2) (by linarith))
    set C : Set ℝ := B ∩ ⋂ k ∈ Finset.range K0, {y : ℝ | dint (δ k * y) < η} with hC
    have hCmem : C ∈ @nhds ℝ bohrTop 0 :=
      Filter.inter_mem hB ((Filter.biInter_finset_mem _).2 fun k _ => dint_mem_nhds_bohr (δ k) hη)
    have hsub : (fun x => x - (x0 : ℝ)) ⁻¹' C ∈ @nhds ℝ bohrTop (x0 : ℝ) := by
      refine (mem_nhds_translate _ bohr_isTopologicalAddGroup _ _).2 ?_
      have e1 : (fun y => (x0 : ℝ) + y) ⁻¹' ((fun x => x - (x0 : ℝ)) ⁻¹' C) = C := by
        ext y
        simp
      rw [e1]
      exact hCmem
    have hJn := @nhds_induced _ _ bohrTop (Subtype.val : J → ℝ) x0
    rw [Filter.mem_map]
    refine hJn.symm ▸ Filter.mem_comap.2 ⟨_, hsub, fun x hx => ?_⟩
    have hx' : (x : ℝ) - x0 ∈ C := hx
    have hall : ∀ k, dint (δ k * ((x : ℝ) - x0)) ≤ η := by
      intro k
      by_cases hk : k < K0
      · have := mem_iInter₂.1 hx'.2 k (Finset.mem_range.2 hk)
        exact le_of_lt this
      · have h1 := hK0 k (by omega) _ x.2
        have h2 := hK0 k (by omega) _ x0.2
        rw [mul_sub]
        have := dint_sub_le (δ k * (x : ℝ)) (δ k * (x0 : ℝ))
        linarith
    have := hBW _ hx'.1 hall
    simpa using this
  exact continuous_iff_le_induced.1 hc

/-- Proposition 4.2 (b), from the neighbourhoods of `0`. -/
theorem inA_of_trace (δ t : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (a : ℝ)
    (h : ∀ W ∈ @nhds ℝ (gamTop δ) 0, ∃ B ∈ @nhds ℝ bohrTop 0,
      B ∩ (Icc (-1 : ℝ) 1 + (a • Tset t + (-a) • Tset t)) ⊆ W) : InA δ t a := by
  intro ε hε
  by_contra hcon
  have hfreq : ∃ᶠ k in atTop, ∃ n, ε < dint (a * δ k * t n) := by
    refine (not_eventually.1 hcon).mono fun k hk => ?_
    push Not at hk
    exact hk
  have hsmall : ∀ n : ℕ, ∀ᶠ k in atTop, dint (a * δ k * t n) < ε := by
    intro n
    have h1 : Tendsto (fun k => a * δ k * t n) atTop (𝓝 0) := by
      have := ((hδ.const_mul a).mul_const (t n))
      simpa using this
    have h2 : Tendsto (fun k => dint (a * δ k * t n)) atTop (𝓝 (dint 0)) := (continuous_dint.tendsto 0).comp h1
    rw [dint_zero] at h2
    exact h2.eventually (Iio_mem_nhds hε)
  have hstep : ∀ K0 N : ℕ, ∃ k n : ℕ, K0 < k ∧ N < n ∧ ε < dint (a * δ k * t n) := by
    intro K0 N
    have hall : ∀ᶠ k in atTop, ∀ n ∈ Finset.range (N + 1), dint (a * δ k * t n) < ε :=
      (Finset.range (N + 1)).eventually_all.2 fun n _ => hsmall n
    obtain ⟨k, ⟨n, hn⟩, hk1, hk2⟩ := (hfreq.and_eventually (hall.and (eventually_gt_atTop K0))).exists
    refine ⟨k, n, hk2, ?_, hn⟩
    by_contra hle
    have := hk1 n (Finset.mem_range.2 (by omega))
    linarith
  choose f g hf hg hfg using hstep
  set p : ℕ → ℕ × ℕ := fun i => Nat.rec (f 0 0, g 0 0) (fun _ q => (f q.1 q.2, g q.1 q.2)) i with hp
  have hps : ∀ i, p (i + 1) = (f (p i).1 (p i).2, g (p i).1 (p i).2) := fun i => rfl
  set kk : ℕ → ℕ := fun i => (p i).1 with hkk
  set nn : ℕ → ℕ := fun i => (p i).2 with hnn
  have hkmono : StrictMono kk := strictMono_nat_of_lt_succ fun i => by
    show (p i).1 < (p (i + 1)).1
    rw [hps]; exact hf _ _
  have hbig : ∀ i, ε < dint (a * δ (kk i) * t (nn i)) := by
    intro i
    cases i with
    | zero => exact hfg 0 0
    | succ j => exact hfg _ _
  set x : ℕ → ℝ := fun i => a * t (nn i) with hx
  have hW : {y : ℝ | ∀ k, dint (δ k * y) ≤ ε / 3} ∈ @nhds ℝ (gamTop δ) 0 :=
    (mem_nhds_gam δ _).2 ⟨univ, Filter.univ_mem, ε / 3, by linarith, fun y _ hy => hy⟩
  obtain ⟨B, hB, hBW⟩ := h _ hW
  obtain ⟨F, η, hη, hF⟩ := exists_bset_subset hB
  obtain ⟨X, hX⟩ := bohr_tb F (show 0 < η / 2 by linarith)
  have hpig : ∃ x0 ∈ X, {i : ℕ | x i - x0 ∈ bset F (η / 2)}.Infinite := by
    by_contra hc
    push Not at hc
    have hfin : (⋃ x0 ∈ X, {i : ℕ | x i - x0 ∈ bset F (η / 2)}).Finite :=
      X.finite_toSet.biUnion fun x0 hx0 => hc x0 hx0
    refine Set.infinite_univ (hfin.subset fun i _ => ?_)
    obtain ⟨x0, hx0, h⟩ := hX (x i)
    exact mem_biUnion hx0 h
  obtain ⟨x0, _, hinf⟩ := hpig
  obtain ⟨i, hi⟩ := hinf.nonempty
  have hfr : ∃ᶠ j in atTop, x j - x0 ∈ bset F (η / 2) := Nat.frequently_atTop_iff_infinite.2 hinf
  have hev : ∀ᶠ j in atTop, dint (δ (kk j) * x i) < ε / 3 := by
    have h1 : Tendsto (fun j => δ (kk j) * x i) atTop (𝓝 0) := by
      have := (hδ.comp hkmono.tendsto_atTop).mul_const (x i)
      simpa using this
    have h2 : Tendsto (fun j => dint (δ (kk j) * x i)) atTop (𝓝 (dint 0)) := (continuous_dint.tendsto 0).comp h1
    rw [dint_zero] at h2
    exact h2.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨j, hj, hjev⟩ := (hfr.and_eventually hev).exists
  have hmem : x j - x i ∈ B := by
    refine hF fun b hb => ?_
    have e1 : b * (x j - x i) = b * (x j - x0) - b * (x i - x0) := by ring
    rw [e1]
    have h1 := hj b hb
    have h2 := hi b hb
    have := dint_sub_le (b * (x j - x0)) (b * (x i - x0))
    linarith
  have hJa : x j - x i ∈ Icc (-1 : ℝ) 1 + (a • Tset t + (-a) • Tset t) := by
    refine Set.mem_add.2 ⟨0, by norm_num, x j - x i, ?_, zero_add _⟩
    refine Set.mem_add.2 ⟨a * t (nn j), ⟨t (nn j), Or.inr ⟨nn j, Or.inl rfl⟩, rfl⟩,
      (-a) * t (nn i), ⟨t (nn i), Or.inr ⟨nn i, Or.inl rfl⟩, rfl⟩, ?_⟩
    rw [hx]; ring
  have hin := hBW ⟨hmem, hJa⟩ (kk j)
  have e2 : a * δ (kk j) * t (nn j) = δ (kk j) * (x j - x i) + δ (kk j) * x i := by rw [hx]; ring
  have := dint_add_le (δ (kk j) * (x j - x i)) (δ (kk j) * x i)
  rw [← e2] at this
  have := hbig j
  linarith

/-- Corollary 4.3, (a) ⇒ (b), conditional on Step 1: `γ` finer than the Bohr topology, `c_k - c_0` formed from characters of an
equicontinuous set `E`. -/
theorem inA_of_step1 (γ : TopologicalSpace ℝ) (hfine : γ ≤ bohrTop)
    (E : Set ℝ) (hV : ∀ ε : ℝ, 0 < ε → {x : ℝ | ∀ c ∈ E, dint (c * x) ≤ ε} ∈ @nhds ℝ γ 0)
    (c : ℕ → ℝ) (c0 : ℝ) (hc : ∀ k, c k ∈ E) (hlim : Tendsto c atTop (euclidNhds c0)) (t : ℕ → ℝ) (a : ℝ)
    (htr : ∀ W ∈ @nhds ℝ γ 0, ∃ B ∈ @nhds ℝ bohrTop 0,
      B ∩ (Icc (-1 : ℝ) 1 + (a • Tset t + (-a) • Tset t)) ⊆ W) :
    InA (fun k => c k - c0) t a := by
  set δ : ℕ → ℝ := fun k => c k - c0 with hδ
  refine inA_of_trace δ t (tendsto_sub_euclid c c0 hlim) a fun W hW => htr W ?_
  obtain ⟨B, hB, η, hη, hBW⟩ := (mem_nhds_gam δ W).1 hW
  have hB' : B ∈ @nhds ℝ γ 0 := nhds_mono hfine hB
  have hc0 : {x : ℝ | dint (c0 * x) < η / 3} ∈ @nhds ℝ γ 0 := nhds_mono hfine (dint_mem_nhds_bohr c0 (by linarith))
  refine Filter.mem_of_superset (Filter.inter_mem hB' (Filter.inter_mem hc0 (hV (η / 3) (by linarith)))) ?_
  rintro x ⟨hxB, hx0, hxE⟩
  refine hBW x hxB fun k => ?_
  have e1 : δ k * x = c k * x - c0 * x := by rw [hδ]; ring
  rw [e1]
  have h1 := hxE _ (hc k)
  have h2 : dint (c0 * x) < η / 3 := hx0
  have := dint_sub_le (c k * x) (c0 * x)
  linarith

/-! ## Countably many coefficients -/

/-- Lemma 4.4: the Bohr set of integers is syndetic. -/
theorem syndetic (F : Finset ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ L : ℕ, ∀ N : ℤ, ∃ p : ℤ, N ≤ p ∧ p ≤ N + L ∧ ∀ a ∈ F, dint (a * p) < η := by
  set ψ : ℤ → (F → AddCircle (1 : ℝ)) := fun p a => (((a : ℝ) * p : ℝ) : AddCircle (1 : ℝ)) with hψ
  have hψsub : ∀ p q, ψ p - ψ q = ψ (p - q) := by
    intro p q
    funext a
    show (((a : ℝ) * p : ℝ) : AddCircle (1 : ℝ)) - (((a : ℝ) * q : ℝ) : AddCircle (1 : ℝ)) =
      (((a : ℝ) * ((p - q : ℤ) : ℝ) : ℝ) : AddCircle (1 : ℝ))
    rw [← AddCircle.coe_sub]
    congr 1; push_cast; ring
  set U : Set (F → AddCircle (1 : ℝ)) := {z | ∀ a, ‖z a‖ < η} with hU
  have hUo : IsOpen U := by
    have h : U = ⋂ a, (fun z : F → AddCircle (1 : ℝ) => z a) ⁻¹' {w | ‖w‖ < η} := by ext z; simp [hU]
    rw [h]
    exact isOpen_iInter_of_finite fun a => (isOpen_lt continuous_norm continuous_const).preimage (continuous_apply a)
  have h0 : (0 : F → AddCircle (1 : ℝ)) ∈ U := fun a => by simpa using hη
  have hcov : closure (range ψ) ⊆ ⋃ p : ℤ, (fun z => z - ψ p) ⁻¹' U := by
    intro z hz
    have ho : IsOpen ((fun w => z - w) ⁻¹' U) := hUo.preimage (continuous_const.sub continuous_id)
    have hm : z ∈ (fun w => z - w) ⁻¹' U := by simpa using h0
    obtain ⟨w, h1, p, rfl⟩ := mem_closure_iff.1 hz _ ho hm
    exact mem_iUnion.2 ⟨p, h1⟩
  obtain ⟨P, hP⟩ := isClosed_closure.isCompact.elim_finite_subcover _
    (fun p => hUo.preimage (continuous_id.sub continuous_const)) hcov
  set M : ℕ := ∑ p ∈ P, p.natAbs with hM
  refine ⟨2 * M, fun N => ?_⟩
  have h := hP (subset_closure (mem_range_self (N + M)))
  simp only [mem_iUnion, exists_prop] at h
  obtain ⟨p, hp, h⟩ := h
  have hpM : p.natAbs ≤ M := Finset.single_le_sum (f := Int.natAbs) (fun _ _ => Nat.zero_le _) hp
  refine ⟨N + M - p, by omega, by push_cast; omega, fun a ha => ?_⟩
  have h2 : ψ (N + M) - ψ p ∈ U := h
  rw [hψsub] at h2
  exact h2 ⟨a, ha⟩

/-- Lemma 4.5: one small number that works for finitely many coefficients and all terms. -/
theorem small (t : ℕ → ℝ) (ht0 : ∀ n, t n ≠ 0) (htr : Tendsto (fun n => |t (n + 1) / t n|) atTop atTop)
    (F : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℝ, y ≠ 0 ∧ |y| ≤ ε ∧ ∀ n, ∀ a ∈ F, dint (a * y * t n) ≤ ε := by
  set ε' : ℝ := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'2 : ε' ≤ ε := min_le_left _ _
  set M : ℝ := 1 + ∑ a ∈ F, |a| with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∑ a ∈ F, |a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hMa : ∀ a ∈ F, |a| ≤ M := by
    intro a ha
    have := Finset.single_le_sum (f := fun b : ℝ => |b|) (fun _ _ => abs_nonneg _) ha
    linarith
  set η : ℝ := ε' / (2 * M) with hη
  have hη0 : 0 < η := by positivity
  have hηM : M * η = ε' / 2 := by rw [hη]; field_simp
  have hηε : η ≤ ε' / 2 := by
    have : 1 * η ≤ M * η := mul_le_mul_of_nonneg_right hM1 hη0.le
    linarith
  have haη : ∀ a ∈ F, |a| * η ≤ ε' / 2 := fun a ha =>
    (mul_le_mul_of_nonneg_right (hMa a ha) hη0.le).trans hηM.le
  obtain ⟨L, hL⟩ := syndetic F (show 0 < ε' / 2 by linarith)
  set R : ℝ := max 2 ((L + 1) / η + 1) with hR
  have hR2 : 2 ≤ R := le_max_left _ _
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (htr.eventually_ge_atTop R)
  have hratio : ∀ n, N1 ≤ n → R * |t n| ≤ |t (n + 1)| := by
    intro n hn
    have h1 := hN1 n hn
    rw [abs_div, le_div_iff₀ (abs_pos.2 (ht0 n))] at h1
    exact h1
  have hmono : ∀ n m, N1 ≤ n → n ≤ m → |t n| ≤ |t m| := by
    intro n m hn hnm
    induction m, hnm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hm ih =>
      have h1 := hratio m (hn.trans hm)
      have h2 : 1 * |t m| ≤ R * |t m| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      linarith
  have hgrow : ∀ j : ℕ, 2 ^ j * |t N1| ≤ |t (N1 + j)| := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := hratio (N1 + j) (by omega)
      have h2 : 2 * |t (N1 + j)| ≤ R * |t (N1 + j)| := mul_le_mul_of_nonneg_right hR2 (abs_nonneg _)
      rw [pow_succ, ← add_assoc]
      linarith
  set B0 : ℝ := 1 + ∑ n ∈ Finset.range (N1 + 1), |t n| with hB0
  have hB1 : 1 ≤ B0 := by
    have : 0 ≤ ∑ n ∈ Finset.range (N1 + 1), |t n| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B0 / |t N1|) (show (1 : ℝ) < 2 by norm_num)
  set n0 := N1 + j with hn0
  have hn0B : B0 ≤ |t n0| := by
    have h1 := hgrow j
    rw [div_lt_iff₀ (abs_pos.2 (ht0 N1))] at hj
    rw [hn0]; linarith
  have ht1 : 1 ≤ |t n0| := hB1.trans hn0B
  have hbelow : ∀ n, n ≤ n0 → |t n| ≤ |t n0| := by
    intro n hn
    by_cases h : n ≤ N1
    · have := Finset.single_le_sum (f := fun n => |t n|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (show n < N1 + 1 by omega))
      linarith
    · exact hmono n n0 (by omega) hn
  set q : ℕ → ℝ := fun j => t (n0 + j + 1) / t (n0 + j) with hq
  have hqR : ∀ j, R ≤ |q j| := fun j => hN1 (n0 + j) (by omega)
  have hh : ∀ j, (L : ℝ) + 1 ≤ η * (|q j| - 1) := by
    intro j
    have h1 : (L + 1) / η + 1 ≤ |q j| := (le_max_right _ _).trans (hqR j)
    have h2 : (L + 1) / η ≤ |q j| - 1 := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hη0.le
    have e1 : η * ((L + 1) / η) = L + 1 := by field_simp
    linarith
  have hstep : ∀ (j : ℕ) (z : ℤ), ∃ z' : ℤ, (∀ a ∈ F, dint (a * z') < ε' / 2) ∧
      |(z' : ℝ) - q j * z| ≤ η * (|q j| - 1) ∧ (z = 0 → 1 ≤ z') := by
    intro j z
    have hLr : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have h1 := hh j
    by_cases hz : z = 0
    · obtain ⟨p, hp1, hp2, hp3⟩ := hL 1
      refine ⟨p, hp3, ?_, fun _ => hp1⟩
      have hp1' : (1 : ℝ) ≤ p := by exact_mod_cast hp1
      have hp2' : (p : ℝ) ≤ 1 + L := by exact_mod_cast hp2
      rw [hz, Int.cast_zero, mul_zero, sub_zero, abs_of_nonneg (by linarith)]
      linarith
    · obtain ⟨p, hp1, hp2, hp3⟩ := hL ⌈q j * z - η * (|q j| - 1)⌉
      refine ⟨p, hp3, ?_, fun h => absurd h hz⟩
      have hc1 := Int.le_ceil (q j * z - η * (|q j| - 1))
      have hc2 := Int.ceil_lt_add_one (q j * z - η * (|q j| - 1))
      have hp1' : (⌈q j * z - η * (|q j| - 1)⌉ : ℝ) ≤ p := by exact_mod_cast hp1
      have hp2' : (p : ℝ) ≤ ⌈q j * z - η * (|q j| - 1)⌉ + L := by exact_mod_cast hp2
      rw [abs_le]; constructor <;> linarith
  choose f hfP hfq hf1 using hstep
  set p : ℕ → ℤ := fun j => Nat.rec 0 (fun i z => f i z) j with hpdef
  have hp0 : p 0 = 0 := rfl
  have hps : ∀ j, p (j + 1) = f j (p j) := fun j => rfl
  have hpP : ∀ j, ∀ a ∈ F, dint (a * p j) ≤ ε' / 2 := by
    intro j a ha
    cases j with
    | zero => rw [hp0, Int.cast_zero, mul_zero, dint_zero]; linarith
    | succ i => rw [hps]; exact (hfP i (p i) a ha).le
  set I : ℕ → Set ℝ := fun j => {y | |y * t (n0 + j) - p j| ≤ η} with hI
  have hIc : ∀ j, IsClosed (I j) := fun j =>
    isClosed_le (continuous_abs.comp ((continuous_id.mul continuous_const).sub continuous_const)) continuous_const
  have hIne : ∀ j, (I j).Nonempty := by
    intro j
    refine ⟨(p j : ℝ) / t (n0 + j), ?_⟩
    show |(p j : ℝ) / t (n0 + j) * t (n0 + j) - p j| ≤ η
    rw [div_mul_cancel₀ _ (ht0 _), sub_self, abs_zero]; exact hη0.le
  have hnest : ∀ j, I (j + 1) ⊆ I j := by
    intro j y hy
    have hy' : |y * t (n0 + j + 1) - p (j + 1)| ≤ η := hy
    have hqj : 0 < |q j| := lt_of_lt_of_le (by linarith) (hqR j)
    have hq0 : q j ≠ 0 := abs_pos.1 hqj
    have e1 : y * t (n0 + j + 1) = q j * (y * t (n0 + j)) := by
      rw [hq]; field_simp [ht0 (n0 + j)]
    have e2 : q j * (y * t (n0 + j) - p j) = (y * t (n0 + j + 1) - p (j + 1)) + ((p (j + 1) : ℝ) - q j * p j) := by
      rw [e1]; ring
    have h1 : |q j| * |y * t (n0 + j) - p j| ≤ η + η * (|q j| - 1) := by
      rw [← abs_mul, e2]
      refine (abs_add_le _ _).trans (add_le_add hy' ?_)
      rw [hps]; exact hfq j (p j)
    have h2 : |q j| * |y * t (n0 + j) - p j| ≤ |q j| * η := by linarith
    exact le_of_mul_le_mul_left h2 hqj
  have hI0 : IsCompact (I 0) := by
    refine Metric.isCompact_of_isClosed_isBounded (hIc 0) ((Metric.isBounded_closedBall (x := (0 : ℝ)) (r := η)).subset ?_)
    intro y hy
    have hy' : |y * t (n0 + 0) - p 0| ≤ η := hy
    rw [hp0, Int.cast_zero, sub_zero, add_zero, abs_mul] at hy'
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left ht1 (abs_nonneg y)
    linarith
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed I hnest hIne hI0 hIc
  have hyI : ∀ j, |y * t (n0 + j) - p j| ≤ η := fun j => mem_iInter.1 hy j
  have hy0 : |y * t n0| ≤ η := by
    have := hyI 0
    rwa [hp0, Int.cast_zero, sub_zero, add_zero] at this
  have hyabs : |y| ≤ η := by
    rw [abs_mul] at hy0
    have := mul_le_mul_of_nonneg_left ht1 (abs_nonneg y)
    linarith
  refine ⟨y, ?_, by linarith, fun n a ha => ?_⟩
  · intro h
    have h1 := hyI 1
    have h2 : (1 : ℤ) ≤ p 1 := show (1 : ℤ) ≤ f 0 (p 0) from hf1 0 (p 0) hp0
    have h3 : (1 : ℝ) ≤ p 1 := by exact_mod_cast h2
    rw [h, zero_mul, zero_sub, abs_neg, abs_of_nonneg (by linarith)] at h1
    linarith
  · by_cases hn : n0 ≤ n
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
      have e1 : a * y * t (n0 + i) = a * p i + a * (y * t (n0 + i) - p i) := by ring
      rw [e1]
      have h1 := hpP i a ha
      have h2 : dint (a * (y * t (n0 + i) - p i)) ≤ ε' / 2 := by
        refine (dint_le_abs _).trans ?_
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hyI i) (abs_nonneg _)).trans (haη a ha)
      have := dint_add_le (a * p i) (a * (y * t (n0 + i) - p i))
      linarith
    · have h1 : |y * t n| ≤ η := by
        have h2 := hbelow n (by omega)
        rw [abs_mul] at hy0 ⊢
        exact (mul_le_mul_of_nonneg_left h2 (abs_nonneg y)).trans hy0
      refine (dint_le_abs _).trans ?_
      rw [mul_assoc, abs_mul]
      have := (mul_le_mul_of_nonneg_left h1 (abs_nonneg a)).trans (haη a ha)
      linarith

/-- The sequence `δ` for a countable set of coefficients. -/
theorem exists_seq (t : ℕ → ℝ) (ht0 : ∀ n, t n ≠ 0) (htr : Tendsto (fun n => |t (n + 1) / t n|) atTop atTop)
    (Λ : Set ℝ) (hΛ : Λ.Countable) :
    ∃ δ : ℕ → ℝ, (∀ k, δ k ≠ 0) ∧ Tendsto δ atTop (𝓝 0) ∧ ∀ a ∈ Λ, InA δ t a := by
  obtain ⟨f, hf⟩ := (hΛ.insert 0).exists_eq_range (insert_nonempty 0 Λ)
  have h := fun k : ℕ => small t ht0 htr ((Finset.range (k + 1)).image f)
    (show (0 : ℝ) < 1 / (k + 1) by positivity)
  choose δ hδ0 hδb hδs using h
  have hlim : Tendsto δ atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.norm_eq_abs]; exact hδb k
  refine ⟨δ, hδ0, hlim, fun a ha ε hε => ?_⟩
  have ha' : a ∈ range f := hf ▸ mem_insert_of_mem 0 ha
  obtain ⟨i, rfl⟩ := ha'
  have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hε)
  filter_upwards [h1, eventually_ge_atTop i] with k hk hik
  intro n
  have h2 := hδs k n (f i) (Finset.mem_image_of_mem f (Finset.mem_range.2 (by omega)))
  exact h2.trans (le_of_lt hk)

/-- A sequence of nonzero numbers tending to `0` takes infinitely many values. -/
lemma infinite_range_of_tendsto (δ : ℕ → ℝ) (h0 : ∀ k, δ k ≠ 0) (hlim : Tendsto δ atTop (𝓝 0)) : (range δ).Infinite := by
  intro hfin
  have hc : IsClosed (range δ) := hfin.isClosed
  have hmem : (0 : ℝ) ∈ range δ := hc.mem_of_tendsto hlim (Eventually.of_forall fun k => mem_range_self k)
  obtain ⟨k, hk⟩ := hmem
  exact h0 k hk

/-- Theorem 4.6. -/
theorem countable_witness (t : ℕ → ℝ) (ht0 : ∀ n, t n ≠ 0) (htr : Tendsto (fun n => |t (n + 1) / t n|) atTop atTop)
    (Λ : Set ℝ) (hΛ : Λ.Countable) :
    ∃ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ ∧ LQC γ ∧ γ ≤ bohrTop ∧ γ ≠ bohrTop ∧
      (∀ x : ℝ, euclidNhds x ≤ @nhds ℝ γ x) ∧
      ∀ (m : ℝ) (l : List ℝ), (∀ a ∈ l, a ∈ Λ) → ∀ J : Set ℝ, J ⊆ Icc (-m) m + sumT t l →
        TopologicalSpace.induced (Subtype.val : J → ℝ) γ = TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop := by
  obtain ⟨δ, h0, hlim, hA⟩ := exists_seq t ht0 htr Λ hΛ
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, |δ k| ≤ M := by
    obtain ⟨M, hM⟩ := hlim.abs.bddAbove_range
    exact ⟨M, fun k => hM (mem_range_self k)⟩
  exact ⟨gamTop δ, gam_group δ, gam_lqc δ, gam_le_bohr δ,
    gam_ne_bohr δ (infinite_range_of_tendsto δ h0 hlim), gam_coarser_euclid δ M hM,
    fun m l hl J hJ => trace_eq δ t hlim m l (fun a ha => hA a (hl a ha)) J hJ⟩

end Two
end PVG
