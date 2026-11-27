import Mathlib
import LeanCheck.PVGTwoRest

/-!
# PVGtwo: the finest group topology that serves a set (Lean check)

For `δ_k → 0`, `θ : ℕ → ℝ/ℤ` and `x` with all `‖δ_k x‖` small put `Φ(x) = Σ_k round(δ_k x) θ_k` (a finite sum).

* `parity_serves` : `x → 0` iff `x → 0` for the Bohr topology, `sup_k ‖δ_k x‖ → 0` and `Φ(x) → 0` defines a group
  topology below the usual one, finer than `γ_δ`, in which every `aS`, `a ∈ A(δ)`, is totally bounded;
* `parity_strict` : for the sparse sequence and `θ_k = 1/2` it is strictly finer than `γ_δ`;
* `finest_lqc` : every locally quasi-convex group topology below the usual one in which these `aS` are totally bounded is
  coarser than `γ_δ`;
* `exists_finest` : every set that can be served has a finest topology that serves it;
* `finest_not_lqc` : for the sparse sequence this finest topology is not `γ_δ` and is not locally quasi-convex.

Order of topologies as in Mathlib: `γ₁ ≤ γ₂` means that `γ₁` is finer. Sequences are indexed from `0`.
A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set
open scoped Pointwise

namespace PVG
namespace Two
open Q95 Lac

lemma round_near (u : ℝ) (m : ℤ) (h : |u - m| < 1 / 2) : round u = m := by
  rw [round_eq, Int.floor_eq_iff]
  obtain ⟨h1, h2⟩ := abs_lt.1 h
  constructor <;> linarith

lemma dint_le_iff_round (u ε : ℝ) : dint u ≤ ε ↔ |u - round u| ≤ ε := by rw [dint_eq]

/-- `Φ(x) = Σ_k round(δ_k x) θ_k`. -/
noncomputable def Phit (δ : ℕ → ℝ) (θ : ℕ → AddCircle (1 : ℝ)) (x : ℝ) : AddCircle (1 : ℝ) :=
  ∑ᶠ k, round (δ k * x) • θ k

lemma round_eventually_zero (δ : ℕ → ℝ) (h0 : Tendsto δ atTop (𝓝 0)) (x : ℝ) :
    (Function.support fun k => round (δ k * x)).Finite := by
  have h : Tendsto (fun k => δ k * x) atTop (𝓝 0) := by
    simpa using h0.mul_const x
  have h1 : ∀ᶠ k in atTop, |δ k * x| < 1 / 2 := by
    refine (Metric.tendsto_nhds.1 h (1 / 2) (by norm_num)).mono fun k hk => ?_
    simpa [Real.dist_eq] using hk
  obtain ⟨K, hK⟩ := eventually_atTop.1 h1
  refine (finite_Iio K).subset fun k hk => ?_
  by_contra hc
  refine hk (round_near _ 0 ?_)
  simpa using hK k (not_lt.1 hc)

lemma Phit_support (δ : ℕ → ℝ) (h0 : Tendsto δ atTop (𝓝 0)) (θ : ℕ → AddCircle (1 : ℝ)) (x : ℝ) :
    (Function.support fun k => round (δ k * x) • θ k).Finite := by
  refine (round_eventually_zero δ h0 x).subset fun k hk hz => hk ?_
  show round (δ k * x) • θ k = 0
  rw [show round (δ k * x) = 0 from hz, zero_smul]

def Nset (δ : ℕ → ℝ) (θ : ℕ → AddCircle (1 : ℝ)) (ε η : ℝ) : Set ℝ :=
  {x | (∀ k, dint (δ k * x) ≤ ε) ∧ ‖Phit δ θ x‖ ≤ η}

lemma round_add_small (u v : ℝ) (hu : dint u ≤ 1 / 5) (hv : dint v ≤ 1 / 5) :
    round (u + v) = round u + round v := by
  refine round_near _ _ ?_
  rw [dint_eq] at hu hv
  have e1 : u + v - ((round u + round v : ℤ) : ℝ) = (u - round u) + (v - round v) := by push_cast; ring
  rw [e1]
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)

lemma round_neg_small (u : ℝ) (hu : dint u ≤ 1 / 5) : round (-u) = -round u := by
  refine round_near _ _ ?_
  rw [dint_eq] at hu
  have e1 : -u - ((-round u : ℤ) : ℝ) = -(u - round u) := by push_cast; ring
  rw [e1, abs_neg]
  linarith

lemma dint_neg' (u : ℝ) : dint (-u) = dint u := by
  unfold dint
  rw [AddCircle.coe_neg, norm_neg]

lemma exists_par (δ : ℕ → ℝ) (h0 : Tendsto δ atTop (𝓝 0)) (θ : ℕ → AddCircle (1 : ℝ)) :
    ∃ τ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ τ _ ∧
      (@nhds ℝ τ 0).HasBasis (fun p : ℝ × ℝ => 0 < p.1 ∧ p.1 ≤ 1 / 5 ∧ 0 < p.2) (fun p => Nset δ θ p.1 p.2) := by
  set P : ℝ × ℝ → Prop := fun p => 0 < p.1 ∧ p.1 ≤ 1 / 5 ∧ 0 < p.2 with hP
  set sets : Set (Set ℝ) := (fun p : ℝ × ℝ => Nset δ θ p.1 p.2) '' {p | P p} with hsets
  have hmem : ∀ p, P p → Nset δ θ p.1 p.2 ∈ sets := fun p hp => ⟨p, hp, rfl⟩
  have h00 : ∀ p, P p → (0 : ℝ) ∈ Nset δ θ p.1 p.2 := by
    intro p hp
    refine ⟨fun k => by rw [mul_zero, dint_zero]; exact hp.1.le, ?_⟩
    have : Phit δ θ 0 = 0 := by
      unfold Phit
      simp [mul_zero]
    rw [this, norm_zero]
    exact hp.2.2.le
  let B : AddGroupFilterBasis ℝ := addGroupFilterBasisOfComm sets ⟨_, hmem (1 / 5, 1) ⟨by norm_num, le_rfl, one_pos⟩⟩
    (by
      rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
      refine ⟨_, hmem (min p.1 q.1, min p.2 q.2) ⟨lt_min hp.1 hq.1, (min_le_left _ _).trans hp.2.1,
        lt_min hp.2.2 hq.2.2⟩, fun x hx => ⟨?_, ?_⟩⟩
      · exact ⟨fun k => (hx.1 k).trans (min_le_left _ _), hx.2.trans (min_le_left _ _)⟩
      · exact ⟨fun k => (hx.1 k).trans (min_le_right _ _), hx.2.trans (min_le_right _ _)⟩)
    (by
      rintro _ ⟨p, hp, rfl⟩
      exact h00 p hp)
    (by
      rintro _ ⟨p, hp, rfl⟩
      have hq : P (p.1 / 2, p.2 / 2) := ⟨half_pos hp.1, by have := hp.1; have := hp.2.1; simp only; linarith,
        half_pos hp.2.2⟩
      refine ⟨_, hmem _ hq, ?_⟩
      rintro _ ⟨x, hx, y, hy, rfl⟩
      have hx5 : ∀ k, dint (δ k * x) ≤ 1 / 5 := fun k => (hx.1 k).trans hq.2.1
      have hy5 : ∀ k, dint (δ k * y) ≤ 1 / 5 := fun k => (hy.1 k).trans hq.2.1
      refine ⟨fun k => ?_, ?_⟩
      · show dint (δ k * (x + y)) ≤ p.1
        rw [mul_add]
        have h1 := dint_add_le' (δ k * x) (δ k * y)
        have h2 : dint (δ k * x) ≤ p.1 / 2 := hx.1 k
        have h3 : dint (δ k * y) ≤ p.1 / 2 := hy.1 k
        linarith
      · have e1 : Phit δ θ (x + y) = Phit δ θ x + Phit δ θ y := by
          unfold Phit
          rw [← finsum_add_distrib (Phit_support δ h0 θ x) (Phit_support δ h0 θ y)]
          refine finsum_congr fun k => ?_
          rw [mul_add, round_add_small _ _ (hx5 k) (hy5 k), add_smul]
        show ‖Phit δ θ (x + y)‖ ≤ p.2
        rw [e1]
        have h2 : ‖Phit δ θ x‖ ≤ p.2 / 2 := hx.2
        have h3 : ‖Phit δ θ y‖ ≤ p.2 / 2 := hy.2
        exact (norm_add_le _ _).trans (by linarith))
    (by
      rintro _ ⟨p, hp, rfl⟩
      refine ⟨_, hmem p hp, fun x hx => ?_⟩
      have hx5 : ∀ k, dint (δ k * x) ≤ 1 / 5 := fun k => (hx.1 k).trans hp.2.1
      refine ⟨fun k => ?_, ?_⟩
      · show dint (δ k * -x) ≤ p.1
        rw [mul_neg, dint_neg']
        exact hx.1 k
      · have e1 : Phit δ θ (-x) = -Phit δ θ x := by
          unfold Phit
          rw [← finsum_neg_distrib]
          refine finsum_congr fun k => ?_
          rw [mul_neg, round_neg_small _ (hx5 k), neg_smul]
        show ‖Phit δ θ (-x)‖ ≤ p.2
        rw [e1, norm_neg]
        exact hx.2)
  refine ⟨B.topology, B.isTopologicalAddGroup, ?_⟩
  refine B.nhds_zero_hasBasis.to_hasBasis ?_ ?_
  · rintro s hs
    obtain ⟨p, hp, rfl⟩ := (show s ∈ sets from hs)
    exact ⟨p, hp, subset_rfl⟩
  · intro p hp
    exact ⟨_, hmem p hp, subset_rfl⟩

/-- The sets `aS` with `a ∈ A(δ)` are totally bounded for the topology of `exists_par`. -/
lemma par_tb (δ : ℕ → ℝ) (h0 : Tendsto δ atTop (𝓝 0)) (θ : ℕ → AddCircle (1 : ℝ)) (N : Filter ℝ)
    (hb : N.HasBasis (fun p : ℝ × ℝ => 0 < p.1 ∧ p.1 ≤ 1 / 5 ∧ 0 < p.2) (fun p => Nset δ θ p.1 p.2))
    (a : ℝ) (ha : InA δ sT a) : Tb N (dil a Sset) := by
  classical
  intro W hW
  obtain ⟨⟨ε, η⟩, ⟨hε, hε5, hη⟩, hsub⟩ := hb.mem_iff.1 hW
  simp only at hε hε5 hη hsub
  obtain ⟨K, hK⟩ := eventually_atTop.1 (ha (ε / 4) (by positivity))
  have htail : ∀ y ∈ dil a Sset, ∀ k, K ≤ k → dint (δ k * y) ≤ ε / 4 := by
    rintro y ⟨s, hs, rfl⟩ k hk
    rw [← Tset_sT] at hs
    rcases hs with rfl | ⟨n, rfl | rfl⟩
    · show dint (δ k * (a * 0)) ≤ ε / 4
      rw [mul_zero, mul_zero, dint_zero]; positivity
    · have e1 : δ k * (a * sT n) = a * δ k * sT n := by ring
      rw [e1]; exact hK k hk n
    · have e1 : δ k * (a * -sT n) = -(a * δ k * sT n) := by ring
      rw [e1, dint_neg']; exact hK k hk n
  set f : ℝ → (Fin K → ℝ) × AddCircle (1 : ℝ) :=
    fun y => (fun k => δ k * y - round (δ k * y), Phit δ θ y) with hf
  set r := min (ε / 8) (η / 2) with hr
  have hr0 : 0 < r := lt_min (by positivity) (by positivity)
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have htot : TotallyBounded (f '' dil a Sset) := by
    have hc : IsCompact ((Set.pi univ fun _ : Fin K => Icc (-(1 / 2) : ℝ) (1 / 2)) ×ˢ
        (univ : Set (AddCircle (1 : ℝ)))) := (isCompact_univ_pi fun _ => isCompact_Icc).prod isCompact_univ
    refine hc.totallyBounded.subset ?_
    rintro _ ⟨y, _, rfl⟩
    refine ⟨fun k _ => ?_, mem_univ _⟩
    exact abs_le.1 (abs_sub_round _)
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.1 htot r hr0
  let good : (Fin K → ℝ) × AddCircle (1 : ℝ) → Prop := fun c => ∃ y ∈ dil a Sset, f y ∈ Metric.ball c r
  let pick : (Fin K → ℝ) × AddCircle (1 : ℝ) → ℝ := fun c => if h : good c then h.choose else 0
  refine ⟨ht.toFinset.image pick, fun y hy => ?_⟩
  obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 (hcov ⟨y, hy, rfl⟩)
  have hg : good c := ⟨y, hy, hyc⟩
  have hp : pick c = hg.choose := dif_pos hg
  refine ⟨pick c, Finset.mem_image_of_mem _ (ht.mem_toFinset.2 hc), hsub ?_⟩
  rw [hp]
  obtain ⟨hy0, hy0c⟩ := hg.choose_spec
  set y0 := hg.choose with hy0def
  have hd : dist (f y) (f y0) ≤ r + r := by
    have h1 : dist (f y) c < r := Metric.mem_ball.1 hyc
    have h2 : dist (f y0) c < r := Metric.mem_ball.1 hy0c
    have := dist_triangle_right (f y) (f y0) c
    linarith
  rw [Prod.dist_eq] at hd
  have hd1 : dist (f y).1 (f y0).1 ≤ r + r := (le_max_left _ _).trans hd
  have hd2 : dist (f y).2 (f y0).2 ≤ r + r := (le_max_right _ _).trans hd
  have hr8 : r ≤ ε / 8 := min_le_left _ _
  have hr2 : r ≤ η / 2 := min_le_right _ _
  have hdiff : ∀ k, |(δ k * y - round (δ k * y)) - (δ k * y0 - round (δ k * y0))| ≤ ε / 2 := by
    intro k
    rcases lt_or_ge k K with hk | hk
    · have h1 := (dist_le_pi_dist (f y).1 (f y0).1 ⟨k, hk⟩).trans hd1
      rw [Real.dist_eq] at h1
      simp only [hf] at h1
      linarith
    · have h1 := htail y hy k hk
      have h2 := htail y0 hy0 k hk
      rw [dint_eq] at h1 h2
      exact (abs_sub _ _).trans (by linarith)
  have hsplit : ∀ k, δ k * (y - y0) =
      ((round (δ k * y) - round (δ k * y0) : ℤ) : ℝ) +
        ((δ k * y - round (δ k * y)) - (δ k * y0 - round (δ k * y0))) := by
    intro k; push_cast; ring
  have hround : ∀ k, round (δ k * (y - y0)) = round (δ k * y) - round (δ k * y0) := by
    intro k
    refine round_near _ _ ?_
    rw [hsplit k, add_sub_cancel_left]
    exact lt_of_le_of_lt (hdiff k) (by linarith)
  refine ⟨fun k => ?_, ?_⟩
  · show dint (δ k * (y - y0)) ≤ ε
    rw [dint_eq, hround k, hsplit k, add_sub_cancel_left]
    exact (hdiff k).trans (by linarith)
  · have e1 : Phit δ θ (y - y0) = Phit δ θ y - Phit δ θ y0 := by
      unfold Phit
      rw [← finsum_sub_distrib (Phit_support δ h0 θ y) (Phit_support δ h0 θ y0)]
      refine finsum_congr fun k => ?_
      rw [hround k, sub_smul]
    show ‖Phit δ θ (y - y0)‖ ≤ η
    rw [e1, ← dist_eq_norm]
    simp only [hf] at hd2
    linarith

/-- The topology given by the Bohr topology, `sup_k ‖δ_k x‖` and `Φ` serves `A(δ)` in all but possibly the strictness
conditions, and is finer than `γ_δ`. -/
theorem parity_serves (δ : ℕ → ℝ) (h0 : Tendsto δ atTop (𝓝 0)) (h1 : ∀ k, |δ k| ≤ 1) (θ : ℕ → AddCircle (1 : ℝ)) :
    ∃ γ : TopologicalSpace ℝ, @IsTopologicalAddGroup ℝ γ _ ∧ γ ≤ gamTop δ ∧ euclidNhds 0 ≤ @nhds ℝ γ 0 ∧
      (∀ a : ℝ, InA δ sT a → Tb (@nhds ℝ γ 0) (dil a Sset)) ∧
      ∀ ε η : ℝ, 0 < ε → ε ≤ 1 / 5 → 0 < η → Nset δ θ ε η ∈ @nhds ℝ γ 0 := by
  obtain ⟨τ, hτ, hb⟩ := exists_par δ h0 θ
  set γ := τ ⊓ bohrTop with hγ
  have e1 : @nhds ℝ γ 0 = @nhds ℝ τ 0 ⊓ @nhds ℝ bohrTop 0 := @nhds_inf ℝ τ bohrTop 0
  have hg : @IsTopologicalAddGroup ℝ γ _ := isTopologicalAddGroup_inf hτ bohr_group
  have hle : γ ≤ τ := inf_le_left
  have hNsets : ∀ ε η : ℝ, 0 < ε → ε ≤ 1 / 5 → 0 < η → Nset δ θ ε η ∈ @nhds ℝ γ 0 := by
    intro ε η hε hε5 hη
    exact nhds_mono hle (hb.mem_of_mem (i := (ε, η)) ⟨hε, hε5, hη⟩)
  refine ⟨γ, hg, ?_, ?_, ?_, hNsets⟩
  · refine le_of_nhds_zero _ _ hg (gam_group δ) fun W hW => ?_
    obtain ⟨B, hB, η, hη, hBW⟩ := (mem_nhds_gam δ W).1 hW
    have hε : 0 < min η (1 / 5 : ℝ) := lt_min hη (by norm_num)
    have h2 := hNsets _ 1 hε (min_le_right _ _) one_pos
    have h3 : B ∈ @nhds ℝ γ 0 := nhds_mono (inf_le_right : γ ≤ bohrTop) hB
    refine Filter.mem_of_superset (Filter.inter_mem h3 h2) fun x hx => ?_
    exact hBW x hx.1 fun k => (hx.2.1 k).trans (min_le_left _ _)
  · rw [e1]
    refine le_inf ?_ (nhds_mono continuous_e.le_induced)
    intro W hW
    obtain ⟨⟨ε, η⟩, ⟨hε, hε5, hη⟩, hsub⟩ := hb.mem_iff.1 hW
    simp only at hε hε5 hη hsub
    have hball : Metric.ball (0 : ℝ) ε ∈ euclidNhds 0 := Metric.ball_mem_nhds _ hε
    refine Filter.mem_of_superset hball fun x hx => hsub ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
    have hk : ∀ k, |δ k * x| < ε := by
      intro k
      rw [abs_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg x) (h1 k)) hx
    refine ⟨fun k => (dint_le_abs _).trans (hk k).le, ?_⟩
    have hz : Phit δ θ x = 0 := by
      unfold Phit
      have : (fun k => round (δ k * x) • θ k) = fun _ => 0 := by
        funext k
        have : round (δ k * x) = 0 := by
          refine round_near _ 0 ?_
          rw [Int.cast_zero, sub_zero]
          exact lt_of_lt_of_le (hk k) (hε5.trans (by norm_num))
        rw [this, zero_smul]
      rw [this, finsum_zero]
    show ‖Phit δ θ x‖ ≤ η
    rw [hz, norm_zero]
    exact hη.le
  · intro a ha
    refine tb_join τ bohrTop hτ bohr_group _ (par_tb δ h0 θ _ hb a ha) ?_
    intro W hW
    obtain ⟨F, hF⟩ := pre_bohr W hW
    exact ⟨F, fun y _ => hF y⟩

/-! ## Strictness for the sparse sequence -/

noncomputable def halfTheta : ℕ → AddCircle (1 : ℝ) := fun _ => ((1 / 2 : ℝ) : AddCircle (1 : ℝ))

lemma half_smul_even (n : ℤ) (h : Even n) : n • ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  obtain ⟨l, rfl⟩ := h
  rw [← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff]
  exact ⟨l, by simp; ring⟩

lemma half_smul_odd (n : ℤ) (h : Odd n) :
    n • ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨l, rfl⟩ := h
  rw [add_smul, one_smul, half_smul_even _ (even_two_mul l), zero_add]

/-- Points that are small for `γ_δ` and have an odd value. -/
lemma odd_points (F : Finset ℝ) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') :
    ∃ x : ℝ, x ∈ bset F η' ∧ (∀ k, dint (dlt2 k * x) ≤ η) ∧
      Phit dlt2 halfTheta x = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ((2 : ℝ) ^ m)⁻¹ * 2 ≤ min η (1 / 8) := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (x := min η (1 / 8) / 2) (by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
    rw [one_div, inv_pow] at hm
    exact ⟨m, by linarith⟩
  set N := 2 ^ m with hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hNr : (N : ℝ) = 2 ^ m := by rw [hN]; push_cast; rfl
  set u : ℕ → (F → AddCircle (1 : ℝ)) := fun i c => (((c : ℝ) * 2 ^ (Lv i - m) : ℝ) : AddCircle (1 : ℝ)) with hu
  obtain ⟨lim, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq u
  set ρ := η' / (4 * N) with hρ
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨M0, hM0⟩ := Metric.tendsto_atTop.1 hlim ρ hρ0
  set M := M0 + m + 1 with hMdef
  set i : ℕ → ℕ := fun j => φ (M + j) with hi
  have hinc : StrictMono i := fun a b hab => hφ (by omega)
  have hige : ∀ j, m + 1 ≤ i j := fun j =>
    le_trans (by omega) (show M + j ≤ φ (M + j) from hφ.id_le (M + j))
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      rw [h] at hm
      have := hm.trans (min_le_right _ _)
      norm_num at this
    · exact h
  have hmL : ∀ j, m ≤ Lv (i j) := by
    intro j
    have h1 := Lv_big (i j)
    have h2 := hige j
    omega
  have hclose : ∀ j (c : F), dist (u (i j) c) (lim c) < ρ := by
    intro j c
    exact lt_of_le_of_lt (dist_le_pi_dist _ _ c) (hM0 (M + j) (by omega))
  set x : ℝ := (∑ j ∈ Finset.range N, (2 : ℝ) ^ (Lv (i (j + 1)) - m)) - 2 ^ Lv (i 0) with hx
  have hLstrict : StrictMono Lv := fun a b hab => by
    have := Lv_gap hab
    omega
  -- integer and small parts of `δ_k x`
  set A : ℕ → ℕ → ℤ := fun k j => if Lv k + m ≤ Lv (i (j + 1)) then 2 ^ (Lv (i (j + 1)) - m - Lv k) else 0 with hA
  set As : ℕ → ℕ → ℝ := fun k j =>
    if Lv k + m ≤ Lv (i (j + 1)) then 0 else 2 ^ (Lv (i (j + 1)) - m) / 2 ^ Lv k with hAs
  set B : ℕ → ℤ := fun k => if Lv k ≤ Lv (i 0) then 2 ^ (Lv (i 0) - Lv k) else 0 with hB
  set Bs : ℕ → ℝ := fun k => if Lv k ≤ Lv (i 0) then 0 else 2 ^ Lv (i 0) / 2 ^ Lv k with hBs
  set n : ℕ → ℤ := fun k => (∑ j ∈ Finset.range N, A k j) - B k with hn
  set s : ℕ → ℝ := fun k => (∑ j ∈ Finset.range N, As k j) - Bs k with hs
  have hsplit : ∀ k, dlt2 k * x = (n k : ℝ) + s k := by
    intro k
    have hp : (0 : ℝ) < 2 ^ Lv k := by positivity
    have t1 : ∀ j, (2 : ℝ) ^ (Lv (i (j + 1)) - m) / 2 ^ Lv k = (A k j : ℝ) + As k j := by
      intro j
      simp only [hA, hAs]
      split_ifs with h
      · have e1 : Lv (i (j + 1)) - m = (Lv (i (j + 1)) - m - Lv k) + Lv k := by omega
        rw [add_zero]
        push_cast
        rw [div_eq_iff hp.ne', ← pow_add, ← e1]
      · simp
    have t2 : (2 : ℝ) ^ Lv (i 0) / 2 ^ Lv k = (B k : ℝ) + Bs k := by
      simp only [hB, hBs]
      split_ifs with h
      · have e1 : Lv (i 0) = (Lv (i 0) - Lv k) + Lv k := by omega
        rw [add_zero]
        push_cast
        rw [div_eq_iff hp.ne', ← pow_add, ← e1]
      · simp
    have e0 : dlt2 k * x = (∑ j ∈ Finset.range N, (2 : ℝ) ^ (Lv (i (j + 1)) - m) / 2 ^ Lv k) -
        2 ^ Lv (i 0) / 2 ^ Lv k := by
      unfold dlt2
      rw [hx, inv_mul_eq_div, sub_div, Finset.sum_div]
    rw [e0, t2, Finset.sum_congr rfl fun j _ => t1 j, Finset.sum_add_distrib]
    simp only [hn, hs]
    push_cast
    ring
  -- the small part is small
  have hsmall : ∀ k, |s k| ≤ ((2 : ℝ) ^ m)⁻¹ * 2 := by
    intro k
    have hAs0 : ∀ j, 0 ≤ As k j := by
      intro j; simp only [hAs]; split_ifs
      · exact le_rfl
      · positivity
    have hBs0 : 0 ≤ Bs k := by
      simp only [hBs]; split_ifs
      · exact le_rfl
      · positivity
    have hlt : ∀ a : ℕ, i a < k → (2 : ℝ) ^ Lv (i a) / 2 ^ Lv k ≤ ((2 : ℝ) ^ (k + 20))⁻¹ := by
      intro a ha
      have h1 := Lv_gap ha
      rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ one_le_two (by omega)
    have hbig : ∀ j, k < i j → Lv k + m ≤ Lv (i j) := by
      intro j hj
      have h1 := Lv_gap hj
      have h2 := hige j
      omega
    -- bound for the terms
    have hterm : ∀ j ∈ Finset.range N, As k j ≤
        (if i (j + 1) = k then ((2 : ℝ) ^ m)⁻¹ else 0) + ((2 : ℝ) ^ m)⁻¹ * ((2 : ℝ) ^ (k + 20))⁻¹ := by
      intro j _
      have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ m)⁻¹ * ((2 : ℝ) ^ (k + 20))⁻¹ := by positivity
      simp only [hAs]
      split_ifs with h h' h'
      · exfalso
        rw [h'] at h
        have := hige (j + 1)
        omega
      · simpa using h0
      · have e1 : (2 : ℝ) ^ (Lv (i (j + 1)) - m) / 2 ^ Lv k = ((2 : ℝ) ^ m)⁻¹ := by
          rw [h', pow_sub₀ _ two_ne_zero (by rw [← h']; exact hmL _)]
          field_simp
        rw [e1]
        exact le_add_of_nonneg_right h0
      · have hlt' : i (j + 1) < k := by
          rcases lt_trichotomy (i (j + 1)) k with hh | hh | hh
          · exact hh
          · exact absurd hh h'
          · exact absurd (hbig _ hh) h
        have e1 : (2 : ℝ) ^ (Lv (i (j + 1)) - m) / 2 ^ Lv k =
            ((2 : ℝ) ^ m)⁻¹ * (2 ^ Lv (i (j + 1)) / 2 ^ Lv k) := by
          rw [pow_sub₀ _ two_ne_zero (hmL _)]
          ring
        rw [e1, zero_add]
        exact mul_le_mul_of_nonneg_left (hlt _ hlt') (by positivity)
    by_cases hk : k ≤ i 0
    · -- all terms are integers
      have h1 : ∀ j ∈ Finset.range N, As k j = 0 := by
        intro j _
        have h2 : k < i (j + 1) := lt_of_le_of_lt hk (hinc (Nat.succ_pos j))
        simp only [hAs, if_pos (hbig _ h2)]
      have h3 : Bs k = 0 := by
        simp only [hBs, if_pos (hLstrict.monotone hk)]
      simp only [hs]
      rw [Finset.sum_eq_zero h1, h3, sub_zero, abs_zero]
      positivity
    · have hk' : i 0 < k := not_le.1 hk
      have hkm : m ≤ k + 20 := by
        have := hige 0
        omega
      have hsum : ∑ j ∈ Finset.range N, As k j ≤ ((2 : ℝ) ^ m)⁻¹ + ((2 : ℝ) ^ (k + 20))⁻¹ := by
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hNr,
          mul_inv_cancel_left₀ (by positivity : (2 : ℝ) ^ m ≠ 0)]
        refine add_le_add ?_ le_rfl
        have h1 : ((Finset.range N).filter fun j => i (j + 1) = k).card ≤ 1 := by
          refine Finset.card_le_one.2 fun a ha b hb => ?_
          have h2 := (Finset.mem_filter.1 ha).2
          have h3 := (Finset.mem_filter.1 hb).2
          have := hinc.injective (h2.trans h3.symm)
          omega
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast h1)
      have hBsle : Bs k ≤ ((2 : ℝ) ^ (k + 20))⁻¹ := by
        simp only [hBs]
        split_ifs
        · positivity
        · exact hlt 0 hk'
      have hkk : ((2 : ℝ) ^ (k + 20))⁻¹ ≤ ((2 : ℝ) ^ m)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two hkm)
      have h0 : 0 ≤ ∑ j ∈ Finset.range N, As k j := Finset.sum_nonneg fun j _ => hAs0 j
      simp only [hs]
      rw [abs_le]
      constructor <;> linarith
  have hs8 : ∀ k, |s k| ≤ 1 / 8 := fun k => (hsmall k).trans (hm.trans (min_le_right _ _))
  have hround : ∀ k, round (dlt2 k * x) = n k := by
    intro k
    refine round_near _ _ ?_
    rw [hsplit k, add_sub_cancel_left]
    exact lt_of_le_of_lt (hs8 k) (by norm_num)
  -- parity
  have hAeven : ∀ k j, Even (A k j) := by
    intro k j
    simp only [hA]
    split_ifs with h
    · refine (even_two).pow_of_ne_zero ?_
      have hne : i (j + 1) ≠ k := by
        intro h'
        rw [h'] at h
        have := hige (j + 1)
        omega
      have hlt : k < i (j + 1) := by
        rcases lt_trichotomy k (i (j + 1)) with hh | hh | hh
        · exact hh
        · exact absurd hh.symm hne
        · have := hLstrict hh
          omega
      have h1 := Lv_gap hlt
      have h2 := hige (j + 1)
      omega
    · exact Even.zero
  have hsumeven : ∀ k, Even (∑ j ∈ Finset.range N, A k j) := fun k =>
    Finset.even_sum _ fun j _ => hAeven k j
  have hneven : ∀ k, k ≠ i 0 → Even (n k) := by
    intro k hk
    refine (hsumeven k).sub ?_
    simp only [hB]
    split_ifs with h
    · refine (even_two).pow_of_ne_zero ?_
      have : Lv k ≠ Lv (i 0) := fun h' => hk (hLstrict.injective h')
      omega
    · exact Even.zero
  have hnodd : Odd (n (i 0)) := by
    refine (hsumeven (i 0)).sub_odd ?_
    simp only [hB, if_pos le_rfl, Nat.sub_self, pow_zero]
    exact odd_one
  refine ⟨x, ?_, ?_, ?_⟩
  · -- Bohr
    intro c hc
    set c' : F := ⟨c, hc⟩ with hc'
    have e1 : ((c * x : ℝ) : AddCircle (1 : ℝ)) = ∑ j ∈ Finset.range N, (u (i (j + 1)) c' - u (i 0) c') := by
      have e2 : c * x = (∑ j ∈ Finset.range N, c * 2 ^ (Lv (i (j + 1)) - m)) - N • (c * 2 ^ (Lv (i 0) - m)) := by
        rw [hx, mul_sub, Finset.mul_sum, nsmul_eq_mul, hNr]
        congr 1
        have e3 : (2 : ℝ) ^ Lv (i 0) = 2 ^ m * 2 ^ (Lv (i 0) - m) := by
          rw [← pow_add]; congr 1; have := hmL 0; omega
        rw [e3]; ring
      rw [e2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      rw [AddCircle.coe_sub, AddCircle.coe_nsmul]
      congr 1
      exact map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _
    show ‖((c * x : ℝ) : AddCircle (1 : ℝ))‖ < η'
    rw [e1]
    have h1 : ∀ j ∈ Finset.range N, ‖u (i (j + 1)) c' - u (i 0) c'‖ ≤ ρ + ρ := by
      intro j _
      rw [← dist_eq_norm]
      have h2 := hclose (j + 1) c'
      have h3 := hclose 0 c'
      have := dist_triangle_right (u (i (j + 1)) c') (u (i 0) c') (lim c')
      linarith
    refine lt_of_le_of_lt ((norm_sum_le _ _).trans (Finset.sum_le_sum h1)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e4 : (N : ℝ) * (ρ + ρ) = η' / 2 := by
      rw [hρ]; field_simp; ring
    rw [e4]
    exact half_lt_self hη'
  · intro k
    rw [hsplit k, add_comm, show s k + (n k : ℝ) = s k - ((-n k : ℤ) : ℝ) by push_cast; ring, dint_sub_int]
    exact (dint_le_abs _).trans ((hsmall k).trans (hm.trans (min_le_left _ _)))
  · unfold Phit halfTheta
    rw [finsum_eq_single _ (i 0) fun k hk => by rw [hround k]; exact half_smul_even _ (hneven k hk)]
    rw [hround]
    exact half_smul_odd _ hnodd

theorem parity_strict (γ : TopologicalSpace ℝ)
    (hN : ∀ ε η : ℝ, 0 < ε → ε ≤ 1 / 5 → 0 < η → Nset dlt2 halfTheta ε η ∈ @nhds ℝ γ 0) : ¬ gamTop dlt2 ≤ γ := by
  intro h
  have h1 : Nset dlt2 halfTheta (1 / 8) (1 / 8) ∈ @nhds ℝ (gamTop dlt2) 0 :=
    nhds_mono h (hN _ _ (by norm_num) (by norm_num) (by norm_num))
  obtain ⟨B, hB, η, hη, hBW⟩ := (mem_nhds_gam dlt2 _).1 h1
  obtain ⟨F, η', hη', hF⟩ := exists_bset_subset hB
  obtain ⟨x, hxF, hxd, hxP⟩ := odd_points F hη hη'
  have h2 := (hBW x (hF hxF) hxd).2
  rw [hxP] at h2
  have h3 : ‖((1 / 2 : ℝ) : AddCircle (1 : ℝ))‖ = 1 / 2 := dint_half
  rw [h3] at h2
  norm_num at h2

/-! ## The finest topologies -/

/-- Among locally quasi-convex group topologies `γ_δ` is the finest. -/
theorem finest_lqc (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (hq : LQC γ)
    (htb : ∀ a : ℝ, InA dlt2 sT a → Tb (@nhds ℝ γ 0) (dil a Sset)) : gamTop dlt2 ≤ γ := by
  classical
  refine le_of_nhds_zero _ _ (gam_group _) hg fun W hW => ?_
  obtain ⟨S, hS, hU, hUW⟩ := hq W hW
  set E := {c : ℝ | ∃ χ ∈ S, ∀ x : ℝ, χ x = ((c * x : ℝ) : AddCircle (1 : ℝ))} with hE
  have hchar : ∀ χ ∈ S, ∃ c ∈ E, ∀ x : ℝ, χ x = ((c * x : ℝ) : AddCircle (1 : ℝ)) := by
    intro χ hχ
    have h0 : Tendsto χ (euclidNhds 0) (@nhds (AddCircle (1 : ℝ)) circleTop 0) := by
      have h := (@Continuous.tendsto ℝ (AddCircle (1 : ℝ)) γ circleTop _ (hS χ hχ) 0).mono_left heu
      rwa [map_zero] at h
    obtain ⟨c, hc⟩ := char_of_tendsto χ h0
    exact ⟨c, ⟨χ, hχ, hc⟩, hc⟩
  have hmem : ∀ x : ℝ, (∀ χ ∈ S, ‖χ x‖ ≤ 1 / 4) → ∀ c ∈ E, dint (c * x) ≤ 1 / 4 := by
    rintro x hx c ⟨χ, hχ, hc⟩
    have := hx χ hχ
    rw [hc x] at this
    exact this
  obtain ⟨η, hη, hb⟩ := ball_of_euclid (heu hU)
  have hbd : E ⊆ Icc (-(1 / η)) (1 / η) := by
    intro c hc
    rw [mem_Icc, ← abs_le]
    by_contra h
    push Not at h
    have hc0 : c ≠ 0 := by
      intro h1
      rw [h1, abs_zero] at h
      exact absurd h (not_lt.2 (by positivity))
    have hx : |(2 * c)⁻¹| < η := by
      rw [abs_inv, abs_mul, abs_two, inv_lt_iff_one_lt_mul₀ (by positivity)]
      rw [div_lt_iff₀ hη] at h
      nlinarith [abs_nonneg c]
    have h2 := hmem _ (hb _ hx) c hc
    have e1 : c * (2 * c)⁻¹ = 1 / 2 := by field_simp
    rw [e1, dint_half] at h2
    norm_num at h2
  set V0 := {x : ℝ | ∀ c ∈ E, dint (c * x) ≤ 1 / 32} with hV0
  have hV0mem : V0 ∈ @nhds ℝ γ 0 := by
    refine Filter.mem_of_superset (nsmul_nhds γ hg _ hU 8) fun x hx c hc => ?_
    have h1 : ∀ k : ℕ, 1 ≤ k → k ≤ 8 → dint (k * (c * x)) ≤ 1 / 4 := by
      intro k _ hk
      have h2 := hmem _ (hx k (Finset.mem_range.2 (Nat.lt_succ_of_le hk))) c hc
      rwa [mul_left_comm] at h2
    have h3 := dint_le_of_multiples 8 (by norm_num) (c * x) h1
    exact h3.trans (by norm_num)
  obtain ⟨ε, hε, F, hF⟩ := rigidity (@nhds ℝ γ 0) (group_half γ hg) heu htb V0 hV0mem
  set Mf := (∑ f ∈ F, |f|) + 1 with hMf
  have hMf0 : 0 < Mf := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => abs_nonneg _) one_pos
  have htot : TotallyBounded E := (isCompact_Icc.totallyBounded).subset hbd
  set r := (1 / 32) / Mf with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨t, htE, htfin, hcov⟩ := Metric.finite_approx_of_totallyBounded htot r hr0
  refine (mem_nhds_gam dlt2 W).2 ⟨bset htfin.toFinset (1 / 32), bset_mem _ (by norm_num), ε, hε, fun x hxB hxd => ?_⟩
  refine hUW fun χ hχ => ?_
  obtain ⟨c, hcE, hc⟩ := hchar χ hχ
  rw [hc x]
  obtain ⟨c', hc't, hcc'⟩ := mem_iUnion₂.1 (hcov hcE)
  have hdist : |c - c'| < r := by simpa [Metric.mem_ball, Real.dist_eq] using hcc'
  obtain ⟨f, hfF, hfV⟩ := hF x fun k => by
    have e1 : x / 2 ^ Lv k = dlt2 k * x := by
      unfold dlt2; rw [inv_mul_eq_div]
    rw [e1]; exact hxd k
  have hfM : |f| ≤ Mf := by
    have h1 := Finset.single_le_sum (f := fun g : ℝ => |g|) (fun _ _ => abs_nonneg _) hfF
    simp only [hMf]
    linarith
  have t1 : dint (c' * x) ≤ 1 / 32 := (hxB c' (htfin.mem_toFinset.2 hc't)).le
  have t2 : dint ((c - c') * f) ≤ 1 / 32 := by
    refine (dint_le_abs _).trans ?_
    rw [abs_mul]
    have h1 : |c - c'| * |f| ≤ r * Mf := mul_le_mul hdist.le hfM (abs_nonneg _) hr0.le
    have e1 : r * Mf = 1 / 32 := by rw [hr]; exact div_mul_cancel₀ _ hMf0.ne'
    linarith
  have t3 : dint (c * (x - f)) ≤ 1 / 32 := hfV c hcE
  have t4 : dint (c' * (x - f)) ≤ 1 / 32 := hfV c' (htE hc't)
  have e1 : c * x = c' * x + (c - c') * f + (c * (x - f) - c' * (x - f)) := by ring
  show dint (c * x) ≤ 1 / 4
  rw [e1]
  have a1 := dint_add_le' (c' * x + (c - c') * f) (c * (x - f) - c' * (x - f))
  have a2 := dint_add_le' (c' * x) ((c - c') * f)
  have a3 := dint_sub_le (c * (x - f)) (c' * (x - f))
  linarith

lemma serves_inf (t1 t2 : TopologicalSpace ℝ) (A : Set ℝ) (h1 : Serves t1 A) (h2 : Serves t2 A) :
    Serves (t1 ⊓ t2) A := by
  have e1 : @nhds ℝ (t1 ⊓ t2) 0 = @nhds ℝ t1 0 ⊓ @nhds ℝ t2 0 := @nhds_inf ℝ t1 t2 0
  refine ⟨isTopologicalAddGroup_inf h1.1 h2.1, inf_le_left.trans h1.2.1, ?_, ?_, fun a ha => ?_⟩
  · intro h
    exact h1.2.2.1 (le_antisymm h1.2.1 (h ▸ inf_le_left))
  · rw [e1]
    exact le_inf h1.2.2.2.1 h2.2.2.2.1
  · exact tb_join t1 t2 h1.1 h2.1 _ (h1.2.2.2.2 a ha) (h2.2.2.2.2 a ha)

/-- Every set that can be served has a finest topology that serves it. -/
theorem exists_finest (A : Set ℝ) (h : Servable A) :
    ∃ γ : TopologicalSpace ℝ, Serves γ A ∧ ∀ γ' : TopologicalSpace ℝ, Serves γ' A → γ ≤ γ' := by
  obtain ⟨γ0, h0⟩ := h
  set T : Set (TopologicalSpace ℝ) := {t | Serves t A} with hT
  refine ⟨sInf T, ?_, fun γ' h' => sInf_le h'⟩
  have hn : @nhds ℝ (sInf T) 0 = ⨅ t ∈ T, @nhds ℝ t 0 := nhds_sInf
  have hle : sInf T ≤ γ0 := sInf_le h0
  refine ⟨isTopologicalAddGroup_sInf fun t ht => ht.1, hle.trans h0.2.1, ?_, ?_, ?_⟩
  · intro h
    exact h0.2.2.1 (le_antisymm h0.2.1 (h ▸ hle))
  · rw [hn]
    exact le_iInf₂ fun t ht => ht.2.2.2.1
  · intro a ha W hW
    rw [hn] at hW
    have hdir : DirectedOn ((fun t : TopologicalSpace ℝ => @nhds ℝ t 0) ⁻¹'o (· ≥ ·)) T := by
      intro t1 h1 t2 h2
      exact ⟨t1 ⊓ t2, serves_inf t1 t2 A h1 h2, nhds_mono inf_le_left, nhds_mono inf_le_right⟩
    obtain ⟨t, ht, hWt⟩ := (Filter.mem_biInf_of_directed hdir ⟨γ0, h0⟩).1 hW
    exact ht.2.2.2.2 a ha W hWt

/-- For the sparse sequence the finest topology that serves `A(δ)` is strictly finer than `γ_δ` and is not locally
quasi-convex. -/
theorem finest_not_lqc : ∃ γ : TopologicalSpace ℝ, Serves γ A2 ∧ (∀ γ' : TopologicalSpace ℝ, Serves γ' A2 → γ ≤ γ') ∧
    γ ≤ gamTop dlt2 ∧ γ ≠ gamTop dlt2 ∧ ¬ LQC γ := by
  obtain ⟨γ, hγ, hfin⟩ := exists_finest A2 ⟨_, serves_dlt2⟩
  have hle : γ ≤ gamTop dlt2 := hfin _ serves_dlt2
  obtain ⟨γp, hg, hgam, heu, htb, hN⟩ := parity_serves dlt2 dlt2_tendsto dlt2_le_one halfTheta
  have hsp : Serves γp A2 := by
    refine ⟨hg, hgam.trans (gam_le_bohr _), ?_, heu, htb⟩
    intro h
    have h1 : bohrTop ≤ gamTop dlt2 := h ▸ hgam
    exact serves_dlt2.2.2.1 (le_antisymm (gam_le_bohr _) h1)
  have hne : γ ≠ gamTop dlt2 := by
    intro h
    exact parity_strict γp hN (h ▸ hfin _ hsp)
  refine ⟨γ, hγ, hfin, hle, hne, fun hq => ?_⟩
  exact hne (le_antisymm hle (finest_lqc γ hγ.1 hγ.2.2.2.1 hq hγ.2.2.2.2))

end Two
end PVG
