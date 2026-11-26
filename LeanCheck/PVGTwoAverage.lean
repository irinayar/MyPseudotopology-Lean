import Mathlib
import LeanCheck.PVGTwoDimension

/-!
# PVGtwo, Section 6: locally quasi-convex topologies do not suffice (Lean check)

Scope. `avTop` is the Bohr topology of `ℝ` together with the pseudonorm `avSup x = sup_N Φ_N(x)`, where
`Φ_N(x) = N⁻¹ ∑_{p=1}^{N} ‖x / 2^p‖` and `‖u‖` is the distance from `u` to the nearest integer. In Mathlib's order `t₁ ≤ t₂` means
that `t₁` is finer. `InL a` says `a ∈ Λ`, that is, `sup_n Φ_N(a s_n) → 0` as `N → ∞`. The sequence `sT` is indexed from `0`.

* `av_group`, `av_le_bohr`, `av_coarser_euclid`, `av_not_precompact`, `av_ne_bohr` : the properties of the topology;
* `av_trace` : the topology and the Bohr topology agree on every subset of `[-m,m] + a_1 S + ⋯ + a_r S`, `a_i ∈ Λ`;
* `inL_add`, `inL_neg`, `inL_zero` : `Λ` is a group;
* `inL_of_digits` : a number whose binary digits have uniform density zero belongs to `Λ`;
* `exists_not_inA` : for every sequence `δ_k ≠ 0`, `δ_k → 0`, some `a ∈ Λ` is not in `A(δ)`;
* `av_no_step1_witness` : the consequence for locally quasi-convex topologies, **conditional on Step 1** of the proof of
  Proposition 16.1 of PVG_v57 (hypotheses `hV`, `hc`), which is not proved in Lean.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Set
open scoped Pointwise

namespace PVG
namespace Two
open Q95 Lac

/-! ## The averages -/

/-- `Φ_N(x)`. -/
noncomputable def avPhi (N : ℕ) (x : ℝ) : ℝ := (∑ p ∈ Finset.range N, dint (x / 2 ^ (p + 1))) / N

lemma avPhi_nonneg (N : ℕ) (x : ℝ) : 0 ≤ avPhi N x :=
  div_nonneg (Finset.sum_nonneg fun _ _ => dint_nonneg _) (Nat.cast_nonneg _)

lemma avPhi_zero (N : ℕ) : avPhi N 0 = 0 := by simp [avPhi, dint_zero]

lemma avPhi_neg (N : ℕ) (x : ℝ) : avPhi N (-x) = avPhi N x := by
  unfold avPhi
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [neg_div, dint_neg]

lemma avPhi_add_le (N : ℕ) (x y : ℝ) : avPhi N (x + y) ≤ avPhi N x + avPhi N y := by
  unfold avPhi
  rw [← add_div, ← Finset.sum_add_distrib]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun p _ => ?_) (Nat.cast_nonneg _)
  rw [add_div]
  exact dint_add_le _ _

lemma avPhi_sub_le (N : ℕ) (x y : ℝ) : avPhi N (x - y) ≤ avPhi N x + avPhi N y := by
  have h := avPhi_add_le N x (-y)
  rwa [← sub_eq_add_neg, avPhi_neg] at h

lemma avPhi_le_half (N : ℕ) (x : ℝ) : avPhi N x ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [avPhi, h]
  unfold avPhi
  rw [div_le_iff₀ (by exact_mod_cast h)]
  refine (Finset.sum_le_sum fun p _ => dint_le_half _).trans (le_of_eq ?_)
  simp [mul_comm]

lemma sum_half_le (N : ℕ) : ∑ p ∈ Finset.range N, ((2 : ℝ) ^ (p + 1))⁻¹ ≤ 1 := by
  have h : ∀ M : ℕ, ∑ p ∈ Finset.range M, ((2 : ℝ) ^ (p + 1))⁻¹ = 1 - ((2 : ℝ) ^ M)⁻¹ := by
    intro M
    induction M with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      field_simp
      ring
  rw [h]
  have : (0 : ℝ) < ((2 : ℝ) ^ N)⁻¹ := by positivity
  linarith

lemma sum_dint_le_abs (N : ℕ) (x : ℝ) : ∑ p ∈ Finset.range N, dint (x / 2 ^ (p + 1)) ≤ |x| := by
  have h1 : ∑ p ∈ Finset.range N, dint (x / 2 ^ (p + 1)) ≤ ∑ p ∈ Finset.range N, |x| * ((2 : ℝ) ^ (p + 1))⁻¹ := by
    refine Finset.sum_le_sum fun p _ => (dint_le_abs _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (p + 1)), div_eq_mul_inv]
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_of_le_one_right (abs_nonneg _) (sum_half_le N)

lemma avPhi_le_abs_div (N : ℕ) (x : ℝ) : avPhi N x ≤ |x| / N :=
  div_le_div_of_nonneg_right (sum_dint_le_abs N x) (Nat.cast_nonneg _)

lemma avPhi_le_abs (N : ℕ) (x : ℝ) : avPhi N x ≤ |x| := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [avPhi, h]
  exact (avPhi_le_abs_div N x).trans (div_le_self (abs_nonneg _) (by exact_mod_cast h))

/-- `Φ(x) = sup_N Φ_N(x)`. -/
noncomputable def avSup (x : ℝ) : ℝ := ⨆ N, avPhi N x

lemma av_bdd (x : ℝ) : BddAbove (range fun N => avPhi N x) :=
  ⟨1 / 2, by rintro _ ⟨N, rfl⟩; exact avPhi_le_half N x⟩

lemma le_avSup (N : ℕ) (x : ℝ) : avPhi N x ≤ avSup x := le_ciSup (av_bdd x) N

lemma avSup_le (x c : ℝ) (h : ∀ N, avPhi N x ≤ c) : avSup x ≤ c := ciSup_le h

noncomputable def avSN : AddGroupSeminorm ℝ where
  toFun := avSup
  map_zero' := le_antisymm (avSup_le _ _ fun N => by rw [avPhi_zero]) ((avPhi_nonneg 0 0).trans (le_avSup 0 0))
  add_le' x y := avSup_le _ _ fun N => (avPhi_add_le N x y).trans (add_le_add (le_avSup N x) (le_avSup N y))
  neg' x := by
    unfold avSup
    simp_rw [avPhi_neg]

lemma avSup_neg (x : ℝ) : avSup (-x) = avSup x := map_neg_eq_map avSN x

lemma avSup_sub_le (x y : ℝ) : avSup (x - y) ≤ avSup x + avSup y := by
  have h : avSup (x + -y) ≤ avSup x + avSup (-y) := map_add_le_add avSN x (-y)
  rwa [← sub_eq_add_neg, avSup_neg] at h

/-! ## The topology -/

set_option warn.classDefReducibility false in
/-- The topology of the pseudonorm alone. -/
noncomputable def avNormTop : TopologicalSpace ℝ :=
  avSN.toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

set_option warn.classDefReducibility false in
/-- The topology `γ` of the article: the Bohr topology together with the pseudonorm. -/
noncomputable def avTop : TopologicalSpace ℝ := bohrTop ⊓ avNormTop

lemma avNormTop_group : @IsTopologicalAddGroup ℝ avNormTop _ := by
  have h : ∀ (E : Type) [SeminormedAddCommGroup E], IsTopologicalAddGroup E := fun E _ => inferInstance
  exact @h ℝ avSN.toSeminormedAddCommGroup

theorem av_group : @IsTopologicalAddGroup ℝ avTop _ :=
  topologicalAddGroup_inf bohr_isTopologicalAddGroup avNormTop_group

theorem av_le_bohr : avTop ≤ bohrTop := inf_le_left

lemma mem_nhds_avNorm (C : Set ℝ) :
    C ∈ @nhds ℝ avNormTop 0 ↔ ∃ η : ℝ, 0 < η ∧ ∀ x : ℝ, (∀ N, avPhi N x ≤ η) → x ∈ C := by
  have hb := @Metric.nhds_basis_closedBall ℝ avSN.toSeminormedAddCommGroup.toPseudoMetricSpace (0 : ℝ)
  have hd : ∀ x : ℝ, @dist ℝ avSN.toSeminormedAddCommGroup.toPseudoMetricSpace.toDist x 0 = avSup x := by
    intro x
    letI := avSN.toSeminormedAddCommGroup
    rw [dist_zero_right]
    rfl
  refine hb.mem_iff.trans ⟨?_, ?_⟩
  · rintro ⟨η, hη, h⟩
    refine ⟨η, hη, fun x hx => h ?_⟩
    show @dist ℝ avSN.toSeminormedAddCommGroup.toPseudoMetricSpace.toDist x 0 ≤ η
    rw [hd]
    exact avSup_le _ _ hx
  · rintro ⟨η, hη, h⟩
    refine ⟨η, hη, fun x hx => h x fun N => ?_⟩
    have hx' : @dist ℝ avSN.toSeminormedAddCommGroup.toPseudoMetricSpace.toDist x 0 ≤ η := hx
    rw [hd] at hx'
    exact (le_avSup N x).trans hx'

lemma mem_nhds_av (W : Set ℝ) :
    W ∈ @nhds ℝ avTop 0 ↔
      ∃ B ∈ @nhds ℝ bohrTop 0, ∃ η : ℝ, 0 < η ∧ ∀ x ∈ B, (∀ N, avPhi N x ≤ η) → x ∈ W := by
  have h : @nhds ℝ avTop 0 = @nhds ℝ bohrTop 0 ⊓ @nhds ℝ avNormTop 0 := @nhds_inf ℝ bohrTop avNormTop 0
  rw [h, Filter.mem_inf_iff_superset]
  constructor
  · rintro ⟨B, hB, C, hC, hBC⟩
    obtain ⟨η, hη, h⟩ := (mem_nhds_avNorm C).1 hC
    exact ⟨B, hB, η, hη, fun x hx hN => hBC ⟨hx, h x hN⟩⟩
  · rintro ⟨B, hB, η, hη, hW⟩
    exact ⟨B, hB, {x | ∀ N, avPhi N x ≤ η}, (mem_nhds_avNorm _).2 ⟨η, hη, fun x hx => hx⟩,
      fun x hx => hW x hx.1 hx.2⟩

/-- `γ` is coarser than the Euclidean topology. -/
theorem av_coarser_euclid (x : ℝ) : 𝓝 x ≤ @nhds ℝ avTop x := by
  intro W hW
  have h0 := (mem_nhds_translate _ av_group x W).1 hW
  obtain ⟨B, hB, η, hη, hBW⟩ := (mem_nhds_av _).1 h0
  have hB' : B ∈ 𝓝 (0 : ℝ) :=
    gam_coarser_euclid (fun _ => 0) 0 (fun _ => by simp) 0 (nhds_mono (gam_le_bohr _) hB)
  have h2 : (fun y => x + y) ⁻¹' W ∈ 𝓝 (0 : ℝ) := by
    refine Filter.mem_of_superset (Filter.inter_mem hB' (Metric.ball_mem_nhds (0 : ℝ) hη)) fun y hy => ?_
    refine hBW y hy.1 fun N => (avPhi_le_abs N y).trans (le_of_lt ?_)
    have h := hy.2
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at h
  rw [← map_add_left_nhds_zero x]
  exact h2

/-! ## `γ` is not precompact -/

lemma dint_third : dint (1 / 3) = 1 / 3 := by
  unfold dint
  have h : ‖((1 / 3 : ℝ) : AddCircle (1 : ℝ))‖ = |(1 / 3 : ℝ)| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 (by norm_num)
  rw [h]; norm_num

lemma dint_pow_third (e : ℕ) : dint ((2 : ℝ) ^ e / 3) = 1 / 3 := by
  have h : ∀ e : ℕ, ∃ z : ℤ, ∃ s : ℝ, (s = 1 / 3 ∨ s = -(1 / 3)) ∧ (2 : ℝ) ^ e / 3 = s - z := by
    intro e
    induction e with
    | zero => exact ⟨0, 1 / 3, Or.inl rfl, by norm_num⟩
    | succ n ih =>
      obtain ⟨z, s, hs, he⟩ := ih
      have e1 : (2 : ℝ) ^ (n + 1) / 3 = 2 * ((2 : ℝ) ^ n / 3) := by rw [pow_succ]; ring
      rcases hs with rfl | rfl
      · refine ⟨2 * z - 1, -(1 / 3), Or.inr rfl, ?_⟩
        rw [e1, he]; push_cast; ring
      · refine ⟨2 * z + 1, 1 / 3, Or.inl rfl, ?_⟩
        rw [e1, he]; push_cast; ring
  obtain ⟨z, s, hs, he⟩ := h e
  rw [he, dint_sub_int]
  rcases hs with rfl | rfl
  · exact dint_third
  · rw [dint_neg]; exact dint_third

lemma sum_big (q : ℕ) : ∑ p ∈ Finset.range q, dint ((2 : ℝ) ^ q / 3 / 2 ^ (p + 1)) = q / 3 := by
  have h : ∀ p ∈ Finset.range q, dint ((2 : ℝ) ^ q / 3 / 2 ^ (p + 1)) = 1 / 3 := by
    intro p hp
    have hp' : p + 1 ≤ q := by have := Finset.mem_range.1 hp; omega
    have e1 : (2 : ℝ) ^ q = 2 ^ (q - (p + 1)) * 2 ^ (p + 1) := by rw [← pow_add, Nat.sub_add_cancel hp']
    have e2 : (2 : ℝ) ^ q / 3 / 2 ^ (p + 1) = 2 ^ (q - (p + 1)) / 3 := by rw [e1]; field_simp
    rw [e2, dint_pow_third]
  rw [Finset.sum_congr rfl h]
  simp [div_eq_mul_inv]

lemma sum_small (r k : ℕ) : ∑ p ∈ Finset.range (r + k), dint ((2 : ℝ) ^ r / 3 / 2 ^ (p + 1)) ≤ r / 3 + 1 / 3 := by
  rw [Finset.sum_range_add, sum_big]
  have h : ∑ x ∈ Finset.range k, dint ((2 : ℝ) ^ r / 3 / 2 ^ (r + x + 1)) ≤
      ∑ x ∈ Finset.range k, (1 / 3) * ((2 : ℝ) ^ (x + 1))⁻¹ := by
    refine Finset.sum_le_sum fun x _ => (dint_le_abs _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (by positivity), show r + x + 1 = r + (x + 1) by omega, pow_add]
    field_simp
  rw [← Finset.mul_sum] at h
  have := sum_half_le k
  linarith

theorem av_not_precompact : ¬ ∀ W ∈ @nhds ℝ avTop 0, ∃ F : Finset ℝ, ∀ x : ℝ, ∃ f ∈ F, x - f ∈ W := by
  intro h
  have hW : {x : ℝ | avSup x < 1 / 8} ∈ @nhds ℝ avTop 0 := by
    refine (mem_nhds_av _).2 ⟨univ, Filter.univ_mem, 1 / 16, by norm_num, fun x _ hx => ?_⟩
    exact lt_of_le_of_lt (avSup_le _ _ hx) (by norm_num)
  obtain ⟨F, hF⟩ := h _ hW
  set x : ℕ → ℝ := fun m => (2 : ℝ) ^ (8 ^ (m + 1)) / 3 with hx
  have hfar : ∀ j m : ℕ, j < m → 1 / 4 ≤ avSup (x m - x j) := by
    intro j m hjm
    set q := 8 ^ (m + 1) with hq
    set r := 8 ^ (j + 1) with hr
    have h8 : 8 * r ≤ q := by
      rw [hq, hr, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hr8 : 8 ≤ r := by
      rw [hr]; exact le_self_pow₀ (by norm_num) (by omega)
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have h1 : avPhi q (x m) = 1 / 3 := by
      unfold avPhi
      simp only [hx, ← hq]
      rw [sum_big]
      field_simp
    have h2 : avPhi q (x j) ≤ 1 / 12 := by
      unfold avPhi
      simp only [hx, ← hr]
      rw [div_le_iff₀ hq0]
      have h3 := sum_small r (q - r)
      rw [show r + (q - r) = q by omega] at h3
      have h4 : (4 : ℝ) * (r + 1) ≤ q := by exact_mod_cast (show 4 * (r + 1) ≤ q by omega)
      linarith
    have h5 := avPhi_add_le q (x m - x j) (x j)
    rw [sub_add_cancel] at h5
    have h6 := le_avSup q (x m - x j)
    linarith
  choose f hfF hfW using fun m => hF (x m)
  obtain ⟨m, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun m => (⟨f m, hfF m⟩ : F))
  have hf : f m = f j := congrArg Subtype.val heq
  have key : ∀ a b : ℕ, a < b → f a = f b → False := by
    intro a b hab hfab
    have h1 := hfar a b hab
    have h2 : x b - x a = (x b - f b) - (x a - f b) := by ring
    have h3 := avSup_sub_le (x b - f b) (x a - f b)
    rw [← h2] at h3
    have h4 : avSup (x b - f b) < 1 / 8 := hfW b
    have h5 : avSup (x a - f b) < 1 / 8 := by rw [← hfab]; exact hfW a
    linarith
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact key m j h' hf
  · exact key j m h' hf.symm

theorem av_ne_bohr : avTop ≠ bohrTop := by
  intro h
  refine av_not_precompact fun W hW => ?_
  rw [h] at hW
  obtain ⟨F, η, hη, hsub⟩ := exists_bset_subset hW
  obtain ⟨X, hX⟩ := bohr_tb F hη
  refine ⟨X, fun x => ?_⟩
  obtain ⟨x0, hx0, h⟩ := hX x
  exact ⟨x0, hx0, hsub h⟩

/-! ## The group `Λ` and the trace -/

/-- `a ∈ Λ`. -/
def InL (a : ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ n, avPhi N (a * sT n) ≤ ε

lemma inL_zero : InL 0 := fun ε hε => Eventually.of_forall fun N n => by
  rw [zero_mul, avPhi_zero]; exact hε.le

lemma inL_neg {a : ℝ} (ha : InL a) : InL (-a) := fun ε hε => (ha ε hε).mono fun N h n => by
  rw [neg_mul, avPhi_neg]; exact h n

lemma inL_add {a b : ℝ} (ha : InL a) (hb : InL b) : InL (a + b) := fun ε hε => by
  filter_upwards [ha (ε / 2) (by linarith), hb (ε / 2) (by linarith)] with N h1 h2 n
  rw [add_mul]
  have := avPhi_add_le N (a * sT n) (b * sT n)
  have := h1 n
  have := h2 n
  linarith

lemma sumT_av : ∀ l : List ℝ, (∀ a ∈ l, InL a) → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ x ∈ sumT sT l, avPhi N x ≤ ε := by
  intro l
  induction l with
  | nil =>
    intro _ ε hε
    refine Eventually.of_forall fun N x hx => ?_
    have : x = 0 := by simpa [sumT] using hx
    rw [this, avPhi_zero]; exact hε.le
  | cons a l ih =>
    intro hl ε hε
    have h1 := hl a (List.mem_cons_self) (ε / 2) (by linarith)
    have h2 := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb)) (ε / 2) (by linarith)
    filter_upwards [h1, h2] with N hN1 hN2
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.1 hx
    obtain ⟨τ, hτ, rfl⟩ := hu
    have hu' : avPhi N (a • τ) ≤ ε / 2 := by
      rw [smul_eq_mul]
      rcases hτ with rfl | ⟨n, rfl | rfl⟩
      · rw [mul_zero, avPhi_zero]; linarith
      · exact hN1 n
      · rw [mul_neg, avPhi_neg]; exact hN1 n
    have := avPhi_add_le N (a • τ) v
    have := hN2 v hv
    linarith

lemma avPhi_mem_nhds_bohr (N : ℕ) {η : ℝ} (hη : 0 < η) : {y : ℝ | avPhi N y < η} ∈ @nhds ℝ bohrTop 0 := by
  have h : (⋂ p ∈ Finset.range N, {y : ℝ | dint (((2 : ℝ) ^ (p + 1))⁻¹ * y) < η / 2}) ∈ @nhds ℝ bohrTop 0 :=
    (Filter.biInter_finset_mem _).2 fun p _ => dint_mem_nhds_bohr _ (by linarith)
  refine Filter.mem_of_superset h fun y hy => ?_
  show avPhi N y < η
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · simpa [avPhi, h0] using hη
  have hle : avPhi N y ≤ η / 2 := by
    unfold avPhi
    rw [div_le_iff₀ (by exact_mod_cast h0)]
    have h1 : ∀ p ∈ Finset.range N, dint (y / 2 ^ (p + 1)) ≤ η / 2 := by
      intro p hp
      have h2 := mem_iInter₂.1 hy p hp
      rw [div_eq_inv_mul]
      exact le_of_lt h2
    refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
    simp [mul_comm]
  linarith

/-- `γ` and the Bohr topology induce the same topology on every member of `I_S(Λ)`. -/
theorem av_trace (m : ℝ) (l : List ℝ) (hl : ∀ a ∈ l, InL a) (J : Set ℝ) (hJ : J ⊆ Icc (-m) m + sumT sT l) :
    TopologicalSpace.induced (Subtype.val : J → ℝ) avTop =
      TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop := by
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ x ∈ J, avPhi N x ≤ ε := by
    intro ε hε
    have h1 := sumT_av l hl (ε / 2) (by linarith)
    have h2 : Tendsto (fun N : ℕ => |m| / (N : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have h3 := h2.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
    filter_upwards [h1, h3] with N hN1 hN3
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.1 (hJ hx)
    have hu' : |u| ≤ |m| := (abs_le.2 ⟨hu.1, hu.2⟩).trans (le_abs_self m)
    have hub : avPhi N u ≤ ε / 2 :=
      (avPhi_le_abs_div N u).trans ((div_le_div_of_nonneg_right hu' (Nat.cast_nonneg _)).trans hN3.le)
    have := avPhi_add_le N u v
    have := hN1 v hv
    linarith
  refine le_antisymm (induced_mono av_le_bohr) ?_
  have hc : @Continuous J ℝ (TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop) avTop Subtype.val := by
    letI : TopologicalSpace J := TopologicalSpace.induced (Subtype.val : J → ℝ) bohrTop
    refine (@continuous_iff_continuousAt J ℝ _ avTop _).2 fun x0 => ?_
    intro W hW
    have hW0 : (fun y => (x0 : ℝ) + y) ⁻¹' W ∈ @nhds ℝ avTop 0 :=
      (mem_nhds_translate _ av_group _ _).1 hW
    obtain ⟨B, hB, η, hη, hBW⟩ := (mem_nhds_av _).1 hW0
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hbound (η / 2) (by linarith))
    set C : Set ℝ := B ∩ ⋂ N ∈ Finset.range N0, {y : ℝ | avPhi N y < η} with hC
    have hCmem : C ∈ @nhds ℝ bohrTop 0 :=
      Filter.inter_mem hB ((Filter.biInter_finset_mem _).2 fun N _ => avPhi_mem_nhds_bohr N hη)
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
    have hall : ∀ N, avPhi N ((x : ℝ) - x0) ≤ η := by
      intro N
      by_cases hN : N < N0
      · have := mem_iInter₂.1 hx'.2 N (Finset.mem_range.2 hN)
        exact le_of_lt this
      · have h1 := hN0 N (by omega) _ x.2
        have h2 := hN0 N (by omega) _ x0.2
        have := avPhi_sub_le N (x : ℝ) (x0 : ℝ)
        linarith
    have := hBW _ hx'.1 hall
    simpa using this
  exact continuous_iff_le_induced.1 hc

/-! ## Binary digits of uniform density zero -/

lemma dint_digits_shift (d : ℕ → Fin 2) (e : ℕ) :
    dint (Real.ofDigits d * 2 ^ e) ≤ Real.ofDigits (fun i => d (i + e)) := by
  have hs := Real.ofDigits_eq_sum_add_ofDigits d e
  obtain ⟨z, hz⟩ := sum_digits_int d e
  have e1 : Real.ofDigits d * 2 ^ e = Real.ofDigits (fun i => d (i + e)) - ((-z : ℤ) : ℝ) := by
    rw [hs]
    push_cast
    rw [← hz]
    field_simp
    ring
  rw [e1, dint_sub_int]
  refine (dint_le_abs _).trans (le_of_eq ?_)
  exact abs_of_nonneg (Real.ofDigits_nonneg _)

lemma tsum_half : ∑' i : ℕ, ((2 : ℝ) ^ (i + 1))⁻¹ = 1 := by
  have h : (fun i : ℕ => ((2 : ℝ) ^ (i + 1))⁻¹) = fun i => (1 / 2) * (1 / 2) ^ i := by
    funext i
    rw [pow_succ, mul_inv, one_div, inv_pow]
    ring
  rw [h, tsum_mul_left, tsum_geometric_two]
  norm_num

lemma summable_half : Summable (fun i : ℕ => ((2 : ℝ) ^ (i + 1))⁻¹) := by
  have h : (fun i : ℕ => ((2 : ℝ) ^ (i + 1))⁻¹) = fun i => (1 / 2) * (1 / 2) ^ i := by
    funext i
    rw [pow_succ, mul_inv, one_div, inv_pow]
    ring
  rw [h]
  exact summable_geometric_two.mul_left _

/-- The main estimate: if every window of length `N` has at most `H` digits `1`, then the sum is at most `H + 1`. -/
lemma sum_digits_bound (d : ℕ → Fin 2) (N M : ℕ) (H : ℝ)
    (hH : ∀ m, (∑ i ∈ Finset.Ico m (m + N), ((d i : ℕ) : ℝ)) ≤ H) :
    ∑ p ∈ Finset.range N, dint (Real.ofDigits d * 2 ^ M / 2 ^ (p + 1)) ≤ H + 1 := by
  have hsplit : N = min N M + (N - min N M) := by omega
  have hA : ∑ p ∈ Finset.range (min N M), dint (Real.ofDigits d * 2 ^ M / 2 ^ (p + 1)) ≤ H := by
    have h1 : ∀ p ∈ Finset.range (min N M), dint (Real.ofDigits d * 2 ^ M / 2 ^ (p + 1)) ≤
        ∑' i, Real.ofDigitsTerm (fun i => d (i + (M - (p + 1)))) i := by
      intro p hp
      have hp' : p + 1 ≤ M := by have := Finset.mem_range.1 hp; omega
      have e1 : (2 : ℝ) ^ M = 2 ^ (M - (p + 1)) * 2 ^ (p + 1) := by rw [← pow_add, Nat.sub_add_cancel hp']
      have e2 : Real.ofDigits d * 2 ^ M / 2 ^ (p + 1) = Real.ofDigits d * 2 ^ (M - (p + 1)) := by
        rw [e1]; field_simp
      rw [e2]
      exact dint_digits_shift d _
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Summable.tsum_finsetSum (fun p _ => Real.summable_ofDigitsTerm)]
    have h2 : ∀ i : ℕ, ∑ p ∈ Finset.range (min N M), Real.ofDigitsTerm (fun i => d (i + (M - (p + 1)))) i ≤
        H * ((2 : ℝ) ^ (i + 1))⁻¹ := by
      intro i
      unfold Real.ofDigitsTerm
      rw [← Finset.sum_mul]
      push_cast
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hinj : Set.InjOn (fun p => i + (M - (p + 1))) (Finset.range (min N M) : Set ℕ) := by
        intro a ha b hb hab
        have ha' := Finset.mem_range.1 ha
        have hb' := Finset.mem_range.1 hb
        simp only at hab
        omega
      rw [← Finset.sum_image (f := fun x => ((d x : ℕ) : ℝ)) hinj]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)) (hH (i + (M - N)))
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      have hp' := Finset.mem_range.1 hp
      rw [Finset.mem_Ico]
      omega
    refine (Summable.tsum_le_tsum h2 (summable_sum fun p _ => Real.summable_ofDigitsTerm)
      (summable_half.mul_left H)).trans (le_of_eq ?_)
    rw [tsum_mul_left, tsum_half, mul_one]
  have hB : ∑ k ∈ Finset.range (N - min N M), dint (Real.ofDigits d * 2 ^ M / 2 ^ (min N M + k + 1)) ≤ 1 := by
    refine le_trans (Finset.sum_le_sum fun k hk => ?_) (sum_half_le (N - min N M))
    have hk' := Finset.mem_range.1 hk
    have hmin : min N M = M := by omega
    rw [hmin]
    refine (dint_le_abs _).trans ?_
    have h0 := Real.ofDigits_nonneg d
    have h1 := Real.ofDigits_le_one d
    rw [abs_of_nonneg (by positivity), show M + k + 1 = M + (k + 1) by omega, pow_add]
    have e2 : Real.ofDigits d * 2 ^ M / (2 ^ M * 2 ^ (k + 1)) = Real.ofDigits d * ((2 : ℝ) ^ (k + 1))⁻¹ := by
      field_simp
    rw [e2]
    exact mul_le_of_le_one_left (by positivity) h1
  have hsum := Finset.sum_range_add (fun p => dint (Real.ofDigits d * 2 ^ M / 2 ^ (p + 1))) (min N M) (N - min N M)
  rw [← hsplit] at hsum
  rw [hsum]
  linarith

/-- A number whose binary digits have uniform density zero belongs to `Λ`. -/
theorem inL_of_digits (d : ℕ → Fin 2)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ m, (∑ i ∈ Finset.Ico m (m + N), ((d i : ℕ) : ℝ)) ≤ ε * N) :
    InL (Real.ofDigits d) := by
  intro ε hε
  have h2 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have h3 := h2.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
  filter_upwards [h (ε / 2) (by linarith), h3, eventually_gt_atTop 0] with N hN h1 hN0
  intro n
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hsum := sum_digits_bound d N ((n + 1) ^ 2) _ hN
  have e1 : sT n = (2 : ℝ) ^ ((n + 1) ^ 2) := by unfold sT sS; rfl
  unfold avPhi
  rw [e1, div_le_iff₀ hN']
  have h4 : (1 : ℝ) < ε / 2 * N := by
    have := (div_lt_iff₀ hN').1 h1
    linarith
  linarith

/-- A set whose elements above `G` are `G` apart has few elements in a window. -/
lemma card_spread (s : Finset ℕ) (m N G : ℕ) (hG : 0 < G) (hs : ∀ x ∈ s, m ≤ x ∧ x < m + N)
    (hgap : ∀ x ∈ s, ∀ y ∈ s, x < y → x + G ≤ y) : s.card ≤ N / G + 1 := by
  have h : s.card ≤ (Finset.range (N / G + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun x => (x - m) / G) (fun x hx => ?_) (fun x hx y hy hxy => ?_)
    · have h1 := hs x hx
      have h2 : (x - m) / G ≤ N / G := Nat.div_le_div_right (by omega)
      exact Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le h2))
    · have key : ∀ a ∈ s, ∀ b ∈ s, a < b → (a - m) / G = (b - m) / G → False := by
        intro a ha b hb hab he
        have h1 := hs a ha
        have h2 := hgap a ha b hb hab
        have h3 : (a - m) / G + 1 ≤ (b - m) / G := by
          rw [← Nat.add_div_right _ hG]
          exact Nat.div_le_div_right (by omega)
        omega
      rcases lt_trichotomy x y with h' | h' | h'
      · exact (key x (Finset.mem_coe.1 hx) y (Finset.mem_coe.1 hy) h' hxy).elim
      · exact h'
      · exact (key y (Finset.mem_coe.1 hy) x (Finset.mem_coe.1 hx) h' hxy.symm).elim
  simpa using h

/-! ## No single sequence serves all of `Λ` -/

lemma exists_scale (x : ℝ) (h0 : 0 < x) (h4 : x ≤ 1 / 4) : ∃ q : ℕ, 1 / 4 < x * 2 ^ q ∧ x * 2 ^ q ≤ 1 / 2 := by
  have hex : ∃ q : ℕ, 1 / 4 < x * 2 ^ q := by
    obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt (1 / 4 / x) (by norm_num : (1 : ℝ) < 2)
    refine ⟨q, ?_⟩
    rw [div_lt_iff₀ h0] at hq
    linarith [mul_comm x ((2 : ℝ) ^ q)]
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  have hne : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h, pow_zero, mul_one] at this
    linarith
  have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  have e1 : (2 : ℝ) ^ Nat.find hex = 2 ^ (Nat.find hex - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have := not_lt.1 hprev
  rw [e1]
  nlinarith

theorem exists_not_inA (δ : ℕ → ℝ) (h0 : ∀ k, δ k ≠ 0) (hlim : Tendsto δ atTop (𝓝 0)) :
    ∃ a : ℝ, InL a ∧ ¬ InA δ sT a := by
  classical
  have hsmall : ∀ᶠ k in atTop, |δ k| ≤ 1 / 4 := by
    have h := (hlim.abs).eventually (Iio_mem_nhds (show |(0 : ℝ)| < 1 / 4 by norm_num))
    exact h.mono fun k hk => le_of_lt hk
  obtain ⟨K, hK⟩ := eventually_atTop.1 hsmall
  have hstep : ∀ s : ℕ × ℕ × ℝ, ∃ t : ℕ × ℕ × ℝ, ∃ b n : ℕ,
      s.1 < t.1 ∧ 4 * s.2.1 + 4 ≤ t.2.1 ∧ b ≤ 1 ∧ t.2.2 = s.2.2 + (b : ℝ) * ((2 : ℝ) ^ t.2.1)⁻¹ ∧
      |δ t.1| * sT n ≤ (1 / 2) * 2 ^ t.2.1 ∧ 1 / 8 ≤ dint (t.2.2 * δ t.1 * sT n) := by
    rintro ⟨k0, i0, v⟩
    set k := max K (k0 + 1) with hk
    obtain ⟨q, hq1, hq2⟩ := exists_scale |δ k| (abs_pos.2 (h0 k)) (hK k (le_max_left _ _))
    set n := q + 4 * i0 + 4 with hn
    set i := (n + 1) ^ 2 - q with hi
    have hsq : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hiq : i + q = (n + 1) ^ 2 := by omega
    have hsT : sT n = (2 : ℝ) ^ i * 2 ^ q := by
      have e1 : sT n = (2 : ℝ) ^ ((n + 1) ^ 2) := by unfold sT sS; rfl
      rw [e1, ← pow_add, hiq]
    have hy : ((2 : ℝ) ^ i)⁻¹ * δ k * sT n = δ k * 2 ^ q := by
      rw [hsT]; field_simp
    have habs : |δ k * 2 ^ q| = |δ k| * 2 ^ q := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ q)]
    have hdy : dint (δ k * 2 ^ q) = |δ k| * 2 ^ q := by
      unfold dint
      have h : ‖((δ k * 2 ^ q : ℝ) : AddCircle (1 : ℝ))‖ = |δ k * 2 ^ q| :=
        (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2 (by rw [habs]; simpa using hq2)
      rw [h, habs]
    have hsz : |δ k| * sT n ≤ (1 / 2) * 2 ^ i := by
      rw [hsT]
      have := mul_le_mul_of_nonneg_left hq2 (show (0 : ℝ) ≤ 2 ^ i by positivity)
      nlinarith
    have hch : ∃ b : ℕ, b ≤ 1 ∧ 1 / 8 ≤ dint ((v + (b : ℝ) * ((2 : ℝ) ^ i)⁻¹) * δ k * sT n) := by
      by_cases hc : 1 / 8 ≤ dint (v * δ k * sT n)
      · exact ⟨0, by norm_num, by simpa using hc⟩
      · refine ⟨1, le_rfl, ?_⟩
        have e2 : (v + ((1 : ℕ) : ℝ) * ((2 : ℝ) ^ i)⁻¹) * δ k * sT n = v * δ k * sT n + δ k * 2 ^ q := by
          rw [← hy]; push_cast; ring
        rw [e2]
        have h := dint_sub_le (v * δ k * sT n + δ k * 2 ^ q) (v * δ k * sT n)
        rw [add_sub_cancel_left, hdy] at h
        have := not_le.1 hc
        linarith
    obtain ⟨b, hb1, hb2⟩ := hch
    exact ⟨(k, i, v + (b : ℝ) * ((2 : ℝ) ^ i)⁻¹), b, n,
      lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _), by show 4 * i0 + 4 ≤ i; omega, hb1, rfl, hsz, hb2⟩
  choose f hf using hstep
  set st : ℕ → ℕ × ℕ × ℝ := fun j => Nat.rec (0, 0, 0) (fun _ s => f s) j with hst
  have hst0 : st 0 = (0, 0, 0) := rfl
  have hstS : ∀ j, st (j + 1) = f (st j) := fun _ => rfl
  choose b n hk hi hb hv hsz hbig using fun j => hf (st j)
  simp only [← hstS] at hk hi hv hsz hbig
  set I : ℕ → ℕ := fun j => (st (j + 1)).2.1 with hI
  have hIgrow : ∀ j, 4 * I j + 4 ≤ I (j + 1) := fun j => hi (j + 1)
  have hI4 : ∀ j, 4 ≤ I j := fun j => by
    have h : 4 * (st j).2.1 + 4 ≤ I j := hi j
    omega
  have hImono : StrictMono I := strictMono_nat_of_lt_succ fun j => by
    have := hIgrow j
    omega
  have hIadd : ∀ j l, I j + l ≤ I (j + l) := by
    intro j l
    induction l with
    | zero => simp
    | succ l ih =>
      have := hImono (show j + l < j + (l + 1) by omega)
      omega
  have hval : ∀ J, (st J).2.2 = ∑ l ∈ Finset.range J, (b l : ℝ) * ((2 : ℝ) ^ I l)⁻¹ := by
    intro J
    induction J with
    | zero => simp [hst0]
    | succ J ih => rw [Finset.sum_range_succ, ← ih]; exact hv J
  set d : ℕ → Fin 2 := fun r => if ∃ j, I j = r + 1 ∧ b j = 1 then 1 else 0 with hd
  have hg : Function.Injective (fun j => I j - 1) := by
    intro x y hxy
    have := hI4 x
    have := hI4 y
    simp only at hxy
    exact hImono.injective (by omega)
  have hdg : ∀ j, ((d (I j - 1) : ℕ) : ℝ) = (b j : ℝ) := by
    intro j
    have h4 := hI4 j
    have hiff : (∃ j', I j' = I j - 1 + 1 ∧ b j' = 1) ↔ b j = 1 := by
      constructor
      · rintro ⟨j', hj', hbj⟩
        have : j' = j := hImono.injective (by omega)
        rwa [this] at hbj
      · intro h
        exact ⟨j, by omega, h⟩
    have hb' := hb j
    by_cases h : b j = 1
    · have : d (I j - 1) = 1 := by simp only [hd]; rw [if_pos (hiff.2 h)]
      rw [this, h]; norm_num
    · have : d (I j - 1) = 0 := by simp only [hd]; rw [if_neg (fun h' => h (hiff.1 h'))]
      have h0b : b j = 0 := by omega
      rw [this, h0b]; norm_num
  set c : ℕ → ℝ := fun j => (b j : ℝ) * ((2 : ℝ) ^ I j)⁻¹ with hc
  have hterm : ∀ j, Real.ofDigitsTerm d (I j - 1) = c j := by
    intro j
    have h4 := hI4 j
    unfold Real.ofDigitsTerm
    rw [hdg j, show I j - 1 + 1 = I j by omega]
    simp [hc]
  have hsupp : Function.support (Real.ofDigitsTerm d) ⊆ range (fun j => I j - 1) := by
    intro r hr
    by_contra hnr
    have : d r = 0 := by
      simp only [hd]
      rw [if_neg]
      rintro ⟨j, hj, _⟩
      exact hnr ⟨j, by simp only; omega⟩
    exact hr (by simp [Real.ofDigitsTerm, this])
  have ha : Real.ofDigits d = ∑' j, c j := by
    unfold Real.ofDigits
    rw [← hg.tsum_eq hsupp]
    exact tsum_congr hterm
  have hcs : Summable c := by
    have h : Summable (fun j => Real.ofDigitsTerm d (I j - 1)) := Real.summable_ofDigitsTerm.comp_injective hg
    exact h.congr hterm
  refine ⟨Real.ofDigits d, ?_, ?_⟩
  · refine inL_of_digits d fun ε hε => ?_
    obtain ⟨G, hG⟩ := exists_nat_gt (2 / ε)
    have hG0 : 0 < G := by
      have : (0 : ℝ) < 2 / ε := div_pos two_pos hε
      exact_mod_cast this.trans hG
    have h2 : Tendsto (fun N : ℕ => ((G : ℝ) + 1) / (N : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have h3 := h2.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
    filter_upwards [h3, eventually_gt_atTop 0] with N hN hN0
    intro m
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
    set s := (Finset.Ico m (m + N)).filter (fun r => d r = 1) with hs
    have hsum : ∑ r ∈ Finset.Ico m (m + N), ((d r : ℕ) : ℝ) = (s.card : ℝ) := by
      rw [hs, Finset.natCast_card_filter]
      refine Finset.sum_congr rfl fun r _ => ?_
      rcases Fin.exists_fin_two.1 ⟨d r, rfl⟩ with h | h <;> simp [h]
    have hlow : (s.filter (fun r => r < G)).card ≤ G := by
      have h : s.filter (fun r => r < G) ⊆ Finset.range G := fun r hr =>
        Finset.mem_range.2 (Finset.mem_filter.1 hr).2
      simpa using Finset.card_le_card h
    have hhigh : (s.filter (fun r => ¬ r < G)).card ≤ N / G + 1 := by
      refine card_spread _ m N G hG0 (fun x hx => ?_) (fun x hx y hy hxy => ?_)
      · exact Finset.mem_Ico.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).1
      · have hpos : ∀ z ∈ s.filter (fun r => ¬ r < G), ∃ j, I j = z + 1 := by
          intro z hz
          have h1 := (Finset.mem_filter.1 (Finset.mem_filter.1 hz).1).2
          by_contra hcon
          have : d z = 0 := by
            simp only [hd]
            rw [if_neg]
            rintro ⟨j, hj, _⟩
            exact hcon ⟨j, hj⟩
          rw [this] at h1
          exact absurd h1 (by decide)
        obtain ⟨jx, hjx⟩ := hpos x hx
        obtain ⟨jy, hjy⟩ := hpos y hy
        have hlt : jx < jy := hImono.lt_iff_lt.1 (by omega)
        have h1 := hImono.monotone (show jx + 1 ≤ jy by omega)
        have h2 := hIgrow jx
        have h3 : G ≤ x := not_lt.1 (Finset.mem_filter.1 hx).2
        omega
    have hcard : s.card ≤ G + (N / G + 1) := by
      rw [← Finset.card_filter_add_card_filter_not (s := s) (fun r => r < G)]
      exact Nat.add_le_add hlow hhigh
    rw [hsum]
    have h1 : (s.card : ℝ) ≤ G + ((N / G : ℕ) : ℝ) + 1 := by
      have : (s.card : ℝ) ≤ ((G + (N / G + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
      push_cast at this ⊢
      linarith
    have h4 : ((N / G : ℕ) : ℝ) ≤ (N : ℝ) / G := Nat.cast_div_le
    have hGr : (0 : ℝ) < G := by exact_mod_cast hG0
    have h5 : (N : ℝ) / G ≤ ε / 2 * N := by
      rw [div_le_iff₀ hGr]
      have h6 : 2 < (G : ℝ) * ε := by
        rw [div_lt_iff₀ hε] at hG
        exact hG
      nlinarith
    have h7 : (G : ℝ) + 1 < ε / 2 * N := by
      have := (div_lt_iff₀ hN').1 hN
      linarith
    linarith
  · intro hA
    obtain ⟨K1, hK1⟩ := eventually_atTop.1 (hA (1 / 32) (by norm_num))
    have hkj : ∀ j, j ≤ (st (j + 1)).1 := by
      intro j
      induction j with
      | zero => omega
      | succ j ih =>
        have : (st (j + 1)).1 < (st (j + 1 + 1)).1 := hk (j + 1)
        omega
    set J := K1 with hJ
    have hbound := hK1 (st (J + 1)).1 (hkj J) (n J)
    set k := (st (J + 1)).1 with hkdef
    set a := Real.ofDigits d with hadef
    have hsplit : a = (st (J + 1)).2.2 + ∑' l, c (l + (J + 1)) := by
      rw [ha, hval (J + 1), ← Summable.sum_add_tsum_nat_add (J + 1) hcs]
    have htail0 : 0 ≤ ∑' l, c (l + (J + 1)) := tsum_nonneg fun l => by simp only [hc]; positivity
    have htail : ∑' l, c (l + (J + 1)) ≤ 2 * ((2 : ℝ) ^ I (J + 1))⁻¹ := by
      have h1 : ∀ l : ℕ, c (l + (J + 1)) ≤ ((2 : ℝ) ^ I (J + 1))⁻¹ * (1 / 2) ^ l := by
        intro l
        have h2 : I (J + 1) + l ≤ I (l + (J + 1)) := by
          have h := hIadd (J + 1) l
          rwa [Nat.add_comm (J + 1) l] at h
        have h3 : (b (l + (J + 1)) : ℝ) ≤ 1 := by exact_mod_cast hb (l + (J + 1))
        have h4 : ((2 : ℝ) ^ I (l + (J + 1)))⁻¹ ≤ ((2 : ℝ) ^ (I (J + 1) + l))⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) h2)
        have h5 : ((2 : ℝ) ^ (I (J + 1) + l))⁻¹ = ((2 : ℝ) ^ I (J + 1))⁻¹ * (1 / 2) ^ l := by
          rw [pow_add, mul_inv, one_div, inv_pow]
        simp only [hc]
        rw [← h5]
        exact le_trans (mul_le_of_le_one_left (by positivity) h3) h4
      have hs2 : Summable (fun l : ℕ => ((2 : ℝ) ^ I (J + 1))⁻¹ * (1 / 2) ^ l) :=
        summable_geometric_two.mul_left _
      have hs1 : Summable (fun l => c (l + (J + 1))) := (summable_nat_add_iff (J + 1)).2 hcs
      refine (Summable.tsum_le_tsum h1 hs1 hs2).trans (le_of_eq ?_)
      rw [tsum_mul_left, tsum_geometric_two]
      ring
    have herr : |(∑' l, c (l + (J + 1))) * δ k * sT (n J)| ≤ 1 / 16 := by
      have hsT0 : (0 : ℝ) ≤ sT (n J) := by unfold sT sS; positivity
      rw [mul_assoc, abs_mul, abs_of_nonneg htail0, abs_mul, abs_of_nonneg hsT0]
      have h1 : |δ k| * sT (n J) ≤ (1 / 2) * 2 ^ I J := hsz J
      have h2 : I J + 4 ≤ I (J + 1) := by
        have := hIgrow J
        omega
      have h3 : (2 : ℝ) ^ I J * 16 ≤ 2 ^ I (J + 1) := by
        have : (2 : ℝ) ^ (I J + 4) ≤ 2 ^ I (J + 1) := pow_le_pow_right₀ (by norm_num) h2
        rw [pow_add] at this
        norm_num at this ⊢
        linarith
      refine (mul_le_mul htail h1 (mul_nonneg (abs_nonneg _) hsT0) (by positivity)).trans ?_
      have hp : (0 : ℝ) < 2 ^ I (J + 1) := by positivity
      have e1 : 2 * ((2 : ℝ) ^ I (J + 1))⁻¹ * (1 / 2 * 2 ^ I J) = 2 ^ I J / 2 ^ I (J + 1) := by
        field_simp
      rw [e1, div_le_iff₀ hp]
      linarith
    have hlow : 1 / 8 ≤ dint ((st (J + 1)).2.2 * δ k * sT (n J)) := hbig J
    have e3 : (st (J + 1)).2.2 * δ k * sT (n J) =
        a * δ k * sT (n J) - (∑' l, c (l + (J + 1))) * δ k * sT (n J) := by
      rw [hsplit]; ring
    rw [e3] at hlow
    have h1 := dint_sub_le (a * δ k * sT (n J)) ((∑' l, c (l + (J + 1))) * δ k * sT (n J))
    have h2 := (dint_le_abs ((∑' l, c (l + (J + 1))) * δ k * sT (n J))).trans herr
    linarith

/-- For a topology with the data of Step 1 of Proposition 16.1, the trace condition fails for some `a ∈ Λ`. -/
theorem av_no_step1_witness (γ : TopologicalSpace ℝ) (hfine : γ ≤ bohrTop)
    (E : Set ℝ) (hV : ∀ ε : ℝ, 0 < ε → {x : ℝ | ∀ c ∈ E, dint (c * x) ≤ ε} ∈ @nhds ℝ γ 0)
    (c : ℕ → ℝ) (c0 : ℝ) (hc : ∀ k, c k ∈ E) (hne : ∀ k, c k ≠ c0) (hlim : Tendsto c atTop (euclidNhds c0)) :
    ∃ a : ℝ, InL a ∧ ¬ ∀ W ∈ @nhds ℝ γ 0, ∃ B ∈ @nhds ℝ bohrTop 0,
      B ∩ (Icc (-1 : ℝ) 1 + (a • Tset sT + (-a) • Tset sT)) ⊆ W := by
  obtain ⟨a, ha, hn⟩ := exists_not_inA (fun k => c k - c0) (fun k => sub_ne_zero.2 (hne k))
    (tendsto_sub_euclid c c0 hlim)
  exact ⟨a, ha, fun h => hn (inA_of_step1 γ hfine E hV c c0 hc hlim sT a h)⟩

end Two
end PVG
