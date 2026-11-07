import LeanCheck.PVGAlgebra
import LeanCheck.PVGInterpolation

/-!
# PVG: reductions for Question 9.5 (Lean check)

Scope. Concrete formalization of `K = Hom(ℝ, 𝕋)` (all algebraic characters of `ℝ`, topology of pointwise
convergence; compact, Hausdorff, a real vector space with `(c • κ)(b) = κ(c b)`), of `e x = (b ↦ b x mod 1)`,
and of the ultrafilter limits `L y U = lim_U e(y_k)` for free ultrafilters `U` on `ℕ`. It checks the
reductions recorded in the research note `PVG_Q95_reduction_2026-11-06.md` for Question 9.5 of
`PVG_v10` (is some compact `η_π` Fréchet–Urysohn, or at least sequentially compact?):

* `L_add`, `L_smul`, `L_const` (R3): `y ↦ L_y(U)` is additive and `L_{c y}(U) = c • L_y(U)`.
* `interpolation_bounded`: Lemma 8.26(a) with the location `0 ≤ b ≤ 2 / |y 0|` of the point `b`.
* `L_sub_ne_e` (R2): for a lacunary sequence `y` (`y 0 ≠ 0`, `4 |y k| ≤ |y (k+1)|`) and distinct free
  ultrafilters `U ≠ V`, `L_y(U) - L_y(V) ≠ e d` for every `d`; in particular `L_y(U) ≠ L_y(V)`.
* `R1`, `R1_linear` (R1): the criterion `SC π a` ("some infinite `B` on which `π ∘ L_a` is constant on
  the free ultrafilters containing `B`", the criterion of Question 9.5 for sequential compactness of
  `η_π`) holds for every real sequence as soon as it holds for every lacunary sequence.
* `R4`, `R1_R4` (R4): some linear retraction `π` (`π e(1) = 1`) satisfies `SC π` for all sequences iff
  there is a choice `y ↦ B_y` for the lacunary sequences such that the real span of all differences
  `L_y(U) - L_y(V)` (`U, V` free, containing `B_y`) meets `ℝ e(1)` only in `0`. `R4` is stated for an
  arbitrary real vector space; it uses `PVG.exists_maximal_admissible`, `PVG.maximal_admissible_iff` and
  `PVG.retraction` of `PVGAlgebra`.

Not formalized: the pseudotopology `η_π` itself, so "sequentially compact" is replaced by the criterion
`SC`; Question 9.5 itself (whether such a choice exists) remains open. A Lean proof verifies its formal
statement under its hypotheses; the correspondence with the research note requires mathematical review.
-/
open Filter Topology

namespace PVG
namespace Q95

/-- The compact group `K = Hom(ℝ, 𝕋)` of all algebraic characters of `ℝ`, with the topology of
pointwise convergence. -/
abbrev K := ℝ →+ AddCircle (1 : ℝ)

instance : TopologicalSpace K :=
  TopologicalSpace.induced (fun κ : K => (κ : ℝ → AddCircle (1 : ℝ))) inferInstance

lemma isEmbedding_coe : Topology.IsEmbedding (fun κ : K => (κ : ℝ → AddCircle (1 : ℝ))) :=
  ⟨⟨rfl⟩, fun _ _ h => DFunLike.coe_injective h⟩

lemma continuous_eval (b : ℝ) : Continuous (fun κ : K => κ b) :=
  (continuous_apply b).comp continuous_induced_dom

instance : T2Space K := isEmbedding_coe.t2Space

instance : CompactSpace K := by
  have hclosed : IsClosed (Set.range (fun κ : K => (κ : ℝ → AddCircle (1 : ℝ)))) := by
    have : Set.range (fun κ : K => (κ : ℝ → AddCircle (1 : ℝ))) =
        (⋂ x, ⋂ y, {f : ℝ → AddCircle (1 : ℝ) | f (x + y) = f x + f y}) ∩
          {f : ℝ → AddCircle (1 : ℝ) | f 0 = 0} := by
      ext f
      simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨κ, rfl⟩
        exact ⟨fun x y => κ.map_add x y, κ.map_zero⟩
      · rintro ⟨hadd, h0⟩
        exact ⟨⟨⟨f, h0⟩, hadd⟩, rfl⟩
    rw [this]
    exact (isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x + y)) ((continuous_apply x).add (continuous_apply y))).inter
      (isClosed_eq (continuous_apply 0) continuous_const)
  exact (Topology.IsClosedEmbedding.mk isEmbedding_coe hclosed).compactSpace

/-- `e x : b ↦ b x mod 1`. -/
def e (x : ℝ) : K :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (AddMonoidHom.mulRight x)

@[simp] lemma e_apply (x b : ℝ) : e x b = ((b * x : ℝ) : AddCircle (1 : ℝ)) := rfl

lemma continuous_e : Continuous e := by
  rw [continuous_induced_rng]
  refine continuous_pi fun b => ?_
  show Continuous fun x : ℝ => ((b * x : ℝ) : AddCircle (1 : ℝ))
  exact (continuous_quotient_mk'.comp (continuous_const.mul continuous_id))

lemma e_add (x y : ℝ) : e (x + y) = e x + e y := by
  ext b; simp [mul_add]

instance : SMul ℝ K := ⟨fun c κ => κ.comp (AddMonoidHom.mulLeft c)⟩

lemma smul_apply (c : ℝ) (κ : K) (b : ℝ) : (c • κ) b = κ (c * b) := rfl

instance : Module ℝ K where
  one_smul κ := by ext b; simp [smul_apply]
  mul_smul c c' κ := by ext b; simp [smul_apply, mul_comm, mul_left_comm]
  smul_zero c := by ext b; simp [smul_apply]
  smul_add c κ κ' := by ext b; simp [smul_apply]
  add_smul c c' κ := by ext b; simp [smul_apply, add_mul]
  zero_smul κ := by ext b; simp [smul_apply]

lemma e_eq_smul (x : ℝ) : e x = x • e 1 := by
  ext b; simp [smul_apply, mul_comm]

lemma smul_e (c x : ℝ) : c • e x = e (c * x) := by
  ext b; simp [smul_apply]; ring_nf

instance : ContinuousAdd K := by
  refine ⟨?_⟩
  rw [continuous_induced_rng]
  refine continuous_pi fun b => ?_
  show Continuous fun p : K × K => (p.1 + p.2) b
  simp only [AddMonoidHom.add_apply]
  exact ((continuous_eval b).comp continuous_fst).add ((continuous_eval b).comp continuous_snd)

lemma continuous_smul_const (c : ℝ) : Continuous (fun κ : K => c • κ) := by
  rw [continuous_induced_rng]
  refine continuous_pi fun b => ?_
  show Continuous fun κ : K => (c • κ) b
  simp only [smul_apply]
  exact continuous_eval (c * b)

/-- Free ultrafilters on `ℕ`. -/
def Free (U : Ultrafilter ℕ) : Prop := (U : Filter ℕ) ≤ Filter.cofinite

/-- `L_y(U) = lim_U e(y_k)`. -/
noncomputable def L (y : ℕ → ℝ) (U : Ultrafilter ℕ) : K :=
  (Ultrafilter.map (fun k => e (y k)) U).lim

lemma tendsto_L (y : ℕ → ℝ) (U : Ultrafilter ℕ) : Tendsto (fun k => e (y k)) U (𝓝 (L y U)) := by
  have h := Ultrafilter.le_nhds_lim (Ultrafilter.map (fun k => e (y k)) U)
  rw [Ultrafilter.coe_map] at h
  exact h

lemma L_eq_of_tendsto {y : ℕ → ℝ} {U : Ultrafilter ℕ} {κ : K}
    (h : Tendsto (fun k => e (y k)) U (𝓝 κ)) : L y U = κ :=
  tendsto_nhds_unique (tendsto_L y U) h

/-- Additivity of `y ↦ L_y(U)`. -/
theorem L_add (y z : ℕ → ℝ) (U : Ultrafilter ℕ) : L (y + z) U = L y U + L z U := by
  apply L_eq_of_tendsto
  have := (tendsto_L y U).add (tendsto_L z U)
  simpa [Pi.add_apply, e_add] using this

/-- Homogeneity of `y ↦ L_y(U)`: `L_{c y}(U) = c • L_y(U)`. -/
theorem L_smul (c : ℝ) (y : ℕ → ℝ) (U : Ultrafilter ℕ) : L (c • y) U = c • L y U := by
  apply L_eq_of_tendsto
  have := ((continuous_smul_const c).tendsto _).comp (tendsto_L y U)
  simpa [Function.comp_def, smul_e, Pi.smul_apply, smul_eq_mul] using this

/-- Constant sequences. -/
theorem L_const (x : ℝ) (U : Ultrafilter ℕ) : L (fun _ => x) U = e x :=
  L_eq_of_tendsto tendsto_const_nhds


/-! ### Interpolation with a bound on `b` -/

section Interp

variable (S : Set ℕ) {a : ℕ → ℝ}

lemma exists_first' (ha : ∀ k, 0 < a k) : ∃ J : Iv S a 0, 0 ≤ J.l ∧ J.r ≤ 2 / a 0 := by
  have e2 : a 0 * (2 / a 0 - 0) = 2 := by
    have := (ha 0).ne'
    rw [sub_zero]
    field_simp
  obtain ⟨l', r', h1, h2, h3, h4⟩ := window S 0 (a := a 0) (l := 0) (r := 2 / a 0) (ha 0)
    (by rw [e2]; norm_num)
  exact ⟨⟨l', r', h3, h4⟩, h1, h2⟩

noncomputable def chain' (ha : ∀ k, 0 < a k) (hr : ∀ k, 4 * a k ≤ a (k + 1)) :
    (k : ℕ) → Iv S a k
  | 0 => Classical.choose (exists_first' S ha)
  | k + 1 => Classical.choose (exists_next S ha hr k (chain' ha hr k))

lemma chain'_succ_le (ha : ∀ k, 0 < a k) (hr : ∀ k, 4 * a k ≤ a (k + 1)) (k : ℕ) :
    (chain' S ha hr k).l ≤ (chain' S ha hr (k + 1)).l ∧
      (chain' S ha hr (k + 1)).r ≤ (chain' S ha hr k).r :=
  Classical.choose_spec (exists_next S ha hr k (chain' S ha hr k))

end Interp

/-- Lemma 8.26(a) with the location of `b`: `0 ≤ b ≤ 2 / |y 0|`. -/
theorem interpolation_bounded (y : ℕ → ℝ) (h0 : y 0 ≠ 0) (hr : ∀ k, 4 * |y k| ≤ |y (k + 1)|)
    (S : Set ℕ) : ∃ b : ℝ, 0 ≤ b ∧ b ≤ 2 / |y 0| ∧ ∀ k, Good S k (b * y k) := by
  set a : ℕ → ℝ := fun k => |y k| with hadef
  have ha : ∀ k, 0 < a k := by
    intro k
    induction k with
    | zero => exact abs_pos.2 h0
    | succ k ih =>
      have := hr k
      simp only [hadef] at ih ⊢
      linarith
  have hr' : ∀ k, 4 * a k ≤ a (k + 1) := hr
  set t : ℕ → Set ℝ := fun k => Set.Icc (chain' S ha hr' k).l (chain' S ha hr' k).r with htdef
  have hnest : ∀ k, t (k + 1) ⊆ t k := by
    intro k x hx
    obtain ⟨h1, h2⟩ := chain'_succ_le S ha hr' k
    exact ⟨h1.trans hx.1, hx.2.trans h2⟩
  have hne : ∀ k, (t k).Nonempty := by
    intro k
    refine ⟨(chain' S ha hr' k).l, le_refl _, ?_⟩
    have := (chain' S ha hr' k).len
    have hp : 0 < 1 / (3 * a k) := by have := ha k; positivity
    linarith
  obtain ⟨b, hb⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hnest hne
    isCompact_Icc (fun k => isClosed_Icc)
  have hspec : 0 ≤ (chain' S ha hr' 0).l ∧ (chain' S ha hr' 0).r ≤ 2 / a 0 :=
    Classical.choose_spec (exists_first' S ha)
  have hb0 : b ∈ t 0 := Set.mem_iInter.1 hb 0
  refine ⟨b, le_trans hspec.1 hb0.1, le_trans hb0.2 hspec.2, fun k => ?_⟩
  have hbk : b ∈ t k := Set.mem_iInter.1 hb k
  have hg := (chain' S ha hr' k).good b hbk
  exact ⟨fun hk => farFromInt_mul_abs (hg.1 hk), fun hk => nearInt_mul_abs (hg.2 hk)⟩

/-! ### Norms on the circle -/

lemma norm_circle_ge_of_far {t : ℝ} (h : FarFromInt t) : 1 / 3 ≤ ‖(t : AddCircle (1 : ℝ))‖ := by
  rw [AddCircle.norm_eq]
  simpa using h (round t)

lemma norm_circle_le_of_near {t : ℝ} (h : NearInt t) : ‖(t : AddCircle (1 : ℝ))‖ ≤ 1 / 6 := by
  obtain ⟨m, hm⟩ := h
  rw [AddCircle.norm_eq]
  simpa using (round_le t m).trans hm

lemma norm_circle_le_abs (t : ℝ) : ‖(t : AddCircle (1 : ℝ))‖ ≤ |t| := by
  rw [AddCircle.norm_eq]
  simpa using round_le t 0

/-! ### R2: a lacunary sequence has no pairwise obstruction -/

lemma abs_y_ge (y : ℕ → ℝ) (hr : ∀ k, 4 * |y k| ≤ |y (k + 1)|) (k : ℕ) :
    4 ^ k * |y 0| ≤ |y k| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := hr k
    calc 4 ^ (k + 1) * |y 0| = 4 * (4 ^ k * |y 0|) := by ring
      _ ≤ 4 * |y k| := by linarith
      _ ≤ |y (k + 1)| := this

lemma exists_separating {U V : Ultrafilter ℕ} (hUV : U ≠ V) : ∃ S : Set ℕ, S ∈ U ∧ Sᶜ ∈ V := by
  by_contra hcon
  have hcon' : ∀ S : Set ℕ, S ∈ U → Sᶜ ∉ V := fun S hS hS' => hcon ⟨S, hS, hS'⟩
  apply hUV
  have hle : (V : Filter ℕ) ≤ U := by
    intro s hs
    by_contra hns
    exact hcon' s hs ((Ultrafilter.compl_mem_iff_notMem).2 hns)
  exact (Ultrafilter.coe_le_coe.1 hle).symm

/-- **R2.** For a lacunary sequence `y` and distinct free ultrafilters `U ≠ V`, the difference
`L_y(U) - L_y(V)` is not of the form `e d`; in particular `L_y(U) ≠ L_y(V)`. -/
theorem L_sub_ne_e (y : ℕ → ℝ) (h0 : y 0 ≠ 0) (hr : ∀ k, 4 * |y k| ≤ |y (k + 1)|)
    {U V : Ultrafilter ℕ} (hU : Free U) (hV : Free V) (hUV : U ≠ V) (d : ℝ) :
    L y U - L y V ≠ e d := by
  obtain ⟨S, hSU, hSV⟩ := exists_separating hUV
  intro hcontra
  have h0pos : 0 < |y 0| := abs_pos.2 h0
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (12 * |d| + 1) / |y 0| < 4 ^ m :=
    pow_unbounded_of_one_lt _ (by norm_num)
  have hym : 12 * |d| + 1 < |y m| := by
    have h1 := abs_y_ge y hr m
    rw [div_lt_iff₀ h0pos] at hm
    linarith
  have hympos : 0 < |y m| := by linarith [abs_nonneg d]
  -- the tail sequence
  set y' : ℕ → ℝ := fun j => y (j + m) with hy'
  have hy'0 : y' 0 ≠ 0 := by
    have : y m ≠ 0 := abs_pos.1 hympos
    simpa [hy'] using this
  have hy'r : ∀ k, 4 * |y' k| ≤ |y' (k + 1)| := fun k => by
    simpa [hy', add_right_comm] using hr (k + m)
  obtain ⟨b, hb0, hbb, hgood⟩ := interpolation_bounded y' hy'0 hy'r {j | j + m ∈ S}
  have hbm : b ≤ 2 / |y m| := by simpa [hy'] using hbb
  -- far on S, near off S, for indices ≥ m
  have hfar : ∀ k, m ≤ k → k ∈ S → 1 / 3 ≤ ‖((b * y k : ℝ) : AddCircle (1 : ℝ))‖ := by
    intro k hk hkS
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact norm_circle_ge_of_far ((hgood j).1 hkS)
  have hnear : ∀ k, m ≤ k → k ∉ S → ‖((b * y k : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1 / 6 := by
    intro k hk hkS
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    exact norm_circle_le_of_near ((hgood j).2 hkS)
  have hcof : {k : ℕ | m ≤ k} ∈ (Filter.cofinite : Filter ℕ) := by
    rw [Filter.mem_cofinite]
    have : ({k : ℕ | m ≤ k}ᶜ : Set ℕ) = Set.Iio m := by ext k; simp
    rw [this]; exact Set.finite_Iio m
  have hUev : ∀ᶠ k in (U : Filter ℕ), 1 / 3 ≤ ‖e (y k) b‖ := by
    have : {k : ℕ | m ≤ k} ∩ S ∈ U := inter_mem (hU hcof) hSU
    filter_upwards [this] with k hk
    exact hfar k hk.1 hk.2
  have hVev : ∀ᶠ k in (V : Filter ℕ), ‖e (y k) b‖ ≤ 1 / 6 := by
    have : {k : ℕ | m ≤ k} ∩ Sᶜ ∈ V := inter_mem (hV hcof) hSV
    filter_upwards [this] with k hk
    exact hnear k hk.1 hk.2
  have hcU : Tendsto (fun k => ‖e (y k) b‖) U (𝓝 ‖L y U b‖) :=
    (continuous_norm.tendsto _).comp (((continuous_eval b).tendsto _).comp (tendsto_L y U))
  have hcV : Tendsto (fun k => ‖e (y k) b‖) V (𝓝 ‖L y V b‖) :=
    (continuous_norm.tendsto _).comp (((continuous_eval b).tendsto _).comp (tendsto_L y V))
  have h1 : 1 / 3 ≤ ‖L y U b‖ := ge_of_tendsto hcU hUev
  have h2 : ‖L y V b‖ ≤ 1 / 6 := le_of_tendsto hcV hVev
  have h3 : 1 / 6 ≤ ‖(L y U - L y V) b‖ := by
    have := norm_sub_norm_le (L y U b) (L y V b)
    simp only [AddMonoidHom.sub_apply]
    linarith
  rw [hcontra] at h3
  simp only [e_apply] at h3
  have h4 := norm_circle_le_abs (b * d)
  have h5 : |b * d| ≤ 2 / |y m| * |d| := by
    rw [abs_mul, abs_of_nonneg hb0]
    exact mul_le_mul_of_nonneg_right hbm (abs_nonneg d)
  have h6 : 2 / |y m| * |d| < 1 / 6 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hympos]
    nlinarith [abs_nonneg d]
  linarith


/-! ### R1: reduction to lacunary sequences -/

/-- The criterion of Question 9.5 for a map `π : K → ℝ` and a real sequence `a`: some infinite `B`
such that `π ∘ L_a` is constant on the free ultrafilters containing `B`. -/
def SC (π : K → ℝ) (a : ℕ → ℝ) : Prop :=
  ∃ B : Set ℕ, B.Infinite ∧ ∃ x : ℝ, ∀ U : Ultrafilter ℕ, Free U → B ∈ U → π (L a U) = x

/-- An unbounded real sequence has a lacunary subsequence. -/
lemma exists_lacunary_subseq (a : ℕ → ℝ) (hunb : ∀ M : ℝ, ∃ k, M < |a k|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ a (φ 0) ≠ 0 ∧ ∀ k, 4 * |a (φ k)| ≤ |a (φ (k + 1))| := by
  have step : ∀ i : ℕ, ∃ j, i < j ∧ 4 * |a i| ≤ |a j| := by
    intro i
    obtain ⟨k, hk⟩ := hunb (4 * |a i| + ∑ n ∈ Finset.range (i + 1), |a n|)
    have hsum : 0 ≤ ∑ n ∈ Finset.range (i + 1), |a n| := Finset.sum_nonneg (fun n _ => abs_nonneg _)
    have hik : i < k := by
      by_contra hle
      have hk' : k ∈ Finset.range (i + 1) := Finset.mem_range.2 (by omega)
      have := Finset.single_le_sum (f := fun n => |a n|) (fun n _ => abs_nonneg (a n)) hk'
      have h4 : 0 ≤ 4 * |a i| := by positivity
      linarith
    exact ⟨k, hik, by linarith⟩
  choose f hf1 hf2 using step
  obtain ⟨i0, hi0⟩ := hunb 0
  set φ : ℕ → ℕ := fun k => f^[k] i0 with hφdef
  have hsucc : ∀ k, φ (k + 1) = f (φ k) := fun k => Function.iterate_succ_apply' f k i0
  refine ⟨φ, strictMono_nat_of_lt_succ (fun k => by rw [hsucc]; exact hf1 _), ?_, fun k => ?_⟩
  · exact abs_pos.1 (by simpa [hφdef] using hi0)
  · rw [hsucc]; exact hf2 _

lemma ultrafilter_le_map {φ : ℕ → ℕ} {U : Ultrafilter ℕ} (hU : Free U)
    (hB : Set.range φ ∈ U) : (U : Filter ℕ) ≤ Filter.map φ atTop := by
  intro s hs
  rw [Filter.mem_map, Filter.mem_atTop_sets] at hs
  obtain ⟨n, hn⟩ := hs
  have hF : (φ '' Set.Iio n)ᶜ ∈ (U : Filter ℕ) := by
    apply hU
    rw [Filter.mem_cofinite, compl_compl]
    exact (Set.finite_Iio n).image φ
  refine Filter.mem_of_superset (inter_mem hB hF) ?_
  rintro x ⟨⟨j, rfl⟩, hx⟩
  by_cases hj : n ≤ j
  · exact hn j hj
  · exact absurd ⟨j, Set.mem_Iio.2 (by omega), rfl⟩ hx

/-- **R1.** If the criterion `SC π` holds for every lacunary sequence, it holds for every real
sequence (`π (e x) = x`). Here `SC π a` is the criterion for sequential compactness of `η_π`
stated in Question 9.5 of PVG_v10; the pseudotopology `η_π` itself is not formalized. -/
theorem R1 (π : K → ℝ) (hπ : ∀ x, π (e x) = x)
    (h : ∀ y : ℕ → ℝ, y 0 ≠ 0 → (∀ k, 4 * |y k| ≤ |y (k + 1)|) → SC π y) (a : ℕ → ℝ) :
    SC π a := by
  by_cases hb : ∃ M : ℝ, ∀ k, |a k| ≤ M
  · -- bounded: a Euclidean convergent subsequence
    obtain ⟨M, hM⟩ := hb
    obtain ⟨y, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (-M) M) (x := a)
      (fun k => by simpa [abs_le] using hM k)
    refine ⟨Set.range φ, Set.infinite_range_of_injective hφ.injective, y, fun U hU hB => ?_⟩
    have hUle := ultrafilter_le_map hU hB
    have h1 : Tendsto a U (𝓝 y) := (tendsto_map'_iff.2 hlim).mono_left hUle
    have h2 : Tendsto (fun k => e (a k)) U (𝓝 (e y)) := (continuous_e.tendsto y).comp h1
    rw [L_eq_of_tendsto h2, hπ]
  · -- unbounded: a lacunary subsequence
    have hunb : ∀ M : ℝ, ∃ k, M < |a k| := by
      intro M
      by_contra hcon
      exact hb ⟨M, fun k => not_lt.1 (fun hk => hcon ⟨k, hk⟩)⟩
    obtain ⟨φ, hφ, hφ0, hφr⟩ := exists_lacunary_subseq a hunb
    obtain ⟨B', hB'inf, x, hx⟩ := h (a ∘ φ) hφ0 hφr
    refine ⟨φ '' B', Set.Infinite.image hφ.injective.injOn hB'inf, x, fun V hV hBV => ?_⟩
    have hrange : Set.range φ ∈ (V : Filter ℕ) :=
      Filter.mem_of_superset hBV (Set.image_subset_range _ _)
    set U' : Ultrafilter ℕ := Ultrafilter.comap V hφ.injective hrange with hU'
    have hcoe : (U' : Filter ℕ) = Filter.comap φ V := Ultrafilter.coe_comap V hφ.injective hrange
    have hmap : Filter.map φ (U' : Filter ℕ) = V := by
      rw [hcoe]; exact Filter.map_comap_of_mem hrange
    have hfree : Free U' := by
      intro s hs
      rw [Filter.mem_cofinite] at hs
      by_contra hns
      have hsc : sᶜ ∈ (U' : Filter ℕ) := (Ultrafilter.compl_mem_iff_notMem).2 hns
      have himg : φ '' sᶜ ∈ (V : Filter ℕ) := by
        rw [← hmap]; exact Filter.image_mem_map hsc
      have hfin : (φ '' sᶜ)ᶜ ∈ (V : Filter ℕ) := by
        apply hV
        rw [Filter.mem_cofinite, compl_compl]
        exact hs.image φ
      exact (Ultrafilter.compl_mem_iff_notMem.1 hfin) himg
    have hB'U' : B' ∈ U' := by
      have : φ ⁻¹' (φ '' B') = B' := Set.preimage_image_eq _ hφ.injective
      rw [← this, ← Ultrafilter.mem_coe, hcoe]
      exact Filter.preimage_mem_comap hBV
    have hL : L (a ∘ φ) U' = L a V := by
      apply L_eq_of_tendsto
      have h1 := tendsto_L a V
      rw [← hmap] at h1
      exact tendsto_map'_iff.1 h1
    have := hx U' hfree hB'U'
    rw [hL] at this
    exact this

/-! ### R4: reformulation as an admissibility problem -/

/-- **R4** (abstract form). Let `K` be a real vector space with a nonzero vector `e1`, `Lac` a set of
sequences, `Lf y U ∈ K` any assignment and `Free` any predicate on ultrafilters. There is a linear
`π : K → ℝ` with `π e1 = 1` that is constant, for every `y ∈ Lac`, on `Lf y U` over the `U` in some infinite
`B_y`, if and only if there is a choice `y ↦ B_y` such that the real span of all differences
`Lf y U - Lf y V` (`U, V` free, containing `B_y`) meets the line `ℝ e1` only in `0`. -/
theorem R4 {K' : Type*} [AddCommGroup K'] [Module ℝ K'] (e1 : K') (he : e1 ≠ 0)
    (Lac : Set (ℕ → ℝ)) (Lf : (ℕ → ℝ) → Ultrafilter ℕ → K') (Fr : Ultrafilter ℕ → Prop) :
    (∃ π : K' →ₗ[ℝ] ℝ, π e1 = 1 ∧ ∀ y ∈ Lac, ∃ B : Set ℕ, B.Infinite ∧ ∃ x : ℝ,
        ∀ U : Ultrafilter ℕ, Fr U → B ∈ U → π (Lf y U) = x) ↔
    ∃ Bsel : (ℕ → ℝ) → Set ℕ, (∀ y ∈ Lac, (Bsel y).Infinite) ∧
      Disjoint (Submodule.span ℝ {v : K' | ∃ y ∈ Lac, ∃ U V : Ultrafilter ℕ, Fr U ∧ Fr V ∧
        Bsel y ∈ U ∧ Bsel y ∈ V ∧ v = Lf y U - Lf y V}) (ℝ ∙ e1) := by
  constructor
  · rintro ⟨π, hπ1, hπ⟩
    classical
    refine ⟨fun y => if hy : y ∈ Lac then Classical.choose (hπ y hy) else ∅, ?_, ?_⟩
    · intro y hy
      simp only [hy, dite_true]
      exact (Classical.choose_spec (hπ y hy)).1
    · have hker : Submodule.span ℝ {v : K' | ∃ y ∈ Lac, ∃ U V : Ultrafilter ℕ, Fr U ∧ Fr V ∧
          (if hy : y ∈ Lac then Classical.choose (hπ y hy) else ∅) ∈ U ∧
          (if hy : y ∈ Lac then Classical.choose (hπ y hy) else ∅) ∈ V ∧ v = Lf y U - Lf y V}
          ≤ LinearMap.ker π := by
        rw [Submodule.span_le]
        rintro v ⟨y, hy, U, V, hU, hV, hBU, hBV, rfl⟩
        simp only [hy, dite_true] at hBU hBV
        obtain ⟨_, x, hx⟩ := Classical.choose_spec (hπ y hy)
        simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
        rw [hx U hU hBU, hx V hV hBV, sub_self]
      exact ((PVG.ker_isCompl π hπ1).symm.disjoint).mono_left hker
  · rintro ⟨Bsel, hinf, hdisj⟩
    set W := Submodule.span ℝ {v : K' | ∃ y ∈ Lac, ∃ U V : Ultrafilter ℕ, Fr U ∧ Fr V ∧
        Bsel y ∈ U ∧ Bsel y ∈ V ∧ v = Lf y U - Lf y V} with hW
    obtain ⟨H, hWH, hHadm, hHmax⟩ := PVG.exists_maximal_admissible (ℝ ∙ e1) W hdisj
    have hcod : Codisjoint H (ℝ ∙ e1) := (PVG.maximal_admissible_iff (ℝ ∙ e1) H hHadm).1 hHmax
    have hcompl : IsCompl (ℝ ∙ e1) H := ⟨hHadm.symm, hcod.symm⟩
    refine ⟨PVG.retraction he H hcompl, PVG.retraction_apply_e1 he H hcompl, fun y hy => ?_⟩
    refine ⟨Bsel y, hinf y hy, ?_⟩
    by_cases hne : ∃ U0 : Ultrafilter ℕ, Fr U0 ∧ Bsel y ∈ U0
    · obtain ⟨U0, hU0, hB0⟩ := hne
      refine ⟨PVG.retraction he H hcompl (Lf y U0), fun U hU hBU => ?_⟩
      have hmem : Lf y U - Lf y U0 ∈ W :=
        Submodule.subset_span ⟨y, hy, U, U0, hU, hU0, hBU, hB0, rfl⟩
      have hker : Lf y U - Lf y U0 ∈ LinearMap.ker (PVG.retraction he H hcompl) := by
        rw [PVG.ker_retraction he H hcompl]; exact hWH hmem
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hker
      exact hker
    · exact ⟨0, fun U hU hBU => absurd ⟨U, hU, hBU⟩ hne⟩


/-! ### Concrete form -/

lemma e_one_ne_zero : e 1 ≠ 0 := by
  intro h
  have h2 := congrArg (fun κ : K => κ (1 / 2)) h
  simp only [e_apply, AddMonoidHom.zero_apply] at h2
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h2
  have h3 : (2 * (n : ℝ)) = 1 := by
    simp only [zsmul_eq_mul, mul_one] at hn
    linarith
  have h4 : 2 * n = 1 := by exact_mod_cast h3
  omega

lemma linear_retraction_e (π : K →ₗ[ℝ] ℝ) (h1 : π (e 1) = 1) (x : ℝ) : π (e x) = x := by
  rw [e_eq_smul, map_smul, h1]; simp

/-- The set of lacunary sequences. -/
def Lac : Set (ℕ → ℝ) := {y | y 0 ≠ 0 ∧ ∀ k, 4 * |y k| ≤ |y (k + 1)|}

/-- **R1 for linear retractions.** For a real linear `π : K → ℝ` with `π e(1) = 1` (so `π e(x) = x`),
the criterion `SC π` holds for all real sequences if and only if it holds for all lacunary sequences. -/
theorem R1_linear (π : K →ₗ[ℝ] ℝ) (h1 : π (e 1) = 1) :
    (∀ a : ℕ → ℝ, SC π a) ↔ ∀ y ∈ Lac, SC π y :=
  ⟨fun h y _ => h y,
   fun h a => R1 π (linear_retraction_e π h1) (fun y hy0 hyr => h y ⟨hy0, hyr⟩) a⟩

/-- **R1 + R4, concrete form.** Some real linear retraction `π : K → ℝ` (`π e(1) = 1`) satisfies the
criterion `SC π a` for every real sequence `a` if and only if there is a choice `y ↦ B_y` of infinite
sets for the lacunary sequences such that the real span of all differences `L_y(U) - L_y(V)`
(`U, V` free ultrafilters containing `B_y`) meets `ℝ e(1)` only in `0`. -/
theorem R1_R4 :
    (∃ π : K →ₗ[ℝ] ℝ, π (e 1) = 1 ∧ ∀ a : ℕ → ℝ, SC π a) ↔
    ∃ Bsel : (ℕ → ℝ) → Set ℕ, (∀ y ∈ Lac, (Bsel y).Infinite) ∧
      Disjoint (Submodule.span ℝ {v : K | ∃ y ∈ Lac, ∃ U V : Ultrafilter ℕ, Free U ∧ Free V ∧
        Bsel y ∈ U ∧ Bsel y ∈ V ∧ v = L y U - L y V}) (ℝ ∙ e 1) := by
  rw [← R4 (e 1) e_one_ne_zero Lac L Free]
  constructor
  · rintro ⟨π, h1, h⟩
    exact ⟨π, h1, fun y hy => (R1_linear π h1).1 h y hy⟩
  · rintro ⟨π, h1, h⟩
    exact ⟨π, h1, (R1_linear π h1).2 h⟩

end Q95
end PVG
