import LeanCheck.ChainTransfer

/-!
# The dual of `T_f(δ)` is exactly `H_f` (second half of `transfer-v8`)

Part A: linearization lemma -- a character of `ℝ` that is `< 1/4` near `0` on a dense `ℚ`-subspace `N`
equals `x ↦ c x mod 1` on `N`.
-/

namespace LeanCheck

open Filter Topology

section LemmaE

variable (χ : ℝ →+ Circ) (N : AddSubgroup ℝ) (ε : ℝ)

/-- For `y ∈ N` and `n ≥ 1` with `n |y| < ε`: `‖χ y‖ ≤ 1/(4n)`. -/
lemma small_bound (hN : ∀ x ∈ N, ∀ q : ℚ, (q : ℝ) * x ∈ N)
    (hsm : ∀ x ∈ N, |x| < ε → ‖χ x‖ < 1 / 4) {y : ℝ} (hy : y ∈ N) {n : ℕ} (hn : 1 ≤ n)
    (hny : (n : ℝ) * |y| < ε) : ‖χ y‖ ≤ 1 / (4 * n) := by
  apply norm_le_of_multiples (χ y) n hn
  intro j hj
  rw [← map_nsmul]
  apply hsm
  · have h1 : ((j : ℚ) : ℝ) * y ∈ N := hN y hy j
    rw [Rat.cast_natCast] at h1
    rwa [nsmul_eq_mul]
  · rw [nsmul_eq_mul, abs_mul, Nat.abs_cast]
    have : (j : ℝ) ≤ n := by exact_mod_cast hj
    calc (j : ℝ) * |y| ≤ n * |y| := by gcongr
      _ < ε := hny

lemma frac_value (hN : ∀ x ∈ N, ∀ q : ℚ, (q : ℝ) * x ∈ N)
    (hsm : ∀ x ∈ N, |x| < ε → ‖χ x‖ < 1 / 4) {x0 : ℝ} (hx0 : x0 ∈ N) (hlt : |x0| < ε)
    {g0 : ℝ} (hg : (g0 : Circ) = χ x0) (hg4 : |g0| < 1 / 4) {n : ℕ} (hn : 1 ≤ n) :
    χ (x0 / n) = ((g0 / n : ℝ) : Circ) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem : x0 / n ∈ N := by
    have := hN x0 hx0 (1 / (n : ℚ))
    simpa [div_eq_inv_mul] using this
  have hnorm : ‖χ (x0 / n)‖ ≤ 1 / (4 * n) := by
    apply small_bound χ N ε hN hsm hmem hn
    rw [abs_div, Nat.abs_cast]
    rw [mul_div_cancel₀ _ hnr.ne']
    exact hlt
  obtain ⟨t, ht, -, htn⟩ := exists_centered (χ (x0 / n))
  have hnt : |t| ≤ 1 / (4 * n) := by rw [← htn]; exact hnorm
  have hsum : n • χ (x0 / n) = χ x0 := by
    rw [← map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hnr.ne']
  rw [← ht, nsmul_coe_circ, ← hg] at hsum
  have hz : (((n * t - g0 : ℝ)) : Circ) = 0 := by
    rw [AddCircle.coe_sub, hsum, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hz
  rw [zsmul_eq_mul, mul_one] at hk
  have hnt' : |(n : ℝ) * t| ≤ 1 / 4 := by
    rw [abs_mul, Nat.abs_cast]
    calc (n : ℝ) * |t| ≤ n * (1 / (4 * n)) := by gcongr
      _ = 1 / 4 := by field_simp
  have hk0 : k = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hne
      exact_mod_cast this
    have h2 : |(n : ℝ) * t - g0| ≤ |(n : ℝ) * t| + |g0| := abs_sub _ _
    rw [← hk] at h2
    linarith
  rw [hk0] at hk
  simp only [Int.cast_zero] at hk
  have : t = g0 / n := by field_simp; linarith
  rw [← ht, this]

lemma rat_value (hN : ∀ x ∈ N, ∀ q : ℚ, (q : ℝ) * x ∈ N)
    (hsm : ∀ x ∈ N, |x| < ε → ‖χ x‖ < 1 / 4) {x0 : ℝ} (hx0 : x0 ∈ N) (hlt : |x0| < ε)
    {g0 : ℝ} (hg : (g0 : Circ) = χ x0) (hg4 : |g0| < 1 / 4) (q : ℚ) :
    χ ((q : ℝ) * x0) = (((q : ℝ) * g0 : ℝ) : Circ) := by
  have hd : 1 ≤ q.den := q.den_pos
  have h1 : (q : ℝ) * x0 = q.num • (x0 / q.den) := by
    rw [zsmul_eq_mul, Rat.cast_def]; ring
  rw [h1, map_zsmul, frac_value χ N ε hN hsm hx0 hlt hg hg4 hd, zsmul_coe_circ]
  congr 1
  rw [Rat.cast_def]; ring

/-- A character that is `< 1/4` on `N ∩ (-ε, ε)` is linear on a dense `ℚ`-subspace `N`. -/
theorem linearize (hε : 0 < ε) (hN : ∀ x ∈ N, ∀ q : ℚ, (q : ℝ) * x ∈ N)
    (hsm : ∀ x ∈ N, |x| < ε → ‖χ x‖ < 1 / 4) (hdense : Dense (N : Set ℝ)) :
    ∃ c : ℝ, ∀ x ∈ N, χ x = ((c * x : ℝ) : Circ) := by
  obtain ⟨x0, hx0N, hx0⟩ := hdense.exists_mem_open (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) ε))
    ⟨ε / 2, by constructor <;> linarith⟩
  have hx0pos : 0 < x0 := hx0.1
  have hx0abs : |x0| < ε := by rw [abs_of_pos hx0pos]; exact hx0.2
  obtain ⟨g0, hg, -, hgn⟩ := exists_centered (χ x0)
  have hg4 : |g0| < 1 / 4 := by rw [← hgn]; exact hsm x0 hx0N hx0abs
  refine ⟨g0 / x0, ?_⟩
  set c := g0 / x0 with hc
  have hcx0 : c * x0 = g0 := by rw [hc]; field_simp
  -- linear bound on small elements of `N`
  have hlin : ∀ y ∈ N, |y| ≤ ε / 4 → ‖χ y‖ ≤ |y| / ε := by
    intro y hy hyε
    by_cases hy0 : y = 0
    · subst hy0; simp
    have hypos : 0 < |y| := abs_pos.mpr hy0
    set n : ℕ := ⌊ε / (2 * |y|)⌋₊ with hn
    have h2 : 2 ≤ ε / (2 * |y|) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hn1 : 1 ≤ n := by
      rw [hn]; apply Nat.le_floor; norm_num; linarith
    have hnle : (n : ℝ) ≤ ε / (2 * |y|) := Nat.floor_le (by positivity)
    have hnlt : ε / (2 * |y|) < n + 1 := Nat.lt_floor_add_one _
    have hny : (n : ℝ) * |y| < ε := by
      have : (n : ℝ) * |y| ≤ ε / (2 * |y|) * |y| := by gcongr
      have h3 : ε / (2 * |y|) * |y| = ε / 2 := by field_simp
      linarith
    have hb := small_bound χ N ε hN hsm hy (by exact hn1) hny
    refine hb.trans ?_
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h4 : ε / (4 * |y|) ≤ n := by
      have : ε / (4 * |y|) = ε / (2 * |y|) / 2 := by field_simp; ring
      rw [this]; linarith
    rw [div_le_div_iff₀ (by positivity) hε]
    have : ε ≤ n * (4 * |y|) := by
      rw [div_le_iff₀ (by positivity)] at h4; linarith
    nlinarith
  have key : ∀ x ∈ N, ∀ η : ℝ, 0 < η → ‖χ x - ((c * x : ℝ) : Circ)‖ ≤ η := by
    intro x hx η hη
    set K : ℝ := 1 / ε + |c| + 1 with hK
    have hKpos : 0 < K := by positivity
    set δ' : ℝ := min (ε / 4) (η / K) with hδ'
    have hδpos : 0 < δ' := lt_min (by positivity) (by positivity)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
      (show x / x0 - δ' / x0 < x / x0 + δ' / x0 by
        have : 0 < δ' / x0 := by positivity
        linarith)
    have hy : x - (q : ℝ) * x0 ∈ N := N.sub_mem hx (hN x0 hx0N q)
    have hyabs : |x - (q : ℝ) * x0| < δ' := by
      have e : x - (q : ℝ) * x0 = x0 * (x / x0 - q) := by field_simp
      rw [e, abs_mul, abs_of_pos hx0pos, ← lt_div_iff₀' hx0pos, abs_lt]
      constructor
      · have : δ' / x0 > 0 := by positivity
        linarith
      · linarith
    set y := x - (q : ℝ) * x0 with hydef
    have hsplit : χ x - ((c * x : ℝ) : Circ) =
        (χ y - ((c * y : ℝ) : Circ)) + (χ ((q : ℝ) * x0) - ((c * ((q : ℝ) * x0) : ℝ) : Circ)) := by
      have hx' : x = y + (q : ℝ) * x0 := by rw [hydef]; ring
      conv_lhs => rw [hx']
      rw [map_add, mul_add, AddCircle.coe_add]
      abel
    have hzero : χ ((q : ℝ) * x0) - ((c * ((q : ℝ) * x0) : ℝ) : Circ) = 0 := by
      rw [rat_value χ N ε hN hsm hx0N hx0abs hg hg4 q, sub_eq_zero]
      congr 1
      rw [← hcx0]; ring
    rw [hsplit, hzero, add_zero]
    have hy4 : |y| ≤ ε / 4 := (hyabs.le).trans (min_le_left _ _)
    have h1 : ‖χ y‖ ≤ |y| / ε := hlin y hy hy4
    have h2 : ‖((c * y : ℝ) : Circ)‖ ≤ |c| * |y| := by
      have := norm_coe_le (c * y) 0
      simpa [abs_mul] using this
    calc ‖χ y - ((c * y : ℝ) : Circ)‖ ≤ ‖χ y‖ + ‖((c * y : ℝ) : Circ)‖ := norm_sub_le _ _
      _ ≤ |y| / ε + |c| * |y| := add_le_add h1 h2
      _ = (1 / ε + |c|) * |y| := by ring
      _ ≤ K * |y| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); rw [hK]; linarith
      _ ≤ K * (η / K) := by
        apply mul_le_mul_of_nonneg_left _ hKpos.le
        exact (hyabs.le).trans (min_le_right _ _)
      _ = η := by field_simp
  intro x hx
  by_contra hne
  have hpos : 0 < ‖χ x - ((c * x : ℝ) : Circ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have := key x hx (‖χ x - ((c * x : ℝ) : Circ)‖ / 2) (by positivity)
  linarith

end LemmaE

/-! ### Part B: joint kernels are dense -/

section Kernel

/-- The joint map `H x = (f(b_j x))_j : ℝ → ℚ^k`. -/
def Hmap (f : ℝ →+ ℚ) {ι : Type} [Fintype ι] (b : ι → ℝ) : ℝ →+ (ι → ℚ) where
  toFun x := fun j => f (b j * x)
  map_zero' := by funext j; simp
  map_add' x y := by funext j; simp [mul_add]

lemma Hmap_apply (f : ℝ →+ ℚ) {ι : Type} [Fintype ι] (b : ι → ℝ) (x : ℝ) (j : ι) :
    Hmap f b x j = f (b j * x) := rfl

lemma countable_of_cyclic (H : AddSubgroup ℝ) (h : IsAddCyclic H) : (H : Set ℝ).Countable := by
  obtain ⟨g, hg⟩ := h.exists_generator
  refine (Set.countable_range (fun n : ℤ => n • (g : ℝ))).mono ?_
  intro x hx
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

/-- The joint kernel of finitely many `f_{b_j}` is dense in `ℝ`. -/
theorem Hker_dense (f : ℝ →+ ℚ) {ι : Type} [Fintype ι] (b : ι → ℝ) :
    Dense ((Hmap f b).ker : Set ℝ) := by
  rcases AddSubgroup.dense_or_isCyclic (Hmap f b).ker with h | h
  · exact h
  · exfalso
    have hc := countable_of_cyclic _ h
    classical
    let r : (ι → ℚ) → ℝ := fun v => if hv : ∃ x, Hmap f b x = v then hv.choose else 0
    have hsub : (Set.univ : Set ℝ) ⊆ ⋃ v : ι → ℚ, (fun e : ℝ => e + r v) '' ((Hmap f b).ker : Set ℝ) := by
      intro x _
      refine Set.mem_iUnion.2 ⟨Hmap f b x, ⟨x - r (Hmap f b x), ?_, by ring⟩⟩
      have hv : ∃ y, Hmap f b y = Hmap f b x := ⟨x, rfl⟩
      have : r (Hmap f b x) = hv.choose := by simp only [r, dif_pos hv]
      rw [this]
      show Hmap f b (x - hv.choose) = 0
      rw [map_sub, hv.choose_spec, sub_self]
    exact Cardinal.not_countable_real ((Set.countable_iUnion fun v => hc.image _).mono hsub)

lemma Hker_qmul (f : ℝ →+ ℚ) {ι : Type} [Fintype ι] (b : ι → ℝ) :
    ∀ x ∈ (Hmap f b).ker, ∀ q : ℚ, (q : ℝ) * x ∈ (Hmap f b).ker := by
  intro x hx q
  rw [AddMonoidHom.mem_ker] at hx ⊢
  funext j
  have := congrFun hx j
  simp only [Hmap_apply, Pi.zero_apply] at this ⊢
  rw [mul_left_comm, f_ratmul, this, mul_zero]

end Kernel

/-! ### Part C: neighbourhood data and an independent reduction -/

section Reduction

/-- `Fa f a = (x ↦ f(a x))` as a `ℚ`-linear functional on `ℝ`. -/
def Fa (f : ℝ →+ ℚ) (a : ℝ) : ℝ →ₗ[ℚ] ℚ where
  toFun x := f (a * x)
  map_add' x y := by simp [mul_add]
  map_smul' q x := by
    show f (a * (q • x)) = q • f (a * x)
    rw [Rat.smul_def, Rat.smul_def, mul_left_comm]
    have := f_ratmul f q (a * x)
    simpa using this

lemma Fa_apply (f : ℝ →+ ℚ) (a x : ℝ) : Fa f a x = f (a * x) := rfl

/-- Neighbourhood data from `T_f(δ)`-continuity of a character. -/
theorem tf_nhds_data (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (χ : ℝ →+ Circ)
    (hχ : @Continuous ℝ Circ (Tf f δ) circTop χ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ I : Finset ℝ, ∃ U : ℝ → Set ℚ,
      (∀ a ∈ I, U a ∈ @nhds ℚ δ 0) ∧
      ∀ x : ℝ, |x| < ε → (∀ a ∈ I, f (a * x) ∈ U a) → ‖χ x‖ < 1 / 4 := by
  have hS : {y : Circ | ‖y‖ < 1 / 4} ∈ 𝓝 (χ 0) := by
    rw [map_zero]
    exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by simp)
  have hT : χ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} ∈ @nhds ℝ (Tf f δ) 0 :=
    (@Continuous.continuousAt ℝ Circ (Tf f δ) circTop χ 0 hχ) hS
  unfold Tf at hT
  rw [nhds_inf] at hT
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_inf_iff.mp hT
  rw [nhds_iInf] at ht2
  obtain ⟨I, hI, V, hV, hVuniv, hs⟩ := Filter.mem_iInf'.mp ht2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht1
  have hex : ∀ a : ℝ, ∃ U : Set ℚ, U ∈ @nhds ℚ δ 0 ∧ fa f a ⁻¹' U ⊆ V a := by
    intro a
    have h := hV a
    rw [nhds_induced, map_zero] at h
    exact Filter.mem_comap.mp h
  choose U hU hUV using hex
  refine ⟨ε, hε, hI.toFinset, U, fun a _ => hU a, ?_⟩
  intro x hx hxU
  have hx1 : x ∈ t1 := hball (by simpa [Metric.mem_ball, dist_zero_right] using hx)
  have hx2 : x ∈ t2 := by
    rw [hs.1]
    refine Set.mem_iInter₂.mpr (fun a ha => ?_)
    exact hUV a (hxU a (hI.mem_toFinset.mpr ha))
  have : x ∈ χ ⁻¹' {y : Circ | ‖y‖ < 1 / 4} := by
    rw [hsub]; exact ⟨hx1, hx2⟩
  exact this

/-- Finitely many `f_a` can be replaced by a `ℚ`-linearly independent subfamily spanning them. -/
lemma indep_reduction (f : ℝ →+ ℚ) (I : Finset ℝ) :
    ∃ (κ : Type) (_ : Fintype κ) (b : κ → ℝ), LinearIndependent ℚ (fun j => Fa f (b j)) ∧
      ∀ a ∈ I, ∃ q : κ → ℚ, ∀ x : ℝ, f (a * x) = ∑ j, q j * f (b j * x) := by
  obtain ⟨κ, t, hinj, hsp, hli⟩ := exists_linearIndependent' ℚ (fun a : I => Fa f (a : ℝ))
  haveI : Finite κ := Finite.of_injective t hinj
  letI : Fintype κ := Fintype.ofFinite κ
  refine ⟨κ, inferInstance, fun j => ((t j : I) : ℝ), hli, ?_⟩
  intro a ha
  have hmem : Fa f a ∈ Submodule.span ℚ (Set.range ((fun a : I => Fa f (a : ℝ)) ∘ t)) := by
    rw [hsp]; exact Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
  refine ⟨q, fun x => ?_⟩
  have := congrArg (fun m : ℝ →ₗ[ℚ] ℚ => m x) hq
  rw [LinearMap.sum_apply] at this
  simp only [LinearMap.smul_apply, Function.comp, Fa_apply, smul_eq_mul] at this
  exact this.symm

/-- Independent functionals `f_{b_j}` give a surjective joint map `ℝ → ℚ^κ`. -/
lemma Hmap_surj (f : ℝ →+ ℚ) {ι : Type} [Fintype ι] (b : ι → ℝ)
    (hli : LinearIndependent ℚ (fun j => Fa f (b j))) : Function.Surjective (Hmap f b) := by
  classical
  let T : ℝ →ₗ[ℚ] (ι → ℚ) := LinearMap.pi (fun j => Fa f (b j))
  have hT : ∀ x j, T x j = f (b j * x) := fun x j => rfl
  by_contra hns
  have hlt : LinearMap.range T < ⊤ := by
    rw [lt_top_iff_ne_top]; intro htop; apply hns; intro v
    have : v ∈ LinearMap.range T := by rw [htop]; trivial
    obtain ⟨x, hx⟩ := this
    exact ⟨x, by rw [← hx]; funext j; exact (hT x j).symm⟩
  obtain ⟨g, hg0, hgker⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  apply hg0
  have hz : ∑ j, (g fun i => if j = i then 1 else 0) • Fa f (b j) = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 := hgker (LinearMap.mem_range_self T x)
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ g (T x)] at h1
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Fa_apply, smul_eq_mul, LinearMap.zero_apply]
    simp only [hT, smul_eq_mul] at h1
    exact (Finset.sum_congr rfl (fun j _ => mul_comm _ _)).trans h1
  have hc := Fintype.linearIndependent_iff.mp hli _ hz
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ g v]
  simp [hc]

/-- Box refinement: finitely many linear conditions in a rational-scalar-continuous group topology. -/
lemma pi_box (δ : TopologicalSpace ℚ) (hg : @IsTopologicalAddGroup ℚ δ _)
    (hs : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x))
    {ι : Type} [Fintype ι] (I : Finset ℝ) (U : ℝ → Set ℚ) (hU : ∀ a ∈ I, U a ∈ @nhds ℚ δ 0)
    (q : ℝ → ι → ℚ) :
    ∃ W : ι → Set ℚ, (∀ j, W j ∈ @nhds ℚ δ 0) ∧
      ∀ y : ι → ℚ, (∀ j, y j ∈ W j) → ∀ a ∈ I, ∑ j, q a j * y j ∈ U a := by
  classical
  letI : TopologicalSpace ℚ := δ
  haveI : IsTopologicalAddGroup ℚ := hg
  have hA : {y : ι → ℚ | ∀ a ∈ I, ∑ j, q a j * y j ∈ U a} ∈ 𝓝 (0 : ι → ℚ) := by
    have : {y : ι → ℚ | ∀ a ∈ I, ∑ j, q a j * y j ∈ U a} =
        ⋂ a ∈ I, (fun y : ι → ℚ => ∑ j, q a j * y j) ⁻¹' U a := by
      ext y; simp
    rw [this, Filter.biInter_finset_mem]
    intro a ha
    have hc : Continuous (fun y : ι → ℚ => ∑ j, q a j * y j) :=
      continuous_finset_sum _ (fun j _ => (hs (q a j)).comp (continuous_apply j))
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hU a ha)
  rw [nhds_pi, Filter.mem_pi] at hA
  obtain ⟨J, hJ, t, ht, hsub⟩ := hA
  refine ⟨fun j => if j ∈ J then t j else Set.univ, fun j => ?_, fun y hy => ?_⟩
  · by_cases hj : j ∈ J
    · simpa [hj] using ht j
    · simp [hj]
  · have : y ∈ J.pi t := fun j hj => by simpa [hj] using hy j
    exact hsub this

/-- Neighbourhood data in independent form. -/
theorem packaged (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (hg : @IsTopologicalAddGroup ℚ δ _)
    (hs : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x)) (χ : ℝ →+ Circ)
    (hχ : @Continuous ℝ Circ (Tf f δ) circTop χ) (I0 : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (κ : Type) (_ : Fintype κ) (b : κ → ℝ) (W : κ → Set ℚ),
      LinearIndependent ℚ (fun j => Fa f (b j)) ∧
      (∀ a ∈ I0, ∃ q : κ → ℚ, ∀ x : ℝ, f (a * x) = ∑ j, q j * f (b j * x)) ∧
      (∀ j, W j ∈ @nhds ℚ δ 0) ∧
      ∀ x : ℝ, |x| < ε → (∀ j, f (b j * x) ∈ W j) → ‖χ x‖ < 1 / 4 := by
  classical
  obtain ⟨ε, hε, I, U, hU, hsm⟩ := tf_nhds_data f δ χ hχ
  obtain ⟨κ, hκ, b, hli, hq⟩ := indep_reduction f (I ∪ I0)
  have hq' : ∀ a : ℝ, ∃ q : κ → ℚ, a ∈ I ∪ I0 → ∀ x : ℝ, f (a * x) = ∑ j, q j * f (b j * x) := by
    intro a
    by_cases ha : a ∈ I ∪ I0
    · obtain ⟨q, hq⟩ := hq a ha
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose Q hQ using hq'
  obtain ⟨W, hW, hbox⟩ := pi_box δ hg hs I U hU Q
  refine ⟨ε, hε, κ, hκ, b, W, hli, fun a ha => ⟨Q a, hQ a (Finset.mem_union_right _ ha)⟩, hW, ?_⟩
  intro x hx hxW
  apply hsm x hx
  intro a ha
  rw [hQ a (Finset.mem_union_left _ ha) x]
  exact hbox (fun j => f (b j * x)) hxW a ha

end Reduction

/-! ### Part D: every `T_f(δ)`-continuous character is some `χ_{c,a}` -/

/-- `x ↦ p(c x)` as a homomorphism `ℝ →+ 𝕋`. -/
def cmulHom (c : ℝ) : ℝ →+ Circ where
  toFun x := ((c * x : ℝ) : Circ)
  map_zero' := by simp
  map_add' x y := by rw [mul_add, AddCircle.coe_add]

lemma cmulHom_apply (c x : ℝ) : cmulHom c x = ((c * x : ℝ) : Circ) := rfl

lemma cmulHom_continuous (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (c : ℝ) :
    @Continuous ℝ Circ (Tf f δ) circTop (cmulHom c) :=
  continuous_inf_dom_left (continuous_coe_circ.comp (continuous_const.mul continuous_id))

/-- **The dual of `T_f(δ)` is contained in `H_f`.** -/
theorem dual_Tf_mp (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (hg : @IsTopologicalAddGroup ℚ δ _)
    (hs : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x))
    (hdual : ∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ δ _ ψ →
      ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ))
    (χ : ℝ →+ Circ) (hχ : @Continuous ℝ Circ (Tf f δ) circTop χ) :
    ∃ c a : ℝ, ∀ x : ℝ, χ x = chiH f c a x := by
  classical
  -- Stage 1: linearize on the joint kernel
  obtain ⟨ε, hε, κ, hκ, b, W, hli, -, hW, hsm⟩ := packaged f δ hg hs χ hχ ∅
  have hsmall : ∀ x ∈ (Hmap f b).ker, |x| < ε → ‖χ x‖ < 1 / 4 := by
    intro x hx hxε
    apply hsm x hxε
    intro j
    have h0 : f (b j * x) = 0 := by
      have := congrFun (AddMonoidHom.mem_ker.mp hx) j
      simpa [Hmap_apply] using this
    rw [h0]; exact mem_of_mem_nhds (hW j)
  obtain ⟨c, hc⟩ := linearize χ (Hmap f b).ker ε hε (Hker_qmul f b) hsmall (Hker_dense f b)
  -- Stage 2: the remainder `χ' = χ - p(c ·)` kills the joint kernel
  let χ' : ℝ →+ Circ := χ + cmulHom (-c)
  have hχ'x : ∀ x, χ' x = χ x - ((c * x : ℝ) : Circ) := by
    intro x
    show χ x + ((-c * x : ℝ) : Circ) = _
    rw [neg_mul, AddCircle.coe_neg, sub_eq_add_neg]
  have hχ' : @Continuous ℝ Circ (Tf f δ) circTop χ' :=
    @Continuous.add Circ _ _ _ ℝ (Tf f δ) _ _ hχ (cmulHom_continuous f δ (-c))
  obtain ⟨ε', hε', κ', hκ', b', W', hli', hspan, hW', hsm'⟩ :=
    packaged f δ hg hs χ' hχ' (Finset.univ.image b)
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
  -- sections `xs j` with `H' (xs j) = e_j`
  choose xs hxs using fun j : κ' => Hmap_surj f b' hli' (Pi.single j (1 : ℚ))
  have hHx : ∀ (t : ℚ) (j i : κ'), Hmap f b' ((t : ℝ) * xs j) i = t * (Pi.single j (1 : ℚ) : κ' → ℚ) i := by
    intro t j i
    rw [Hmap_apply, mul_left_comm, f_ratmul, ← Hmap_apply, hxs j]
  -- the coordinate characters `θ_j`
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
    have := hsm' _ hy hHy
    have hχn : χ' ((t : ℝ) * xs j + n) = θ j t := by
      rw [map_add, hker0 n hnN, add_zero, hθ]
    rwa [hχn] at this
  choose r hr using fun j => hdual (θ j) (hθcont j)
  -- decomposition of `χ'`
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
  -- assemble `a = ∑ r_j b'_j`
  refine ⟨c, ∑ j, ((r j : ℚ) : ℝ) * b' j, fun x => ?_⟩
  have hfa : f ((∑ j, ((r j : ℚ) : ℝ) * b' j) * x) = ∑ j, r j * f (b' j * x) := by
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_assoc, f_ratmul]
  have h1 : χ x = χ' x + ((c * x : ℝ) : Circ) := by rw [hχ'x]; abel
  rw [h1, hdecomp]
  unfold chiH
  rw [hfa]
  let ψ0 : ℚ →+ Circ := (AddCommGroup.torsion Circ).subtype.comp piHom
  have hψ0 : ∀ s : ℚ, ψ0 s = ((s : ℝ) : Circ) := fun s => by simp [ψ0, piHom_coe]
  have e1 : ∑ j, θ j (f (b' j * x)) = (((∑ j, r j * f (b' j * x) : ℚ) : ℝ) : Circ) :=
    calc ∑ j, θ j (f (b' j * x)) = ∑ j, ψ0 (r j * f (b' j * x)) :=
          Finset.sum_congr rfl (fun j _ => by rw [hr j, hψ0])
      _ = ψ0 (∑ j, r j * f (b' j * x)) := (map_sum ψ0 _ _).symm
      _ = _ := hψ0 _
  rw [e1, AddCircle.coe_add, add_comm]

/-- **The dual of `T_f(δ)` is exactly `H_f`**, for `δ` a group topology on `ℚ` with all rational
multiplications continuous and dual exactly `Γ`. -/
theorem dual_Tf (f : ℝ →+ ℚ) (δ : TopologicalSpace ℚ) (hg : @IsTopologicalAddGroup ℚ δ _)
    (hs : ∀ s : ℚ, Continuous[δ, δ] (fun x : ℚ => s * x))
    (hdual : ∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ δ _ ψ ↔
      ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ))
    (χ : ℝ →+ Circ) :
    @Continuous ℝ Circ (Tf f δ) circTop χ ↔ ∃ c a : ℝ, ∀ x : ℝ, χ x = chiH f c a x := by
  constructor
  · exact dual_Tf_mp f δ hg hs (fun ψ hψ => (hdual ψ).mp hψ) χ
  · rintro ⟨c, a, h⟩
    have hp : @Continuous ℚ Circ δ _ (fun s : ℚ => ((s : ℝ) : Circ)) := by
      have := ((hdual ((AddCommGroup.torsion Circ).subtype.comp piHom)).mpr
        ⟨1, fun s => by simp [piHom_coe]⟩)
      exact this
    have : (χ : ℝ → Circ) = chiH f c a := funext h
    rw [this]
    exact chiH_continuous f δ hp c a

/-- `lift_capstone` together with rational scalar continuity of the lifted topologies. -/
theorem lift_capstone_scalar :
    ∃ (g1 g2 : TopologicalSpace ℚ),
      @IsTopologicalAddGroup ℚ g1 _ ∧ @IsTopologicalAddGroup ℚ g2 _ ∧
      (∀ s : ℚ, Continuous[g1, g1] (fun x : ℚ => s * x)) ∧
      (∀ s : ℚ, Continuous[g2, g2] (fun x : ℚ => s * x)) ∧
      (∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ g1 _ ψ ↔ ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ)) ∧
      (∀ ψ : ℚ →+ Circ, @Continuous ℚ Circ g2 _ ψ ↔ ∃ r : ℚ, ∀ s : ℚ, ψ s = (((r * s : ℚ) : ℝ) : Circ)) ∧
      ∃ ψ : ℚ →+ Circ, @Continuous ℚ Circ (g1 ⊓ g2) _ ψ ∧
        ∀ r : ℚ, ∃ s : ℚ, ψ s ≠ (((r * s : ℚ) : ℝ) : Circ) := by
  obtain ⟨M1, M2, ζ, h1, h2, ht1, ht2, hd1, hd2, hζ, hne⟩ := final_capstone
  have g1 := (basisOf (Set.range M1)).isTopologicalAddGroup
  have g2 := (basisOf (Set.range M2)).isTopologicalAddGroup
  obtain ⟨ψ, hψ, hψne⟩ := lift_incompatible (basisOf (Set.range M1)).topology
    (basisOf (Set.range M2)).topology ζ hζ hne
  exact ⟨gam (basisOf (Set.range M1)).topology, gam (basisOf (Set.range M2)).topology,
    gam_group _ g1, gam_group _ g2, gam_scalar _, gam_scalar _,
    dual_gam _ g1 hd1, dual_gam _ g2 hd2, ψ, hψ, hψne⟩

/-- **The transfer theorem, exact form.**  For every coefficient function `f` there are two Hausdorff TVG group
topologies on `ℝ`, finer than the usual one, each with continuous character group EXACTLY `H_f`, whose join
carries a continuous character outside `H_f`.  (Local quasi-convexity is not formalized.) -/
theorem transfer_capstone_exact (f : ℝ →+ ℚ) (u : ℝ) (hu : f u = 1) :
    ∃ T₁ T₂ : TopologicalSpace ℝ,
      @IsTopologicalAddGroup ℝ T₁ _ ∧ @IsTopologicalAddGroup ℝ T₂ _ ∧
      @T2Space ℝ T₁ ∧ @T2Space ℝ T₂ ∧
      T₁ ≤ uR ∧ T₂ ≤ uR ∧
      (∀ c : ℝ, Continuous[T₁, T₁] (fun x : ℝ => c * x)) ∧
      (∀ c : ℝ, Continuous[T₂, T₂] (fun x : ℝ => c * x)) ∧
      (∀ χ : ℝ →+ Circ, @Continuous ℝ Circ T₁ circTop χ ↔ ∃ c a : ℝ, ∀ x : ℝ, χ x = chiH f c a x) ∧
      (∀ χ : ℝ →+ Circ, @Continuous ℝ Circ T₂ circTop χ ↔ ∃ c a : ℝ, ∀ x : ℝ, χ x = chiH f c a x) ∧
      ∃ φ : ℝ →+ Circ, @Continuous ℝ Circ (T₁ ⊓ T₂) circTop φ ∧
        ¬ ∃ c a : ℝ, ∀ x : ℝ, φ x = chiH f c a x := by
  obtain ⟨g1, g2, hg1, hg2, hs1, hs2, hd1, hd2, ψ, hψ, hne⟩ := lift_capstone_scalar
  obtain ⟨φ, hφ, hφne⟩ := transfer_obstruction f u hu g1 g2 ψ hψ hne
  exact ⟨Tf f g1, Tf f g2, Tf_group f g1 hg1, Tf_group f g2 hg2, Tf_t2 f g1, Tf_t2 f g2,
    Tf_le_usual f g1, Tf_le_usual f g2, Tf_dilation f g1, Tf_dilation f g2,
    dual_Tf f g1 hg1 hs1 hd1, dual_Tf f g2 hg2 hs2 hd2, φ, hφ, hφne⟩

/-- Coefficient functions exist (Hamel; uses choice): an additive `f : ℝ → ℚ` with `f 1 = 1`. -/
theorem exists_coefficient : ∃ f : ℝ →+ ℚ, f 1 = 1 := by
  have h1 : (1 : ℝ) ∉ (⊥ : Submodule ℚ ℝ) := by
    simp
  obtain ⟨g, hg, -⟩ := Submodule.exists_le_ker_of_notMem h1
  refine ⟨((g 1)⁻¹ • g).toAddMonoidHom, ?_⟩
  simp [hg]

end LeanCheck
