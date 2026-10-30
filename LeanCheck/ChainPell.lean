import LeanCheck.ChainDuality

/-!
# The Pell sequence and sequence separation (TVGQ-v7, §"Sequence separation and its quantifiers")

`pz n = n! (3 - 2√2)^{n²} = n! (P_n - Q_n √2)` with `(3 + 2√2)^{n²} = P_n + Q_n √2`.

* `pell_scaled`   (Theorem `scaled-sequence`): for every nonzero `f` and nonzero `S` there is `y ≠ 0` such that
  `y · pz n → 0` in `σ_{f,S}` and `β_{f,S}` but not in `τ_{f,S}`, `|f(a₀ x_n)| → ∞`, and the set
  `{0, x₁, x₂, …}` is compact for `σ`, `β` and not compact for `τ`.
* `pell_criterion` (Theorem `pell-criterion`): `pz n → 0` in `σ` and `β` for every `f`; it fails to converge in `τ`
  iff `f` is nonzero on `S + √2 S`; hence it separates for all nonzero `f` iff `S + √2 S = ℝ`.
-/

namespace LeanCheck

open Filter Topology

/-! ### Pell numbers -/

/-- `(P_k, Q_k)` with `(3 + 2√2)^k = P_k + Q_k √2`. -/
def pq : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 => (3 * (pq k).1 + 4 * (pq k).2, 2 * (pq k).1 + 3 * (pq k).2)

def PP (k : ℕ) : ℤ := (pq k).1
def QQ (k : ℕ) : ℤ := (pq k).2

lemma sqrt2_sq : (Real.sqrt 2) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma pq_plus (k : ℕ) : (3 + 2 * Real.sqrt 2) ^ k = (PP k : ℝ) + (QQ k : ℝ) * Real.sqrt 2 := by
  induction k with
  | zero => simp [PP, QQ, pq]
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [PP, QQ, pq] at *
    push_cast
    linear_combination (2 * ((pq k).2 : ℝ)) * sqrt2_sq

lemma pq_minus (k : ℕ) : (3 - 2 * Real.sqrt 2) ^ k = (PP k : ℝ) - (QQ k : ℝ) * Real.sqrt 2 := by
  induction k with
  | zero => simp [PP, QQ, pq]
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [PP, QQ, pq] at *
    push_cast
    linear_combination (2 * ((pq k).2 : ℝ)) * sqrt2_sq

lemma pq_pos : ∀ k : ℕ, 1 ≤ PP k ∧ 0 ≤ QQ k := by
  intro k
  induction k with
  | zero => simp [PP, QQ, pq]
  | succ k ih =>
    simp only [PP, QQ, pq] at *
    omega

lemma QQ_ge_one {k : ℕ} (hk : 1 ≤ k) : 1 ≤ QQ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have := pq_pos j
  simp only [PP, QQ, pq] at *
  omega

/-- The unscaled Pell sequence `z_n = n! (3 - 2√2)^{n²}`. -/
noncomputable def pz (n : ℕ) : ℝ := (n.factorial : ℝ) * (3 - 2 * Real.sqrt 2) ^ (n ^ 2)

lemma pz_eq (n : ℕ) : pz n = (n.factorial : ℝ) * ((PP (n ^ 2) : ℝ) - (QQ (n ^ 2) : ℝ) * Real.sqrt 2) := by
  rw [pz, pq_minus]

lemma alpha_pos : 0 < 3 - 2 * Real.sqrt 2 := by
  have h : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

lemma alpha_lt : 3 - 2 * Real.sqrt 2 < 1 := by
  have : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

/-- `z_n → 0` in the usual topology. -/
theorem pz_tendsto_zero : Tendsto pz atTop (𝓝 0) := by
  set α : ℝ := 3 - 2 * Real.sqrt 2 with hα
  have hα0 := alpha_pos
  have hα1 := alpha_lt
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) * α ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hα0.le hα1
  have h2 : ∀ᶠ n : ℕ in atTop, (n : ℝ) * α ^ n ≤ 1 / 2 :=
    h1.eventually (ge_mem_nhds (by norm_num))
  have h3 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ h3
  · unfold pz; positivity
  · filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
    have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have hsq : α ^ (n ^ 2) = (α ^ n) ^ n := by rw [← pow_mul, sq]
    calc pz n = (n.factorial : ℝ) * α ^ (n ^ 2) := rfl
      _ ≤ (n : ℝ) ^ n * α ^ (n ^ 2) := by gcongr
      _ = ((n : ℝ) * α ^ n) ^ n := by rw [hsq, mul_pow]
      _ ≤ (1 / 2) ^ n := by gcongr

/-- `n! Q_{n²} → ∞`. -/
theorem qn_tendsto : Tendsto (fun n : ℕ => (n.factorial : ℝ) * (QQ (n ^ 2) : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono' atTop (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩) tendsto_natCast_atTop_atTop
  have h1 : (1 : ℝ) ≤ (QQ (n ^ 2) : ℝ) := by
    exact_mod_cast QQ_ge_one (Nat.one_le_pow _ _ hn)
  have h2 : (n : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial n
  nlinarith [Nat.cast_nonneg (α := ℝ) n.factorial]

/-! ### Convergence in the initial topologies -/

lemma tendsto_TfS_iff (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (δ : TopologicalSpace ℚ) (u : ℕ → ℝ) :
    Tendsto u atTop (@nhds ℝ (TfS f S δ) 0) ↔
      Tendsto u atTop (𝓝 0) ∧ ∀ a : S, Tendsto (fun n => fa f (a : ℝ) (u n)) atTop (@nhds ℚ δ 0) := by
  unfold TfS
  rw [@nhds_inf ℝ (show TopologicalSpace ℝ from inferInstance)
    (⨅ a : S, TopologicalSpace.induced (fa f (a : ℝ)) δ) 0, tendsto_inf, nhds_iInf, tendsto_iInf]
  refine and_congr Iff.rfl (forall_congr' fun a => ?_)
  rw [nhds_induced, tendsto_comap_iff]
  simp [Function.comp_def]

lemma tendsto_sigma_iff (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (u : ℕ → ℝ) :
    Tendsto u atTop (@nhds ℝ (sigmaT f S) 0) ↔
      Tendsto u atTop (𝓝 0) ∧ ∀ a : S,
        Tendsto (fun n => (((f ((a : ℝ) * u n) : ℚ) : ℝ) : Circ)) atTop (𝓝 0) := by
  rw [sigmaT_eq_A]
  rw [@nhds_inf ℝ (show TopologicalSpace ℝ from inferInstance)
    (⨅ a : S, TopologicalSpace.induced
      (fun x : ℝ => (((f ((a : ℝ) * x) : ℚ) : ℝ) : Circ)) circTop) 0, tendsto_inf, nhds_iInf, tendsto_iInf]
  refine and_congr Iff.rfl (forall_congr' fun a => ?_)
  rw [nhds_induced, tendsto_comap_iff]
  simp [Function.comp_def]
  rfl

lemma tendsto_tau_iff (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (u : ℕ → ℝ) :
    Tendsto u atTop (@nhds ℝ (tauT f S) 0) ↔
      Tendsto u atTop (𝓝 0) ∧ ∀ a : S, Tendsto (fun n => ((f ((a : ℝ) * u n) : ℚ) : ℝ)) atTop (𝓝 0) := by
  unfold tauT
  rw [tendsto_TfS_iff]
  refine and_congr Iff.rfl (forall_congr' fun a => ?_)
  unfold usualQ
  rw [Rat.isEmbedding_coe_real.isInducing.tendsto_nhds_iff]
  simp [Function.comp_def, fa_apply]

/-! ### The Pell computation -/

lemma g_pz (g : ℝ →+ ℚ) (t : ℝ) (n : ℕ) :
    g (t * pz n) = (n.factorial : ℚ) * ((PP (n ^ 2) : ℚ) * g t - (QQ (n ^ 2) : ℚ) * g (t * Real.sqrt 2)) := by
  have e : t * pz n = (((n.factorial : ℤ) * PP (n ^ 2) : ℤ)) • t +
      (-(((n.factorial : ℤ) * QQ (n ^ 2) : ℤ))) • (t * Real.sqrt 2) := by
    rw [pz_eq]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [e, map_add, map_zsmul, map_zsmul]
  simp only [zsmul_eq_mul]
  push_cast
  ring

lemma g_pz_real (g : ℝ →+ ℚ) (t : ℝ) (n : ℕ) :
    ((g (t * pz n) : ℚ) : ℝ) = (g t : ℝ) * pz n +
      ((n.factorial : ℝ) * (QQ (n ^ 2) : ℝ)) * (Real.sqrt 2 * (g t : ℝ) - (g (t * Real.sqrt 2) : ℝ)) := by
  rw [g_pz, pz_eq]
  push_cast
  ring

lemma g_pz_int (g : ℝ →+ ℚ) (t : ℝ) : ∃ N : ℕ, ∀ n ≥ N, ∃ m : ℤ, g (t * pz n) = m := by
  refine ⟨(g t).den * (g (t * Real.sqrt 2)).den, fun n hn => ?_⟩
  have hD : (g t).den * (g (t * Real.sqrt 2)).den ∣ n.factorial :=
    Nat.dvd_factorial (Nat.mul_pos (g t).den_pos (g (t * Real.sqrt 2)).den_pos) hn
  obtain ⟨k1, hk1⟩ := exists_k_of_den_dvd (g t) n.factorial
    (dvd_trans (Dvd.intro _ rfl) hD)
  obtain ⟨k2, hk2⟩ := exists_k_of_den_dvd (g (t * Real.sqrt 2)) n.factorial
    (dvd_trans (Dvd.intro_left _ rfl) hD)
  refine ⟨PP (n ^ 2) * k1 - QQ (n ^ 2) * k2, ?_⟩
  rw [g_pz]
  push_cast
  rw [← hk1, ← hk2]
  ring

lemma d_ne_zero (u v : ℚ) (h : u ≠ 0 ∨ v ≠ 0) : Real.sqrt 2 * (u : ℝ) - (v : ℝ) ≠ 0 := by
  intro hd
  rcases h with hu | hv
  · apply irrational_sqrt_two
    refine ⟨v / u, ?_⟩
    have hu' : (u : ℝ) ≠ 0 := by exact_mod_cast hu
    push_cast
    field_simp
    linarith
  · have : Real.sqrt 2 * (u : ℝ) = (v : ℝ) := by linarith
    by_cases hu : u = 0
    · subst hu; simp at this; exact hv (by exact_mod_cast this.symm)
    · apply irrational_sqrt_two
      refine ⟨v / u, ?_⟩
      have hu' : (u : ℝ) ≠ 0 := by exact_mod_cast hu
      push_cast
      field_simp
      linarith

/-- Divergence of the observation: `|g(t z_n)| → ∞` when `√2 g(t) - g(t√2) ≠ 0`. -/
lemma abs_g_pz_tendsto (g : ℝ →+ ℚ) (t : ℝ) (hd : Real.sqrt 2 * (g t : ℝ) - (g (t * Real.sqrt 2) : ℝ) ≠ 0) :
    Tendsto (fun n => |((g (t * pz n) : ℚ) : ℝ)|) atTop atTop := by
  set d : ℝ := Real.sqrt 2 * (g t : ℝ) - (g (t * Real.sqrt 2) : ℝ) with hdd
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have h1 : Tendsto (fun n : ℕ => ((n.factorial : ℝ) * (QQ (n ^ 2) : ℝ)) * |d|) atTop atTop :=
    qn_tendsto.atTop_mul_const hdpos
  have h2 : Tendsto (fun n : ℕ => ((n.factorial : ℝ) * (QQ (n ^ 2) : ℝ)) * |d| - |(g t : ℝ)| * 1)
      atTop atTop := tendsto_atTop_add_const_right _ _ h1
  have hz : Tendsto (fun n : ℕ => |(g t : ℝ)| * |pz n|) atTop (𝓝 0) := by
    have := (pz_tendsto_zero.abs).const_mul |(g t : ℝ)|
    simpa using this
  have hz1 : ∀ᶠ n : ℕ in atTop, |(g t : ℝ)| * |pz n| ≤ |(g t : ℝ)| * 1 := by
    have hzabs : ∀ᶠ n : ℕ in atTop, |pz n| ≤ 1 :=
      (pz_tendsto_zero.abs.eventually (ge_mem_nhds (by simp)))
    filter_upwards [hzabs] with n hn
    exact mul_le_mul_of_nonneg_left hn (abs_nonneg _)
  refine tendsto_atTop_mono' atTop ?_ h2
  filter_upwards [hz1] with n hn
  rw [g_pz_real]
  have e : (g t : ℝ) * pz n + ((n.factorial : ℝ) * (QQ (n ^ 2) : ℝ)) * d =
      (g t : ℝ) * pz n + ((n.factorial : ℝ) * (QQ (n ^ 2) : ℝ)) *
        (Real.sqrt 2 * (g t : ℝ) - (g (t * Real.sqrt 2) : ℝ)) := rfl
  rw [← e]
  have hq : 0 ≤ (n.factorial : ℝ) * (QQ (n ^ 2) : ℝ) := by
    have := pq_pos (n ^ 2)
    have h0 : (0 : ℝ) ≤ (QQ (n ^ 2) : ℝ) := by exact_mod_cast this.2
    positivity
  have h3 : |((n.factorial : ℝ) * (QQ (n ^ 2) : ℝ)) * d| = ((n.factorial : ℝ) * (QQ (n ^ 2) : ℝ)) * |d| := by
    rw [abs_mul, abs_of_nonneg hq]
  have h4 : |((n.factorial : ℝ) * (QQ (n ^ 2) : ℝ)) * d| - |(g t : ℝ) * pz n| ≤
      |(g t : ℝ) * pz n + ((n.factorial : ℝ) * (QQ (n ^ 2) : ℝ)) * d| := by
    have := abs_sub_abs_le_abs_sub (((n.factorial : ℝ) * (QQ (n ^ 2) : ℝ)) * d) (-((g t : ℝ) * pz n))
    rw [sub_neg_eq_add, abs_neg, add_comm] at this
    exact this
  rw [h3, abs_mul (g t : ℝ) (pz n)] at h4
  linarith

/-! ### Modular convergence and the Pell criterion -/

/-- `y · z_n → 0` in `σ_{f,S}` for every `y`. -/
theorem modular_conv (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (y : ℝ) :
    Tendsto (fun n => y * pz n) atTop (@nhds ℝ (sigmaT f S) 0) := by
  rw [tendsto_sigma_iff]
  refine ⟨by simpa using pz_tendsto_zero.const_mul y, fun a => ?_⟩
  obtain ⟨N, hN⟩ := g_pz_int f ((a : ℝ) * y)
  refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : Circ)))
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨m, hm⟩ := hN n hn
  have : (a : ℝ) * (y * pz n) = ((a : ℝ) * y) * pz n := by ring
  rw [this, hm]
  symm
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨m, by simp⟩

theorem modular_conv_beta (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) (y : ℝ) :
    Tendsto (fun n => y * pz n) atTop (@nhds ℝ (betaT f S) 0) :=
  (modular_conv f S y).mono_right (nhds_mono (sigmaT_le_betaT f S))

/-- **Theorem `pell-criterion`**: the unscaled Pell sequence converges to `0` in `σ_{f,S}` and `β_{f,S}` for every `f`;
it fails to converge in `τ_{f,S}` exactly when `f` is nonzero on `S + √2 S`. -/
theorem pell_criterion (f : ℝ →+ ℚ) (S : Submodule ℚ ℝ) :
    Tendsto pz atTop (@nhds ℝ (sigmaT f S) 0) ∧ Tendsto pz atTop (@nhds ℝ (betaT f S) 0) ∧
      (¬ Tendsto pz atTop (@nhds ℝ (tauT f S) 0) ↔
        ∃ a ∈ S, f a ≠ 0 ∨ f (a * Real.sqrt 2) ≠ 0) := by
  refine ⟨by simpa using modular_conv f S 1, by simpa using modular_conv_beta f S 1, ?_⟩
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    apply h
    rw [tendsto_tau_iff]
    refine ⟨pz_tendsto_zero, fun a => ?_⟩
    have hz : ∀ n, ((f ((a : ℝ) * pz n) : ℚ) : ℝ) = 0 := by
      intro n
      obtain ⟨h1, h2⟩ := hno a a.2
      rw [g_pz, h1, h2]; simp
    simp [hz]
  · rintro ⟨a, ha, hne⟩ hconv
    rw [tendsto_tau_iff] at hconv
    have h1 := hconv.2 ⟨a, ha⟩
    have h2 := abs_g_pz_tendsto f a (d_ne_zero (f a) (f (a * Real.sqrt 2)) (by
      rcases hne with h | h
      · exact Or.inl h
      · exact Or.inr h))
    exact not_tendsto_atTop_of_tendsto_nhds (by simpa using h1.abs) h2

/-- `S + √2 S`. -/
noncomputable def sumSqrt2 (S : Submodule ℚ ℝ) : Submodule ℚ ℝ :=
  S ⊔ S.map (LinearMap.mulLeft ℚ (Real.sqrt 2))

/-- **Separation for every nonzero `f`** iff `S + √2 S = ℝ`. -/
theorem pell_separates_iff (S : Submodule ℚ ℝ) :
    (∀ g : ℝ →+ ℚ, g ≠ 0 → ¬ Tendsto pz atTop (@nhds ℝ (tauT g S) 0)) ↔ sumSqrt2 S = ⊤ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top (sumSqrt2 S) (lt_top_iff_ne_top.mpr hne)
    let g : ℝ →+ ℚ := φ.toAddMonoidHom
    have hg0 : g ≠ 0 := by
      intro h0; apply hφ0; ext x; exact congrArg (fun m : ℝ →+ ℚ => m x) h0
    apply h g hg0
    have := (pell_criterion g S).2.2
    by_contra hnot
    obtain ⟨a, ha, hne'⟩ := this.1 hnot
    have h1 : g a = 0 := hφ (Submodule.mem_sup_left ha)
    have h2 : g (a * Real.sqrt 2) = 0 := hφ (Submodule.mem_sup_right
      ⟨a, ha, by simp [mul_comm]⟩)
    rcases hne' with h3 | h3 <;> contradiction
  · intro htop g hg
    apply (pell_criterion g S).2.2.2
    by_contra hno
    push_neg at hno
    apply hg
    ext x
    have hx : x ∈ sumSqrt2 S := by rw [htop]; trivial
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨s', hs', rfl⟩ := ht
    have h1 := (hno s hs).1
    have h2 := (hno s' hs').2
    simp only [LinearMap.mulLeft_apply] at *
    rw [map_add, h1, show Real.sqrt 2 * s' = s' * Real.sqrt 2 from mul_comm _ _, h2]
    simp

/-! ### Compactness of the sequence -/

lemma compact_of_tendsto' {X : Type} (t : TopologicalSpace X) (u : ℕ → X) (a : X)
    (h : Tendsto u atTop (@nhds X t a)) : @IsCompact X t (insert a (Set.range u)) := by
  letI := t
  exact h.isCompact_insert_range

lemma not_compact_of_cluster {X : Type} (t u : TopologicalSpace X) (hT2 : @T2Space X t) (hle : u ≤ t)
    (x : ℕ → X) (a : X) (hx : Tendsto x atTop (@nhds X t a)) (V : Set X) (hV : V ∈ @nhds X u a)
    (hev : ∀ᶠ n in atTop, x n ∉ V) : ¬ @IsCompact X u (insert a (Set.range x)) := by
  intro hK
  have hmap : Filter.map x atTop ≤ 𝓟 (insert a (Set.range x)) := by
    rw [le_principal_iff]
    exact Filter.mem_map.mpr (Eventually.of_forall fun n => Or.inr ⟨n, rfl⟩)
  obtain ⟨c, -, hc⟩ := @IsCompact.exists_mapClusterPt X u (insert a (Set.range x)) ℕ hK atTop _ x hmap
  have hc2 : @ClusterPt X u c (Filter.map x atTop) := hc
  have hc' : @ClusterPt X t c (Filter.map x atTop) := by
    unfold ClusterPt at hc2 ⊢
    exact Filter.NeBot.mono hc2 (inf_le_inf_right _ (@nhds_mono X u t c hle))
  have hca : c = a := by
    have : (@nhds X t c ⊓ @nhds X t a).NeBot := @ClusterPt.mono X t c _ _ hc' hx
    exact @eq_of_nhds_neBot X t hT2 _ _ this
  subst hca
  have h1 : Vᶜ ∈ Filter.map x atTop := hev
  have h2 : V ∩ Vᶜ ∈ @nhds X u c ⊓ Filter.map x atTop := Filter.inter_mem_inf hV h1
  rw [Set.inter_compl_self] at h2
  have hne : (@nhds X u c ⊓ Filter.map x atTop).NeBot := hc2
  exact hne.ne (Filter.empty_mem_iff_bot.mp h2)

/-- **Theorem `scaled-sequence`**: for every nonzero `f` and every nonzero `S` there is `y ≠ 0` such that
`x_n = y z_n` converges to `0` in `β_{f,S}` and `σ_{f,S}` but not in `τ_{f,S}`; some observation
`|f(a₀ x_n)|` tends to `∞`; and `{0, x₁, x₂, …}` is compact for `σ` and `β` but not for `τ`. -/
theorem pell_scaled (f : ℝ →+ ℚ) (hf : f ≠ 0) (S : Submodule ℚ ℝ) (hS : ∃ a ∈ S, a ≠ 0) :
    ∃ y : ℝ, y ≠ 0 ∧
      Tendsto (fun n => y * pz n) atTop (@nhds ℝ (sigmaT f S) 0) ∧
      Tendsto (fun n => y * pz n) atTop (@nhds ℝ (betaT f S) 0) ∧
      ¬ Tendsto (fun n => y * pz n) atTop (@nhds ℝ (tauT f S) 0) ∧
      (∃ a₀ ∈ S, Tendsto (fun n => |((f (a₀ * (y * pz n)) : ℚ) : ℝ)|) atTop atTop) ∧
      @IsCompact ℝ (sigmaT f S) (insert 0 (Set.range fun n => y * pz n)) ∧
      @IsCompact ℝ (betaT f S) (insert 0 (Set.range fun n => y * pz n)) ∧
      ¬ @IsCompact ℝ (tauT f S) (insert 0 (Set.range fun n => y * pz n)) := by
  obtain ⟨a₀, ha₀, ha₀ne⟩ := hS
  obtain ⟨x0, hx0⟩ : ∃ x0, f x0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hf (AddMonoidHom.ext hall)
  set y : ℝ := (((f x0)⁻¹ : ℚ) : ℝ) * x0 / a₀ with hy
  have hay : a₀ * y = (((f x0)⁻¹ : ℚ) : ℝ) * x0 := by rw [hy]; field_simp
  have hfy : f (a₀ * y) = 1 := by
    rw [hay, f_ratmul]; field_simp
  have hy0 : y ≠ 0 := by
    intro h; rw [h, mul_zero, map_zero] at hfy; exact zero_ne_one hfy
  have hdiv : Tendsto (fun n => |((f (a₀ * (y * pz n)) : ℚ) : ℝ)|) atTop atTop := by
    have e : ∀ n, a₀ * (y * pz n) = (a₀ * y) * pz n := fun n => by ring
    simp_rw [e]
    refine abs_g_pz_tendsto f (a₀ * y) ?_
    rw [hfy]
    exact d_ne_zero 1 (f (a₀ * y * Real.sqrt 2)) (Or.inl one_ne_zero) |> fun h => by
      simpa using h
  have hσ := modular_conv f S y
  have hnotτ : ¬ Tendsto (fun n => y * pz n) atTop (@nhds ℝ (tauT f S) 0) := by
    intro h
    rw [tendsto_tau_iff] at h
    have h1 := h.2 ⟨a₀, ha₀⟩
    exact not_tendsto_atTop_of_tendsto_nhds (by simpa using h1.abs) hdiv
  refine ⟨y, hy0, hσ, modular_conv_beta f S y, hnotτ, ⟨a₀, ha₀, hdiv⟩,
    compact_of_tendsto' _ _ _ hσ, compact_of_tendsto' _ _ _ (modular_conv_beta f S y), ?_⟩
  have hτle : tauT f S ≤ (inferInstance : TopologicalSpace ℝ) :=
    (tauT_le_sigmaT f S).trans (sigmaT_le_usual f S)
  have hcont := faR_cont_tau f S a₀ ha₀
  have hV : faR f a₀ ⁻¹' Metric.ball (0 : ℝ) 1 ∈ @nhds ℝ (tauT f S) 0 := by
    have := @Continuous.continuousAt ℝ ℝ (tauT f S) _ (faR f a₀) 0 hcont
    exact this (by simpa using Metric.ball_mem_nhds (0 : ℝ) one_pos)
  have hxusual : Tendsto (fun n => y * pz n) atTop (@nhds ℝ (show TopologicalSpace ℝ from inferInstance) 0) := by
    simpa using pz_tendsto_zero.const_mul y
  refine not_compact_of_cluster (show TopologicalSpace ℝ from inferInstance) (tauT f S)
    (show @T2Space ℝ (show TopologicalSpace ℝ from inferInstance) from inferInstance) hτle _ 0 hxusual _ hV ?_
  filter_upwards [tendsto_atTop.1 hdiv 1] with n hn hmem
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, faR_apply, Real.norm_eq_abs] at hmem
  linarith

end LeanCheck
