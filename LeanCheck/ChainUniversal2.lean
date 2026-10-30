import LeanCheck.ChainUniversal

/-!
# Sufficiency in `universal-complete` (TVGQ-v7)

If `S + θ₁S + ⋯ + θ_rS = ℝ` for irrational `θ_i`, the interleaved sequence of Diophantine approximants
`w_{i,n} = n!(p_{i,n} - q_{i,n} θ_i)` (with `q_{i,n} > n`, `|p_{i,n} - q_{i,n}θ_i| < 1/((n+1) n!)`) converges to `0` in
every `σ_{f,S}` and `β_{f,S}` and in no `τ_{f,S}` with `f ≠ 0`.  Combined with `universal_necessary` this proves
the complete criterion: a universal separating sequence exists iff finitely many `b_t` satisfy `∑ b_t S = ℝ`.
-/

namespace LeanCheck

open Filter Topology

/-! ### Diophantine approximation with large denominators -/

lemma exists_eps {θ : ℝ} (hθ : Irrational θ) (K : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, 1 ≤ k → k ≤ K → ∀ j : ℤ, ε ≤ |(k : ℝ) * θ - j| := by
  induction K with
  | zero => exact ⟨1, one_pos, fun k hk1 hk0 => by omega⟩
  | succ K ih =>
    obtain ⟨ε, hε, h⟩ := ih
    have hirr : Irrational (((K + 1 : ℕ) : ℝ) * θ) := hθ.natCast_mul (Nat.succ_ne_zero K)
    have hδ : 0 < |(((K + 1 : ℕ) : ℝ) * θ) - round (((K + 1 : ℕ) : ℝ) * θ)| :=
      abs_pos.mpr (sub_ne_zero.mpr (hirr.ne_int _))
    refine ⟨min ε |(((K + 1 : ℕ) : ℝ) * θ) - round (((K + 1 : ℕ) : ℝ) * θ)|, lt_min hε hδ, ?_⟩
    intro k hk1 hkK j
    by_cases hk : k ≤ K
    · exact (min_le_left _ _).trans (h k hk1 hk j)
    · have : k = K + 1 := by omega
      subst this
      exact (min_le_right _ _).trans (round_le _ j)

lemma approx_irr {θ : ℝ} (hθ : Irrational θ) (K : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ (p : ℤ) (q : ℕ), K < q ∧ |(p : ℝ) - q * θ| < η := by
  obtain ⟨ε, hε, h⟩ := exists_eps hθ K
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (lt_min hε hη)
  obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le θ (n := m + 1) (Nat.succ_pos m)
  lift k to ℕ using hk0.le
  have hbound : |((k : ℤ) : ℝ) * θ - j| < min ε η := by
    refine lt_of_le_of_lt hjk (lt_of_le_of_lt ?_ hm)
    push_cast
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  refine ⟨j, k, ?_, ?_⟩
  · by_contra hle
    push_neg at hle
    have hk1 : 1 ≤ k := by exact_mod_cast hk0
    have := h k hk1 hle j
    have h2 := lt_of_lt_of_le hbound (min_le_left _ _)
    push_cast at this h2
    linarith
  · have h3 := lt_of_lt_of_le hbound (min_le_right _ _)
    push_cast at h3
    rw [abs_sub_comm]
    exact h3

/-! ### Observation formulas -/

lemma obs_real (g : ℝ →+ ℚ) (t θ : ℝ) (n : ℕ) (p : ℤ) (q : ℕ) :
    ((g (t * ((n.factorial : ℝ) * ((p : ℝ) - q * θ))) : ℚ) : ℝ) =
      (g t : ℝ) * ((n.factorial : ℝ) * ((p : ℝ) - q * θ)) +
        ((n.factorial : ℝ) * q) * (θ * (g t : ℝ) - (g (t * θ) : ℝ)) := by
  have e : t * ((n.factorial : ℝ) * ((p : ℝ) - q * θ)) =
      (((n.factorial : ℤ) * p : ℤ)) • t + (-(((n.factorial : ℤ) * q : ℤ))) • (t * θ) := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [e, map_add, map_zsmul, map_zsmul]
  simp only [zsmul_eq_mul]
  push_cast
  ring

lemma obs_int (g : ℝ →+ ℚ) (t θ : ℝ) (n : ℕ) (p : ℤ) (q : ℕ)
    (h1 : (g t).den ∣ n.factorial) (h2 : (g (t * θ)).den ∣ n.factorial) :
    ∃ m : ℤ, g (t * ((n.factorial : ℝ) * ((p : ℝ) - q * θ))) = m := by
  obtain ⟨k1, hk1⟩ := exists_k_of_den_dvd (g t) n.factorial h1
  obtain ⟨k2, hk2⟩ := exists_k_of_den_dvd (g (t * θ)) n.factorial h2
  refine ⟨p * k1 - q * k2, ?_⟩
  have e : t * ((n.factorial : ℝ) * ((p : ℝ) - q * θ)) =
      (((n.factorial : ℤ) * p : ℤ)) • t + (-(((n.factorial : ℤ) * q : ℤ))) • (t * θ) := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [e, map_add, map_zsmul, map_zsmul]
  simp only [zsmul_eq_mul]
  push_cast
  rw [← hk1, ← hk2]
  ring

lemma d_ne_zero' {θ : ℝ} (hθ : Irrational θ) (u v : ℚ) (h : u ≠ 0 ∨ v ≠ 0) :
    θ * (u : ℝ) - (v : ℝ) ≠ 0 := by
  intro hd
  by_cases hu : u = 0
  · subst hu
    simp at hd
    rcases h with h | h
    · exact h rfl
    · exact h (by exact_mod_cast hd)
  · apply hθ
    refine ⟨v / u, ?_⟩
    have hu' : (u : ℝ) ≠ 0 := by exact_mod_cast hu
    push_cast
    field_simp
    linarith

lemma abs_obs_tendsto (g : ℝ →+ ℚ) (t θ : ℝ) (w qn : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (hq : Tendsto qn atTop atTop)
    (hform : ∀ n, ((g (t * w n) : ℚ) : ℝ) = (g t : ℝ) * w n + qn n * (θ * (g t : ℝ) - (g (t * θ) : ℝ)))
    (hd : θ * (g t : ℝ) - (g (t * θ) : ℝ) ≠ 0) :
    Tendsto (fun n => |((g (t * w n) : ℚ) : ℝ)|) atTop atTop := by
  set d : ℝ := θ * (g t : ℝ) - (g (t * θ) : ℝ) with hdd
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have h1 : Tendsto (fun n => qn n * |d|) atTop atTop := hq.atTop_mul_const hdpos
  have h2 : Tendsto (fun n => qn n * |d| - |(g t : ℝ)|) atTop atTop :=
    tendsto_atTop_add_const_right _ _ h1
  refine tendsto_atTop_mono' atTop ?_ h2
  filter_upwards [hq.eventually_ge_atTop 0] with n hn
  rw [hform n]
  have h3 : |qn n * d| = qn n * |d| := by rw [abs_mul, abs_of_nonneg hn]
  have h4 : |qn n * d| - |(g t : ℝ) * w n| ≤ |(g t : ℝ) * w n + qn n * d| := by
    have := abs_sub_abs_le_abs_sub (qn n * d) (-((g t : ℝ) * w n))
    rw [sub_neg_eq_add, abs_neg, add_comm] at this
    exact this
  rw [h3, abs_mul (g t : ℝ) (w n)] at h4
  have h5 : |(g t : ℝ)| * |w n| ≤ |(g t : ℝ)| := by
    calc |(g t : ℝ)| * |w n| ≤ |(g t : ℝ)| * 1 := mul_le_mul_of_nonneg_left (hw n) (abs_nonneg _)
      _ = |(g t : ℝ)| := mul_one _
  linarith

/-! ### The interleaved sequence -/

lemma cover_nonzero (S : Submodule ℚ ℝ) {r : ℕ} (hr : 0 < r) (θ : Fin r → ℝ)
    (hcov : S ⊔ (⨆ i, S.map (LinearMap.mulLeft ℚ (θ i))) = ⊤) (f : ℝ →+ ℚ) (hf : f ≠ 0) :
    ∃ a ∈ S, ∃ i : Fin r, f a ≠ 0 ∨ f (a * θ i) ≠ 0 := by
  by_contra hno
  push_neg at hno
  apply hf
  ext z
  have hz : z ∈ S ⊔ (⨆ i, S.map (LinearMap.mulLeft ℚ (θ i))) := by rw [hcov]; trivial
  obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp hz
  have hu0 : f u = 0 := by
    refine Submodule.iSup_induction (fun i => S.map (LinearMap.mulLeft ℚ (θ i)))
      (motive := fun z => f z = 0) hu (fun i y hy => ?_) (by simp) (fun y y' hy hy' => by
        rw [map_add, hy, hy', add_zero])
    obtain ⟨s', hs', rfl⟩ := hy
    have := (hno s' hs' i).2
    simpa [mul_comm] using this
  have hs0 : f s = 0 := (hno s hs ⟨0, hr⟩).1
  rw [map_add, hs0, hu0]; simp

theorem universal_sufficient (S : Submodule ℚ ℝ) {r : ℕ} (hr : 0 < r) (θ : Fin r → ℝ)
    (hθ : ∀ i, Irrational (θ i))
    (hcov : S ⊔ (⨆ i, S.map (LinearMap.mulLeft ℚ (θ i))) = ⊤) :
    ∃ x : ℕ → ℝ, ∀ f : ℝ →+ ℚ, f ≠ 0 →
      Tendsto x atTop (@nhds ℝ (sigmaT f S) 0) ∧ Tendsto x atTop (@nhds ℝ (betaT f S) 0) ∧
      ¬ Tendsto x atTop (@nhds ℝ (tauT f S) 0) := by
  classical
  have hch : ∀ (i : Fin r) (n : ℕ), ∃ pq : ℤ × ℕ, n < pq.2 ∧
      |(pq.1 : ℝ) - pq.2 * θ i| < 1 / (((n : ℝ) + 1) * n.factorial) := by
    intro i n
    obtain ⟨p, q, h1, h2⟩ := approx_irr (hθ i) n
      (η := 1 / (((n : ℝ) + 1) * n.factorial)) (by positivity)
    exact ⟨(p, q), h1, h2⟩
  choose pq hpq1 hpq2 using hch
  let w : Fin r → ℕ → ℝ := fun i n =>
    (n.factorial : ℝ) * (((pq i n).1 : ℝ) - (pq i n).2 * θ i)
  have hw : ∀ i n, |w i n| ≤ 1 / ((n : ℝ) + 1) := by
    intro i n
    have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    simp only [w]
    rw [abs_mul, abs_of_pos hfpos]
    calc (n.factorial : ℝ) * |((pq i n).1 : ℝ) - (pq i n).2 * θ i|
        ≤ (n.factorial : ℝ) * (1 / (((n : ℝ) + 1) * n.factorial)) :=
          mul_le_mul_of_nonneg_left (hpq2 i n).le hfpos.le
      _ = 1 / ((n : ℝ) + 1) := by field_simp
  let x : ℕ → ℝ := fun k => w ⟨k % r, Nat.mod_lt k hr⟩ (k / r)
  have hdiv : Tendsto (fun k : ℕ => k / r) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨b * r, fun k hk => ?_⟩
    exact (Nat.le_div_iff_mul_le hr).2 hk
  have hxnull : Tendsto x atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => 1 / (((k / r : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hdiv
    exact squeeze_zero_norm (fun k => by simpa [x, Real.norm_eq_abs] using hw _ (k / r)) h1
  refine ⟨x, fun f hf => ?_⟩
  have hσ : Tendsto x atTop (@nhds ℝ (sigmaT f S) 0) := by
    rw [tendsto_sigma_iff]
    refine ⟨hxnull, fun a => ?_⟩
    set D : ℕ := (f (a : ℝ)).den * ∏ i : Fin r, (f ((a : ℝ) * θ i)).den with hD
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : Circ)))
    filter_upwards [eventually_ge_atTop (r * D)] with k hk
    have hn : D ≤ k / r := (Nat.le_div_iff_mul_le hr).2 (by rw [mul_comm]; exact hk)
    have hDpos : 0 < D := Nat.mul_pos (f a).den_pos
      (Finset.prod_pos fun i _ => (f ((a : ℝ) * θ i)).den_pos)
    have hdD : D ∣ (k / r).factorial := Nat.dvd_factorial hDpos hn
    have h1 : (f (a : ℝ)).den ∣ (k / r).factorial := dvd_trans (Dvd.intro _ rfl) hdD
    have h2 : (f ((a : ℝ) * θ ⟨k % r, Nat.mod_lt k hr⟩)).den ∣ (k / r).factorial :=
      dvd_trans (dvd_trans (Finset.dvd_prod_of_mem (fun i : Fin r => (f ((a : ℝ) * θ i)).den)
        (Finset.mem_univ (⟨k % r, Nat.mod_lt k hr⟩ : Fin r))) (Dvd.intro_left _ rfl)) hdD
    obtain ⟨m, hm⟩ := obs_int f (a : ℝ) (θ ⟨k % r, Nat.mod_lt k hr⟩) (k / r)
      (pq ⟨k % r, Nat.mod_lt k hr⟩ (k / r)).1 (pq ⟨k % r, Nat.mod_lt k hr⟩ (k / r)).2 h1 h2
    show (0 : Circ) = (((f ((a : ℝ) * x k) : ℚ) : ℝ) : Circ)
    simp only [x, w]
    rw [hm]
    symm
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨m, by simp⟩
  refine ⟨hσ, hσ.mono_right (nhds_mono (sigmaT_le_betaT f S)), ?_⟩
  intro hτ
  rw [tendsto_tau_iff] at hτ
  obtain ⟨a, ha, i, hne⟩ := cover_nonzero S hr θ hcov f hf
  have h1 := hτ.2 ⟨a, ha⟩
  -- the subsequence `k = r n + i`
  have hsub : Tendsto (fun n : ℕ => r * n + (i : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      have := Nat.le_mul_of_pos_left n hr
      simp only [id]; omega) tendsto_id
  have hxi : ∀ n, x (r * n + (i : ℕ)) = w i n := by
    intro n
    have hmod : (r * n + (i : ℕ)) % r = i := by
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt i.2
    have hdivn : (r * n + (i : ℕ)) / r = n := by
      rw [Nat.mul_add_div hr, Nat.div_eq_of_lt i.2, add_zero]
    simp only [x]
    have : (⟨(r * n + (i : ℕ)) % r, Nat.mod_lt _ hr⟩ : Fin r) = i := Fin.ext hmod
    rw [this, hdivn]
  have h2 := h1.comp hsub
  have hq : Tendsto (fun n : ℕ => (n.factorial : ℝ) * (pq i n).2) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have h3 : (n : ℝ) < (pq i n).2 := by exact_mod_cast hpq1 i n
    have h4 : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
    have h5 : (n : ℝ) ≤ n.factorial := by exact_mod_cast Nat.self_le_factorial n
    nlinarith [Nat.cast_nonneg (α := ℝ) (pq i n).2]
  have h6 := abs_obs_tendsto f a (θ i) (fun n => w i n) (fun n => (n.factorial : ℝ) * (pq i n).2)
    (fun n => (hw i n).trans (by
      rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n])) hq
    (fun n => obs_real f a (θ i) n (pq i n).1 (pq i n).2)
    (d_ne_zero' (hθ i) (f a) (f (a * θ i)) hne)
  have h7 : Tendsto (fun n => |((f ((a : ℝ) * x (r * n + (i : ℕ))) : ℚ) : ℝ)|) atTop (𝓝 0) := by
    simpa using h2.abs
  simp only [hxi] at h7
  exact not_tendsto_atTop_of_tendsto_nhds h7 h6

/-! ### The complete criterion -/

/-- From `∑_{t∈T} t S = ℝ` extract finitely many irrationals `θ_i` with `S + ∑ θ_i S = ℝ`
(rational ratios `t/t₀` only contribute elements of `S`; `√2` is added so the list is nonempty). -/
lemma reduce_irrational (S : Submodule ℚ ℝ) (T : Finset ℝ)
    (hT : (⨆ t : T, S.map (LinearMap.mulLeft ℚ (t : ℝ))) = ⊤) :
    ∃ (r : ℕ) (hr : 0 < r) (θ : Fin r → ℝ), (∀ i, Irrational (θ i)) ∧
      S ⊔ (⨆ i, S.map (LinearMap.mulLeft ℚ (θ i))) = ⊤ := by
  classical
  -- a nonzero element of `T`
  obtain ⟨t0, ht0, ht0ne⟩ : ∃ t0 ∈ T, t0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    have : (⨆ t : T, S.map (LinearMap.mulLeft ℚ (t : ℝ))) = ⊥ := by
      refine iSup_eq_bot.2 fun t => ?_
      have : (t : ℝ) = 0 := hall t t.2
      rw [this]
      ext y; simp
    rw [hT] at this
    exact top_ne_bot this
  let Θ : Finset ℝ := insert (Real.sqrt 2) ((T.image (fun t => t / t0)).filter Irrational)
  have hΘpos : 0 < Θ.card := Finset.card_pos.2 ⟨_, Finset.mem_insert_self _ _⟩
  let θ : Fin Θ.card → ℝ := fun i => (Θ.equivFin.symm i : ℝ)
  have hθΘ : ∀ i, θ i ∈ Θ := fun i => (Θ.equivFin.symm i).2
  have hirr : ∀ i, Irrational (θ i) := by
    intro i
    rcases Finset.mem_insert.1 (hθΘ i) with h | h
    · rw [h]; exact irrational_sqrt_two
    · exact (Finset.mem_filter.1 h).2
  refine ⟨Θ.card, hΘpos, θ, hirr, ?_⟩
  set R : Submodule ℚ ℝ := S ⊔ (⨆ i, S.map (LinearMap.mulLeft ℚ (θ i))) with hR
  rw [eq_top_iff]
  intro w _
  have hw : t0 * w ∈ (⨆ t : T, S.map (LinearMap.mulLeft ℚ (t : ℝ))) := by rw [hT]; trivial
  have key : (fun z : ℝ => t0⁻¹ * z ∈ R) (t0 * w) := by
    refine Submodule.iSup_induction (fun t : T => S.map (LinearMap.mulLeft ℚ (t : ℝ)))
      (motive := fun z => t0⁻¹ * z ∈ R) hw (fun t y hy => ?_) (by simp) (fun y y' hy hy' => by
        rw [mul_add]; exact R.add_mem hy hy')
    obtain ⟨s, hs, rfl⟩ := hy
    have e : t0⁻¹ * ((LinearMap.mulLeft ℚ (t : ℝ)) s) = ((t : ℝ) / t0) * s := by
      simp [LinearMap.mulLeft_apply]; field_simp
    rw [e]
    by_cases hrat : Irrational ((t : ℝ) / t0)
    · have hmem : (t : ℝ) / t0 ∈ Θ := Finset.mem_insert_of_mem
        (Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨t, t.2, rfl⟩, hrat⟩)
      obtain ⟨i, hi⟩ : ∃ i, θ i = (t : ℝ) / t0 := by
        refine ⟨Θ.equivFin ⟨(t : ℝ) / t0, hmem⟩, ?_⟩
        simp [θ]
      refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i ⟨s, hs, ?_⟩)
      simp [LinearMap.mulLeft_apply, hi]
    · rw [Irrational, not_not] at hrat
      obtain ⟨q, hq⟩ := hrat
      refine Submodule.mem_sup_left ?_
      have : ((t : ℝ) / t0) * s = q • s := by rw [← hq, Rat.smul_def]
      rw [this]; exact S.smul_mem q hs
  have : w = t0⁻¹ * (t0 * w) := by field_simp
  rw [this]
  exact key

/-- **Theorem `universal-complete`.** For a nonzero rational subspace `S ⊆ ℝ`: there is a single sequence that converges
to `0` in `σ_{f,S}` and does not converge in `τ_{f,S}` for every nonzero `f : ℝ →+ ℚ` iff finitely many reals
`b_t` satisfy `∑ b_t S = ℝ`. -/
theorem universal_complete (S : Submodule ℚ ℝ) (hS : ∃ a ∈ S, a ≠ 0) :
    (∃ x : ℕ → ℝ, ∀ g : ℝ →+ ℚ, g ≠ 0 →
      Tendsto x atTop (@nhds ℝ (sigmaT g S) 0) ∧ ¬ Tendsto x atTop (@nhds ℝ (tauT g S) 0)) ↔
    ∃ T : Finset ℝ, (⨆ t : T, S.map (LinearMap.mulLeft ℚ (t : ℝ))) = ⊤ := by
  constructor
  · rintro ⟨x, hx⟩
    exact universal_necessary S hS x hx
  · rintro ⟨T, hT⟩
    obtain ⟨r, hr, θ, hθ, hcov⟩ := reduce_irrational S T hT
    obtain ⟨x, hx⟩ := universal_sufficient S hr θ hθ hcov
    exact ⟨x, fun g hg => ⟨(hx g hg).1, (hx g hg).2.2⟩⟩

/-- The sequence furnished in the sufficient direction also converges in every `β_{f,S}`. -/
theorem universal_complete_beta (S : Submodule ℚ ℝ) (T : Finset ℝ)
    (hT : (⨆ t : T, S.map (LinearMap.mulLeft ℚ (t : ℝ))) = ⊤) :
    ∃ x : ℕ → ℝ, ∀ g : ℝ →+ ℚ, g ≠ 0 →
      Tendsto x atTop (@nhds ℝ (sigmaT g S) 0) ∧ Tendsto x atTop (@nhds ℝ (betaT g S) 0) ∧
        ¬ Tendsto x atTop (@nhds ℝ (tauT g S) 0) := by
  obtain ⟨r, hr, θ, hθ, hcov⟩ := reduce_irrational S T hT
  exact universal_sufficient S hr θ hθ hcov

/-- Subspaces of finite rational codimension (in particular `S = ℝ`) always admit a universal separating
sequence (Corollary `field-universal`, finite-codimension part). -/
theorem finite_codim_universal (S : Submodule ℚ ℝ) (hS : ∃ a ∈ S, a ≠ 0)
    (hfin : Module.Finite ℚ (ℝ ⧸ S)) :
    ∃ x : ℕ → ℝ, ∀ g : ℝ →+ ℚ, g ≠ 0 →
      Tendsto x atTop (@nhds ℝ (sigmaT g S) 0) ∧ ¬ Tendsto x atTop (@nhds ℝ (tauT g S) 0) := by
  classical
  obtain ⟨s0, hs0, hs0ne⟩ := hS
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl S
  haveI : Module.Finite ℚ Q := Module.Finite.equiv (Submodule.quotientEquivOfIsCompl S Q hQ)
  obtain ⟨R, hR⟩ := (Submodule.fg_iff_finiteDimensional Q).2 (inferInstance : FiniteDimensional ℚ Q)
  let T : Finset ℝ := insert 1 (R.image (fun r => r / s0))
  have hT : (⨆ t : T, S.map (LinearMap.mulLeft ℚ (t : ℝ))) = ⊤ := by
    have hspan : ∀ z ∈ Submodule.span ℚ (R : Set ℝ), z ∈ (⨆ t : T, S.map (LinearMap.mulLeft ℚ (t : ℝ))) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem r hr =>
        refine Submodule.mem_iSup_of_mem
          (⟨r / s0, Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨r, hr, rfl⟩)⟩ : T) ⟨s0, hs0, ?_⟩
        simp [LinearMap.mulLeft_apply]; field_simp
      | zero => exact Submodule.zero_mem _
      | add u u' _ _ hu hu' => exact Submodule.add_mem _ hu hu'
      | smul c u _ hu => exact Submodule.smul_mem _ c hu
    rw [eq_top_iff]
    intro w _
    obtain ⟨s, hs, q, hq, rfl⟩ := Submodule.mem_sup.mp (hQ.sup_eq_top ▸ (Submodule.mem_top : w ∈ (⊤ : Submodule ℚ ℝ)))
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_iSup_of_mem (⟨1, Finset.mem_insert_self _ _⟩ : T) ⟨s, hs, by simp⟩
    · exact hspan q (by rw [hR]; exact hq)
  exact (universal_complete S ⟨s0, hs0, hs0ne⟩).2 ⟨T, hT⟩

end LeanCheck
