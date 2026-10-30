import LeanCheck.ChainU1

/-!
# Sequences in a finite rational span
(HamelCharactersTVG_v18 Theorem 14.6 `thm:finite-span-sequences`, Corollary 14.7)

For rationally independent reals `b_1, …, b_m` and a nonzero rational-valued additive `f`, the sequence
`x_n = ∑_j q_{n,j} b_j` (`q_{n,j} ∈ ℚ`) satisfies
* `x_n → 0` in `τ_f` iff `q_{n,j} → 0` usually for each `j`;
* `x_n → 0` in `σ_f` (equivalently in `β_f`) iff `x_n → 0` usually and `‖q_{n,j}/d‖_𝕋 → 0` for all `j` and `d ≥ 1`.
-/

namespace LeanCheck

open Filter Topology

section FiniteSpan

variable {m : ℕ}

/-- The map `a ↦ (f(a b_j))_j` is onto `ℚ^m` for rationally independent `b_j`. -/
lemma finite_span_onto (f : ℝ →+ ℚ) (hf : f ≠ 0) (b : Fin m → ℝ) (hb : LinearIndependent ℚ b)
    (v : Fin m → ℚ) : ∃ a : ℝ, ∀ j, f (a * b j) = v j := by
  classical
  let φ : ℝ →ₗ[ℚ] (Fin m → ℚ) :=
    LinearMap.pi (fun j => (AddMonoidHom.toRatLinearMap f).comp (LinearMap.mulRight ℚ (b j)))
  have hφ : ∀ a j, φ a j = f (a * b j) := fun a j => rfl
  have hrange : LinearMap.range φ = ⊤ := by
    by_contra hne
    obtain ⟨ψ, hψ0, hψ⟩ := Submodule.exists_le_ker_of_lt_top (LinearMap.range φ) (lt_top_iff_ne_top.2 hne)
    set r : Fin m → ℚ := fun j => ψ (Pi.single j 1) with hr
    have hψr : ∀ w : Fin m → ℚ, ψ w = ∑ j, r j * w j := by
      intro w
      have : w = ∑ j, w j • (Pi.single j 1 : Fin m → ℚ) := by
        ext i; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [this]
      simp [map_sum, map_smul, hr, mul_comm]
    have hr0 : r ≠ 0 := by
      intro h0
      apply hψ0
      ext w
      simp [hψr, h0]
    have hzero : ∀ a : ℝ, ∑ j, r j * f (a * b j) = 0 := fun a => by
      have := hψ (LinearMap.mem_range_self φ a)
      rw [LinearMap.mem_ker, hψr] at this
      simpa [hφ] using this
    set w : ℝ := ∑ j, (r j : ℝ) * b j with hw
    have hw0 : w ≠ 0 := by
      intro h0
      have := Fintype.linearIndependent_iff.1 hb r (by
        rw [← h0, hw]; simp [Rat.smul_def])
      exact hr0 (funext this)
    have hfw : ∀ y : ℝ, f y = 0 := by
      intro y
      have e : y = (y / w) * w := by field_simp
      have h1 : f ((y / w) * w) = ∑ j, r j * f ((y / w) * b j) := by
        rw [hw, Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [show (y / w) * ((r j : ℝ) * b j) = (r j : ℝ) * ((y / w) * b j) by ring, f_ratmul]
      rw [e, h1]
      exact hzero (y / w)
    exact hf (AddMonoidHom.ext hfw)
  obtain ⟨a, ha⟩ := LinearMap.range_eq_top.1 hrange v
  exact ⟨a, fun j => by rw [← hφ a j, ha]⟩

lemma coe_circ_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    ((∑ i ∈ s, g i : ℝ) : Circ) = ∑ i ∈ s, ((g i : ℝ) : Circ) :=
  map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) g s

/-- `f` applied to a rational combination. -/
lemma f_combo (f : ℝ →+ ℚ) (b : Fin m → ℝ) (q : Fin m → ℚ) (a : ℝ) :
    f (a * ∑ j, ((q j : ℚ) : ℝ) * b j) = ∑ j, q j * f (a * b j) := by
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show a * ((q j : ℝ) * b j) = (q j : ℝ) * (a * b j) by ring, f_ratmul]

/-- **Theorem 14.6, `τ_f`.** -/
theorem finite_span_tau (f : ℝ →+ ℚ) (hf : f ≠ 0) (b : Fin m → ℝ) (hb : LinearIndependent ℚ b)
    (q : ℕ → Fin m → ℚ) :
    Tendsto (fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j) atTop (@nhds ℝ (tauT f ⊤) 0) ↔
      ∀ j, Tendsto (fun n => ((q n j : ℚ) : ℝ)) atTop (𝓝 0) := by
  have key := conv_tau_iff f (fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j) 0
  simp only [sub_zero] at key
  rw [key]
  constructor
  · rintro ⟨-, hall⟩ j
    obtain ⟨a, ha⟩ := finite_span_onto f hf b hb (Pi.single j 1)
    have := hall a
    simp_rw [f_combo f b (q _) a, ha] at this
    simpa [Pi.single_apply] using this
  · intro h
    refine ⟨?_, fun a => ?_⟩
    · have : Tendsto (fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j) atTop (𝓝 (∑ j : Fin m, (0 : ℝ) * b j)) :=
        tendsto_finset_sum _ (fun j _ => (h j).mul_const (b j))
      simpa using this
    · simp_rw [f_combo f b (q _) a]
      have : Tendsto (fun n => ∑ j, ((q n j : ℚ) : ℝ) * ((f (a * b j) : ℚ) : ℝ)) atTop
          (𝓝 (∑ j : Fin m, (0 : ℝ) * ((f (a * b j) : ℚ) : ℝ))) :=
        tendsto_finset_sum _ (fun j _ => (h j).mul_const _)
      simpa using this

/-- **Theorem 14.6, `σ_f`.** -/
theorem finite_span_sigma (f : ℝ →+ ℚ) (hf : f ≠ 0) (b : Fin m → ℝ) (hb : LinearIndependent ℚ b)
    (q : ℕ → Fin m → ℚ) :
    Tendsto (fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j) atTop (@nhds ℝ (sigmaT f ⊤) 0) ↔
      Tendsto (fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j) atTop (𝓝 0) ∧
      ∀ j, ∀ d : ℕ, 1 ≤ d → Tendsto (fun n => (((q n j / d : ℚ) : ℝ) : Circ)) atTop (𝓝 0) := by
  have key := conv_sigma_iff f (fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j) 0
  simp only [sub_zero] at key
  rw [key]
  refine and_congr Iff.rfl ⟨fun hall j d hd => ?_, fun h a => ?_⟩
  · have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    obtain ⟨a, ha⟩ := finite_span_onto f hf b hb (Pi.single j (1 / (d : ℚ)))
    have := hall a
    have e : ∀ n, f (a * ∑ k, ((q n k : ℚ) : ℝ) * b k) = q n j / d := fun n => by
      rw [f_combo f b (q n) a]
      simp_rw [ha]
      rw [Finset.sum_eq_single j]
      · simp [div_eq_mul_inv]
      · intro k _ hk; simp [Pi.single_apply, hk]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    simpa only [e] using this
  · show Tendsto (fun n => (((f (a * ∑ j, ((q n j : ℚ) : ℝ) * b j) : ℚ) : ℝ) : Circ)) atTop (𝓝 0)
    -- common denominator `D` of the rationals `r_k = f (a b_k)`
    set r : Fin m → ℚ := fun k => f (a * b k) with hr
    set D : ℕ := ∏ k, (r k).den with hD
    have hDpos : 1 ≤ D := Finset.prod_pos (fun k _ => (r k).den_pos)
    have hrD : ∀ k, ∃ z : ℤ, r k = z / D := fun k => by
      have hdvd : (r k).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
      obtain ⟨c, hc⟩ := hdvd
      have hc0 : (c : ℚ) ≠ 0 := by
        have : c ≠ 0 := by
          rintro rfl
          simp at hc
          exact (Finset.prod_pos (fun k _ => (r k).den_pos) : 0 < D).ne' hc
        exact_mod_cast this
      refine ⟨(r k).num * c, ?_⟩
      rw [hc]
      push_cast
      rw [mul_div_mul_right _ _ hc0]
      exact (Rat.num_div_den (r k)).symm
    choose z hz using hrD
    have hterm : ∀ n, (((f (a * ∑ j, ((q n j : ℚ) : ℝ) * b j) : ℚ) : ℝ) : Circ) =
        ∑ k, z k • (((q n k / D : ℚ) : ℝ) : Circ) := fun n => by
      rw [f_combo f b (q n) a, Rat.cast_sum, coe_circ_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [zsmul_coe_circ]
      congr 1
      have e : ((r k : ℚ) : ℝ) = (z k : ℝ) / (D : ℝ) := by
        rw [hz k]; push_cast; rfl
      rw [Rat.cast_mul, show ((f (a * b k) : ℚ) : ℝ) = ((r k : ℚ) : ℝ) from rfl, e]
      push_cast
      ring
    have : Tendsto (fun n => ∑ k, z k • (((q n k / D : ℚ) : ℝ) : Circ)) atTop
        (𝓝 (∑ k : Fin m, z k • (0 : Circ))) :=
      tendsto_finset_sum _ (fun k _ => (h k D hDpos).const_smul (z k))
    simp only [smul_zero, Finset.sum_const_zero] at this
    simpa only [hterm] using this

/-- **Theorem 14.6, `β_f`** (the same as `σ_f`). -/
theorem finite_span_beta (f : ℝ →+ ℚ) (hf : f ≠ 0) (b : Fin m → ℝ) (hb : LinearIndependent ℚ b)
    (q : ℕ → Fin m → ℚ) :
    Tendsto (fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j) atTop (@nhds ℝ (betaT f ⊤) 0) ↔
      Tendsto (fun n => ∑ j, ((q n j : ℚ) : ℝ) * b j) atTop (𝓝 0) ∧
      ∀ j, ∀ d : ℕ, 1 ≤ d → Tendsto (fun n => (((q n j / d : ℚ) : ℝ) : Circ)) atTop (𝓝 0) := by
  rw [beta_null_iff_sigma_null]
  exact finite_span_sigma f hf b hb q

/-- **Corollary 14.7, dimension one**: a sequence in a one-dimensional rational subspace that tends to zero
in `σ_f` also tends to zero in `τ_f`. -/
theorem one_dim_no_separation (f : ℝ →+ ℚ) (hf : f ≠ 0) (b : ℝ) (hb : b ≠ 0) (q : ℕ → ℚ)
    (h : Tendsto (fun n => ((q n : ℚ) : ℝ) * b) atTop (@nhds ℝ (sigmaT f ⊤) 0)) :
    Tendsto (fun n => ((q n : ℚ) : ℝ) * b) atTop (@nhds ℝ (tauT f ⊤) 0) := by
  have hb1 : LinearIndependent ℚ (fun _ : Fin 1 => b) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    fin_cases j
    simp at hg
    rcases hg with hg | hg
    · exact hg
    · exact absurd hg hb
  have h1 := (finite_span_sigma f hf (fun _ : Fin 1 => b) hb1 (fun n _ => q n)).1 (by simpa using h)
  have hu : Tendsto (fun n => ((q n : ℚ) : ℝ)) atTop (𝓝 0) := by
    have := h1.1
    simp at this
    have h2 : Tendsto (fun n => ((q n : ℚ) : ℝ) * b * b⁻¹) atTop (𝓝 (0 * b⁻¹)) := this.mul_const _
    simpa [hb] using h2
  have := (finite_span_tau f hf (fun _ : Fin 1 => b) hb1 (fun n _ => q n)).2 (fun _ => hu)
  simpa using this

/-- **Corollary 14.7, dimension two**: the universal sequence `x_n = n!(3-2√2)^{n²}` lies in the rational span of
`1, √2`, tends to zero in `σ_f` and `β_f` but not in `τ_f`, for every nonzero `f`. -/
theorem two_dim_separation :
    (∀ n, ∃ q1 q2 : ℚ, pz n = q1 + q2 * Real.sqrt 2) ∧
      ∀ f : ℝ →+ ℚ, f ≠ 0 → Tendsto pz atTop (@nhds ℝ (sigmaT f ⊤) 0) ∧
        Tendsto pz atTop (@nhds ℝ (betaT f ⊤) 0) ∧ ¬ Tendsto pz atTop (@nhds ℝ (tauT f ⊤) 0) := by
  refine ⟨fun n => ⟨(n.factorial * PP (n ^ 2) : ℤ), -(n.factorial * QQ (n ^ 2) : ℤ), ?_⟩, fun f hf => ?_⟩
  · rw [pz_eq]; push_cast; ring
  · obtain ⟨h1, h2, h3, -⟩ := pell_unscaled_top f hf
    exact ⟨h1, h2, h3⟩

end FiniteSpan

end LeanCheck
