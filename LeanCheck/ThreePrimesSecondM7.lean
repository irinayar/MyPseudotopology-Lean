import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# ThreePrimesSecondM7: the geometric core of the proposition on the second independent ball vector

In lattice coordinates (a basis of the lattice whose first vector is the primitive vector `v₁`) the lattice
is `ℤ × ℤ^k`, and the symmetric convex open body `C ⊆ ℝ × ℝ^k` has the central chord `{(t,0) : |t| μ < 1}`.

`second_vector_core`: if `2^k < ofReal ((μ/2) (1-μ/2)^k) * vol C`, then `C` contains an integer point `(a,b)`
with `b ≠ 0` (so a lattice vector of `C` that is not a multiple of `v₁`).

Proof: the projection `C'` of `C` along the first axis has `vol C ≤ (2/μ) vol C'` (chord lemma and Fubini),
Minkowski's first theorem for `ℤ^k` applied to `(1-μ/2) C'` gives a nonzero integer `b` in it, and a convex
combination of an interior point of `C` with a closure point on the first axis gives `(a,b) ∈ C`.

Not formalised: the passage from a general lattice to these coordinates (completing a primitive vector to a
basis, the change of volume by the determinant).
-/
open MeasureTheory Pointwise

theorem minkowski_int (k : ℕ) (s : Set (Fin k → ℝ)) (hs : ∀ x ∈ s, -x ∈ s) (hc : Convex ℝ s)
    (hv : 2 ^ k < volume s) : ∃ b : Fin k → ℤ, b ≠ 0 ∧ (fun i => (b i : ℝ)) ∈ s := by
  classical
  have hfd := ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin k)) (volume : Measure (Fin k → ℝ))
  have hF : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin k))) = 1 := by
    rw [ZSpan.volume_fundamentalDomain]
    have h1 : Matrix.of ⇑(Pi.basisFun ℝ (Fin k)) = 1 := by
      ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [h1]; simp
  have hv' : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin k))) * 2 ^ Module.finrank ℝ (Fin k → ℝ) < volume s := by
    rw [hF]; simpa using hv
  have : Countable ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))).toAddSubgroup :=
    inferInstanceAs (Countable ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))))
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))).toAddSubgroup) hfd hs hc hv'
  have hmem : (x : Fin k → ℝ) ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k))) := x.2
  rw [Module.Basis.mem_span_iff_repr_mem] at hmem
  choose z hz using fun i => hmem i
  refine ⟨z, ?_, ?_⟩
  · intro h
    apply hx0
    ext i
    have := hz i
    simp [Pi.basisFun_repr, h] at this
    simpa using this.symm
  · have : (fun i => (z i : ℝ)) = (x : Fin k → ℝ) := by
      ext i; have := hz i; simp [Pi.basisFun_repr] at this; simpa using this
    rw [this]; exact hxs


/-- chord lemma: every chord of a symmetric convex set parallel to the first axis is at most as long
as the central chord -/
theorem chord_le (k : ℕ) (C : Set (ℝ × (Fin k → ℝ))) (hCc : Convex ℝ C) (hCs : ∀ x ∈ C, -x ∈ C)
    (μ : ℝ) (hμ0 : 0 < μ) (hcen : ∀ t : ℝ, (t, (0 : Fin k → ℝ)) ∈ C → |t| * μ < 1)
    (h : Fin k → ℝ) : volume {t : ℝ | (t, h) ∈ C} ≤ ENNReal.ofReal (2 / μ) := by
  refine (Real.volume_le_diam _).trans ?_
  refine Metric.ediam_le fun x hx y hy => ?_
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  have hy' : (-y, -h) ∈ C := by simpa using hCs _ hy
  have hmid := hCc hx hy' (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  have e : (1/2 : ℝ) • (x, h) + (1/2 : ℝ) • (-y, -h) = ((x - y) / 2, (0 : Fin k → ℝ)) := by
    ext <;> simp <;> ring
  rw [e] at hmid
  have := hcen _ hmid
  rw [abs_div, abs_two, div_mul_eq_mul_div, div_lt_one (by norm_num)] at this
  rw [le_div_iff₀ hμ0]
  nlinarith [abs_nonneg (x - y)]

theorem vol_le_proj (k : ℕ) (C : Set (ℝ × (Fin k → ℝ))) (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hCs : ∀ x ∈ C, -x ∈ C) (μ : ℝ) (hμ0 : 0 < μ)
    (hcen : ∀ t : ℝ, (t, (0 : Fin k → ℝ)) ∈ C → |t| * μ < 1) :
    volume C ≤ ENNReal.ofReal (2 / μ) * volume (Prod.snd '' C) := by
  have hmeas : MeasurableSet C := hCo.measurableSet
  have hmeas' : MeasurableSet (Prod.snd '' C) := (isOpenMap_snd C hCo).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas]
  calc ∫⁻ h, volume ((fun x => (x, h)) ⁻¹' C)
      ≤ ∫⁻ h, (Prod.snd '' C).indicator (fun _ => ENNReal.ofReal (2 / μ)) h := by
        refine lintegral_mono fun h => ?_
        by_cases hh : h ∈ Prod.snd '' C
        · rw [Set.indicator_of_mem hh]
          exact chord_le k C hCc hCs μ hμ0 hcen h
        · have : (fun x => (x, h)) ⁻¹' C = ∅ := by
            ext t; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
            intro ht; exact hh ⟨_, ht, rfl⟩
          rw [this]; simp
    _ = ENNReal.ofReal (2 / μ) * volume (Prod.snd '' C) := by
        rw [lintegral_indicator_const hmeas']

theorem second_vector_core (k : ℕ) (C : Set (ℝ × (Fin k → ℝ))) (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hCs : ∀ x ∈ C, -x ∈ C) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hcen : ∀ t : ℝ, (t, (0 : Fin k → ℝ)) ∈ C ↔ |t| * μ < 1)
    (hvol : (2 : ENNReal) ^ k < ENNReal.ofReal ((μ / 2) * (1 - μ / 2) ^ k) * volume C) :
    ∃ (a : ℤ) (b : Fin k → ℤ), b ≠ 0 ∧ (((a : ℝ), fun i => (b i : ℝ)) ∈ C) := by
  have hvp := vol_le_proj k C hCo hCc hCs μ hμ0 (fun t ht => (hcen t).1 ht)
  have hC'o : IsOpen (Prod.snd '' C) := isOpenMap_snd C hCo
  have hC'c : Convex ℝ (Prod.snd '' C) := by
    simpa using hCc.linear_image (LinearMap.snd ℝ ℝ (Fin k → ℝ))
  have hC's : ∀ x ∈ Prod.snd '' C, -x ∈ Prod.snd '' C := by
    rintro _ ⟨y, hy, rfl⟩; exact ⟨-y, hCs y hy, by simp⟩
  have hρ0 : 0 < 1 - μ / 2 := by linarith
  have hρ1 : 1 - μ / 2 < 1 := by linarith
  have hvolρ : volume ((1 - μ / 2) • Prod.snd '' C) = ENNReal.ofReal ((1 - μ / 2) ^ k) * volume (Prod.snd '' C) := by
    rw [Measure.addHaar_smul]; simp [abs_of_pos (pow_pos hρ0 k)]
  have hbig : (2 : ENNReal) ^ k < volume ((1 - μ / 2) • Prod.snd '' C) := by
    rw [hvolρ]
    calc (2 : ENNReal) ^ k < ENNReal.ofReal ((μ / 2) * (1 - μ / 2) ^ k) * volume C := hvol
      _ ≤ ENNReal.ofReal ((μ / 2) * (1 - μ / 2) ^ k) * (ENNReal.ofReal (2 / μ) * volume (Prod.snd '' C)) := by
          gcongr
      _ = ENNReal.ofReal ((1 - μ / 2) ^ k) * volume (Prod.snd '' C) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          field_simp
  obtain ⟨b, hb0, hbs⟩ := minkowski_int k ((1 - μ / 2) • Prod.snd '' C)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨-x, hC's x hx, by simp⟩)
    (hC'c.smul _) hbig
  obtain ⟨x', hx', hxb⟩ := hbs
  obtain ⟨y, hyC, rfl⟩ := hx'
  refine ⟨round ((1 - μ / 2) * y.1), b, hb0, ?_⟩
  set ρ := 1 - μ / 2 with hρdef
  set t0 := ρ * y.1 with ht0
  set τ := ((round t0 : ℝ) - t0) / (1 - ρ) with hτ
  have hτb : |τ| * μ ≤ 1 := by
    have h1 : 1 - ρ = μ / 2 := by rw [hρdef]; ring
    have h2 : |(round t0 : ℝ) - t0| ≤ 1 / 2 := by
      rw [abs_sub_comm]; exact abs_sub_round t0
    rw [hτ, abs_div, h1, abs_of_pos (by positivity : 0 < μ / 2), div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith
  have hw : ((τ, (0 : Fin k → ℝ)) : ℝ × (Fin k → ℝ)) ∈ closure C := by
    have hcont : Continuous (fun t : ℝ => (t, (0 : Fin k → ℝ))) := by fun_prop
    have hset : (fun t : ℝ => (t, (0 : Fin k → ℝ))) ⁻¹' C = Set.Ioo (-(1 / μ)) (1 / μ) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ioo]
      rw [hcen, ← abs_lt, lt_div_iff₀ hμ0]
    have hmem : τ ∈ closure ((fun t : ℝ => (t, (0 : Fin k → ℝ))) ⁻¹' C) := by
      have hpos : 0 < 1 / μ := by positivity
      rw [hset, closure_Ioo (by intro h; linarith)]
      have hτ' : |τ| ≤ 1 / μ := by rw [le_div_iff₀ hμ0]; linarith
      exact ⟨(abs_le.mp hτ').1, (abs_le.mp hτ').2⟩
    exact hcont.closure_preimage_subset C hmem
  have key := hCc.combo_interior_closure_mem_interior (x := y) (y := (τ, (0 : Fin k → ℝ)))
    (by rwa [hCo.interior_eq]) hw (a := ρ) (b := 1 - ρ) hρ0 (by linarith) (by ring)
  rw [hCo.interior_eq] at key
  convert key using 1
  have h1ρ : (1 - ρ) ≠ 0 := by linarith
  have hmul : (1 - ρ) * τ = (round t0 : ℝ) - t0 := by rw [hτ]; field_simp
  ext x
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linarith
  · have := congrFun hxb x
    simp only [Prod.snd_add, Prod.smul_snd, smul_zero, add_zero]
    simpa using this.symm
