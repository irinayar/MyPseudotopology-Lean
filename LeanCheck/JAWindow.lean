import Mathlib

/-!
# The window kernel (component 11), stage 1: the window, its integrals, one-sided lattice sums

`wD D t = (max 0 (1 - D^2 t^2))^2` is the window `w_D` of `TVGaddmore_v27` (on `|t| ≤ 1/2`, `D ≥ 3`).

Checked here (no axiom, no `sorry`):

* elementary properties: `0 ≤ wD ≤ 1`, even, continuous, nonincreasing on `[0, ∞)`, zero for `|t| ≥ 1/D`;
* `integral_wD`: `∫_{-1/D}^{1/D} w_D = 16/(15 D)` (`I_1` of the paper);
* `integral_wD_sq`: `∫_{-1/D}^{1/D} w_D^2 = 256/(315 D)` (`I_2`);
* `half_lattice`: for a nonincreasing function `0 ≤ f ≤ 1` on `[0, ∞)`, a step `h > 0`, a start `p_0 ∈ [0, h]` and
  `k` points, `∫_0^T f - h ≤ h ∑_{i<k} f(p_0 + i h) ≤ ∫_0^T f + h`, `T = p_0 + k h` (the total-variation estimate for a
  lattice sum, one side).
-/

namespace LeanCheck
namespace JAWindow

open Set MeasureTheory intervalIntegral Finset

/-- The window `w_D`. -/
noncomputable def wD (D t : ℝ) : ℝ := (max 0 (1 - D ^ 2 * t ^ 2)) ^ 2

lemma wD_nonneg (D t : ℝ) : 0 ≤ wD D t := sq_nonneg _

lemma wD_le_one (D t : ℝ) : wD D t ≤ 1 := by
  unfold wD
  have h1 : max 0 (1 - D ^ 2 * t ^ 2) ≤ 1 :=
    max_le zero_le_one (by nlinarith [sq_nonneg (D * t)])
  have h0 : 0 ≤ max 0 (1 - D ^ 2 * t ^ 2) := le_max_left _ _
  nlinarith

lemma wD_even (D t : ℝ) : wD D (-t) = wD D t := by
  unfold wD; ring_nf

lemma wD_continuous (D : ℝ) : Continuous (wD D) := by
  unfold wD
  exact (continuous_const.max (by fun_prop)).pow 2

lemma wD_antitone (D : ℝ) : AntitoneOn (wD D) (Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  unfold wD
  have h : max 0 (1 - D ^ 2 * b ^ 2) ≤ max 0 (1 - D ^ 2 * a ^ 2) := by
    apply max_le_max le_rfl
    have : a ^ 2 ≤ b ^ 2 := by nlinarith
    nlinarith [sq_nonneg D]
  exact pow_le_pow_left₀ (le_max_left _ _) h 2

lemma wD_zero (D : ℝ) (hD : 0 < D) (t : ℝ) (ht : 1 / D ≤ |t|) : wD D t = 0 := by
  unfold wD
  have h1 : 1 ≤ D * |t| := by
    rw [div_le_iff₀ hD] at ht; linarith
  have h2 : 1 ≤ (D * |t|) ^ 2 := by nlinarith
  have h3 : D ^ 2 * t ^ 2 = (D * |t|) ^ 2 := by rw [mul_pow, sq_abs]
  rw [max_eq_left (by linarith)]
  simp

lemma wD_eq_poly (D : ℝ) (t : ℝ) (ht : |t| ≤ 1 / D) (hD : 0 < D) :
    wD D t = (1 - D ^ 2 * t ^ 2) ^ 2 := by
  unfold wD
  have h1 : D * |t| ≤ 1 := by
    rw [le_div_iff₀ hD] at ht; linarith
  have hn : 0 ≤ D * |t| := by positivity
  have h2 : (D * |t|) ^ 2 ≤ 1 := by nlinarith
  have h3 : D ^ 2 * t ^ 2 = (D * |t|) ^ 2 := by rw [mul_pow, sq_abs]
  rw [max_eq_right (by linarith)]

/-- `I_1 = ∫ w_D = 16 / (15 D)`. -/
theorem integral_wD (D : ℝ) (hD : 0 < D) :
    ∫ t in (-(1 / D))..(1 / D), wD D t = 16 / (15 * D) := by
  have hcongr : ∫ t in (-(1 / D))..(1 / D), wD D t =
      ∫ t in (-(1 / D))..(1 / D), (1 - D ^ 2 * t ^ 2) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hle : -(1 / D) ≤ 1 / D := by
      have : 0 < 1 / D := by positivity
      linarith
    rw [uIcc_of_le hle] at ht
    exact wD_eq_poly D t (abs_le.mpr ⟨ht.1, ht.2⟩) hD
  rw [hcongr]
  have hder : ∀ t ∈ uIcc (-(1 / D)) (1 / D),
      HasDerivAt (fun t => t - (2 * D ^ 2 / 3) * t ^ 3 + (D ^ 4 / 5) * t ^ 5)
        ((1 - D ^ 2 * t ^ 2) ^ 2) t := by
    intro t _
    have := ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).const_mul (2 * D ^ 2 / 3))).add
      ((hasDerivAt_pow 5 t).const_mul (D ^ 4 / 5))
    exact this.congr_deriv ((by norm_num <;> ring) : _ = (1 - D ^ 2 * t ^ 2) ^ 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (by
    apply Continuous.intervalIntegrable; fun_prop)]
  field_simp
  ring

/-- `I_2 = ∫ w_D^2 = 256 / (315 D)`. -/
theorem integral_wD_sq (D : ℝ) (hD : 0 < D) :
    ∫ t in (-(1 / D))..(1 / D), (wD D t) ^ 2 = 256 / (315 * D) := by
  have hcongr : ∫ t in (-(1 / D))..(1 / D), (wD D t) ^ 2 =
      ∫ t in (-(1 / D))..(1 / D), (1 - D ^ 2 * t ^ 2) ^ 4 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hle : -(1 / D) ≤ 1 / D := by
      have : 0 < 1 / D := by positivity
      linarith
    rw [uIcc_of_le hle] at ht
    beta_reduce
    rw [wD_eq_poly D t (abs_le.mpr ⟨ht.1, ht.2⟩) hD]
    ring
  rw [hcongr]
  have hder : ∀ t ∈ uIcc (-(1 / D)) (1 / D),
      HasDerivAt (fun t => t - (4 * D ^ 2 / 3) * t ^ 3 + (6 * D ^ 4 / 5) * t ^ 5 -
          (4 * D ^ 6 / 7) * t ^ 7 + (D ^ 8 / 9) * t ^ 9)
        ((1 - D ^ 2 * t ^ 2) ^ 4) t := by
    intro t _
    have := ((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).const_mul (4 * D ^ 2 / 3))).add
      ((hasDerivAt_pow 5 t).const_mul (6 * D ^ 4 / 5))).sub
      ((hasDerivAt_pow 7 t).const_mul (4 * D ^ 6 / 7))).add
      ((hasDerivAt_pow 9 t).const_mul (D ^ 8 / 9))
    exact this.congr_deriv ((by norm_num <;> ring) : _ = (1 - D ^ 2 * t ^ 2) ^ 4)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (by
    apply Continuous.intervalIntegrable; fun_prop)]
  field_simp
  ring

/-- **One-sided lattice sums of a nonincreasing function** (total-variation estimate). -/
theorem half_lattice (f : ℝ → ℝ) (hf0 : ∀ s, 0 ≤ f s) (hf1 : ∀ s, f s ≤ 1)
    (hanti : AntitoneOn f (Ici 0)) (hcont : Continuous f) (h p₀ : ℝ) (k : ℕ)
    (hh : 0 < h) (hp0 : 0 ≤ p₀) (hph : p₀ ≤ h) :
    (∫ s in (0 : ℝ)..(p₀ + k * h), f s) - h ≤ h * ∑ i ∈ range k, f (p₀ + i * h) ∧
      h * ∑ i ∈ range k, f (p₀ + i * h) ≤ (∫ s in (0 : ℝ)..(p₀ + k * h), f s) + h := by
  set g : ℝ → ℝ := fun u => f (p₀ + h * u) with hg
  have hgc : Continuous g := hcont.comp (by fun_prop)
  have hgnn : ∀ u, 0 ≤ g u := fun u => hf0 _
  -- change of variables
  have hchg : ∀ n : ℕ, ∫ u in (0 : ℝ)..(n : ℝ), g u = (1 / h) * ∫ s in p₀..(p₀ + n * h), f s := by
    intro n
    have h0 := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := (n : ℝ)) f hh.ne' p₀
    have e0 : h * 0 + p₀ = p₀ := by ring
    have e1 : h * (n : ℝ) + p₀ = p₀ + n * h := by ring
    rw [e0, e1] at h0
    have e : ∀ u, g u = f (h * u + p₀) := fun u => by simp only [hg]; rw [add_comm]
    simp_rw [e]
    rw [h0, smul_eq_mul, one_div]
  have hanti_g : AntitoneOn g (Icc 0 (k : ℝ)) := by
    intro u hu v hv huv
    apply hanti
    · simp only [Set.mem_Ici]; have := hu.1; nlinarith
    · simp only [Set.mem_Ici]; have := hv.1; nlinarith
    · nlinarith
  -- integral of f over [p0, p0 + k h]
  have hsplit : (∫ s in (0 : ℝ)..(p₀ + k * h), f s) =
      (∫ s in (0 : ℝ)..p₀, f s) + ∫ s in p₀..(p₀ + k * h), f s := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hcont.intervalIntegrable _ _
    · exact hcont.intervalIntegrable _ _
  have hfirst : (∫ s in (0 : ℝ)..p₀, f s) ≤ h := by
    have : (∫ s in (0 : ℝ)..p₀, f s) ≤ ∫ s in (0 : ℝ)..p₀, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on hp0 (hcont.intervalIntegrable _ _)
        (by simp) (fun s _ => hf1 s)
    simp at this
    linarith
  have hfirst0 : 0 ≤ (∫ s in (0 : ℝ)..p₀, f s) :=
    intervalIntegral.integral_nonneg hp0 (fun s _ => hf0 s)
  constructor
  · -- lower bound
    have h2 : ∫ u in (0 : ℝ)..(k : ℝ), g u ≤ ∑ i ∈ range k, g (i : ℝ) := by
      have := AntitoneOn.integral_le_sum (x₀ := 0) (a := k) (f := g) (by rw [zero_add]; exact hanti_g)
      simpa using this
    rw [hchg k] at h2
    have h3 : ∑ i ∈ range k, g (i : ℝ) = ∑ i ∈ range k, f (p₀ + i * h) := by
      apply Finset.sum_congr rfl; intro i _; simp only [hg]; ring_nf
    rw [h3] at h2
    have h4 : ∫ s in p₀..(p₀ + k * h), f s ≤ h * ∑ i ∈ range k, f (p₀ + i * h) := by
      have := mul_le_mul_of_nonneg_left h2 hh.le
      rw [← mul_assoc, mul_one_div_cancel hh.ne', one_mul] at this
      exact this
    linarith
  · -- upper bound
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
      have := hfirst0
      linarith
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hanti_g' : AntitoneOn g (Icc 0 (0 + (k' : ℝ))) := by
        rw [zero_add]
        exact hanti_g.mono (Set.Icc_subset_Icc le_rfl (by push_cast; linarith))
      have h2 : ∑ i ∈ range k', g (0 + ↑(i + 1)) ≤ ∫ u in (0 : ℝ)..(0 + k'), g u :=
        AntitoneOn.sum_le_integral hanti_g'
      simp only [zero_add] at h2
      rw [hchg k'] at h2
      have h3 : ∑ i ∈ range k', g ((i + 1 : ℕ) : ℝ) = ∑ i ∈ range k', f (p₀ + ((i + 1 : ℕ) : ℝ) * h) := by
        apply Finset.sum_congr rfl; intro i _; simp only [hg]; ring_nf
      rw [h3] at h2
      have h4 : h * ∑ i ∈ range k', f (p₀ + ((i + 1 : ℕ) : ℝ) * h) ≤ ∫ s in p₀..(p₀ + k' * h), f s := by
        have := mul_le_mul_of_nonneg_left h2 hh.le
        rw [← mul_assoc, mul_one_div_cancel hh.ne', one_mul] at this
        exact this
      have h5 : ∫ s in p₀..(p₀ + k' * h), f s ≤ ∫ s in p₀..(p₀ + (k' + 1 : ℕ) * h), f s := by
        have hk0 : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
        have hadj := intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable (μ := volume) p₀ (p₀ + k' * h))
          (hcont.intervalIntegrable (μ := volume) (p₀ + k' * h) (p₀ + ((k' + 1 : ℕ) : ℝ) * h))
        have hnn : 0 ≤ ∫ s in (p₀ + k' * h)..(p₀ + ((k' + 1 : ℕ) : ℝ) * h), f s :=
          intervalIntegral.integral_nonneg (by push_cast; nlinarith) (fun s _ => hf0 s)
        linarith
      have hsum : ∑ i ∈ range (k' + 1), f (p₀ + (i : ℝ) * h) =
          f p₀ + ∑ i ∈ range k', f (p₀ + ((i + 1 : ℕ) : ℝ) * h) := by
        rw [Finset.sum_range_succ']
        simp [add_comm]
      rw [hsum, mul_add]
      have hf0' := hf1 p₀
      nlinarith [hsplit, hfirst0]


/-- For `f` vanishing on `[R, ∞)`, the integral over `[0, T]` is the integral over `[0, R]` when `T ≥ R`. -/
lemma integral_tail (f : ℝ → ℝ) (hcont : Continuous f) (R T : ℝ) (hR : 0 ≤ R) (hT : R ≤ T)
    (hzero : ∀ s, R ≤ s → f s = 0) :
    (∫ s in (0 : ℝ)..T, f s) = ∫ s in (0 : ℝ)..R, f s := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := R)
    (hcont.intervalIntegrable (μ := volume) 0 R) (hcont.intervalIntegrable (μ := volume) R T)]
  have : ∫ s in R..T, f s = 0 := by
    have : ∫ s in R..T, f s = ∫ s in R..T, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hT] at hs
      exact hzero s hs.1
    rw [this]; simp
  rw [this, add_zero]

/-- **Two-sided lattice sums** of an even, nonincreasing-on-`[0,∞)` function supported in `[-R, R]`:
the sum over the lattice `{p_0 + i h} ∪ {-(h - p_0) - i h}` times `h` is within `2h` of `2 ∫_0^R f`. -/
theorem two_sided (f : ℝ → ℝ) (hf0 : ∀ s, 0 ≤ f s) (hf1 : ∀ s, f s ≤ 1)
    (hanti : AntitoneOn f (Ici 0)) (hcont : Continuous f) (R : ℝ) (hR : 0 ≤ R)
    (hzero : ∀ s, R ≤ s → f s = 0) (h p₀ : ℝ) (k k' : ℕ) (hh : 0 < h) (hp0 : 0 ≤ p₀) (hph : p₀ ≤ h)
    (hk : R ≤ p₀ + k * h) (hk' : R ≤ (h - p₀) + k' * h) :
    |h * (∑ i ∈ range k, f (p₀ + i * h) + ∑ i ∈ range k', f ((h - p₀) + i * h)) -
        2 * ∫ s in (0 : ℝ)..R, f s| ≤ 2 * h := by
  have h1 := half_lattice f hf0 hf1 hanti hcont h p₀ k hh hp0 hph
  have h2 := half_lattice f hf0 hf1 hanti hcont h (h - p₀) k' hh (by linarith) (by linarith)
  rw [integral_tail f hcont R _ hR hk hzero] at h1
  rw [integral_tail f hcont R _ hR hk' hzero] at h2
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- Half integrals of `w_D` and `w_D^2` (evenness). -/
lemma integral_half_of_even (f : ℝ → ℝ) (hcont : Continuous f) (heven : ∀ s, f (-s) = f s) (R : ℝ) :
    ∫ s in (-R)..R, f s = 2 * ∫ s in (0 : ℝ)..R, f s := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable (μ := volume) (-R) 0) (hcont.intervalIntegrable (μ := volume) 0 R)]
  have : ∫ s in (-R)..0, f s = ∫ s in (0 : ℝ)..R, f s := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := R) f
    simp only [neg_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro s _
    exact (heven s).symm ▸ rfl
  rw [this]; ring

theorem half_integral_wD (D : ℝ) (hD : 0 < D) :
    ∫ s in (0 : ℝ)..(1 / D), wD D s = 8 / (15 * D) := by
  have h := integral_half_of_even (wD D) (wD_continuous D) (wD_even D) (1 / D)
  rw [integral_wD D hD] at h
  have e : 16 / (15 * D) = 2 * (8 / (15 * D)) := by ring
  linarith

theorem half_integral_wD_sq (D : ℝ) (hD : 0 < D) :
    ∫ s in (0 : ℝ)..(1 / D), (wD D s) ^ 2 = 128 / (315 * D) := by
  have h := integral_half_of_even (fun s => (wD D s) ^ 2) ((wD_continuous D).pow 2)
    (fun s => by simp only [wD_even]) (1 / D)
  rw [integral_wD_sq D hD] at h
  have e : 256 / (315 * D) = 2 * (128 / (315 * D)) := by ring
  linarith

/-- **Lattice sums of `w_D`**: within `2h` of `2 · 8/(15D) = I_1`. -/
theorem lattice_wD (D : ℝ) (hD : 0 < D) (h p₀ : ℝ) (k k' : ℕ) (hh : 0 < h) (hp0 : 0 ≤ p₀)
    (hph : p₀ ≤ h) (hk : 1 / D ≤ p₀ + k * h) (hk' : 1 / D ≤ (h - p₀) + k' * h) :
    |h * (∑ i ∈ range k, wD D (p₀ + i * h) + ∑ i ∈ range k', wD D ((h - p₀) + i * h)) -
        16 / (15 * D)| ≤ 2 * h := by
  have := two_sided (wD D) (wD_nonneg D) (wD_le_one D) (wD_antitone D) (wD_continuous D) (1 / D)
    (by positivity) (fun s hs => wD_zero D hD s (by rw [abs_of_nonneg (by linarith [show (0 : ℝ) ≤ 1 / D by positivity])]; exact hs))
    h p₀ k k' hh hp0 hph hk hk'
  rw [half_integral_wD D hD] at this
  have e : 2 * (8 / (15 * D)) = 16 / (15 * D) := by ring
  rwa [e] at this

/-- **Lattice sums of `w_D^2`**: within `2h` of `I_2`. -/
theorem lattice_wD_sq (D : ℝ) (hD : 0 < D) (h p₀ : ℝ) (k k' : ℕ) (hh : 0 < h) (hp0 : 0 ≤ p₀)
    (hph : p₀ ≤ h) (hk : 1 / D ≤ p₀ + k * h) (hk' : 1 / D ≤ (h - p₀) + k' * h) :
    |h * (∑ i ∈ range k, (wD D (p₀ + i * h)) ^ 2 + ∑ i ∈ range k', (wD D ((h - p₀) + i * h)) ^ 2) -
        256 / (315 * D)| ≤ 2 * h := by
  have hanti2 : AntitoneOn (fun s => (wD D s) ^ 2) (Ici 0) := by
    intro a ha b hb hab
    exact pow_le_pow_left₀ (wD_nonneg D b) (wD_antitone D ha hb hab) 2
  have := two_sided (fun s => (wD D s) ^ 2) (fun s => sq_nonneg _)
    (fun s => by nlinarith [wD_nonneg D s, wD_le_one D s]) hanti2 ((wD_continuous D).pow 2) (1 / D)
    (by positivity)
    (fun s hs => by
      show wD D s ^ 2 = 0
      rw [wD_zero D hD s (by rw [abs_of_nonneg (by linarith [show (0 : ℝ) ≤ 1 / D by positivity])]; exact hs)]
      simp)
    h p₀ k k' hh hp0 hph hk hk'
  rw [half_integral_wD_sq D hD] at this
  have e : 2 * (128 / (315 * D)) = 256 / (315 * D) := by ring
  rwa [e] at this

#print axioms integral_wD
#print axioms integral_wD_sq
#print axioms half_lattice
#print axioms two_sided
#print axioms lattice_wD
#print axioms lattice_wD_sq

end JAWindow
end LeanCheck
