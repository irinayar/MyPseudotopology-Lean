import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# ThreePrimesPackingM8: translates along the shortest vector outside a subgroup, and the criterion for `N_r`

The convex body of the prose is the open unit ball of the norm of a real normed space `E`, the lattice is a
countable additive subgroup `L` with a fundamental domain `F`, and the volume of the image of `(lam/2) K` in
`E ⧸ L` is `μ ((⋃ v : L, ball v (lam/2)) ∩ F)`.

* `translate_sep`: the separation of the points `s • z` from the lattice.
* `packing_image`: `N * (volume of the image) ≤ volume of F` whenever `N * lam ≤ ‖z‖`.
* `packing_ball`: if every nonzero lattice vector has norm `≥ lam`, then `N * μ (ball 0 (lam/2)) ≤ μ F`.
* `restricted_min_lt`: the arithmetic step `⌊R/mu⌋ mu^n ≤ V → R < mu + V / mu^(n-1)`.
* `nr_sharp`, `nr_two`, `nr_eps`: the three forms of the criterion for an element not divisible by `r`,
  on the witness lattice written in the coordinates `(s/T, m (D s - j_i q_i)/q_i)`.

Not formalised: the identification of the moduli `q_i` with the retained prime squares, the omitted
coordinates, and the passage to `P_S` and to ball elements.
-/
open MeasureTheory Pointwise Metric
open scoped ENNReal

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `z` has the least norm in `L \ L'`, then `s • z` is at distance at least `lam` from `L`
as long as `lam ≤ s‖z‖ ≤ ‖z‖ - lam`. -/
theorem translate_sep (L L' : AddSubgroup E) (z : E) (hz : z ∈ L) (hz' : z ∉ L')
    (hmin : ∀ v ∈ L, v ∉ L' → ‖z‖ ≤ ‖v‖) (lam s : ℝ) (hs0 : 0 ≤ s) (h1 : lam ≤ s * ‖z‖)
    (h2 : s * ‖z‖ ≤ ‖z‖ - lam) (p : E) (hp : p ∈ L) : lam ≤ ‖s • z - p‖ := by
  by_contra h
  push Not at h
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => hz' (h0 ▸ L'.zero_mem)
  have hsz : ‖s • z‖ = s * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hs0]
  by_cases hpL : p ∈ L'
  · have hw : z - p ∈ L := L.sub_mem hz hp
    have hw' : z - p ∉ L' := fun hc => hz' (by simpa using L'.add_mem hc hpL)
    have h3 := hmin _ hw hw'
    have hl : 0 < lam := lt_of_le_of_lt (norm_nonneg _) h
    have hs1 : s ≤ 1 := by
      have : s * ‖z‖ ≤ 1 * ‖z‖ := by linarith
      exact le_of_mul_le_mul_right this hzpos
    have h4 : ‖z - p‖ ≤ ‖(1 - s) • z‖ + ‖s • z - p‖ := by
      have e : z - p = (1 - s) • z + (s • z - p) := by rw [sub_smul, one_smul]; abel
      calc ‖z - p‖ = ‖(1 - s) • z + (s • z - p)‖ := by rw [← e]
        _ ≤ _ := norm_add_le _ _
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hs1), sub_mul, one_mul] at h4
    linarith
  · have h3 := hmin _ hp hpL
    have h4 : ‖p‖ ≤ ‖s • z‖ + ‖s • z - p‖ := by
      have e : p = s • z - (s • z - p) := by abel
      calc ‖p‖ = ‖s • z - (s • z - p)‖ := by rw [← e]
        _ ≤ _ := norm_sub_le _ _
    rw [hsz] at h4
    linarith

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddLeftInvariant]

/-- The packing inequality for the image of the ball in the quotient. -/
theorem packing_image (L L' : AddSubgroup E) [Countable L] (F : Set E)
    (hF : IsAddFundamentalDomain L F μ) (z : E) (hz : z ∈ L) (hz' : z ∉ L')
    (hmin : ∀ v ∈ L, v ∉ L' → ‖z‖ ≤ ‖v‖) (lam : ℝ) (hlam : 0 < lam) (N : ℕ)
    (hN : (N : ℝ) * lam ≤ ‖z‖) :
    (N : ℝ≥0∞) * μ ((⋃ v : L, ball (v : E) (lam / 2)) ∩ F) ≤ μ F := by
  set A : Set E := ⋃ v : L, ball (v : E) (lam / 2) with hA
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => hz' (h0 ▸ L'.zero_mem)
  have hAo : IsOpen A := isOpen_iUnion fun _ => isOpen_ball
  have hAinv : ∀ g : L, (fun x : E => g +ᵥ x) ⁻¹' A = A := by
    intro g
    ext y
    simp only [Set.mem_preimage, hA, Set.mem_iUnion, mem_ball, AddSubgroup.vadd_def, vadd_eq_add]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨v - g, ?_⟩
      have e : dist y ((v - g : L) : E) = dist ((g : E) + y) (v : E) := by
        rw [dist_eq_norm, dist_eq_norm, AddSubgroup.coe_sub]; congr 1; abel
      rw [e]; exact hv
    · rintro ⟨v, hv⟩
      refine ⟨g + v, ?_⟩
      have e : dist ((g : E) + y) ((g + v : L) : E) = dist y (v : E) := by
        rw [AddSubgroup.coe_add, dist_add_left]
      rw [e]; exact hv
  set x : ℕ → E := fun j => ((j : ℝ) * lam / ‖z‖) • z with hx
  set B : ℕ → Set E := fun j => (fun y => y - x j) ⁻¹' A with hB
  have hsep : ∀ j l : ℕ, l < j → j < N → Disjoint (B j) (B l) := by
    intro j l hlj hjN
    rw [Set.disjoint_left]
    intro y hyj hyl
    simp only [hB, Set.mem_preimage, hA, Set.mem_iUnion, mem_ball] at hyj hyl
    obtain ⟨v, hv⟩ := hyj
    obtain ⟨w, hw⟩ := hyl
    set s : ℝ := ((j : ℝ) - l) * lam / ‖z‖ with hs
    have hjl : (1 : ℝ) ≤ (j : ℝ) - l := by
      have : (l : ℝ) + 1 ≤ j := by exact_mod_cast hlj
      linarith
    have hsz : s * ‖z‖ = ((j : ℝ) - l) * lam := by rw [hs]; field_simp
    have h1 : lam ≤ s * ‖z‖ := by
      rw [hsz]; nlinarith
    have h2 : s * ‖z‖ ≤ ‖z‖ - lam := by
      have : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
      have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      have h3 : ((j : ℝ) - l + 1) * lam ≤ N * lam :=
        mul_le_mul_of_nonneg_right (by linarith) hlam.le
      rw [hsz]; linarith
    have hs0 : 0 ≤ s := by
      rw [hs]; exact div_nonneg (mul_nonneg (by linarith) hlam.le) hzpos.le
    have hp : (w : E) - v ∈ L := L.sub_mem w.2 v.2
    have key := translate_sep L L' z hz hz' hmin lam s hs0 h1 h2 _ hp
    have hdiff : s • z = x j - x l := by
      simp only [hx, hs]
      rw [← sub_smul]; congr 1; ring
    have e : s • z - ((w : E) - v) = (y - x l - w) - (y - x j - v) := by
      rw [hdiff]; abel
    rw [e] at key
    have : ‖(y - x l - w) - (y - x j - v)‖ < lam := by
      refine lt_of_le_of_lt (norm_sub_le _ _) ?_
      rw [← dist_eq_norm, ← dist_eq_norm]
      linarith
    linarith
  have hmeas : ∀ j, μ (B j ∩ F) = μ (A ∩ F) := by
    intro j
    have e1 : B j ∩ F = (fun h => -x j + h) ⁻¹' (A ∩ (fun h => x j + h) ⁻¹' F) := by
      ext y
      simp only [hB, Set.mem_inter_iff, Set.mem_preimage]
      rw [neg_add_eq_sub, add_sub_cancel]
    have e2 : (fun h => x j + h) ⁻¹' F = (-x j) +ᵥ F := by
      ext y
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg]
      rfl
    rw [e1, measure_preimage_add, e2]
    exact (hF.vadd_of_comm (-x j)).measure_set_eq hF hAo.measurableSet hAinv
  have hsum : ∑ j ∈ Finset.range N, μ (B j ∩ F) ≤ μ F := by
    rw [← measure_biUnion_finset₀]
    · exact measure_mono (Set.iUnion₂_subset fun _ _ => Set.inter_subset_right)
    · intro j hj l hl hne
      refine Disjoint.aedisjoint ?_
      rcases lt_or_gt_of_ne hne with h | h
      · exact ((hsep l j h (Finset.mem_range.mp hl)).symm).mono Set.inter_subset_left Set.inter_subset_left
      · exact (hsep j l h (Finset.mem_range.mp hj)).mono Set.inter_subset_left Set.inter_subset_left
    · intro j _
      exact ((hAo.preimage (continuous_id.sub continuous_const)).measurableSet.nullMeasurableSet).inter
        hF.nullMeasurableSet
  simpa [hmeas, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsum

omit [NormedSpace ℝ E] in
/-- If all nonzero lattice vectors have norm at least `lam`, the image of the ball has the volume of the ball
(the inequality needed here). -/
theorem ball_le_image (L : AddSubgroup E) [Countable L] (F : Set E)
    (hF : IsAddFundamentalDomain L F μ) (lam : ℝ) (hL : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖) :
    μ (ball (0 : E) (lam / 2)) ≤ μ ((⋃ v : L, ball (v : E) (lam / 2)) ∩ F) := by
  have h1 : μ (ball (0 : E) (lam / 2)) = ∑' g : L, μ (ball (g : E) (lam / 2) ∩ F) := by
    rw [hF.measure_eq_tsum (ball (0 : E) (lam / 2))]
    refine tsum_congr fun g => ?_
    have e : g +ᵥ ball (0 : E) (lam / 2) = ball (g : E) (lam / 2) := by
      ext y
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, mem_ball, mem_ball, dist_zero_right, dist_eq_norm,
        AddSubgroup.vadd_def, vadd_eq_add, AddSubgroup.coe_neg, neg_add_eq_sub]
    rw [e]
  have h3 : μ (⋃ g : L, ball (g : E) (lam / 2) ∩ F) = ∑' g : L, μ (ball (g : E) (lam / 2) ∩ F) := by
    refine measure_iUnion₀ ?_ fun g => measurableSet_ball.nullMeasurableSet.inter hF.nullMeasurableSet
    intro g h hne
    refine Disjoint.aedisjoint (Disjoint.mono Set.inter_subset_left Set.inter_subset_left ?_)
    refine ball_disjoint_ball ?_
    have hne' : ((g : E) - h) ≠ 0 := sub_ne_zero.mpr fun hc => hne (Subtype.ext hc)
    have := hL _ (L.sub_mem g.2 h.2) hne'
    rw [dist_eq_norm]; linarith
  rw [h1, ← h3, Set.iUnion_inter]

/-- `N * μ(ball) ≤ μ(F)` when all nonzero lattice vectors have norm at least `lam`. -/
theorem packing_ball (L L' : AddSubgroup E) [Countable L] (F : Set E)
    (hF : IsAddFundamentalDomain L F μ) (z : E) (hz : z ∈ L) (hz' : z ∉ L')
    (hmin : ∀ v ∈ L, v ∉ L' → ‖z‖ ≤ ‖v‖) (lam : ℝ) (hlam : 0 < lam)
    (hL : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖) (N : ℕ) (hN : (N : ℝ) * lam ≤ ‖z‖) :
    (N : ℝ≥0∞) * μ (ball (0 : E) (lam / 2)) ≤ μ F :=
  le_trans (mul_le_mul_right (ball_le_image μ L F hF lam hL) _)
    (packing_image μ L L' F hF z hz hz' hmin lam hlam N hN)

end Abstract

/-- The arithmetic step from `⌊R/mu⌋ mu^n ≤ V` to `R < mu + V / mu^(n-1)`. -/
theorem restricted_min_lt (R mu V : ℝ) (n : ℕ) (hmu : 0 < mu)
    (h : (⌊R / mu⌋₊ : ℝ) * mu ^ (n + 1) ≤ V) : R < mu + V / mu ^ n := by
  have h1 : R / mu < ⌊R / mu⌋₊ + 1 := Nat.lt_floor_add_one _
  have h2 : (⌊R / mu⌋₊ : ℝ) * mu ≤ V / mu ^ n := by
    rw [le_div_iff₀ (pow_pos hmu n)]
    calc (⌊R / mu⌋₊ : ℝ) * mu * mu ^ n = (⌊R / mu⌋₊ : ℝ) * mu ^ (n + 1) := by ring
      _ ≤ V := h
  rw [div_lt_iff₀ hmu] at h1
  nlinarith

section Witness

variable (c : ℕ) (q : Fin c → ℤ) (D : ℤ) (m T : ℝ)

/-- rows `(1/T, m D / q_i)` and `m e_i` -/
noncomputable def witnessMatrix : Matrix (Fin (c + 1)) (Fin (c + 1)) ℝ :=
  Matrix.of (Fin.cons (Fin.cons (1 / T) fun i => m * D / q i) fun i => Pi.single i.succ m)

theorem witnessMatrix_det : (witnessMatrix c q D m T).det = m ^ c / T := by
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · have hsub : (witnessMatrix c q D m T).submatrix (Fin.succAbove 0) Fin.succ
        = Matrix.diagonal fun _ => m := by
      ext i j
      simp [witnessMatrix, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
    rw [hsub, Matrix.det_diagonal]
    simp [witnessMatrix]
    ring
  · intro i _ hi
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hi
    have : witnessMatrix c q D m T k.succ 0 = 0 := by
      simp [witnessMatrix, (Fin.succ_ne_zero k).symm]
    simp [this]
  · simp

/-- Everything about the witness lattice that the three criteria use. -/
theorem witness_core (hm : 0 < m) (hT : 0 < T) (hq : ∀ i, 0 < q i) (r : ℤ) (hr : ¬ r ∣ 1)
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ s : ℤ, ∀ j : Fin c → ℤ, (s ≠ 0 ∨ j ≠ 0) →
      lam ≤ |(s : ℝ)| / T ∨ ∃ i, lam ≤ m * |(D : ℝ) * s - j i * q i| / q i) :
    lam ^ (c + 1) ≤ m ^ c / T ∧
    ((∀ s : ℤ, ∀ j : Fin c → ℤ, ¬ r ∣ s → |(s : ℝ)| < T →
        ¬ ∀ i, m * |(D : ℝ) * s - j i * q i| < q i) →
      (⌊1 / lam⌋₊ : ℝ) * lam ^ (c + 1) ≤ m ^ c / T) := by
  classical
  have hdet : (witnessMatrix c q D m T).det = m ^ c / T := witnessMatrix_det c q D m T
  have hdetpos : 0 < m ^ c / T := div_pos (pow_pos hm c) hT
  have hli : LinearIndependent ℝ (witnessMatrix c q D m T).row :=
    Matrix.linearIndependent_rows_of_det_ne_zero (A := witnessMatrix c q D m T)
      (by rw [hdet]; exact hdetpos.ne')
  set b : Module.Basis (Fin (c + 1)) ℝ (Fin (c + 1) → ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp) with hb
  have hbrow : ⇑b = (witnessMatrix c q D m T).row := by
    rw [hb]; exact coe_basisOfLinearIndependentOfCardEqFinrank _ _
  set L : AddSubgroup (Fin (c + 1) → ℝ) := (Submodule.span ℤ (Set.range b)).toAddSubgroup with hLdef
  have : Countable L := inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  have hF : IsAddFundamentalDomain L (ZSpan.fundamentalDomain b) volume :=
    ZSpan.isAddFundamentalDomain b volume
  have hFvol : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal (m ^ c / T) := by
    rw [ZSpan.volume_fundamentalDomain]
    have : Matrix.of ⇑b = witnessMatrix c q D m T := by rw [hbrow]; rfl
    rw [this, hdet, abs_of_pos hdetpos]
  -- coordinates of lattice vectors
  have hcoord : ∀ v ∈ L, ∃ s : ℤ, ∃ j : Fin c → ℤ, v 0 = s / T ∧
      (∀ i : Fin c, v i.succ = m * ((D : ℝ) * s - j i * q i) / q i) ∧ (v ≠ 0 → s ≠ 0 ∨ j ≠ 0) := by
    intro v hv
    have hv' : v ∈ Submodule.span ℤ (Set.range b) := hv
    obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv'
    have hcomp : ∀ t : Fin (c + 1), v t = ∑ a, (k a : ℝ) * witnessMatrix c q D m T a t := by
      intro t
      rw [← hk, Finset.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Pi.smul_apply, hbrow, zsmul_eq_mul]
      rfl
    refine ⟨k 0, fun i => -k i.succ, ?_, ?_, ?_⟩
    · rw [hcomp 0, Fin.sum_univ_succ]
      have : ∀ a : Fin c, witnessMatrix c q D m T a.succ 0 = 0 := fun a => by
        simp [witnessMatrix, (Fin.succ_ne_zero a).symm]
      simp only [this, mul_zero, Finset.sum_const_zero, add_zero]
      simp [witnessMatrix, div_eq_mul_inv]
    · intro i
      have hqi : (q i : ℝ) ≠ 0 := by exact_mod_cast (hq i).ne'
      rw [hcomp i.succ, Fin.sum_univ_succ]
      have h0 : witnessMatrix c q D m T 0 i.succ = m * D / q i := by simp [witnessMatrix]
      have hs : ∀ a : Fin c, witnessMatrix c q D m T a.succ i.succ = if a = i then m else 0 := by
        intro a
        simp [witnessMatrix, Pi.single_apply, eq_comm]
      simp only [h0, hs, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      push_cast
      field_simp
      ring
    · intro hv0
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2⟩ := hc
      apply hv0
      have hk0 : ∀ a, k a = 0 := by
        intro a
        refine Fin.cases h1 (fun i => ?_) a
        have := congrFun h2 i
        simpa using this
      rw [← hk]
      simp [hk0]
  have hLmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖ := by
    intro v hv hv0
    obtain ⟨s, j, h0, hi, hne⟩ := hcoord v hv
    rcases hmin s j (hne hv0) with h | ⟨i, h⟩
    · refine le_trans h (le_trans (le_of_eq ?_) (norm_le_pi_norm v 0))
      rw [h0, Real.norm_eq_abs, abs_div, abs_of_pos hT]
    · have hqi : (0 : ℝ) < q i := by exact_mod_cast hq i
      refine le_trans h (le_trans (le_of_eq ?_) (norm_le_pi_norm v i.succ))
      rw [hi i, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hm, abs_of_pos hqi]
  have hball : volume (ball (0 : Fin (c + 1) → ℝ) (lam / 2)) = ENNReal.ofReal (lam ^ (c + 1)) := by
    rw [Real.volume_pi_ball _ (by linarith : (0 : ℝ) < lam / 2), Fintype.card_fin]
    congr 2
    ring
  refine ⟨?_, ?_⟩
  · have h := le_trans (ball_le_image volume L _ hF lam hLmin) (measure_mono Set.inter_subset_right)
    rw [hball, hFvol, ENNReal.ofReal_le_ofReal_iff hdetpos.le] at h
    exact h
  · intro hno
    -- the subgroup of vectors with `r ∣ s`
    let L' : AddSubgroup (Fin (c + 1) → ℝ) :=
      { carrier := {v | ∃ k : ℤ, r ∣ k ∧ v 0 * T = k}
        zero_mem' := ⟨0, dvd_zero r, by simp⟩
        add_mem' := by
          rintro a b' ⟨k, hk, hka⟩ ⟨l, hl, hlb⟩
          refine ⟨k + l, dvd_add hk hl, ?_⟩
          rw [Pi.add_apply, add_mul, hka, hlb]; push_cast; ring
        neg_mem' := by
          rintro a ⟨k, hk, hka⟩
          refine ⟨-k, (dvd_neg).mpr hk, ?_⟩
          rw [Pi.neg_apply, neg_mul, hka]; push_cast; ring }
    have hmemL' : ∀ v : Fin (c + 1) → ℝ, ∀ s : ℤ, v 0 = s / T → (v ∈ L' ↔ r ∣ s) := by
      intro v s h0
      have hs : v 0 * T = s := by rw [h0]; field_simp
      constructor
      · rintro ⟨k, hk, hkv⟩
        have : (k : ℝ) = s := by rw [← hkv, hs]
        have : k = s := by exact_mod_cast this
        rwa [this] at hk
      · exact fun h => ⟨s, h, hs⟩
    have hb0L : b 0 ∈ L := Submodule.subset_span ⟨0, rfl⟩
    have hb0 : b 0 0 = ((1 : ℤ) : ℝ) / T := by
      rw [hbrow]
      simp [Matrix.row, witnessMatrix]
    have hb0L' : b 0 ∉ L' := fun h => hr ((hmemL' _ 1 hb0).mp h)
    set Sset : Set (Fin (c + 1) → ℝ) := {v | v ∈ L ∧ v ∉ L' ∧ ‖v‖ ≤ ‖b 0‖} with hSset
    have hfin : Sset.Finite := by
      refine Set.Finite.subset (ZSpan.setFinite_inter b
        (isBounded_closedBall (x := (0 : Fin (c + 1) → ℝ)) (r := ‖b 0‖))) ?_
      rintro v ⟨hv, _, hn⟩
      exact ⟨by simpa using hn, hv⟩
    obtain ⟨z, hzS, hzmin⟩ := Set.exists_min_image Sset (fun v => ‖v‖) hfin
      ⟨b 0, hb0L, hb0L', le_rfl⟩
    have hmin' : ∀ v ∈ L, v ∉ L' → ‖z‖ ≤ ‖v‖ := by
      intro v hv hv'
      by_cases h : ‖v‖ ≤ ‖b 0‖
      · exact hzmin v ⟨hv, hv', h⟩
      · exact le_trans hzS.2.2 (le_of_lt (not_le.mp h))
    have hz1 : 1 ≤ ‖z‖ := by
      by_contra hlt
      push Not at hlt
      obtain ⟨s, j, h0, hi, _⟩ := hcoord z hzS.1
      have hrs : ¬ r ∣ s := fun h => hzS.2.1 ((hmemL' z s h0).mpr h)
      have hsT : |(s : ℝ)| < T := by
        have := lt_of_le_of_lt (norm_le_pi_norm z 0) hlt
        rw [h0, Real.norm_eq_abs, abs_div, abs_of_pos hT, div_lt_one hT] at this
        exact this
      refine hno s j hrs hsT fun i => ?_
      have hqi : (0 : ℝ) < q i := by exact_mod_cast hq i
      have := lt_of_le_of_lt (norm_le_pi_norm z i.succ) hlt
      rw [hi i, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hm, abs_of_pos hqi, div_lt_one hqi] at this
      exact this
    have hN : (⌊1 / lam⌋₊ : ℝ) * lam ≤ ‖z‖ := by
      have h1 : (⌊1 / lam⌋₊ : ℝ) ≤ 1 / lam := Nat.floor_le (by positivity)
      rw [le_div_iff₀ hlam] at h1
      exact le_trans h1 hz1
    have h := packing_ball volume L L' _ hF z hzS.1 hzS.2.1 hmin' lam hlam hLmin ⌊1 / lam⌋₊ hN
    rw [hball, hFvol, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_le_ofReal_iff hdetpos.le] at h
    exact h

/-- Sharp form: `m^c / T < ⌊1/lam⌋ lam^(c+1)` gives a vector of the box with `r ∤ s`. -/
theorem nr_sharp (hm : 0 < m) (hT : 0 < T) (hq : ∀ i, 0 < q i) (r : ℤ) (hr : ¬ r ∣ 1)
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ s : ℤ, ∀ j : Fin c → ℤ, (s ≠ 0 ∨ j ≠ 0) →
      lam ≤ |(s : ℝ)| / T ∨ ∃ i, lam ≤ m * |(D : ℝ) * s - j i * q i| / q i)
    (hcrit : m ^ c / T < (⌊1 / lam⌋₊ : ℝ) * lam ^ (c + 1)) :
    ∃ s : ℤ, ∃ j : Fin c → ℤ, ¬ r ∣ s ∧ |(s : ℝ)| < T ∧ ∀ i, m * |(D : ℝ) * s - j i * q i| < q i := by
  by_contra h
  push Not at h
  have hcore := (witness_core c q D m T hm hT hq r hr lam hlam hmin).2
    (fun s j hrs hsT hall => by
      obtain ⟨i, hi⟩ := h s j hrs hsT
      exact absurd (hall i) (not_lt.mpr hi))
  linarith

/-- The form `T ≥ 2 (m/lam)^c`. -/
theorem nr_two (hm : 0 < m) (hT : 0 < T) (hq : ∀ i, 0 < q i) (r : ℤ) (hr : ¬ r ∣ 1)
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ s : ℤ, ∀ j : Fin c → ℤ, (s ≠ 0 ∨ j ≠ 0) →
      lam ≤ |(s : ℝ)| / T ∨ ∃ i, lam ≤ m * |(D : ℝ) * s - j i * q i| / q i)
    (hcrit : 2 * m ^ c ≤ T * lam ^ c) :
    ∃ s : ℤ, ∃ j : Fin c → ℤ, ¬ r ∣ s ∧ |(s : ℝ)| < T ∧ ∀ i, m * |(D : ℝ) * s - j i * q i| < q i := by
  have hle : m ^ c / T ≤ lam ^ c / 2 := by
    rw [div_le_div_iff₀ hT two_pos]; linarith
  have hlc : 0 < lam ^ c := pow_pos hlam c
  have hlam1 : lam ≤ 1 := by
    have h1 := (witness_core c q D m T hm hT hq r hr lam hlam hmin).1
    have h2 : lam ^ c * lam ≤ lam ^ c * (1 / 2) := by
      rw [← pow_succ]; linarith
    have := le_of_mul_le_mul_left h2 hlc
    linarith
  refine nr_sharp c q D m T hm hT hq r hr lam hlam hmin (lt_of_le_of_lt hle ?_)
  set N := ⌊1 / lam⌋₊ with hN
  have hN1 : 1 ≤ N := by
    rw [hN]; apply Nat.le_floor; rw [Nat.cast_one, le_div_iff₀ hlam]; linarith
  have hN2 : 1 / lam < N + 1 := Nat.lt_floor_add_one _
  rw [div_lt_iff₀ hlam] at hN2
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hhalf : 1 / 2 < (N : ℝ) * lam := by nlinarith
  have : lam ^ c * (1 / 2) < lam ^ c * ((N : ℝ) * lam) := mul_lt_mul_of_pos_left hhalf hlc
  calc lam ^ c / 2 = lam ^ c * (1 / 2) := by ring
    _ < lam ^ c * ((N : ℝ) * lam) := this
    _ = (N : ℝ) * lam ^ (c + 1) := by ring

/-- The form `T ≥ 2 eps^(-c)`: if every `0 < s < T` is at distance `eps` at some modulus (or has
`s / T ≥ m eps`) and `2 ≤ T eps^c`, then some positive `s < T` with `r ∤ D s` lies in the ball. -/
theorem nr_eps (hm : 1 ≤ m) (hT : 0 < T) (hq : ∀ i, 0 < q i) (r : ℤ) (hr : ¬ r ∣ 1)
    (hcop : IsCoprime r D) (eps : ℝ) (heps : 0 < eps) (hme : m * eps < 1)
    (hfar : ∀ s : ℤ, 0 < s → (s : ℝ) < T →
      m * eps ≤ s / T ∨ ∃ i, ∀ j : ℤ, eps * q i ≤ |(D : ℝ) * s - j * q i|)
    (hcrit : 2 ≤ T * eps ^ c) :
    ∃ s : ℤ, 0 < s ∧ (s : ℝ) < T ∧ ¬ r ∣ D * s ∧
      ∀ i, ∃ j : ℤ, m * |(D : ℝ) * s - j * q i| < q i := by
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  have hlam : 0 < m * eps := mul_pos hm0 heps
  have hmin : ∀ s : ℤ, ∀ j : Fin c → ℤ, (s ≠ 0 ∨ j ≠ 0) →
      m * eps ≤ |(s : ℝ)| / T ∨ ∃ i, m * eps ≤ m * |(D : ℝ) * s - j i * q i| / q i := by
    intro s j hne
    have hstep : ∀ i : Fin c, ∀ x : ℝ, eps * q i ≤ x → m * eps ≤ m * x / q i := by
      intro i x hx
      have hqi : (0 : ℝ) < q i := by exact_mod_cast hq i
      rw [le_div_iff₀ hqi, mul_assoc]
      exact mul_le_mul_of_nonneg_left hx hm0.le
    by_cases hs0 : s = 0
    · have hj : j ≠ 0 := by
        rcases hne with h | h
        · exact absurd hs0 h
        · exact h
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hj
      refine Or.inr ⟨i, hstep i _ ?_⟩
      have hqi : (0 : ℝ) < q i := by exact_mod_cast hq i
      have h1 : (1 : ℝ) ≤ |(j i : ℝ)| := by
        have : (1 : ℤ) ≤ |j i| := Int.one_le_abs (by simpa using hi)
        exact_mod_cast this
      have heps1 : eps ≤ 1 := by
        have : eps ≤ m * eps := le_mul_of_one_le_left heps.le hm
        linarith
      rw [hs0, Int.cast_zero, mul_zero, zero_sub, abs_neg, abs_mul, abs_of_pos hqi]
      exact mul_le_mul_of_nonneg_right (le_trans heps1 h1) hqi.le
    · by_cases hsT : T ≤ |(s : ℝ)|
      · refine Or.inl (le_trans hme.le ?_)
        rwa [le_div_iff₀ hT, one_mul]
      · push Not at hsT
        have habs : ((|s| : ℤ) : ℝ) = |(s : ℝ)| := Int.cast_abs
        rcases hfar |s| (abs_pos.mpr hs0) (by rw [habs]; exact hsT) with h | ⟨i, h⟩
        · exact Or.inl (by rwa [habs] at h)
        · refine Or.inr ⟨i, hstep i _ ?_⟩
          rcases abs_cases s with ⟨he, _⟩ | ⟨he, _⟩
          · have := h (j i); rwa [he] at this
          · have := h (-j i)
            rw [he] at this
            have e : (D : ℝ) * ((-s : ℤ) : ℝ) - ((-j i : ℤ) : ℝ) * q i
                = -((D : ℝ) * s - j i * q i) := by push_cast; ring
            rwa [e, abs_neg] at this
  have hcrit2 : 2 * m ^ c ≤ T * (m * eps) ^ c := by
    have := mul_le_mul_of_nonneg_right hcrit (pow_nonneg hm0.le c)
    calc 2 * m ^ c ≤ T * eps ^ c * m ^ c := this
      _ = T * (m * eps) ^ c := by rw [mul_pow]; ring
  obtain ⟨s, j, hrs, hsT, hbox⟩ := nr_two c q D m T hm0 hT hq r hr (m * eps) hlam hmin hcrit2
  have hs0 : s ≠ 0 := fun h => hrs (h ▸ dvd_zero r)
  have hrDs : ∀ t : ℤ, ¬ r ∣ t → ¬ r ∣ D * t := fun t ht h => ht (hcop.dvd_of_dvd_mul_left h)
  rcases lt_or_gt_of_ne hs0 with hneg | hpos
  · refine ⟨-s, neg_pos.mpr hneg, ?_, hrDs _ (fun h => hrs (dvd_neg.mp h)), fun i => ⟨-j i, ?_⟩⟩
    · have : ((-s : ℤ) : ℝ) ≤ |(s : ℝ)| := by push_cast; exact neg_le_abs _
      exact lt_of_le_of_lt this hsT
    · have e : (D : ℝ) * ((-s : ℤ) : ℝ) - ((-j i : ℤ) : ℝ) * q i
          = -((D : ℝ) * s - j i * q i) := by push_cast; ring
      rw [e, abs_neg]; exact hbox i
  · exact ⟨s, hpos, lt_of_le_of_lt (le_abs_self _) hsT, hrDs _ hrs, fun i => ⟨j i, hbox i⟩⟩

end Witness
