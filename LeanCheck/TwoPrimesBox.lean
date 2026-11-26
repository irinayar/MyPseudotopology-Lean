import Mathlib
import LeanCheck.TwoPrimesFormula

/-!
# The lattice-box estimate for an arbitrary nonsingular matrix of congruence rows

`J j` are independent and uniform on `N j` consecutive integers and `g = Σ w j * J j (mod Q)`, where
`Σ w j * u j ≡ 1 (mod Q)` for some `u`.  Let `B` be a nonsingular integer matrix whose rows `b`
satisfy `Σ b j * w j ≡ 0 (mod Q)`, and `r j` its column sums of absolute values.  The determinant of
`B` need **not** be `±Q`: the rows may span a proper sublattice of the congruence lattice.

* `box_bounds`: `Π (N j + 1 - r j)⁺ ≤ Q * n c ≤ Π (N j - 1 + r j)`, where `n c` counts the points
  of the box with residue `c`.
* `box_energy`: `Σ_{0<b<Q} |E e(b g / Q)|² ≤ (U - 1)(1 - L)`.

The proof compares volumes: the translates of the centred parallelepiped of the rows by the integer
points of one residue cover every point of space the same number of times.
-/

namespace TwoPrimesBox

open Finset Matrix MeasureTheory Real

variable {h : ℕ}

/-- The data: a modulus, weights, and a nonsingular matrix of rows in the congruence lattice. -/
structure Data (h : ℕ) where
  Q : ℕ
  hQ : 0 < Q
  w : Fin h → ℤ
  B : Matrix (Fin h) (Fin h) ℤ
  hdet : B.det ≠ 0
  hrow : ∀ i, (Q : ℤ) ∣ ∑ j, B i j * w j
  u : Fin h → ℤ
  hu : (Q : ℤ) ∣ (∑ j, w j * u j) - 1

namespace Data

variable (D : Data h)

/-- The matrix over the reals. -/
noncomputable def M : Matrix (Fin h) (Fin h) ℝ := D.B.map (Int.castRingHom ℝ)

/-- The column sums of absolute values. -/
def r (j : Fin h) : ℝ := ∑ i, |(D.B i j : ℝ)|

lemma M_det : IsUnit D.M.det := by
  have e : D.M.det = ((D.B.det : ℤ) : ℝ) := ((Int.castRingHom ℝ).map_det D.B).symm
  rw [e, isUnit_iff_ne_zero]
  exact_mod_cast D.hdet

/-- Coordinates of a point in the basis of the rows. -/
noncomputable def coord (x : Fin h → ℝ) : Fin h → ℝ := x ᵥ* D.M⁻¹

lemma coord_mul (x : Fin h → ℝ) : D.coord x ᵥ* D.M = x := by
  unfold coord
  rw [vecMul_vecMul, nonsing_inv_mul _ D.M_det, vecMul_one]

lemma coord_of (t : Fin h → ℝ) : D.coord (t ᵥ* D.M) = t := by
  unfold coord
  rw [vecMul_vecMul, mul_nonsing_inv _ D.M_det, vecMul_one]

/-- The centred half-open parallelepiped of the rows. -/
def P : Set (Fin h → ℝ) := {x | ∀ i, D.coord x i ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2)}

lemma abs_le_of_mem {x : Fin h → ℝ} (hx : x ∈ D.P) (j : Fin h) : |x j| ≤ D.r j / 2 := by
  have e : x j = ∑ i, D.coord x i * (D.B i j : ℝ) := by
    conv_lhs => rw [← D.coord_mul x]
    rfl
  rw [e]
  refine le_trans (abs_sum_le_sum_abs _ _) ?_
  rw [r, sum_div]
  refine sum_le_sum fun i _ => ?_
  rw [abs_mul]
  have h1 : |D.coord x i| ≤ 1 / 2 := by
    have := hx i
    rw [abs_le]
    exact ⟨this.1, this.2.le⟩
  have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (D.B i j : ℝ))
  linarith

lemma measurable_coord : Measurable D.coord := by
  unfold coord
  exact (Continuous.matrix_vecMul continuous_id continuous_const).measurable

lemma measurableSet_P : MeasurableSet D.P := by
  have e : D.P = D.coord ⁻¹' (Set.univ.pi fun _ => Set.Ico (-(1 / 2) : ℝ) (1 / 2)) := by
    ext x
    simp [P, Set.mem_pi]
  rw [e]
  exact D.measurable_coord (MeasurableSet.univ_pi fun _ => measurableSet_Ico)

lemma P_subset : D.P ⊆ Set.Icc (fun j => -(D.r j / 2)) (fun j => D.r j / 2) := by
  intro x hx
  exact ⟨fun j => (abs_le.mp (D.abs_le_of_mem hx j)).1, fun j => (abs_le.mp (D.abs_le_of_mem hx j)).2⟩

lemma volume_P_lt_top : volume D.P < ⊤ :=
  lt_of_le_of_lt (measure_mono D.P_subset) isCompact_Icc.measure_lt_top

noncomputable def V : ℝ := (volume D.P).toReal

/-- The lattice vector with coefficients `n`. -/
def lat (n : Fin h → ℤ) : Fin h → ℤ := n ᵥ* D.B

def res (z : Fin h → ℤ) : ℤ := ∑ j, D.w j * z j

lemma res_add (z z' : Fin h → ℤ) : D.res (z + z') = D.res z + D.res z' := by
  unfold res
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j _ => by rw [Pi.add_apply]; ring

lemma res_lat (n : Fin h → ℤ) : (D.Q : ℤ) ∣ D.res (D.lat n) := by
  have e : D.res (D.lat n) = ∑ i, n i * ∑ j, D.B i j * D.w j := by
    unfold res lat vecMul dotProduct
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  rw [e]
  exact dvd_sum fun i _ => (D.hrow i).mul_left _

def cast (z : Fin h → ℤ) : Fin h → ℝ := fun j => (z j : ℝ)

lemma cast_add (z z' : Fin h → ℤ) : cast (z + z') = cast z + cast z' := by
  funext j; simp [cast]

lemma cast_lat (n : Fin h → ℤ) : cast (D.lat n) = (fun i => (n i : ℝ)) ᵥ* D.M := by
  funext j
  simp only [cast, lat, vecMul, dotProduct, M, Matrix.map_apply, eq_intCast, Int.cast_sum,
    Int.cast_mul]

lemma coord_sub_lat (y : Fin h → ℝ) (n : Fin h → ℤ) (i : Fin h) :
    D.coord (y - cast (D.lat n)) i = D.coord y i - n i := by
  have e : D.coord (y - cast (D.lat n)) = D.coord y - fun i => (n i : ℝ) := by
    unfold coord
    rw [sub_vecMul]
    congr 1
    rw [D.cast_lat]
    exact D.coord_of _
  rw [e, Pi.sub_apply]

/-- The integer points `z` with `x - z` in the parallelepiped. -/
def T (x : Fin h → ℝ) : Set (Fin h → ℤ) := {z | x - cast z ∈ D.P}

noncomputable def shift (x : Fin h → ℝ) (z : Fin h → ℤ) : Fin h → ℤ :=
  fun i => ⌊D.coord (x - cast z) i + 1 / 2⌋

/-- Reduction of an integer point into `T x` by a lattice vector. -/
noncomputable def red (x : Fin h → ℝ) (z : Fin h → ℤ) : Fin h → ℤ := z + D.lat (D.shift x z)

lemma red_mem (x : Fin h → ℝ) (z : Fin h → ℤ) : D.red x z ∈ D.T x := by
  intro i
  have e : x - cast (D.red x z) = (x - cast z) - cast (D.lat (D.shift x z)) := by
    unfold red
    rw [cast_add]
    abel
  rw [e, D.coord_sub_lat]
  unfold shift
  have h1 := Int.floor_le (D.coord (x - cast z) i + 1 / 2)
  have h2 := Int.lt_floor_add_one (D.coord (x - cast z) i + 1 / 2)
  exact ⟨by linarith, by linarith⟩

/-- Two points of `T x` which differ by a lattice vector are equal. -/
lemma eq_of_mem_T {x : Fin h → ℝ} {z z' : Fin h → ℤ} (hz : z ∈ D.T x) (hz' : z' ∈ D.T x)
    (n : Fin h → ℤ) (e : z' = z + D.lat n) : z' = z := by
  have hn : n = 0 := by
    funext i
    have h1 := hz i
    have h2 := hz' i
    have e1 : x - cast z' = (x - cast z) - cast (D.lat n) := by
      rw [e, cast_add]; abel
    rw [e1, D.coord_sub_lat] at h2
    have h3 : (n i : ℝ) < 1 := by linarith [h1.1, h1.2, h2.1, h2.2]
    have h4 : (-1 : ℝ) < (n i : ℝ) := by linarith [h1.1, h1.2, h2.1, h2.2]
    have h5 : n i < 1 := by exact_mod_cast h3
    have h6 : -1 < n i := by exact_mod_cast h4
    simp only [Pi.zero_apply]
    omega
  rw [e, hn]
  simp [lat]

lemma T_finite (x : Fin h → ℝ) : (D.T x).Finite := by
  refine Set.Finite.subset (s := (Fintype.piFinset fun j =>
    Icc ⌈x j - D.r j / 2⌉ ⌊x j + D.r j / 2⌋ : Set (Fin h → ℤ))) (Finset.finite_toSet _) ?_
  intro z hz
  rw [Fintype.coe_piFinset]
  intro j _
  have h1 := abs_le.mp (D.abs_le_of_mem hz j)
  simp only [Pi.sub_apply, cast] at h1
  simp only [mem_coe, mem_Icc]
  exact ⟨Int.ceil_le.mpr (by linarith [h1.2]), Int.le_floor.mpr (by linarith [h1.1])⟩

noncomputable def fiber (x : Fin h → ℝ) (c : ℤ) : Finset (Fin h → ℤ) :=
  (D.T_finite x).toFinset.filter fun z => (D.Q : ℤ) ∣ D.res z - c

lemma mem_fiber {x : Fin h → ℝ} {c : ℤ} {z : Fin h → ℤ} :
    z ∈ D.fiber x c ↔ z ∈ D.T x ∧ (D.Q : ℤ) ∣ D.res z - c := by
  rw [fiber, mem_filter, Set.Finite.mem_toFinset]

lemma card_fiber_le (x x' : Fin h → ℝ) (c c' : ℤ) :
    (D.fiber x c).card ≤ (D.fiber x' c').card := by
  set s : Fin h → ℤ := fun j => (c' - c) * D.u j with hs
  have hsres : (D.Q : ℤ) ∣ D.res s - (c' - c) := by
    have e : D.res s - (c' - c) = (c' - c) * ((∑ j, D.w j * D.u j) - 1) := by
      unfold res
      rw [hs, mul_sub, mul_one, mul_sum]
      congr 1
      exact sum_congr rfl fun j _ => by ring
    rw [e]
    exact D.hu.mul_left _
  refine card_le_card_of_injOn (fun z => D.red x' (z + s)) (fun z hz => ?_) ?_
  · rw [mem_coe, D.mem_fiber] at hz ⊢
    refine ⟨D.red_mem _ _, ?_⟩
    have e : D.res (D.red x' (z + s)) - c'
        = (D.res z - c) + (D.res s - (c' - c)) + D.res (D.lat (D.shift x' (z + s))) := by
      unfold red
      rw [D.res_add, D.res_add]
      ring
    rw [e]
    exact dvd_add (dvd_add hz.2 hsres) (D.res_lat _)
  · intro z1 h1 z2 h2 e
    rw [mem_coe, D.mem_fiber] at h1 h2
    have e' : z2 = z1 + D.lat (D.shift x' (z1 + s) - D.shift x' (z2 + s)) := by
      have hl : D.lat (D.shift x' (z1 + s) - D.shift x' (z2 + s))
          = D.lat (D.shift x' (z1 + s)) - D.lat (D.shift x' (z2 + s)) := by
        unfold lat
        exact sub_vecMul _ _ _
      rw [hl]
      simp only [red] at e
      funext j
      have := congrFun e j
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      omega
    exact (D.eq_of_mem_T h1.1 h2.1 _ e').symm

/-- Every residue occurs equally often in every `T x`. -/
noncomputable def m : ℕ := (D.fiber 0 0).card

lemma card_fiber (x : Fin h → ℝ) (c : ℤ) : (D.fiber x c).card = D.m :=
  le_antisymm (D.card_fiber_le x 0 c 0) (D.card_fiber_le 0 x 0 c)

lemma m_pos : 0 < D.m := by
  have hz := D.red_mem 0 0
  set z := D.red 0 0 with hzdef
  have : z ∈ D.fiber 0 (D.res z) := D.mem_fiber.mpr ⟨hz, by simp⟩
  have h1 : 0 < (D.fiber 0 (D.res z)).card := card_pos.mpr ⟨z, this⟩
  rwa [D.card_fiber] at h1

/-! ## Volumes -/

def box (a : Fin h → ℤ) (N : Fin h → ℕ) : Finset (Fin h → ℤ) :=
  Fintype.piFinset fun j => Ico (a j) (a j + N j)

noncomputable def cls (a : Fin h → ℤ) (N : Fin h → ℕ) (c : ℤ) : Finset (Fin h → ℤ) :=
  (box a N).filter fun z => (D.Q : ℤ) ∣ D.res z - c

noncomputable def ind (z : Fin h → ℤ) (x : Fin h → ℝ) : ℝ := (D.T x).indicator (fun _ => 1) z

lemma ind_eq_indicator (z : Fin h → ℤ) :
    D.ind z = ((fun x => x - cast z) ⁻¹' D.P).indicator fun _ => (1 : ℝ) := by
  funext x
  unfold ind Set.indicator T
  rfl

lemma integrable_ind (z : Fin h → ℤ) : Integrable (D.ind z) := by
  rw [D.ind_eq_indicator]
  refine (integrable_indicator_iff ?_).mpr (integrableOn_const ?_)
  · exact (measurable_id.sub_const (cast z)) D.measurableSet_P
  · simp only [sub_eq_add_neg]
    rw [measure_preimage_add_right]
    exact D.volume_P_lt_top.ne

lemma integral_ind (z : Fin h → ℤ) : ∫ x, D.ind z x = D.V := by
  rw [D.ind_eq_indicator, integral_indicator_const]
  · unfold V Measure.real
    simp only [sub_eq_add_neg]
    rw [measure_preimage_add_right, smul_eq_mul, mul_one]
  · exact (measurable_id.sub_const (cast z)) D.measurableSet_P

lemma sum_ind (S : Finset (Fin h → ℤ)) (x : Fin h → ℝ) [DecidablePred (· ∈ D.T x)] :
    ∑ z ∈ S, D.ind z x = ((S.filter fun z => z ∈ D.T x).card : ℝ) := by
  rw [card_filter, Nat.cast_sum]
  refine sum_congr rfl fun z _ => ?_
  unfold ind Set.indicator
  split <;> simp

lemma volume_toReal_Ioo (l u : Fin h → ℝ) :
    (volume (Set.univ.pi fun j => Set.Ioo (l j) (u j))).toReal = ∏ j, max (u j - l j) 0 := by
  rw [volume_pi_pi, ENNReal.toReal_prod]
  refine prod_congr rfl fun j _ => ?_
  rw [Real.volume_Ioo, ENNReal.toReal_ofReal']

lemma volume_toReal_Icc (l u : Fin h → ℝ) (hlu : ∀ j, l j ≤ u j) :
    (volume (Set.univ.pi fun j => Set.Icc (l j) (u j))).toReal = ∏ j, (u j - l j) := by
  rw [volume_pi_pi, ENNReal.toReal_prod]
  refine prod_congr rfl fun j _ => ?_
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [hlu j])]

lemma r_one_le (j : Fin h) : 1 ≤ D.r j := by
  have hex : ∃ i, D.B i j ≠ 0 := by
    by_contra hc
    push Not at hc
    exact D.hdet (det_eq_zero_of_column_eq_zero j hc)
  obtain ⟨i, hi⟩ := hex
  unfold r
  refine le_trans ?_ (single_le_sum (fun i _ => abs_nonneg (D.B i j : ℝ)) (mem_univ i))
  have : 1 ≤ |D.B i j| := Int.one_le_abs hi
  exact_mod_cast this

/-- The two volume comparisons. -/
lemma volume_bounds (a : Fin h → ℤ) (N : Fin h → ℕ) (hN : ∀ j, 1 ≤ N j) (c : ℤ) :
    (D.m : ℝ) * ∏ j, max ((N j : ℝ) + 1 - D.r j) 0 ≤ ((D.cls a N c).card : ℝ) * D.V ∧
      ((D.cls a N c).card : ℝ) * D.V ≤ (D.m : ℝ) * ∏ j, ((N j : ℝ) - 1 + D.r j) := by
  classical
  set S := D.cls a N c with hS
  have hint : ∫ x, ∑ z ∈ S, D.ind z x = (S.card : ℝ) * D.V := by
    rw [integral_finsetSum _ fun z _ => D.integrable_ind z,
      sum_congr rfl fun z _ => D.integral_ind z, sum_const, nsmul_eq_mul]
  have hsumint : Integrable fun x => ∑ z ∈ S, D.ind z x :=
    integrable_finsetSum _ fun z _ => D.integrable_ind z
  have hmem : ∀ x, ∀ z ∈ S, z ∈ D.T x → z ∈ D.fiber x c := by
    intro x z hz hT
    exact D.mem_fiber.mpr ⟨hT, (mem_filter.mp hz).2⟩
  have hbox : ∀ z ∈ S, ∀ j, a j ≤ z j ∧ z j ≤ a j + N j - 1 := by
    intro z hz j
    have h1 := Fintype.mem_piFinset.mp (mem_filter.mp hz).1 j
    rw [mem_Ico] at h1
    omega
  constructor
  · -- lower bound
    set inner : Set (Fin h → ℝ) := Set.univ.pi fun j =>
      Set.Ioo ((a j : ℝ) - 1 + D.r j / 2) ((a j : ℝ) + N j - D.r j / 2) with hinner
    have hm : MeasurableSet inner := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
    have hfin : volume inner ≠ ⊤ := by
      rw [hinner, volume_pi_pi]
      refine ENNReal.prod_ne_top fun j _ => ?_
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    have hpt : ∀ x, inner.indicator (fun _ => (D.m : ℝ)) x ≤ ∑ z ∈ S, D.ind z x := by
      intro x
      by_cases hx : x ∈ inner
      · rw [Set.indicator_of_mem hx, D.sum_ind, ← D.card_fiber x c]
        refine Nat.cast_le.mpr (card_le_card fun z hz => ?_)
        obtain ⟨hT, hres⟩ := D.mem_fiber.mp hz
        refine mem_filter.mpr ⟨mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, hres⟩, hT⟩
        have h1 := abs_le.mp (D.abs_le_of_mem hT j)
        simp only [Pi.sub_apply, cast] at h1
        have h2 := hx j (Set.mem_univ _)
        have h3 : ((a j - 1 : ℤ) : ℝ) < (z j : ℝ) := by
          push_cast
          linarith [h1.2, h2.1]
        have h4 : (z j : ℝ) < ((a j + N j : ℤ) : ℝ) := by
          push_cast
          linarith [h1.1, h2.2]
        have h5 : a j - 1 < z j := by exact_mod_cast h3
        have h6 : z j < a j + N j := by exact_mod_cast h4
        rw [mem_Ico]
        omega
      · rw [Set.indicator_of_notMem hx]
        exact sum_nonneg fun z _ => by
          unfold ind
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have h := integral_mono ((integrable_indicator_iff hm).mpr (integrableOn_const hfin)) hsumint hpt
    rw [hint, integral_indicator_const _ hm, smul_eq_mul] at h
    have e : volume.real inner = ∏ j, max ((N j : ℝ) + 1 - D.r j) 0 := by
      unfold Measure.real
      rw [hinner, volume_toReal_Ioo]
      refine prod_congr rfl fun j _ => ?_
      congr 1
      ring
    rw [e, mul_comm] at h
    exact h
  · -- upper bound
    set outer : Set (Fin h → ℝ) := Set.univ.pi fun j =>
      Set.Icc ((a j : ℝ) - D.r j / 2) ((a j : ℝ) + N j - 1 + D.r j / 2) with houter
    have hm : MeasurableSet outer := MeasurableSet.univ_pi fun _ => measurableSet_Icc
    have hfin : volume outer ≠ ⊤ := by
      rw [houter, volume_pi_pi]
      refine ENNReal.prod_ne_top fun j _ => ?_
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hpt : ∀ x, ∑ z ∈ S, D.ind z x ≤ outer.indicator (fun _ => (D.m : ℝ)) x := by
      intro x
      rw [D.sum_ind]
      by_cases hx : x ∈ outer
      · rw [Set.indicator_of_mem hx, ← D.card_fiber x c]
        refine Nat.cast_le.mpr (card_le_card fun z hz => ?_)
        obtain ⟨hzS, hT⟩ := mem_filter.mp hz
        exact hmem x z hzS hT
      · rw [Set.indicator_of_notMem hx]
        have : (S.filter fun z => z ∈ D.T x) = ∅ := by
          refine filter_eq_empty_iff.mpr fun z hz hT => hx fun j _ => ?_
          have h1 := abs_le.mp (D.abs_le_of_mem hT j)
          simp only [Pi.sub_apply, cast] at h1
          have h2 := hbox z hz j
          have h3 : (a j : ℝ) ≤ (z j : ℝ) := by exact_mod_cast h2.1
          have h4 : (z j : ℝ) ≤ (a j : ℝ) + N j - 1 := by exact_mod_cast h2.2
          exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
        rw [this, card_empty, Nat.cast_zero]
    have h := integral_mono hsumint ((integrable_indicator_iff hm).mpr (integrableOn_const hfin)) hpt
    rw [hint, integral_indicator_const _ hm, smul_eq_mul] at h
    have e : volume.real outer = ∏ j, ((N j : ℝ) - 1 + D.r j) := by
      unfold Measure.real
      rw [houter, volume_toReal_Icc]
      · refine prod_congr rfl fun j _ => ?_
        ring
      · intro j
        have h1 : (1 : ℝ) ≤ N j := by exact_mod_cast hN j
        have := D.r_one_le j
        linarith
    rw [e, mul_comm (∏ j, ((N j : ℝ) - 1 + D.r j))] at h
    exact h

/-- The residue classes partition the box. -/
lemma sum_cls (a : Fin h → ℤ) (N : Fin h → ℕ) :
    ∑ c ∈ range D.Q, (D.cls a N c).card = ∏ j, N j := by
  have hQ : (0 : ℤ) < D.Q := by exact_mod_cast D.hQ
  have hbox : (box a N).card = ∏ j, N j := by
    unfold box
    rw [Fintype.card_piFinset]
    refine prod_congr rfl fun j _ => ?_
    rw [Int.card_Ico]
    omega
  rw [← hbox]
  have hmap : ∀ z ∈ box a N, (D.res z % (D.Q : ℤ)).toNat ∈ range D.Q := by
    intro z _
    have h1 := Int.emod_nonneg (D.res z) hQ.ne'
    have h2 := Int.emod_lt_of_pos (D.res z) hQ
    rw [mem_range]
    omega
  rw [card_eq_sum_card_fiberwise hmap]
  refine sum_congr rfl fun c hc => ?_
  congr 1
  unfold cls
  refine filter_congr fun z _ => ?_
  have hc' := mem_range.mp hc
  have h1 := Int.emod_nonneg (D.res z) hQ.ne'
  have h3 : (c : ℤ) % (D.Q : ℤ) = c := Int.emod_eq_of_lt (by omega) (by omega)
  constructor
  · intro hd
    have h4 : (c : ℤ) % (D.Q : ℤ) = D.res z % (D.Q : ℤ) := Int.modEq_iff_dvd.mpr hd
    omega
  · intro he
    refine Int.modEq_iff_dvd.mp ?_
    show (c : ℤ) % (D.Q : ℤ) = D.res z % (D.Q : ℤ)
    omega

/-- The volume of the parallelepiped is `Q * m`. -/
lemma V_eq : D.V = (D.Q : ℝ) * D.m := by
  have hlim : ∀ s : Fin h → ℝ, Filter.Tendsto (fun K : ℕ => ∏ j, ((K : ℝ) + s j) / K)
      Filter.atTop (nhds 1) := by
    intro s
    have h1 : ∀ j : Fin h, Filter.Tendsto (fun K : ℕ => ((K : ℝ) + s j) / K) Filter.atTop
        (nhds 1) := by
      intro j
      have h2 : Filter.Tendsto (fun K : ℕ => 1 + s j / (K : ℝ)) Filter.atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (s j))
      rw [add_zero] at h2
      refine h2.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with K hK
      have : (K : ℝ) ≠ 0 := by positivity
      field_simp
    have := tendsto_finsetProd (univ : Finset (Fin h)) fun j _ => h1 j
    simpa using this
  have hsandwich : ∀ᶠ K : ℕ in Filter.atTop,
      (D.Q : ℝ) * D.m * ∏ j, ((K : ℝ) + (1 - D.r j)) / K ≤ D.V ∧
        D.V ≤ (D.Q : ℝ) * D.m * ∏ j, ((K : ℝ) + (D.r j - 1)) / K := by
    obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ j, D.r j ≤ R := by
      refine ⟨⌈∑ j, D.r j⌉₊, fun j => le_trans ?_ (Nat.le_ceil _)⟩
      exact single_le_sum (f := D.r)
        (fun j _ => le_trans zero_le_one (D.r_one_le j)) (mem_univ j)
    filter_upwards [Filter.eventually_ge_atTop (R + 1)] with K hK
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    have hKh : (0 : ℝ) < (K : ℝ) ^ h := by positivity
    have hsum : ∑ c ∈ range D.Q, ((D.cls 0 (fun _ => K) c).card : ℝ) * D.V = (K : ℝ) ^ h * D.V := by
      rw [← sum_mul, ← Nat.cast_sum, D.sum_cls, prod_const, card_univ, Fintype.card_fin,
        Nat.cast_pow]
    have hb := fun c : ℤ => D.volume_bounds 0 (fun _ => K) (fun _ => by omega) c
    have hprod : ∀ s : Fin h → ℝ, ∏ j, ((K : ℝ) + s j) / K = (∏ j, ((K : ℝ) + s j)) / (K : ℝ) ^ h := by
      intro s
      rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin]
    have e1 : ∏ j, max ((K : ℝ) + 1 - D.r j) 0 = ∏ j, ((K : ℝ) + (1 - D.r j)) := by
      refine prod_congr rfl fun j _ => ?_
      have h1 : D.r j ≤ K := le_trans (hR j) (by exact_mod_cast (by omega : R ≤ K))
      rw [max_eq_left (by linarith)]
      ring
    have e2 : ∏ j, ((K : ℝ) - 1 + D.r j) = ∏ j, ((K : ℝ) + (D.r j - 1)) :=
      prod_congr rfl fun j _ => by ring
    have hlow : ∑ _c ∈ range D.Q, (D.m : ℝ) * ∏ j, ((K : ℝ) + (1 - D.r j))
        ≤ (K : ℝ) ^ h * D.V := by
      rw [← hsum, ← e1]
      exact sum_le_sum fun c _ => (hb c).1
    have hup : (K : ℝ) ^ h * D.V
        ≤ ∑ _c ∈ range D.Q, (D.m : ℝ) * ∏ j, ((K : ℝ) + (D.r j - 1)) := by
      rw [← hsum, ← e2]
      exact sum_le_sum fun c _ => (hb c).2
    rw [sum_const, card_range, nsmul_eq_mul, ← mul_assoc] at hlow hup
    constructor
    · rw [hprod, mul_div_assoc', div_le_iff₀ hKh, mul_comm D.V]
      exact hlow
    · rw [hprod, mul_div_assoc', le_div_iff₀ hKh, mul_comm D.V]
      exact hup
  have h1 : Filter.Tendsto (fun K : ℕ => (D.Q : ℝ) * D.m * ∏ j, ((K : ℝ) + (1 - D.r j)) / K)
      Filter.atTop (nhds ((D.Q : ℝ) * D.m * 1)) := (hlim _).const_mul _
  have h2 : Filter.Tendsto (fun K : ℕ => (D.Q : ℝ) * D.m * ∏ j, ((K : ℝ) + (D.r j - 1)) / K)
      Filter.atTop (nhds ((D.Q : ℝ) * D.m * 1)) := (hlim _).const_mul _
  rw [mul_one] at h1 h2
  refine le_antisymm ?_ ?_
  · exact ge_of_tendsto h2 (hsandwich.mono fun K hK => hK.2)
  · exact le_of_tendsto h1 (hsandwich.mono fun K hK => hK.1)

/-- **The lattice-box estimate.** -/
theorem box_bounds (a : Fin h → ℤ) (N : Fin h → ℕ) (hN : ∀ j, 1 ≤ N j) (c : ℤ) :
    ∏ j, max ((N j : ℝ) + 1 - D.r j) 0 ≤ (D.Q : ℝ) * (D.cls a N c).card ∧
      (D.Q : ℝ) * (D.cls a N c).card ≤ ∏ j, ((N j : ℝ) - 1 + D.r j) := by
  have hm : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
  have h := D.volume_bounds a N hN c
  rw [D.V_eq] at h
  have e : ((D.cls a N c).card : ℝ) * ((D.Q : ℝ) * D.m)
      = (D.m : ℝ) * ((D.Q : ℝ) * (D.cls a N c).card) := by ring
  rw [e] at h
  exact ⟨le_of_mul_le_mul_left h.1 hm, le_of_mul_le_mul_left h.2 hm⟩

/-! ## The Fourier consequence -/

noncomputable def U (N : Fin h → ℕ) : ℝ := ∏ j, ((N j : ℝ) - 1 + D.r j) / N j

noncomputable def L (N : Fin h → ℕ) : ℝ := ∏ j, max ((N j : ℝ) + 1 - D.r j) 0 / N j

/-- `|E e(b g / Q)|²` for the box. -/
noncomputable def coeff (a : Fin h → ℤ) (N : Fin h → ℕ) (b : ℕ) : ℝ :=
  Complex.normSq (∑ z ∈ box a N, TwoPrimesFormula.e ((b : ℝ) * D.res z / D.Q))
    / ((∏ j, N j : ℕ) : ℝ) ^ 2

lemma sum_normSq (a : Fin h → ℤ) (N : Fin h → ℕ) :
    ∑ b ∈ range D.Q, Complex.normSq (∑ z ∈ box a N, TwoPrimesFormula.e ((b : ℝ) * D.res z / D.Q))
      = (D.Q : ℝ) * ∑ c ∈ range D.Q, ((D.cls a N c).card : ℝ) ^ 2 := by
  have hQ : (0 : ℤ) < D.Q := by exact_mod_cast D.hQ
  have hexp : ∀ b : ℕ,
      Complex.normSq (∑ z ∈ box a N, TwoPrimesFormula.e ((b : ℝ) * D.res z / D.Q))
        = ∑ z ∈ box a N, ∑ z' ∈ box a N,
            Real.cos (2 * π * ((b : ℝ) * ((D.res z - D.res z' : ℤ) : ℝ) / D.Q)) := by
    intro b
    have hre : ∀ x : ℝ, (TwoPrimesFormula.e x).re = Real.cos (2 * π * x)
        ∧ (TwoPrimesFormula.e x).im = Real.sin (2 * π * x) := by
      intro x
      unfold TwoPrimesFormula.e
      exact ⟨Complex.exp_ofReal_mul_I_re _, Complex.exp_ofReal_mul_I_im _⟩
    rw [Complex.normSq_apply, Complex.re_sum, Complex.im_sum, sum_mul_sum, sum_mul_sum,
      ← sum_add_distrib]
    refine sum_congr rfl fun z _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun z' _ => ?_
    rw [(hre _).1, (hre _).1, (hre _).2, (hre _).2, ← Real.cos_sub]
    congr 1
    push_cast
    ring
  rw [sum_congr rfl fun b _ => hexp b, sum_comm]
  have horth : ∀ z z' : Fin h → ℤ,
      ∑ b ∈ range D.Q, Real.cos (2 * π * ((b : ℝ) * ((D.res z - D.res z' : ℤ) : ℝ) / D.Q))
        = if (D.Q : ℤ) ∣ D.res z - D.res z' then (D.Q : ℝ) else 0 := by
    intro z z'
    exact TwoPrimesFormula.sum_cos_mod D.Q D.hQ _
  have h1 : ∀ z ∈ box a N, ∑ b ∈ range D.Q, ∑ z' ∈ box a N,
        Real.cos (2 * π * ((b : ℝ) * ((D.res z - D.res z' : ℤ) : ℝ) / D.Q))
      = (D.Q : ℝ) * (D.cls a N (D.res z % D.Q).toNat).card := by
    intro z _
    rw [sum_comm, sum_congr rfl fun z' _ => horth z z', sum_ite, sum_const, sum_const_zero,
      add_zero, nsmul_eq_mul, mul_comm]
    congr 2
    unfold cls
    congr 1
    refine filter_congr fun z' _ => ?_
    have h2 := Int.emod_nonneg (D.res z) hQ.ne'
    rw [Int.toNat_of_nonneg h2]
    have h3 : (D.Q : ℤ) ∣ D.res z - D.res z % D.Q := Int.dvd_self_sub_emod
    constructor
    · intro hd
      have := (dvd_sub h3 hd)
      have e : D.res z - D.res z % D.Q - (D.res z - D.res z') = D.res z' - D.res z % D.Q := by ring
      rwa [e] at this
    · intro hd
      have := dvd_sub h3 hd
      have e : D.res z - D.res z % D.Q - (D.res z' - D.res z % D.Q) = D.res z - D.res z' := by ring
      rwa [e] at this
  rw [sum_congr rfl h1, ← mul_sum]
  congr 1
  have hmap : ∀ z ∈ box a N, (D.res z % (D.Q : ℤ)).toNat ∈ range D.Q := by
    intro z _
    have h1 := Int.emod_nonneg (D.res z) hQ.ne'
    have h2 := Int.emod_lt_of_pos (D.res z) hQ
    rw [mem_range]
    omega
  rw [← sum_fiberwise_of_maps_to hmap]
  refine sum_congr rfl fun c hc => ?_
  have hfil : ((box a N).filter fun z => (D.res z % (D.Q : ℤ)).toNat = c) = D.cls a N c := by
    unfold cls
    refine filter_congr fun z _ => ?_
    have hc' := mem_range.mp hc
    have h2 := Int.emod_nonneg (D.res z) hQ.ne'
    have h3 : (c : ℤ) % (D.Q : ℤ) = c := Int.emod_eq_of_lt (by omega) (by omega)
    constructor
    · intro he
      refine Int.modEq_iff_dvd.mp ?_
      show (c : ℤ) % (D.Q : ℤ) = D.res z % (D.Q : ℤ)
      omega
    · intro hd
      have h4 : (c : ℤ) % (D.Q : ℤ) = D.res z % (D.Q : ℤ) := Int.modEq_iff_dvd.mpr hd
      omega
  have hcongr : ∀ z ∈ (box a N).filter (fun z => (D.res z % (D.Q : ℤ)).toNat = c),
      ((D.cls a N (D.res z % D.Q).toNat).card : ℝ) = ((D.cls a N c).card : ℝ) := by
    intro z hz
    rw [(mem_filter.mp hz).2]
  rw [sum_congr rfl hcongr, sum_const, hfil, nsmul_eq_mul, sq]

/-- **The Fourier consequence of the lattice-box estimate.** -/
theorem box_energy (a : Fin h → ℤ) (N : Fin h → ℕ) (hN : ∀ j, 1 ≤ N j) :
    ∑ b ∈ Ico 1 D.Q, D.coeff a N b ≤ (D.U N - 1) * (1 - D.L N) := by
  have hQ0 : (0 : ℝ) < D.Q := by exact_mod_cast D.hQ
  obtain ⟨T0, hTd⟩ : ∃ T0 : ℝ, T0 = ((∏ j, N j : ℕ) : ℝ) := ⟨_, rfl⟩
  have hT0 : 0 < T0 := by
    have : 0 < ∏ j, N j := prod_pos fun j _ => hN j
    rw [hTd]
    exact_mod_cast this
  have hTp : T0 = ∏ j, (N j : ℝ) := by rw [hTd, Nat.cast_prod]
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, ∀ c : ℕ, f c = (D.Q : ℝ) * (D.cls a N c).card / T0 :=
    ⟨_, fun _ => rfl⟩
  have hfU : ∀ c, D.L N ≤ f c ∧ f c ≤ D.U N := by
    intro c
    have h := D.box_bounds a N hN c
    have eU : D.U N = (∏ j, ((N j : ℝ) - 1 + D.r j)) / T0 := by
      rw [U, prod_div_distrib, hTp]
    have eL : D.L N = (∏ j, max ((N j : ℝ) + 1 - D.r j) 0) / T0 := by
      rw [L, prod_div_distrib, hTp]
    rw [eU, eL, hf]
    exact ⟨div_le_div_of_nonneg_right h.1 hT0.le, div_le_div_of_nonneg_right h.2 hT0.le⟩
  have hsumf : ∑ c ∈ range D.Q, f c = D.Q := by
    simp only [hf]
    rw [← sum_div, ← mul_sum, ← Nat.cast_sum, D.sum_cls, ← hTd, mul_div_assoc, div_self hT0.ne',
      mul_one]
  have hsq : ∑ c ∈ range D.Q, f c ^ 2 - D.Q ≤ D.Q * ((D.U N - 1) * (1 - D.L N)) := by
    have h1 : ∀ c ∈ range D.Q, f c ^ 2 ≤ (D.L N + D.U N) * f c - D.L N * D.U N := by
      intro c _
      have h2 := mul_nonneg (sub_nonneg.mpr (hfU c).1) (sub_nonneg.mpr (hfU c).2)
      nlinarith
    have h3 := sum_le_sum h1
    rw [sum_sub_distrib, ← mul_sum, hsumf, sum_const, card_range, nsmul_eq_mul] at h3
    nlinarith
  have hcoeff : ∑ b ∈ range D.Q, D.coeff a N b = (∑ c ∈ range D.Q, f c ^ 2) / D.Q := by
    have e1 : ∑ c ∈ range D.Q, f c ^ 2
        = (D.Q : ℝ) ^ 2 * (∑ c ∈ range D.Q, ((D.cls a N c).card : ℝ) ^ 2) / T0 ^ 2 := by
      rw [mul_sum, sum_div]
      refine sum_congr rfl fun c _ => ?_
      rw [hf]
      ring
    have e2 : ∑ b ∈ range D.Q, D.coeff a N b
        = (D.Q : ℝ) * (∑ c ∈ range D.Q, ((D.cls a N c).card : ℝ) ^ 2) / T0 ^ 2 := by
      unfold coeff
      rw [← sum_div, D.sum_normSq, hTd]
    rw [e1, e2, eq_div_iff hQ0.ne']
    generalize (∑ c ∈ range D.Q, ((D.cls a N c).card : ℝ) ^ 2) = Sq
    generalize ((D.Q : ℕ) : ℝ) = q
    ring
  have h0 : D.coeff a N 0 = 1 := by
    unfold coeff
    have e : ∀ z ∈ box a N, TwoPrimesFormula.e (((0 : ℕ) : ℝ) * D.res z / D.Q) = 1 := by
      intro z _
      simp [TwoPrimesFormula.e]
    rw [sum_congr rfl e, sum_const, nsmul_eq_mul, mul_one]
    have hc : (box a N).card = ∏ j, N j := by
      unfold box
      rw [Fintype.card_piFinset]
      refine prod_congr rfl fun j _ => ?_
      rw [Int.card_Ico]
      omega
    rw [hc, Complex.normSq_natCast, ← hTd, ← sq, div_self (pow_ne_zero 2 hT0.ne')]
  have hsplit : ∑ b ∈ range D.Q, D.coeff a N b = D.coeff a N 0 + ∑ b ∈ Ico 1 D.Q, D.coeff a N b := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot D.hQ]
  rw [h0, hcoeff] at hsplit
  have h4 : (∑ c ∈ range D.Q, f c ^ 2) / D.Q ≤ 1 + (D.U N - 1) * (1 - D.L N) := by
    rw [div_le_iff₀ hQ0]
    nlinarith
  linarith

end Data

end TwoPrimesBox
