import LeanCheck.PVGLacIdeal

/-!
# PVG: the dilation lemma for the lacunary ideal (Lean check)

Scope. Lemma 7.3 of `PVG_v19`: for `A ∈ I_S` there is `c ∈ [1,2]` such that `c t ∈ A` for only finitely many `t ∈ T`, where `T` is
the set of all numbers `±s_n ± s_l` with `n > l ≥ 1`. The proof is the Borel–Cantelli argument of the article, with the counting
bound `ncard² ≤ K s_L` of `PVGLacCount.count_bound` in place of the polylogarithmic bound:

* for each `t = ±s_n ± s_l` the set `E_t = {c ∈ [1,2] : c t ∈ A}` has measure at most `|Y| · (2/s_n) · 2m`, where
  `Y = Σ ∩ [-ρ s_n, ρ s_n]` and `ρ = 4 + m` (`volume_E_le`);
* the union `F_n` of the `E_t` with largest index `n` (at most `4n` of them) has measure at most `16 m √K · n (1/√2)^n`, which is
  summable (`volume_F_le`, `summable_W`);
* `measure_limsup_atTop_eq_zero` gives a point `c ∈ [1,2]` that lies in only finitely many `F_n` (`exists_dilation`).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Set Pointwise MeasureTheory Filter Topology
open scoped Classical

namespace PVG
namespace Lac

/-- The sign `±1` of a Boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by cases b <;> simp [sgn]

/-- The number `±s_n ± s_l`. -/
def tval (n l : ℕ) (b1 b2 : Bool) : ℝ := sgn b1 * sS n + sgn b2 * sS l

/-- `T`: all numbers `±s_n ± s_l` with `n > l ≥ 1`. -/
def Tset : Set ℝ := {t | ∃ n l : ℕ, 1 ≤ l ∧ l < n ∧ ∃ b1 b2 : Bool, t = tval n l b1 b2}

lemma two_sS_le {l n : ℕ} (h : l < n) : 2 * sS l ≤ sS n := by
  have h1 : sS (l + 1) ≤ sS n := sS_mono h
  have h2 : 2 * sS l ≤ sS (l + 1) := by
    rw [sS_succ]
    have : (2 : ℝ) ≤ 2 ^ (2 * l + 1) :=
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * l + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [sS_pos l]
  linarith

lemma tval_bounds {l n : ℕ} (h : l < n) (b1 b2 : Bool) :
    sS n / 2 ≤ |tval n l b1 b2| ∧ |tval n l b1 b2| ≤ 2 * sS n := by
  have h1 := two_sS_le h
  have hn := sS_pos n
  have hl := sS_pos l
  have e1 : |sgn b1 * sS n| = sS n := by rw [abs_mul, abs_sgn, one_mul, abs_of_pos hn]
  have e2 : |sgn b2 * sS l| = sS l := by rw [abs_mul, abs_sgn, one_mul, abs_of_pos hl]
  unfold tval
  constructor
  · have := abs_sub_abs_le_abs_sub (sgn b1 * sS n) (-(sgn b2 * sS l))
    rw [abs_neg, e1, e2, sub_neg_eq_add] at this
    linarith
  · have := abs_add_le (sgn b1 * sS n) (sgn b2 * sS l)
    rw [e1, e2] at this
    linarith

/-! ### The measure of `E_t` -/

lemma volume_E_le {lst : List ℝ} {m : ℝ} (hm : 0 ≤ m) {A : Set ℝ}
    (hA : ∀ z ∈ A, ∃ y σ : ℝ, |y| ≤ m ∧ σ ∈ sumSet lst ∧ z = y + σ)
    {n l : ℕ} (hl : l < n) (b1 b2 : Bool)
    (hfin : (sumSet lst ∩ Icc (-((4 + m) * sS n)) ((4 + m) * sS n)).Finite) :
    volume {c : ℝ | c ∈ Icc (1 : ℝ) 2 ∧ c * tval n l b1 b2 ∈ A} ≤
      ENNReal.ofReal (((sumSet lst ∩ Icc (-((4 + m) * sS n)) ((4 + m) * sS n)).ncard : ℝ) *
        ((2 / sS n) * (2 * m))) := by
  obtain ⟨hlow, hup⟩ := tval_bounds hl b1 b2
  set t := tval n l b1 b2 with ht
  have hn := sS_pos n
  have hn1 := one_le_sS n
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hlow; linarith
  set Y := sumSet lst ∩ Icc (-((4 + m) * sS n)) ((4 + m) * sS n) with hY
  have hcover : {c : ℝ | c ∈ Icc (1 : ℝ) 2 ∧ c * t ∈ A} ⊆
      ⋃ σ ∈ hfin.toFinset, (fun c : ℝ => t * c) ⁻¹' Icc (σ - m) (σ + m) := by
    rintro c ⟨hc, hcA⟩
    obtain ⟨y, σ, hy, hσ, hyσ⟩ := hA _ hcA
    have hyb := abs_le.1 hy
    have hct : |c * t| ≤ 4 * sS n := by
      rw [abs_mul, abs_of_nonneg (by linarith [hc.1])]
      nlinarith [hc.2, abs_nonneg t]
    have hctb := abs_le.1 hct
    have hσI : σ ∈ Icc (-((4 + m) * sS n)) ((4 + m) * sS n) := by
      constructor <;> nlinarith [hyb.1, hyb.2]
    simp only [Set.mem_iUnion, Set.mem_preimage]
    refine ⟨σ, (hfin.mem_toFinset).2 ⟨hσ, hσI⟩, ?_, ?_⟩ <;> nlinarith [hyb.1, hyb.2]
  refine (measure_mono hcover).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ σ ∈ hfin.toFinset, volume ((fun c : ℝ => t * c) ⁻¹' Icc (σ - m) (σ + m)) ≤
      ENNReal.ofReal ((2 / sS n) * (2 * m)) := by
    intro σ _
    rw [Real.volume_preimage_mul_left ht0, Real.volume_Icc]
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : |t⁻¹| ≤ 2 / sS n := by
      rw [abs_inv, inv_eq_one_div, div_le_div_iff₀ (abs_pos.2 ht0) hn]
      linarith
    have h2 : σ + m - (σ - m) = 2 * m := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hcard : (hfin.toFinset.card : ℝ) = (Y.ncard : ℝ) := by rw [Set.ncard_eq_toFinset_card Y hfin]
  rw [hcard]

/-! ### The measure of `F_n` -/

/-- The union of the `E_t` with largest index `n`. -/
def Fn (A : Set ℝ) (n : ℕ) : Set ℝ :=
  {c : ℝ | c ∈ Icc (1 : ℝ) 2 ∧ ∃ l : ℕ, 1 ≤ l ∧ l < n ∧ ∃ b1 b2 : Bool, c * tval n l b1 b2 ∈ A}

/-- The majorant `W n = 16 m √K · n (1/√2)^n`. -/
noncomputable def Wmaj (m K : ℝ) (n : ℕ) : ℝ := 16 * m * Real.sqrt K * (n * ((Real.sqrt 2)⁻¹) ^ n)

lemma inv_sqrt_sS_le (n : ℕ) : 1 / Real.sqrt (sS n) ≤ ((Real.sqrt 2)⁻¹) ^ n := by
  have h2 : (2 : ℝ) ^ n ≤ sS n := by
    unfold sS; exact pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le n])
  have h1 : (Real.sqrt 2) ^ n ≤ Real.sqrt (sS n) := by
    apply Real.le_sqrt_of_sq_le
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
    exact h2
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [inv_pow, one_div]
  exact inv_anti₀ (pow_pos hs n) h1

lemma volume_F_le {lst : List ℝ} {m K : ℝ} (hm : 0 ≤ m) (hK : 0 < K) {A : Set ℝ}
    (hA : ∀ z ∈ A, ∃ y σ : ℝ, |y| ≤ m ∧ σ ∈ sumSet lst ∧ z = y + σ)
    (hcount : ∀ L : ℕ, (sumSet lst ∩ Icc (-((4 + m) * sS L)) ((4 + m) * sS L)).Finite ∧
      (((sumSet lst ∩ Icc (-((4 + m) * sS L)) ((4 + m) * sS L)).ncard : ℝ)) ^ 2 ≤ K * sS L) (n : ℕ) :
    volume (Fn A n) ≤ ENNReal.ofReal (Wmaj m K n) := by
  obtain ⟨hfin, hnc⟩ := hcount n
  set Y := sumSet lst ∩ Icc (-((4 + m) * sS n)) ((4 + m) * sS n) with hY
  set B : ℝ := (Y.ncard : ℝ) * ((2 / sS n) * (2 * m)) with hB
  have hsub : Fn A n ⊆ ⋃ i ∈ (Finset.Ico 1 n ×ˢ (Finset.univ : Finset (Bool × Bool))),
      {c : ℝ | c ∈ Icc (1 : ℝ) 2 ∧ c * tval n i.1 i.2.1 i.2.2 ∈ A} := by
    rintro c ⟨hc, l, hl1, hln, b1, b2, hcA⟩
    simp only [Set.mem_iUnion]
    exact ⟨(l, b1, b2), by simp [Finset.mem_product, Finset.mem_Ico, hl1, hln], hc, hcA⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ i ∈ (Finset.Ico 1 n ×ˢ (Finset.univ : Finset (Bool × Bool))),
      volume {c : ℝ | c ∈ Icc (1 : ℝ) 2 ∧ c * tval n i.1 i.2.1 i.2.2 ∈ A} ≤ ENNReal.ofReal B := by
    intro i hi
    have hi1 : i.1 < n := (Finset.mem_Ico.1 (Finset.mem_product.1 hi).1).2
    exact volume_E_le hm hA hi1 i.2.1 i.2.2 hfin
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  -- `card ≤ 4 n`, `B ≤ 4 m √K r^n`
  have hcard : ((Finset.Ico 1 n ×ˢ (Finset.univ : Finset (Bool × Bool))).card : ℝ) ≤ 4 * n := by
    rw [Finset.card_product, Nat.card_Ico]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
    have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    push_cast
    nlinarith
  have hs := sS_pos n
  set q := Real.sqrt (sS n) with hq
  have hq0 : 0 < q := Real.sqrt_pos.2 hs
  have hq2 : q ^ 2 = sS n := Real.sq_sqrt hs.le
  have hncle : (Y.ncard : ℝ) ≤ Real.sqrt K * q := by
    have := Real.le_sqrt_of_sq_le hnc
    rwa [Real.sqrt_mul hK.le] at this
  have hB' : B ≤ 4 * m * Real.sqrt K * (1 / q) := by
    rw [hB]
    have h1 : (Y.ncard : ℝ) * ((2 / sS n) * (2 * m)) ≤ Real.sqrt K * q * ((2 / sS n) * (2 * m)) :=
      mul_le_mul_of_nonneg_right hncle (by positivity)
    refine h1.trans ?_
    rw [← hq2]
    field_simp
    nlinarith [Real.sqrt_nonneg K]
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hr := inv_sqrt_sS_le n
  have hnn : (0 : ℝ) ≤ 4 * n := by positivity
  calc ((Finset.Ico 1 n ×ˢ (Finset.univ : Finset (Bool × Bool))).card : ℝ) * B ≤ 4 * n * B :=
        mul_le_mul_of_nonneg_right hcard hB0
    _ ≤ 4 * n * (4 * m * Real.sqrt K * ((Real.sqrt 2)⁻¹ ^ n)) := by
        apply mul_le_mul_of_nonneg_left _ hnn
        refine hB'.trans ?_
        exact mul_le_mul_of_nonneg_left hr (by positivity)
    _ = Wmaj m K n := by unfold Wmaj; ring

lemma summable_W (m K : ℝ) : Summable (Wmaj m K) := by
  have hr : ‖(Real.sqrt 2)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 (by norm_num)))]
    rw [inv_lt_one₀ (Real.sqrt_pos.2 (by norm_num))]
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left (16 * m * Real.sqrt K)
  refine this.congr (fun n => ?_)
  unfold Wmaj; simp

/-- **Lemma 7.3.** For `A ∈ I_S` there is `c ∈ [1,2]` such that `c t ∈ A` for only finitely many `t ∈ T`. -/
theorem exists_dilation {A : Set ℝ} (hA : A ∈ IS) :
    ∃ c ∈ Icc (1 : ℝ) 2, {t | t ∈ Tset ∧ c * t ∈ A}.Finite := by
  rw [mem_IS_iff] at hA
  obtain ⟨m0, lst, hA⟩ := hA
  set m : ℝ := |m0| with hm
  have hm0 : 0 ≤ m := abs_nonneg _
  have hA' : ∀ z ∈ A, ∃ y σ : ℝ, |y| ≤ m ∧ σ ∈ sumSet lst ∧ z = y + σ := by
    intro z hz
    obtain ⟨y, σ, hy, hσ, h⟩ := hA z hz
    exact ⟨y, σ, hy.trans (le_abs_self m0), hσ, h⟩
  obtain ⟨K, hK, hcount⟩ := count_bound lst (4 + m) (by linarith)
  have hvol : ∀ n, volume (Fn A n) ≤ ENNReal.ofReal (Wmaj m K n) :=
    fun n => volume_F_le hm0 hK hA' hcount n
  have hWnn : ∀ n, 0 ≤ Wmaj m K n := fun n => by unfold Wmaj; positivity
  have htsum : ∑' n, volume (Fn A n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hvol)
    rw [← ENNReal.ofReal_tsum_of_nonneg hWnn (summable_W m K)]
    exact ENNReal.ofReal_ne_top
  have hlim : volume (limsup (Fn A) atTop) = 0 := measure_limsup_atTop_eq_zero htsum
  -- a point of `[1,2]` outside the limsup
  have hex : ∃ c ∈ Icc (1 : ℝ) 2, c ∉ limsup (Fn A) atTop := by
    by_contra hno
    push Not at hno
    have h1 : Icc (1 : ℝ) 2 ⊆ limsup (Fn A) atTop := hno
    have h2 := measure_mono (μ := volume) h1
    rw [hlim, Real.volume_Icc] at h2
    norm_num at h2
  obtain ⟨c, hc, hcn⟩ := hex
  refine ⟨c, hc, ?_⟩
  rw [Filter.mem_limsup_iff_frequently_mem, not_frequently] at hcn
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hcn
  -- every such `t` has largest index below `N0`
  have hsub : {t | t ∈ Tset ∧ c * t ∈ A} ⊆
      (fun i : ℕ × ℕ × Bool × Bool => tval i.1 i.2.1 i.2.2.1 i.2.2.2) ''
        ↑(Finset.range N0 ×ˢ Finset.range N0 ×ˢ (Finset.univ : Finset (Bool × Bool))) := by
    rintro t ⟨⟨n, l, hl1, hln, b1, b2, rfl⟩, htA⟩
    by_cases hn : n < N0
    · refine ⟨(n, l, b1, b2), ?_, rfl⟩
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range, Finset.mem_univ, and_true]
      exact ⟨hn, by omega⟩
    · exfalso
      apply hN0 n (by omega)
      exact ⟨hc, l, hl1, hln, b1, b2, htA⟩
  exact Set.Finite.subset (Set.Finite.image _ (Finset.finite_toSet _)) hsub

#print axioms volume_E_le
#print axioms volume_F_le
#print axioms exists_dilation

end Lac
end PVG
