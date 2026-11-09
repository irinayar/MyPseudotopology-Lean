import Mathlib
import LeanCheck.PVGBetaHalf

/-!
# Kronecker's density theorem (Lean check)

Scope. `KroneckerDensity` of `PVGBetaHalf`: if `1, β₁, …, β_w` are linearly independent over `ℚ`, then the points `(kβ₁, …, kβ_w)`, `k ∈ ℤ`
(here `k ∈ ℕ` suffices), are dense modulo `1`. The proof is Weyl's: the averages of the exponential monomials `mFourier n` of Mathlib
along the orbit tend to `0` for `n ≠ 0` (geometric series, because `n·β ∉ ℤ`), the trigonometric polynomials are dense in the continuous
functions on the torus (Mathlib, `span_mFourier_closure_eq_top`), the averages are therefore asymptotically translation invariant, and a
finite family of translates of a bump function covers the torus.

* `kronecker_density`: the statement `KroneckerDensity`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology Complex

namespace PVG
namespace Beta

abbrev Tor (w : ℕ) := UnitAddTorus (Fin w)

variable {w : ℕ}

/-- The ergodic averages along the orbit of `b`. -/
noncomputable def avg (b : Tor w) (K : ℕ) (g : C(Tor w, ℂ)) : ℂ :=
  (1 / (K : ℂ)) * ∑ k ∈ Finset.range K, g (k • b)

/-- The translate of `g` by `a`. -/
def trans (a : Tor w) (g : C(Tor w, ℂ)) : C(Tor w, ℂ) :=
  ⟨fun x => g (x + a), by fun_prop⟩

lemma avg_add (b : Tor w) (K : ℕ) (g h : C(Tor w, ℂ)) : avg b K (g + h) = avg b K g + avg b K h := by
  simp [avg, Finset.sum_add_distrib, mul_add]

lemma avg_smul (b : Tor w) (K : ℕ) (c : ℂ) (g : C(Tor w, ℂ)) : avg b K (c • g) = c * avg b K g := by
  simp [avg, ← Finset.mul_sum]; ring

lemma avg_sub (b : Tor w) (K : ℕ) (g h : C(Tor w, ℂ)) : avg b K (g - h) = avg b K g - avg b K h := by
  simp [avg, Finset.sum_sub_distrib, mul_sub]

lemma avg_norm_le (b : Tor w) (K : ℕ) (g : C(Tor w, ℂ)) : ‖avg b K g‖ ≤ ‖g‖ := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [avg]
  · unfold avg
    rw [norm_mul]
    have h1 : ‖∑ k ∈ Finset.range K, g (k • b)‖ ≤ K * ‖g‖ := by
      calc ‖∑ k ∈ Finset.range K, g (k • b)‖ ≤ ∑ k ∈ Finset.range K, ‖g (k • b)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range K, ‖g‖ := Finset.sum_le_sum (fun k _ => g.norm_coe_le_norm _)
        _ = K * ‖g‖ := by simp
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    calc ‖(1 / (K : ℂ))‖ * ‖∑ k ∈ Finset.range K, g (k • b)‖ ≤ ‖(1 / (K : ℂ))‖ * (K * ‖g‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖g‖ := by
          rw [norm_div, norm_one, Complex.norm_natCast]; field_simp

lemma avg_trans_norm_le (b : Tor w) (K : ℕ) (a : Tor w) (g : C(Tor w, ℂ)) :
    ‖avg b K (trans a g)‖ ≤ ‖g‖ := by
  refine (avg_norm_le b K _).trans ?_
  refine (ContinuousMap.norm_le _ (norm_nonneg g)).2 (fun x => ?_)
  exact g.norm_coe_le_norm _

lemma mFourier_add_arg (n : Fin w → ℤ) (x y : Tor w) :
    UnitAddTorus.mFourier n (x + y) = UnitAddTorus.mFourier n x * UnitAddTorus.mFourier n y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp [fourier_apply, smul_add, AddCircle.toCircle_add]

lemma mFourier_zero_arg (n : Fin w → ℤ) : UnitAddTorus.mFourier n (0 : Tor w) = 1 := by
  simp [UnitAddTorus.mFourier]

lemma mFourier_nsmul (n : Fin w → ℤ) (b : Tor w) (k : ℕ) :
    UnitAddTorus.mFourier n (k • b) = (UnitAddTorus.mFourier n b) ^ k := by
  induction k with
  | zero => simp [mFourier_zero_arg]
  | succ k ih => rw [succ_nsmul, mFourier_add_arg, ih, pow_succ]

/-- The orbit generator. -/
noncomputable def bvec (β : Fin w → ℝ) : Tor w := fun i => ((β i : ℝ) : AddCircle (1 : ℝ))

lemma mFourier_bvec (n : Fin w → ℤ) (β : Fin w → ℝ) :
    UnitAddTorus.mFourier n (bvec β) =
      Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * β i : ℝ) : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, bvec, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp
  ring

lemma norm_mFourier_apply (n : Fin w → ℤ) (x : Tor w) : ‖UnitAddTorus.mFourier n x‖ = 1 := by
  simp [UnitAddTorus.mFourier, fourier_apply, norm_prod]

lemma trans_add (a : Tor w) (g h : C(Tor w, ℂ)) : trans a (g + h) = trans a g + trans a h := by
  ext x; simp [trans]

lemma trans_sub (a : Tor w) (g h : C(Tor w, ℂ)) : trans a (g - h) = trans a g - trans a h := by
  ext x; simp [trans]

lemma trans_smul (a : Tor w) (c : ℂ) (g : C(Tor w, ℂ)) : trans a (c • g) = c • trans a g := by
  ext x; simp [trans]

lemma trans_zero (a : Tor w) : trans a (0 : C(Tor w, ℂ)) = 0 := by
  ext x; simp [trans]

lemma z_ne_one {β : Fin w → ℝ} (hli : LinearIndependent ℚ (Fin.cons (1 : ℝ) β : Fin (w + 1) → ℝ))
    {n : Fin w → ℤ} (hn : n ≠ 0) : UnitAddTorus.mFourier n (bvec β) ≠ 1 := by
  rw [mFourier_bvec, Ne, Complex.exp_eq_one_iff]
  rintro ⟨m, hm⟩
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hs : (((∑ i, (n i : ℝ) * β i : ℝ)) : ℂ) = (m : ℂ) := by
    have : (2 * (Real.pi : ℂ) * Complex.I) * (((∑ i, (n i : ℝ) * β i : ℝ)) : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * (m : ℂ) := by rw [hm]; ring
    exact mul_left_cancel₀ h2pi this
  have hs' : (∑ i, (n i : ℝ) * β i) = (m : ℝ) := by exact_mod_cast hs
  apply hn
  rw [Fintype.linearIndependent_iff] at hli
  have := hli (Fin.cons (-(m : ℚ)) (fun i => (n i : ℚ))) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Rat.smul_def]
    push_cast
    linarith [hs'])
  funext i
  have := this i.succ
  simpa using this

lemma avg_char_tendsto {β : Fin w → ℝ} (hli : LinearIndependent ℚ (Fin.cons (1 : ℝ) β : Fin (w + 1) → ℝ))
    {n : Fin w → ℤ} (hn : n ≠ 0) :
    Tendsto (fun K => avg (bvec β) K (UnitAddTorus.mFourier n)) atTop (𝓝 0) := by
  set z := UnitAddTorus.mFourier n (bvec β) with hz
  have hz1 : z ≠ 1 := z_ne_one hli hn
  have hzn : ‖z‖ = 1 := norm_mFourier_apply n _
  have hz1' : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz1)
  have hbound : ∀ K : ℕ, ‖avg (bvec β) K (UnitAddTorus.mFourier n)‖ ≤ (2 / ‖z - 1‖) / K := by
    intro K
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [avg]
    · unfold avg
      simp only [mFourier_nsmul]
      rw [← hz, geom_sum_eq hz1 K, norm_mul, norm_div, norm_div, norm_one, Complex.norm_natCast]
      have hK' : (0 : ℝ) < K := by exact_mod_cast hK
      have h1 : ‖z ^ K - 1‖ ≤ 2 := by
        calc ‖z ^ K - 1‖ ≤ ‖z ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, hzn]; simp; norm_num
      calc 1 / (K : ℝ) * (‖z ^ K - 1‖ / ‖z - 1‖) ≤ 1 / (K : ℝ) * (2 / ‖z - 1‖) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 hz1'.le) (by positivity)
        _ = (2 / ‖z - 1‖) / K := by ring
  exact squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)

/-- The averages of `g` and of all its translates converge to `ℓ`. -/
def HasLim (b : Tor w) (g : C(Tor w, ℂ)) (ℓ : ℂ) : Prop :=
  Tendsto (fun K => avg b K g) atTop (𝓝 ℓ) ∧
    ∀ a : Tor w, Tendsto (fun K => avg b K (trans a g)) atTop (𝓝 ℓ)

lemma hasLim_char {β : Fin w → ℝ} (hli : LinearIndependent ℚ (Fin.cons (1 : ℝ) β : Fin (w + 1) → ℝ))
    (n : Fin w → ℤ) : ∃ ℓ, HasLim (bvec β) (UnitAddTorus.mFourier n) ℓ := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨1, ?_, fun a => ?_⟩
    · have : ∀ K ≥ 1, avg (bvec β) K (UnitAddTorus.mFourier (0 : Fin w → ℤ)) = 1 := by
        intro K hK
        have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
        simp [avg, UnitAddTorus.mFourier_zero]
        field_simp
      exact tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop 1] with K hK using (this K hK).symm)
    · have h0 : trans a (UnitAddTorus.mFourier (0 : Fin w → ℤ)) = UnitAddTorus.mFourier 0 := by
        ext x; simp [trans, UnitAddTorus.mFourier_zero]
      have : ∀ K ≥ 1, avg (bvec β) K (trans a (UnitAddTorus.mFourier (0 : Fin w → ℤ))) = 1 := by
        intro K hK
        have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
        rw [h0]
        simp [avg, UnitAddTorus.mFourier_zero]
        field_simp
      exact tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop 1] with K hK using (this K hK).symm)
  · refine ⟨0, avg_char_tendsto hli hn, fun a => ?_⟩
    have h1 : trans a (UnitAddTorus.mFourier n) = (UnitAddTorus.mFourier n a) • UnitAddTorus.mFourier n := by
      ext x; simp [trans, mFourier_add_arg, mul_comm]
    have h2 : ∀ K, avg (bvec β) K (trans a (UnitAddTorus.mFourier n)) =
        UnitAddTorus.mFourier n a * avg (bvec β) K (UnitAddTorus.mFourier n) := by
      intro K; rw [h1, avg_smul]
    simp_rw [h2]
    simpa using (avg_char_tendsto hli hn).const_mul (UnitAddTorus.mFourier n a)

lemma hasLim_span {β : Fin w → ℝ} (hli : LinearIndependent ℚ (Fin.cons (1 : ℝ) β : Fin (w + 1) → ℝ))
    {g : C(Tor w, ℂ)} (hg : g ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin w)))) :
    ∃ ℓ, HasLim (bvec β) g ℓ := by
  induction hg using Submodule.span_induction with
  | mem g hg => obtain ⟨n, rfl⟩ := hg; exact hasLim_char hli n
  | zero => exact ⟨0, by simp [avg], fun a => by simp [trans_zero, avg]⟩
  | add g h _ _ ih1 ih2 =>
    obtain ⟨ℓ1, h11, h12⟩ := ih1
    obtain ⟨ℓ2, h21, h22⟩ := ih2
    refine ⟨ℓ1 + ℓ2, ?_, fun a => ?_⟩
    · simp_rw [avg_add]; exact h11.add h21
    · simp_rw [trans_add, avg_add]; exact (h12 a).add (h22 a)
  | smul c g _ ih =>
    obtain ⟨ℓ, h1, h2⟩ := ih
    refine ⟨c * ℓ, ?_, fun a => ?_⟩
    · simp_rw [avg_smul]; exact h1.const_mul c
    · simp_rw [trans_smul, avg_smul]; exact (h2 a).const_mul c

/-- The averages are asymptotically translation invariant. -/
lemma trans_asymp {β : Fin w → ℝ} (hli : LinearIndependent ℚ (Fin.cons (1 : ℝ) β : Fin (w + 1) → ℝ))
    (g : C(Tor w, ℂ)) (a : Tor w) :
    Tendsto (fun K => avg (bvec β) K (trans a g) - avg (bvec β) K g) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hg : g ∈ (Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin w)))).topologicalClosure := by
    rw [UnitAddTorus.span_mFourier_closure_eq_top]; trivial
  obtain ⟨P, hP, hdist⟩ := Metric.mem_closure_iff.1 hg (ε / 4) (by positivity)
  obtain ⟨ℓ, h1, h2⟩ := hasLim_span hli hP
  rw [Metric.tendsto_atTop] at h1
  obtain ⟨K1, hK1⟩ := h1 (ε / 4) (by positivity)
  obtain ⟨K2, hK2⟩ := (Metric.tendsto_atTop.1 (h2 a)) (ε / 4) (by positivity)
  refine ⟨max K1 K2, fun K hK => ?_⟩
  have e1 := hK1 K (le_trans (le_max_left _ _) hK)
  have e2 := hK2 K (le_trans (le_max_right _ _) hK)
  rw [dist_eq_norm] at e1 e2 hdist ⊢
  have hgP : ‖g - P‖ < ε / 4 := hdist
  have hdecomp : avg (bvec β) K (trans a g) - avg (bvec β) K g - 0 =
      avg (bvec β) K (trans a (g - P)) + (avg (bvec β) K (trans a P) - ℓ) - (avg (bvec β) K P - ℓ)
        - avg (bvec β) K (g - P) := by
    rw [trans_sub, avg_sub, avg_sub]; ring
  rw [hdecomp]
  have b1 := avg_trans_norm_le (bvec β) K a (g - P)
  have b2 := avg_norm_le (bvec β) K (g - P)
  calc ‖avg (bvec β) K (trans a (g - P)) + (avg (bvec β) K (trans a P) - ℓ) - (avg (bvec β) K P - ℓ)
          - avg (bvec β) K (g - P)‖
      ≤ ‖avg (bvec β) K (trans a (g - P))‖ + ‖avg (bvec β) K (trans a P) - ℓ‖ +
        ‖avg (bvec β) K P - ℓ‖ + ‖avg (bvec β) K (g - P)‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl
    _ < ε := by linarith

/-- **Kronecker's density theorem** (Weyl's proof). -/
theorem kronecker_density : KroneckerDensity := by
  intro w β hli θ ε hε
  classical
  let θv : Tor w := fun i => ((θ i : ℝ) : AddCircle (1 : ℝ))
  let Fr : Tor w → ℝ := fun x => ∏ i, max 0 (ε - ‖x i - θv i‖)
  have hFr_cont : Continuous Fr :=
    continuous_finset_prod _ (fun i _ => continuous_const.max
      (continuous_const.sub (continuous_norm.comp ((continuous_apply i).sub continuous_const))))
  have hFr_nonneg : ∀ x, 0 ≤ Fr x := fun x => Finset.prod_nonneg (fun i _ => le_max_left _ _)
  have hFr_θ : 0 < Fr θv := Finset.prod_pos (fun i _ => by simp [θv, hε])
  let f : C(Tor w, ℂ) := ⟨fun x => (Fr x : ℂ), Complex.continuous_ofReal.comp hFr_cont⟩
  set c : ℝ := Fr θv / 2 with hc
  have hc0 : 0 < c := by positivity
  -- a finite family of translates covering the torus
  obtain ⟨S, hS⟩ : ∃ S : Finset (Tor w), ∀ x, ∃ a ∈ S, c < Fr (x + a) := by
    have hopen : ∀ a : Tor w, IsOpen {x : Tor w | c < Fr (x + a)} := fun a =>
      isOpen_lt continuous_const (hFr_cont.comp (continuous_id.add continuous_const))
    have hcov : (Set.univ : Set (Tor w)) ⊆ ⋃ a : Tor w, {x | c < Fr (x + a)} := fun x _ => by
      refine Set.mem_iUnion.2 ⟨θv - x, ?_⟩
      show c < Fr (x + (θv - x))
      rw [add_sub_cancel]; linarith
    obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
    refine ⟨S, fun x => ?_⟩
    have := hS (Set.mem_univ x)
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
    obtain ⟨a, ha, hx⟩ := this
    exact ⟨a, ha, hx⟩
  by_contra hno
  push Not at hno
  -- `Fr` vanishes on the orbit
  have hzero : ∀ k : ℕ, Fr (k • bvec β) = 0 := by
    intro k
    obtain ⟨s, hs⟩ := hno (k : ℤ)
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    have : (k • bvec β) s - θv s = (((k : ℝ) * β s - θ s : ℝ) : AddCircle (1 : ℝ)) := by
      simp [bvec, θv, AddCircle.coe_sub, nsmul_eq_mul]
    rw [this]
    have : ε - ‖(((k : ℝ) * β s - θ s : ℝ) : AddCircle (1 : ℝ))‖ ≤ 0 := by
      have := hs; push_cast at this; linarith
    exact max_eq_left this
  have havgf : ∀ K : ℕ, avg (bvec β) K f = 0 := by
    intro K; simp [avg, f, hzero]
  -- the averages of the translates tend to `0`
  have hT : ∀ a : Tor w, Tendsto (fun K => avg (bvec β) K (trans a f)) atTop (𝓝 0) := by
    intro a
    have := trans_asymp hli f a
    simpa [havgf] using this
  have hsum : Tendsto (fun K => ∑ a ∈ S, avg (bvec β) K (trans a f)) atTop (𝓝 0) := by
    have := tendsto_finset_sum S (fun a _ => hT a)
    simpa using this
  -- a lower bound for the real parts
  let Q : ℕ → ℝ := fun K => (1 / (K : ℝ)) * ∑ k ∈ Finset.range K, ∑ a ∈ S, Fr (k • bvec β + a)
  have hQ : ∀ K : ℕ, ∑ a ∈ S, avg (bvec β) K (trans a f) = (Q K : ℂ) := by
    intro K
    simp only [avg, trans, f, ContinuousMap.coe_mk, Q]
    push_cast
    rw [← Finset.mul_sum, Finset.sum_comm]
  have hQge : ∀ K : ℕ, 1 ≤ K → c ≤ Q K := by
    intro K hK
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hinner : ∀ k : ℕ, c ≤ ∑ a ∈ S, Fr (k • bvec β + a) := by
      intro k
      obtain ⟨a, ha, hlt⟩ := hS (k • bvec β)
      exact hlt.le.trans (Finset.single_le_sum (f := fun a => Fr (k • bvec β + a))
        (fun a _ => hFr_nonneg _) ha)
    have : (K : ℝ) * c ≤ ∑ k ∈ Finset.range K, ∑ a ∈ S, Fr (k • bvec β + a) := by
      calc (K : ℝ) * c = ∑ _k ∈ Finset.range K, c := by simp
        _ ≤ _ := Finset.sum_le_sum (fun k _ => hinner k)
    simp only [Q]
    rw [one_div]
    exact (le_inv_mul_iff₀ hK').2 this
  have hQt : Tendsto Q atTop (𝓝 0) := by
    have h1 : Tendsto (fun K => ((Q K : ℝ) : ℂ)) atTop (𝓝 0) := by
      simpa [hQ] using hsum
    have h2 := (Complex.continuous_re.tendsto 0).comp h1
    exact h2.congr (fun K => by simp)
  obtain ⟨K, hK⟩ := (eventually_ge_atTop 1).and (hQt.eventually (gt_mem_nhds hc0)) |>.exists
  exact absurd (hQge K hK.1) (not_le.2 hK.2)

end Beta
end PVG
