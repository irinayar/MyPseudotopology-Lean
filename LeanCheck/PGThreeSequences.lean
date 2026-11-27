import Mathlib
import LeanCheck.PGThreeZFC

/-!
# PGthree, Section 9: no convergent sequences for fewer than `2 ^ 𝔠` generators

The interpolation argument of `PGThreeZFC` is repeated here with a *set* in place of
the subgroup `H` (only the fibres at the points themselves are used), so that it
applies to every infinite subset of every abelian group after one translation.
Then: a set of fewer than `2 ^ 𝔠` ultrafilters generates a PG in which, on every
infinite set, some free ultrafilter converges to no point of a prescribed set of
fewer than `2 ^ 𝔠` points.
-/

open Filter Set Topology MeasureTheory

open scoped ComplexConjugate Cardinal

namespace PG

namespace Seq

open Sel PG.Bohr PG.ZFC

variable {G : Type} [AddCommGroup G]

variable (H : Set G)

theorem both_sides_set (n : ℕ) (hfib : ∀ y : G, {x : G | x ∈ H ∧ n • x = y}.Finite)
    (h2 : (∀ y : G, {x : G | x ∈ H ∧ (2 * n) • x = y}.Finite) ∨ (∀ x ∈ H, (2 * n) • x = 0))
    (A : Set G) (hA : A ⊆ H) (E : Set (Dual G)) (hE : MeasurableSet E) (hpos : 0 < (μ G) E) :
    {a ∈ A | ¬ (0 < (μ G) (E ∩ {χ | 1 / 8 < (ev (n • a) χ).re}) ∧
      0 < (μ G) (E ∩ {χ | (ev (n • a) χ).re < -(1 / 8)}))}.Finite := by
  set m : ℝ := (μ G).real E with hm
  have hmpos : 0 < m := by
    rw [hm, measureReal_def]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hfin : ∀ k : ℕ, (∀ y : G, {x : G | x ∈ H ∧ k • x = y}.Finite) →
      {a ∈ A | m / 8 ≤ ‖∫ χ in E, ev (k • a) χ ∂(μ G)‖}.Finite := by
    intro k hk
    have h1 := finite_large_coeff E hE (m / 8) (by positivity)
    have h3 : {a ∈ A | m / 8 ≤ ‖∫ χ in E, ev (k • a) χ ∂(μ G)‖}
        ⊆ ⋃ y ∈ {y : G | m / 8 ≤ ‖∫ χ in E, ev y χ ∂(μ G)‖}, {x : G | x ∈ H ∧ k • x = y} := by
      intro a ha
      exact mem_iUnion₂.2 ⟨k • a, ha.2, hA ha.1, rfl⟩
    exact (h1.biUnion (fun y _ => hk y)).subset h3
  have hbad2 : ∃ T : Set G, T.Finite ∧ ∀ a ∈ A, a ∉ T →
      m / 2 - m / 16 ≤ ∫ χ in E, (ev (n • a) χ).re ^ 2 ∂(μ G) := by
    have hrew : ∀ a : G, ∫ χ in E, (ev (n • a) χ).re ^ 2 ∂(μ G)
        = m / 2 + (∫ χ in E, ev ((2 * n) • a) χ ∂(μ G)).re / 2 := by
      intro a
      have e1 : ∀ χ : Dual G, (ev (n • a) χ).re ^ 2 = 1 / 2 + (ev ((2 * n) • a) χ).re / 2 := by
        intro χ
        rw [sq_re_ev, ← add_nsmul, ← two_mul]
        ring
      simp only [e1]
      have hi : IntegrableOn (fun χ => (ev ((2 * n) • a) χ).re) E (μ G) :=
        (integrable_ev _).re.integrableOn
      rw [integral_add (integrable_const _).integrableOn (hi.div_const 2), setIntegral_const,
        integral_div]
      have e2 : ∫ χ in E, (ev ((2 * n) • a) χ).re ∂(μ G) = (∫ χ in E, ev ((2 * n) • a) χ ∂(μ G)).re :=
        integral_re (integrable_ev _).integrableOn
      rw [e2, smul_eq_mul, ← hm]
      ring
    rcases h2 with h2 | h2
    · refine ⟨_, hfin (2 * n) h2, fun a ha hnot => ?_⟩
      have h3 : ‖∫ χ in E, ev ((2 * n) • a) χ ∂(μ G)‖ < m / 8 := not_le.1 (fun h => hnot ⟨ha, h⟩)
      have h4 := (abs_le.1 (Complex.abs_re_le_norm (∫ χ in E, ev ((2 * n) • a) χ ∂(μ G)))).1
      rw [hrew]
      linarith
    · refine ⟨∅, finite_empty, fun a ha _ => ?_⟩
      rw [hrew, h2 a (hA ha)]
      simp only [ev_zero]
      rw [setIntegral_const, ← hm]
      simp
      linarith
  obtain ⟨T, hT, hT2⟩ := hbad2
  refine ((hfin n hfib).union hT).subset (fun a ha => ?_)
  by_contra hnot
  rw [mem_union, not_or] at hnot
  have h1 : ‖∫ χ in E, ev (n • a) χ ∂(μ G)‖ < m / 8 := not_le.1 (fun h => hnot.1 ⟨ha.1, h⟩)
  have h2' := hT2 a ha.1 hnot.2
  set f : Dual G → ℝ := fun χ => (ev (n • a) χ).re with hf
  have hfc : Continuous f := Complex.continuous_re.comp (continuous_ev _)
  have hfi : IntegrableOn f E (μ G) := (integrable_ev _).re.integrableOn
  have hf2i : IntegrableOn (fun χ => f χ ^ 2) E (μ G) :=
    ((hfc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integrableOn
  have hif : |∫ χ in E, f χ ∂(μ G)| < m / 8 := by
    have e2 : ∫ χ in E, f χ ∂(μ G) = (∫ χ in E, ev (n • a) χ ∂(μ G)).re :=
      integral_re (integrable_ev _).integrableOn
    rw [e2]
    exact lt_of_le_of_lt (Complex.abs_re_le_norm _) h1
  have hif' := abs_lt.1 hif
  apply ha.2
  constructor
  · rw [pos_iff_ne_zero]
    intro h0
    have hae : ∀ᵐ χ ∂(μ G).restrict E, f χ ^ 2 ≤ 1 / 8 + (-(7 / 8)) * f χ := by
      rw [ae_restrict_iff' hE, ae_iff]
      refine measure_mono_null (fun χ hχ => ?_) h0
      simp only [mem_setOf_eq, Classical.not_imp, not_le] at hχ
      refine ⟨hχ.1, ?_⟩
      show 1 / 8 < f χ
      by_contra h
      have h' : f χ ≤ 1 / 8 := not_lt.1 h
      have h5 := (abs_re_ev (n • a) χ).1
      have h6 : -1 ≤ f χ := h5
      nlinarith [hχ.2]
    have h7 := integral_mono_ae hf2i ((integrable_const _).integrableOn.add (hfi.const_mul _)) hae
    simp only [Pi.add_apply] at h7
    rw [integral_add (integrable_const _).integrableOn (hfi.const_mul _), setIntegral_const,
      integral_const_mul, smul_eq_mul, ← hm] at h7
    linarith [hif'.1, hif'.2]
  · rw [pos_iff_ne_zero]
    intro h0
    have hae : ∀ᵐ χ ∂(μ G).restrict E, f χ ^ 2 ≤ 1 / 8 + (7 / 8) * f χ := by
      rw [ae_restrict_iff' hE, ae_iff]
      refine measure_mono_null (fun χ hχ => ?_) h0
      simp only [mem_setOf_eq, Classical.not_imp, not_le] at hχ
      refine ⟨hχ.1, ?_⟩
      show f χ < -(1 / 8)
      by_contra h
      have h' : -(1 / 8) ≤ f χ := not_lt.1 h
      have h5 := (abs_re_ev (n • a) χ).2
      have h6 : f χ ≤ 1 := h5
      nlinarith [hχ.2]
    have h7 := integral_mono_ae hf2i ((integrable_const _).integrableOn.add (hfi.const_mul _)) hae
    simp only [Pi.add_apply] at h7
    rw [integral_add (integrable_const _).integrableOn (hfi.const_mul _), setIntegral_const,
      integral_const_mul, smul_eq_mul, ← hm] at h7
    linarith [hif'.1, hif'.2]

variable (M : Set ℕ)

theorem step_set (hfib : ∀ n ∈ M, ∀ y : G, {x : G | x ∈ H ∧ n • x = y}.Finite)
    (h2 : ∀ n ∈ M, (∀ y : G, {x : G | x ∈ H ∧ (2 * n) • x = y}.Finite) ∨ (∀ x ∈ H, (2 * n) • x = 0))
    (A : Set G) (hA : A ⊆ H) (hAinf : A.Infinite) (b : ℕ → G) (j : ℕ) (hb : Good M b j) :
    ∃ a ∈ A, (∀ i < j, b i ≠ a) ∧ Good M (Function.update b j a) (j + 1) := by
  classical
  let σ' : (Fin j → Bool) → ℕ → Bool := fun τ i => if h : i < j then τ ⟨i, h⟩ else false
  let Bad : ℕ → (Fin j → Bool) → Set G := fun n τ =>
    {a ∈ A | n ∈ M ∧ n ≤ j ∧ ¬ (0 < (μ G) (Pat b n j (σ' τ) ∩ {χ | 1 / 8 < (ev (n • a) χ).re}) ∧
      0 < (μ G) (Pat b n j (σ' τ) ∩ {χ | (ev (n • a) χ).re < -(1 / 8)}))}
  have hBad : ∀ n τ, (Bad n τ).Finite := by
    intro n τ
    by_cases hn : n ∈ M ∧ n ≤ j
    · have hmeas : MeasurableSet (Pat b n j (σ' τ)) :=
        (Finset.measurableSet_biInter _ (fun i _ => (isOpen_Up _ _ _).measurableSet))
      refine (both_sides_set H n (hfib n hn.1) (h2 n hn.1) A hA _ hmeas (hb n hn.1 hn.2 _)).subset ?_
      exact fun a ha => ⟨ha.1, ha.2.2.2⟩
    · refine Set.finite_empty.subset (fun a ha => ?_)
      exact absurd ⟨ha.2.1, ha.2.2.1⟩ hn
  have hall : (⋃ n ∈ Finset.range (j + 1), ⋃ τ : Fin j → Bool, Bad n τ).Finite :=
    (Finset.range (j + 1)).finite_toSet.biUnion (fun n _ => finite_iUnion (fun τ => hBad n τ))
  have himg : (b '' Set.Iio j).Finite := (finite_Iio j).image b
  obtain ⟨a, haA, hnot⟩ := (hAinf.diff (hall.union himg)).nonempty
  rw [mem_union, not_or] at hnot
  refine ⟨a, haA, fun i hi h => hnot.2 ⟨i, hi, h⟩, fun n hn hnj σ => ?_⟩
  rcases Nat.lt_or_ge j n with h | h
  · have e : Pat (Function.update b j a) n (j + 1) σ = univ := by
      have e0 : Finset.Ico n (j + 1) = ∅ := Finset.Ico_eq_empty (by omega)
      unfold Pat
      rw [e0]
      simp
    rw [e, measure_univ]
    exact one_pos
  · set τ : Fin j → Bool := fun i => σ i with hτ
    have hgood : ¬ (a ∈ Bad n τ) := fun h' => hnot.1
      (mem_iUnion₂.2 ⟨n, Finset.mem_range.2 (by omega), mem_iUnion.2 ⟨τ, h'⟩⟩)
    have hboth : 0 < (μ G) (Pat b n j (σ' τ) ∩ {χ | 1 / 8 < (ev (n • a) χ).re}) ∧
        0 < (μ G) (Pat b n j (σ' τ) ∩ {χ | (ev (n • a) χ).re < -(1 / 8)}) := by
      by_contra hc
      exact hgood ⟨haA, hn, h, hc⟩
    have e1 : Pat (Function.update b j a) n (j + 1) σ = Pat b n j (σ' τ) ∩ Up n a (σ j) := by
      have e2 : Finset.Ico n (j + 1) = insert j (Finset.Ico n j) := by
        ext i
        simp only [Finset.mem_insert, Finset.mem_Ico]
        omega
      have e3 : Pat (Function.update b j a) n j σ = Pat b n j (σ' τ) := by
        refine Pat_congr _ _ _ _ _ _ (fun i hi => ?_) (fun i hi => ?_)
        · rw [Function.update_of_ne (by omega : i ≠ j)]
        · show σ i = if h : i < j then τ ⟨i, h⟩ else false
          rw [dif_pos hi]
      rw [← e3]
      unfold Pat
      rw [e2, Finset.set_biInter_insert, Function.update_self, inter_comm]
    rw [e1]
    cases hs : σ j
    · exact hboth.2
    · exact hboth.1

theorem interpolation_set (hpos : ∀ n ∈ M, 0 < n) (hfib : ∀ n ∈ M, ∀ y : G, {x : G | x ∈ H ∧ n • x = y}.Finite)
    (h2 : ∀ n ∈ M, (∀ y : G, {x : G | x ∈ H ∧ (2 * n) • x = y}.Finite) ∨ (∀ x ∈ H, (2 * n) • x = 0))
    (A : Set G) (hA : A ⊆ H) (hAinf : A.Infinite) :
    ∃ b : ℕ → G, Function.Injective b ∧ (∀ i, b i ∈ A) ∧
      ∀ n ∈ M, ∀ s : ℕ → Bool, ∃ χ : Dual G, ∀ j, n ≤ j → χ ∈ Cl n (b j) (s j) := by
  classical
  let St : ℕ → Type := fun j => {b : ℕ → G // Good M b j ∧ (∀ i < j, b i ∈ A) ∧
    ∀ i < j, ∀ k < j, b i = b k → i = k}
  have h0 : Good M (fun _ : ℕ => (0 : G)) 0 := by
    intro n hn hn0 σ
    exact absurd hn0 (not_le.2 (hpos n hn))
  have hnext : ∀ j (s : St j), ∃ t : St (j + 1), ∀ i < j, t.1 i = s.1 i := by
    intro j s
    obtain ⟨a, ha, hne, hg⟩ := step_set H M hfib h2 A hA hAinf s.1 j s.2.1
    have hupd : ∀ i < j, Function.update s.1 j a i = s.1 i := fun i hi =>
      Function.update_of_ne (by omega : i ≠ j) _ _
    have hmem : ∀ i < j + 1, Function.update s.1 j a i ∈ A := by
      intro i hi
      by_cases h : i = j
      · rw [h, Function.update_self]
        exact ha
      · rw [hupd i (by omega)]
        exact s.2.2.1 i (by omega)
    have hinj : ∀ i < j + 1, ∀ k < j + 1, Function.update s.1 j a i = Function.update s.1 j a k → i = k := by
      intro i hi k hk h
      by_cases h1 : i = j
      · by_cases h3 : k = j
        · rw [h1, h3]
        · rw [h1, Function.update_self, hupd k (by omega)] at h
          exact absurd h.symm (hne k (by omega))
      · by_cases h3 : k = j
        · rw [h3, Function.update_self, hupd i (by omega)] at h
          exact absurd h (hne i (by omega))
        · rw [hupd i (by omega), hupd k (by omega)] at h
          exact s.2.2.2 i (by omega) k (by omega) h
    exact ⟨⟨Function.update s.1 j a, hg, hmem, hinj⟩, hupd⟩
  choose next hnext' using hnext
  let state : (j : ℕ) → St j := fun j =>
    Nat.rec (motive := St) ⟨fun _ => 0, h0, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩ (fun k s => next k s) j
  have hstate : ∀ j, state (j + 1) = next j (state j) := fun _ => rfl
  have hagree : ∀ j k, j ≤ k → ∀ i < j, (state k).1 i = (state j).1 i := by
    intro j k hjk
    induction hjk with
    | refl => exact fun _ _ => rfl
    | step h ih =>
      intro i hi
      rw [hstate, hnext' _ _ i (lt_of_lt_of_le hi h)]
      exact ih i hi
  set b : ℕ → G := fun i => (state (i + 1)).1 i with hb
  have hbj : ∀ j, ∀ i < j, b i = (state j).1 i := fun j i hi =>
    (hagree (i + 1) j hi i (Nat.lt_succ_self i)).symm
  have hGood : ∀ j, Good M b j := by
    intro j n hn hnj σ
    rw [Pat_congr b (state j).1 n j σ σ (hbj j) (fun _ _ => rfl)]
    exact (state j).2.1 n hn hnj σ
  refine ⟨b, fun i k h => ?_, fun i => ?_, fun n hn s => ?_⟩
  · have h1 := hbj (max i k + 1) i (by omega)
    have h3 := hbj (max i k + 1) k (by omega)
    exact (state (max i k + 1)).2.2.2 i (by omega) k (by omega) (h1.symm.trans (h.trans h3))
  · exact (state (i + 1)).2.2.1 i (Nat.lt_succ_self i)
  · set C : ℕ → Set (Dual G) := fun J => ⋂ i ∈ Finset.Ico n J, Cl n (b i) (s i) with hC
    have hclosed : ∀ J, IsClosed (C J) := fun J => isClosed_biInter (fun i _ => isClosed_Cl _ _ _)
    have hanti : ∀ J, C (J + 1) ⊆ C J := by
      intro J x hx
      simp only [hC, mem_iInter] at hx ⊢
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact hx i (Finset.mem_Ico.2 ⟨hi.1, by omega⟩)
    have hne : ∀ J, (C J).Nonempty := by
      intro J
      by_cases h : n ≤ J
      · have h1 := hGood J n hn h s
        obtain ⟨χ, hχ⟩ := nonempty_of_measure_ne_zero h1.ne'
        refine ⟨χ, ?_⟩
        simp only [Pat, mem_iInter] at hχ
        simp only [hC, mem_iInter]
        exact fun i hi => Up_subset_Cl _ _ _ (hχ i hi)
      · have e : Finset.Ico n J = ∅ := Finset.Ico_eq_empty (by omega)
        refine ⟨0, ?_⟩
        simp only [hC, e]
        simp
    obtain ⟨χ, hχ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hanti hne
      (hclosed 0).isCompact hclosed
    refine ⟨χ, fun j hj => ?_⟩
    have h1 := mem_iInter.1 hχ (j + 1)
    simp only [hC, mem_iInter] at h1
    exact h1 j (Finset.mem_Ico.2 ⟨hj, Nat.lt_succ_self j⟩)

/-! ### Many ultrafilters with different limits -/

/-! ### Many limits on every infinite set -/

theorem lam_translate (a : G) (p : Ultrafilter G) : lam (p.map (fun x => a + x)) = iota a + lam p := by
  refine lam_eq ?_
  have h : Tendsto iota (p : Filter G) (𝓝 (lam p)) := lim_lam p
  have h2 : Tendsto (fun x => iota a + iota x) (p : Filter G) (𝓝 (iota a + lam p)) :=
    tendsto_const_nhds.add h
  unfold Lim
  rw [Ultrafilter.coe_map, tendsto_map'_iff]
  have e : (iota (G := G) ∘ fun x => a + x) = fun x => iota a + iota x := by
    funext x
    simp
  rw [e]
  exact h2

/-- The multiplier `1` alone, when the fibres of `x ↦ 2 x` on `A` are finite or `2 A = 0`. -/
theorem distinct_limits_core (A : Set G) (hAinf : A.Infinite)
    (h2 : (∀ y : G, {x : G | x ∈ A ∧ (2 * 1) • x = y}.Finite) ∨ (∀ x ∈ A, (2 * 1) • x = 0)) :
    ∃ b : ℕ → G, Function.Injective b ∧ (∀ i, b i ∈ A) ∧
      ∀ v w : Ultrafilter ℕ, (v : Filter ℕ) ≤ cofinite → (w : Filter ℕ) ≤ cofinite →
        lam (v.map b) = lam (w.map b) → v = w := by
  have hfib : ∀ n ∈ ({1} : Set ℕ), ∀ y : G, {x : G | x ∈ A ∧ n • x = y}.Finite := by
    intro n hn y
    rw [mem_singleton_iff] at hn
    subst hn
    refine (finite_singleton y).subset (fun x hx => ?_)
    have h := hx.2
    rw [one_nsmul] at h
    exact h
  obtain ⟨b, hbinj, hbA, hint⟩ := interpolation_set A {1} (by simp) hfib
    (by
      intro n hn
      rw [mem_singleton_iff] at hn
      subst hn
      exact h2) A subset_rfl hAinf
  refine ⟨b, hbinj, hbA, fun v w hv hw h => ?_⟩
  refine nsmul_lam_injective b 1 (hint 1 rfl) v w hv hw ?_
  rw [one_nsmul, one_nsmul]
  exact h

/-- Every infinite subset of an abelian group contains a sequence of distinct points on
which different free ultrafilters have different limits in the Bohr compactification. -/
theorem distinct_limits (A : Set G) (hAinf : A.Infinite) :
    ∃ b : ℕ → G, Function.Injective b ∧ (∀ i, b i ∈ A) ∧
      ∀ v w : Ultrafilter ℕ, (v : Filter ℕ) ≤ cofinite → (w : Filter ℕ) ≤ cofinite →
        lam (v.map b) = lam (w.map b) → v = w := by
  classical
  by_cases hc : ∃ c : G, {a ∈ A | a + a = c}.Infinite
  · obtain ⟨c, hc⟩ := hc
    obtain ⟨a0, ha0⟩ := hc.nonempty
    set B : Set G := (fun a => a - a0) '' {a ∈ A | a + a = c} with hB
    have hBinf : B.Infinite := hc.image (fun x _ y _ h => sub_left_injective h)
    have hB2 : ∀ x ∈ B, (2 * 1) • x = 0 := by
      rintro x ⟨a, ha, rfl⟩
      show (2 * 1) • (a - a0) = 0
      rw [mul_one, two_nsmul]
      have e : a - a0 + (a - a0) = (a + a) - (a0 + a0) := by abel
      rw [e, ha.2, ha0.2, sub_self]
    obtain ⟨b, hbinj, hbB, hb⟩ := distinct_limits_core B hBinf (Or.inr hB2)
    refine ⟨fun i => a0 + b i, fun i j h => hbinj (add_left_cancel h), fun i => ?_, fun v w hv hw h => ?_⟩
    · obtain ⟨a, ha, e⟩ := hbB i
      have e2 : a0 + b i = a := by
        rw [← e]
        show a0 + (a - a0) = a
        abel
      show a0 + b i ∈ A
      rw [e2]
      exact ha.1
    · refine hb v w hv hw ?_
      have e : ∀ z : Ultrafilter ℕ,
          lam (z.map (fun i => a0 + b i)) = iota a0 + lam (z.map b) := by
        intro z
        have e1 : z.map (fun i => a0 + b i) = (z.map b).map (fun x => a0 + x) := by
          rw [Ultrafilter.map_map]
          rfl
        rw [e1, lam_translate]
      rw [e v, e w] at h
      exact add_left_cancel h
  · refine distinct_limits_core A hAinf (Or.inl (fun y => ?_))
    have h : {a ∈ A | a + a = y}.Finite := not_infinite.1 (fun h => hc ⟨y, h⟩)
    refine h.subset (fun x hx => ⟨hx.1, ?_⟩)
    have h3 := hx.2
    rwa [mul_one, two_nsmul] at h3

/-! ### Convergence in the generated PG -/

/-- `F` converges to `d` in the PG generated by the ultrafilters in `S`. -/
def ConvTo (S : Set (Ultrafilter G)) (F : Filter G) (d : G) : Prop :=
  Filter.map (fun x => x - d) F ∈ genFam (ultraGen S)

theorem lam_of_convTo (S : Set (Ultrafilter G)) (p : Ultrafilter G) (d : G) (h : ConvTo S p d) :
    lam p - iota d ∈ K (ultraGen S) := by
  have h1 : (p.map (fun x => x - d) : Filter G) ∈ genFam (ultraGen S) := by
    rw [Ultrafilter.coe_map]
    exact h
  have h2 := lim_mem_K (ultraGen S) _ h1
  have e : p.map (fun x => x - d) = p.map (fun x => -d + x) := by
    congr 1
    funext x
    abel
  rw [e, lam_translate, map_neg] at h2
  rwa [sub_eq_neg_add]

theorem mk_K_lt (S : Set (Ultrafilter G)) (hS : #S < (2 : Cardinal.{0}) ^ 𝔠) :
    #(K (ultraGen S)) < (2 : Cardinal.{0}) ^ 𝔠 := by
  have h1 : #(L (ultraGen S)) ≤ #S :=
    (Cardinal.mk_le_mk_of_subset (L_ultraGen S)).trans Cardinal.mk_image_le
  have h2 : #(AddSubgroup.closure (L (ultraGen S))) ≤ max ℵ₀ #(L (ultraGen S)) := mk_closure_le _
  exact lt_of_le_of_lt h2 (max_lt aleph0_lt_two_pow_c (lt_of_le_of_lt h1 hS))

/-- **The theorem.** Fewer than `2 ^ 𝔠` generators, a set `D` of fewer than `2 ^ 𝔠`
points and an infinite set `A`: some free ultrafilter containing `A` converges to no
point of `D`. -/
theorem exists_divergent (S : Set (Ultrafilter G)) (hS : #S < (2 : Cardinal.{0}) ^ 𝔠)
    (D : Set G) (hD : #D < (2 : Cardinal.{0}) ^ 𝔠) (A : Set G) (hA : A.Infinite) :
    ∃ p : Ultrafilter G, A ∈ p ∧ (p : Filter G) ≤ cofinite ∧ ∀ d ∈ D, ¬ ConvTo S p d := by
  classical
  obtain ⟨b, hbinj, hbA, hb⟩ := distinct_limits A hA
  have hmemA : ∀ v : Ultrafilter ℕ, A ∈ v.map b := by
    intro v
    rw [Ultrafilter.mem_map]
    have e : b ⁻¹' A = univ := eq_univ_of_forall hbA
    rw [e]
    exact Filter.univ_mem
  have hfree : ∀ v : Ultrafilter ℕ, (v : Filter ℕ) ≤ cofinite → (v.map b : Filter G) ≤ cofinite := by
    intro v hv
    rw [Ultrafilter.coe_map]
    exact (Filter.map_mono hv).trans hbinj.tendsto_cofinite
  by_contra hcon
  have hbad : ∀ v : {v : Ultrafilter ℕ // (v : Filter ℕ) ≤ cofinite},
      ∃ d : D, ConvTo S (v.1.map b) d.1 := by
    intro v
    by_contra h
    exact hcon ⟨v.1.map b, hmemA v.1, hfree v.1 v.2, fun d hd hc => h ⟨⟨d, hd⟩, hc⟩⟩
  choose d hd using hbad
  have hk : ∀ v : {v : Ultrafilter ℕ // (v : Filter ℕ) ≤ cofinite},
      lam (v.1.map b) - iota (d v).1 ∈ K (ultraGen S) :=
    fun v => lam_of_convTo S _ _ (hd v)
  let f : {v : Ultrafilter ℕ // (v : Filter ℕ) ≤ cofinite} → D × K (ultraGen S) :=
    fun v => (d v, ⟨_, hk v⟩)
  have hf : Function.Injective f := by
    intro v w h
    have h1 : d v = d w := congrArg Prod.fst h
    have h2 : lam (v.1.map b) - iota (d v).1 = lam (w.1.map b) - iota (d w).1 :=
      congrArg (fun z => (z.2 : Circles G)) h
    rw [h1] at h2
    exact Subtype.ext (hb v.1 w.1 v.2 w.2 (sub_left_injective h2))
  have h1 := le_mk_free.trans (Cardinal.mk_le_of_injective hf)
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id] at h1
  have h2 : #D * #(K (ultraGen S)) < (2 : Cardinal.{0}) ^ 𝔠 :=
    Cardinal.mul_lt_of_lt aleph0_lt_two_pow_c.le hD (mk_K_lt S hS)
  exact absurd h1 (not_le.2 h2)

/-- No sequence of distinct points converges. -/
theorem no_convergent_sequence (S : Set (Ultrafilter G)) (hS : #S < (2 : Cardinal.{0}) ^ 𝔠)
    (b : ℕ → G) (hb : Function.Injective b) (d : G) : ¬ ConvTo S (Filter.map b cofinite) d := by
  intro h
  have hD : #({d} : Set G) < (2 : Cardinal.{0}) ^ 𝔠 := by
    rw [Cardinal.mk_singleton]
    exact Cardinal.one_lt_aleph0.trans aleph0_lt_two_pow_c
  obtain ⟨p, hpA, hpfree, hp⟩ := exists_divergent S hS {d} hD (range b) (infinite_range_of_injective hb)
  have hle : (p : Filter G) ≤ Filter.map b cofinite := by
    intro s hs
    have h1 : (b ⁻¹' s)ᶜ.Finite := hs
    have h2 : (b '' (b ⁻¹' s)ᶜ)ᶜ ∈ (p : Filter G) := hpfree (h1.image b).compl_mem_cofinite
    refine mem_of_superset (inter_mem (show range b ∈ (p : Filter G) from hpA) h2) ?_
    rintro x ⟨⟨i, rfl⟩, hx⟩
    by_contra hxs
    exact hx ⟨i, hxs, rfl⟩
  refine hp d rfl ?_
  haveI : (p : Filter G).NeBot := p.neBot
  exact (genFam_nullFamily _).finer _ h _ (Filter.map_mono hle) (Filter.NeBot.map p.neBot _)

/-- No infinite set of fewer than `2 ^ 𝔠` points is compact. -/
theorem no_small_compact (S : Set (Ultrafilter G)) (hS : #S < (2 : Cardinal.{0}) ^ 𝔠)
    (A : Set G) (hA : A.Infinite) (hcard : #A < (2 : Cardinal.{0}) ^ 𝔠) :
    ∃ p : Ultrafilter G, A ∈ p ∧ ∀ d ∈ A, ¬ ConvTo S p d := by
  obtain ⟨p, hpA, _, hp⟩ := exists_divergent S hS A hcard A hA
  exact ⟨p, hpA, hp⟩

/-- A filter with a countable base that converges contains a finite set. -/
theorem finite_mem_of_countably_generated (S : Set (Ultrafilter G))
    (hS : #S < (2 : Cardinal.{0}) ^ 𝔠) (F : Filter G) [F.IsCountablyGenerated] (d : G)
    (h : ConvTo S F d) : ∃ E ∈ F, E.Finite := by
  classical
  by_contra hcon
  obtain ⟨s, hs⟩ := F.exists_antitone_basis
  have hinf : ∀ n, (s n).Infinite := fun n hfin => hcon ⟨s n, hs.mem n, hfin⟩
  have hpick : ∀ (n : ℕ) (T : Finset G), ∃ x ∈ s n, x ∉ T := fun n T =>
    (hinf n).exists_notMem_finset T
  choose pick hpick1 hpick2 using hpick
  let T : ℕ → Finset G := fun n => Nat.rec ∅ (fun k Tk => insert (pick k Tk) Tk) n
  have hT : ∀ n, T (n + 1) = insert (pick n (T n)) (T n) := fun n => rfl
  let x : ℕ → G := fun n => pick n (T n)
  have hmono : Monotone T := monotone_nat_of_le_succ (fun n => by
    rw [hT]
    exact Finset.subset_insert _ _)
  have hxinj : Function.Injective x := by
    have key : ∀ i j, i < j → x i ≠ x j := by
      intro i j hij he
      have h1 : x i ∈ T (i + 1) := by
        rw [hT]
        exact Finset.mem_insert_self _ _
      have h2 : x i ∈ T j := hmono (Nat.succ_le_of_lt hij) h1
      rw [he] at h2
      exact hpick2 j (T j) h2
    intro i j he
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd he (key i j h')
    · exact h'
    · exact absurd he.symm (key j i h')
  have hle : Filter.map x cofinite ≤ F := by
    rw [Nat.cofinite_eq_atTop]
    intro t ht
    obtain ⟨n, hn⟩ := hs.mem_iff.1 ht
    refine mem_map.2 (mem_atTop_sets.2 ⟨n, fun m hm => hn (hs.antitone hm (hpick1 m (T m)))⟩)
  refine no_convergent_sequence S hS x hxinj d ?_
  exact (genFam_nullFamily _).finer _ h _ (Filter.map_mono hle)
    (Filter.NeBot.map (Filter.NeBot.map (Filter.cofinite_neBot) x) _)

/-- The bound `2 ^ 𝔠` cannot be improved: all ultrafilters containing `range b` give a
convergent sequence. -/
theorem sharp (b : ℕ → G) (d : G) :
    ConvTo {u : Ultrafilter G | range b ∈ u} (Filter.map (fun n => b n + d) cofinite) d := by
  have e : Filter.map (fun x => x - d) (Filter.map (fun n => b n + d) cofinite)
      = Filter.map b cofinite := by
    rw [Filter.map_map]
    congr 1
    funext n
    simp
  unfold ConvTo
  rw [e]
  refine ⟨Filter.NeBot.map Filter.cofinite_neBot b, fun U hU => ⟨U, SumClosure.gen ⟨U, ?_, rfl⟩, le_rfl⟩⟩
  exact hU (mem_map.2 (univ_mem' (fun n => mem_range_self n)))

end Seq

end PG
