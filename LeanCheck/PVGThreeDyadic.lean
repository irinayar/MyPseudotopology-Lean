import LeanCheck.PVGThreeDescribe
import LeanCheck.PVGTwoKR

/-!
# PVGthree: rigid and non-rigid dyadic sequences

`δ_k = 2^(-L_k)` with strictly increasing exponents.

* `finest_lqc_rigid` (first theorem) : under rigidity `γ_δ` is the finest locally quasi-convex serving topology;
* `rig_of_bounded` : bounded gaps `L_(k+1) - L_k` give a bounded `U(ε)` and rigidity;
* `not_rig` : unbounded gaps and `A(δ)` inside the dyadic rationals give no rigidity;
* `rig_iff` : (assuming Kalton–Roberts) `δ` is rigid iff the parity topologies generate a topology finer than all
  serving ones; `finest_of_rig` : then it is the finest serving topology.

Order of topologies as in Mathlib: `γ₁ ≤ γ₂` means that `γ₁` is finer. Sequences are indexed from `0`.
-/

open Filter Topology Set UniformSpace
open scoped Pointwise

namespace PVG
namespace Three
open Two Q95 Lac

variable [D : Dy]

/-- Under rigidity `γ_δ` is the finest locally quasi-convex topology with the total boundedness. Generated from
`finest_lqc` of `PVGTwoFinest`. -/
theorem finest_lqc (γ : TopologicalSpace ℝ) (hg : @IsTopologicalAddGroup ℝ γ _)
    (heu : euclidNhds 0 ≤ @nhds ℝ γ 0) (hq : LQC γ)
    (htb : ∀ a : ℝ, InA dy sT a → Tb (@nhds ℝ γ 0) (dil a Sset)) : gamTop dy ≤ γ := by
  classical
  refine le_of_nhds_zero _ _ (gam_group _) hg fun W hW => ?_
  obtain ⟨S, hS, hU, hUW⟩ := hq W hW
  set E := {c : ℝ | ∃ χ ∈ S, ∀ x : ℝ, χ x = ((c * x : ℝ) : AddCircle (1 : ℝ))} with hE
  have hchar : ∀ χ ∈ S, ∃ c ∈ E, ∀ x : ℝ, χ x = ((c * x : ℝ) : AddCircle (1 : ℝ)) := by
    intro χ hχ
    have h0 : Tendsto χ (euclidNhds 0) (@nhds (AddCircle (1 : ℝ)) circleTop 0) := by
      have h := (@Continuous.tendsto ℝ (AddCircle (1 : ℝ)) γ circleTop _ (hS χ hχ) 0).mono_left heu
      rwa [map_zero] at h
    obtain ⟨c, hc⟩ := char_of_tendsto χ h0
    exact ⟨c, ⟨χ, hχ, hc⟩, hc⟩
  have hmem : ∀ x : ℝ, (∀ χ ∈ S, ‖χ x‖ ≤ 1 / 4) → ∀ c ∈ E, dint (c * x) ≤ 1 / 4 := by
    rintro x hx c ⟨χ, hχ, hc⟩
    have := hx χ hχ
    rw [hc x] at this
    exact this
  obtain ⟨η, hη, hb⟩ := ball_of_euclid (heu hU)
  have hbd : E ⊆ Icc (-(1 / η)) (1 / η) := by
    intro c hc
    rw [mem_Icc, ← abs_le]
    by_contra h
    push Not at h
    have hc0 : c ≠ 0 := by
      intro h1
      rw [h1, abs_zero] at h
      exact absurd h (not_lt.2 (by positivity))
    have hx : |(2 * c)⁻¹| < η := by
      rw [abs_inv, abs_mul, abs_two, inv_lt_iff_one_lt_mul₀ (by positivity)]
      rw [div_lt_iff₀ hη] at h
      nlinarith [abs_nonneg c]
    have h2 := hmem _ (hb _ hx) c hc
    have e1 : c * (2 * c)⁻¹ = 1 / 2 := by field_simp
    rw [e1, dint_half] at h2
    norm_num at h2
  set V0 := {x : ℝ | ∀ c ∈ E, dint (c * x) ≤ 1 / 32} with hV0
  have hV0mem : V0 ∈ @nhds ℝ γ 0 := by
    refine Filter.mem_of_superset (nsmul_nhds γ hg _ hU 8) fun x hx c hc => ?_
    have h1 : ∀ k : ℕ, 1 ≤ k → k ≤ 8 → dint (k * (c * x)) ≤ 1 / 4 := by
      intro k _ hk
      have h2 := hmem _ (hx k (Finset.mem_range.2 (Nat.lt_succ_of_le hk))) c hc
      rwa [mul_left_comm] at h2
    have h3 := dint_le_of_multiples 8 (by norm_num) (c * x) h1
    exact h3.trans (by norm_num)
  obtain ⟨ε, hε, F, hF⟩ := Dy.rig γ hg heu (fun a ha => htb a ha) V0 hV0mem
  set Mf := (∑ f ∈ F, |f|) + 1 with hMf
  have hMf0 : 0 < Mf := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => abs_nonneg _) one_pos
  have htot : TotallyBounded E := (isCompact_Icc.totallyBounded).subset hbd
  set r := (1 / 32) / Mf with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨t, htE, htfin, hcov⟩ := Metric.finite_approx_of_totallyBounded htot r hr0
  refine (mem_nhds_gam dy W).2 ⟨bset htfin.toFinset (1 / 32), bset_mem _ (by norm_num), ε, hε, fun x hxB hxd => ?_⟩
  refine hUW fun χ hχ => ?_
  obtain ⟨c, hcE, hc⟩ := hchar χ hχ
  rw [hc x]
  obtain ⟨c', hc't, hcc'⟩ := mem_iUnion₂.1 (hcov hcE)
  have hdist : |c - c'| < r := by simpa [Metric.mem_ball, Real.dist_eq] using hcc'
  obtain ⟨f, hfF, hfV⟩ := hF x hxd
  have hfM : |f| ≤ Mf := by
    have h1 := Finset.single_le_sum (f := fun g : ℝ => |g|) (fun _ _ => abs_nonneg _) hfF
    simp only [hMf]
    linarith
  have t1 : dint (c' * x) ≤ 1 / 32 := (hxB c' (htfin.mem_toFinset.2 hc't)).le
  have t2 : dint ((c - c') * f) ≤ 1 / 32 := by
    refine (dint_le_abs _).trans ?_
    rw [abs_mul]
    have h1 : |c - c'| * |f| ≤ r * Mf := mul_le_mul hdist.le hfM (abs_nonneg _) hr0.le
    have e1 : r * Mf = 1 / 32 := by rw [hr]; exact div_mul_cancel₀ _ hMf0.ne'
    linarith
  have t3 : dint (c * (x - f)) ≤ 1 / 32 := hfV c hcE
  have t4 : dint (c' * (x - f)) ≤ 1 / 32 := hfV c' (htE hc't)
  have e1 : c * x = c' * x + (c - c') * f + (c * (x - f) - c' * (x - f)) := by ring
  show dint (c * x) ≤ 1 / 4
  rw [e1]
  have a1 := dint_add_le' (c' * x + (c - c') * f) (c * (x - f) - c' * (x - f))
  have a2 := dint_add_le' (c' * x) ((c - c') * f)
  have a3 := dint_sub_le (c * (x - f)) (c' * (x - f))
  linarith

omit D

lemma dyseq_ne (L : ℕ → ℕ) (k : ℕ) : dyseq L k ≠ 0 := by
  unfold dyseq
  positivity

lemma dyseq_le_one (L : ℕ → ℕ) (k : ℕ) : |dyseq L k| ≤ 1 := by
  unfold dyseq
  rw [abs_of_pos (by positivity)]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)

lemma dyseq_tendsto (L : ℕ → ℕ) (hL : StrictMono L) : Tendsto (dyseq L) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero (fun k => by unfold dyseq; positivity) (fun k => ?_) h1
  unfold dyseq
  rw [inv_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two (hL.id_le k))

lemma dyseq_mul (L : ℕ → ℕ) (k : ℕ) (x : ℝ) : dyseq L k * x = x / 2 ^ L k := by
  unfold dyseq
  rw [inv_mul_eq_div]

/-- Bounded gaps: `U(ε)` is bounded, hence `δ` is rigid. -/
theorem rig_of_bounded (L : ℕ → ℕ) (hL : StrictMono L) (G : ℕ) (hG : ∀ k, L (k + 1) ≤ L k + G) :
    (∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ, ∀ x : ℝ, (∀ k, dint (dyseq L k * x) ≤ ε) → |x| ≤ B) ∧ Rig (dyseq L) := by
  set ε : ℝ := ((2 : ℝ) ^ (G + 3))⁻¹ with hε
  have hε0 : 0 < ε := by positivity
  have hbdd : ∀ x : ℝ, (∀ k, dint (dyseq L k * x) ≤ ε) → |x| ≤ ε * 2 ^ L 0 := by
    intro x hx
    have hr : ∀ k, |x / 2 ^ L k - round (x / 2 ^ L k)| ≤ ε := by
      intro k
      rw [← Two.dint_eq, ← dyseq_mul]
      exact hx k
    have hstep : ∀ k, round (x / 2 ^ L (k + 1)) = 0 → round (x / 2 ^ L k) = 0 := by
      intro k hk
      have hlt : L k < L (k + 1) := hL (Nat.lt_succ_self k)
      set g := L (k + 1) - L k with hg
      have hgG : g ≤ G := by
        have := hG k
        omega
      have e : x / 2 ^ L k = 2 ^ g * (x / 2 ^ L (k + 1)) := by
        have h2 : (2 : ℝ) ^ L (k + 1) = 2 ^ L k * 2 ^ g := by
          rw [← pow_add]
          congr 1
          omega
        rw [h2]
        field_simp
      have h3 := hr (k + 1)
      rw [hk, Int.cast_zero, sub_zero] at h3
      have h4 : |x / 2 ^ L k| < 1 / 2 := by
        rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ g)]
        have h5 : (2 : ℝ) ^ g * |x / 2 ^ L (k + 1)| ≤ 2 ^ G * ε :=
          mul_le_mul (pow_le_pow_right₀ one_le_two hgG) h3 (abs_nonneg _) (by positivity)
        have h6 : (2 : ℝ) ^ G * ε = 1 / 8 := by
          rw [hε, pow_add]
          field_simp
          norm_num
        linarith
      refine round_near _ 0 ?_
      rwa [Int.cast_zero, sub_zero]
    obtain ⟨K, hK⟩ : ∃ K : ℕ, round (x / 2 ^ L K) = 0 := by
      obtain ⟨n, hn⟩ := exists_nat_gt (2 * |x|)
      refine ⟨n, round_near _ 0 ?_⟩
      rw [Int.cast_zero, sub_zero, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ L n),
        div_lt_iff₀ (by positivity)]
      have h2 : (n : ℝ) ≤ 2 ^ L n := by
        have h3 : n ≤ 2 ^ L n := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right two_pos (hL.id_le n))
        exact_mod_cast h3
      linarith
    have h0 : round (x / 2 ^ L 0) = 0 := by
      have : ∀ j, j ≤ K → round (x / 2 ^ L (K - j)) = 0 := by
        intro j
        induction j with
        | zero => intro _; simpa using hK
        | succ j ih =>
          intro hj
          refine hstep _ ?_
          have e : K - (j + 1) + 1 = K - j := by omega
          rw [e]
          exact ih (by omega)
      simpa using this K le_rfl
    have h1 := hr 0
    rw [h0, Int.cast_zero, sub_zero, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ L 0),
      div_le_iff₀ (by positivity)] at h1
    exact h1
  refine ⟨⟨ε, hε0, ε * 2 ^ L 0, hbdd⟩, fun γ _ heu _ W hW => ⟨ε, hε0, ?_⟩⟩
  have hW' := heu hW
  obtain ⟨r, hr0, hr⟩ := Metric.mem_nhds_iff.1 hW'
  set B := ε * 2 ^ L 0 with hB
  have htot : TotallyBounded (Icc (-B) B) := isCompact_Icc.totallyBounded
  obtain ⟨t, -, htfin, hcov⟩ := Metric.finite_approx_of_totallyBounded htot r hr0
  refine ⟨htfin.toFinset, fun x hx => ?_⟩
  have hxB : x ∈ Icc (-B) B := abs_le.1 (hbdd x hx)
  obtain ⟨f, hf, h⟩ := mem_iUnion₂.1 (hcov hxB)
  refine ⟨f, htfin.mem_toFinset.2 hf, hr ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
  rwa [Metric.mem_ball, Real.dist_eq] at h

lemma dint_intZ (z : ℤ) : dint (z : ℝ) = 0 := by
  rw [Two.dint_eq, round_intCast]
  simp

/-- One of two points has all squares at distance at least `i`. -/
lemma off_squares (i N : ℕ) (hN : (3 * i + 3) ^ 2 ≤ N) :
    ∃ M : ℕ, N + 2 * i + 1 ≤ M ∧ M ≤ N + 4 * i + 2 ∧ ∀ n : ℕ, M + i ≤ n ^ 2 ∨ n ^ 2 + i ≤ M := by
  by_contra h
  push Not at h
  obtain ⟨a, ha1, ha2⟩ := h (N + 2 * i + 1) le_rfl (by omega)
  obtain ⟨b, hb1, hb2⟩ := h (N + 4 * i + 2) (by omega) le_rfl
  have hab : a < b := by
    by_contra hc
    have := Nat.pow_le_pow_left (not_lt.1 hc) 2
    omega
  have ha : 3 * i + 3 ≤ a := by
    by_contra hc
    have h1 := Nat.pow_le_pow_left (show a ≤ 3 * i + 2 by omega) 2
    have h2 : (3 * i + 2) ^ 2 + 6 * i + 5 = (3 * i + 3) ^ 2 := by ring
    omega
  have h1 := Nat.pow_le_pow_left (show a + 1 ≤ b by omega) 2
  have h2 : (a + 1) ^ 2 = a ^ 2 + 2 * a + 1 := by ring
  omega

/-- Unbounded gaps and `A(δ)` inside the dyadic rationals: `δ` is not rigid. -/
theorem not_rig (L : ℕ → ℕ) (hL : StrictMono L) (hgaps : ∀ G : ℕ, ∃ k, L k + G ≤ L (k + 1))
    (hA : ∀ a : ℝ, InA (dyseq L) sT a → ∃ r : ℕ, ∃ z : ℤ, a = z / 2 ^ r) : ¬ Rig (dyseq L) := by
  classical
  intro hrig
  have hlarge : ∀ G K : ℕ, ∃ k, K ≤ k ∧ L k + G ≤ L (k + 1) := by
    intro G K
    obtain ⟨k, hk⟩ := hgaps (G + (∑ j ∈ Finset.range K, L (j + 1)) + 1)
    refine ⟨k, ?_, by omega⟩
    by_contra hc
    have := Finset.single_le_sum (f := fun j => L (j + 1)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (not_le.1 hc))
    omega
  have hex : ∀ i p : ℕ, ∃ q : ℕ × ℕ, (3 * i + 3) ^ 2 ≤ L q.1 ∧ p + i + 2 ≤ L q.1 ∧
      L q.1 + (5 * i + 2) ≤ L (q.1 + 1) ∧ L q.1 + 2 * i + 1 ≤ q.2 ∧ q.2 ≤ L q.1 + 4 * i + 2 ∧
      ∀ n : ℕ, q.2 + i ≤ n ^ 2 ∨ n ^ 2 + i ≤ q.2 := by
    intro i p
    obtain ⟨k, hk, hgap⟩ := hlarge (5 * i + 2) (max ((3 * i + 3) ^ 2) (p + i + 2))
    have h1 := hk.trans (hL.id_le k)
    have h2 : (3 * i + 3) ^ 2 ≤ L k := (le_max_left _ _).trans h1
    obtain ⟨M, hM1, hM2, hM3⟩ := off_squares i (L k) h2
    exact ⟨(k, M), h2, (le_max_right _ _).trans h1, hgap, hM1, hM2, hM3⟩
  choose pick hp1 hp2 hp3 hp4 hp5 hp6 using hex
  let q : ℕ → ℕ × ℕ := fun i => Nat.rec (pick 0 0) (fun j prev => pick (j + 1) prev.2) i
  let k : ℕ → ℕ := fun i => (q i).1
  let M : ℕ → ℕ := fun i => (q i).2
  have hq : ∀ i, ∃ p, q i = pick i p := by
    intro i
    cases i with
    | zero => exact ⟨0, rfl⟩
    | succ j => exact ⟨(q j).2, rfl⟩
  have hprop : ∀ i, L (k i) + (5 * i + 2) ≤ L (k i + 1) ∧ L (k i) + 2 * i + 1 ≤ M i ∧
      M i ≤ L (k i) + 4 * i + 2 ∧ ∀ n : ℕ, M i + i ≤ n ^ 2 ∨ n ^ 2 + i ≤ M i := by
    intro i
    obtain ⟨p, hp⟩ := hq i
    simp only [k, M, hp]
    exact ⟨hp3 i p, hp4 i p, hp5 i p, hp6 i p⟩
  have hstep : ∀ i, M i + 3 ≤ M (i + 1) := by
    intro i
    have h1 : q (i + 1) = pick (i + 1) (q i).2 := rfl
    have h2 := hp2 (i + 1) (q i).2
    have h3 := hp4 (i + 1) (q i).2
    simp only [M, h1]
    omega
  have hMmono : StrictMono M := strictMono_nat_of_lt_succ fun i => by
    have := hstep i
    omega
  have hMfar : ∀ i j, i < j → M i + 3 ≤ M j := by
    intro i j hij
    exact (hstep i).trans (hMmono.monotone hij)
  have hInA : ∀ a : ℝ, InA (dyseq L) sT a → InA (dyseq M) sT a := by
    intro a ha ε hε
    obtain ⟨r, z, rfl⟩ := hA a ha
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (x := ε / (|(z : ℝ)| + 1)) (by positivity)
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine eventually_atTop.2 ⟨max (r + 1) m, fun i hi n => ?_⟩
    have hir : r + 1 ≤ i := le_trans (le_max_left _ _) hi
    have him : m ≤ i := le_trans (le_max_right _ _) hi
    have hs : sT n = (2 : ℝ) ^ ((n + 1) ^ 2) := rfl
    rw [hs]
    rcases (hprop i).2.2.2 (n + 1) with h | h
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show M i + r ≤ (n + 1) ^ 2 by omega)
      have e : (z : ℝ) / 2 ^ r * dyseq M i * 2 ^ ((n + 1) ^ 2) = ((z * 2 ^ d : ℤ) : ℝ) := by
        unfold dyseq
        rw [hd, pow_add, pow_add]
        push_cast
        field_simp
      rw [e, dint_intZ]
      exact hε.le
    · refine (dint_le_abs _).trans ?_
      have e : |(z : ℝ) / 2 ^ r * dyseq M i * 2 ^ ((n + 1) ^ 2)| =
          |(z : ℝ)| * (2 ^ ((n + 1) ^ 2) / 2 ^ M i) / 2 ^ r := by
        unfold dyseq
        rw [abs_mul, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ r),
          abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ M i)⁻¹),
          abs_of_pos (by positivity : (0 : ℝ) < 2 ^ ((n + 1) ^ 2))]
        ring
      have h2 : (2 : ℝ) ^ ((n + 1) ^ 2) / 2 ^ M i ≤ (1 / 2) ^ m := by
        rw [div_le_iff₀ (by positivity), one_div, inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity),
          ← pow_add]
        exact pow_le_pow_right₀ one_le_two (by omega)
      have h3 : |(z : ℝ)| * (1 / 2) ^ m ≤ ε := by
        have h4 : (|(z : ℝ)| + 1) * (1 / 2) ^ m ≤ ε := by
          have := (lt_div_iff₀ (by positivity : (0 : ℝ) < |(z : ℝ)| + 1)).1 hm
          linarith
        have h5 : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
        nlinarith
      rw [e]
      refine (div_le_self (by positivity) (one_le_pow₀ one_le_two)).trans ?_
      exact (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)).trans h3
  -- the points that no finite set of translates covers
  set x : ℕ → ℝ := fun i => 2 ^ (M i - 1) with hx
  have hM1 : ∀ i, 1 ≤ M i := fun i => by
    have := (hprop i).2.1
    omega
  have hxU : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ j, dint (dyseq L j * x i) ≤ ε := by
    intro ε hε
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    refine eventually_atTop.2 ⟨m, fun i hi j => ?_⟩
    obtain ⟨h1, h2, h3, -⟩ := hprop i
    rcases le_or_gt j (k i) with hj | hj
    · have hLj : L j ≤ M i - 1 := by
        have := hL.monotone hj
        omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hLj
      have e : dyseq L j * x i = (((2 : ℤ) ^ d : ℤ) : ℝ) := by
        simp only [dyseq, hx]
        rw [hd, pow_add]
        push_cast
        field_simp
      rw [e, dint_intZ]
      exact hε.le
    · have hLj : M i - 1 + i ≤ L j := by
        have := hL.monotone (show k i + 1 ≤ j from hj)
        omega
      refine (dint_le_abs _).trans ?_
      rw [dyseq_mul, abs_of_pos (by simp only [hx]; positivity)]
      refine le_of_lt (lt_of_le_of_lt ?_ hm)
      simp only [hx]
      rw [div_le_iff₀ (by positivity), one_div, inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity),
        ← pow_add]
      exact pow_le_pow_right₀ one_le_two (by omega)
  have hhalf : ∀ i, dyseq M i * x i = 1 / 2 := by
    intro i
    have h := hM1 i
    have e : (2 : ℝ) ^ M i = 2 ^ (M i - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    simp only [dyseq, hx]
    rw [e]
    field_simp
  have hsmall : ∀ i j, i < j → dint (dyseq M j * x i) ≤ 1 / 16 := by
    intro i j hij
    have h := hMfar i j hij
    have h1 := hM1 i
    refine (dint_le_abs _).trans ?_
    rw [dyseq_mul, abs_of_pos (by simp only [hx]; positivity)]
    simp only [hx]
    rw [div_le_iff₀ (by positivity)]
    have h2 : (2 : ℝ) ^ (M i - 1) * 16 ≤ 2 ^ M j := by
      have e : (16 : ℝ) = 2 ^ 4 := by norm_num
      rw [e, ← pow_add]
      exact pow_le_pow_right₀ one_le_two (by omega)
    linarith
  -- rigidity applied to `γ_{δ'}`
  have h0 := dyseq_tendsto M hMmono
  have hs := serves_gam (dyseq M) h0 (dyseq_le_one M) (dyseq_ne M)
  have hW : {y : ℝ | ∀ j, dint (dyseq M j * y) ≤ 1 / 16} ∈ @nhds ℝ (gamTop (dyseq M)) 0 :=
    (mem_nhds_gam (dyseq M) _).2 ⟨univ, univ_mem, 1 / 16, by norm_num, fun y _ h => h⟩
  obtain ⟨ε, hε, F, hF⟩ := hrig (gamTop (dyseq M)) (gam_group _) (gam_coarser_euclid _ 1 (dyseq_le_one M) 0)
    (fun a ha => hs.2.2.2.2 a (hInA a ha)) _ hW
  obtain ⟨i0, hi0⟩ := eventually_atTop.1 (hxU ε hε)
  have hcov : ∀ n : ℕ, ∃ f : F, ∀ j, dint (dyseq M j * (x (i0 + n) - f.1)) ≤ 1 / 16 := by
    intro n
    obtain ⟨f, hf, h⟩ := hF (x (i0 + n)) (hi0 _ (Nat.le_add_right _ _))
    exact ⟨⟨f, hf⟩, h⟩
  choose g hg using hcov
  obtain ⟨n1, n2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite g
  have key : ∀ a b : ℕ, a < b → g a = g b → False := by
    intro a b hab he
    set i := i0 + a with hi
    set j := i0 + b with hj
    have hij : i < j := by omega
    have h1 := hg a j
    have h2 := hg b j
    rw [← he] at h2
    have h3 : dint (dyseq M j * x j - dyseq M j * x i) ≤ 1 / 8 := by
      have e : dyseq M j * x j - dyseq M j * x i =
          dyseq M j * (x (i0 + b) - (g a).1) - dyseq M j * (x (i0 + a) - (g a).1) := by
        rw [← hi, ← hj]
        ring
      rw [e]
      exact (dint_sub_le _ _).trans (by linarith)
    have h4 : dint (dyseq M j * x j) = 1 / 2 := by
      rw [hhalf, Two.dint_eq]
      have : round (1 / 2 : ℝ) = 1 := by
        rw [round_eq]
        norm_num
      rw [this]
      norm_num
    have h5 := dint_add_le' (dyseq M j * x j - dyseq M j * x i) (dyseq M j * x i)
    rw [sub_add_cancel, h4] at h5
    have h6 := hsmall i j hij
    linarith
  rcases lt_or_gt_of_ne hne with h | h
  · exact key n1 n2 h heq
  · exact key n2 n1 h heq.symm

/-- For a rigid dyadic sequence the parity topologies generate the finest serving topology. -/
theorem finest_of_rig (hKR : Stab.KaltonRobertsClassical) (L : ℕ → ℕ) (hL : StrictMono L)
    (hrig : Rig (dyseq L)) :
    Serves (gamOf (dyseq L) (dyseq_tendsto L hL)) {a | InA (dyseq L) sT a} ∧
      ∀ γ : TopologicalSpace ℝ, Serves γ {a | InA (dyseq L) sT a} →
        gamOf (dyseq L) (dyseq_tendsto L hL) ≤ γ := by
  letI : Dy := ⟨L, hL, hrig⟩
  have hle : ∀ γ : TopologicalSpace ℝ, Serves γ {a | InA (dyseq L) sT a} →
      gamOf (dyseq L) (dyseq_tendsto L hL) ≤ γ := fun γ hs =>
    gamAll_le (Stab.kaltonRoberts_of_classical hKR) γ hs
  obtain ⟨γ, hγ, hfin⟩ := exists_finest {a | InA (dyseq L) sT a}
    ⟨_, serves_gam (dyseq L) (dyseq_tendsto L hL) (dyseq_le_one L) (dyseq_ne L)⟩
  have h2 : γ ≤ gamOf (dyseq L) (dyseq_tendsto L hL) :=
    le_iInf fun θ => hfin _ (parOf_serves _ _ (dyseq_le_one L) (dyseq_ne L) θ)
  have e : gamOf (dyseq L) (dyseq_tendsto L hL) = γ := le_antisymm (hle γ hγ) h2
  exact ⟨e ▸ hγ, hle⟩

/-- Rigidity is equivalent to the description of the finest serving topology. -/
theorem rig_iff (hKR : Stab.KaltonRobertsClassical) (L : ℕ → ℕ) (hL : StrictMono L) :
    Rig (dyseq L) ↔ ∀ γ : TopologicalSpace ℝ, Serves γ {a | InA (dyseq L) sT a} →
      gamOf (dyseq L) (dyseq_tendsto L hL) ≤ γ :=
  ⟨fun h => (finest_of_rig hKR L hL h).2,
    fun h => rig_of_finest _ (dyseq_tendsto L hL) (dyseq_le_one L) (dyseq_ne L) h⟩

end Three
end PVG
