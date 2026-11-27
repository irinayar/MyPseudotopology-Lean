import LeanCheck.PVGThreeDyadic

/-!
# PVGthree: countably many coefficients

* `tune` : for finitely many coefficients and any `x` far from the lacunary set there is a frequency `y`
  with `y x` near `1/2` and `‖a y s_n‖` small for all `n`;
* `not_rig_of_countable` : if `A(δ)` is countable and `U(ε)` contains points far from the lacunary set, then
  `δ` is not rigid;
* `rig_iff_bounded_of_countable` : for dyadic `δ` with countable `A(δ)`, rigidity means bounded gaps.

Sequences are indexed from `0`; `sT n = 2^((n+1)^2)`.
-/

open Filter Topology Set

namespace PVG
namespace Three
open Two Q95 Lac

lemma sT_eq (n : ℕ) : sT n = (2 : ℝ) ^ ((n + 1) ^ 2) := rfl

lemma sT_pos' (n : ℕ) : 0 < sT n := by
  rw [sT_eq]
  positivity

lemma sT_mono : Monotone sT := fun a b hab => by
  rw [sT_eq, sT_eq]
  exact pow_le_pow_right₀ one_le_two (Nat.pow_le_pow_left (by omega) 2)

lemma sT_step (n : ℕ) : sT (n + 1) = sT n * 2 ^ (2 * n + 3) := by
  rw [sT_eq, sT_eq, ← pow_add]
  congr 1
  ring

lemma sT_double (n : ℕ) : 2 * sT n ≤ sT (n + 1) := by
  rw [sT_step, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (sT_pos' n).le
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 * n + 3) := pow_le_pow_right₀ one_le_two (by omega)

lemma sT_geom (n i : ℕ) : sT n * 2 ^ i ≤ sT (n + i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h := sT_double (n + i)
    rw [pow_succ]
    calc sT n * (2 ^ i * 2) = 2 * (sT n * 2 ^ i) := by ring
      _ ≤ 2 * sT (n + i) := by linarith
      _ ≤ sT (n + (i + 1)) := h

lemma sT_large (R : ℝ) : ∃ n, R < sT n := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt R (one_lt_two (α := ℝ))
  refine ⟨m, hm.trans_le ?_⟩
  rw [sT_eq]
  exact pow_le_pow_right₀ one_le_two (by nlinarith)

lemma tail_bound {Λ K ρ A C : ℝ} (hA : 0 < A) (hC : 0 < C) (h : 4 * Λ * K ≤ C * ρ) :
    Λ * (2 * (K / (A * C))) * A ≤ ρ / 2 := by
  have e : Λ * (2 * (K / (A * C))) * A = 2 * Λ * K / C := by
    field_simp
  rw [e, div_le_iff₀ hC]
  nlinarith

attribute [local irreducible] sT sS in
/-- A frequency near `1/(2x)` that is almost invisible on the dilates of the lacunary set. -/
lemma tune (F : Finset ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Q : ℝ, 1 ≤ Q ∧ ∀ x : ℝ, Q ≤ x → (∀ n, Q * sT n ≤ x ∨ Q * x ≤ sT n) →
      ∃ y : ℝ, |y * x - 1 / 2| ≤ 1 / 8 ∧ ∀ a ∈ F, ∀ n, dint (a * y * sT n) ≤ ρ := by
  classical
  set Λ : ℝ := 1 + ∑ a ∈ F, |a| with hΛ
  have hΛ1 : 1 ≤ Λ := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hΛa : ∀ a ∈ F, |a| ≤ Λ := fun a ha => by
    have := Finset.single_le_sum (f := fun b : ℝ => |b|) (fun _ _ => abs_nonneg _) ha
    simp only [hΛ]
    linarith
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ1
  obtain ⟨L, hL⟩ := syndetic F (half_pos hρ)
  set K : ℝ := (L : ℝ) + 1 with hK
  have hK1 : 1 ≤ K := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt (4 * Λ * K / ρ) (one_lt_two (α := ℝ))
  set Q : ℝ := 1 + Λ / ρ + sT N0 + 16 * K + 4 * Λ * K / ρ with hQ
  have p1 : 0 < Λ / ρ := div_pos hΛ0 hρ
  have p2 : 0 < sT N0 := sT_pos' N0
  have p3 : 0 < 4 * Λ * K / ρ := by positivity
  have hQ1 : 1 ≤ Q := by simp only [hQ]; linarith
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ1
  have hQa : Λ / ρ ≤ Q := by simp only [hQ]; linarith
  have hQb : sT N0 ≤ Q := by simp only [hQ]; linarith
  have hQc : 16 * K ≤ Q := by simp only [hQ]; linarith
  have hQd : 4 * Λ * K / ρ ≤ Q := by simp only [hQ]; linarith
  refine ⟨Q, hQ1, fun x hx hfar => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le hQ0 hx
  have hex : ∃ n, x < sT n := sT_large x
  obtain ⟨n1, hn1x, hmin⟩ : ∃ n, x < sT n ∧ ∀ m, m < n → ¬ x < sT m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hbelow : ∀ n, n < n1 → Q * sT n ≤ x := by
    intro n hn
    have h1 : sT n ≤ x := not_lt.1 (hmin n hn)
    rcases hfar n with h | h
    · exact h
    · have h2 : x ≤ Q * x := le_mul_of_one_le_left hx0.le hQ1
      have h3 : sT n = x := le_antisymm h1 (h2.trans h)
      have h4 : Q * x ≤ x := h3 ▸ h
      have h5 : Q * x = x := le_antisymm h4 h2
      rw [h3, h5]
  have hat : Q * x ≤ sT n1 := by
    rcases hfar n1 with h | h
    · have h2 : sT n1 ≤ Q * sT n1 := le_mul_of_one_le_left (sT_pos' n1).le hQ1
      exact absurd (h2.trans h) (not_le.2 hn1x)
    · exact h
  have hN0n1 : N0 ≤ n1 := by
    by_contra hc
    have h1 : sT n1 ≤ sT N0 := sT_mono (le_of_lt (not_le.1 hc))
    have h2 : sT N0 ≤ Q * x := hQb.trans (le_mul_of_one_le_right hQ0.le (hQ1.trans hx))
    -- then `Q * x ≤ sT n1 ≤ sT N0 ≤ Q`, impossible for `x ≥ Q > 16`
    have h3 : Q * x ≤ Q := hat.trans (h1.trans hQb)
    have h4 : (16 : ℝ) ≤ x := le_trans (le_trans (by linarith) hQc) hx
    nlinarith
  -- the corrections
  have hpick : ∀ w : ℝ, ∃ p : ℤ, |(p : ℝ) - w| ≤ K ∧ ∀ a ∈ F, dint (a * p) < ρ / 2 := by
    intro w
    obtain ⟨p, hp1, hp2, hp3⟩ := hL ⌈w⌉
    refine ⟨p, ?_, hp3⟩
    have h1 : w ≤ (p : ℝ) := (Int.le_ceil w).trans (by exact_mod_cast hp1)
    have h2 : (p : ℝ) ≤ (⌈w⌉ : ℝ) + L := by exact_mod_cast hp2
    have h3 : (⌈w⌉ : ℝ) < w + 1 := Int.ceil_lt_add_one w
    rw [abs_of_nonneg (sub_nonneg.2 h1)]
    simp only [hK]
    linarith
  choose pick hpick1 hpick2 using hpick
  set t : ℝ := 1 / (2 * x) with ht
  have ht0 : 0 < t := by positivity
  obtain ⟨u, hu0, huS⟩ : ∃ u : ℕ → ℝ, u 0 = t ∧
      ∀ m, u (m + 1) = (pick (u m * sT (n1 + m)) : ℝ) / sT (n1 + m) :=
    ⟨fun m => Nat.rec t (fun i prev => (pick (prev * sT (n1 + i)) : ℝ) / sT (n1 + i)) m, rfl, fun _ => rfl⟩
  have hstep : ∀ m, |u (m + 1) - u m| ≤ K / sT (n1 + m) := by
    intro m
    have hs := sT_pos' (n1 + m)
    have e : u (m + 1) - u m = ((pick (u m * sT (n1 + m)) : ℝ) - u m * sT (n1 + m)) / sT (n1 + m) := by
      rw [huS]
      field_simp
    rw [e, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right (hpick1 _) hs.le
  have hstep' : ∀ m i, |u (m + i + 1) - u (m + i)| ≤ (K / sT (n1 + m)) * (1 / 2) ^ i := by
    intro m i
    refine (hstep (m + i)).trans ?_
    have h1 := sT_geom (n1 + m) i
    have e : n1 + (m + i) = n1 + m + i := by omega
    rw [e, one_div, inv_pow, ← div_eq_mul_inv, div_div]
    exact div_le_div_of_nonneg_left hK0.le (mul_pos (sT_pos' _) (by positivity)) h1
  have hcauchy : CauchySeq u := by
    refine cauchySeq_of_le_geometric (1 / 2) (K / sT n1) (by norm_num) fun i => ?_
    rw [Real.dist_eq, abs_sub_comm]
    have h := hstep' 0 i
    simpa only [zero_add, add_zero] using h
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  have htail : ∀ m, |y - u m| ≤ 2 * (K / sT (n1 + m)) := by
    intro m
    have h1 : Tendsto (fun i => u (m + i)) atTop (𝓝 y) := by
      have := hy.comp (tendsto_add_atTop_nat m)
      simpa only [Function.comp_def, add_comm] using this
    have h2 : dist (u (m + 0)) y ≤ (K / sT (n1 + m)) / (1 - 1 / 2) := by
      refine dist_le_of_le_geometric_of_tendsto₀ (1 / 2) (K / sT (n1 + m)) (by norm_num) (fun i => ?_) h1
      rw [Real.dist_eq, abs_sub_comm]
      exact hstep' m i
    rw [add_zero, Real.dist_eq, abs_sub_comm] at h2
    refine h2.trans (le_of_eq ?_)
    ring
  have hyt : |y - t| ≤ 2 * (K / sT n1) := by
    have h := htail 0
    rwa [hu0, add_zero] at h
  refine ⟨y, ?_, fun a ha n => ?_⟩
  · have e : y * x - 1 / 2 = (y - t) * x := by
      rw [ht]
      field_simp
    rw [e, abs_mul, abs_of_pos hx0]
    have h1 : |y - t| * x ≤ 2 * (K / sT n1) * x := mul_le_mul_of_nonneg_right hyt hx0.le
    have h2 : 2 * (K / sT n1) * x ≤ 1 / 8 := by
      have h3 : 2 * (K / sT n1) * x = 2 * K * x / sT n1 := by ring
      rw [h3, div_le_iff₀ (sT_pos' n1)]
      have h4 : 16 * K * x ≤ Q * x := mul_le_mul_of_nonneg_right hQc hx0.le
      linarith
    exact h1.trans h2
  · have haΛ := hΛa a ha
    have hsn := sT_pos' n
    have hQρ : Λ ≤ ρ * Q := by
      have := (div_le_iff₀ hρ).1 hQa
      linarith
    have hKρ : 4 * Λ * K ≤ ρ * Q := by
      have := (div_le_iff₀ hρ).1 hQd
      linarith
    rcases lt_or_ge n n1 with hn | hn
    · have h1 := hbelow n hn
      have hA : |a * t * sT n| ≤ ρ / 2 := by
        rw [abs_mul, abs_mul, abs_of_pos ht0, abs_of_pos hsn]
        have h2 : |a| * t * sT n ≤ Λ * t * sT n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right haΛ ht0.le) hsn.le
        have h3 : Λ * t * sT n ≤ ρ / 2 := by
          have e : Λ * t * sT n = Λ * sT n / (2 * x) := by rw [ht]; ring
          rw [e, div_le_iff₀ (by positivity)]
          have h4 : Λ * sT n ≤ ρ * Q * sT n := mul_le_mul_of_nonneg_right hQρ hsn.le
          have h5 : ρ * (Q * sT n) ≤ ρ * x := mul_le_mul_of_nonneg_left h1 hρ.le
          nlinarith
        exact h2.trans h3
      have hB : |a * (y - t) * sT n| ≤ ρ / 2 := by
        rw [abs_mul, abs_mul, abs_of_pos hsn]
        have h2 : |a| * |y - t| * sT n ≤ Λ * (2 * (K / sT n1)) * sT n :=
          mul_le_mul_of_nonneg_right (mul_le_mul haΛ hyt (abs_nonneg _) hΛ0.le) hsn.le
        have h3 : Λ * (2 * (K / sT n1)) * sT n ≤ ρ / 2 := by
          have e : Λ * (2 * (K / sT n1)) * sT n = 2 * Λ * K * sT n / sT n1 := by ring
          rw [e, div_le_iff₀ (sT_pos' n1)]
          -- `Q² sT n ≤ Q x ≤ sT n1`
          have h4 : Q * (Q * sT n) ≤ sT n1 := (mul_le_mul_of_nonneg_left h1 hQ0.le).trans hat
          have h5 : 4 * Λ * K * sT n ≤ ρ * Q * sT n := mul_le_mul_of_nonneg_right hKρ hsn.le
          have h6 : ρ * (Q * sT n) ≤ ρ * (Q * (Q * sT n)) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (mul_pos hQ0 hsn).le hQ1) hρ.le
          have h7 : ρ * (Q * (Q * sT n)) ≤ ρ * sT n1 := mul_le_mul_of_nonneg_left h4 hρ.le
          nlinarith
        exact h2.trans h3
      have e : a * y * sT n = a * t * sT n + a * (y - t) * sT n := by ring
      rw [e]
      refine (dint_add_le' _ _).trans ?_
      have := (dint_le_abs (a * t * sT n)).trans hA
      have := (dint_le_abs (a * (y - t) * sT n)).trans hB
      linarith
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
      have hs1 := sT_pos' (n1 + m + 1)
      have hp : u (m + 1) * sT (n1 + m) = (pick (u m * sT (n1 + m)) : ℝ) := by
        rw [huS]
        exact div_mul_cancel₀ _ (sT_pos' (n1 + m)).ne'
      have e : a * y * sT (n1 + m) =
          a * (pick (u m * sT (n1 + m)) : ℝ) + a * (y - u (m + 1)) * sT (n1 + m) := by
        rw [← hp]
        ring
      have hA := hpick2 (u m * sT (n1 + m)) a ha
      have hB : |a * (y - u (m + 1)) * sT (n1 + m)| ≤ ρ / 2 := by
        rw [abs_mul, abs_mul, abs_of_pos hsn]
        have h1 := htail (m + 1)
        have e1 : n1 + (m + 1) = n1 + m + 1 := by omega
        rw [e1] at h1
        have h2 : |a| * |y - u (m + 1)| * sT (n1 + m) ≤ Λ * (2 * (K / sT (n1 + m + 1))) * sT (n1 + m) :=
          mul_le_mul_of_nonneg_right (mul_le_mul haΛ h1 (abs_nonneg _) hΛ0.le) hsn.le
        have h3 : Λ * (2 * (K / sT (n1 + m + 1))) * sT (n1 + m) ≤ ρ / 2 := by
          -- the ratio of consecutive terms is at least `4 Λ K / ρ`
          have h4 : 4 * Λ * K / ρ ≤ 2 ^ (2 * (n1 + m) + 3) :=
            hN0.le.trans (pow_le_pow_right₀ one_le_two (by omega))
          rw [sT_step (n1 + m)]
          exact tail_bound hsn (by positivity) ((div_le_iff₀ hρ).1 h4)
        exact h2.trans h3
      rw [e]
      refine (dint_add_le' _ _).trans ?_
      have := (dint_le_abs (a * (y - u (m + 1)) * sT (n1 + m))).trans hB
      linarith

/-- Countably many coefficients and points of `U(ε)` far from the lacunary set: no rigidity. -/
theorem not_rig_of_countable (δ : ℕ → ℝ) (hA : Set.Countable {a | InA δ sT a})
    (hfar : ∀ ε : ℝ, 0 < ε → ∀ Q : ℝ, ∃ x : ℝ, Q ≤ x ∧ (∀ k, dint (δ k * x) ≤ ε) ∧
      ∀ n, Q * sT n ≤ x ∨ Q * x ≤ sT n) : ¬ Rig δ := by
  classical
  intro hrig
  have h0mem : (0 : ℝ) ∈ {a | InA δ sT a} := by
    intro ε hε
    exact Eventually.of_forall fun k n => by
      rw [zero_mul, zero_mul, dint_zero]
      exact hε.le
  obtain ⟨f, hf⟩ := hA.exists_eq_range ⟨0, h0mem⟩
  have htune : ∀ i : ℕ, ∃ Q : ℝ, 1 ≤ Q ∧ ∀ x : ℝ, Q ≤ x → (∀ n, Q * sT n ≤ x ∨ Q * x ≤ sT n) →
      ∃ y : ℝ, |y * x - 1 / 2| ≤ 1 / 8 ∧ ∀ a ∈ (Finset.range (i + 1)).image f, ∀ n,
        dint (a * y * sT n) ≤ 1 / ((i : ℝ) + 1) :=
    fun i => tune _ (by positivity)
  choose Q hQ1 hQ using htune
  have hex : ∀ (i : ℕ) (p : ℝ), ∃ x : ℝ, max (max (Q i) (16 * p)) ((i : ℝ) + 1) ≤ x ∧
      (∀ k, dint (δ k * x) ≤ 1 / ((i : ℝ) + 1)) ∧
      ∀ n, max (max (Q i) (16 * p)) ((i : ℝ) + 1) * sT n ≤ x ∨
        max (max (Q i) (16 * p)) ((i : ℝ) + 1) * x ≤ sT n :=
    fun i p => hfar _ (by positivity) _
  choose pt hpt1 hpt2 hpt3 using hex
  let x : ℕ → ℝ := fun i => Nat.rec (pt 0 0) (fun j prev => pt (j + 1) prev) i
  have hx : ∀ i, ∃ p, x i = pt i p ∧ (∀ j, i = j + 1 → p = x j) := by
    intro i
    cases i with
    | zero => exact ⟨0, rfl, fun j h => absurd h (by omega)⟩
    | succ j =>
      refine ⟨x j, rfl, fun j' h => ?_⟩
      have : j = j' := by omega
      rw [this]
  have hxQ : ∀ i, Q i ≤ x i ∧ (i : ℝ) + 1 ≤ x i := by
    intro i
    obtain ⟨p, hp, -⟩ := hx i
    rw [hp]
    exact ⟨le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hpt1 i p),
      le_trans (le_max_right _ _) (hpt1 i p)⟩
  have hx1 : ∀ i, 1 ≤ x i := fun i =>
    le_trans (le_add_of_nonneg_left (Nat.cast_nonneg i)) (hxQ i).2
  have hx0 : ∀ i, 0 < x i := fun i => lt_of_lt_of_le one_pos (hx1 i)
  have hgrow : ∀ i, 16 * x i ≤ x (i + 1) := by
    intro i
    have h : x (i + 1) = pt (i + 1) (x i) := rfl
    rw [h]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hpt1 (i + 1) (x i))
  have hmono : Monotone x := monotone_nat_of_le_succ fun i => by
    have := hgrow i
    have := hx0 i
    linarith
  have hfarx : ∀ i n, Q i * sT n ≤ x i ∨ Q i * x i ≤ sT n := by
    intro i n
    obtain ⟨p, hp, -⟩ := hx i
    have hle : Q i ≤ max (max (Q i) (16 * p)) ((i : ℝ) + 1) := le_trans (le_max_left _ _) (le_max_left _ _)
    have h := hpt3 i p n
    rw [← hp] at h
    rcases h with h | h
    · exact Or.inl ((mul_le_mul_of_nonneg_right hle (sT_pos' n).le).trans h)
    · exact Or.inr ((mul_le_mul_of_nonneg_right hle (hx0 i).le).trans h)
  have hy : ∀ i, ∃ y : ℝ, |y * x i - 1 / 2| ≤ 1 / 8 ∧ ∀ a ∈ (Finset.range (i + 1)).image f, ∀ n,
      dint (a * y * sT n) ≤ 1 / ((i : ℝ) + 1) :=
    fun i => hQ i (x i) (hxQ i).1 (hfarx i)
  choose y hy1 hy2 using hy
  have hyx : ∀ i, 3 / 8 ≤ y i * x i ∧ y i * x i ≤ 5 / 8 := by
    intro i
    have h := abs_le.1 (hy1 i)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hypos : ∀ i, 0 < y i := fun i =>
    pos_of_mul_pos_left (lt_of_lt_of_le (by norm_num) (hyx i).1) (hx0 i).le
  have hyle : ∀ i, y i ≤ 5 / 8 / x i := fun i => by
    rw [le_div_iff₀ (hx0 i)]
    exact (hyx i).2
  have hy0 : Tendsto y atTop (𝓝 0) := by
    refine squeeze_zero (fun i => (hypos i).le) (fun i => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    refine (hyle i).trans ?_
    rw [div_le_div_iff₀ (hx0 i) (by positivity)]
    have := (hxQ i).2
    have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    nlinarith
  have hy1' : ∀ i, |y i| ≤ 1 := fun i => by
    rw [abs_of_pos (hypos i)]
    refine (hyle i).trans ?_
    rw [div_le_one (hx0 i)]
    have := hx1 i
    linarith
  have hInA : ∀ a : ℝ, InA δ sT a → InA y sT a := by
    intro a ha ε hε
    have ha' : a ∈ range f := by
      rw [← hf]
      exact ha
    obtain ⟨j, rfl⟩ := ha'
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    refine eventually_atTop.2 ⟨max j m, fun i hi n => ?_⟩
    have hji : j ≤ i := le_trans (le_max_left _ _) hi
    have hmi : m ≤ i := le_trans (le_max_right _ _) hi
    have hmem : f j ∈ (Finset.range (i + 1)).image f :=
      Finset.mem_image.2 ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le hji), rfl⟩
    refine (hy2 i _ hmem n).trans (le_trans ?_ hm.le)
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmi 1)
  have hxU : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ k, dint (δ k * x i) ≤ ε := by
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    refine eventually_atTop.2 ⟨m, fun i hi k => ?_⟩
    obtain ⟨p, hp, -⟩ := hx i
    rw [hp]
    refine (hpt2 i p k).trans (le_trans ?_ hm.le)
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hi 1)
  have hsmall : ∀ i j, i < j → dint (y j * x i) ≤ 1 / 16 := by
    intro i j hij
    refine (dint_le_abs _).trans ?_
    rw [abs_of_pos (mul_pos (hypos j) (hx0 i))]
    have h1 : 16 * x i ≤ x j := (hgrow i).trans (hmono (Nat.succ_le_of_lt hij))
    have h2 : y j * (16 * x i) ≤ y j * x j := mul_le_mul_of_nonneg_left h1 (hypos j).le
    have h3 := (hyx j).2
    linarith
  have hbig : ∀ i, 3 / 8 ≤ dint (y i * x i) := by
    intro i
    have h1 := dint_add_le' (y i * x i) (1 / 2 - y i * x i)
    rw [add_sub_cancel, dint_half] at h1
    have h2 : dint (1 / 2 - y i * x i) ≤ 1 / 8 := by
      refine (dint_le_abs _).trans ?_
      rw [abs_sub_comm]
      exact hy1 i
    linarith
  -- rigidity applied to `γ_y`
  have hs := serves_gam y hy0 hy1' (fun i => (hypos i).ne')
  have hW : {z : ℝ | ∀ j, dint (y j * z) ≤ 1 / 16} ∈ @nhds ℝ (gamTop y) 0 :=
    (mem_nhds_gam y _).2 ⟨univ, univ_mem, 1 / 16, by norm_num, fun z _ h => h⟩
  obtain ⟨ε, hε, F, hF⟩ := hrig (gamTop y) (gam_group _) (gam_coarser_euclid _ 1 hy1' 0)
    (fun a ha => hs.2.2.2.2 a (hInA a ha)) _ hW
  obtain ⟨i0, hi0⟩ := eventually_atTop.1 (hxU ε hε)
  have hcov : ∀ n : ℕ, ∃ g : F, ∀ j, dint (y j * (x (i0 + n) - g.1)) ≤ 1 / 16 := by
    intro n
    obtain ⟨g, hg, h⟩ := hF (x (i0 + n)) (hi0 _ (Nat.le_add_right _ _))
    exact ⟨⟨g, hg⟩, h⟩
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
    have h3 : dint (y j * x j - y j * x i) ≤ 1 / 8 := by
      have e : y j * x j - y j * x i =
          y j * (x (i0 + b) - (g a).1) - y j * (x (i0 + a) - (g a).1) := by
        rw [← hi, ← hj]
        ring
      rw [e]
      exact (dint_sub_le _ _).trans (by linarith)
    have h4 := hbig j
    have h5 := dint_add_le' (y j * x j - y j * x i) (y j * x i)
    rw [sub_add_cancel] at h5
    have h6 := hsmall i j hij
    linarith
  rcases lt_or_gt_of_ne hne with h | h
  · exact key n1 n2 h heq
  · exact key n2 n1 h heq.symm

/-- Unbounded gaps give points of `U(ε)` far from the lacunary set. -/
lemma far_of_gaps (L : ℕ → ℕ) (hL : StrictMono L) (hgaps : ∀ G : ℕ, ∃ k, L k + G ≤ L (k + 1)) :
    ∀ ε : ℝ, 0 < ε → ∀ Q : ℝ, ∃ x : ℝ, Q ≤ x ∧ (∀ k, dint (dyseq L k * x) ≤ ε) ∧
      ∀ n, Q * sT n ≤ x ∨ Q * x ≤ sT n := by
  intro ε hε Q
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt Q (one_lt_two (α := ℝ))
  set h := m + q + 1 with hh
  -- a large gap far out
  obtain ⟨k, hk⟩ := hgaps ((5 * h + 2) + (∑ j ∈ Finset.range ((3 * h + 3) ^ 2), L (j + 1)) + 1)
  have hkK : (3 * h + 3) ^ 2 ≤ k := by
    by_contra hc
    have := Finset.single_le_sum (f := fun j => L (j + 1)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (not_le.1 hc))
    omega
  have hLk : (3 * h + 3) ^ 2 ≤ L k := hkK.trans (hL.id_le k)
  have hgap : L k + (5 * h + 2) ≤ L (k + 1) := by omega
  obtain ⟨M, hM1, hM2, hM3⟩ := off_squares h (L k) hLk
  refine ⟨2 ^ (M - 1), ?_, fun j => ?_, fun n => ?_⟩
  · refine hq.le.trans (pow_le_pow_right₀ one_le_two ?_)
    omega
  · rcases le_or_gt j k with hj | hj
    · have hLj : L j ≤ M - 1 := by
        have := hL.monotone hj
        omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hLj
      have e : dyseq L j * (2 : ℝ) ^ (M - 1) = (((2 : ℤ) ^ d : ℤ) : ℝ) := by
        unfold dyseq
        rw [hd, pow_add]
        push_cast
        field_simp
      rw [e, dint_intZ]
      exact hε.le
    · have hLj : M - 1 + m ≤ L j := by
        have := hL.monotone (show k + 1 ≤ j from hj)
        omega
      refine (dint_le_abs _).trans ?_
      rw [dyseq_mul, abs_of_pos (by positivity)]
      refine le_of_lt (lt_of_le_of_lt ?_ hm)
      rw [div_le_iff₀ (by positivity), one_div, inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity),
        ← pow_add]
      exact pow_le_pow_right₀ one_le_two (by omega)
  · rcases hM3 (n + 1) with hs | hs
    · -- the square is above `M`
      right
      rw [sT_eq]
      refine (mul_le_mul_of_nonneg_right (hq.le.trans (pow_le_pow_right₀ one_le_two (show q ≤ h by omega)))
        (by positivity)).trans ?_
      rw [← pow_add]
      exact pow_le_pow_right₀ one_le_two (by omega)
    · left
      rw [sT_eq]
      refine (mul_le_mul_of_nonneg_right (hq.le.trans (pow_le_pow_right₀ one_le_two (show q ≤ h - 1 by omega)))
        (by positivity)).trans ?_
      rw [← pow_add]
      exact pow_le_pow_right₀ one_le_two (by omega)

/-- For a dyadic sequence with countably many coefficients, rigidity means bounded gaps. -/
theorem rig_iff_bounded_of_countable (L : ℕ → ℕ) (hL : StrictMono L)
    (hA : Set.Countable {a | InA (dyseq L) sT a}) :
    Rig (dyseq L) ↔ ∃ G : ℕ, ∀ k, L (k + 1) ≤ L k + G := by
  constructor
  · intro hrig
    by_contra hc
    push Not at hc
    refine not_rig_of_countable (dyseq L) hA (far_of_gaps L hL fun G => ?_) hrig
    obtain ⟨k, hk⟩ := hc G
    exact ⟨k, hk.le⟩
  · rintro ⟨G, hG⟩
    exact (rig_of_bounded L hL G hG).2

end Three
end PVG
