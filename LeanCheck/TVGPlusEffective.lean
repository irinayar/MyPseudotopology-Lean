import LeanCheck.TVGPlusSizes
import LeanCheck.TVGPlusDual

/-!
# TVGplus: sequences converging to zero (Proposition 3.4) and the effective transfer (Corollary 6.6)

* `PS S hne k = P_S(k)`; `PS_lt_iff : P_S(k) < δ ↔ InBall S δ k`; `PS_pos : P_S(k) > 0` for `k ≠ 0`.
* `seq_lower` and `seq_lower_liminf`: Proposition 3.4 (a): for every `b < c_S`, `b log²(1/P_S(k_j)) ≤ log |k_j|` eventually,
  for every sequence of nonzero integers with `P_S(k_j) → 0`.
* `seq_upper`: Proposition 3.4 (b): for every `B > x_S` there are `k_j ≥ 1`, `δ_j ↓ 0` with `P_S(k_j) < δ_j` and `log k_j ≤ B log²(1/δ_j)`.
* `effective_transfer`: Corollary 6.6.  If the unit-target block statements `JA({p_i},{p_{i+1},…})` along a list of distinct primes have
  witnesses of size `exp(C log²(1/η))`, then for targets of absolute value at most `T` and `0 < ε ≤ 1/2` there is a solution `k` of size
  `exp(C' (log(1/ε)/log 2)^(2^(s-1)))`, with `C'` depending only on `C`, `T`, `s`.  (The article's statement for all `ε < 1` is corrected to
  `ε ≤ 1/2`: for `ε` near 1 the right-hand side tends to 1.)

No external hypothesis other than the stated block bounds; no `sorry`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime Filter

/-- `P_S(k) = max_{p ∈ S} P_p(k)`. -/
noncomputable def PS (S : Finset ℕ) (hne : S.Nonempty) (k : ℤ) : ℝ :=
  S.sup' hne (fun p => Pn (sqScales p) k)

lemma PS_lt_iff (S : Finset ℕ) (hne : S.Nonempty) (k : ℤ) (δ : ℝ) : PS S hne k < δ ↔ InBall S δ k := by
  unfold PS InBall
  exact Finset.sup'_lt_iff hne

lemma PS_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) {k : ℤ} (hk : k ≠ 0) :
    0 < PS S hne k := by
  obtain ⟨p, hp⟩ := hne
  have hp2 := (hS p hp).two_le
  set m : ℕ := 2 * k.natAbs + 1 with hm
  have hq : (2 * |(k : ℝ)|) < ((p ^ (m ^ 2) : ℕ) : ℝ) := by
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : 2 ^ m ≤ 2 ^ (m ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [Nat.zero_le m])
    have h3 : 2 ^ (m ^ 2) ≤ p ^ (m ^ 2) := Nat.pow_le_pow_left hp2 _
    have h4 : 2 * k.natAbs < p ^ (m ^ 2) := by omega
    have h5 : (2 * |(k : ℝ)|) = ((2 * k.natAbs : ℕ) : ℝ) := by
      push_cast; rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h5]; exact_mod_cast h4
  have hqpos : (0 : ℝ) < ((p ^ (m ^ 2) : ℕ) : ℝ) := lt_of_le_of_lt (by positivity) hq
  have hkpos : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have hnr : nrm ((k : ℝ) / ((p ^ (m ^ 2) : ℕ) : ℝ)) = |(k : ℝ)| / ((p ^ (m ^ 2) : ℕ) : ℝ) := by
    apply (nrm_eq_abs _).trans
    · rw [abs_div, abs_of_pos hqpos]
    · rw [abs_div, abs_of_pos hqpos, div_le_iff₀ hqpos]; linarith
  have hle := le_Pn (S := sqScales p) (q := p ^ (m ^ 2)) (mem_sqScales (by omega)) k
  have hge : Pn (sqScales p) k ≤ PS S ⟨p, hp⟩ k := Finset.le_sup' (fun q => Pn (sqScales q) k) hp
  have : 0 < |(k : ℝ)| / ((p ^ (m ^ 2) : ℕ) : ℝ) := div_pos hkpos hqpos
  linarith

theorem seq_lower {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) {b : ℝ} (hb : b < cS S) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ k : ℤ, k ≠ 0 → PS S hne k < δ₀ / 2 →
      Real.exp (b * Real.log (1 / (2 * PS S hne k)) ^ 2) ≤ |(k : ℝ)| := by
  obtain ⟨δ₀, hδ₀, h⟩ := uS_lower hS hb
  refine ⟨δ₀, hδ₀, ?_⟩
  intro k hk hP
  have hpos := PS_pos hS hne hk
  have hδ : 2 * PS S hne k < δ₀ := by linarith
  have hball : InBall S (2 * PS S hne k) (k.natAbs : ℤ) := by
    rw [← PS_lt_iff S hne]
    have : PS S hne ((k.natAbs : ℕ) : ℤ) = PS S hne k := by
      unfold PS
      rcases Int.natAbs_eq k with h1 | h1
      · rw [← h1]
      · have : ((k.natAbs : ℕ) : ℤ) = -k := by omega
        rw [this]; congr 1; funext p; exact Pn_neg _ _
    rw [this]; linarith
  have h1 := uS_le (S := S) (δ := 2 * PS S hne k) (n := k.natAbs) (by omega) hball
  have h2 := h (2 * PS S hne k) (by positivity) hδ
  have h3 : (uS S (2 * PS S hne k) : ℝ) ≤ |(k : ℝ)| := by
    have : (uS S (2 * PS S hne k) : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast h1
    rwa [Nat.cast_natAbs, Int.cast_abs] at this
  exact h2.trans h3

theorem seq_lower_liminf {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) {b : ℝ} (hb : b < cS S)
    {k : ℕ → ℤ} (hk : ∀ j, k j ≠ 0) (hP : Tendsto (fun j => PS S hne (k j)) atTop (nhds 0)) :
    ∀ᶠ j in atTop, b * Real.log (1 / PS S hne (k j)) ^ 2 ≤ Real.log |(k j : ℝ)| := by
  have hlog : ∀ j, 0 ≤ Real.log |(k j : ℝ)| := fun j =>
    Real.log_nonneg (by
      have : (1 : ℤ) ≤ |k j| := Int.one_le_abs (hk j)
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|k j| : ℤ) : ℝ) := by exact_mod_cast this
      rw [Int.cast_abs] at h2; simpa using h2)
  by_cases hb0 : b ≤ 0
  · exact Eventually.of_forall (fun j => by nlinarith [hlog j, sq_nonneg (Real.log (1 / PS S hne (k j)))])
  · push Not at hb0
    obtain ⟨b', hb'1, hb'2⟩ : ∃ b', b < b' ∧ b' < cS S := ⟨(b + cS S) / 2, by linarith, by linarith⟩
    obtain ⟨δ₀, hδ₀, h⟩ := seq_lower hS hne hb'2
    have hP' : ∀ᶠ j in atTop, PS S hne (k j) < δ₀ / 2 := hP.eventually (gt_mem_nhds (by positivity))
    have hpos : ∀ j, 0 < PS S hne (k j) := fun j => PS_pos hS hne (hk j)
    have hL : Tendsto (fun j => Real.log (1 / PS S hne (k j))) atTop atTop := by
      have h1 : Tendsto (fun j => PS S hne (k j)) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hP, Eventually.of_forall hpos⟩
      have h2 := h1.inv_tendsto_nhdsGT_zero
      have h3 := Real.tendsto_log_atTop.comp h2
      refine h3.congr (fun j => ?_)
      simp [one_div]
    have hL' : ∀ᶠ j in atTop, 2 * b' * Real.log 2 / (b' - b) ≤ Real.log (1 / PS S hne (k j)) :=
      hL.eventually_ge_atTop _
    filter_upwards [hP', hL'] with j hj1 hj2
    have h4 := h (k j) (hk j) hj1
    have h5 : Real.log (1 / (2 * PS S hne (k j))) = Real.log (1 / PS S hne (k j)) - Real.log 2 := by
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul (by norm_num) (hpos j).ne']; ring
    rw [h5] at h4
    have h6 : b' * (Real.log (1 / PS S hne (k j)) - Real.log 2) ^ 2 ≤ Real.log |(k j : ℝ)| := by
      have := Real.log_le_log (Real.exp_pos _) h4
      rwa [Real.log_exp] at this
    set L := Real.log (1 / PS S hne (k j)) with hLdef
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hbb : 0 < b' - b := by linarith
    have h7 : 2 * b' * Real.log 2 ≤ (b' - b) * L := by
      rw [div_le_iff₀ hbb] at hj2; linarith
    have hLpos : 0 ≤ L := by
      have hb2 : 0 < b' := by linarith
      have : 0 ≤ 2 * b' * Real.log 2 := by positivity
      by_contra hneg; push Not at hneg
      nlinarith
    have h8 : b * L ^ 2 ≤ b' * (L - Real.log 2) ^ 2 := by
      nlinarith [mul_nonneg hLpos (sub_nonneg.mpr h7), sq_nonneg (Real.log 2), mul_pos (by linarith : 0 < b') (sq_pos_of_pos hlog2)]
    linarith

theorem seq_upper {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty) {B : ℝ} (hB : xS S < B) :
    ∃ (k : ℕ → ℕ) (δ : ℕ → ℝ), (∀ j, 0 < δ j) ∧ Tendsto δ atTop (nhds 0) ∧
      (∀ j, 1 ≤ k j ∧ InBall S (δ j) (k j : ℤ) ∧ Real.log (k j : ℝ) ≤ B * Real.log (1 / δ j) ^ 2) := by
  obtain ⟨B', hB'1, hB'2⟩ : ∃ B', xS S < B' ∧ B' < B := ⟨(xS S + B) / 2, by linarith, by linarith⟩
  obtain ⟨δ₀, hδ₀, h⟩ := uS_upper hS hB'1
  obtain ⟨δ₁, hδ₁, hh⟩ := order_upper hS hB'1
  have hBpos : 0 < B - B' := by linarith
  -- δ_j = min (δ₀/2) (exp (-(j + L₁))) with L₁ large enough that log 2 ≤ (B - B') L²
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : ℝ, L₁ = Real.log 2 / (B - B') + 1 := ⟨_, rfl⟩
  have hL₁pos : 0 < L₁ := by
    have : 0 ≤ Real.log 2 / (B - B') := div_nonneg (Real.log_nonneg (by norm_num)) hBpos.le
    linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, δ = fun j : ℕ => min (min δ₀ δ₁ / 2) (Real.exp (-((j : ℝ) + L₁))) := ⟨_, rfl⟩
  have hδpos : ∀ j, 0 < δ j := fun j => by rw [hδ]; exact lt_min (by have := lt_min hδ₀ hδ₁; positivity) (Real.exp_pos _)
  refine ⟨fun j => uS S (δ j), δ, hδpos, ?_, ?_⟩
  · rw [hδ]
    have h1 : Tendsto (fun j : ℕ => Real.exp (-((j : ℝ) + L₁))) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_atTop_add_const_right atTop L₁ tendsto_natCast_atTop_atTop))
    have h2 := (tendsto_const_nhds (x := min δ₀ δ₁ / 2)).min h1
    rwa [min_eq_right (by positivity : (0 : ℝ) ≤ min δ₀ δ₁ / 2)] at h2
  · intro j
    have hδm : δ j ≤ min δ₀ δ₁ / 2 := by rw [hδ]; exact min_le_left _ _
    have hmin0 : min δ₀ δ₁ ≤ δ₀ := min_le_left _ _
    have hmin1 : min δ₀ δ₁ ≤ δ₁ := min_le_right _ _
    have hminpos : 0 < min δ₀ δ₁ := lt_min hδ₀ hδ₁
    have hδlt : δ j < δ₀ := by linarith
    have hδlt1 : δ j < δ₁ := by linarith
    have hup := h (δ j) (hδpos j) hδlt
    have hL : L₁ ≤ Real.log (1 / δ j) := by
      rw [one_div, Real.log_inv]
      have : δ j ≤ Real.exp (-((j : ℝ) + L₁)) := by rw [hδ]; exact min_le_right _ _
      have h2 := Real.log_le_log (hδpos j) this
      rw [Real.log_exp] at h2
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    -- membership and positivity of `uS`
    have hex : ∃ n : ℕ, 0 < n ∧ InBall S (δ j) (n : ℤ) := by
      obtain ⟨k, hk1, _, hkb⟩ := hh (δ j) (hδpos j) hδlt1
      have hkn : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
      exact ⟨k.toNat, by omega, by rw [hkn]; exact hkb⟩
    obtain ⟨hpos, hmem⟩ := uS_mem hex
    refine ⟨hpos, hmem, ?_⟩
    show Real.log (uS S (δ j) : ℝ) ≤ B * Real.log (1 / δ j) ^ 2
    have h2 : (uS S (δ j) : ℝ) ≤ 2 * Real.exp (B' * Real.log (1 / δ j) ^ 2) := hup
    have h3 := Real.log_le_log (by exact_mod_cast hpos) h2
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h3
    have hLL : Real.log 2 ≤ (B - B') * Real.log (1 / δ j) ^ 2 := by
      have h4 : 1 ≤ Real.log (1 / δ j) := by
        have : 1 ≤ L₁ := by
          rw [hL₁]; have : 0 ≤ Real.log 2 / (B - B') := div_nonneg (Real.log_nonneg (by norm_num)) hBpos.le
          linarith
        linarith
      have h5 : Real.log 2 / (B - B') ≤ Real.log (1 / δ j) := by rw [hL₁] at hL; linarith
      rw [div_le_iff₀ hBpos] at h5
      have h6 : Real.log (1 / δ j) ≤ Real.log (1 / δ j) ^ 2 := by nlinarith
      have h7 := mul_le_mul_of_nonneg_left h6 hBpos.le
      linarith
    linarith


/-- Unit-target block witnesses along a list of primes `p₁, p₂, …`: for each `i`, every accuracy `η ∈ (0,1)` has a witness `m` of size at most
`exp (C log²(1/η))` with `P_{p_i}(m - 1) < η` and `P_q(m) < η` for the later primes `q`. -/
def BlockBound (C : ℝ) : List ℕ → Prop
  | [] => True
  | p :: l => (∀ η : ℝ, 0 < η → η < 1 → ∃ m : ℤ, |(m : ℝ)| ≤ Real.exp (C * Real.log (1 / η) ^ 2) ∧
        Pn (sqScales p) (m - 1) < η ∧ ∀ q ∈ l, Pn (sqScales q) m < η) ∧ BlockBound C l

/-- **Corollary 6.6 (effective transfer).**  Unit-target block bounds of size `exp (C log²(1/η))` along a nonempty list of primes give, for targets
of absolute value at most `T` and every `0 < ε ≤ 1/2`, a solution `k` of all the coordinate conditions of size
`exp (C' (log(1/ε)/log 2)^(2^(s-1)))`, where `s` is the length of the list. -/
theorem effective_transfer {C : ℝ} (hC : 0 ≤ C) :
    ∀ (l : List ℕ), l ≠ [] → BlockBound C l → ∀ T : ℕ, ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ t : ℕ → ℤ, (∀ p ∈ l, |t p| ≤ T) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ∃ k : ℤ, (∀ p ∈ l, Pn (sqScales p) (k - t p) < ε) ∧
          |(k : ℝ)| ≤ Real.exp (C' * (Real.log (1 / ε) / Real.log 2) ^ (2 ^ (l.length - 1))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons p l' ih =>
    intro _ hBB T
    obtain ⟨hblock, hBB'⟩ := hBB
    have hu1 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → 1 ≤ Real.log (1 / ε) / Real.log 2 := by
      intro ε hε hε2
      rw [le_div_iff₀ hlog2, one_mul, one_div, Real.log_inv]
      have := Real.log_le_log hε hε2
      rw [one_div, Real.log_inv] at this
      linarith
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    rcases l' with _ | ⟨q, l''⟩
    · -- a single prime: the target itself
      refine ⟨Real.log (T + 1), Real.log_nonneg (by linarith), ?_⟩
      intro t ht ε hε hε2
      refine ⟨t p, ?_, ?_⟩
      · intro p' hp'
        simp only [List.mem_singleton] at hp'
        rw [hp', sub_self, Pn_zero]; exact hε
      · simp only [List.length_singleton, Nat.sub_self, pow_zero, pow_one]
        have h1 : |((t p : ℤ) : ℝ)| ≤ T := by
          have := ht p (by simp)
          exact_mod_cast this
        have hu := hu1 ε hε hε2
        have h2 : Real.log ((T : ℝ) + 1) ≤ Real.log ((T : ℝ) + 1) * (Real.log (1 / ε) / Real.log 2) := by
          have : 0 ≤ Real.log ((T : ℝ) + 1) := Real.log_nonneg (by linarith)
          nlinarith
        calc |((t p : ℤ) : ℝ)| ≤ T := h1
          _ ≤ (T : ℝ) + 1 := by linarith
          _ = Real.exp (Real.log ((T : ℝ) + 1)) := (Real.exp_log (by positivity)).symm
          _ ≤ _ := Real.exp_le_exp.mpr h2
    · obtain ⟨C₁, hC₁0, hIH⟩ := ih (by simp) hBB' T
      obtain ⟨l', hl'⟩ : ∃ l' : List ℕ, l' = q :: l'' := ⟨_, rfl⟩
      rw [← hl'] at hIH hblock ⊢
      obtain ⟨e, he⟩ : ∃ e : ℕ, e = 2 ^ (l'.length - 1) := ⟨_, rfl⟩
      have he1 : 1 ≤ e := by rw [he]; exact Nat.one_le_two_pow
      have hexp : 2 ^ ((p :: l').length - 1) = 2 * e := by
        rw [he]
        have hlen : (p :: l').length - 1 = (l'.length - 1) + 1 := by
          have : 1 ≤ l'.length := by rw [hl']; simp
          simp only [List.length_cons]; omega
        rw [hlen, pow_succ]; ring
      obtain ⟨G, hG⟩ : ∃ G : ℝ, G = C₁ * 3 ^ e := ⟨_, rfl⟩
      have hG0 : 0 ≤ G := by rw [hG]; positivity
      have hlogT2 : 0 ≤ Real.log ((T : ℝ) + 2) := Real.log_nonneg (by linarith)
      have hlogT1 : 0 ≤ Real.log (2 * ((T : ℝ) + 1)) := Real.log_nonneg (by linarith)
      obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * Real.log 2 + Real.log ((T : ℝ) + 2) + G + Real.log 2 := ⟨_, rfl⟩
      have hK0 : 0 ≤ K := by rw [hK]; positivity
      refine ⟨Real.log (2 * ((T : ℝ) + 1)) + C * K ^ 2 + G, by positivity, ?_⟩
      intro t ht ε hε hε2
      have hε4 : 0 < ε / 4 := by positivity
      have hε42 : ε / 4 ≤ 1 / 2 := by linarith
      obtain ⟨b, hb1, hb2⟩ := hIH t (fun p' hp' => ht p' (List.mem_cons_of_mem _ hp')) (ε / 4) hε4 hε42
      obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.log (1 / ε) / Real.log 2 := ⟨_, rfl⟩
      have hu1' : 1 ≤ u := by rw [hu]; exact hu1 ε hε hε2
      have hL : Real.log (1 / ε) = Real.log 2 * u := by rw [hu]; field_simp
      have hu_e1 : 1 ≤ u ^ e := one_le_pow₀ hu1'
      have hu_le : u ≤ u ^ e := le_self_pow₀ hu1' (by omega)
      -- the size of `b`
      have hb3 : |(b : ℝ)| ≤ Real.exp (G * u ^ e) := by
        refine hb2.trans (Real.exp_le_exp.mpr ?_)
        have hlg : Real.log (1 / (ε / 4)) / Real.log 2 = u + 2 := by
          have : Real.log (1 / (ε / 4)) = Real.log (1 / ε) + 2 * Real.log 2 := by
            rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_div hε.ne' (by norm_num),
              show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            push_cast; ring
          rw [this, hL]; field_simp
        rw [hlg, ← he]
        have h3 : (u + 2) ^ e ≤ (3 * u) ^ e := pow_le_pow_left₀ (by linarith) (by linarith) e
        rw [mul_pow] at h3
        rw [hG]
        have := mul_le_mul_of_nonneg_left h3 hC₁0
        linarith
      obtain ⟨a, ha⟩ : ∃ a : ℤ, a = t p := ⟨_, rfl⟩
      have haT : |(a : ℝ)| ≤ T := by
        have := ht p (by simp)
        rw [ha]; exact_mod_cast this
      obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |(a : ℝ)| + |(b : ℝ)| + 1 := ⟨_, rfl⟩
      have hM1 : 1 ≤ M := by rw [hM]; have := abs_nonneg (a : ℝ); have := abs_nonneg (b : ℝ); linarith
      have hX1 : 1 ≤ Real.exp (G * u ^ e) := Real.one_le_exp (by positivity)
      have hMle : M ≤ ((T : ℝ) + 2) * Real.exp (G * u ^ e) := by
        rw [hM]; nlinarith
      obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε / (4 * M) := ⟨_, rfl⟩
      have hηpos : 0 < η := by rw [hη]; positivity
      have hηlt : η < 1 := by
        rw [hη, div_lt_one (by positivity)]; nlinarith
      obtain ⟨m, hm1, hm2, hm3⟩ := hblock η hηpos hηlt
      have hηM : ε / (4 * (|(a : ℝ)| + |(b : ℝ)| + 1)) = η := by rw [← hM, hη]
      have hcomb := block_combine (A := {p}) (B := l'.toFinset) t hε a b m
        (by intro p' hp'; rw [Finset.mem_singleton.mp hp', ha, sub_self, Pn_zero]; exact hε4)
        (by intro q' hq'; exact hb1 q' (List.mem_toFinset.mp hq'))
        (by intro p' hp'; rw [Finset.mem_singleton.mp hp', hηM]; exact hm2)
        (by intro q' hq'; rw [hηM]; exact hm3 q' (List.mem_toFinset.mp hq'))
      refine ⟨m * a + (1 - m) * b, ?_, ?_⟩
      · intro p' hp'
        apply hcomb.1
        rcases List.mem_cons.mp hp' with h | h
        · exact Finset.mem_union_left _ (Finset.mem_singleton.mpr h)
        · exact Finset.mem_union_right _ (List.mem_toFinset.mpr h)
      · rw [hexp, ← hu]
        have hsize := hcomb.2
        have hlogM : Real.log M ≤ Real.log ((T : ℝ) + 2) + G * u ^ e := by
          have := Real.log_le_log (by linarith) hMle
          rwa [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at this
        have hLη : Real.log (1 / η) ≤ K * u ^ e := by
          have h1 : 1 / η = 4 * M * (1 / ε) := by rw [hη]; field_simp
          have h2 : Real.log (1 / η) = 2 * Real.log 2 + Real.log M + Real.log (1 / ε) := by
            rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
              show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            push_cast; ring
          rw [h2, hL, hK]
          have a1 := mul_le_mul_of_nonneg_left hu_e1 (by positivity : (0 : ℝ) ≤ 2 * Real.log 2)
          have a2 := mul_le_mul_of_nonneg_left hu_e1 hlogT2
          have a3 := mul_le_mul_of_nonneg_left hu_le hlog2.le
          nlinarith
        have hL0 : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((one_le_div hηpos).mpr hηlt.le)
        have hsq : Real.log (1 / η) ^ 2 ≤ K ^ 2 * u ^ (2 * e) := by
          have := pow_le_pow_left₀ hL0 hLη 2
          calc Real.log (1 / η) ^ 2 ≤ (K * u ^ e) ^ 2 := this
            _ = K ^ 2 * u ^ (2 * e) := by rw [mul_pow, ← pow_mul, mul_comm e 2]
        obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = Real.exp (C * K ^ 2 * u ^ (2 * e)) := ⟨_, rfl⟩
        have hY1 : 1 ≤ Y := by rw [hY]; exact Real.one_le_exp (by positivity)
        have hmY : |(m : ℝ)| ≤ Y := by
          rw [hY]
          refine hm1.trans (Real.exp_le_exp.mpr ?_)
          have := mul_le_mul_of_nonneg_left hsq hC
          linarith
        have hab : |(a : ℝ)| + |(b : ℝ)| ≤ ((T : ℝ) + 1) * Real.exp (G * u ^ e) := by nlinarith
        have hk1 : |((m * a + (1 - m) * b : ℤ) : ℝ)| ≤ 2 * Y * (((T : ℝ) + 1) * Real.exp (G * u ^ e)) := by
          refine hsize.trans ?_
          have hm' : |(m : ℝ)| + 1 ≤ 2 * Y := by linarith
          exact mul_le_mul hm' hab (by positivity) (by positivity)
        have hu2 : 1 ≤ u ^ (2 * e) := one_le_pow₀ hu1'
        have hue : u ^ e ≤ u ^ (2 * e) := pow_le_pow_right₀ hu1' (by omega)
        have hexpeq : 2 * Y * (((T : ℝ) + 1) * Real.exp (G * u ^ e))
            = Real.exp (Real.log (2 * ((T : ℝ) + 1)) + C * K ^ 2 * u ^ (2 * e) + G * u ^ e) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity), ← hY]; ring
        refine hk1.trans ?_
        rw [hexpeq]
        refine Real.exp_le_exp.mpr ?_
        have b1 := mul_le_mul_of_nonneg_left hu2 hlogT1
        have b2 := mul_le_mul_of_nonneg_left hue hG0
        rw [mul_one] at b1
        linarith

#print axioms effective_transfer

#print axioms seq_lower_liminf
#print axioms seq_upper

end TVGPlus
end LeanCheck
