import LeanCheck.MixedPrimeBasics
import LeanCheck.MixedPrimeFlat
import LeanCheck.MixedPrimeRadii

/-!
# TVGaddmore_v17: density upper bound (Theorem "density", upper bound)

For a base `ℓ ≥ 2` and `δ > 0`, let `okN ℓ δ N k` say `‖k / ℓ^(n^2)‖ < δ` for `1 ≤ n ≤ N`.
Then for `K ≥ ℓ^(N^2)`,  `#{k < K : okN ℓ δ N k} ≤ 2 K e^{1/δ} (2δ)^N`.
(The mixed ball is contained in the one-prime ball, so this bounds `B_δ ∩ [0,K)`; for `δ < 1/2`
this is `exp(-c √ln K)` by choosing `N = ⌊√(log_ℓ K)⌋`.)
-/

namespace LeanCheck
namespace MixedPrime

open Classical

/-- `q_n = ℓ^(n^2)`. -/
def qn (ℓ n : ℕ) : ℕ := ℓ ^ (n ^ 2)

/-- The first `N` square-scale constraints. -/
def okN (ℓ : ℕ) (δ : ℝ) (N : ℕ) (k : ℤ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ N → nrm ((k : ℝ) / (qn ℓ n : ℝ)) < δ

lemma qn_pos {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (n : ℕ) : 0 < qn ℓ n := by unfold qn; positivity

lemma qn_dvd (ℓ : ℕ) {n N : ℕ} (h : n ≤ N) : qn ℓ n ∣ qn ℓ N := by
  unfold qn
  exact Nat.pow_dvd_pow ℓ (by nlinarith)

lemma okN_add_mul {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {δ : ℝ} {N : ℕ} (k m : ℤ) :
    okN ℓ δ N (k + (qn ℓ N : ℤ) * m) ↔ okN ℓ δ N k := by
  have key : ∀ n, 1 ≤ n → n ≤ N → nrm ((((k + (qn ℓ N : ℤ) * m : ℤ)) : ℝ) / (qn ℓ n : ℝ))
      = nrm ((k : ℝ) / (qn ℓ n : ℝ)) := by
    intro n _ hn
    obtain ⟨c, hc⟩ := qn_dvd ℓ hn
    have hq : (qn ℓ n : ℝ) ≠ 0 := by exact_mod_cast (qn_pos hℓ n).ne'
    have e : (((k + (qn ℓ N : ℤ) * m : ℤ)) : ℝ) / (qn ℓ n : ℝ)
        = (k : ℝ) / (qn ℓ n : ℝ) + ((c : ℤ) * m : ℤ) := by
      push_cast
      rw [hc]; push_cast; field_simp
    rw [e, nrm_add_int]
  constructor
  · intro h n h1 hn; rw [← key n h1 hn]; exact h n h1 hn
  · intro h n h1 hn; rw [key n h1 hn]; exact h n h1 hn

lemma okN_mod {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {δ : ℝ} {N : ℕ} (k : ℤ) :
    okN ℓ δ N k ↔ okN ℓ δ N (k % (qn ℓ N : ℤ)) := by
  have := okN_add_mul hℓ (δ := δ) (N := N) (k % (qn ℓ N : ℤ)) (k / (qn ℓ N : ℤ))
  rw [Int.emod_add_mul_ediv] at this
  exact this

/-- Residues modulo `q_N` satisfying the first `N` constraints. -/
noncomputable def Afin (ℓ : ℕ) (δ : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (qn ℓ N)).filter fun r => okN ℓ δ N (r : ℤ)

/-- Periodic counting. -/
lemma count_le {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (δ : ℝ) (N K : ℕ) :
    ((Finset.range K).filter fun k : ℕ => okN ℓ δ N (k : ℤ)).card ≤ (K / qn ℓ N + 1) * (Afin ℓ δ N).card := by
  have hq := qn_pos hℓ N
  set s := (Finset.range K).filter fun k : ℕ => okN ℓ δ N (k : ℤ) with hs
  have himg : s.image (fun k => k % qn ℓ N) ⊆ Afin ℓ δ N := by
    intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    simp only [hs, Finset.mem_filter] at hk
    simp only [Afin, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hq, ?_⟩
    have := (okN_mod hℓ (δ := δ) (N := N) (k : ℤ)).mp hk.2
    simpa using this
  calc s.card ≤ (K / qn ℓ N + 1) * (s.image (fun k => k % qn ℓ N)).card := by
        apply Finset.card_le_mul_card_image
        intro a ha
        calc (s.filter fun k => k % qn ℓ N = a).card
            ≤ ((Finset.range (K / qn ℓ N + 1)).image fun j => a + qn ℓ N * j).card := by
              apply Finset.card_le_card
              intro k hk
              simp only [Finset.mem_filter, hs, Finset.mem_range] at hk
              simp only [Finset.mem_image, Finset.mem_range]
              refine ⟨k / qn ℓ N, ?_, ?_⟩
              · have := Nat.div_le_div_right (c := qn ℓ N) hk.1.1.le
                omega
              · rw [← hk.2]; exact Nat.mod_add_div k (qn ℓ N)
          _ ≤ (Finset.range (K / qn ℓ N + 1)).card := Finset.card_image_le
          _ = K / qn ℓ N + 1 := Finset.card_range _
    _ ≤ (K / qn ℓ N + 1) * (Afin ℓ δ N).card := by
        gcongr

lemma qn_succ (ℓ N : ℕ) : qn ℓ (N + 1) = ℓ ^ (2 * N + 1) * qn ℓ N := by
  unfold qn
  rw [show (N + 1) ^ 2 = (2 * N + 1) + N ^ 2 by ring, pow_add]

lemma nrm_unit {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : nrm t = min t (1 - t) := by
  rw [nrm_eq, abs_sub_round_eq_min, Int.fract_eq_self.mpr ⟨h0, h1⟩]

/-- At most `2 ⌈δ a⌉` of the `a` lifts of a residue modulo `q_N` to a residue modulo `q_{N+1} = a q_N`
satisfy the next constraint. -/
lemma lift_card {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {δ : ℝ} (hδ : 0 < δ) (N c : ℕ) (hc : c < qn ℓ N) :
    ((Finset.range (ℓ ^ (2 * N + 1))).filter fun j : ℕ =>
        nrm ((((c + qn ℓ N * j : ℕ)) : ℝ) / (qn ℓ (N + 1) : ℝ)) < δ).card
      ≤ 2 * ⌈δ * ((ℓ ^ (2 * N + 1) : ℕ) : ℝ)⌉₊ := by
  set a : ℕ := ℓ ^ (2 * N + 1) with ha
  set q : ℕ := qn ℓ N with hq
  set c0 : ℕ := ⌈δ * (a : ℝ)⌉₊ with hc0
  have hq0 : 0 < q := qn_pos hℓ N
  have ha0 : 0 < a := by rw [ha]; positivity
  have hM : qn ℓ (N + 1) = a * q := qn_succ ℓ N
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  have hsub : ((Finset.range a).filter fun j : ℕ =>
        nrm ((((c + q * j : ℕ)) : ℝ) / (qn ℓ (N + 1) : ℝ)) < δ)
      ⊆ Finset.range c0 ∪ Finset.Ico (a - c0) a := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hja, hnr⟩ := hj
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    have hy : c + q * j < a * q := by nlinarith
    have hMR : ((qn ℓ (N + 1) : ℕ) : ℝ) = a * q := by rw [hM]; push_cast; ring
    have hyR : (((c + q * j : ℕ)) : ℝ) = c + q * j := by push_cast; ring
    have ht0 : 0 ≤ (((c + q * j : ℕ)) : ℝ) / (qn ℓ (N + 1) : ℝ) := by positivity
    have ht1 : (((c + q * j : ℕ)) : ℝ) / (qn ℓ (N + 1) : ℝ) < 1 := by
      rw [div_lt_one (by rw [hMR]; positivity), hMR]
      exact_mod_cast hy
    rw [nrm_unit ht0 ht1] at hnr
    rcases min_lt_iff.mp hnr with h1 | h1
    · left
      rw [div_lt_iff₀ (by rw [hMR]; positivity), hMR, hyR] at h1
      have h2 : (q : ℝ) * j < δ * a * q := by
        have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
        nlinarith
      have h3 : (j : ℝ) < δ * a := by
        have : (q : ℝ) * j < q * (δ * a) := by nlinarith
        exact lt_of_mul_lt_mul_left this hqR.le
      exact Nat.lt_ceil.mpr h3
    · right
      have h2 : 1 - (((c + q * j : ℕ)) : ℝ) / (qn ℓ (N + 1) : ℝ) = ((a * q : ℝ) - (c + q * j)) / (a * q) := by
        rw [hMR, hyR]; field_simp
      rw [h2, div_lt_iff₀ (by positivity)] at h1
      have hcq : (c : ℝ) + 1 ≤ q := by exact_mod_cast hc
      have h3 : (q : ℝ) * ((a : ℝ) - j - 1) < δ * a * q := by nlinarith
      have h4 : ((a : ℝ) - j - 1) < δ * a := by
        have : (q : ℝ) * ((a : ℝ) - j - 1) < q * (δ * a) := by nlinarith
        exact lt_of_mul_lt_mul_left this hqR.le
      have h5 : ((a : ℝ) - j - 1) < c0 := lt_of_lt_of_le h4 (Nat.le_ceil _)
      have h6 : a < j + 1 + c0 := by
        have : (a : ℝ) < j + 1 + c0 := by linarith
        exact_mod_cast this
      exact ⟨by omega, hja⟩
  calc _ ≤ (Finset.range c0 ∪ Finset.Ico (a - c0) a).card := Finset.card_le_card hsub
    _ ≤ (Finset.range c0).card + (Finset.Ico (a - c0) a).card := Finset.card_union_le _ _
    _ ≤ c0 + c0 := by
        rw [Finset.card_range, Nat.card_Ico]
        have : a - (a - c0) ≤ c0 := by omega
        omega
    _ = 2 * c0 := by ring

/-- One step of the recursion for the number of admissible residues. -/
lemma Afin_succ {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    (Afin ℓ δ (N + 1)).card ≤ (Afin ℓ δ N).card * (2 * ⌈δ * ((ℓ ^ (2 * N + 1) : ℕ) : ℝ)⌉₊) := by
  have hq := qn_pos hℓ N
  have himg : (Afin ℓ δ (N + 1)).image (fun r => r % qn ℓ N) ⊆ Afin ℓ δ N := by
    intro r hr
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    simp only [Afin, Finset.mem_filter, Finset.mem_range] at hk
    simp only [Afin, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hq, ?_⟩
    have h1 : okN ℓ δ N (k : ℤ) := fun n h1 hn => hk.2 n h1 (by omega)
    have := (okN_mod hℓ (δ := δ) (N := N) (k : ℤ)).mp h1
    simpa using this
  calc (Afin ℓ δ (N + 1)).card
      ≤ (2 * ⌈δ * ((ℓ ^ (2 * N + 1) : ℕ) : ℝ)⌉₊) * ((Afin ℓ δ (N + 1)).image (fun r => r % qn ℓ N)).card := by
        apply Finset.card_le_mul_card_image
        intro a' ha'
        have ha'N : a' < qn ℓ N := by
          have := himg ha'
          simp only [Afin, Finset.mem_filter, Finset.mem_range] at this
          exact this.1
        calc ((Afin ℓ δ (N + 1)).filter fun r => r % qn ℓ N = a').card
            ≤ (((Finset.range (ℓ ^ (2 * N + 1))).filter fun j : ℕ =>
                nrm ((((a' + qn ℓ N * j : ℕ)) : ℝ) / (qn ℓ (N + 1) : ℝ)) < δ).image
                  fun j => a' + qn ℓ N * j).card := by
              apply Finset.card_le_card
              intro r hr
              simp only [Finset.mem_filter, Afin, Finset.mem_range] at hr
              obtain ⟨⟨hrlt, hrok⟩, hmod⟩ := hr
              simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
              have hdec : a' + qn ℓ N * (r / qn ℓ N) = r := by rw [← hmod]; exact Nat.mod_add_div r _
              refine ⟨r / qn ℓ N, ⟨?_, ?_⟩, hdec⟩
              · rw [Nat.div_lt_iff_lt_mul hq]
                rw [qn_succ] at hrlt
                nlinarith
              · have := hrok (N + 1) (by omega) le_rfl
                have e : ((r : ℤ) : ℝ) = (((a' + qn ℓ N * (r / qn ℓ N) : ℕ)) : ℝ) := by
                  rw [hdec]; simp
                rw [e] at this
                exact this
          _ ≤ _ := Finset.card_image_le
          _ ≤ 2 * ⌈δ * ((ℓ ^ (2 * N + 1) : ℕ) : ℝ)⌉₊ := lift_card hℓ hδ N a' ha'N
    _ ≤ (2 * ⌈δ * ((ℓ ^ (2 * N + 1) : ℕ) : ℝ)⌉₊) * (Afin ℓ δ N).card := by
        gcongr
    _ = _ := by ring

lemma Afin_zero_card (ℓ : ℕ) (δ : ℝ) : (Afin ℓ δ 0).card ≤ 1 := by
  have : qn ℓ 0 = 1 := by simp [qn]
  calc (Afin ℓ δ 0).card ≤ (Finset.range (qn ℓ 0)).card := Finset.card_filter_le _ _
    _ = 1 := by rw [this]; simp

lemma Afin_prod {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ((Afin ℓ δ N).card : ℝ) ≤
      ∏ n ∈ Finset.range N, (2 * δ * (ℓ : ℝ) ^ (2 * n + 1) + 2) := by
  induction N with
  | zero => simpa using (by exact_mod_cast Afin_zero_card ℓ δ : ((Afin ℓ δ 0).card : ℝ) ≤ 1)
  | succ N ih =>
    rw [Finset.prod_range_succ]
    have h1 := Afin_succ hℓ hδ N
    have h2 : (((Afin ℓ δ (N + 1)).card : ℕ) : ℝ) ≤
        ((Afin ℓ δ N).card : ℝ) * (2 * ⌈δ * ((ℓ ^ (2 * N + 1) : ℕ) : ℝ)⌉₊ : ℕ) := by exact_mod_cast h1
    have h3 : ((2 * ⌈δ * ((ℓ ^ (2 * N + 1) : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ 2 * δ * (ℓ : ℝ) ^ (2 * N + 1) + 2 := by
      push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ δ * ((ℓ ^ (2 * N + 1) : ℕ) : ℝ) by positivity)
      push_cast at this
      nlinarith
    have h4 : 0 ≤ ((Afin ℓ δ N).card : ℝ) := Nat.cast_nonneg _
    calc _ ≤ _ := h2
      _ ≤ ((Afin ℓ δ N).card : ℝ) * (2 * δ * (ℓ : ℝ) ^ (2 * N + 1) + 2) := by gcongr
      _ ≤ (∏ n ∈ Finset.range N, (2 * δ * (ℓ : ℝ) ^ (2 * n + 1) + 2)) *
            (2 * δ * (ℓ : ℝ) ^ (2 * N + 1) + 2) := by gcongr

lemma prod_a (ℓ : ℕ) (N : ℕ) :
    ∏ n ∈ Finset.range N, (ℓ : ℝ) ^ (2 * n + 1) = (ℓ : ℝ) ^ (N ^ 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ih, ← pow_add]
    congr 1; ring

lemma sum_inv_a_le {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / (ℓ : ℝ) ^ (2 * n + 1) ≤ 1 := by
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  calc ∑ n ∈ Finset.range N, 1 / (ℓ : ℝ) ^ (2 * n + 1)
      ≤ ∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ (n + 1) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [one_div_pow]
        have h1 : (2 : ℝ) ^ (n + 1) ≤ (ℓ : ℝ) ^ (2 * n + 1) := by
          calc (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (2 * n + 1) :=
                pow_le_pow_right₀ (by norm_num) (by omega)
            _ ≤ (ℓ : ℝ) ^ (2 * n + 1) := by gcongr
        exact one_div_le_one_div_of_le (by positivity) h1
    _ ≤ 1 := geom_half_le N

/-- **Density upper bound** (Theorem "density", upper bound). -/
theorem density_upper {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {δ : ℝ} (hδ : 0 < δ) (N K : ℕ) (hK : qn ℓ N ≤ K) :
    (((Finset.range K).filter fun k : ℕ => okN ℓ δ N (k : ℤ)).card : ℝ)
      ≤ 2 * K * Real.exp (1 / δ) * (2 * δ) ^ N := by
  have hℓ1 : 1 ≤ ℓ := by omega
  have hqpos : (0 : ℝ) < qn ℓ N := by exact_mod_cast qn_pos hℓ1 N
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  -- the residue bound
  have hA : ((Afin ℓ δ N).card : ℝ) ≤ qn ℓ N * Real.exp (1 / δ) * (2 * δ) ^ N := by
    refine (Afin_prod hℓ1 hδ N).trans ?_
    have hfac : ∀ n ∈ Finset.range N,
        (2 * δ * (ℓ : ℝ) ^ (2 * n + 1) + 2)
          ≤ (ℓ : ℝ) ^ (2 * n + 1) * ((2 * δ) * Real.exp (1 / δ * (1 / (ℓ : ℝ) ^ (2 * n + 1)))) := by
      intro n _
      have ha : (0 : ℝ) < (ℓ : ℝ) ^ (2 * n + 1) := by positivity
      have h1 := Real.add_one_le_exp (1 / δ * (1 / (ℓ : ℝ) ^ (2 * n + 1)))
      calc 2 * δ * (ℓ : ℝ) ^ (2 * n + 1) + 2
          = (ℓ : ℝ) ^ (2 * n + 1) * ((2 * δ) * (1 / δ * (1 / (ℓ : ℝ) ^ (2 * n + 1)) + 1)) := by
            field_simp; ring
        _ ≤ (ℓ : ℝ) ^ (2 * n + 1) * ((2 * δ) * Real.exp (1 / δ * (1 / (ℓ : ℝ) ^ (2 * n + 1)))) := by
            gcongr
    calc ∏ n ∈ Finset.range N, (2 * δ * (ℓ : ℝ) ^ (2 * n + 1) + 2)
        ≤ ∏ n ∈ Finset.range N, ((ℓ : ℝ) ^ (2 * n + 1) *
            ((2 * δ) * Real.exp (1 / δ * (1 / (ℓ : ℝ) ^ (2 * n + 1))))) :=
          Finset.prod_le_prod₀ (fun n _ => by positivity) hfac
      _ = (∏ n ∈ Finset.range N, (ℓ : ℝ) ^ (2 * n + 1)) *
            ((2 * δ) ^ N * Real.exp (∑ n ∈ Finset.range N, 1 / δ * (1 / (ℓ : ℝ) ^ (2 * n + 1)))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
            Real.exp_sum]
      _ ≤ (ℓ : ℝ) ^ (N ^ 2) * ((2 * δ) ^ N * Real.exp (1 / δ)) := by
          rw [prod_a]
          gcongr
          rw [← Finset.mul_sum]
          calc 1 / δ * ∑ n ∈ Finset.range N, 1 / (ℓ : ℝ) ^ (2 * n + 1) ≤ 1 / δ * 1 := by
                gcongr; exact sum_inv_a_le hℓ N
            _ = 1 / δ := mul_one _
      _ = qn ℓ N * Real.exp (1 / δ) * (2 * δ) ^ N := by
          unfold qn; push_cast; ring
  -- periodic counting
  have hcount := count_le hℓ1 δ N K
  have hc : (((Finset.range K).filter fun k : ℕ => okN ℓ δ N (k : ℤ)).card : ℝ)
      ≤ (((K / qn ℓ N + 1 : ℕ)) : ℝ) * ((Afin ℓ δ N).card : ℝ) := by exact_mod_cast hcount
  have hdiv : (((K / qn ℓ N + 1 : ℕ)) : ℝ) ≤ 2 * K / qn ℓ N := by
    have h1 : ((K / qn ℓ N : ℕ) : ℝ) ≤ (K : ℝ) / qn ℓ N := Nat.cast_div_le
    have h2 : (1 : ℝ) ≤ (K : ℝ) / qn ℓ N := by
      rw [le_div_iff₀ hqpos]; simpa using (by exact_mod_cast hK : (qn ℓ N : ℝ) ≤ K)
    push_cast
    calc ((K / qn ℓ N : ℕ) : ℝ) + 1 ≤ (K : ℝ) / qn ℓ N + (K : ℝ) / qn ℓ N := by linarith
      _ = 2 * K / qn ℓ N := by ring
  have hA0 : 0 ≤ ((Afin ℓ δ N).card : ℝ) := Nat.cast_nonneg _
  calc _ ≤ (((K / qn ℓ N + 1 : ℕ)) : ℝ) * ((Afin ℓ δ N).card : ℝ) := hc
    _ ≤ (2 * K / qn ℓ N) * (qn ℓ N * Real.exp (1 / δ) * (2 * δ) ^ N) := by gcongr
    _ = 2 * K * Real.exp (1 / δ) * (2 * δ) ^ N := by field_simp


/-- The same bound for the (mixed) ball `{k : Pn S k < δ}` for every scale set containing `sqScales ℓ`. -/
theorem density_ball {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {δ : ℝ} (hδ : 0 < δ) (S : Set ℕ) (hSub : sqScales ℓ ⊆ S)
    (N K : ℕ) (hK : qn ℓ N ≤ K) :
    (((Finset.range K).filter fun k : ℕ => Pn S (k : ℤ) < δ).card : ℝ)
      ≤ 2 * K * Real.exp (1 / δ) * (2 * δ) ^ N := by
  refine le_trans ?_ (density_upper hℓ hδ N K hK)
  have : ((Finset.range K).filter fun k : ℕ => Pn S (k : ℤ) < δ) ⊆
      (Finset.range K).filter fun k : ℕ => okN ℓ δ N (k : ℤ) := by
    intro k hk
    simp only [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, fun n hn _ => lt_of_le_of_lt ?_ hk.2⟩
    exact le_Pn (hSub (mem_sqScales hn)) (k : ℤ)
  exact_mod_cast Finset.card_le_card this

end MixedPrime
end LeanCheck
