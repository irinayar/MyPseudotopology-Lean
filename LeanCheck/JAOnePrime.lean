import Mathlib
import LeanCheck.MixedPrimeRadii
import LeanCheck.ChainLemmas

/-!
# The one-prime theorem (Theorem `oneprime` of `TVGaddmore_v27`)

If `k ↦ e(kα)` is continuous at `0` for the pseudo-norm `P_ℓ(k) = sup_n ‖k / ℓ^(n^2)‖` of a single base `ℓ ≥ 2`, then
`ℓ^(j^2) α ∈ ℤ` for some `j`; i.e. the parameters are exactly those in `ℤ[1/ℓ]/ℤ`.

Checked here (no axiom, no `sorry`): `geom_sq`, `step1` (the sums `∑ ℓ^(m^2) w_m` with small `w_m` are `P_ℓ`-small),
`oneprime` and `oneprime_two_three` (a parameter that is continuous for both `P_2` and `P_3` is an integer).
-/

namespace LeanCheck
namespace JAOnePrime

open MixedPrime Finset

lemma geom_sq (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (n : ℕ) :
    ∑ m ∈ Finset.range n, (ℓ : ℝ) ^ ((m + 1) ^ 2) ≤ 2 * (ℓ : ℝ) ^ (n ^ 2) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    have h1 : (ℓ : ℝ) ^ ((n + 1) ^ 2) = (ℓ : ℝ) ^ (n ^ 2) * (ℓ : ℝ) ^ (2 * n + 1) := by
      rw [← pow_add]; congr 1; ring
    have h2 : (2 : ℝ) ≤ (ℓ : ℝ) ^ (2 * n + 1) := by
      calc (2 : ℝ) ≤ ℓ := hℓ'
        _ = (ℓ : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (ℓ : ℝ) ^ (2 * n + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    have h3 : 0 < (ℓ : ℝ) ^ (n ^ 2) := by positivity
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left h2 h3.le]

/-- Step 1: combinations `∑ ℓ^(m^2) w_m` with `|w_m| < δ' ℓ^(2m+1)` have `P_ℓ ≤ 2δ'`. -/
lemma step1 (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (δ' : ℝ) (hδ' : 0 ≤ δ') (F : Finset ℕ) (w : ℕ → ℤ)
    (hw : ∀ m ∈ F, |(w m : ℝ)| < δ' * (ℓ : ℝ) ^ (2 * m + 1)) :
    Pn (sqScales ℓ) (∑ m ∈ F, (ℓ : ℤ) ^ (m ^ 2) * w m) ≤ 2 * δ' := by
  classical
  have hne : (sqScales ℓ).Nonempty := ⟨ℓ ^ (1 ^ 2), 1, le_rfl, rfl⟩
  apply Pn_le hne
  rintro q ⟨n, hn, rfl⟩
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  set A : ℤ := ∑ m ∈ F.filter (fun m => m < n), (ℓ : ℤ) ^ (m ^ 2) * w m with hA
  set B : ℤ := ∑ m ∈ F.filter (fun m => ¬ m < n), (ℓ : ℤ) ^ (m ^ 2) * w m with hB
  have hsplit : ∑ m ∈ F, (ℓ : ℤ) ^ (m ^ 2) * w m = A + B :=
    (Finset.sum_filter_add_sum_filter_not F _ _).symm
  obtain ⟨c, hc⟩ : ∃ c : ℤ, B = (ℓ : ℤ) ^ (n ^ 2) * c := by
    refine ⟨∑ m ∈ F.filter (fun m => ¬ m < n), (ℓ : ℤ) ^ (m ^ 2 - n ^ 2) * w m, ?_⟩
    rw [hB, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmn : n ≤ m := not_lt.mp (Finset.mem_filter.mp hm).2
    have h1 : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hmn 2
    have h2 : (ℓ : ℤ) ^ (m ^ 2) = (ℓ : ℤ) ^ (n ^ 2) * (ℓ : ℤ) ^ (m ^ 2 - n ^ 2) := by
      rw [← pow_add]; congr 1; omega
    rw [h2]; ring
  have hq : (0 : ℝ) < ((ℓ ^ (n ^ 2) : ℕ) : ℝ) := by positivity
  have hk : (((∑ m ∈ F, (ℓ : ℤ) ^ (m ^ 2) * w m : ℤ) : ℝ)) / ((ℓ ^ (n ^ 2) : ℕ) : ℝ) =
      (A : ℝ) / ((ℓ ^ (n ^ 2) : ℕ) : ℝ) + (c : ℝ) := by
    rw [hsplit, hc]; push_cast; field_simp
  rw [hk, nrm_add_int]
  refine (nrm_le_abs _).trans ?_
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
  -- bound `|A|`
  have hterm : ∀ m ∈ F.filter (fun m => m < n),
      |((ℓ : ℤ) ^ (m ^ 2) * w m : ℤ)| ≤ δ' * (ℓ : ℝ) ^ ((m + 1) ^ 2) := by
    intro m hm
    have hmF := (Finset.mem_filter.mp hm).1
    have := hw m hmF
    have e : (ℓ : ℝ) ^ ((m + 1) ^ 2) = (ℓ : ℝ) ^ (m ^ 2) * (ℓ : ℝ) ^ (2 * m + 1) := by
      rw [← pow_add]; congr 1; ring
    have hp : (0 : ℝ) < (ℓ : ℝ) ^ (m ^ 2) := by positivity
    push_cast
    rw [abs_mul, abs_of_pos hp, e]
    nlinarith
  have hAabs : |(A : ℝ)| ≤ ∑ m ∈ F.filter (fun m => m < n), δ' * (ℓ : ℝ) ^ ((m + 1) ^ 2) := by
    have h1 : |(A : ℝ)| ≤ ∑ m ∈ F.filter (fun m => m < n), |(((ℓ : ℤ) ^ (m ^ 2) * w m : ℤ) : ℝ)| := by
      rw [hA]; push_cast
      exact Finset.abs_sum_le_sum_abs _ _
    refine h1.trans (Finset.sum_le_sum (fun m hm => ?_))
    have := hterm m hm
    simpa using this
  have hsub : ∑ m ∈ F.filter (fun m => m < n), δ' * (ℓ : ℝ) ^ ((m + 1) ^ 2) ≤
      ∑ m ∈ Finset.range n, δ' * (ℓ : ℝ) ^ ((m + 1) ^ 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hm).2
    · intro m _ _; positivity
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsub
  rw [← Finset.mul_sum] at hAabs
  have hg := geom_sq ℓ hℓ n
  have hpowq : ((ℓ ^ (n ^ 2) : ℕ) : ℝ) = (ℓ : ℝ) ^ (n ^ 2) := by push_cast; ring
  rw [hpowq]
  have h3 := mul_le_mul_of_nonneg_left hg hδ'
  nlinarith [h3, hAabs, hsub, hδ']
/-- The residue of `ℓ^(m^2) α` modulo `ℤ`, in `[-1/2, 1/2]`. -/
noncomputable def rr (ℓ : ℕ) (α : ℝ) (m : ℕ) : ℝ :=
  (ℓ : ℝ) ^ (m ^ 2) * α - round ((ℓ : ℝ) ^ (m ^ 2) * α)

/-- `W_m`, the largest integer below `δ' ℓ^(2m+1)`. -/
noncomputable def Wm (ℓ : ℕ) (δ' : ℝ) (m : ℕ) : ℕ := ⌈δ' * (ℓ : ℝ) ^ (2 * m + 1)⌉₊ - 1

lemma Wm_lt (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (δ' : ℝ) (hδ' : 0 < δ') (m : ℕ) :
    (Wm ℓ δ' m : ℝ) < δ' * (ℓ : ℝ) ^ (2 * m + 1) := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hx : 0 < δ' * (ℓ : ℝ) ^ (2 * m + 1) := by positivity
  have h1 : 1 ≤ ⌈δ' * (ℓ : ℝ) ^ (2 * m + 1)⌉₊ := Nat.ceil_pos.mpr hx
  have h2 := Nat.ceil_lt_add_one hx.le
  unfold Wm
  rw [Nat.cast_sub h1]
  push_cast
  linarith

lemma Wm_ge (ℓ : ℕ) (δ' : ℝ) (m : ℕ) (hx : 2 ≤ δ' * (ℓ : ℝ) ^ (2 * m + 1)) :
    δ' * (ℓ : ℝ) ^ (2 * m + 1) / 2 ≤ (Wm ℓ δ' m : ℝ) ∧ 1 ≤ Wm ℓ δ' m := by
  have h1 : 1 ≤ ⌈δ' * (ℓ : ℝ) ^ (2 * m + 1)⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have h2 := Nat.le_ceil (δ' * (ℓ : ℝ) ^ (2 * m + 1))
  have e : (Wm ℓ δ' m : ℝ) = (⌈δ' * (ℓ : ℝ) ^ (2 * m + 1)⌉₊ : ℝ) - 1 := by
    unfold Wm; rw [Nat.cast_sub h1]; simp
  refine ⟨by rw [e]; linarith, ?_⟩
  have : (1 : ℝ) ≤ (Wm ℓ δ' m : ℝ) := by rw [e]; linarith
  exact_mod_cast this

lemma exists_m1 (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → 2 ≤ δ' * (ℓ : ℝ) ^ (2 * m + 1) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / δ') (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, fun m hm => ?_⟩
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h1 : (2 : ℝ) ^ n ≤ (ℓ : ℝ) ^ (2 * m + 1) :=
    calc (2 : ℝ) ^ n ≤ 2 ^ (2 * m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ (ℓ : ℝ) ^ (2 * m + 1) := pow_le_pow_left₀ (by norm_num) hℓ' _
  rw [div_lt_iff₀ hδ'] at hn
  nlinarith [mul_le_mul_of_nonneg_left h1 hδ'.le]

/-- **The one-prime theorem.** -/
theorem oneprime (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (α δ : ℝ) (hδ : 0 < δ)
    (h : ∀ k : ℤ, Pn (sqScales ℓ) k < δ → nrm ((k : ℝ) * α) < 1 / 4) :
    ∃ (j : ℕ) (z : ℤ), (ℓ : ℝ) ^ (j ^ 2) * α = z := by
  classical
  set δ' : ℝ := δ / 3 with hδ'def
  have hδ' : 0 < δ' := by positivity
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ1 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hcomb : ∀ (F : Finset ℕ) (w : ℕ → ℤ), (∀ m ∈ F, |(w m : ℝ)| < δ' * (ℓ : ℝ) ^ (2 * m + 1)) →
      nrm (((∑ m ∈ F, (ℓ : ℤ) ^ (m ^ 2) * w m : ℤ) : ℝ) * α) < 1 / 4 := by
    intro F w hw
    apply h
    have := step1 ℓ hℓ δ' hδ'.le F w hw
    linarith
  obtain ⟨m₁, hm₁⟩ := exists_m1 ℓ hℓ δ' hδ'
  -- Step 2: each residue is tiny
  have step2 : ∀ m, m₁ ≤ m → |rr ℓ α m| ≤ 1 / (4 * (Wm ℓ δ' m : ℝ)) := by
    intro m hm
    obtain ⟨_, hW1⟩ := Wm_ge ℓ δ' m (hm₁ m hm)
    have hWlt := Wm_lt ℓ hℓ δ' hδ' m
    have hmult : ∀ ρ : ℕ, ρ ≤ Wm ℓ δ' m →
        ∃ n : ℤ, |(ρ : ℝ) * ((ℓ : ℝ) ^ (m ^ 2) * α) - n| < 1 / 4 := by
      intro ρ hρ
      rcases Nat.eq_zero_or_pos ρ with rfl | hρ0
      · exact ⟨0, by norm_num⟩
      · have hlt := hcomb {m} (fun _ => (ρ : ℤ)) (by
          intro m' hm'
          rw [Finset.mem_singleton] at hm'; subst hm'
          have : (ρ : ℝ) ≤ Wm ℓ δ' m' := by exact_mod_cast hρ
          show |((ρ : ℤ) : ℝ)| < _
          rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ρ)]
          linarith)
        rw [Finset.sum_singleton, nrm_eq] at hlt
        refine ⟨round ((((ℓ : ℤ) ^ (m ^ 2) * (ρ : ℤ) : ℤ) : ℝ) * α), ?_⟩
        have e : (((ℓ : ℤ) ^ (m ^ 2) * (ρ : ℤ) : ℤ) : ℝ) * α =
            (ρ : ℝ) * ((ℓ : ℝ) ^ (m ^ 2) * α) := by push_cast; ring
        rw [e] at hlt ⊢
        exact hlt
    obtain ⟨z, hz⟩ := near_of_all_multiples (θ := (ℓ : ℝ) ^ (m ^ 2) * α) (R := Wm ℓ δ' m) hW1 hmult
    exact (round_le _ z).trans hz
  -- the terms `t`
  set t : ℕ → ℝ := fun i => (Wm ℓ δ' (m₁ + i) : ℝ) * |rr ℓ α (m₁ + i)| with htdef
  have ht0 : ∀ i, 0 ≤ t i := fun i => by simp only [htdef]; positivity
  have ht4 : ∀ i, t i ≤ 1 / 4 := by
    intro i
    have h2 := step2 (m₁ + i) (by omega)
    obtain ⟨_, hW1⟩ := Wm_ge ℓ δ' (m₁ + i) (hm₁ _ (by omega))
    have hW : (0 : ℝ) < Wm ℓ δ' (m₁ + i) := Nat.cast_pos.mpr (by omega)
    simp only [htdef]
    calc (Wm ℓ δ' (m₁ + i) : ℝ) * |rr ℓ α (m₁ + i)|
        ≤ (Wm ℓ δ' (m₁ + i) : ℝ) * (1 / (4 * (Wm ℓ δ' (m₁ + i) : ℝ))) := by gcongr
      _ = 1 / 4 := by field_simp
  -- Step 3: partial sums stay below 1/4
  have hpart : ∀ N, ∑ i ∈ Finset.range N, t i < 1 / 4 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hlt : ∑ i ∈ Finset.range (N + 1), t i < 1 / 2 := by
        rw [Finset.sum_range_succ]; linarith [ht4 N]
      have hnn : 0 ≤ ∑ i ∈ Finset.range (N + 1), t i := Finset.sum_nonneg (fun i _ => ht0 i)
      set s : ℕ → ℤ := fun m => if 0 ≤ rr ℓ α m then 1 else -1 with hs
      set w : ℕ → ℤ := fun m => (Wm ℓ δ' m : ℤ) * s m with hw
      set F : Finset ℕ := Finset.Ico m₁ (m₁ + (N + 1)) with hF
      have hFw : ∀ m ∈ F, |(w m : ℝ)| < δ' * (ℓ : ℝ) ^ (2 * m + 1) := by
        intro m _
        have hs1 : |(s m : ℝ)| = 1 := by
          simp only [hs]; split_ifs <;> simp
        have : |(w m : ℝ)| = (Wm ℓ δ' m : ℝ) := by
          simp only [hw]; push_cast; rw [abs_mul, hs1, mul_one]; exact abs_of_nonneg (Nat.cast_nonneg _)
        rw [this]; exact Wm_lt ℓ hℓ δ' hδ' m
      have hlt4 := hcomb F w hFw
      have hk : ((∑ m ∈ F, (ℓ : ℤ) ^ (m ^ 2) * w m : ℤ) : ℝ) * α =
          ∑ i ∈ Finset.range (N + 1), t i +
            ((∑ m ∈ F, w m * round ((ℓ : ℝ) ^ (m ^ 2) * α) : ℤ) : ℝ) := by
        have h1 : ∀ m ∈ F, (((ℓ : ℤ) ^ (m ^ 2) * w m : ℤ) : ℝ) * α =
            (Wm ℓ δ' m : ℝ) * |rr ℓ α m| + ((w m * round ((ℓ : ℝ) ^ (m ^ 2) * α) : ℤ) : ℝ) := by
          intro m _
          have hsr : ((w m : ℤ) : ℝ) * rr ℓ α m = (Wm ℓ δ' m : ℝ) * |rr ℓ α m| := by
            simp only [hw, hs]
            by_cases h0 : 0 ≤ rr ℓ α m
            · simp [h0, abs_of_nonneg h0]
            · push_neg at h0
              simp [not_le.mpr h0, abs_of_neg h0]
          have hrr : (ℓ : ℝ) ^ (m ^ 2) * α = rr ℓ α m + round ((ℓ : ℝ) ^ (m ^ 2) * α) := by
            unfold rr; ring
          push_cast
          linear_combination (w m : ℝ) * hrr + hsr
        rw [Int.cast_sum, Finset.sum_mul]
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
        congr 1
        · rw [hF, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
        · rw [Int.cast_sum]
      have hn : nrm (∑ i ∈ Finset.range (N + 1), t i) < 1 / 4 := by
        rw [hk, nrm_add_int] at hlt4; exact hlt4
      rw [nrm_eq_abs (by rw [abs_of_nonneg hnn]; linarith), abs_of_nonneg hnn] at hn
      exact hn
  have hsum : Summable t := summable_of_sum_range_le ht0 (c := 1 / 4) (fun n => (hpart n).le)
  have ht_tend := hsum.tendsto_atTop_zero
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (ht_tend.eventually (gt_mem_nhds (show (0 : ℝ) < δ' / 4 by positivity)))
  -- Step 4
  set m₂ : ℕ := m₁ + N₀ with hm₂
  have hsmall : ∀ m, m₂ ≤ m → (ℓ : ℝ) ^ (2 * m + 1) * |rr ℓ α m| < 1 / 2 := by
    intro m hm
    obtain ⟨hWge, _⟩ := Wm_ge ℓ δ' m (hm₁ m (by omega))
    have hti := hN₀ (m - m₁) (by omega)
    have e : m₁ + (m - m₁) = m := by omega
    have hti' : (Wm ℓ δ' m : ℝ) * |rr ℓ α m| < δ' / 4 := by
      have : t (m - m₁) = (Wm ℓ δ' m : ℝ) * |rr ℓ α m| := by simp only [htdef, e]
      rw [← this]; exact hti
    have h3 := mul_le_mul_of_nonneg_right hWge (abs_nonneg (rr ℓ α m))
    have h4 : δ' * ((ℓ : ℝ) ^ (2 * m + 1) * |rr ℓ α m|) < δ' * (1 / 2) := by nlinarith
    exact lt_of_mul_lt_mul_left h4 hδ'.le
  have hrec : ∀ m, m₂ ≤ m → rr ℓ α (m + 1) = (ℓ : ℝ) ^ (2 * m + 1) * rr ℓ α m := by
    intro m hm
    have hs := hsmall m hm
    have hLpos : (0 : ℝ) < (ℓ : ℝ) ^ (2 * m + 1) := by positivity
    have hy : |(ℓ : ℝ) ^ (2 * m + 1) * rr ℓ α m| < 1 / 2 := by
      rw [abs_mul, abs_of_pos hLpos]; exact hs
    have hy' := abs_lt.mp hy
    set z : ℤ := round ((ℓ : ℝ) ^ (m ^ 2) * α) with hz
    have hθ' : (ℓ : ℝ) ^ ((m + 1) ^ 2) * α =
        (ℓ : ℝ) ^ (2 * m + 1) * rr ℓ α m + (((ℓ : ℤ) ^ (2 * m + 1) * z : ℤ) : ℝ) := by
      have : (ℓ : ℝ) ^ ((m + 1) ^ 2) = (ℓ : ℝ) ^ (m ^ 2) * (ℓ : ℝ) ^ (2 * m + 1) := by
        rw [← pow_add]; congr 1; ring
      unfold rr; rw [this]; push_cast; rw [← hz]; ring
    have hr1 : round ((ℓ : ℝ) ^ ((m + 1) ^ 2) * α) = (ℓ : ℤ) ^ (2 * m + 1) * z := by
      rw [hθ', round_add_intCast, round_eq_zero_iff.mpr ⟨hy'.1.le, hy'.2⟩, zero_add]
    have e1 : rr ℓ α (m + 1) =
        (ℓ : ℝ) ^ ((m + 1) ^ 2) * α - round ((ℓ : ℝ) ^ ((m + 1) ^ 2) * α) := rfl
    rw [e1, hr1, hθ']
    push_cast
    ring
  have hclosed : ∀ j, rr ℓ α (m₂ + j) * (ℓ : ℝ) ^ (m₂ ^ 2) = (ℓ : ℝ) ^ ((m₂ + j) ^ 2) * rr ℓ α m₂ := by
    intro j
    induction j with
    | zero => simp [mul_comm]
    | succ j ih =>
      have h1 := hrec (m₂ + j) (by omega)
      have e : m₂ + (j + 1) = (m₂ + j) + 1 := by ring
      rw [e, h1]
      have hp : (ℓ : ℝ) ^ (((m₂ + j) + 1) ^ 2) =
          (ℓ : ℝ) ^ ((m₂ + j) ^ 2) * (ℓ : ℝ) ^ (2 * (m₂ + j) + 1) := by
        rw [← pow_add]; congr 1; ring
      rw [hp]
      calc (ℓ : ℝ) ^ (2 * (m₂ + j) + 1) * rr ℓ α (m₂ + j) * (ℓ : ℝ) ^ (m₂ ^ 2)
          = (ℓ : ℝ) ^ (2 * (m₂ + j) + 1) * (rr ℓ α (m₂ + j) * (ℓ : ℝ) ^ (m₂ ^ 2)) := by ring
        _ = (ℓ : ℝ) ^ (2 * (m₂ + j) + 1) * ((ℓ : ℝ) ^ ((m₂ + j) ^ 2) * rr ℓ α m₂) := by rw [ih]
        _ = (ℓ : ℝ) ^ ((m₂ + j) ^ 2) * (ℓ : ℝ) ^ (2 * (m₂ + j) + 1) * rr ℓ α m₂ := by ring
  have hbound : ∀ j, |rr ℓ α (m₂ + j)| ≤ 1 / 4 := by
    intro j
    have h2 := step2 (m₂ + j) (by omega)
    obtain ⟨_, hW1⟩ := Wm_ge ℓ δ' (m₂ + j) (hm₁ _ (by omega))
    have hW : (1 : ℝ) ≤ Wm ℓ δ' (m₂ + j) := by exact_mod_cast hW1
    refine h2.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hr0 : rr ℓ α m₂ = 0 := by
    by_contra hne
    have hpos : 0 < |rr ℓ α m₂| := abs_pos.mpr hne
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((ℓ : ℝ) ^ (m₂ ^ 2) / (4 * |rr ℓ α m₂|))
      (by norm_num : (1 : ℝ) < 2)
    have h2j : (2 : ℝ) ^ j ≤ (ℓ : ℝ) ^ ((m₂ + j) ^ 2) :=
      calc (2 : ℝ) ^ j ≤ 2 ^ ((m₂ + j) ^ 2) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
        _ ≤ (ℓ : ℝ) ^ ((m₂ + j) ^ 2) := pow_le_pow_left₀ (by norm_num) hℓ1 _
    have hcl := hclosed j
    have hb := hbound j
    have habs : |rr ℓ α (m₂ + j)| * (ℓ : ℝ) ^ (m₂ ^ 2) = (ℓ : ℝ) ^ ((m₂ + j) ^ 2) * |rr ℓ α m₂| := by
      have := congrArg abs hcl
      rw [abs_mul, abs_mul, abs_of_pos (pow_pos hℓ0 (m₂ ^ 2)), abs_of_pos (pow_pos hℓ0 ((m₂ + j) ^ 2))] at this
      exact this
    rw [div_lt_iff₀ (by positivity)] at hj
    have h5 := mul_le_mul_of_nonneg_right h2j hpos.le
    have h6 := mul_le_mul_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ (ℓ : ℝ) ^ (m₂ ^ 2))
    nlinarith
  refine ⟨m₂, round ((ℓ : ℝ) ^ (m₂ ^ 2) * α), ?_⟩
  have := hr0
  unfold rr at this
  linarith

/-- A parameter that is continuous for both `P_2` and `P_3` is an integer. -/
theorem oneprime_two_three (α δ₂ δ₃ : ℝ) (h₂δ : 0 < δ₂) (h₃δ : 0 < δ₃)
    (h₂ : ∀ k : ℤ, Pn (sqScales 2) k < δ₂ → nrm ((k : ℝ) * α) < 1 / 4)
    (h₃ : ∀ k : ℤ, Pn (sqScales 3) k < δ₃ → nrm ((k : ℝ) * α) < 1 / 4) :
    ∃ z : ℤ, α = z := by
  obtain ⟨a, z₂, h2⟩ := oneprime 2 le_rfl α δ₂ h₂δ h₂
  obtain ⟨b, z₃, h3⟩ := oneprime 3 (by norm_num) α δ₃ h₃δ h₃
  have hc : IsCoprime ((2 : ℤ) ^ (a ^ 2)) ((3 : ℤ) ^ (b ^ 2)) :=
    IsCoprime.pow (⟨-1, 1, by norm_num⟩ : IsCoprime (2 : ℤ) 3)
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨u * z₂ + v * z₃, ?_⟩
  have h2' : (2 : ℝ) ^ (a ^ 2) * α = z₂ := by simpa using h2
  have h3' : (3 : ℝ) ^ (b ^ 2) * α = z₃ := by simpa using h3
  have huv' : (u : ℝ) * (2 : ℝ) ^ (a ^ 2) + (v : ℝ) * (3 : ℝ) ^ (b ^ 2) = 1 := by exact_mod_cast huv
  push_cast
  linear_combination (-(α)) * huv' + (u : ℝ) * h2' + (v : ℝ) * h3'

#print axioms step1
#print axioms oneprime
#print axioms oneprime_two_three


end JAOnePrime
end LeanCheck
