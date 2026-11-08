import LeanCheck.JAOnePrime
import LeanCheck.DD3GenHeights
import LeanCheck.DD3GenPn

/-!
# The one-prime theorem for general exponent chains (Lean check)

Scope. The one-prime theorem (`JAOnePrime.oneprime`) for the scale sets `{ℓ^(f n) : n ≥ 1}` of a strictly increasing exponent
sequence `f` whose consecutive scale ratios tend to infinity (`DD3Gen.ratio_to_infty`, available under the gap hypothesis
`GapE`): if `k ↦ e(kα)` is continuous at `0` for the pseudo-norm `P_ℓ(k) = sup_n ‖k / ℓ^(f n)‖`, then `ℓ^(f a) α ∈ ℤ` for
some `a`. In the square case `f n = n²` the increments are `r m = 2m + 1`; here the increments `r m = f (m+1) - f m` are
arbitrary, with `ℓ^(f (m+1)) = ℓ^(f m) ℓ^(r m)`.

* `geom_f`: `∑_{m<n} ℓ^(f (m+1)) ≤ 2 ℓ^(f n) - 1` (each ratio is at least `2`);
* `step1_f`: combinations `∑ ℓ^(f m) w_m` with `|w_m| < δ' ℓ^(r m)` have `P_ℓ ≤ 2 δ'`;
* `oneprime_f`: the theorem for an abstract `f, r` with `ratio` hypothesis;
* `oneprimeE`: the theorem for the scale sets `scalesE E ℓ` under `StrictMono (E ℓ)` and `GapE ℓ (E ℓ)`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open MixedPrime Finset JAOnePrime DD3Sorted

/-- The scale set `{ℓ^(f n) : n ≥ 1}`. -/
def fsc (ℓ : ℕ) (f : ℕ → ℕ) : Set ℕ := {q | ∃ n : ℕ, 1 ≤ n ∧ q = ℓ ^ f n}

lemma scalesE_eq_fsc (E : ℕ → ℕ → ℕ) (p : ℕ) : scalesE E p = fsc p (E p) := rfl

lemma geom_f (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (f r : ℕ → ℕ) (hfr : ∀ m, f (m + 1) = f m + r m)
    (hr1 : ∀ m, 1 ≤ r m) (n : ℕ) :
    ∑ m ∈ Finset.range n, (ℓ : ℝ) ^ (f (m + 1)) ≤ 2 * (ℓ : ℝ) ^ (f n) - 1 := by
  have hℓ' : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  induction n with
  | zero =>
    rw [Finset.sum_range_zero]
    have : (1 : ℝ) ≤ (ℓ : ℝ) ^ (f 0) := one_le_pow₀ (by linarith)
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : (ℓ : ℝ) ^ (f (n + 1)) = (ℓ : ℝ) ^ (f n) * (ℓ : ℝ) ^ (r n) := by
      rw [hfr n, pow_add]
    have h2 : (2 : ℝ) ≤ (ℓ : ℝ) ^ (r n) := by
      calc (2 : ℝ) ≤ ℓ := hℓ'
        _ = (ℓ : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (ℓ : ℝ) ^ (r n) := pow_le_pow_right₀ (by linarith) (hr1 n)
    have h3 : 0 < (ℓ : ℝ) ^ (f n) := by positivity
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left h2 h3.le]

/-- Combinations `∑ ℓ^(f m) w_m` with `|w_m| < δ' ℓ^(r m)` have `P_ℓ ≤ 2δ'`. -/
lemma step1_f (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (f r : ℕ → ℕ) (hfr : ∀ m, f (m + 1) = f m + r m)
    (hr1 : ∀ m, 1 ≤ r m) (hmono : Monotone f) (δ' : ℝ) (hδ' : 0 ≤ δ') (F : Finset ℕ) (w : ℕ → ℤ)
    (hw : ∀ m ∈ F, |(w m : ℝ)| < δ' * (ℓ : ℝ) ^ (r m)) :
    Pn (fsc ℓ f) (∑ m ∈ F, (ℓ : ℤ) ^ (f m) * w m) ≤ 2 * δ' := by
  classical
  have hne : (fsc ℓ f).Nonempty := ⟨ℓ ^ (f 1), 1, le_rfl, rfl⟩
  apply Pn_le hne
  rintro q ⟨n, hn, rfl⟩
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  set A : ℤ := ∑ m ∈ F.filter (fun m => m < n), (ℓ : ℤ) ^ (f m) * w m with hA
  set B : ℤ := ∑ m ∈ F.filter (fun m => ¬ m < n), (ℓ : ℤ) ^ (f m) * w m with hB
  have hsplit : ∑ m ∈ F, (ℓ : ℤ) ^ (f m) * w m = A + B :=
    (Finset.sum_filter_add_sum_filter_not F _ _).symm
  obtain ⟨c, hc⟩ : ∃ c : ℤ, B = (ℓ : ℤ) ^ (f n) * c := by
    refine ⟨∑ m ∈ F.filter (fun m => ¬ m < n), (ℓ : ℤ) ^ (f m - f n) * w m, ?_⟩
    rw [hB, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hmn : n ≤ m := not_lt.mp (Finset.mem_filter.mp hm).2
    have h1 : f n ≤ f m := hmono hmn
    have h2 : (ℓ : ℤ) ^ (f m) = (ℓ : ℤ) ^ (f n) * (ℓ : ℤ) ^ (f m - f n) := by
      rw [← pow_add]; congr 1; omega
    rw [h2]; ring
  have hq : (0 : ℝ) < ((ℓ ^ (f n) : ℕ) : ℝ) := by positivity
  have hk : (((∑ m ∈ F, (ℓ : ℤ) ^ (f m) * w m : ℤ) : ℝ)) / ((ℓ ^ (f n) : ℕ) : ℝ) =
      (A : ℝ) / ((ℓ ^ (f n) : ℕ) : ℝ) + (c : ℝ) := by
    rw [hsplit, hc]; push_cast; field_simp
  rw [hk, nrm_add_int]
  refine (nrm_le_abs _).trans ?_
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
  have hterm : ∀ m ∈ F.filter (fun m => m < n),
      |((ℓ : ℤ) ^ (f m) * w m : ℤ)| ≤ δ' * (ℓ : ℝ) ^ (f (m + 1)) := by
    intro m hm
    have hmF := (Finset.mem_filter.mp hm).1
    have := hw m hmF
    have e : (ℓ : ℝ) ^ (f (m + 1)) = (ℓ : ℝ) ^ (f m) * (ℓ : ℝ) ^ (r m) := by
      rw [hfr m, pow_add]
    have hp : (0 : ℝ) < (ℓ : ℝ) ^ (f m) := by positivity
    push_cast
    rw [abs_mul, abs_of_pos hp, e]
    nlinarith
  have hAabs : |(A : ℝ)| ≤ ∑ m ∈ F.filter (fun m => m < n), δ' * (ℓ : ℝ) ^ (f (m + 1)) := by
    have h1 : |(A : ℝ)| ≤ ∑ m ∈ F.filter (fun m => m < n), |(((ℓ : ℤ) ^ (f m) * w m : ℤ) : ℝ)| := by
      rw [hA]; push_cast
      exact Finset.abs_sum_le_sum_abs _ _
    refine h1.trans (Finset.sum_le_sum (fun m hm => ?_))
    have := hterm m hm
    simpa using this
  have hsub : ∑ m ∈ F.filter (fun m => m < n), δ' * (ℓ : ℝ) ^ (f (m + 1)) ≤
      ∑ m ∈ Finset.range n, δ' * (ℓ : ℝ) ^ (f (m + 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hm).2
    · intro m _ _; positivity
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsub
  rw [← Finset.mul_sum] at hAabs
  have hg := geom_f ℓ hℓ f r hfr hr1 n
  have hpowq : ((ℓ ^ (f n) : ℕ) : ℝ) = (ℓ : ℝ) ^ (f n) := by push_cast; ring
  rw [hpowq]
  have h3 := mul_le_mul_of_nonneg_left hg hδ'
  nlinarith [h3, hAabs, hsub, hδ']

/-- The residue of `ℓ^(f m) α` modulo `ℤ`, in `[-1/2, 1/2]`. -/
noncomputable def rrf (ℓ : ℕ) (f : ℕ → ℕ) (α : ℝ) (m : ℕ) : ℝ :=
  (ℓ : ℝ) ^ (f m) * α - round ((ℓ : ℝ) ^ (f m) * α)

/-- `W_m`, the largest integer below `δ' ℓ^(r m)`. -/
noncomputable def Wf (ℓ : ℕ) (r : ℕ → ℕ) (δ' : ℝ) (m : ℕ) : ℕ := ⌈δ' * (ℓ : ℝ) ^ (r m)⌉₊ - 1

lemma Wf_lt (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (r : ℕ → ℕ) (δ' : ℝ) (hδ' : 0 < δ') (m : ℕ) :
    (Wf ℓ r δ' m : ℝ) < δ' * (ℓ : ℝ) ^ (r m) := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hx : 0 < δ' * (ℓ : ℝ) ^ (r m) := by positivity
  have h1 : 1 ≤ ⌈δ' * (ℓ : ℝ) ^ (r m)⌉₊ := Nat.ceil_pos.mpr hx
  have h2 := Nat.ceil_lt_add_one hx.le
  unfold Wf
  rw [Nat.cast_sub h1]
  push_cast
  linarith

lemma Wf_ge (ℓ : ℕ) (r : ℕ → ℕ) (δ' : ℝ) (m : ℕ) (hx : 2 ≤ δ' * (ℓ : ℝ) ^ (r m)) :
    δ' * (ℓ : ℝ) ^ (r m) / 2 ≤ (Wf ℓ r δ' m : ℝ) ∧ 1 ≤ Wf ℓ r δ' m := by
  have h1 : 1 ≤ ⌈δ' * (ℓ : ℝ) ^ (r m)⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have h2 := Nat.le_ceil (δ' * (ℓ : ℝ) ^ (r m))
  have e : (Wf ℓ r δ' m : ℝ) = (⌈δ' * (ℓ : ℝ) ^ (r m)⌉₊ : ℝ) - 1 := by
    unfold Wf; rw [Nat.cast_sub h1]; simp
  refine ⟨by rw [e]; linarith, ?_⟩
  have : (1 : ℝ) ≤ (Wf ℓ r δ' m : ℝ) := by rw [e]; linarith
  exact_mod_cast this

lemma exists_m1_f (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (f r : ℕ → ℕ) (hfr : ∀ m, f (m + 1) = f m + r m)
    (hratio : ∀ K : ℕ, ∃ J, ∀ j, J ≤ j → K * ℓ ^ (f j) < ℓ ^ (f (j + 1)))
    (δ' : ℝ) (hδ' : 0 < δ') :
    ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → 2 ≤ δ' * (ℓ : ℝ) ^ (r m) := by
  obtain ⟨J, hJ⟩ := hratio ⌈2 / δ'⌉₊
  refine ⟨J, fun m hm => ?_⟩
  have h := hJ m hm
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hp : (0 : ℝ) < (ℓ : ℝ) ^ (f m) := by positivity
  rw [hfr m, pow_add] at h
  have h' : ((⌈2 / δ'⌉₊ : ℕ) : ℝ) * (ℓ : ℝ) ^ (f m) < (ℓ : ℝ) ^ (f m) * (ℓ : ℝ) ^ (r m) := by
    exact_mod_cast h
  rw [mul_comm] at h'
  have h'' : ((⌈2 / δ'⌉₊ : ℕ) : ℝ) < (ℓ : ℝ) ^ (r m) := lt_of_mul_lt_mul_left h' hp.le
  have h3 : 2 / δ' < (ℓ : ℝ) ^ (r m) := lt_of_le_of_lt (Nat.le_ceil _) h''
  rw [div_lt_iff₀ hδ'] at h3
  linarith

/-- **The one-prime theorem for an abstract exponent sequence.** -/
theorem oneprime_f (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (f r : ℕ → ℕ) (hfr : ∀ m, f (m + 1) = f m + r m)
    (hr1 : ∀ m, 1 ≤ r m)
    (hratio : ∀ K : ℕ, ∃ J, ∀ j, J ≤ j → K * ℓ ^ (f j) < ℓ ^ (f (j + 1)))
    (α δ : ℝ) (hδ : 0 < δ)
    (h : ∀ k : ℤ, Pn (fsc ℓ f) k < δ → nrm ((k : ℝ) * α) < 1 / 4) :
    ∃ (j : ℕ) (z : ℤ), (ℓ : ℝ) ^ (f j) * α = z := by
  classical
  have hmono : Monotone f := monotone_nat_of_le_succ (fun n => by rw [hfr n]; omega)
  have hfge : ∀ n, n ≤ f n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have := hfr n; have := hr1 n; omega
  set δ' : ℝ := δ / 3 with hδ'def
  have hδ' : 0 < δ' := by positivity
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hℓ1 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hcomb : ∀ (F : Finset ℕ) (w : ℕ → ℤ), (∀ m ∈ F, |(w m : ℝ)| < δ' * (ℓ : ℝ) ^ (r m)) →
      nrm (((∑ m ∈ F, (ℓ : ℤ) ^ (f m) * w m : ℤ) : ℝ) * α) < 1 / 4 := by
    intro F w hw
    apply h
    have := step1_f ℓ hℓ f r hfr hr1 hmono δ' hδ'.le F w hw
    linarith
  obtain ⟨m₁, hm₁⟩ := exists_m1_f ℓ hℓ f r hfr hratio δ' hδ'
  -- Step 2: each residue is tiny
  have step2 : ∀ m, m₁ ≤ m → |rrf ℓ f α m| ≤ 1 / (4 * (Wf ℓ r δ' m : ℝ)) := by
    intro m hm
    obtain ⟨_, hW1⟩ := Wf_ge ℓ r δ' m (hm₁ m hm)
    have hWlt := Wf_lt ℓ hℓ r δ' hδ' m
    have hmult : ∀ ρ : ℕ, ρ ≤ Wf ℓ r δ' m →
        ∃ n : ℤ, |(ρ : ℝ) * ((ℓ : ℝ) ^ (f m) * α) - n| < 1 / 4 := by
      intro ρ hρ
      rcases Nat.eq_zero_or_pos ρ with rfl | hρ0
      · exact ⟨0, by norm_num⟩
      · have hlt := hcomb {m} (fun _ => (ρ : ℤ)) (by
          intro m' hm'
          rw [Finset.mem_singleton] at hm'; subst hm'
          have : (ρ : ℝ) ≤ Wf ℓ r δ' m' := by exact_mod_cast hρ
          show |((ρ : ℤ) : ℝ)| < _
          rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ρ)]
          linarith)
        rw [Finset.sum_singleton, nrm_eq] at hlt
        refine ⟨round ((((ℓ : ℤ) ^ (f m) * (ρ : ℤ) : ℤ) : ℝ) * α), ?_⟩
        have e : (((ℓ : ℤ) ^ (f m) * (ρ : ℤ) : ℤ) : ℝ) * α =
            (ρ : ℝ) * ((ℓ : ℝ) ^ (f m) * α) := by push_cast; ring
        rw [e] at hlt ⊢
        exact hlt
    obtain ⟨z, hz⟩ := near_of_all_multiples (θ := (ℓ : ℝ) ^ (f m) * α) (R := Wf ℓ r δ' m) hW1 hmult
    exact (round_le _ z).trans hz
  -- the terms `t`
  set t : ℕ → ℝ := fun i => (Wf ℓ r δ' (m₁ + i) : ℝ) * |rrf ℓ f α (m₁ + i)| with htdef
  have ht0 : ∀ i, 0 ≤ t i := fun i => by simp only [htdef]; positivity
  have ht4 : ∀ i, t i ≤ 1 / 4 := by
    intro i
    have h2 := step2 (m₁ + i) (by omega)
    obtain ⟨_, hW1⟩ := Wf_ge ℓ r δ' (m₁ + i) (hm₁ _ (by omega))
    have hW : (0 : ℝ) < Wf ℓ r δ' (m₁ + i) := Nat.cast_pos.mpr (by omega)
    simp only [htdef]
    calc (Wf ℓ r δ' (m₁ + i) : ℝ) * |rrf ℓ f α (m₁ + i)|
        ≤ (Wf ℓ r δ' (m₁ + i) : ℝ) * (1 / (4 * (Wf ℓ r δ' (m₁ + i) : ℝ))) := by gcongr
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
      set s : ℕ → ℤ := fun m => if 0 ≤ rrf ℓ f α m then 1 else -1 with hs
      set w : ℕ → ℤ := fun m => (Wf ℓ r δ' m : ℤ) * s m with hw
      set F : Finset ℕ := Finset.Ico m₁ (m₁ + (N + 1)) with hF
      have hFw : ∀ m ∈ F, |(w m : ℝ)| < δ' * (ℓ : ℝ) ^ (r m) := by
        intro m _
        have hs1 : |(s m : ℝ)| = 1 := by
          simp only [hs]; split_ifs <;> simp
        have : |(w m : ℝ)| = (Wf ℓ r δ' m : ℝ) := by
          simp only [hw]; push_cast; rw [abs_mul, hs1, mul_one]; exact abs_of_nonneg (Nat.cast_nonneg _)
        rw [this]; exact Wf_lt ℓ hℓ r δ' hδ' m
      have hlt4 := hcomb F w hFw
      have hk : ((∑ m ∈ F, (ℓ : ℤ) ^ (f m) * w m : ℤ) : ℝ) * α =
          ∑ i ∈ Finset.range (N + 1), t i +
            ((∑ m ∈ F, w m * round ((ℓ : ℝ) ^ (f m) * α) : ℤ) : ℝ) := by
        have h1 : ∀ m ∈ F, (((ℓ : ℤ) ^ (f m) * w m : ℤ) : ℝ) * α =
            (Wf ℓ r δ' m : ℝ) * |rrf ℓ f α m| + ((w m * round ((ℓ : ℝ) ^ (f m) * α) : ℤ) : ℝ) := by
          intro m _
          have hsr : ((w m : ℤ) : ℝ) * rrf ℓ f α m = (Wf ℓ r δ' m : ℝ) * |rrf ℓ f α m| := by
            simp only [hw, hs]
            by_cases h0 : 0 ≤ rrf ℓ f α m
            · simp [h0, abs_of_nonneg h0]
            · push Not at h0
              simp [not_le.mpr h0, abs_of_neg h0]
          have hrr : (ℓ : ℝ) ^ (f m) * α = rrf ℓ f α m + round ((ℓ : ℝ) ^ (f m) * α) := by
            unfold rrf; ring
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
  have hsmall : ∀ m, m₂ ≤ m → (ℓ : ℝ) ^ (r m) * |rrf ℓ f α m| < 1 / 2 := by
    intro m hm
    obtain ⟨hWge, _⟩ := Wf_ge ℓ r δ' m (hm₁ m (by omega))
    have hti := hN₀ (m - m₁) (by omega)
    have e : m₁ + (m - m₁) = m := by omega
    have hti' : (Wf ℓ r δ' m : ℝ) * |rrf ℓ f α m| < δ' / 4 := by
      have : t (m - m₁) = (Wf ℓ r δ' m : ℝ) * |rrf ℓ f α m| := by simp only [htdef, e]
      rw [← this]; exact hti
    have h3 := mul_le_mul_of_nonneg_right hWge (abs_nonneg (rrf ℓ f α m))
    have h4 : δ' * ((ℓ : ℝ) ^ (r m) * |rrf ℓ f α m|) < δ' * (1 / 2) := by nlinarith
    exact lt_of_mul_lt_mul_left h4 hδ'.le
  have hrec : ∀ m, m₂ ≤ m → rrf ℓ f α (m + 1) = (ℓ : ℝ) ^ (r m) * rrf ℓ f α m := by
    intro m hm
    have hs := hsmall m hm
    have hLpos : (0 : ℝ) < (ℓ : ℝ) ^ (r m) := by positivity
    have hy : |(ℓ : ℝ) ^ (r m) * rrf ℓ f α m| < 1 / 2 := by
      rw [abs_mul, abs_of_pos hLpos]; exact hs
    have hy' := abs_lt.mp hy
    set z : ℤ := round ((ℓ : ℝ) ^ (f m) * α) with hz
    have hθ' : (ℓ : ℝ) ^ (f (m + 1)) * α =
        (ℓ : ℝ) ^ (r m) * rrf ℓ f α m + (((ℓ : ℤ) ^ (r m) * z : ℤ) : ℝ) := by
      have : (ℓ : ℝ) ^ (f (m + 1)) = (ℓ : ℝ) ^ (f m) * (ℓ : ℝ) ^ (r m) := by
        rw [hfr m, pow_add]
      unfold rrf; rw [this]; push_cast; rw [← hz]; ring
    have hr1' : round ((ℓ : ℝ) ^ (f (m + 1)) * α) = (ℓ : ℤ) ^ (r m) * z := by
      rw [hθ', round_add_intCast, round_eq_zero_iff.mpr ⟨hy'.1.le, hy'.2⟩, zero_add]
    have e1 : rrf ℓ f α (m + 1) =
        (ℓ : ℝ) ^ (f (m + 1)) * α - round ((ℓ : ℝ) ^ (f (m + 1)) * α) := rfl
    rw [e1, hr1', hθ']
    push_cast
    ring
  have hclosed : ∀ j, rrf ℓ f α (m₂ + j) * (ℓ : ℝ) ^ (f m₂) = (ℓ : ℝ) ^ (f (m₂ + j)) * rrf ℓ f α m₂ := by
    intro j
    induction j with
    | zero => simp [mul_comm]
    | succ j ih =>
      have h1 := hrec (m₂ + j) (by omega)
      have e : m₂ + (j + 1) = (m₂ + j) + 1 := by ring
      rw [e, h1]
      have hp : (ℓ : ℝ) ^ (f ((m₂ + j) + 1)) =
          (ℓ : ℝ) ^ (f (m₂ + j)) * (ℓ : ℝ) ^ (r (m₂ + j)) := by
        rw [hfr (m₂ + j), pow_add]
      rw [hp]
      calc (ℓ : ℝ) ^ (r (m₂ + j)) * rrf ℓ f α (m₂ + j) * (ℓ : ℝ) ^ (f m₂)
          = (ℓ : ℝ) ^ (r (m₂ + j)) * (rrf ℓ f α (m₂ + j) * (ℓ : ℝ) ^ (f m₂)) := by ring
        _ = (ℓ : ℝ) ^ (r (m₂ + j)) * ((ℓ : ℝ) ^ (f (m₂ + j)) * rrf ℓ f α m₂) := by rw [ih]
        _ = (ℓ : ℝ) ^ (f (m₂ + j)) * (ℓ : ℝ) ^ (r (m₂ + j)) * rrf ℓ f α m₂ := by ring
  have hbound : ∀ j, |rrf ℓ f α (m₂ + j)| ≤ 1 / 4 := by
    intro j
    have h2 := step2 (m₂ + j) (by omega)
    obtain ⟨_, hW1⟩ := Wf_ge ℓ r δ' (m₂ + j) (hm₁ _ (by omega))
    have hW : (1 : ℝ) ≤ Wf ℓ r δ' (m₂ + j) := by exact_mod_cast hW1
    refine h2.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hr0 : rrf ℓ f α m₂ = 0 := by
    by_contra hne
    have hpos : 0 < |rrf ℓ f α m₂| := abs_pos.mpr hne
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((ℓ : ℝ) ^ (f m₂) / (4 * |rrf ℓ f α m₂|))
      (by norm_num : (1 : ℝ) < 2)
    have hjf : j ≤ f (m₂ + j) := le_trans (by omega : j ≤ m₂ + j) (hfge _)
    have h2j : (2 : ℝ) ^ j ≤ (ℓ : ℝ) ^ (f (m₂ + j)) :=
      calc (2 : ℝ) ^ j ≤ 2 ^ (f (m₂ + j)) := pow_le_pow_right₀ (by norm_num) hjf
        _ ≤ (ℓ : ℝ) ^ (f (m₂ + j)) := pow_le_pow_left₀ (by norm_num) hℓ1 _
    have hcl := hclosed j
    have hb := hbound j
    have habs : |rrf ℓ f α (m₂ + j)| * (ℓ : ℝ) ^ (f m₂) = (ℓ : ℝ) ^ (f (m₂ + j)) * |rrf ℓ f α m₂| := by
      have := congrArg abs hcl
      rw [abs_mul, abs_mul, abs_of_pos (pow_pos hℓ0 (f m₂)), abs_of_pos (pow_pos hℓ0 (f (m₂ + j)))] at this
      exact this
    rw [div_lt_iff₀ (by positivity)] at hj
    have h5 := mul_le_mul_of_nonneg_right h2j hpos.le
    have h6 := mul_le_mul_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ (ℓ : ℝ) ^ (f m₂))
    nlinarith
  refine ⟨m₂, round ((ℓ : ℝ) ^ (f m₂) * α), ?_⟩
  have := hr0
  unfold rrf at this
  linarith

/-- **The one-prime theorem for the scale set `{ℓ^(E ℓ n)}`** under the gap hypothesis. -/
theorem oneprimeE (E : ℕ → ℕ → ℕ) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (he : StrictMono (E ℓ)) (hg : GapE ℓ (E ℓ))
    (α δ : ℝ) (hδ : 0 < δ)
    (h : ∀ k : ℤ, Pn (scalesE E ℓ) k < δ → nrm ((k : ℝ) * α) < 1 / 4) :
    ∃ (a : ℕ) (z : ℤ), (ℓ : ℝ) ^ (E ℓ a) * α = z := by
  refine oneprime_f ℓ hℓ (E ℓ) (fun m => E ℓ (m + 1) - E ℓ m) ?_ ?_ ?_ α δ hδ h
  · intro m
    have := he (Nat.lt_add_one m)
    show E ℓ (m + 1) = E ℓ m + (E ℓ (m + 1) - E ℓ m)
    omega
  · intro m
    have := he (Nat.lt_add_one m)
    show 1 ≤ E ℓ (m + 1) - E ℓ m
    omega
  · exact fun K => ratio_to_infty hℓ he hg K

#print axioms oneprime_f
#print axioms oneprimeE

end DD3Gen
end LeanCheck
