import LeanCheck.ThreePrimesTheoremBM3

/-!
# ThreePrimes (version M5): the exact counting bound (Theorem 3.2 of ThreePrimes_v8)

For integers `a_p ≥ 0`, `D = ∏ p^(a_p²)`, `m` with `m δ ≥ 1` and a natural number `N`, let
`CCset S a m N = {(p,n) : p ∈ S, n > a_p, p^(n²) ≤ m D N}` (the retained coordinates).
If `m ^ |CCset| ≤ N`, the pigeonhole on the multiples `D x`, `0 ≤ x ≤ N` gives `k` with
`1 ≤ k ≤ D N`, `D ∣ k` and `P_S(k) < δ` (`exact_pigeonM5`). With `N = m^c` this is the form
`C(c) ≤ c ⇒ u_S(δ) ≤ D m^c` (`exact_upper_cM5`); `c*` is the least such `c` (`cstarM5`, `sInf`).

Comparison with Theorem B (`ThreePrimesTheoremBM3`): `exact_le_multM5` shows, under the sufficient
condition `hcond` of `explicit_upper_multM3`, that `c₁ = ⌊M/η⌋` satisfies `m^c₁ ≤ 2^M` and
`|CCset S a m (m^c₁)| ≤ c₁` (the retained set is contained in `retSet`, the retained set of M3);
`hcond_MstarR` is the `hcond` of `explicit_upper_BM3` as a lemma; `exists_cM5` gives the existence of
`c`; `exact_bounds_BM5` is Theorem 3.2 for the forced exponents `a_p = a_p(δ)`:
`D_S(δ) ≤ k ≤ D_S(δ) m^(c*)`, `P_S(k) < δ`, `m^(c*) ≤ 2^M` with `M = MstarR S a (log₂ m)`.
Not formalised: the iteration `c_{j+1} = C(c_j)` converging to `c*` and the remarks of the article.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- `D = ∏ p^(a_p²)`. -/
def Dprod (S : Finset ℕ) (a : ℕ → ℕ) : ℕ := ∏ p ∈ S, p ^ (a p ^ 2)

/-- The retained coordinates `{(p,n) : n > a_p, p^(n²) ≤ m D N}`; `n ≤ D N m` is automatic. -/
def CCset (S : Finset ℕ) (a : ℕ → ℕ) (m N : ℕ) : Finset (ℕ × ℕ) :=
  (S ×ˢ Finset.range (Dprod S a * N * m + 1)).filter
    (fun c => a c.1 < c.2 ∧ c.1 ^ (c.2 ^ 2) ≤ m * Dprod S a * N)

lemma n_lt_pow_sq {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : n < p ^ (n ^ 2) := by
  have h1 : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  have h2 : n ^ 2 < p ^ (n ^ 2) := Nat.lt_pow_self (by omega)
  omega

lemma mem_ccset {S : Finset ℕ} {a : ℕ → ℕ} {m N p n : ℕ} (hp2 : 2 ≤ p) (hp : p ∈ S)
    (han : a p < n) (hq : p ^ (n ^ 2) ≤ m * Dprod S a * N) : (p, n) ∈ CCset S a m N := by
  unfold CCset
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨hp, ?_⟩, han, hq⟩
  rw [Finset.mem_range]
  have h1 : n < m * Dprod S a * N := lt_of_lt_of_le (n_lt_pow_sq hp2 n) hq
  have e : m * Dprod S a * N = Dprod S a * N * m := by ring
  rw [e] at h1
  exact Nat.lt_succ_of_lt h1

lemma ccset_mono {S : Finset ℕ} {a : ℕ → ℕ} {m N N' : ℕ} (h : N ≤ N') :
    CCset S a m N ⊆ CCset S a m N' := by
  intro c hc
  unfold CCset at hc ⊢
  rw [Finset.mem_filter, Finset.mem_product] at hc ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hc
  refine ⟨⟨h1, ?_⟩, h3, ?_⟩
  · rw [Finset.mem_range] at h2 ⊢
    have : Dprod S a * N * m ≤ Dprod S a * N' * m := by gcongr
    omega
  · calc c.1 ^ (c.2 ^ 2) ≤ m * Dprod S a * N := h4
      _ ≤ m * Dprod S a * N' := by gcongr

/-- **Exact pigeonhole bound.** If `m ^ |CCset S a m N| ≤ N` there is `k`, `1 ≤ k ≤ D N`, `D ∣ k`,
with `P_S(k) < δ`. -/
theorem exact_pigeonM5 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (m N : ℕ) (a : ℕ → ℕ) (hm : 1 ≤ (m : ℝ) * δ)
    (hcount : m ^ (CCset S a m N).card ≤ N) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ (Dprod S a : ℤ) * (N : ℤ) ∧ ((Dprod S a : ℤ) ∣ k) ∧ InBall S δ k := by
  classical
  set D : ℕ := Dprod S a with hDdef
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    have hm' : (m : ℝ) = 0 := by exact_mod_cast this
    rw [hm'] at hm
    norm_num at hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hDpos : 0 < D := by
    rw [hDdef]; unfold Dprod
    apply Finset.prod_pos
    intro p hp
    have := hS p hp
    positivity
  have hN1 : 1 ≤ N := le_trans (Nat.one_le_pow _ _ hm1) hcount
  set C : Finset (ℕ × ℕ) := CCset S a m N with hC
  have hCpos : ∀ c ∈ C, 0 < c.1 ^ (c.2 ^ 2) := by
    intro c hc
    rw [hC] at hc
    unfold CCset at hc
    rw [Finset.mem_filter, Finset.mem_product] at hc
    obtain ⟨⟨hp, _⟩, _, _⟩ := hc
    have := hS c.1 hp
    positivity
  obtain ⟨k, hk1, hkN, hkD, hk⟩ := pigeonhole_box_mul C hCpos m N D hm1 hDpos hcount
  refine ⟨k, hk1, hkN, hkD, ?_⟩
  intro p hp
  have hp2 := hS p hp
  have hhalf : 1 / (m : ℝ) ≤ δ := by
    rw [div_le_iff₀ hm0]
    linarith
  have hNpos : (0 : ℝ) < ((D * N : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hDpos hN1
  have hB : ((D * N : ℕ) : ℝ) / (((D * N : ℕ) : ℝ) * m + 1) < 1 / (m : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hm0]
    nlinarith
  -- the tail estimate: `D N m + 1 ≤ q` gives `‖k/q‖ ≤ D N / (D N m + 1)`
  have tailest : ∀ n : ℕ, D * N * m + 1 ≤ p ^ (n ^ 2) →
      nrm ((k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) ≤
        ((D * N : ℕ) : ℝ) / (((D * N : ℕ) : ℝ) * m + 1) := by
    intro n hn
    have hNm1 : ((D * N : ℕ) : ℝ) * m + 1 ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by
      have h6 : ((D * N * m + 1 : ℕ) : ℝ) ≤ ((p ^ (n ^ 2) : ℕ) : ℝ) := by exact_mod_cast hn
      push_cast at h6 ⊢
      exact h6
    have hqpos : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
      exact_mod_cast pow_pos (by omega : 0 < p) _
    refine (nrm_le_abs _).trans ?_
    rw [abs_div, abs_of_pos hqpos]
    have hkabs : |(k : ℝ)| ≤ ((D * N : ℕ) : ℝ) := by
      rw [abs_of_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ k))]
      have : (k : ℝ) ≤ (((D : ℤ) * (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast hkN
      push_cast at this ⊢
      exact this
    calc |(k : ℝ)| / ((p ^ (n ^ 2) : ℕ) : ℝ) ≤ ((D * N : ℕ) : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) := by
          gcongr
      _ ≤ ((D * N : ℕ) : ℝ) / (((D * N : ℕ) : ℝ) * m + 1) := by
          gcongr
  have hfin : ∀ n : ℕ, 1 ≤ n → n ≤ D * N * m →
      nrm ((k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) < 1 / (m : ℝ) := by
    intro n hn hnR
    by_cases han : n ≤ a p
    · -- the coordinate divides D, hence k
      have hdvd1 : p ^ (n ^ 2) ∣ D := by
        calc p ^ (n ^ 2) ∣ p ^ (a p ^ 2) := pow_dvd_pow p (Nat.pow_le_pow_left han 2)
          _ ∣ D := Finset.dvd_prod_of_mem (fun p => p ^ (a p ^ 2)) hp
      have hdvd : ((p ^ (n ^ 2) : ℕ) : ℤ) ∣ k :=
        dvd_trans (Int.natCast_dvd_natCast.mpr hdvd1) hkD
      obtain ⟨z, hz⟩ := hdvd
      have hqpos : (0 : ℝ) < ((p ^ (n ^ 2) : ℕ) : ℝ) := by
        exact_mod_cast pow_pos (by omega : 0 < p) _
      have hkz : (k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ) = (z : ℝ) := by
        rw [hz]
        push_cast
        field_simp
      rw [hkz, nrm_int]
      positivity
    · push_neg at han
      by_cases hq : p ^ (n ^ 2) ≤ m * D * N
      · exact hk (p, n) (mem_ccset hp2 hp han hq)
      · push_neg at hq
        have e : m * D * N = D * N * m := by ring
        rw [e] at hq
        exact lt_of_le_of_lt (tailest n hq) hB
  have htail : ∀ n : ℕ, D * N * m < n →
      nrm ((k : ℝ) / ((p ^ (n ^ 2) : ℕ) : ℝ)) ≤
        ((D * N : ℕ) : ℝ) / (((D * N : ℕ) : ℝ) * m + 1) := by
    intro n hn
    apply tailest
    have := n_lt_pow_sq hp2 n
    omega
  have hlt := Pn_sq_lt p k (D * N * m) hB hfin htail
  exact lt_of_lt_of_le hlt hhalf

/-- **The `c`-form.** If `|CCset S a m (m^c)| ≤ c` there is `k`, `1 ≤ k ≤ D m^c`, `D ∣ k`, `P_S(k) < δ`. -/
theorem exact_upper_cM5 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {δ : ℝ} (hδ : 0 < δ)
    (m : ℕ) (a : ℕ → ℕ) (hm : 1 ≤ (m : ℝ) * δ) (c : ℕ)
    (hc : (CCset S a m (m ^ c)).card ≤ c) :
    ∃ k : ℤ, 1 ≤ k ∧ k ≤ (Dprod S a : ℤ) * ((m ^ c : ℕ) : ℤ) ∧ ((Dprod S a : ℤ) ∣ k) ∧ InBall S δ k := by
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    have hm' : (m : ℝ) = 0 := by exact_mod_cast this
    rw [hm'] at hm
    norm_num at hm
  exact exact_pigeonM5 hS hδ m (m ^ c) a hm (Nat.pow_le_pow_right hm1 hc)


/-- The retained set of `ThreePrimesTheoremBM3`: `⋃ Ioc (a p) ⌊√(Λ/log₂p)⌋`. -/
noncomputable def retSet (S : Finset ℕ) (a : ℕ → ℕ) (Λ : ℝ) : Finset (ℕ × ℕ) :=
  S.biUnion (fun p => (Finset.Ioc (a p) ⌊Real.sqrt (Λ / Real.logb 2 (p : ℝ))⌋₊).image (fun n => (p, n)))

lemma card_retained_le {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hσa : ∀ p ∈ S, (a p : ℝ) ≤ Real.sqrt (Λ / Real.logb 2 (p : ℝ))) :
    ((retSet S a Λ).card : ℝ)
      ≤ Real.sqrt Λ * (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ) := by
  classical
  have h1 : (retSet S a Λ).card ≤ ∑ p ∈ S, (⌊Real.sqrt (Λ / Real.logb 2 (p : ℝ))⌋₊ - a p) := by
    unfold retSet
    calc _ ≤ ∑ p ∈ S, ((Finset.Ioc (a p) ⌊Real.sqrt (Λ / Real.logb 2 (p : ℝ))⌋₊).image
              (fun n => (p, n))).card := Finset.card_biUnion_le
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p _
        calc _ ≤ (Finset.Ioc (a p) ⌊Real.sqrt (Λ / Real.logb 2 (p : ℝ))⌋₊).card :=
              Finset.card_image_le
          _ = _ := by simp
  have h2 : ((∑ p ∈ S, (⌊Real.sqrt (Λ / Real.logb 2 (p : ℝ))⌋₊ - a p) : ℕ) : ℝ)
      ≤ ∑ p ∈ S, (Real.sqrt (Λ / Real.logb 2 (p : ℝ)) - a p) := by
    push_cast
    apply Finset.sum_le_sum
    intro p hp
    have hle : a p ≤ ⌊Real.sqrt (Λ / Real.logb 2 (p : ℝ))⌋₊ := Nat.le_floor (hσa p hp)
    rw [Nat.cast_sub hle]
    have := Nat.floor_le (Real.sqrt_nonneg (Λ / Real.logb 2 (p : ℝ)))
    linarith
  have h3 : ∑ p ∈ S, (Real.sqrt (Λ / Real.logb 2 (p : ℝ)) - a p)
      = Real.sqrt Λ * (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [div_eq_mul_one_div, Real.sqrt_mul hΛ0]
  calc ((retSet S a Λ).card : ℝ) ≤ ((∑ p ∈ S, (⌊Real.sqrt (Λ / Real.logb 2 (p : ℝ))⌋₊ - a p) : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ ≤ _ := h2
    _ = _ := h3

/-- `a_p ≤ √(Λ / log₂ p)` for `Λ = Δ + M + η`, `η ≥ 0`. -/
lemma a_le_sigma {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (M : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    ∀ p ∈ S, (a p : ℝ) ≤ Real.sqrt (((∑ q ∈ S, (a q : ℝ) ^ 2 * Real.logb 2 (q : ℝ)) + M + η)
      / Real.logb 2 (p : ℝ)) := by
  intro p hp
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb' (hS p hp)
  have hlbp := hlb p hp
  have hlpos : 0 < Real.logb 2 (p : ℝ) := by linarith
  have h1 : (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ) ≤ ∑ q ∈ S, (a q : ℝ) ^ 2 * Real.logb 2 (q : ℝ) :=
    Finset.single_le_sum (f := fun p => (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ))
      (fun q hq => by have := hlb q hq; positivity) hp
  have h2 : (a p : ℝ) ^ 2 ≤ (((∑ q ∈ S, (a q : ℝ) ^ 2 * Real.logb 2 (q : ℝ)) + M + η)
      / Real.logb 2 (p : ℝ)) := by
    rw [le_div_iff₀ hlpos]
    linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  calc (a p : ℝ) = Real.sqrt ((a p : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h2

/-- The retained set for `N = 2^M` lies in the set `retSet` with `Λ = Δ + M + η`. -/
lemma ccset_sub_ret {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (a : ℕ → ℕ) (m M : ℕ) (η : ℝ)
    (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) :
    CCset S a m (2 ^ M) ⊆
      retSet S a ((∑ q ∈ S, (a q : ℝ) ^ 2 * Real.logb 2 (q : ℝ)) + M + η) := by
  classical
  intro c hc
  obtain ⟨p, n⟩ := c
  unfold CCset at hc
  rw [Finset.mem_filter, Finset.mem_product] at hc
  obtain ⟨⟨hp, _⟩, han, hq⟩ := hc
  simp only at han hq hp
  have hp2 := hS p hp
  have hlb : 1 ≤ Real.logb 2 (p : ℝ) := one_le_logb' hp2
  have hlpos : 0 < Real.logb 2 (p : ℝ) := by linarith
  set Δ : ℝ := ∑ q ∈ S, (a q : ℝ) ^ 2 * Real.logb 2 (q : ℝ) with hΔ
  have hDpos : 0 < Dprod S a := by
    unfold Dprod
    apply Finset.prod_pos
    intro p hp
    have := hS p hp
    positivity
  have hDpos' : (0 : ℝ) < (Dprod S a : ℝ) := by exact_mod_cast hDpos
  have hqR : (((p ^ (n ^ 2) : ℕ)) : ℝ) ≤ (m : ℝ) * (Dprod S a : ℝ) * (2 : ℝ) ^ M := by
    exact_mod_cast hq
  have hmD : (m : ℝ) * (Dprod S a : ℝ) * (2 : ℝ) ^ M ≤ (Dprod S a : ℝ) * (2 : ℝ) ^ ((M : ℝ) + η) := by
    calc (m : ℝ) * (Dprod S a : ℝ) * (2 : ℝ) ^ M ≤ (2 : ℝ) ^ η * (Dprod S a : ℝ) * (2 : ℝ) ^ M := by
          gcongr
      _ = (Dprod S a : ℝ) * (2 : ℝ) ^ ((M : ℝ) + η) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_natCast]; ring
  have hp0 : (0 : ℝ) < (((p ^ (n ^ 2) : ℕ)) : ℝ) := by
    exact_mod_cast pow_pos (by omega : 0 < p) _
  have h1 : Real.logb 2 (((p ^ (n ^ 2) : ℕ)) : ℝ)
      ≤ Real.logb 2 ((Dprod S a : ℝ) * (2 : ℝ) ^ ((M : ℝ) + η)) :=
    Real.logb_le_logb_of_le (by norm_num) hp0 (hqR.trans hmD)
  have h2 : Real.logb 2 (((p ^ (n ^ 2) : ℕ)) : ℝ) = (n : ℝ) ^ 2 * Real.logb 2 (p : ℝ) := by
    push_cast
    rw [Real.logb_pow]
    push_cast
    ring
  have h3 : Real.logb 2 ((Dprod S a : ℝ) * (2 : ℝ) ^ ((M : ℝ) + η)) = Δ + ((M : ℝ) + η) := by
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_rpow (by norm_num) (by norm_num)]
    have : Real.logb 2 (Dprod S a : ℝ) = Δ := by
      unfold Dprod
      exact logb_D hS a
    rw [this]
  rw [h2, h3] at h1
  unfold retSet
  rw [Finset.mem_biUnion]
  refine ⟨p, hp, Finset.mem_image.mpr ⟨n, Finset.mem_Ioc.mpr ⟨han, ?_⟩, rfl⟩⟩
  apply Nat.le_floor
  have h4 : (n : ℝ) ^ 2 ≤ (Δ + (M : ℝ) + η) / Real.logb 2 (p : ℝ) := by
    rw [le_div_iff₀ hlpos]
    linarith
  calc (n : ℝ) = Real.sqrt ((n : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h4

/-- **Comparison with Theorem B.** Under the hypotheses of `explicit_upper_multM3` (`hcond`), with
`c₁ = ⌊M/η⌋`: `m^c₁ ≤ 2^M` and `|CCset S a m (m^c₁)| ≤ c₁`. -/
theorem exact_le_multM5 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (m M : ℕ) (η : ℝ) (a : ℕ → ℕ)
    (hm1 : 1 ≤ m) (hmh : (m : ℝ) ≤ (2 : ℝ) ^ η) (hη : 0 < η)
    (hcond : η * (Real.sqrt ((∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ)) + M + η) *
        (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ)) ≤ M) :
    m ^ ⌊(M : ℝ) / η⌋₊ ≤ 2 ^ M ∧ (CCset S a m (m ^ ⌊(M : ℝ) / η⌋₊)).card ≤ ⌊(M : ℝ) / η⌋₊ := by
  classical
  set c1 : ℕ := ⌊(M : ℝ) / η⌋₊ with hc1
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hc1le : (c1 : ℝ) ≤ (M : ℝ) / η := Nat.floor_le (by positivity)
  have hηc : η * c1 ≤ M := by
    have := (le_div_iff₀ hη).mp hc1le
    linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hpow : m ^ c1 ≤ 2 ^ M := by
    have hR : (m : ℝ) ^ c1 ≤ ((2 ^ M : ℕ) : ℝ) := by
      calc (m : ℝ) ^ c1 ≤ ((2 : ℝ) ^ η) ^ c1 := pow_le_pow_left₀ hm0.le hmh _
        _ = (2 : ℝ) ^ (η * c1) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        _ ≤ (2 : ℝ) ^ (M : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hηc
        _ = ((2 ^ M : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
    exact_mod_cast hR
  refine ⟨hpow, ?_⟩
  set Λ : ℝ := (∑ q ∈ S, (a q : ℝ) ^ 2 * Real.logb 2 (q : ℝ)) + M + η with hΛ
  have hΔ0 : 0 ≤ ∑ q ∈ S, (a q : ℝ) ^ 2 * Real.logb 2 (q : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    have := one_le_logb' (hS p hp)
    positivity
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; linarith
  have hsub : CCset S a m (m ^ c1) ⊆ retSet S a Λ :=
    (ccset_mono hpow).trans (ccset_sub_ret hS a m M η hmh)
  have hcard1 : (CCset S a m (m ^ c1)).card ≤ (retSet S a Λ).card := Finset.card_le_card hsub
  have hret := card_retained_le hS a hΛ0 (a_le_sigma hS a M hη.le)
  have hX : ((retSet S a Λ).card : ℝ) ≤ (M : ℝ) / η := by
    rw [le_div_iff₀ hη]
    have : η * ((retSet S a Λ).card : ℝ) ≤ η * (Real.sqrt Λ *
        (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ)) :=
      mul_le_mul_of_nonneg_left hret hη.le
    linarith
  have hfl : (retSet S a Λ).card ≤ c1 := Nat.le_floor hX
  exact hcard1.trans hfl

/-- The sufficient condition `hcond` holds for `M = ⌈t*² − η − Δ⌉` (as in `explicit_upper_BM3`). -/
lemma hcond_MstarR {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) (a : ℕ → ℕ) (η : ℝ)
    (hη : 0 ≤ η) :
    η * (Real.sqrt ((∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ)) + (MstarR S a η : ℕ) + η) *
        (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ))
      ≤ ((MstarR S a η : ℕ) : ℝ) := by
  have hQ := discQR_nonneg hS hne a η hη
  have hlb : ∀ p ∈ S, 1 ≤ Real.logb 2 (p : ℝ) := fun p hp => one_le_logb' (hS p hp)
  have hA0 : 0 ≤ sumA S := Finset.sum_nonneg (fun p _ => Real.sqrt_nonneg _)
  have hΔ0 : 0 ≤ sumDelta S a := by
    apply Finset.sum_nonneg
    intro p hp
    have := hlb p hp
    positivity
  have hh0 : (0 : ℝ) ≤ η := hη
  set M := MstarR S a η with hMdef
  set t := tstarR S a η with ht
  have ht0 : 0 ≤ t := by
    rw [ht]; unfold tstarR
    have := Real.sqrt_nonneg (discQR S a η)
    positivity
  have hM : t ^ 2 - η - sumDelta S a ≤ M := Nat.le_ceil _
  have hΛ : t ^ 2 ≤ sumDelta S a + M + η := by linarith
  have hΛ0 : 0 ≤ sumDelta S a + M + η := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hx : t ≤ Real.sqrt (sumDelta S a + M + η) := by
    calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht0).symm
      _ ≤ _ := Real.sqrt_le_sqrt hΛ
  have hxsq : Real.sqrt (sumDelta S a + M + η) ^ 2 = sumDelta S a + M + η := Real.sq_sqrt hΛ0
  have hq := quad_step (A := sumA S) (α := sumAlpha S a) (Δ := sumDelta S a) (h := η) hh0 hA0 hQ
    (x := Real.sqrt (sumDelta S a + M + η)) hx
  have hqq : η * (sumA S * Real.sqrt (sumDelta S a + M + η) - sumAlpha S a)
      ≤ Real.sqrt (sumDelta S a + M + η) ^ 2 - η - sumDelta S a := hq
  rw [hxsq] at hqq
  unfold sumA sumAlpha sumDelta at hqq
  have e : η * (Real.sqrt ((∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ)) + M + η) *
        (∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) - ∑ p ∈ S, (a p : ℝ))
      = η * ((∑ p ∈ S, Real.sqrt (1 / Real.logb 2 (p : ℝ))) *
        Real.sqrt ((∑ p ∈ S, (a p : ℝ) ^ 2 * Real.logb 2 (p : ℝ)) + M + η) - ∑ p ∈ S, (a p : ℝ)) := by
    ring
  rw [e]
  linarith

/-- `c*`, the least `c` with `|CCset S a m (m^c)| ≤ c`. -/
noncomputable def cstarM5 (S : Finset ℕ) (a : ℕ → ℕ) (m : ℕ) : ℕ :=
  sInf {c : ℕ | (CCset S a m (m ^ c)).card ≤ c}

/-- Existence of `c` (Theorem B gives one). -/
lemma exists_cM5 {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (hne : S.Nonempty) (a : ℕ → ℕ) (m : ℕ)
    (hm2 : 2 ≤ m) : ∃ c : ℕ, (CCset S a m (m ^ c)).card ≤ c := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm1R : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hηpos : 0 < Real.logb 2 (m : ℝ) := Real.logb_pos (by norm_num) hm1R
  have hmh : (m : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 (m : ℝ)) := by
    rw [Real.rpow_logb (by norm_num) (by norm_num) hm0]
  have hc := hcond_MstarR hS hne a (Real.logb 2 (m : ℝ)) hηpos.le
  exact ⟨_, (exact_le_multM5 hS m (MstarR S a (Real.logb 2 (m : ℝ))) (Real.logb 2 (m : ℝ)) a hm1 hmh
    hηpos hc).2⟩

lemma cstarM5_spec {S : Finset ℕ} {a : ℕ → ℕ} {m : ℕ} (h : ∃ c : ℕ, (CCset S a m (m ^ c)).card ≤ c) :
    (CCset S a m (m ^ cstarM5 S a m)).card ≤ cstarM5 S a m :=
  Nat.sInf_mem (s := {c : ℕ | (CCset S a m (m ^ c)).card ≤ c}) h

lemma cstarM5_le {S : Finset ℕ} {a : ℕ → ℕ} {m c : ℕ} (hc : (CCset S a m (m ^ c)).card ≤ c) :
    cstarM5 S a m ≤ c :=
  Nat.sInf_le (s := {c : ℕ | (CCset S a m (m ^ c)).card ≤ c}) hc

/-- **Theorem 3.2 (exact counting bound), forced exponents.** With `c* = cstarM5` there is `k` with
`D_S(δ) ≤ k ≤ D_S(δ) m^(c*)`, `P_S(k) < δ`, and `m^(c*) ≤ 2^M` (`M` the exponent of Theorem B,
`η = log₂ m`). -/
theorem exact_bounds_BM5 {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hne : S.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ) (hm2 : 2 ≤ m) (hm : 1 ≤ (m : ℝ) * δ) :
    ∃ k : ℤ, 1 ≤ k ∧ (Dvis S δ : ℤ) ≤ k ∧
      k ≤ (Dvis S δ : ℤ) * ((m ^ cstarM5 S (fun p => aThr p δ) m : ℕ) : ℤ) ∧ InBall S δ k ∧
      m ^ cstarM5 S (fun p => aThr p δ) m ≤
        2 ^ (MstarR S (fun p => aThr p δ) (Real.logb 2 (m : ℝ))) := by
  have hS2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (hS p hp).two_le
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm1R : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hηpos : 0 < Real.logb 2 (m : ℝ) := Real.logb_pos (by norm_num) hm1R
  have hmh : (m : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 (m : ℝ)) := by
    rw [Real.rpow_logb (by norm_num) (by norm_num) hm0]
  have hex := exists_cM5 hS2 hne (fun p => aThr p δ) m hm2
  have hspec := cstarM5_spec hex
  obtain ⟨k, hk1, hkN, hkD, hk⟩ :=
    exact_upper_cM5 hS2 hδ m (fun p => aThr p δ) hm (cstarM5 S (fun p => aThr p δ) m) hspec
  have hDeq : Dprod S (fun p => aThr p δ) = Dvis S δ := rfl
  rw [hDeq] at hkN hkD
  refine ⟨k, hk1, Int.le_of_dvd (by omega) hkD, hkN, hk, ?_⟩
  have hc := hcond_MstarR hS2 hne (fun p => aThr p δ) (Real.logb 2 (m : ℝ)) hηpos.le
  obtain ⟨hpow, hcard⟩ := exact_le_multM5 hS2 m (MstarR S (fun p => aThr p δ) (Real.logb 2 (m : ℝ)))
    (Real.logb 2 (m : ℝ)) (fun p => aThr p δ) hm1 hmh hηpos hc
  have hle := cstarM5_le hcard
  exact (Nat.pow_le_pow_right hm1 hle).trans hpow

#print axioms exact_pigeonM5
#print axioms exact_upper_cM5
#print axioms exact_le_multM5
#print axioms hcond_MstarR
#print axioms exists_cM5
#print axioms exact_bounds_BM5

end TVGPlus
end LeanCheck
