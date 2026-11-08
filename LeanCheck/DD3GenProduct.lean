import Mathlib
import LeanCheck.DD3Product
import LeanCheck.DD3GenGrowth

/-!
# Three chains with general exponents: the product bound (Lean check)

Scope. Counterpart of `DD3Product` for the chains with general exponents `E b k` (`DD3GenSorted`). The scales `b^(E b n)` have
`lpE E b n = E b n * log b ≥ n/4` (strict monotonicity of the exponents gives `E b n ≥ n`), so the sum of the cubes of the
reciprocals of `sqrt (lpE)` over distinct levels is bounded by the convergent series `∑ n^(-3/2)`.

* `Zeta32 = ∑' n, 1 / (sqrt n)^3` (summable); `lpE_ge`, `n_le_of_sqrt_ltE` (`sqrt (lpE) < T` gives `n ≤ ⌊4 T²⌋`),
  `period_injE`;
* `sum_inv_cube_genE`: `∑ 1/(sqrt (lpE))^3 ≤ |ℬ| · 8 Zeta32` over distinct levels with bases in `ℬ`;
* `product_final_genE`, `product_final3E`: for a strictly increasing selection of levels, factors `1 ≤ f_i ≤ B` with
  `f_i ≤ 1 + Cf (1/sqrt(lpE))^3` outside `K` exceptions and for `sqrt (lpE) ≥ T`, the product is at most
  `B^(K + |ℬ| ⌊4 T²⌋) exp(Cf |ℬ| 8 Zeta32)` (the constants differ from the square case, where the sum was bounded by `∑ n^(-3)`).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open Finset

/-- The convergent series `∑ n^(-3/2)` (as `∑ 1/(sqrt n)^3`). -/
noncomputable def Zeta32 : ℝ := ∑' n : ℕ, 1 / (Real.sqrt n) ^ 3

lemma summable_zeta32 : Summable (fun n : ℕ => 1 / (Real.sqrt n) ^ 3) := by
  have h := (Real.summable_one_div_nat_rpow (p := (3 / 2 : ℝ))).2 (by norm_num)
  refine h.congr (fun n => ?_)
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

lemma lpE_ge {E : ℕ → ℕ → ℕ} {b : ℕ} (hb : 2 ≤ b) (he : StrictMono (E b)) (n : ℕ) :
    (n : ℝ) / 4 ≤ lpE E b n := by
  have h1 : (n : ℝ) ≤ (E b n : ℝ) := by exact_mod_cast he.id_le n
  have h2 := JAMerged.log_ge_quarter hb
  unfold lpE
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma n_le_of_sqrt_ltE {E : ℕ → ℕ → ℕ} {b : ℕ} (hb : 2 ≤ b) (he : StrictMono (E b)) {n : ℕ} (T : ℝ)
    (h : Real.sqrt (lpE E b n) < T) : n ≤ ⌊4 * T ^ 2⌋₊ := by
  apply Nat.le_floor
  have hT : 0 < T := lt_of_le_of_lt (Real.sqrt_nonneg _) h
  have h1 : Real.sqrt ((n : ℝ) / 4) ≤ Real.sqrt (lpE E b n) := Real.sqrt_le_sqrt (lpE_ge hb he n)
  have h2 : Real.sqrt ((n : ℝ) / 4) < T := lt_of_le_of_lt h1 h
  have h3 : ((n : ℝ) / 4) < T ^ 2 := by
    have := pow_lt_pow_left₀ h2 (Real.sqrt_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)
    rwa [Real.sq_sqrt (by positivity)] at this
  linarith

lemma period_injE {E : ℕ → ℕ → ℕ} (L : ℕ) (b n : ℕ → ℕ)
    (hmono : ∀ a c, a < c → c < L → lpE E (b a) (n a) < lpE E (b c) (n c)) :
    Set.InjOn (fun i => (b i, n i)) (↑(range L) : Set ℕ) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  have hb : b i = b j := (Prod.mk.inj hij).1
  have hn : n i = n j := (Prod.mk.inj hij).2
  rcases lt_or_gt_of_ne hne with h | h
  · have := hmono i j h hj
    rw [hb, hn] at this
    exact lt_irrefl _ this
  · have := hmono j i h hi
    rw [hb, hn] at this
    exact lt_irrefl _ this

lemma sum_inv_cube_genE {E : ℕ → ℕ → ℕ} (ℬ : Finset ℕ) (hℬ : ∀ b ∈ ℬ, 2 ≤ b) (hE : ∀ b ∈ ℬ, StrictMono (E b))
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, p.1 ∈ ℬ ∧ 1 ≤ p.2) :
    ∑ p ∈ s, 1 / (Real.sqrt (lpE E p.1 p.2)) ^ 3 ≤ ℬ.card * (8 * Zeta32) := by
  classical
  have hmaps : ∀ p ∈ s, p.1 ∈ ℬ := fun p hp => (hs p hp).1
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) hmaps]
  have hfib : ∀ b ∈ ℬ, ∑ p ∈ s.filter (fun p => p.1 = b), 1 / (Real.sqrt (lpE E p.1 p.2)) ^ 3 ≤ 8 * Zeta32 := by
    intro b hb
    have hb2 := hℬ b hb
    have hterm : ∀ p ∈ s.filter (fun p => p.1 = b),
        1 / (Real.sqrt (lpE E p.1 p.2)) ^ 3 ≤ 8 * (1 / (Real.sqrt (p.2 : ℝ)) ^ 3) := by
      intro p hp
      obtain ⟨hps, hp1⟩ := Finset.mem_filter.mp hp
      rw [hp1]
      have hn : (0 : ℝ) < p.2 := by exact_mod_cast (hs p hps).2
      have h1 : Real.sqrt ((p.2 : ℝ) / 4) ≤ Real.sqrt (lpE E b p.2) := Real.sqrt_le_sqrt (lpE_ge hb2 (hE b hb) p.2)
      have h2 : Real.sqrt (p.2 : ℝ) / 2 = Real.sqrt ((p.2 : ℝ) / 4) := by
        rw [Real.sqrt_div (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hpos : 0 < Real.sqrt (p.2 : ℝ) := Real.sqrt_pos.mpr hn
      have h3 : (Real.sqrt (p.2 : ℝ) / 2) ^ 3 ≤ (Real.sqrt (lpE E b p.2)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (h2 ▸ h1) 3
      have h4 : 1 / (Real.sqrt (lpE E b p.2)) ^ 3 ≤ 1 / (Real.sqrt (p.2 : ℝ) / 2) ^ 3 :=
        one_div_le_one_div_of_le (by positivity) h3
      calc 1 / (Real.sqrt (lpE E b p.2)) ^ 3 ≤ 1 / (Real.sqrt (p.2 : ℝ) / 2) ^ 3 := h4
        _ = 8 * (1 / (Real.sqrt (p.2 : ℝ)) ^ 3) := by field_simp; norm_num
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hinj : Set.InjOn Prod.snd (s.filter (fun p => p.1 = b) : Set (ℕ × ℕ)) := by
      intro p hp q hq h
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
      exact Prod.ext (by rw [hp.2, hq.2]) h
    rw [← Finset.sum_image (f := fun n : ℕ => 1 / (Real.sqrt (n : ℝ)) ^ 3) hinj]
    have hle := summable_zeta32.sum_le_tsum ((s.filter (fun p => p.1 = b)).image Prod.snd)
      (fun n _ => by positivity)
    exact mul_le_mul_of_nonneg_left hle (by norm_num)
  calc ∑ b ∈ ℬ, ∑ p ∈ s.filter (fun p => p.1 = b), 1 / (Real.sqrt (lpE E p.1 p.2)) ^ 3
      ≤ ∑ b ∈ ℬ, 8 * Zeta32 := Finset.sum_le_sum hfib
    _ = ℬ.card * (8 * Zeta32) := by simp

/-- **The final product bound** for a finite set `ℬ` of bases, general exponents. -/
theorem product_final_genE {E : ℕ → ℕ → ℕ} (ℬ : Finset ℕ) (hℬ : ∀ b ∈ ℬ, 2 ≤ b) (hE : ∀ b ∈ ℬ, StrictMono (E b))
    (L : ℕ) (b n : ℕ → ℕ) (hb : ∀ i, b i ∈ ℬ) (hn : ∀ i, i < L → 1 ≤ n i)
    (hmono : ∀ a c, a < c → c < L → lpE E (b a) (n a) < lpE E (b c) (n c))
    (f : ℕ → ℝ) (B Cf T : ℝ) (hB : 1 ≤ B) (hCf : 0 ≤ Cf)
    (hfB : ∀ i, i < L → 1 ≤ f i ∧ f i ≤ B)
    (E' : Finset ℕ) (K : ℕ) (hEcard : E'.card ≤ K)
    (hgood : ∀ i, i < L → i ∉ E' → T ≤ Real.sqrt (lpE E (b i) (n i)) →
      f i ≤ 1 + Cf * (1 / Real.sqrt (lpE E (b i) (n i))) ^ 3) :
    ∏ i ∈ range L, f i ≤ B ^ (K + ℬ.card * ⌊4 * T ^ 2⌋₊) * Real.exp (Cf * (ℬ.card * (8 * Zeta32))) := by
  classical
  have hb2 : ∀ i, 2 ≤ b i := fun i => hℬ _ (hb i)
  set early : Finset ℕ := (range L).filter (fun i => Real.sqrt (lpE E (b i) (n i)) < T) with hearly
  set bad : Finset ℕ := E'.filter (fun i => i < L) ∪ early with hbad
  have hbadsub : bad ⊆ range L := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact Finset.mem_range.mpr (Finset.mem_filter.mp h).2
    · exact (Finset.mem_filter.mp h).1
  have hinj := period_injE L b n hmono
  have hearly_card : early.card ≤ ℬ.card * ⌊4 * T ^ 2⌋₊ := by
    have hsub : early.image (fun i => (b i, n i)) ⊆ ℬ ×ˢ Finset.Icc 1 ⌊4 * T ^ 2⌋₊ := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hiL, hit⟩ := Finset.mem_filter.mp hi
      rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · exact hb i
      · rw [Finset.mem_Icc]
        exact ⟨hn i (Finset.mem_range.mp hiL), n_le_of_sqrt_ltE (hb2 i) (hE _ (hb i)) T hit⟩
    have h1 : (early.image (fun i => (b i, n i))).card = early.card :=
      Finset.card_image_of_injOn (hinj.mono (by
        intro i hi
        exact Finset.mem_coe.mpr (Finset.mem_filter.mp hi).1))
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_product, Nat.card_Icc, h1] at h2
    simpa using h2
  have hbad_card : bad.card ≤ K + ℬ.card * ⌊4 * T ^ 2⌋₊ := by
    calc bad.card ≤ (E'.filter (fun i => i < L)).card + early.card := Finset.card_union_le _ _
      _ ≤ E'.card + early.card := by
          have := Finset.card_filter_le E' (fun i => i < L)
          omega
      _ ≤ K + ℬ.card * ⌊4 * T ^ 2⌋₊ := by omega
  have hsum : ∑ i ∈ range L \ bad, Cf * (1 / Real.sqrt (lpE E (b i) (n i))) ^ 3 ≤
      Cf * (ℬ.card * (8 * Zeta32)) := by
    have hnn : ∀ i ∈ range L, 0 ≤ Cf * (1 / Real.sqrt (lpE E (b i) (n i))) ^ 3 :=
      fun i _ => by positivity
    calc ∑ i ∈ range L \ bad, Cf * (1 / Real.sqrt (lpE E (b i) (n i))) ^ 3
        ≤ ∑ i ∈ range L, Cf * (1 / Real.sqrt (lpE E (b i) (n i))) ^ 3 :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i hi _ => hnn i hi)
      _ = Cf * ∑ i ∈ range L, (1 / Real.sqrt (lpE E (b i) (n i))) ^ 3 := by
          rw [Finset.mul_sum]
      _ = Cf * ∑ p ∈ (range L).image (fun i => (b i, n i)),
            1 / (Real.sqrt (lpE E p.1 p.2)) ^ 3 := by
          rw [Finset.sum_image hinj]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [one_div_pow]
      _ ≤ Cf * (ℬ.card * (8 * Zeta32)) := by
          apply mul_le_mul_of_nonneg_left _ hCf
          apply sum_inv_cube_genE ℬ hℬ hE
          intro p hp
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
          exact ⟨hb i, hn i (Finset.mem_range.mp hi)⟩
  have key := MixedPrimeAnalytic.product_bound_with_exceptions (range L) bad hbadsub f
    (fun i => Cf * (1 / Real.sqrt (lpE E (b i) (n i))) ^ 3)
    (fun i hi => by linarith [(hfB i (Finset.mem_range.mp hi)).1])
    (fun i => by positivity) B
    (Cf * (ℬ.card * (8 * Zeta32)))
    (K + ℬ.card * ⌊4 * T ^ 2⌋₊) hB hbad_card
    (fun i hi => (hfB i (Finset.mem_range.mp (hbadsub hi))).2)
    (fun i hi => by
      obtain ⟨hiL, hibad⟩ := Finset.mem_sdiff.mp hi
      have hiL' := Finset.mem_range.mp hiL
      apply hgood i hiL'
      · intro hiE
        exact hibad (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiE, hiL'⟩))
      · by_contra hlt
        push Not at hlt
        exact hibad (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hiL, hlt⟩)))
    hsum
  exact key

/-- **The final product bound for the bases `2, 3, 5`** with general exponents. -/
theorem product_final3E {E : ℕ → ℕ → ℕ} (hE : OK3 E) (L : ℕ) (b n : ℕ → ℕ)
    (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5) (hn : ∀ i, i < L → 1 ≤ n i)
    (hmono : ∀ a c, a < c → c < L → lpE E (b a) (n a) < lpE E (b c) (n c))
    (f : ℕ → ℝ) (B Cf T : ℝ) (hB : 1 ≤ B) (hCf : 0 ≤ Cf)
    (hfB : ∀ i, i < L → 1 ≤ f i ∧ f i ≤ B)
    (E' : Finset ℕ) (K : ℕ) (hEcard : E'.card ≤ K)
    (hgood : ∀ i, i < L → i ∉ E' → T ≤ Real.sqrt (lpE E (b i) (n i)) →
      f i ≤ 1 + Cf * (1 / Real.sqrt (lpE E (b i) (n i))) ^ 3) :
    ∏ i ∈ range L, f i ≤ B ^ (K + 3 * ⌊4 * T ^ 2⌋₊) * Real.exp (Cf * (3 * (8 * Zeta32))) := by
  have hℬ : ∀ c ∈ ({2, 3, 5} : Finset ℕ), 2 ≤ c := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with h | h | h <;> omega
  have hℬE : ∀ c ∈ ({2, 3, 5} : Finset ℕ), StrictMono (E c) := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    exact (hE c hc).1
  have hb' : ∀ i, b i ∈ ({2, 3, 5} : Finset ℕ) := by
    intro i
    rcases hb i with h | h | h <;> simp [h]
  have := product_final_genE {2, 3, 5} hℬ hℬE L b n hb' hn hmono f B Cf T hB hCf hfB E' K hEcard hgood
  have hc : ({2, 3, 5} : Finset ℕ).card = 3 := by decide
  rw [hc] at this
  simpa using this

end DD3Gen
end LeanCheck
