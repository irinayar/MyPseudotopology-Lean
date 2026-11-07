import Mathlib
import LeanCheck.JAProductFinal
import LeanCheck.JAMerged
import LeanCheck.MixedPrimeAnalytic

/-!
# Diagonal density for three primes: the final product bound (Lean check)

Scope. Third piece of the Lean version of the conditional proof of `DD({2,3,5})` (research note
`TVGplus_conditional_DD235_2026-11-07.md`, item 3, last step). `JAProductFinal.product_final` concludes that
`∏ f_i` is bounded independently of the number of levels, from `1 ≤ f_i ≤ B`, boundedly many exceptional levels and
`f_i ≤ 1 + Cf (1/t_i)³` on the others; its two uses of the number of bases (at most `2⌊2T⌋` early levels, and
`∑ t_i⁻³ ≤ 2((√log 2)⁻³ + (√log 3)⁻³)`) are replaced here by a finite set `ℬ` of bases:

* `sum_inv_cube_gen`: for a finite set `s` of distinct periods `(b,n)` with `b ∈ ℬ`, `n ≥ 1`,
  `∑ (√(lp b n))⁻³ ≤ 2 ∑_{b ∈ ℬ} (√log b)⁻³`;
* `product_final_gen`: the product bound `∏ f_i ≤ B^(K + |ℬ| ⌊2T⌋) exp(Cf · 2 ∑_{b∈ℬ} (√log b)⁻³)`;
* `product_final3`: the case `ℬ = {2,3,5}`: `B^(K + 3⌊2T⌋) exp(Cf · 2((√log 2)⁻³ + (√log 3)⁻³ + (√log 5)⁻³))`.

The proof of `product_final_gen` is `JAProductFinal.product_final` with these two replacements. A Lean proof verifies its
formal statement under its hypotheses; the correspondence with the research note requires mathematical review.
-/

namespace LeanCheck
namespace DD3Product

open Finset JAMerged JAProductFinal

/-- `∑ (√(lp b n))⁻³` over distinct periods with bases in `ℬ` is at most `2 ∑_{b∈ℬ} (√log b)⁻³`. -/
lemma sum_inv_cube_gen (ℬ : Finset ℕ) (hℬ : ∀ b ∈ ℬ, 2 ≤ b) (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, p.1 ∈ ℬ ∧ 1 ≤ p.2) :
    ∑ p ∈ s, 1 / (Real.sqrt (lp p.1 p.2)) ^ 3 ≤ 2 * ∑ b ∈ ℬ, 1 / (Real.sqrt (Real.log b)) ^ 3 := by
  classical
  have hmaps : ∀ p ∈ s, p.1 ∈ ℬ := fun p hp => (hs p hp).1
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  have hb2 := hℬ b hb
  have hpos : 0 < Real.sqrt (Real.log b) :=
    Real.sqrt_pos.mpr (by have := log_ge_quarter hb2; linarith)
  have hterm : ∀ p ∈ s.filter (fun p => p.1 = b),
      1 / (Real.sqrt (lp p.1 p.2)) ^ 3 = 1 / (Real.sqrt (Real.log b)) ^ 3 * (1 / (p.2 : ℝ) ^ 3) := by
    intro p hp
    obtain ⟨hps, hp1⟩ := Finset.mem_filter.mp hp
    rw [sqrt_lp, hp1]
    have hn : (0 : ℝ) < p.2 := by exact_mod_cast (hs p hps).2
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hinj : Set.InjOn Prod.snd (s.filter (fun p => p.1 = b) : Set (ℕ × ℕ)) := by
    intro p hp q hq h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
    exact Prod.ext (by rw [hp.2, hq.2]) h
  rw [← Finset.sum_image (f := fun n : ℕ => 1 / (n : ℝ) ^ 3) hinj]
  have hsum := inv_cube_sum_set ((s.filter (fun p => p.1 = b)).image Prod.snd) (by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact (hs p (Finset.mem_filter.mp hp).1).2)
  have hc : (0 : ℝ) ≤ 1 / (Real.sqrt (Real.log b)) ^ 3 := by positivity
  nlinarith

/-- **The final product bound** for a finite set `ℬ` of bases. -/
theorem product_final_gen (ℬ : Finset ℕ) (hℬ : ∀ b ∈ ℬ, 2 ≤ b) (L : ℕ) (b n : ℕ → ℕ)
    (hb : ∀ i, b i ∈ ℬ) (hn : ∀ i, i < L → 1 ≤ n i)
    (hmono : ∀ a c, a < c → c < L → lp (b a) (n a) < lp (b c) (n c))
    (f : ℕ → ℝ) (B Cf T : ℝ) (hB : 1 ≤ B) (hCf : 0 ≤ Cf)
    (hfB : ∀ i, i < L → 1 ≤ f i ∧ f i ≤ B)
    (E : Finset ℕ) (K : ℕ) (hEcard : E.card ≤ K)
    (hgood : ∀ i, i < L → i ∉ E → T ≤ Real.sqrt (lp (b i) (n i)) →
      f i ≤ 1 + Cf * (1 / Real.sqrt (lp (b i) (n i))) ^ 3) :
    ∏ i ∈ range L, f i ≤ B ^ (K + ℬ.card * ⌊2 * T⌋₊) *
      Real.exp (Cf * (2 * ∑ c ∈ ℬ, 1 / (Real.sqrt (Real.log c)) ^ 3)) := by
  classical
  have hb2 : ∀ i, 2 ≤ b i := fun i => hℬ _ (hb i)
  set early : Finset ℕ := (range L).filter (fun i => Real.sqrt (lp (b i) (n i)) < T) with hearly
  set bad : Finset ℕ := E.filter (fun i => i < L) ∪ early with hbad
  have hbadsub : bad ⊆ range L := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact Finset.mem_range.mpr (Finset.mem_filter.mp h).2
    · exact (Finset.mem_filter.mp h).1
  have hinj := period_inj L b n hmono
  have hearly_card : early.card ≤ ℬ.card * ⌊2 * T⌋₊ := by
    have hsub : early.image (fun i => (b i, n i)) ⊆ ℬ ×ˢ Finset.Icc 1 ⌊2 * T⌋₊ := by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hiL, hit⟩ := Finset.mem_filter.mp hi
      rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · exact hb i
      · rw [Finset.mem_Icc]
        refine ⟨hn i (Finset.mem_range.mp hiL), ?_⟩
        apply Nat.le_floor
        exact n_le_of_sqrt_lt (b i) (n i) (hb2 i) T hit
    have h1 : (early.image (fun i => (b i, n i))).card = early.card :=
      Finset.card_image_of_injOn (hinj.mono (by
        intro i hi
        exact Finset.mem_coe.mpr (Finset.mem_filter.mp hi).1))
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_product, Nat.card_Icc, h1] at h2
    simpa using h2
  have hbad_card : bad.card ≤ K + ℬ.card * ⌊2 * T⌋₊ := by
    calc bad.card ≤ (E.filter (fun i => i < L)).card + early.card := Finset.card_union_le _ _
      _ ≤ E.card + early.card := by
          have := Finset.card_filter_le E (fun i => i < L)
          omega
      _ ≤ K + ℬ.card * ⌊2 * T⌋₊ := by omega
  have hsum : ∑ i ∈ range L \ bad, Cf * (1 / Real.sqrt (lp (b i) (n i))) ^ 3 ≤
      Cf * (2 * ∑ c ∈ ℬ, 1 / (Real.sqrt (Real.log c)) ^ 3) := by
    have hnn : ∀ i ∈ range L, 0 ≤ Cf * (1 / Real.sqrt (lp (b i) (n i))) ^ 3 :=
      fun i _ => by positivity
    calc ∑ i ∈ range L \ bad, Cf * (1 / Real.sqrt (lp (b i) (n i))) ^ 3
        ≤ ∑ i ∈ range L, Cf * (1 / Real.sqrt (lp (b i) (n i))) ^ 3 :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i hi _ => hnn i hi)
      _ = Cf * ∑ i ∈ range L, (1 / Real.sqrt (lp (b i) (n i))) ^ 3 := by
          rw [Finset.mul_sum]
      _ = Cf * ∑ p ∈ (range L).image (fun i => (b i, n i)),
            1 / (Real.sqrt (lp p.1 p.2)) ^ 3 := by
          rw [Finset.sum_image hinj]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [one_div_pow]
      _ ≤ Cf * (2 * ∑ c ∈ ℬ, 1 / (Real.sqrt (Real.log c)) ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ hCf
          apply sum_inv_cube_gen ℬ hℬ
          intro p hp
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
          exact ⟨hb i, hn i (Finset.mem_range.mp hi)⟩
  have key := MixedPrimeAnalytic.product_bound_with_exceptions (range L) bad hbadsub f
    (fun i => Cf * (1 / Real.sqrt (lp (b i) (n i))) ^ 3)
    (fun i hi => by linarith [(hfB i (Finset.mem_range.mp hi)).1])
    (fun i => by positivity) B
    (Cf * (2 * ∑ c ∈ ℬ, 1 / (Real.sqrt (Real.log c)) ^ 3))
    (K + ℬ.card * ⌊2 * T⌋₊) hB hbad_card
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

/-- **The final product bound for the bases `2, 3, 5`.** -/
theorem product_final3 (L : ℕ) (b n : ℕ → ℕ) (hb : ∀ i, b i = 2 ∨ b i = 3 ∨ b i = 5)
    (hn : ∀ i, i < L → 1 ≤ n i)
    (hmono : ∀ a c, a < c → c < L → lp (b a) (n a) < lp (b c) (n c))
    (f : ℕ → ℝ) (B Cf T : ℝ) (hB : 1 ≤ B) (hCf : 0 ≤ Cf)
    (hfB : ∀ i, i < L → 1 ≤ f i ∧ f i ≤ B)
    (E : Finset ℕ) (K : ℕ) (hEcard : E.card ≤ K)
    (hgood : ∀ i, i < L → i ∉ E → T ≤ Real.sqrt (lp (b i) (n i)) →
      f i ≤ 1 + Cf * (1 / Real.sqrt (lp (b i) (n i))) ^ 3) :
    ∏ i ∈ range L, f i ≤ B ^ (K + 3 * ⌊2 * T⌋₊) *
      Real.exp (Cf * (2 * (1 / (Real.sqrt (Real.log 2)) ^ 3 + 1 / (Real.sqrt (Real.log 3)) ^ 3 +
        1 / (Real.sqrt (Real.log 5)) ^ 3))) := by
  have hℬ : ∀ c ∈ ({2, 3, 5} : Finset ℕ), 2 ≤ c := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with h | h | h <;> omega
  have hb' : ∀ i, b i ∈ ({2, 3, 5} : Finset ℕ) := by
    intro i
    rcases hb i with h | h | h <;> simp [h]
  have := product_final_gen {2, 3, 5} hℬ L b n hb' hn hmono f B Cf T hB hCf hfB E K hEcard hgood
  have hc : ({2, 3, 5} : Finset ℕ).card = 3 := by decide
  rw [hc] at this
  have hs : ∑ c ∈ ({2, 3, 5} : Finset ℕ), 1 / (Real.sqrt (Real.log (c : ℝ))) ^ 3 =
      1 / (Real.sqrt (Real.log 2)) ^ 3 + 1 / (Real.sqrt (Real.log 3)) ^ 3 +
        1 / (Real.sqrt (Real.log 5)) ^ 3 := by
    simp [Finset.sum_insert, add_assoc]
  rw [hs] at this
  exact this

end DD3Product
end LeanCheck
