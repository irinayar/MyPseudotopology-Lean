import Mathlib
import LeanCheck.JAHeights

/-!
# Diagonal density for three primes: buffered heights for three chains (Lean check)

Scope. Phase 5e of the Lean version of the conditional proof of `DD({2,3,5})` (research note
`TVGplus_conditional_DD235_2026-11-07.md`). It is the three-prime counterpart of `JAHeights.exists_buffered`.

`Buffered3 D X na nb nc`: with the start level `s = ⌈D⌉` for the three primes `2, 3, 5`, the scales `p^{(s+n_p)^2}` are the last
scales below `D X` and are buffered (`4 q ≤ X`).

`exists_buffered3`: for `D ≥ 3` and every `M` there is a height `X ≥ M` and depths `na, nb, nc` with `Buffered3 D X na nb nc`.

The two-prime argument (adjust one multiplier) does not extend directly, since multiplying by a constant can leave the
range of a previously fixed prime. Here: let `E = 4⌈D⌉` and `X_i = X₀ E^i`, `i < 4`, with `X₀` large. For a prime `p`
the "bad" heights (`p` has no level `j` with `4 p^{j²} ≤ X` and `⌈D⌉ X < p^{(j+1)²}`) are at most one among the four `X_i`
(`bad_unique`: two bad heights `X < X'` with `E X ≤ X' ≤ E³ X` and levels above a large `J` contradict
`p^{2j+3} > 4⌈D⌉E³`); three primes, four candidates, so one candidate is good for all three (pigeonhole).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Heights

open Finset JAHeights

/-- `X` is a buffered height for the three chains with depths `na, nb, nc` (start level `⌈D⌉`). -/
def Buffered3 (D : ℝ) (X na nb nc : ℕ) : Prop :=
  D * X < (2 : ℝ) ^ ((sD D + na + 1) ^ 2) ∧ D * X < (3 : ℝ) ^ ((sD D + nb + 1) ^ 2) ∧
  D * X < (5 : ℝ) ^ ((sD D + nc + 1) ^ 2) ∧
  4 * 2 ^ ((sD D + na) ^ 2) ≤ X ∧ 4 * 3 ^ ((sD D + nb) ^ 2) ≤ X ∧ 4 * 5 ^ ((sD D + nc) ^ 2) ≤ X

lemma exists_level (p : ℕ) (hp : 2 ≤ p) (X : ℕ) (h4 : 4 ≤ X) :
    ∃ j : ℕ, 4 * p ^ (j ^ 2) ≤ X ∧ X < 4 * p ^ ((j + 1) ^ 2) := by
  classical
  have hex : ∃ j : ℕ, X < 4 * p ^ ((j + 1) ^ 2) := by
    refine ⟨X, ?_⟩
    have h1 : X < p ^ X := Nat.lt_pow_self (by omega)
    have h2 : p ^ X ≤ p ^ ((X + 1) ^ 2) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    exact lt_of_lt_of_le h1 (le_trans h2 (Nat.le_mul_of_pos_left _ (by norm_num)))
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; simpa using h4
  · obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
    have := Nat.find_min hex (show i < Nat.find hex by omega)
    rw [hi]
    exact not_lt.mp this

lemma level_gt (p : ℕ) (hp : 2 ≤ p) (J X : ℕ) (hX : 4 * p ^ ((J + 1) ^ 2) ≤ X) (j : ℕ)
    (hj : X < 4 * p ^ ((j + 1) ^ 2)) : J < j := by
  by_contra h
  push Not at h
  have h1 : (j + 1) ^ 2 ≤ (J + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : p ^ ((j + 1) ^ 2) ≤ p ^ ((J + 1) ^ 2) := Nat.pow_le_pow_right (by omega) h1
  linarith

lemma bad_unique (p : ℕ) (hp : 2 ≤ p) (D' E J : ℕ) (hE : 4 * D' ≤ E) (hJ : 4 * D' * E ^ 3 < p ^ (2 * J + 3))
    (X X' j j' : ℕ) (hXX' : E * X ≤ X') (hXX'3 : X' ≤ E ^ 3 * X) (hjJ : J < j)
    (hj1 : X < 4 * p ^ ((j + 1) ^ 2)) (hj2 : p ^ ((j + 1) ^ 2) ≤ D' * X)
    (hj1' : X' < 4 * p ^ ((j' + 1) ^ 2)) (hj2' : p ^ ((j' + 1) ^ 2) ≤ D' * X') : False := by
  have hapos : 0 < p ^ ((j + 1) ^ 2) := pow_pos (by omega) _
  set a := p ^ ((j + 1) ^ 2) with ha
  have a1 : 4 * a ≤ X' := by
    calc 4 * a ≤ 4 * (D' * X) := by omega
      _ = (4 * D') * X := by ring
      _ ≤ E * X := Nat.mul_le_mul_right _ hE
      _ ≤ X' := hXX'
  have a2 : j < j' := by
    by_contra h
    push Not at h
    have h1 : (j' + 1) ^ 2 ≤ (j + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : p ^ ((j' + 1) ^ 2) ≤ a := Nat.pow_le_pow_right (by omega) h1
    omega
  have a3 : (j + 2) ^ 2 ≤ (j' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have a4 : p ^ ((j + 2) ^ 2) ≤ D' * X' :=
    le_trans (Nat.pow_le_pow_right (by omega) a3) hj2'
  have a5 : p ^ ((j + 2) ^ 2) = a * p ^ (2 * j + 3) := by
    rw [ha, ← pow_add]; congr 1; ring
  have a6 : D' * X' ≤ (4 * D' * E ^ 3) * a := by
    calc D' * X' ≤ D' * (E ^ 3 * X) := Nat.mul_le_mul_left _ hXX'3
      _ ≤ D' * (E ^ 3 * (4 * a)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hj1.le)
      _ = (4 * D' * E ^ 3) * a := by ring
  have a7 : a * p ^ (2 * j + 3) ≤ a * (4 * D' * E ^ 3) := by
    rw [← a5]
    calc p ^ ((j + 2) ^ 2) ≤ D' * X' := a4
      _ ≤ (4 * D' * E ^ 3) * a := a6
      _ = a * (4 * D' * E ^ 3) := by ring
  have a8 : p ^ (2 * j + 3) ≤ 4 * D' * E ^ 3 := Nat.le_of_mul_le_mul_left a7 hapos
  have a9 : p ^ (2 * J + 3) ≤ p ^ (2 * j + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

lemma rel_pow (X₀ E i i' : ℕ) (hE : 1 ≤ E) (hlt : i < i') (hi' : i' ≤ i + 3) :
    E * (X₀ * E ^ i) ≤ X₀ * E ^ i' ∧ X₀ * E ^ i' ≤ E ^ 3 * (X₀ * E ^ i) := by
  constructor
  · calc E * (X₀ * E ^ i) = X₀ * E ^ (i + 1) := by ring
      _ ≤ X₀ * E ^ i' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hE hlt)
  · calc X₀ * E ^ i' ≤ X₀ * E ^ (i + 3) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hE hi')
      _ = E ^ 3 * (X₀ * E ^ i) := by ring

/-- **Arbitrarily large buffered heights for three chains.** -/
theorem exists_buffered3 (D : ℝ) (hD : 3 ≤ D) (M : ℕ) :
    ∃ X : ℕ, M ≤ X ∧ ∃ na nb nc : ℕ, Buffered3 D X na nb nc := by
  classical
  have hD0 : 0 < D := by linarith
  obtain ⟨s, hs⟩ : ∃ s, s = sD D := ⟨_, rfl⟩
  have hsD : D ≤ (s : ℝ) := by rw [hs]; exact Nat.le_ceil D
  have hs3 : 3 ≤ s := by
    have : (3 : ℝ) ≤ (s : ℝ) := le_trans hD hsD
    exact_mod_cast this
  obtain ⟨E, hE⟩ : ∃ E, E = 4 * s := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by omega
  obtain ⟨K, hK⟩ : ∃ K, K = 4 * s * E ^ 3 := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = K + s + M := ⟨_, rfl⟩
  have hKJ : ∀ p : ℕ, 2 ≤ p → 4 * s * E ^ 3 < p ^ (2 * J + 3) := by
    intro p hp
    rw [← hK]
    have h1 : K < 2 ^ K := Nat.lt_pow_self (by norm_num)
    have h2 : 2 ^ K ≤ 2 ^ (2 * J + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ (2 * J + 3) ≤ p ^ (2 * J + 3) := Nat.pow_le_pow_left hp _
    omega
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, X₀ = 4 * 5 ^ ((J + 1) ^ 2) := ⟨_, rfl⟩
  have hX₀M : M ≤ X₀ := by
    have h1 : (J + 1) ^ 2 < 5 ^ ((J + 1) ^ 2) := Nat.lt_pow_self (by norm_num)
    have h2 : J + 1 ≤ (J + 1) ^ 2 := by nlinarith
    omega
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℕ, ∀ i, X i = X₀ * E ^ i := ⟨fun i => X₀ * E ^ i, fun _ => rfl⟩
  have hXge : ∀ i p, 2 ≤ p → p ≤ 5 → 4 * p ^ ((J + 1) ^ 2) ≤ X i := by
    intro i p hp hp5
    rw [hXdef, hX₀]
    have h1 : p ^ ((J + 1) ^ 2) ≤ 5 ^ ((J + 1) ^ 2) := Nat.pow_le_pow_left hp5 _
    have h2 : 1 ≤ E ^ i := Nat.one_le_pow _ _ (by omega)
    calc 4 * p ^ ((J + 1) ^ 2) ≤ 4 * 5 ^ ((J + 1) ^ 2) := Nat.mul_le_mul_left _ h1
      _ = 4 * 5 ^ ((J + 1) ^ 2) * 1 := by ring
      _ ≤ 4 * 5 ^ ((J + 1) ^ 2) * E ^ i := Nat.mul_le_mul_left _ h2
  -- good heights
  let good : ℕ → ℕ → Prop := fun p x => ∃ j : ℕ, 4 * p ^ (j ^ 2) ≤ x ∧ s * x < p ^ ((j + 1) ^ 2)
  -- a bad height has a level above `J`
  have bad_level : ∀ (p : ℕ), 2 ≤ p → p ≤ 5 → ∀ i, ¬ good p (X i) →
      ∃ j, J < j ∧ X i < 4 * p ^ ((j + 1) ^ 2) ∧ p ^ ((j + 1) ^ 2) ≤ s * X i := by
    intro p hp hp5 i hbad
    have h4 : 4 ≤ X i := by
      have := hXge i p hp hp5
      have h1 : 1 ≤ p ^ ((J + 1) ^ 2) := Nat.one_le_pow _ _ (by omega)
      omega
    obtain ⟨j, hj1, hj2⟩ := exists_level p hp (X i) h4
    refine ⟨j, level_gt p hp J (X i) (hXge i p hp hp5) j hj2, hj2, ?_⟩
    by_contra hlt
    push Not at hlt
    exact hbad ⟨j, hj1, hlt⟩
  have hex : ∃ i, i < 4 ∧ good 2 (X i) ∧ good 3 (X i) ∧ good 5 (X i) := by
    by_contra hno
    push Not at hno
    -- the bad prime of each candidate
    let f : ℕ → ℕ := fun i => if ¬ good 2 (X i) then 2 else if ¬ good 3 (X i) then 3 else 5
    have hfmem : ∀ i ∈ Finset.range 4, f i ∈ ({2, 3, 5} : Finset ℕ) := by
      intro i _
      simp only [f]
      split_ifs <;> simp
    have hfbad : ∀ i ∈ Finset.range 4, ¬ good (f i) (X i) := by
      intro i hi
      have hi4 : i < 4 := Finset.mem_range.mp hi
      by_cases h2 : good 2 (X i)
      · by_cases h3 : good 3 (X i)
        · have := hno i hi4 h2 h3
          have hf : f i = 5 := by simp [f, h2, h3]
          rw [hf]; exact this
        · have hf : f i = 3 := by simp [f, h2, h3]
          rw [hf]; exact h3
      · have hf : f i = 2 := by simp [f, h2]
        rw [hf]; exact h2
    have hcard : ({2, 3, 5} : Finset ℕ).card < (Finset.range 4).card := by decide
    obtain ⟨i, hi, i', hi', hne, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hfmem
    have hfp : f i ∈ ({2, 3, 5} : Finset ℕ) := hfmem i hi
    have hp2 : 2 ≤ f i ∧ f i ≤ 5 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hfp
      omega
    have hb1 := hfbad i hi
    have hb2 := hfbad i' hi'
    rw [← hf] at hb2
    obtain ⟨j, hjJ, hj1, hj2⟩ := bad_level (f i) hp2.1 hp2.2 i hb1
    obtain ⟨j', hjJ', hj1', hj2'⟩ := bad_level (f i) hp2.1 hp2.2 i' hb2
    have hi4 : i < 4 := Finset.mem_range.mp hi
    have hi4' : i' < 4 := Finset.mem_range.mp hi'
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hr := rel_pow X₀ E i i' hE1 hlt (by omega)
      simp only [hXdef] at hj1 hj2 hj1' hj2'
      exact bad_unique (f i) hp2.1 s E J (by omega) (hKJ _ hp2.1)
        (X₀ * E ^ i) (X₀ * E ^ i') j j' hr.1 hr.2 hjJ hj1 hj2 hj1' hj2'
    · have hr := rel_pow X₀ E i' i hE1 hlt (by omega)
      simp only [hXdef] at hj1 hj2 hj1' hj2'
      exact bad_unique (f i) hp2.1 s E J (by omega) (hKJ _ hp2.1)
        (X₀ * E ^ i') (X₀ * E ^ i) j' j hr.1 hr.2 hjJ' hj1' hj2' hj1 hj2
  obtain ⟨i, hi, g2, g3, g5⟩ := hex
  obtain ⟨j2, h2a, h2b⟩ := g2
  obtain ⟨j3, h3a, h3b⟩ := g3
  obtain ⟨j5, h5a, h5b⟩ := g5
  -- the levels exceed `J ≥ s`
  have hlev : ∀ (p : ℕ), 2 ≤ p → p ≤ 5 → ∀ j, s * X i < p ^ ((j + 1) ^ 2) → s ≤ j := by
    intro p hp hp5 j hj
    have h4 : 4 ≤ X i := by
      have := hXge i p hp hp5
      have h1 : 1 ≤ p ^ ((J + 1) ^ 2) := Nat.one_le_pow _ _ (by omega)
      omega
    have h5 : X i < 4 * p ^ ((j + 1) ^ 2) := by
      have : X i ≤ s * X i := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have := level_gt p hp J (X i) (hXge i p hp hp5) j h5
    omega
  have l2 := hlev 2 le_rfl (by norm_num) j2 h2b
  have l3 := hlev 3 (by norm_num) (by norm_num) j3 h3b
  have l5 := hlev 5 (by norm_num) le_rfl j5 h5b
  have hX0 : (0 : ℝ) ≤ X i := Nat.cast_nonneg _
  have key : ∀ (p j : ℕ), s * X i < p ^ ((j + 1) ^ 2) →
      D * (X i : ℝ) < (p : ℝ) ^ ((j + 1) ^ 2) := by
    intro p j h
    have h' : ((s * X i : ℕ) : ℝ) < ((p ^ ((j + 1) ^ 2) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    nlinarith [mul_le_mul_of_nonneg_right hsD hX0]
  refine ⟨X i, ?_, j2 - s, j3 - s, j5 - s, ?_⟩
  · rw [hXdef]
    have h2 : 1 ≤ E ^ i := Nat.one_le_pow _ _ (by omega)
    calc M ≤ X₀ := hX₀M
      _ = X₀ * 1 := by ring
      _ ≤ X₀ * E ^ i := Nat.mul_le_mul_left _ h2
  · have e2 : sD D + (j2 - s) = j2 := by omega
    have e3 : sD D + (j3 - s) = j3 := by omega
    have e5 : sD D + (j5 - s) = j5 := by omega
    unfold Buffered3
    rw [e2, e3, e5]
    exact ⟨key 2 j2 h2b, key 3 j3 h3b, key 5 j5 h5b, h2a, h3a, h5a⟩

#print axioms exists_level
#print axioms bad_unique
#print axioms exists_buffered3

end DD3Heights
end LeanCheck
