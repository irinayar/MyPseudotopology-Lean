import Mathlib
import LeanCheck.DD3Heights
import LeanCheck.DD3GenGrowth

/-!
# Three chains with general exponents: buffered heights (Lean check)

Scope. Counterpart of `DD3Heights` (phase 5e) for the chains with general exponents `E p k` (`DD3GenSorted`), under the log-gap
hypothesis `OK3 E` (`DD3GenGrowth`). `Buffered3E E D X na nb nc`: with the start level `s = ⌈D⌉`, the scales `p^(E p (s+n_p))`
are the last scales below `D X` and are buffered (`4 q ≤ X`).

* `ratio_to_infty`: from the gap hypothesis the ratios `Q_{j+1}/Q_j` of consecutive scales `Q_j = p^(E p j)` tend to infinity
  (`K Q_j < Q_{j+1}` for large `j`); this replaces the identity `p^((j+1)²) / p^(j²) = p^(2j+1)` of the square case;
* `exists_levelE`, `level_gtE`, `bad_uniqueE`: the three lemmas of `DD3Heights` for the scales `Q_j`;
* `exists_buffered3E`: for `D ≥ 3` and every `M` there is a height `X ≥ M` and depths `na, nb, nc` with `Buffered3E`
  (the four heights `X_i = X₀ E^i` and the pigeonhole over the three primes are unchanged).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the research note requires
mathematical review.
-/

namespace LeanCheck
namespace DD3Gen

open Finset JAHeights

/-- `X` is a buffered height for the three chains with exponents `E` and depths `na, nb, nc` (start level `⌈D⌉`). -/
def Buffered3E (E : ℕ → ℕ → ℕ) (D : ℝ) (X na nb nc : ℕ) : Prop :=
  D * X < (2 : ℝ) ^ (E 2 (sD D + na + 1)) ∧ D * X < (3 : ℝ) ^ (E 3 (sD D + nb + 1)) ∧
  D * X < (5 : ℝ) ^ (E 5 (sD D + nc + 1)) ∧
  4 * 2 ^ (E 2 (sD D + na)) ≤ X ∧ 4 * 3 ^ (E 3 (sD D + nb)) ≤ X ∧ 4 * 5 ^ (E 5 (sD D + nc)) ≤ X

/-- The ratios of consecutive scales tend to infinity. -/
lemma ratio_to_infty {E : ℕ → ℕ → ℕ} {b : ℕ} (hb : 2 ≤ b) (he : StrictMono (E b)) (hg : GapE b (E b)) (K : ℕ) :
    ∃ J, ∀ j, J ≤ j → K * b ^ (E b j) < b ^ (E b (j + 1)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hlogq : (1 / 4 : ℝ) ≤ Real.log b := JAMerged.log_ge_quarter hb
  set c : ℝ := Real.log ((max K 1 : ℕ) : ℝ) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by exact_mod_cast le_max_right K 1)
  refine ⟨⌈4 * c ^ 2⌉₊, fun j hj => ?_⟩
  have hjR : 4 * c ^ 2 ≤ (j : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hj)
  have hEj : (j : ℝ) ≤ (E b j : ℝ) := by exact_mod_cast he.id_le j
  have h1 : c ^ 2 ≤ (E b j : ℝ) * Real.log b := by nlinarith [Nat.cast_nonneg (α := ℝ) (E b j)]
  have h2 : c ≤ Real.sqrt ((E b j : ℝ) * Real.log b) := Real.le_sqrt_of_sq_le h1
  have h3 := hg j
  have h4 : c < (E b (j + 1) : ℝ) * Real.log b - (E b j : ℝ) * Real.log b := lt_of_le_of_lt h2 h3
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    simp only [zero_mul]
    exact pow_pos (by omega) _
  · have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hmax : max K 1 = K := max_eq_left hKpos
    rw [hmax] at hc
    have hQ : (0 : ℝ) < (K : ℝ) * (b : ℝ) ^ (E b j) := by positivity
    have : Real.log ((K : ℝ) * (b : ℝ) ^ (E b j)) < Real.log ((b : ℝ) ^ (E b (j + 1))) := by
      rw [Real.log_mul hKR.ne' (by positivity), Real.log_pow, Real.log_pow]
      linarith
    have h5 := (Real.log_lt_log_iff hQ (by positivity)).1 this
    exact_mod_cast h5

lemma exists_J_ratio {E : ℕ → ℕ → ℕ} (hE : OK3 E) (K : ℕ) :
    ∃ J, ∀ p, (p = 2 ∨ p = 3 ∨ p = 5) → ∀ j, J ≤ j → K * p ^ (E p j) < p ^ (E p (j + 1)) := by
  obtain ⟨J2, h2⟩ := ratio_to_infty (E := E) (b := 2) le_rfl (hE 2 (Or.inl rfl)).1 (hE 2 (Or.inl rfl)).2 K
  obtain ⟨J3, h3⟩ := ratio_to_infty (E := E) (b := 3) (by norm_num) (hE 3 (by simp)).1 (hE 3 (by simp)).2 K
  obtain ⟨J5, h5⟩ := ratio_to_infty (E := E) (b := 5) (by norm_num) (hE 5 (by simp)).1 (hE 5 (by simp)).2 K
  refine ⟨max J2 (max J3 J5), fun p hp j hj => ?_⟩
  rcases hp with rfl | rfl | rfl
  · exact h2 j (le_trans (le_max_left _ _) hj)
  · exact h3 j (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hj)
  · exact h5 j (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hj)

lemma exists_levelE {E : ℕ → ℕ → ℕ} {p : ℕ} (hp : 2 ≤ p) (he : StrictMono (E p)) (X : ℕ)
    (h4 : 4 * p ^ (E p 0) ≤ X) : ∃ j : ℕ, 4 * p ^ (E p j) ≤ X ∧ X < 4 * p ^ (E p (j + 1)) := by
  classical
  have hex : ∃ j : ℕ, X < 4 * p ^ (E p (j + 1)) := by
    refine ⟨X, ?_⟩
    have h1 : X < p ^ X := Nat.lt_pow_self (by omega)
    have h2 : p ^ X ≤ p ^ (E p (X + 1)) := Nat.pow_le_pow_right (by omega) (le_trans (Nat.le_succ X) (he.id_le (X + 1)))
    exact lt_of_lt_of_le h1 (le_trans h2 (Nat.le_mul_of_pos_left _ (by norm_num)))
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; exact h4
  · obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
    have := Nat.find_min hex (show i < Nat.find hex by omega)
    rw [hi]
    exact not_lt.mp this

lemma level_gtE {E : ℕ → ℕ → ℕ} {p : ℕ} (hp : 2 ≤ p) (he : StrictMono (E p)) (J X : ℕ)
    (hX : 4 * p ^ (E p (J + 1)) ≤ X) (j : ℕ) (hj : X < 4 * p ^ (E p (j + 1))) : J < j := by
  by_contra h
  push Not at h
  have h1 : E p (j + 1) ≤ E p (J + 1) := he.monotone (by omega)
  have h2 : p ^ (E p (j + 1)) ≤ p ^ (E p (J + 1)) := Nat.pow_le_pow_right (by omega) h1
  linarith

lemma bad_uniqueE {E : ℕ → ℕ → ℕ} {p : ℕ} (hp : 2 ≤ p) (he : StrictMono (E p)) (D' E' J : ℕ) (hE : 4 * D' ≤ E')
    (hJ : ∀ j, J < j → 4 * D' * E' ^ 3 * p ^ (E p (j + 1)) < p ^ (E p (j + 1 + 1)))
    (X X' j j' : ℕ) (hXX' : E' * X ≤ X') (hXX'3 : X' ≤ E' ^ 3 * X) (hjJ : J < j)
    (hj1 : X < 4 * p ^ (E p (j + 1))) (hj2 : p ^ (E p (j + 1)) ≤ D' * X)
    (hj1' : X' < 4 * p ^ (E p (j' + 1))) (hj2' : p ^ (E p (j' + 1)) ≤ D' * X') : False := by
  have hapos : 0 < p ^ (E p (j + 1)) := pow_pos (by omega) _
  set a := p ^ (E p (j + 1)) with ha
  have a1 : 4 * a ≤ X' := by
    calc 4 * a ≤ 4 * (D' * X) := by omega
      _ = (4 * D') * X := by ring
      _ ≤ E' * X := Nat.mul_le_mul_right _ hE
      _ ≤ X' := hXX'
  have a2 : j < j' := by
    by_contra h
    push Not at h
    have h1 : E p (j' + 1) ≤ E p (j + 1) := he.monotone (by omega)
    have h2 : p ^ (E p (j' + 1)) ≤ a := Nat.pow_le_pow_right (by omega) h1
    omega
  have a3 : E p (j + 1 + 1) ≤ E p (j' + 1) := he.monotone (by omega)
  have a4 : p ^ (E p (j + 1 + 1)) ≤ D' * X' :=
    le_trans (Nat.pow_le_pow_right (by omega) a3) hj2'
  have a6 : D' * X' ≤ (4 * D' * E' ^ 3) * a := by
    calc D' * X' ≤ D' * (E' ^ 3 * X) := Nat.mul_le_mul_left _ hXX'3
      _ ≤ D' * (E' ^ 3 * (4 * a)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hj1.le)
      _ = (4 * D' * E' ^ 3) * a := by ring
  have a7 := hJ j hjJ
  rw [← ha] at a7
  have : (4 * D' * E' ^ 3) * a < p ^ (E p (j + 1 + 1)) := by
    calc (4 * D' * E' ^ 3) * a = 4 * D' * E' ^ 3 * a := rfl
      _ < _ := a7
  omega

/-- **Arbitrarily large buffered heights for three chains with general exponents.** -/
theorem exists_buffered3E {E : ℕ → ℕ → ℕ} (hE : OK3 E) (D : ℝ) (hD : 3 ≤ D) (M : ℕ) :
    ∃ X : ℕ, M ≤ X ∧ ∃ na nb nc : ℕ, Buffered3E E D X na nb nc := by
  classical
  have hD0 : 0 < D := by linarith
  have hmono : ∀ p, (p = 2 ∨ p = 3 ∨ p = 5) → StrictMono (E p) := fun p hp => (hE p hp).1
  obtain ⟨s, hs⟩ : ∃ s, s = sD D := ⟨_, rfl⟩
  have hsD : D ≤ (s : ℝ) := by rw [hs]; exact Nat.le_ceil D
  have hs3 : 3 ≤ s := by
    have : (3 : ℝ) ≤ (s : ℝ) := le_trans hD hsD
    exact_mod_cast this
  obtain ⟨E', hE'⟩ : ∃ E', E' = 4 * s := ⟨_, rfl⟩
  have hE1 : 1 ≤ E' := by omega
  obtain ⟨J0, hJ0⟩ := exists_J_ratio hE (4 * s * E' ^ 3)
  obtain ⟨J, hJ⟩ : ∃ J, J = J0 + s + M := ⟨_, rfl⟩
  have hKJ : ∀ p : ℕ, (p = 2 ∨ p = 3 ∨ p = 5) → ∀ j, J < j →
      4 * s * E' ^ 3 * p ^ (E p (j + 1)) < p ^ (E p (j + 1 + 1)) :=
    fun p hp j hj => hJ0 p hp (j + 1) (by omega)
  have hp2 : ∀ p : ℕ, (p = 2 ∨ p = 3 ∨ p = 5) → 2 ≤ p := fun p hp => by rcases hp with rfl | rfl | rfl <;> norm_num
  obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ (E 2 (J + 1)) * 3 ^ (E 3 (J + 1)) * 5 ^ (E 5 (J + 1)) := ⟨_, rfl⟩
  have hQP : ∀ p : ℕ, (p = 2 ∨ p = 3 ∨ p = 5) → p ^ (E p (J + 1)) ≤ P := by
    intro p hp
    rw [hP]
    have h2 : 1 ≤ 2 ^ (E 2 (J + 1)) := Nat.one_le_pow _ _ (by norm_num)
    have h3 : 1 ≤ 3 ^ (E 3 (J + 1)) := Nat.one_le_pow _ _ (by norm_num)
    have h5 : 1 ≤ 5 ^ (E 5 (J + 1)) := Nat.one_le_pow _ _ (by norm_num)
    rcases hp with rfl | rfl | rfl
    · calc 2 ^ (E 2 (J + 1)) = 2 ^ (E 2 (J + 1)) * 1 * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) h5
    · calc 3 ^ (E 3 (J + 1)) = 1 * 3 ^ (E 3 (J + 1)) * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul h2 le_rfl) h5
    · calc 5 ^ (E 5 (J + 1)) = 1 * 1 * 5 ^ (E 5 (J + 1)) := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul h2 h3) le_rfl
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, X₀ = 4 * P := ⟨_, rfl⟩
  have hX₀M : M ≤ X₀ := by
    have h1 : J + 1 < 5 ^ (J + 1) := Nat.lt_pow_self (by norm_num)
    have h2 : 5 ^ (J + 1) ≤ 5 ^ (E 5 (J + 1)) :=
      Nat.pow_le_pow_right (by norm_num) ((hmono 5 (by simp)).id_le (J + 1))
    have h3 := hQP 5 (by simp)
    omega
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℕ, ∀ i, X i = X₀ * E' ^ i := ⟨fun i => X₀ * E' ^ i, fun _ => rfl⟩
  have hXge : ∀ i p, (p = 2 ∨ p = 3 ∨ p = 5) → 4 * p ^ (E p (J + 1)) ≤ X i := by
    intro i p hp
    rw [hXdef, hX₀]
    have h2 : 1 ≤ E' ^ i := Nat.one_le_pow _ _ (by omega)
    calc 4 * p ^ (E p (J + 1)) ≤ 4 * P := Nat.mul_le_mul_left _ (hQP p hp)
      _ = 4 * P * 1 := by ring
      _ ≤ 4 * P * E' ^ i := Nat.mul_le_mul_left _ h2
  let good : ℕ → ℕ → Prop := fun p x => ∃ j : ℕ, 4 * p ^ (E p j) ≤ x ∧ s * x < p ^ (E p (j + 1))
  have hX0 : ∀ i p, (p = 2 ∨ p = 3 ∨ p = 5) → 4 * p ^ (E p 0) ≤ X i := by
    intro i p hp
    refine le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by have := hp2 p hp; omega)
      ((hmono p hp).monotone (Nat.zero_le (J + 1))))) (hXge i p hp)
  have bad_level : ∀ (p : ℕ), (p = 2 ∨ p = 3 ∨ p = 5) → ∀ i, ¬ good p (X i) →
      ∃ j, J < j ∧ X i < 4 * p ^ (E p (j + 1)) ∧ p ^ (E p (j + 1)) ≤ s * X i := by
    intro p hp i hbad
    obtain ⟨j, hj1, hj2⟩ := exists_levelE (hp2 p hp) (hmono p hp) (X i) (hX0 i p hp)
    refine ⟨j, level_gtE (hp2 p hp) (hmono p hp) J (X i) (hXge i p hp) j hj2, hj2, ?_⟩
    by_contra hlt
    push Not at hlt
    exact hbad ⟨j, hj1, hlt⟩
  have hex : ∃ i, i < 4 ∧ good 2 (X i) ∧ good 3 (X i) ∧ good 5 (X i) := by
    by_contra hno
    push Not at hno
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
    have hp235 : f i = 2 ∨ f i = 3 ∨ f i = 5 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hfp
    have hb1 := hfbad i hi
    have hb2 := hfbad i' hi'
    rw [← hf] at hb2
    obtain ⟨j, hjJ, hj1, hj2⟩ := bad_level (f i) hp235 i hb1
    obtain ⟨j', hjJ', hj1', hj2'⟩ := bad_level (f i) hp235 i' hb2
    have hi4 : i < 4 := Finset.mem_range.mp hi
    have hi4' : i' < 4 := Finset.mem_range.mp hi'
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hr := DD3Heights.rel_pow X₀ E' i i' hE1 hlt (by omega)
      simp only [hXdef] at hj1 hj2 hj1' hj2'
      exact bad_uniqueE (hp2 _ hp235) (hmono _ hp235) s E' J (by omega) (hKJ _ hp235)
        (X₀ * E' ^ i) (X₀ * E' ^ i') j j' hr.1 hr.2 hjJ hj1 hj2 hj1' hj2'
    · have hr := DD3Heights.rel_pow X₀ E' i' i hE1 hlt (by omega)
      simp only [hXdef] at hj1 hj2 hj1' hj2'
      exact bad_uniqueE (hp2 _ hp235) (hmono _ hp235) s E' J (by omega) (hKJ _ hp235)
        (X₀ * E' ^ i') (X₀ * E' ^ i) j' j hr.1 hr.2 hjJ' hj1' hj2' hj1 hj2
  obtain ⟨i, hi, g2, g3, g5⟩ := hex
  obtain ⟨j2, h2a, h2b⟩ := g2
  obtain ⟨j3, h3a, h3b⟩ := g3
  obtain ⟨j5, h5a, h5b⟩ := g5
  have hlev : ∀ (p : ℕ), (p = 2 ∨ p = 3 ∨ p = 5) → ∀ j, s * X i < p ^ (E p (j + 1)) → s ≤ j := by
    intro p hp j hj
    have h5 : X i < 4 * p ^ (E p (j + 1)) := by
      have : X i ≤ s * X i := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have := level_gtE (hp2 p hp) (hmono p hp) J (X i) (hXge i p hp) j h5
    omega
  have l2 := hlev 2 (by simp) j2 h2b
  have l3 := hlev 3 (by simp) j3 h3b
  have l5 := hlev 5 (by simp) j5 h5b
  have hX0' : (0 : ℝ) ≤ X i := Nat.cast_nonneg _
  have key : ∀ (p j : ℕ), s * X i < p ^ (E p (j + 1)) → D * (X i : ℝ) < (p : ℝ) ^ (E p (j + 1)) := by
    intro p j h
    have h' : ((s * X i : ℕ) : ℝ) < ((p ^ (E p (j + 1)) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    nlinarith [mul_le_mul_of_nonneg_right hsD hX0']
  refine ⟨X i, ?_, j2 - s, j3 - s, j5 - s, ?_⟩
  · rw [hXdef]
    have h2 : 1 ≤ E' ^ i := Nat.one_le_pow _ _ (by omega)
    calc M ≤ X₀ := hX₀M
      _ = X₀ * 1 := by ring
      _ ≤ X₀ * E' ^ i := Nat.mul_le_mul_left _ h2
  · have e2 : sD D + (j2 - s) = j2 := by omega
    have e3 : sD D + (j3 - s) = j3 := by omega
    have e5 : sD D + (j5 - s) = j5 := by omega
    unfold Buffered3E
    rw [e2, e3, e5]
    exact ⟨key 2 j2 h2b, key 3 j3 h3b, key 5 j5 h5b, h2a, h3a, h5a⟩

end DD3Gen
end LeanCheck
