import LeanCheck.TVGPlusValuation
import LeanCheck.MixedPrimeSplit

/-!
# TVGplus: diagonal density and block approximation

`JAblock A B` is the block approximation property: for every `ε > 0` there is `k` with `P_p(k - 1) < ε` for `p ∈ A` and
`P_q(k) < ε` for `q ∈ B`.  `DD S` is the diagonal density `TVGPlusValuation.DD`.

* `DD_union`: `DD A`, `DD B` and `JAblock A B` imply `DD (A ∪ B)`.  (Given targets `t`, take `a`, `b` approximating them on `A`,
  `B`, a multiplier `m` from `JAblock A B` with accuracy `ε / (4 (|a| + |b| + 1))`, and `k = m a + (1 - m) b`.)
* `JAblock_of_DD`: for disjoint `A`, `B`, `DD (A ∪ B)` implies `JAblock A B`.
* `DD_insert_iff`: for `p ∉ T`, `DD (insert p T) ↔ DD T ∧ JAblock {p} T`.  Hence diagonal density for a finite set of
  primes is equivalent to the chain of block approximations `JA ({p_i}, {p_{i+1}, ..., p_s})`.

No external hypothesis and no `sorry`.
-/

namespace LeanCheck
namespace TVGPlus

open MixedPrime

/-- Block approximation: `k ≈ 1` for the primes in `A` and `k ≈ 0` for the primes in `B`. -/
def JAblock (A B : Finset ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℤ, (∀ p ∈ A, Pn (sqScales p) (k - 1) < ε) ∧ (∀ q ∈ B, Pn (sqScales q) k < ε)

lemma DD_mono {S T : Finset ℕ} (h : T ⊆ S) (hS : DD S) : DD T := by
  intro t ε hε
  obtain ⟨k, hk⟩ := hS t ε hε
  exact ⟨k, fun p hp => hk p (h hp)⟩

lemma DD_singleton (p : ℕ) : DD {p} := by
  intro t ε hε
  refine ⟨t p, fun q hq => ?_⟩
  rw [Finset.mem_singleton] at hq
  subst hq
  simpa [Pn_zero] using hε

/-- Combination of approximations by `m a + (1 - m) b`. -/
theorem DD_union {A B : Finset ℕ} (hA : DD A) (hB : DD B) (hJ : JAblock A B) : DD (A ∪ B) := by
  intro t ε hε
  obtain ⟨a, ha⟩ := hA t (ε / 4) (by positivity)
  obtain ⟨b, hb⟩ := hB t (ε / 4) (by positivity)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = |(a : ℝ)| + |(b : ℝ)| + 1 := ⟨_, rfl⟩
  have hM : 0 < M := by rw [hMdef]; positivity
  obtain ⟨m, hm1, hm2⟩ := hJ (ε / (4 * M)) (by positivity)
  have hMη : M * (ε / (4 * M)) = ε / 4 := by field_simp
  have hab : |((b - a : ℤ) : ℝ)| ≤ M := by
    rw [hMdef]; push_cast
    have := abs_sub (b : ℝ) (a : ℝ)
    have := abs_nonneg (a : ℝ)
    linarith
  have hba : |((a - b : ℤ) : ℝ)| ≤ M := by
    rw [hMdef]; push_cast
    have := abs_sub (a : ℝ) (b : ℝ)
    have := abs_nonneg (b : ℝ)
    linarith
  refine ⟨m * a + (1 - m) * b, fun p hp => ?_⟩
  rcases Finset.mem_union.mp hp with hpA | hpB
  · -- p ∈ A : k - t p = (a - t p) + (b - a) * (1 - m)
    have e : m * a + (1 - m) * b - t p = (a - t p) + (b - a) * (1 - m) := by ring
    rw [e]
    have h1 := Pn_add_le (sq_nonempty p) (a - t p) ((b - a) * (1 - m))
    have h2 := Pn_zsmul_le (sq_nonempty p) (b - a) (1 - m)
    have h3 : Pn (sqScales p) (1 - m) = Pn (sqScales p) (m - 1) := by
      rw [← Pn_neg]; congr 1; ring
    have h4 := hm1 p hpA
    have h5 := ha p hpA
    rw [h3] at h2
    have h6 : |((b - a : ℤ) : ℝ)| * Pn (sqScales p) (m - 1) ≤ M * Pn (sqScales p) (m - 1) :=
      mul_le_mul_of_nonneg_right hab (Pn_nonneg _ _)
    have h7 : M * Pn (sqScales p) (m - 1) < M * (ε / (4 * M)) := mul_lt_mul_of_pos_left h4 hM
    linarith
  · have e : m * a + (1 - m) * b - t p = (b - t p) + (a - b) * m := by ring
    rw [e]
    have h1 := Pn_add_le (sq_nonempty p) (b - t p) ((a - b) * m)
    have h2 := Pn_zsmul_le (sq_nonempty p) (a - b) m
    have h4 := hm2 p hpB
    have h5 := hb p hpB
    have h6 : |((a - b : ℤ) : ℝ)| * Pn (sqScales p) m ≤ M * Pn (sqScales p) m :=
      mul_le_mul_of_nonneg_right hba (Pn_nonneg _ _)
    have h7 : M * Pn (sqScales p) m < M * (ε / (4 * M)) := mul_lt_mul_of_pos_left h4 hM
    linarith

theorem JAblock_of_DD {A B : Finset ℕ} (hdis : Disjoint A B) (h : DD (A ∪ B)) : JAblock A B := by
  classical
  intro ε hε
  obtain ⟨k, hk⟩ := h (fun p => if p ∈ A then 1 else 0) ε hε
  refine ⟨k, fun p hp => ?_, fun q hq => ?_⟩
  · have := hk p (Finset.mem_union_left _ hp)
    simpa [hp] using this
  · have hqA : q ∉ A := fun hq' => Finset.disjoint_left.mp hdis hq' hq
    have := hk q (Finset.mem_union_right _ hq)
    simpa [hqA] using this

/-- Diagonal density for `insert p T` is diagonal density for `T` plus the block approximation `JAblock {p} T`. -/
theorem DD_insert_iff {p : ℕ} {T : Finset ℕ} (hp : p ∉ T) :
    DD (insert p T) ↔ DD T ∧ JAblock {p} T := by
  have hu : insert p T = {p} ∪ T := by rw [Finset.insert_eq]
  constructor
  · intro h
    refine ⟨DD_mono (Finset.subset_insert p T) h, JAblock_of_DD ?_ (by rw [← hu]; exact h)⟩
    simpa using hp
  · rintro ⟨hT, hJ⟩
    rw [hu]
    exact DD_union (DD_singleton p) hT hJ

/-- **Arbitrary targets reduce to the unit target.**  If `m` is a block-approximation witness with accuracy `η`
(`P_p(m - 1) < η` on `A`, `P_q(m) < η` on `B`), then `k = t_B + (t_A - t_B) m` satisfies
`P_p(k - t_A) ≤ |t_A - t_B| η` on `A` and `P_q(k - t_B) ≤ |t_A - t_B| η` on `B`.  Hence a bound for the unit-target witness
at accuracy `ε / (|t_A - t_B| + 1)` gives a bound `|k| ≤ |t_B| + |t_A - t_B| |m|` for any pair of integer targets. -/
theorem affine_target {A B : Finset ℕ} (tA tB m : ℤ) {η : ℝ}
    (hA : ∀ p ∈ A, Pn (sqScales p) (m - 1) < η) (hB : ∀ q ∈ B, Pn (sqScales q) m < η) :
    (∀ p ∈ A, Pn (sqScales p) (tB + (tA - tB) * m - tA) ≤ |((tA - tB : ℤ) : ℝ)| * η) ∧
      (∀ q ∈ B, Pn (sqScales q) (tB + (tA - tB) * m - tB) ≤ |((tA - tB : ℤ) : ℝ)| * η) := by
  constructor
  · intro p hp
    have e : tB + (tA - tB) * m - tA = (tA - tB) * (m - 1) := by ring
    rw [e]
    exact (Pn_zsmul_le (sq_nonempty p) (tA - tB) (m - 1)).trans
      (mul_le_mul_of_nonneg_left (hA p hp).le (abs_nonneg _))
  · intro q hq
    have e : tB + (tA - tB) * m - tB = (tA - tB) * m := by ring
    rw [e]
    exact (Pn_zsmul_le (sq_nonempty q) (tA - tB) m).trans
      (mul_le_mul_of_nonneg_left (hB q hq).le (abs_nonneg _))

#print axioms DD_union
#print axioms affine_target
#print axioms JAblock_of_DD
#print axioms DD_insert_iff

end TVGPlus
end LeanCheck
