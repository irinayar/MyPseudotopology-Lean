import LeanCheck.ChainZ5

/-!
# The run condition for a subset of a chain, and the union lemma
(TVGQ-v7 Lemma 17.2 `chains:union`; HamelCharactersTVG_v18 Lemma D.2)

Fix a divisibility chain `m : ℕ → ℕ`.  For a set `U ⊆ ℕ` of indices, a *chain of length `k` in `U` with ratio bound
`A`* is a strictly increasing sequence `w 0 < ... < w k` of elements of `U` with `m (w (j+1)) < A * m (w j)`.
`HSet m U` ("`H(U)`") says: for every `A > 2` the lengths of such chains are bounded.  (This is the same as the
printed condition on runs of consecutive terms of the selected subsequence: a chain with bounded ratios can be
filled in with the intermediate indices of `U`, because ratios only grow when terms are skipped.)
-/

namespace LeanCheck

open Filter Topology

section HSetDef

/-- A chain of length `k` in `U` with all ratios `< A`. -/
def IsChain (m : ℕ → ℕ) (U : Set ℕ) (A : ℝ) (k : ℕ) (w : ℕ → ℕ) : Prop :=
  (∀ j, j ≤ k → w j ∈ U) ∧ (∀ j, j < k → w j < w (j + 1) ∧ (m (w (j + 1)) : ℝ) < A * m (w j))

/-- Set form of the condition `H(U)`. -/
def HSet (m : ℕ → ℕ) (U : Set ℕ) : Prop :=
  ∀ A : ℝ, 2 < A → ∃ L : ℕ, ∀ k w, IsChain m U A k w → k ≤ L

variable {m : ℕ → ℕ}

lemma IsChain.lt {U : Set ℕ} {A : ℝ} {k : ℕ} {w : ℕ → ℕ} (h : IsChain m U A k w) {p q : ℕ}
    (hpq : p < q) (hq : q ≤ k) : w p < w q := by
  induction q, hpq using Nat.le_induction with
  | base => exact (h.2 p (by omega)).1
  | succ q hpq ih =>
    exact lt_trans (ih (by omega)) (h.2 q (by omega)).1

lemma IsChain.ratio {U : Set ℕ} {A : ℝ} (hA : 0 < A) {k : ℕ} {w : ℕ → ℕ} (h : IsChain m U A k w) {p : ℕ} :
    ∀ d : ℕ, 1 ≤ d → p + d ≤ k → (m (w (p + d)) : ℝ) < A ^ d * m (w p) := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
    intro hk
    simpa using (h.2 p (by omega)).2
  | succ d hd ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := (h.2 (p + d) (by omega)).2
    calc (m (w (p + (d + 1))) : ℝ) = m (w (p + d + 1)) := by rw [add_assoc]
      _ < A * m (w (p + d)) := h2
      _ ≤ A * (A ^ d * m (w p)) := by gcongr
      _ = A ^ (d + 1) * m (w p) := by ring

/-- A finite set of indices satisfies `H`. -/
lemma HSet_finite {U : Set ℕ} (hU : U.Finite) : HSet m U := by
  intro A _
  refine ⟨hU.toFinset.card, fun k w hw => ?_⟩
  have hinj : Set.InjOn w (Finset.range (k + 1) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hw.lt h (by omega)).ne hxy
    · exact (hw.lt h (by omega)).ne hxy.symm
  have := Finset.card_le_card_of_injOn w (s := Finset.range (k + 1)) (t := hU.toFinset)
    (fun j hj => by
      have hj' : j < k + 1 := by simpa using hj
      exact hU.mem_toFinset.2 (hw.1 j (by omega))) hinj
  simp at this
  omega

/-- **Finite unions of chain subsets** (Lemma 17.2 / D.2): `H(S)` and `H(T)` give `H(S ∪ T)`. -/
theorem HSet_union {S T : Set ℕ} (hS : HSet m S) (hT : HSet m T) : HSet m (S ∪ T) := by
  intro A hA
  obtain ⟨l, hl⟩ := hT A hA
  set g : ℕ := l + 2 with hg
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  set Bd : ℝ := A ^ (2 * g) with hBd
  have hBd2 : 2 < Bd := by
    have : A ^ 1 ≤ A ^ (2 * g) := pow_le_pow_right₀ hA1 (by omega)
    rw [pow_one] at this
    linarith
  obtain ⟨lS, hlS⟩ := hS Bd hBd2
  refine ⟨(lS + 2) * g, fun k w hw => ?_⟩
  by_contra hk
  push_neg at hk
  have hwin : ∀ j, (j + 1) * g ≤ k + 1 → ∃ p, j * g ≤ p ∧ p < (j + 1) * g ∧ w p ∈ S := by
    intro j hj
    by_contra hnone
    push_neg at hnone
    have e1 : (j + 1) * g = j * g + g := by ring
    have hT' : IsChain m T A (g - 1) (fun i => w (j * g + i)) := by
      constructor
      · intro i hi
        have hmem := hw.1 (j * g + i) (by omega)
        rcases hmem with h | h
        · exact absurd h (hnone (j * g + i) (by omega) (by omega))
        · exact h
      · intro i hi
        have hik : j * g + i < k := by omega
        have := hw.2 (j * g + i) hik
        simpa [add_assoc] using this
    have := hl _ _ hT'
    omega
  choose! p hp1 hp2 hp3 using hwin
  have hjk : ∀ j, j ≤ lS + 1 → (j + 1) * g ≤ k + 1 := fun j hj => by
    have : (j + 1) * g ≤ (lS + 2) * g := Nat.mul_le_mul_right g (by omega)
    omega
  have hv : IsChain m S Bd (lS + 1) (fun i => w (p i)) := by
    constructor
    · intro j hj
      exact hp3 j (hjk j hj)
    · intro j hj
      have hj1 := hjk j (by omega)
      have hj2 := hjk (j + 1) (by omega)
      have e1 := hp1 j hj1
      have e2 := hp2 j hj1
      have e3 := hp1 (j + 1) hj2
      have e4 := hp2 (j + 1) hj2
      have hgpos : 1 ≤ g := by omega
      have hpj : p j < p (j + 1) := by
        have : (j + 1) * g ≤ p (j + 1) := e3
        omega
      refine ⟨hw.lt hpj (by omega), ?_⟩
      obtain ⟨d, hd⟩ : ∃ d, p (j + 1) = p j + d := ⟨p (j + 1) - p j, by omega⟩
      have hd1 : 1 ≤ d := by omega
      have e5 : (j + 1 + 1) * g = j * g + 2 * g := by ring
      have hd2 : d ≤ 2 * g := by omega
      have hk' : p j + d ≤ k := by
        rw [← hd]; omega
      have hr := hw.ratio hA0 d hd1 hk'
      rw [← hd] at hr
      calc (m (w (p (j + 1))) : ℝ) < A ^ d * m (w (p j)) := hr
        _ ≤ A ^ (2 * g) * m (w (p j)) := by
            gcongr
  have := hlS _ _ hv
  omega

end HSetDef

end LeanCheck
