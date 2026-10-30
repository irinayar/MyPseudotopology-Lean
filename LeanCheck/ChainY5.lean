import LeanCheck.ChainY4

/-!
# Theorem F, compatible direction: the two cases
(TVGQ-v7 Theorem 17.3; HamelCharactersTVG_v18 Theorem D.3)
-/

namespace LeanCheck

open Filter Topology

section Cases

variable {M : ℕ → ℕ} (hM : ChainSeq M) {ε : ℝ} {c' : ℝ}
include hM

/-- **Case 2 (unstable): contradiction.**  Suppose an infinite set `I` of indices carries multipliers `s_i` with
`s_i M_i ≤ η M_{i+1}` and `c_1 ≤ s_i |r_i| ≤ 1/8` where `r_i` is the centered representative of `p(c' M_i)`.
Then the hypothesis (★) fails. -/
lemma case_unstable (hε : 0 < ε) (hε8 : ε < 1 / 8)
    (hstar : ∀ n : ℤ, (∀ i, ‖(((n : ℝ) / (M i : ℝ) : ℝ) : Circ)‖ < ε) → ‖((c' * n : ℝ) : Circ)‖ < 1 / 4)
    (r : ℕ → ℝ) (hr1 : ∀ i, (r i : Circ) = ((c' * M i : ℝ) : Circ))
    (I : Set ℕ) (hI : I.Infinite) (s : ℕ → ℕ)
    (hs : ∀ i ∈ I, (s i : ℝ) * M i ≤ ε / 16 * M (i + 1))
    (c1 : ℝ) (hc1 : 0 < c1) (ht : ∀ i ∈ I, c1 ≤ s i * |r i| ∧ s i * |r i| ≤ 1 / 8) : False := by
  classical
  let e : ℕ → ℕ := Nat.nth (fun x => x ∈ I)
  have he : Function.Injective e := Nat.nth_injective hI
  have heI : ∀ j, e j ∈ I := fun j => Nat.nth_mem_of_infinite hI j
  let σ : ℕ → ℤ := fun j => if 0 ≤ r (e j) then 1 else -1
  have hσ : ∀ j, |σ j| ≤ 1 := fun j => by
    simp only [σ]; split_ifs <;> simp
  have hσr : ∀ j, (σ j : ℝ) * r (e j) = |r (e j)| := fun j => by
    simp only [σ]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · push_neg at h; simp [abs_of_neg h]
  obtain ⟨m, hm1, hm2⟩ := crossing (t := fun j => (s (e j) : ℝ) * |r (e j)|) hc1
    (fun j => (ht (e j) (heI j)).1) (fun j => (ht (e j) (heI j)).2)
  set n : ℤ := ∑ j ∈ Finset.range m, σ j * s (e j) * M (e j) with hn
  have hnorm : ∀ l, ‖(((n : ℝ) / (M l : ℝ) : ℝ) : Circ)‖ < ε := fun l => by
    have := tail_bound hM (ε / 16) (by positivity) (Finset.range m) e he σ hσ (fun j => s (e j))
      (fun j => hs (e j) (heI j)) l
    refine lt_of_le_of_lt this ?_
    linarith
  have h1 := hstar n hnorm
  -- compute p(c' n)
  have key : ∀ f : ℕ → ℝ, ((∑ j ∈ Finset.range m, f j : ℝ) : Circ) = ∑ j ∈ Finset.range m, (f j : Circ) :=
    fun f => map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f (Finset.range m)
  have hterm : ∀ j, ((((σ j * s (e j) : ℤ) : ℝ) * (c' * M (e j)) : ℝ) : Circ) =
      ((((σ j * s (e j) : ℤ) : ℝ) * r (e j) : ℝ) : Circ) := fun j => by
    rw [← zsmul_coe_circ, ← zsmul_coe_circ, ← hr1 (e j)]
  have e1 : (c' * (n : ℝ)) = ∑ j ∈ Finset.range m, ((σ j * s (e j) : ℤ) : ℝ) * (c' * M (e j)) := by
    rw [hn]; push_cast; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have e2 : (∑ j ∈ Finset.range m, (s (e j) : ℝ) * |r (e j)|) =
      ∑ j ∈ Finset.range m, ((σ j * s (e j) : ℤ) : ℝ) * r (e j) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast
    rw [← hσr j]; ring
  have hcn : ((c' * n : ℝ) : Circ) = ((∑ j ∈ Finset.range m, (s (e j) : ℝ) * |r (e j)| : ℝ) : Circ) := by
    rw [e1, e2, key, key]
    exact Finset.sum_congr rfl (fun j _ => hterm j)
  rw [hcn] at h1
  set T : ℝ := ∑ j ∈ Finset.range m, (s (e j) : ℝ) * |r (e j)| with hT
  have hTabs : |T| ≤ 1 / 2 := by rw [abs_of_pos (by linarith)]; linarith
  rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by simpa using hTabs),
    abs_of_pos (by linarith)] at h1
  linarith

end Cases

end LeanCheck
