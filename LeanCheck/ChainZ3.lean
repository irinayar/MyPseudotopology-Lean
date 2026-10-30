import LeanCheck.ChainZ2

/-!
# Theorem G, compatible direction: the unstable case
-/

namespace LeanCheck

open Filter Topology

section ZetaPos2

variable {M : ℕ → ℕ}

/-- **Unstable case for `ℚ/ℤ`: contradiction.**  Suppose an infinite set `I` of indices carries multipliers `s_i`
with `s_i M_i ≤ (ε/16) M_{i+1}` and `c₁ ≤ s_i |ρ_i| ≤ 1/8`, where `ρ_i` is the centered representative of
`ζ(e_{i+1})`.  Then `ζ` is not `ε`-small-to-`1/4`. -/
lemma case_unstable_G (hM : ChainSeq M) {ε : ℝ} (hε : 0 < ε) (ζ : TorsA →+ Circ)
    (hsmall : ∀ x : TorsA, (∀ l, ‖M l • (x : Circ)‖ < ε) → ‖ζ x‖ < 1 / 4)
    (ρ : ℕ → ℝ) (hρ : ∀ k, (ρ k : Circ) = ζ (eT M (k + 1)))
    (I : Set ℕ) (hI : I.Infinite) (s : ℕ → ℕ)
    (hs : ∀ i ∈ I, (s i : ℝ) * M i ≤ ε / 16 * M (i + 1))
    (c1 : ℝ) (hc1 : 0 < c1) (ht : ∀ i ∈ I, c1 ≤ s i * |ρ i| ∧ s i * |ρ i| ≤ 1 / 8) : False := by
  classical
  let e : ℕ → ℕ := Nat.nth (fun x => x ∈ I)
  have he : Function.Injective e := Nat.nth_injective hI
  have heI : ∀ j, e j ∈ I := fun j => Nat.nth_mem_of_infinite hI j
  let σ : ℕ → ℤ := fun j => if 0 ≤ ρ (e j) then 1 else -1
  have hσ : ∀ j, |σ j| ≤ 1 := fun j => by
    simp only [σ]; split_ifs <;> simp
  have hσr : ∀ j, (σ j : ℝ) * ρ (e j) = |ρ (e j)| := fun j => by
    simp only [σ]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · push_neg at h; simp [abs_of_neg h]
  obtain ⟨m, hm1, hm2⟩ := crossing (t := fun j => (s (e j) : ℝ) * |ρ (e j)|) hc1
    (fun j => (ht (e j) (heI j)).1) (fun j => (ht (e j) (heI j)).2)
  set x : TorsA := ∑ j ∈ Finset.range m, (σ j * s (e j) : ℤ) • eT M (e j + 1) with hx
  have key : ∀ f : ℕ → ℝ, ((∑ j ∈ Finset.range m, f j : ℝ) : Circ) = ∑ j ∈ Finset.range m, (f j : Circ) :=
    fun f => map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f (Finset.range m)
  have hxc : (x : Circ) = ((∑ j ∈ Finset.range m,
      ((σ j * s (e j) : ℤ) : ℝ) * (1 / (M (e j + 1) : ℝ)) : ℝ) : Circ) := by
    rw [key, hx, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [AddSubgroup.coe_zsmul, eT_coe, zsmul_coe_circ]
  have hnorm : ∀ l, ‖M l • (x : Circ)‖ < ε := fun l => by
    rw [hxc, nsmul_coe_circ]
    have := tail_bound_G hM (ε / 16) (by positivity) (Finset.range m) e he σ hσ (fun j => s (e j))
      (fun j => hs (e j) (heI j)) l
    refine lt_of_le_of_lt this ?_
    linarith
  have h1 := hsmall x hnorm
  have hzx : ζ x = ((∑ j ∈ Finset.range m, (s (e j) : ℝ) * |ρ (e j)| : ℝ) : Circ) := by
    rw [hx, map_sum, key]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_zsmul, ← hρ, zsmul_coe_circ]
    congr 1
    push_cast
    rw [← hσr j]; ring
  rw [hzx] at h1
  set T : ℝ := ∑ j ∈ Finset.range m, (s (e j) : ℝ) * |ρ (e j)| with hT
  have hTabs : |T| ≤ 1 / 2 := by rw [abs_of_pos (by linarith)]; linarith
  rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by simpa using hTabs),
    abs_of_pos (by linarith)] at h1
  linarith

end ZetaPos2

end LeanCheck
