import LeanCheck.PVGSeqFU2

/-!
# PVG: clusters of arithmetic progressions accumulate at `0` in the Bohr topology (Lean check)

Scope. Proposition `clusters` (`clusters`) of `PVG_v19`: for `M_i > 0` and `H_i → ∞`, the set `C = ⋃_i {M_i h : 1 ≤ h ≤ H_i}` does not
contain `0`, but `0` lies in its Bohr closure.

* `K_nhds_zero_basic`: a neighbourhood of `0` in `K` contains `{κ : ‖κ b‖ < ε for b in a finite set}`;
* `exists_small_multiple`: pigeonhole in the torus: for a finite set `I` of frequencies and `ε > 0` there is `N` such that for
  every `a` some `h ∈ [1,N]` has `‖b (a h)‖ < ε` for all `b ∈ I`;
* `mem_closure_bohr`: criterion for membership in the Bohr closure;
* `clusters`: the statement.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology Pointwise

namespace PVG
namespace Q95

/-- A neighbourhood of `0` in `K` contains a basic one defined by finitely many frequencies. -/
theorem K_nhds_zero_basic {V : Set K} (hV : V ∈ 𝓝 (0 : K)) :
    ∃ (I : Finset ℝ) (ε : ℝ), 0 < ε ∧ ∀ κ : K, (∀ b ∈ I, ‖κ b‖ < ε) → κ ∈ V := by
  rw [isEmbedding_coe.isInducing.nhds_eq_comap] at hV
  obtain ⟨T, hT, hTV⟩ := Filter.mem_comap.1 hV
  have hT' : T ∈ Filter.pi (fun b : ℝ => 𝓝 ((0 : K) b)) := by
    rw [← nhds_pi]; exact hT
  obtain ⟨I, t, ht, hIT⟩ := Filter.mem_pi'.1 hT'
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ b ∈ I, Metric.ball (0 : AddCircle (1 : ℝ)) ε ⊆ t b := by
    rw [Filter.eventually_all_finset]
    intro b _
    have hb : t b ∈ 𝓝 (0 : AddCircle (1 : ℝ)) := ht b
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 hb
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    exact (Metric.ball_subset_ball hε.2.le).trans hball
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hballs, hε⟩ := (hev.and hpos).exists
  refine ⟨I, ε, hε, fun κ hκ => hTV ?_⟩
  refine hIT (fun b hb => hballs b hb ?_)
  rw [mem_ball_zero_iff]
  exact hκ b hb

lemma coe_add_int (x : ℝ) (n : ℤ) : ((x + n : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := by
  rw [AddCircle.coe_add]
  have : ((n : ℝ) : AddCircle (1 : ℝ)) = 0 := (AddCircle.coe_eq_zero_iff (1 : ℝ)).2 ⟨n, by simp⟩
  rw [this, add_zero]

/-- Pigeonhole in the torus. -/
theorem exists_small_multiple (I : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ a : ℝ, ∃ h : ℕ, 1 ≤ h ∧ h ≤ N ∧ ∀ b ∈ I, ‖((b * (a * h) : ℝ) : AddCircle (1 : ℝ))‖ < ε := by
  classical
  set Q : ℕ := ⌈1 / ε⌉₊ + 1 with hQ
  have hQpos : (0 : ℝ) < Q := by positivity
  have hQε : 1 / (Q : ℝ) < ε := by
    rw [div_lt_iff₀ hQpos]
    have h1 : 1 / ε ≤ ⌈1 / ε⌉₊ := Nat.le_ceil _
    have h2 : ((Q : ℕ) : ℝ) = (⌈1 / ε⌉₊ : ℝ) + 1 := by rw [hQ]; push_cast; ring
    rw [h2]
    have h3 : 1 < ε * ((⌈1 / ε⌉₊ : ℝ) + 1) := by
      have : 1 / ε * ε = 1 := by field_simp
      nlinarith
    linarith
  refine ⟨Q ^ I.card, fun a => ?_⟩
  -- the box of the `j`-th multiple
  have hbox : ∀ (j : ℕ) (b : ℝ), ⌊(Q : ℝ) * Int.fract ((j : ℝ) * (b * a))⌋₊ < Q := by
    intro j b
    rw [Nat.floor_lt (mul_nonneg hQpos.le (Int.fract_nonneg _))]
    have := Int.fract_lt_one ((j : ℝ) * (b * a))
    nlinarith
  let g : Fin (Q ^ I.card + 1) → (↥I → Fin Q) := fun j b => ⟨_, hbox j b⟩
  have hcard : Fintype.card (↥I → Fin Q) < Fintype.card (Fin (Q ^ I.card + 1)) := by
    rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, Fintype.card_fin]
    exact Nat.lt_succ_self _
  obtain ⟨x, y, hxy, hgxy⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  -- order the two indices
  have key : ∀ j₁ j₂ : Fin (Q ^ I.card + 1), j₁ < j₂ → g j₁ = g j₂ →
      ∃ h : ℕ, 1 ≤ h ∧ h ≤ Q ^ I.card ∧ ∀ b ∈ I, ‖((b * (a * h) : ℝ) : AddCircle (1 : ℝ))‖ < ε := by
    intro j₁ j₂ hlt hg
    refine ⟨(j₂ : ℕ) - (j₁ : ℕ), by omega, by have := j₂.2; omega, fun b hb => ?_⟩
    have hbx := congrFun hg ⟨b, hb⟩
    have hfl : ⌊(Q : ℝ) * Int.fract (((j₁ : ℕ) : ℝ) * (b * a))⌋₊ = ⌊(Q : ℝ) * Int.fract (((j₂ : ℕ) : ℝ) * (b * a))⌋₊ :=
      congrArg Fin.val hbx
    set f₁ := Int.fract (((j₁ : ℕ) : ℝ) * (b * a)) with hf₁
    set f₂ := Int.fract (((j₂ : ℕ) : ℝ) * (b * a)) with hf₂
    have h1 := (Nat.floor_eq_iff (mul_nonneg hQpos.le (Int.fract_nonneg _))).1 hfl.symm
    have h2 := (Nat.floor_eq_iff (mul_nonneg hQpos.le (Int.fract_nonneg ((((j₁ : ℕ) : ℝ) * (b * a)))))).1 rfl
    have hdiff : |f₂ - f₁| < 1 / (Q : ℝ) := by
      have h3 : |(Q : ℝ) * (f₂ - f₁)| < 1 := by
        rw [abs_lt]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
      rw [abs_mul, abs_of_pos hQpos] at h3
      rw [lt_div_iff₀ hQpos]; linarith
    have hcast : ((((j₂ : ℕ) - (j₁ : ℕ) : ℕ) : ℝ)) = ((j₂ : ℕ) : ℝ) - ((j₁ : ℕ) : ℝ) := by
      rw [Nat.cast_sub hlt.le]
    have hrewrite : b * (a * (((j₂ : ℕ) - (j₁ : ℕ) : ℕ) : ℝ)) =
        (f₂ - f₁) + ((⌊((j₂ : ℕ) : ℝ) * (b * a)⌋ - ⌊((j₁ : ℕ) : ℝ) * (b * a)⌋ : ℤ) : ℝ) := by
      rw [hcast]
      have e2 : f₂ = ((j₂ : ℕ) : ℝ) * (b * a) - ⌊((j₂ : ℕ) : ℝ) * (b * a)⌋ := rfl
      have e1 : f₁ = ((j₁ : ℕ) : ℝ) * (b * a) - ⌊((j₁ : ℕ) : ℝ) * (b * a)⌋ := rfl
      rw [e1, e2]; push_cast; ring
    rw [hrewrite, coe_add_int]
    exact lt_of_le_of_lt (norm_circle_le_abs _) (hdiff.trans hQε)
  rcases lt_or_gt_of_ne hxy with h | h
  · exact key x y h hgxy
  · exact key y x h hgxy.symm

/-- `x` is in the Bohr closure of `A` if every neighbourhood of `e x` in `K` contains some `e a`, `a ∈ A`. -/
theorem mem_closure_bohr (A : Set ℝ) (x : ℝ) (h : ∀ V ∈ 𝓝 (e x), ∃ a ∈ A, e a ∈ V) :
    x ∈ @closure ℝ bohrTop A := by
  letI : TopologicalSpace ℝ := bohrTop
  rw [mem_closure_iff_nhds]
  intro W hW
  rw [nhds_bohr] at hW
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.1 hW
  obtain ⟨a, haA, haV⟩ := h V hV
  exact ⟨a, hVW haV, haA⟩

/-- **Proposition `clusters`.** `0 ∉ C` and `0 ∈ cl_{τ_B}(C)` for `C = ⋃_i {M_i h : 1 ≤ h ≤ H_i}`. -/
theorem clusters (M : ℕ → ℝ) (hM : ∀ i, 0 < M i) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    (0 : ℝ) ∉ {x : ℝ | ∃ i h : ℕ, 1 ≤ h ∧ h ≤ H i ∧ x = M i * h} ∧
    (0 : ℝ) ∈ @closure ℝ bohrTop {x : ℝ | ∃ i h : ℕ, 1 ≤ h ∧ h ≤ H i ∧ x = M i * h} := by
  refine ⟨?_, ?_⟩
  · rintro ⟨i, h, hh, -, hx⟩
    have : 0 < M i * (h : ℝ) := mul_pos (hM i) (by exact_mod_cast hh)
    linarith
  · refine mem_closure_bohr _ 0 (fun V hV => ?_)
    rw [e_zero] at hV
    obtain ⟨I, ε, hε, hIV⟩ := K_nhds_zero_basic hV
    obtain ⟨N, hN⟩ := exists_small_multiple I hε
    obtain ⟨i, hi⟩ := (hH.eventually_ge_atTop N).exists
    obtain ⟨h, hh1, hhN, hsmall⟩ := hN (M i)
    refine ⟨M i * h, ⟨i, h, hh1, hhN.trans hi, rfl⟩, hIV _ (fun b hb => ?_)⟩
    simpa [e_apply] using hsmall b hb

#print axioms K_nhds_zero_basic
#print axioms exists_small_multiple
#print axioms clusters

end Q95
end PVG
