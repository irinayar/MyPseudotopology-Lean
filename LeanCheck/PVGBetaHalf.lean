import Mathlib

/-!
# PVG: half-integer witnesses (Lean check, with Kronecker's theorem as an explicit hypothesis)

Scope. Lemma `lem:halfint` of PVG_v22. Kronecker's density theorem is a classical result (for example Hardy and Wright, Chapter XXIII);
it is not in Mathlib, which has only the one-dimensional case (`AddCircle.denseRange_zsmul_iff`). It enters here as the explicit
hypothesis `KroneckerDensity`, in the form: if `1, β₁, …, β_w` are linearly independent over `ℚ`, then for every target `θ` and every
`ε > 0` some integer `k` has `‖kβ_s − θ_s‖ < ε` for all `s`, where `‖·‖` is the distance to the nearest integer (the norm of `AddCircle 1`).

* `half_integer_witness`: if `y₁, …, y_M` are reals such that `1` is not in their rational linear span, then for every `ε > 0` there is
  an integer `k` with `‖(k + 1/2) y_l‖ < ε` for all `l`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open Filter Topology

namespace PVG
namespace Beta

/-- **Hypothesis (Kronecker's theorem, not formalized).** -/
def KroneckerDensity : Prop :=
  ∀ (w : ℕ) (β : Fin w → ℝ), LinearIndependent ℚ (Fin.cons (1 : ℝ) β : Fin (w + 1) → ℝ) →
    ∀ (θ : Fin w → ℝ) (ε : ℝ), 0 < ε →
      ∃ k : ℤ, ∀ s, ‖(((k : ℝ) * β s - θ s : ℝ) : AddCircle (1 : ℝ))‖ < ε

theorem half_integer_witness (hK : KroneckerDensity) {M : ℕ} (y : Fin M → ℝ)
    (h1 : (1 : ℝ) ∉ Submodule.span ℚ (Set.range y)) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℤ, ∀ l, ‖((((k : ℝ) + 1 / 2) * y l : ℝ) : AddCircle (1 : ℝ))‖ < ε := by
  classical
  set W : Submodule ℚ ℝ := Submodule.span ℚ (Set.range y) with hW
  have : Module.Finite ℚ W := by rw [hW]; exact Module.Finite.span_of_finite ℚ (Set.finite_range y)
  let b := Module.finBasis ℚ W
  set w := Module.finrank ℚ W with hw
  -- rational coordinates
  have hyW : ∀ l, y l ∈ W := fun l => Submodule.subset_span ⟨l, rfl⟩
  let r : Fin M → Fin w → ℚ := fun l s => b.repr ⟨y l, hyW l⟩ s
  have hrep : ∀ l, y l = ∑ s, (r l s : ℝ) * (b s : ℝ) := by
    intro l
    have := b.sum_repr ⟨y l, hyW l⟩
    have h2 := congrArg (fun z : W => (z : ℝ)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    rw [← h2]
    simp [r, Rat.smul_def]
  -- a common denominator
  obtain ⟨D, hDpos, hD⟩ : ∃ D : ℕ, 0 < D ∧ ∀ l s, ∃ a : ℤ, (a : ℚ) = r l s * D := by
    refine ⟨∏ p : Fin M × Fin w, (r p.1 p.2).den, Finset.prod_pos (fun p _ => (r p.1 p.2).den_pos), ?_⟩
    intro l s
    obtain ⟨e, he⟩ : (r l s).den ∣ ∏ p : Fin M × Fin w, (r p.1 p.2).den :=
      Finset.dvd_prod_of_mem (fun p : Fin M × Fin w => (r p.1 p.2).den) (Finset.mem_univ (l, s))
    refine ⟨(r l s).num * e, ?_⟩
    rw [he]
    push_cast
    have := Rat.mul_den_eq_num (r l s)
    rw [← this]; ring
  choose a ha using hD
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hDpos.ne'
  -- the scaled basis
  let β : Fin w → ℝ := fun s => (b s : ℝ) / D
  have hy : ∀ l, y l = ∑ s, (a l s : ℝ) * β s := by
    intro l
    rw [hrep l]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have : (a l s : ℝ) = (r l s : ℝ) * D := by exact_mod_cast ha l s
    simp only [β]; rw [this]; field_simp
  -- linear independence of `(1, β)`
  have hli : LinearIndependent ℚ (Fin.cons (1 : ℝ) β : Fin (w + 1) → ℝ) := by
    rw [linearIndependent_finCons]
    constructor
    · -- `β` is linearly independent
      have hb : LinearIndependent ℚ (fun s => (b s : ℝ)) :=
        b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
      have hD' : ((D : ℚ)⁻¹) ≠ 0 := by simpa using hDpos.ne'
      have hβ : β = fun s => ((D : ℚ)⁻¹) • (b s : ℝ) := by
        funext s; simp [β, Rat.smul_def, div_eq_inv_mul]
      rw [hβ]
      exact hb.units_smul (fun _ => Units.mk0 _ hD')
    · intro hmem
      apply h1
      -- `span β ⊆ W`
      have : Submodule.span ℚ (Set.range β) ≤ W := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨s, rfl⟩
        have : β s = ((D : ℚ)⁻¹) • (b s : ℝ) := by simp [β, Rat.smul_def, div_eq_inv_mul]
        rw [this]; exact W.smul_mem _ (b s).2
      exact this hmem
  -- apply Kronecker with target `-β/2`
  set A : ℕ := 1 + ∑ l, ∑ s, (a l s).natAbs with hA
  have hApos : (0 : ℝ) < A := by positivity
  obtain ⟨k, hk⟩ := hK w β hli (fun s => -(β s) / 2) (ε / A) (by positivity)
  refine ⟨k, fun l => ?_⟩
  have key : ((((k : ℝ) + 1 / 2) * y l : ℝ) : AddCircle (1 : ℝ)) =
      ∑ s, (a l s) • ((((k : ℝ) + 1 / 2) * β s : ℝ) : AddCircle (1 : ℝ)) := by
    rw [hy l, Finset.mul_sum]
    rw [show ((∑ s, ((k : ℝ) + 1 / 2) * ((a l s : ℝ) * β s) : ℝ) : AddCircle (1 : ℝ)) =
      ∑ s, (((((k : ℝ) + 1 / 2) * ((a l s : ℝ) * β s) : ℝ)) : AddCircle (1 : ℝ)) from
        map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ _]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have : ((k : ℝ) + 1 / 2) * ((a l s : ℝ) * β s) = (a l s) • (((k : ℝ) + 1 / 2) * β s) := by
      rw [zsmul_eq_mul]; ring
    rw [this]
    exact AddCircle.coe_zsmul (p := (1 : ℝ)) (n := a l s) (x := ((k : ℝ) + 1 / 2) * β s)
  have hs : ∀ s, ‖((((k : ℝ) + 1 / 2) * β s : ℝ) : AddCircle (1 : ℝ))‖ < ε / A := by
    intro s
    have := hk s
    have e : (k : ℝ) * β s - (-(β s) / 2) = ((k : ℝ) + 1 / 2) * β s := by ring
    simpa [e] using this
  rw [key]
  calc ‖∑ s, (a l s) • ((((k : ℝ) + 1 / 2) * β s : ℝ) : AddCircle (1 : ℝ))‖
      ≤ ∑ s, ‖(a l s) • ((((k : ℝ) + 1 / 2) * β s : ℝ) : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ s, ((a l s).natAbs : ℝ) * (ε / A) := by
        refine Finset.sum_le_sum (fun s _ => ?_)
        calc ‖(a l s) • ((((k : ℝ) + 1 / 2) * β s : ℝ) : AddCircle (1 : ℝ))‖
            ≤ ‖a l s‖ * ‖((((k : ℝ) + 1 / 2) * β s : ℝ) : AddCircle (1 : ℝ))‖ := norm_zsmul_le _ _
          _ ≤ ((a l s).natAbs : ℝ) * (ε / A) := by
              have h0 : ‖a l s‖ = ((a l s).natAbs : ℝ) := by simp [Int.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs]
              rw [h0]
              exact mul_le_mul_of_nonneg_left (hs s).le (by positivity)
    _ = (∑ s, ((a l s).natAbs : ℝ)) * (ε / A) := by rw [Finset.sum_mul]
    _ < ε := by
        have hle : (∑ s, ((a l s).natAbs : ℝ)) ≤ A - 1 := by
          have : (∑ s, (a l s).natAbs) ≤ ∑ l', ∑ s, (a l' s).natAbs :=
            Finset.single_le_sum (f := fun l' => ∑ s, (a l' s).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
          have h3 : ((∑ s, (a l s).natAbs : ℕ) : ℝ) ≤ ((∑ l', ∑ s, (a l' s).natAbs : ℕ) : ℝ) := by exact_mod_cast this
          simp only [hA]; push_cast at h3 ⊢; linarith
        have : (∑ s, ((a l s).natAbs : ℝ)) * (ε / A) ≤ (A - 1) * (ε / A) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
        calc _ ≤ (A - 1) * (ε / A) := this
          _ = ε - ε / A := by field_simp
          _ < ε := by have : 0 < ε / A := by positivity
                      linarith

end Beta
end PVG
