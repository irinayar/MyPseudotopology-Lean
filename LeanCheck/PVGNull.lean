import LeanCheck.PVGPseudo

/-!
# PVG: pseudotopologies from the filters converging to zero (Lean check)

Scope. Formal counterpart of Proposition 2.5 (`prop:null`, "Filters converging to zero") of `PVG_v19`, for an arbitrary real
vector space `X`:

* `IsNullFamily C`: a family `C` of filters on `X` with (i) `pure 0 ∈ C` and `C` closed under finer filters, (ii) closed under
  `F + G`, (iii) closed under `a F`, (iv) a filter belongs to `C` as soon as every ultrafilter finer than it does;
* `convOf C F x := F - x ∈ C`: `convOf_isPVG` shows it is a PVG pseudotopology whose filters converging to `0` are exactly the
  members of `C` (`convOf_zero_iff`); `convOf_hausdorff_iff`: it is Hausdorff iff no nonempty filter `F` and `z ≠ 0` satisfy
  `F ∈ C` and `F - z ∈ C`;
* conversely, for a PVG pseudotopology `conv`, `nullFamily_of_pvg` shows that the filters converging to `0` form a family with
  (i) to (iv) and `conv_iff_translate` that `F → x` iff `F - x → 0`, so `conv = convOf (nullFamily conv)`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Filter Topology

namespace PVG
namespace Q95

section Null

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- The translated filter `F - x`. -/
def transl (x : X) (F : Filter X) : Filter X := F.map (fun z => z - x)

/-- A family of filters with the properties (i) to (iv) of Proposition 2.5. -/
structure IsNullFamily (C : Set (Filter X)) : Prop where
  zero : (pure 0 : Filter X) ∈ C
  mono : ∀ {F G : Filter X}, F ∈ C → G ≤ F → G ∈ C
  add : ∀ {F G : Filter X}, F ∈ C → G ∈ C → Filter.map₂ (· + ·) F G ∈ C
  smul : ∀ (a : ℝ) {F : Filter X}, F ∈ C → F.map (fun z => a • z) ∈ C
  ultra : ∀ (F : Filter X) [F.NeBot], (∀ U : Ultrafilter X, (U : Filter X) ≤ F → (U : Filter X) ∈ C) → F ∈ C

/-- The convergence defined by a family of null filters. -/
def convOf (C : Set (Filter X)) (F : Filter X) (x : X) : Prop := transl x F ∈ C

lemma transl_zero (F : Filter X) : transl (0 : X) F = F := by simp [transl]

/-- **Proposition 2.5, first half.** -/
theorem convOf_isPVG {C : Set (Filter X)} (h : IsNullFamily C) : IsPVG (convOf C) where
  p1 x := by
    unfold convOf transl
    rw [Filter.map_pure, sub_self]
    exact h.zero
  p2 := by
    intro F G x hF hGF
    exact h.mono hF (Filter.map_mono hGF)
  p3 := by
    intro F _ x hU
    unfold convOf
    haveI : (transl x F).NeBot := Filter.map_neBot
    refine h.ultra (transl x F) (fun W hW => ?_)
    obtain ⟨U, hUF, hUW⟩ := exists_ultra_map (fun z => z - x) F W hW
    have := hU U hUF
    unfold convOf transl at this
    rw [← hUW, Ultrafilter.coe_map]
    exact this
  add := by
    intro F G x y hF hG
    unfold convOf at *
    have hS := h.add hF hG
    refine h.mono hS ?_
    intro s hs
    obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_map₂_iff.1 hs
    refine Filter.mem_map₂_iff.2 ⟨(fun z => z - x) ⁻¹' A, hA, (fun z => z - y) ⁻¹' B, hB, ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have := hAB ⟨a - x, ha, b - y, hb, rfl⟩
    simpa [sub_add_sub_comm] using this
  smul := by
    intro a F x hF
    unfold convOf at *
    have := h.smul a hF
    have e : transl (a • x) (F.map (fun z => a • z)) = (transl x F).map (fun z => a • z) := by
      unfold transl
      rw [Filter.map_map, Filter.map_map]
      congr 1
      funext z
      simp [smul_sub]
    rw [e]
    exact this

lemma convOf_zero_iff {C : Set (Filter X)} (F : Filter X) : convOf C F 0 ↔ F ∈ C := by
  unfold convOf; rw [transl_zero]

/-- The pseudotopology of `convOf C` is Hausdorff iff no nonempty filter `F` and `z ≠ 0` have `F ∈ C` and `F - z ∈ C`. -/
theorem convOf_hausdorff_iff {C : Set (Filter X)} (h : IsNullFamily C) :
    PHausdorff (convOf C) ↔ ∀ (F : Filter X) [F.NeBot] (z : X), z ≠ 0 → F ∈ C → transl z F ∈ C → False := by
  constructor
  · intro hH F _ z hz hF hFz
    have h1 : convOf C F 0 := (convOf_zero_iff F).2 hF
    have h2 : convOf C F z := hFz
    exact hz (hH F 0 z h1 h2).symm
  · intro hnull F _ x y hx hy
    by_contra hne
    have hz : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    -- translate by `x`
    haveI : (transl x F).NeBot := Filter.map_neBot
    refine hnull (transl x F) (y - x) hz hx ?_
    have : transl (y - x) (transl x F) = transl y F := by
      unfold transl; rw [Filter.map_map]; congr 1; funext z; simp
    rw [this]; exact hy

/-- **Proposition 2.5, second half**: the filters converging to `0` of a PVG form a family with (i) to (iv). -/
theorem nullFamily_of_pvg {conv : Filter X → X → Prop} (h : IsPVG conv) : IsNullFamily {F | conv F 0} where
  zero := h.p1 0
  mono := fun hF hGF => h.p2 hF hGF
  add := by
    intro F G hF hG
    have := h.add hF hG
    simpa using this
  smul := by
    intro a F hF
    have := h.smul a hF
    simpa using this
  ultra := fun F _ hU => h.p3 F 0 (fun U hUF => hU U hUF)

/-- `F → x` iff `F - x → 0`. -/
theorem conv_iff_translate {conv : Filter X → X → Prop} (h : IsPVG conv) (F : Filter X) (x : X) :
    conv F x ↔ conv (transl x F) 0 := by
  constructor
  · intro hF
    have h1 := h.add hF (h.p1 (-x))
    rw [Filter.map₂_pure_right, add_neg_cancel] at h1
    unfold transl
    simpa [sub_eq_add_neg] using h1
  · intro hF
    have h1 := h.add hF (h.p1 x)
    rw [Filter.map₂_pure_right, zero_add] at h1
    unfold transl at h1
    rw [Filter.map_map] at h1
    have e : ((fun a : X => a + x) ∘ fun z => z - x) = id := by funext z; simp
    rw [e, Filter.map_id] at h1
    exact h1

/-- A PVG pseudotopology is the one defined by its null filters. -/
theorem conv_eq_convOf {conv : Filter X → X → Prop} (h : IsPVG conv) (F : Filter X) (x : X) :
    conv F x ↔ convOf {F | conv F 0} F x := conv_iff_translate h F x

#print axioms convOf_isPVG
#print axioms convOf_hausdorff_iff
#print axioms nullFamily_of_pvg
#print axioms conv_iff_translate

end Null

end Q95
end PVG
