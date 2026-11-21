import Mathlib

/-!
# PG: a pseudotopological group is determined by its filters converging to zero (Lean check)

Scope. Proposition 2.6 of `PG_v1`/`PG_v2` (article "Pseudotopological Groups and Ideals of Sparse Sets"). Filters are proper
(`NeBot`); "finer" is `≤` in Mathlib's order on filters.

* `NullFamily C` : the properties (i)-(iv) of Proposition 2.6 of a family `C` of filters on an abelian group `G`
  (and that members are proper).
* `conv C F x` : `F → x` iff `F - x ∈ C`. Theorems `conv_pure` (P1), `conv_mono` (P2), `conv_ultra` (P3),
  `conv_add`, `conv_neg` (continuity of addition and negation in the form of Lemma 2.4), `conv_zero`
  (the filters converging to `0` are the members of `C`), `hausdorff_iff`.
* `IsPGConv Conv` : a convergence relation with (P1)-(P3), `F → x, H → y ⇒ F + H → x + y`, `F → x ⇒ -F → -x`.
  Theorem `nullFamily_of_conv` and `conv_iff_of_conv`: the filters converging to `0` form a null family and
  `F → x ↔ F - x → 0`, so the relation is the one defined by the null family.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set

namespace PG

variable {G : Type*} [AddCommGroup G]

/-- Properties (i)-(iv) of Proposition 2.6. -/
structure NullFamily (C : Set (Filter G)) : Prop where
  ne : ∀ F ∈ C, F.NeBot
  pure_zero : pure (0 : G) ∈ C
  finer : ∀ F ∈ C, ∀ H : Filter G, H ≤ F → H.NeBot → H ∈ C
  add : ∀ F ∈ C, ∀ H ∈ C, Filter.map₂ (· + ·) F H ∈ C
  neg : ∀ F ∈ C, Filter.map (fun x : G => -x) F ∈ C
  ultra : ∀ F : Filter G, F.NeBot →
    (∀ U : Ultrafilter G, (U : Filter G) ≤ F → (U : Filter G) ∈ C) → F ∈ C

/-- Convergence defined by a family of null filters: `F → x` iff `F - x ∈ C`. -/
def conv (C : Set (Filter G)) (F : Filter G) (x : G) : Prop :=
  Filter.map (fun y => y - x) F ∈ C

theorem conv_zero (C : Set (Filter G)) (F : Filter G) : conv C F 0 ↔ F ∈ C := by
  simp [conv]

/-- (P1) -/
theorem conv_pure {C : Set (Filter G)} (h : NullFamily C) (x : G) : conv C (pure x) x := by
  simpa [conv] using h.pure_zero

/-- (P2) -/
theorem conv_mono {C : Set (Filter G)} (h : NullFamily C) {F H : Filter G} {x : G}
    (hF : conv C F x) (hle : H ≤ F) (hne : H.NeBot) : conv C H x := by
  refine h.finer _ hF _ (Filter.map_mono hle) ?_
  have := hne
  infer_instance

/-- (P3) -/
theorem conv_ultra {C : Set (Filter G)} (h : NullFamily C) {F : Filter G} {x : G} (hne : F.NeBot)
    (hU : ∀ U : Ultrafilter G, (U : Filter G) ≤ F → conv C U x) : conv C F x := by
  refine h.ultra _ (by have := hne; infer_instance) ?_
  intro V hV
  let U : Ultrafilter G := V.map (fun y => y + x)
  have hUeq : (U : Filter G) = Filter.map (fun y => y + x) (V : Filter G) := rfl
  have h1 : (U : Filter G) ≤ F := by
    rw [hUeq]
    calc Filter.map (fun y => y + x) (V : Filter G)
        ≤ Filter.map (fun y => y + x) (Filter.map (fun y => y - x) F) := Filter.map_mono hV
      _ = F := by
        rw [Filter.map_map]
        have : ((fun y : G => y + x) ∘ fun y => y - x) = id := by
          funext y; simp
        rw [this, Filter.map_id]
  have h2 := hU U h1
  unfold conv at h2
  have h3 : Filter.map (fun y => y - x) (U : Filter G) = (V : Filter G) := by
    rw [hUeq, Filter.map_map]
    have : ((fun y : G => y - x) ∘ fun y => y + x) = id := by
      funext y; simp
    rw [this, Filter.map_id]
  rwa [h3] at h2

/-- Addition (Lemma 2.4). -/
theorem conv_add {C : Set (Filter G)} (h : NullFamily C) {F H : Filter G} {x y : G}
    (hF : conv C F x) (hH : conv C H y) : conv C (Filter.map₂ (· + ·) F H) (x + y) := by
  have h1 := h.add _ hF _ hH
  have e : Filter.map (fun z => z - (x + y)) (Filter.map₂ (· + ·) F H)
      = Filter.map₂ (· + ·) (Filter.map (fun z => z - x) F) (Filter.map (fun z => z - y) H) := by
    apply Filter.map_map₂_distrib
    intro a b
    show a + b - (x + y) = (a - x) + (b - y)
    abel
  unfold conv
  rw [e]
  exact h1

/-- Negation (Lemma 2.4). -/
theorem conv_neg {C : Set (Filter G)} (h : NullFamily C) {F : Filter G} {x : G}
    (hF : conv C F x) : conv C (Filter.map (fun z : G => -z) F) (-x) := by
  have h1 := h.neg _ hF
  have e : Filter.map (fun z => z - (-x)) (Filter.map (fun z : G => -z) F)
      = Filter.map (fun z : G => -z) (Filter.map (fun z => z - x) F) := by
    rw [Filter.map_map, Filter.map_map]
    congr 1
    funext z
    simp only [Function.comp]
    abel
  unfold conv
  rw [e]
  exact h1

/-- Hausdorff criterion of Proposition 2.6. -/
theorem hausdorff_iff {C : Set (Filter G)} :
    (∀ (F : Filter G) (x y : G), conv C F x → conv C F y → x = y) ↔
      (∀ (F : Filter G) (z : G), F ∈ C → Filter.map (fun y => y - z) F ∈ C → z = 0) := by
  constructor
  · intro H F z hF hFz
    have h0 : conv C F 0 := (conv_zero C F).2 hF
    exact (H F 0 z h0 hFz).symm
  · intro H F x y hx hy
    have e : Filter.map (fun w => w - (y - x)) (Filter.map (fun w => w - x) F)
        = Filter.map (fun w => w - y) F := by
      rw [Filter.map_map]
      congr 1
      funext w
      simp only [Function.comp]
      abel
    have := H (Filter.map (fun w => w - x) F) (y - x) hx (by unfold conv at hy; rw [e]; exact hy)
    exact (sub_eq_zero.mp this).symm

/-- A convergence relation making `G` a pseudotopological group (properties P1-P3, Lemma 2.4). -/
structure IsPGConv (Conv : Filter G → G → Prop) : Prop where
  ne : ∀ F x, Conv F x → F.NeBot
  p1 : ∀ x, Conv (pure x) x
  p2 : ∀ F H x, Conv F x → H ≤ F → H.NeBot → Conv H x
  p3 : ∀ F x, F.NeBot → (∀ U : Ultrafilter G, (U : Filter G) ≤ F → Conv U x) → Conv F x
  add : ∀ F H x y, Conv F x → Conv H y → Conv (Filter.map₂ (· + ·) F H) (x + y)
  neg : ∀ F x, Conv F x → Conv (Filter.map (fun z : G => -z) F) (-x)

/-- `F → x ↔ F - x → 0` for a pseudotopological group convergence. -/
theorem conv_iff_of_conv {Conv : Filter G → G → Prop} (h : IsPGConv Conv) (F : Filter G) (x : G) :
    Conv F x ↔ Conv (Filter.map (fun y => y - x) F) 0 := by
  constructor
  · intro hF
    have h1 := h.add F (pure (-x)) x (-x) hF (h.p1 (-x))
    rw [Filter.map₂_pure_right, add_neg_cancel] at h1
    have e : Filter.map (fun y => y + -x) F = Filter.map (fun y => y - x) F := by
      congr 1
      funext y
      simp [sub_eq_add_neg]
    rwa [e] at h1
  · intro hF
    have h1 := h.add _ (pure x) 0 x hF (h.p1 x)
    rw [Filter.map₂_pure_right, zero_add, Filter.map_map] at h1
    have e : ((fun y : G => y + x) ∘ fun y => y - x) = id := by
      funext y; simp
    rwa [e, Filter.map_id] at h1

/-- The filters converging to `0` form a null family. -/
theorem nullFamily_of_conv {Conv : Filter G → G → Prop} (h : IsPGConv Conv) :
    NullFamily {F : Filter G | Conv F 0} where
  ne := fun F hF => h.ne F 0 hF
  pure_zero := h.p1 0
  finer := fun F hF H hle hne => h.p2 F H 0 hF hle hne
  add := fun F hF H hH => by
    have := h.add F H 0 0 hF hH
    rwa [add_zero] at this
  neg := fun F hF => by
    have := h.neg F 0 hF
    rwa [neg_zero] at this
  ultra := fun F hne hU => h.p3 F 0 hne hU

/-- The relation `Conv` is the one defined by the null family of the filters converging to `0`. -/
theorem conv_eq_of_conv {Conv : Filter G → G → Prop} (h : IsPGConv Conv) (F : Filter G) (x : G) :
    Conv F x ↔ conv {F : Filter G | Conv F 0} F x :=
  conv_iff_of_conv h F x

end PG
