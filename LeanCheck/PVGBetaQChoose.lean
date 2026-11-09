import Mathlib
import LeanCheck.PVGBetaQCantor
import LeanCheck.PVGBetaChoose
import LeanCheck.PVGBetaMain

/-!
# PVG: the recursion of the variant of the construction (Lean check)

Scope. Addendum H of the research note. One step of the recursion of `PVGBetaChoose` (`exists_next`: new centers algebraically independent
over the old ones, finite family of half-integer witnesses, radius) followed by the radius shrinking of `PVGBetaQStage` (`exists_Q_radius`),
which gives the recurrence property `Qprop`; shrinking a radius preserves the other conditions.

* `Pprop_mono`: the witness property is inherited by smaller radii;
* `exists_nextQ`: the step;
* `exists_stagesQ`: a `StagesQ` system exists (with Kronecker's theorem as a hypothesis);
* `exists_Q_measure`: the measure of the system is a probability measure without atoms carried by `[1,2]`, with the stage property
  `StageProperty` and the recurrence property `RecurProp`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open MeasureTheory Filter Topology Set

namespace PVG
namespace Beta

lemma Pprop_mono {n : ℕ} {z : ℕ → ℝ} {r r' : ℝ} (h : r' ≤ r) (hP : Pprop n ⟨z, r⟩) : Pprop n ⟨z, r'⟩ := by
  intro c hc
  obtain ⟨k, E, hE, hk⟩ := hP c hc
  refine ⟨k, E, hE, fun a ha haE l hl i => hk a ha haE l ?_ i⟩
  have h1 : z a - r' ≤ l := hl.1
  have h2 : l ≤ z a + r' := hl.2
  exact ⟨by show z a - r ≤ l; linarith, by show l ≤ z a + r; linarith⟩

theorem exists_nextQ (hK : KroneckerDensity) (n : ℕ) (s : Stage) (hs : 0 < s.rad) :
    ∃ s' : Stage, Good (n + 1) s' ∧ Qprop (n + 1) s' ∧ Link n s s' := by
  obtain ⟨s1, hg, hl⟩ := exists_next hK n s hs
  obtain ⟨r2, hr2, hr2le, hQ⟩ := exists_Q_radius (n + 1) (by omega) s1.ctr s1.rad hg.1
  refine ⟨⟨s1.ctr, r2⟩, ⟨hr2, hr2le.trans hg.2.1, fun h1 => ?_⟩, hQ, ?_, ?_⟩
  · have hP : Pprop (n + 1) ⟨s1.ctr, s1.rad⟩ := hg.2.2 h1
    exact Pprop_mono hr2le hP
  · intro a ha
    have := hl.1 a ha
    show |s1.ctr a - s.ctr (a / 2)| + r2 < s.rad
    linarith
  · intro c hc
    have := hl.2 c hc
    show 2 * r2 < |s1.ctr (2 * c) - s1.ctr (2 * c + 1)|
    linarith

/-- **A stage system with the recurrence field exists** (with Kronecker's theorem as a hypothesis). -/
theorem exists_stagesQ (hK : KroneckerDensity) : ∃ (x : ℕ → ℕ → ℝ) (r : ℕ → ℝ), StagesQ x r := by
  classical
  have hnext : ∀ (n : ℕ) (s : Stage), 0 < s.rad →
      ∃ s' : Stage, Good (n + 1) s' ∧ Qprop (n + 1) s' ∧ Link n s s' :=
    fun n s hs => exists_nextQ hK n s hs
  choose F hF using hnext
  let g : (n : ℕ) → {s : Stage // Good n s ∧ (1 ≤ n → Qprop n s)} :=
    fun n => Nat.rec (motive := fun n => {s : Stage // Good n s ∧ (1 ≤ n → Qprop n s)})
      ⟨stage0, good0, fun h => (Nat.not_succ_le_zero 0 h).elim⟩
      (fun n ih => ⟨F n ih.1 ih.2.1.1, (hF n ih.1 ih.2.1.1).1, fun _ => (hF n ih.1 ih.2.1.1).2.1⟩) n
  refine ⟨fun n a => (g n).1.ctr a, fun n => (g n).1.rad, ?_⟩
  exact
    { r_pos := fun n => (g n).2.1.1
      r_le := fun n => (g n).2.1.2.1
      root := ⟨rfl, rfl⟩
      nest := fun n a ha => (hF n (g n).1 (g n).2.1.1).2.2.1 a ha
      sib := fun n c hc => (hF n (g n).1 (g n).2.1.1).2.2.2 c hc
      P := fun n hn c hc => (g n).2.1.2.2 hn c hc
      Q := fun n hn => (g n).2.2 hn }

/-- The measure of the variant: stage property and recurrence property. -/
theorem exists_Q_measure (hK : KroneckerDensity) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ NullSingletonClass μ ∧ μ (Icc (1 : ℝ) 2)ᶜ = 0 ∧
      StageProperty μ ∧ RecurProp μ := by
  obtain ⟨x, r, h⟩ := exists_stagesQ hK
  exact ⟨cantorMeasure x, h.toStages.isProb, ⟨h.toStages.null_single⟩, h.toStages.supp,
    h.toStages.stageProperty, h.recurProp⟩

end Beta
end PVG
