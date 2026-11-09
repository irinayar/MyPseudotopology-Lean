import Mathlib
import LeanCheck.PVGBetaChoose
import LeanCheck.PVGLacMain

/-!
# PVG: the recurrence witnesses of the variant of the construction (Lean check)

Scope. Property `(Q_n)` of Addendum H of the research note (the variant of Theorem `thm:betaexists` for which `ξ_{β,I_S}` is not
pretopological). For the lacunary sequence `sS n = 2^(n^2)` and centers `x_j`: for every vector `c` of the box `[-n,n]^n` there are
`p > q ≥ n` with `‖c_i (sS p − sS q) λ‖ < 1/n` for all `i ≤ n` and all `λ` in the intervals of level `n`. No algebraic independence is needed:
the witnesses come from a pigeonhole argument in the compact torus.

* `witness_Q_pointwise`: the pigeonhole step for one vector `c`;
* `finite_witnesses_Q`: a finite family serves every vector of the box (compactness);
* `exists_Q_radius`: for every stage and radius `r' > 0` there is `r'' ∈ (0, r']` such that the stage with radius `r''` has `Qprop`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical review.
-/

open MeasureTheory Filter Topology Set

namespace PVG
namespace Beta

open PVG.Lac in
/-- The recurrence property of a stage at level `n`. -/
def Qprop (n : ℕ) (s : Stage) : Prop :=
  ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ n) → ∃ p q : ℕ, n ≤ q ∧ q < p ∧
    ∀ a, a < 2 ^ n → ∀ l ∈ Icc (s.ctr a - s.rad) (s.ctr a + s.rad), ∀ i : Fin n,
      ‖((c i * (sS p - sS q) * l : ℝ) : AddCircle (1 : ℝ))‖ < 1 / n

/-- Pigeonhole in the compact torus: for one vector `c` and finitely many centers. -/
theorem witness_Q_pointwise (n N : ℕ) (x : Fin N → ℝ) (c : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℕ, n ≤ q ∧ q < p ∧ ∀ (i : Fin n) (j : Fin N),
      ‖((c i * (PVG.Lac.sS p - PVG.Lac.sS q) * x j : ℝ) : AddCircle (1 : ℝ))‖ < ε := by
  classical
  let Φ : ℕ → (Fin n × Fin N → AddCircle (1 : ℝ)) :=
    fun p ij => ((c ij.1 * PVG.Lac.sS p * x ij.2 : ℝ) : AddCircle (1 : ℝ))
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq (fun k : ℕ => Φ (n + k))
  have hcau := hlim.cauchySeq
  rw [Metric.cauchySeq_iff] at hcau
  obtain ⟨K, hK⟩ := hcau ε hε
  have hd := hK (K + 1) (Nat.le_succ K) K le_rfl
  refine ⟨n + φ (K + 1), n + φ K, by omega, by have := hφ (show K < K + 1 by omega); omega, ?_⟩
  intro i j
  have h1 := (dist_pi_lt_iff hε).1 hd (i, j)
  rw [dist_eq_norm] at h1
  have e : (Φ (n + φ (K + 1)) (i, j)) - (Φ (n + φ K) (i, j)) =
      ((c i * (PVG.Lac.sS (n + φ (K + 1)) - PVG.Lac.sS (n + φ K)) * x j : ℝ) : AddCircle (1 : ℝ)) := by
    simp only [Φ]
    rw [← AddCircle.coe_sub]
    congr 1
    ring
  simpa [Function.comp_def, e] using h1

/-- A finite family of recurrence witnesses serves every vector of the box. -/
theorem finite_witnesses_Q (n N : ℕ) (x : Fin N → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset (Fin n → ℝ)) (P Q : (Fin n → ℝ) → ℕ),
      (∀ c ∈ S, n ≤ Q c ∧ Q c < P c) ∧
      ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ n) →
        ∃ c₀ ∈ S, ∀ (i : Fin n) (j : Fin N),
          ‖((c i * (PVG.Lac.sS (P c₀) - PVG.Lac.sS (Q c₀)) * x j : ℝ) : AddCircle (1 : ℝ))‖ < ε := by
  classical
  have hw : ∀ c : Fin n → ℝ, ∃ p q : ℕ, n ≤ q ∧ q < p ∧ ∀ (i : Fin n) (j : Fin N),
      ‖((c i * (PVG.Lac.sS p - PVG.Lac.sS q) * x j : ℝ) : AddCircle (1 : ℝ))‖ < ε / 2 + ε / 2 := by
    intro c
    obtain ⟨p, q, hq, hpq, h⟩ := witness_Q_pointwise n N x c (by positivity : 0 < ε / 2)
    exact ⟨p, q, hq, hpq, fun i j => by linarith [h i j]⟩
  choose P Q hQ hPQ hk using hw
  let U : (Fin n → ℝ) → Set (Fin n → ℝ) := fun c =>
    {c' | ∀ (i : Fin n) (j : Fin N),
      ‖((c' i * (PVG.Lac.sS (P c) - PVG.Lac.sS (Q c)) * x j : ℝ) : AddCircle (1 : ℝ))‖ < ε}
  have hUopen : ∀ c, IsOpen (U c) := by
    intro c
    have : U c = ⋂ i : Fin n, ⋂ j : Fin N,
        {c' : Fin n → ℝ | ‖((c' i * (PVG.Lac.sS (P c) - PVG.Lac.sS (Q c)) * x j : ℝ) : AddCircle (1 : ℝ))‖ < ε} := by
      ext c'; simp [U]
    rw [this]
    refine isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j => ?_))
    refine isOpen_lt (continuous_norm.comp ?_) continuous_const
    exact (AddCircle.continuous_mk' 1).comp
      (((continuous_apply i).mul continuous_const).mul continuous_const)
  have hcU : ∀ c, c ∈ U c := by
    intro c i j
    have := hk c i j
    linarith
  have hcomp : IsCompact {c : Fin n → ℝ | ∀ i, |c i| ≤ n} := by
    have : {c : Fin n → ℝ | ∀ i, |c i| ≤ n} = Set.pi Set.univ (fun _ => Set.Icc (-(n : ℝ)) n) := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies, abs_le]
    rw [this]
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨S, -, hS⟩ := hcomp.elim_nhds_subcover U (fun c _ => (hUopen c).mem_nhds (hcU c))
  refine ⟨S, P, Q, fun c _ => ⟨hQ c, hPQ c⟩, ?_⟩
  intro c hc
  have := hS hc
  rw [Set.mem_iUnion₂] at this
  obtain ⟨c₀, hc₀, hcc₀⟩ := this
  exact ⟨c₀, hc₀, hcc₀⟩

/-- Shrinking the radius gives the recurrence property. -/
theorem exists_Q_radius (n : ℕ) (hn : 1 ≤ n) (z : ℕ → ℝ) (r' : ℝ) (hr' : 0 < r') :
    ∃ r'' : ℝ, 0 < r'' ∧ r'' ≤ r' ∧ Qprop n ⟨z, r''⟩ := by
  classical
  set m : ℝ := (n : ℝ) with hm
  have hmpos : 0 < m := by have h0 : 0 < n := hn; rw [hm]; exact_mod_cast h0
  obtain ⟨S, P, Q, hPQ, hS⟩ := finite_witnesses_Q n (2 ^ n) (fun j : Fin (2 ^ n) => z j)
    (ε := 1 / (2 * m)) (by positivity)
  set T : ℝ := ∑ c₀ ∈ S, |PVG.Lac.sS (P c₀) - PVG.Lac.sS (Q c₀)| with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set D : ℝ := 1 / (2 * m ^ 2 * (T + 1)) with hD
  have hD0 : 0 < D := by positivity
  refine ⟨min r' D, lt_min hr' hD0, min_le_left _ _, ?_⟩
  intro c hc
  obtain ⟨c₀, hc₀S, hc₀⟩ := hS c hc
  refine ⟨P c₀, Q c₀, (hPQ c₀ hc₀S).1, (hPQ c₀ hc₀S).2, ?_⟩
  intro a ha l hl i
  have hmain := hc₀ i ⟨a, ha⟩
  have hδ : |l - z a| ≤ min r' D := abs_le.2 ⟨by linarith [hl.1], by linarith [hl.2]⟩
  have hδD : |l - z a| ≤ D := hδ.trans (min_le_right _ _)
  have hΔ : |PVG.Lac.sS (P c₀) - PVG.Lac.sS (Q c₀)| ≤ T :=
    Finset.single_le_sum (f := fun c₀ => |PVG.Lac.sS (P c₀) - PVG.Lac.sS (Q c₀)|)
      (fun _ _ => abs_nonneg _) hc₀S
  have hsplit : c i * (PVG.Lac.sS (P c₀) - PVG.Lac.sS (Q c₀)) * l =
      c i * (PVG.Lac.sS (P c₀) - PVG.Lac.sS (Q c₀)) * z a +
        c i * (PVG.Lac.sS (P c₀) - PVG.Lac.sS (Q c₀)) * (l - z a) := by ring
  have hperturb : |c i * (PVG.Lac.sS (P c₀) - PVG.Lac.sS (Q c₀)) * (l - z a)| ≤ m * T * D := by
    rw [abs_mul, abs_mul]
    have hci : |c i| ≤ m := hc i
    exact mul_le_mul (mul_le_mul hci hΔ (abs_nonneg _) hmpos.le) hδD (abs_nonneg _)
      (mul_nonneg hmpos.le hT0)
  have hmTD : m * T * D < 1 / (2 * m) := by
    rw [hD]
    have hTT : T / (T + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have : m * T * (1 / (2 * m ^ 2 * (T + 1))) = (T / (T + 1)) * (1 / (2 * m)) := by
      field_simp
    rw [this]
    have : 0 < 1 / (2 * m) := by positivity
    nlinarith
  have hfin1 : ‖((c i * (PVG.Lac.sS (P c₀) - PVG.Lac.sS (Q c₀)) * l : ℝ) : AddCircle (1 : ℝ))‖ ≤
      ‖((c i * (PVG.Lac.sS (P c₀) - PVG.Lac.sS (Q c₀)) * z a : ℝ) : AddCircle (1 : ℝ))‖ +
        |c i * (PVG.Lac.sS (P c₀) - PVG.Lac.sS (Q c₀)) * (l - z a)| := by
    rw [hsplit]; exact norm_perturb _ _
  have hfin2 : 1 / (2 * m) + 1 / (2 * m) = 1 / m := by field_simp; ring
  linarith [hfin1, hfin2, hmain, hperturb, hmTD]

end Beta
end PVG
