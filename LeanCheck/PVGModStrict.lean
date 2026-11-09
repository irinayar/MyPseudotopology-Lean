import LeanCheck.PVGClusterBound
import LeanCheck.PVGSeqFU2

/-!
# PVG: the topological modification of the lacunary PVG is strictly between `τ_B` and `τ_E` (Lean check)

Scope. Corollary `modstrict` of `PVG_v19`: for `ξ = ξ_{τ_B, I_S}`, `τ_B ⊊ τ_ξ ⊊ τ_E`. With `Cl = ⋃_i {M_i h : 1 ≤ h ≤ i}`:

* `Tc_closed`: the elements of `J ∩ Cl` with a fixed label (`PVGClusterBound.cluster_label`) form a set `T_c` that is the range of a
  sequence with ratios at least `5` (consecutive layers), hence `τ_B`-closed by `lacclosed`;
* `trace_closed`: `J ∩ Cl` is `τ_B`-closed for every `J ∈ I_S` (a finite set together with finitely many sets `T_c`);
* `modstrict`: with `relaxed_strict`, `clusters` (`Cl` is not `τ_B`-closed), `lac_modTop_le_euclid` and `lac_ball_not_open`:
  `τ_B ⊆ τ_ξ ⊆ τ_E`, `τ_ξ ⊄ τ_B` and `τ_E ⊄ τ_ξ`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires mathematical
review.
-/

open Set Filter Topology
open scoped Classical

namespace PVG
namespace Lac

open Q95

/-- `Cl = ⋃_i {M_i h : 1 ≤ h ≤ i}`. -/
def Cl : Set ℝ := {x | ∃ i h : ℕ, 1 ≤ h ∧ h ≤ i ∧ x = Mi i * h}

lemma Mi_mono {i j : ℕ} (h : i ≤ j) : Mi i ≤ Mi j := by
  unfold Mi
  exact pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.pow_le_pow_left h 2])

lemma layer_ratio (i : ℕ) : 5 * ((i : ℝ) * Mi i) ≤ Mi (i + 1) := by
  have h1 : Mi (i + 1) = Mi i * 2 ^ (8 * i + 4) := by
    unfold Mi; rw [← pow_add]; congr 1; ring
  have h2 : (i : ℝ) < 2 ^ i := by exact_mod_cast Nat.lt_two_pow_self (n := i)
  have h3 : (5 : ℝ) * 2 ^ i ≤ 2 ^ (8 * i + 4) := by
    calc (5 : ℝ) * 2 ^ i ≤ 2 ^ 3 * 2 ^ i := by norm_num
      _ = 2 ^ (3 + i) := by rw [pow_add]
      _ ≤ 2 ^ (8 * i + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hM := Mi_pos i
  rw [h1]
  nlinarith

/-- The elements of `J ∩ Cl` with a fixed label, for layers `≥ i₀`. -/
def Tc (J : Set ℝ) (i0 : ℕ) (lab : ℕ → ℕ → ℝ) (c : ℝ) : Set ℝ :=
  {x | ∃ i h : ℕ, i0 ≤ i ∧ 1 ≤ h ∧ h ≤ i ∧ Mi i * h ∈ J ∧ lab i h = c ∧ x = Mi i * h}

lemma bohr_finite_closed (s : Set ℝ) (hs : s.Finite) : @IsClosed ℝ bohrTop s := by
  letI : TopologicalSpace ℝ := bohrTop
  haveI := bohr_t2
  exact hs.isClosed

theorem Tc_closed {J : Set ℝ} {i0 : ℕ} {lab : ℕ → ℕ → ℝ}
    (hinj : ∀ i, i0 ≤ i → ∀ h h' : ℕ, 1 ≤ h → h ≤ i → 1 ≤ h' → h' ≤ i → Mi i * h ∈ J → Mi i * h' ∈ J →
        lab i h = lab i h' → h = h') (c : ℝ) : @IsClosed ℝ bohrTop (Tc J i0 lab c) := by
  set p : ℕ → Prop := fun i => i0 ≤ i ∧ ∃ h : ℕ, 1 ≤ h ∧ h ≤ i ∧ Mi i * h ∈ J ∧ lab i h = c with hp
  by_cases hfin : (setOf p).Finite
  · refine bohr_finite_closed _ (Set.Finite.subset
      (hfin.biUnion (fun i _ => ((Set.finite_Icc 1 i).image (fun h : ℕ => Mi i * (h : ℝ))))) ?_)
    rintro x ⟨i, h, hi0, h1, hhi, hJ, hlab, rfl⟩
    simp only [Set.mem_iUnion]
    exact ⟨i, ⟨hi0, h, h1, hhi, hJ, hlab⟩, h, ⟨h1, hhi⟩, rfl⟩
  · have hinf : (setOf p).Infinite := hfin
    have hsel : ∀ i, p i → ∃ h : ℕ, 1 ≤ h ∧ h ≤ i ∧ Mi i * h ∈ J ∧ lab i h = c := fun i hi => hi.2
    choose! hh hhs using hsel
    set φ : ℕ → ℕ := Nat.nth p with hφ
    have hφm : StrictMono φ := Nat.nth_strictMono hinf
    have hpφ : ∀ j, p (φ j) := fun j => Nat.nth_mem_of_infinite hinf j
    set t : ℕ → ℝ := fun j => Mi (φ j) * (hh (φ j) : ℝ) with ht
    have hrange : Tc J i0 lab c = Set.range t := by
      ext x
      constructor
      · rintro ⟨i, h, hi0, h1, hhi, hJ, hlab, rfl⟩
        have hpi : p i := ⟨hi0, h, h1, hhi, hJ, hlab⟩
        have hmem : i ∈ Set.range (Nat.nth p) := by rw [Nat.range_nth_of_infinite hinf]; exact hpi
        obtain ⟨j, hj⟩ := hmem
        obtain ⟨hh1, hh2, hh3, hh4⟩ := hhs i hpi
        have : h = hh i := hinj i hi0 h (hh i) h1 hhi hh1 hh2 hJ hh3 (hlab.trans hh4.symm)
        refine ⟨j, ?_⟩
        show Mi (φ j) * (hh (φ j) : ℝ) = Mi i * h
        rw [show φ j = i from hj, ← this]
      · rintro ⟨j, rfl⟩
        obtain ⟨hh1, hh2, hh3, hh4⟩ := hhs (φ j) (hpφ j)
        exact ⟨φ j, hh (φ j), (hpφ j).1, hh1, hh2, hh3, hh4, rfl⟩
    rw [hrange]
    have hpos : ∀ j, 0 < t j := by
      intro j
      obtain ⟨hh1, _⟩ := hhs (φ j) (hpφ j)
      exact mul_pos (Mi_pos _) (by exact_mod_cast hh1)
    refine lacclosed t (hpos 0).ne' (fun j => ?_)
    obtain ⟨h1, h2, _⟩ := hhs (φ j) (hpφ j)
    obtain ⟨h1', _⟩ := hhs (φ (j + 1)) (hpφ (j + 1))
    have hk : φ j + 1 ≤ φ (j + 1) := hφm (Nat.lt_succ_self j)
    have hMk := Mi_mono hk
    have hr := layer_ratio (φ j)
    have hh2R : (hh (φ j) : ℝ) ≤ φ j := by exact_mod_cast h2
    have hh1R : (1 : ℝ) ≤ hh (φ (j + 1)) := by exact_mod_cast h1'
    rw [abs_of_pos (hpos j), abs_of_pos (hpos (j + 1))]
    show 5 * (Mi (φ j) * (hh (φ j) : ℝ)) ≤ Mi (φ (j + 1)) * (hh (φ (j + 1)) : ℝ)
    have hM1 := Mi_pos (φ j)
    have hM2 := Mi_pos (φ (j + 1))
    nlinarith [mul_le_mul_of_nonneg_left hh2R hM1.le]

/-- For every `J ∈ I_S`, the trace `J ∩ Cl` is `τ_B`-closed. -/
theorem trace_closed {J : Set ℝ} (hJ : J ∈ IS) : @IsClosed ℝ bohrTop (J ∩ Cl) := by
  obtain ⟨i0, Cf, lab, hmap, hinj⟩ := cluster_label hJ
  have heq : J ∩ Cl = {x | ∃ i h : ℕ, i < i0 ∧ 1 ≤ h ∧ h ≤ i ∧ x = Mi i * h ∧ x ∈ J} ∪
      ⋃ c ∈ Cf, Tc J i0 lab c := by
    ext x
    constructor
    · rintro ⟨hxJ, i, h, h1, hhi, rfl⟩
      by_cases hi : i < i0
      · exact Or.inl ⟨i, h, hi, h1, hhi, rfl, hxJ⟩
      · push Not at hi
        refine Or.inr (Set.mem_iUnion₂.2 ⟨lab i h, hmap i hi h h1 hhi hxJ, i, h, hi, h1, hhi, hxJ, rfl, rfl⟩)
    · rintro (⟨i, h, hi, h1, hhi, rfl, hxJ⟩ | hx)
      · exact ⟨hxJ, i, h, h1, hhi, rfl⟩
      · obtain ⟨c, -, hc⟩ := Set.mem_iUnion₂.1 hx
        obtain ⟨i, h, hi0, h1, hhi, hxJ, -, rfl⟩ := hc
        exact ⟨hxJ, i, h, h1, hhi, rfl⟩
  rw [heq]
  letI : TopologicalSpace ℝ := bohrTop
  refine IsClosed.union ?_ ?_
  · refine bohr_finite_closed _ (Set.Finite.subset
      ((Set.finite_Iio i0).biUnion (fun i _ => ((Set.finite_Icc 1 i).image (fun h : ℕ => Mi i * (h : ℝ))))) ?_)
    rintro x ⟨i, h, hi, h1, hhi, rfl, -⟩
    simp only [Set.mem_iUnion]
    exact ⟨i, hi, h, ⟨h1, hhi⟩, rfl⟩
  · exact isClosed_biUnion_finset (fun c _ => Tc_closed hinj c)

/-- **Corollary `modstrict`**: `τ_B ⊊ τ_ξ ⊊ τ_E` for `ξ = ξ_{τ_B, I_S}`. -/
theorem modstrict :
    (∀ U : Set ℝ, @IsOpen ℝ bohrTop U → @IsOpen ℝ (modTop lacConv) U) ∧
    (∃ U : Set ℝ, @IsOpen ℝ (modTop lacConv) U ∧ ¬ @IsOpen ℝ bohrTop U) ∧
    (∀ U : Set ℝ, @IsOpen ℝ (modTop lacConv) U → IsOpen U) ∧
    (∃ U : Set ℝ, IsOpen U ∧ ¬ @IsOpen ℝ (modTop lacConv) U) := by
  refine ⟨?_, ?_, fun U hU => lac_modTop_le_euclid hU, ⟨Metric.ball (0 : ℝ) 1, Metric.isOpen_ball, lac_ball_not_open⟩⟩
  · intro U hU
    letI : TopologicalSpace ℝ := bohrTop
    haveI := bohr_isTopologicalAddGroup
    haveI := bohr_constSMul
    exact beta_open_mod (I := IS) hU
  · letI : TopologicalSpace ℝ := bohrTop
    haveI := bohr_isTopologicalAddGroup
    haveI := bohr_constSMul
    have hnot : ¬ IsClosed Cl := by
      intro hcl
      obtain ⟨h0, hcls⟩ := clusters Mi (fun i => Mi_pos i) (fun i => i) tendsto_id
      have hcls' : (0 : ℝ) ∈ closure Cl := hcls
      rw [hcl.closure_eq] at hcls'
      exact h0 hcls'
    exact relaxed_strict (I := IS) (fun J hJ => trace_closed hJ) hnot

#print axioms Tc_closed
#print axioms trace_closed
#print axioms modstrict

end Lac
end PVG
