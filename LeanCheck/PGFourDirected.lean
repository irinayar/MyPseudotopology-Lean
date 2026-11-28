import Mathlib
import LeanCheck.PGFourAllGroups

/-!
# PGfour: the group topologies below the PG of a topology and an ideal

`K` consists of the group topologies all of whose convergent filters converge for the PG of `β` and `I`.

* `directed` : two members of `K` have a greatest lower bound among group topologies, and it belongs to `K`;
* `no_minimal` : for a sparse sequence, `K` has no minimal member;
* `chain` : the column unions give a strictly coarsening sequence in `K` with no common coarser member of `K`.

In Mathlib's order, `σ ≤ τ` means that `σ` is finer than `τ`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology Pointwise

noncomputable section

namespace PG.NoCoreAll

open PG.NoCore (col column_infinite)

variable {G : Type*} [AddCommGroup G]

/-- Membership in `K`. -/
def InK (β : TopologicalSpace G) (J : Set (Set G)) (σ : TopologicalSpace G) : Prop :=
  @IsTopologicalAddGroup G σ _ ∧ ∀ x : G, @xi G β J (@nhds G σ x) x

/-- Two members of `K` have a greatest lower bound, again in `K`. -/
theorem directed (β : TopologicalSpace G) (hβ : @IsTopologicalAddGroup G β _) (J : Set (Set G))
    (hJ : AdmIdeal J) (σ τ : TopologicalSpace G) (hσ : InK β J σ) (hτ : InK β J τ) :
    ∃ μ : TopologicalSpace G, InK β J μ ∧ σ ≤ μ ∧ τ ≤ μ ∧
      ∀ ν : TopologicalSpace G, @IsTopologicalAddGroup G ν _ → σ ≤ ν → τ ≤ ν → μ ≤ ν := by
  classical
  have hσg := hσ.1
  have hτg := hτ.1
  -- the base of the sums `U + V`
  let S : Set (Set G) := {W | ∃ U ∈ @nhds G σ 0, ∃ V ∈ @nhds G τ 0, W = U + V}
  have half : ∀ (t : TopologicalSpace G), @IsTopologicalAddGroup G t _ → ∀ U ∈ @nhds G t 0,
      ∃ U' ∈ @nhds G t 0, U' + U' ⊆ U ∧ ∀ x ∈ U', -x ∈ U := by
    intro t ht U hU
    letI := t
    haveI := ht
    obtain ⟨U1, hU1o, hU10, hU1⟩ := exists_open_nhds_zero_add_subset hU
    have h2 : (fun x : G => -x) ⁻¹' U ∈ 𝓝 (0 : G) := by
      have : Tendsto (fun x : G => -x) (𝓝 0) (𝓝 0) := (continuous_neg.tendsto' 0 0 neg_zero)
      exact this hU
    refine ⟨U1 ∩ (fun x : G => -x) ⁻¹' U, inter_mem (hU1o.mem_nhds hU10) h2, ?_, fun x hx => hx.2⟩
    exact (add_subset_add inter_subset_left inter_subset_left).trans hU1
  have h0 : ∀ (t : TopologicalSpace G) (U : Set G), U ∈ @nhds G t 0 → (0 : G) ∈ U := fun t U hU =>
    @mem_of_mem_nhds G t 0 U hU
  let B : AddGroupFilterBasis G := addGroupFilterBasisOfComm S
    ⟨_, univ, univ_mem, univ, univ_mem, rfl⟩
    (by
      rintro _ _ ⟨U1, hU1, V1, hV1, rfl⟩ ⟨U2, hU2, V2, hV2, rfl⟩
      refine ⟨(U1 ∩ U2) + (V1 ∩ V2), ⟨_, inter_mem hU1 hU2, _, inter_mem hV1 hV2, rfl⟩, ?_⟩
      exact subset_inter (add_subset_add inter_subset_left inter_subset_left)
        (add_subset_add inter_subset_right inter_subset_right))
    (by
      rintro _ ⟨U, hU, V, hV, rfl⟩
      exact ⟨0, h0 σ U hU, 0, h0 τ V hV, add_zero 0⟩)
    (by
      rintro _ ⟨U, hU, V, hV, rfl⟩
      obtain ⟨U', hU', hUU, _⟩ := half σ hσg U hU
      obtain ⟨V', hV', hVV, _⟩ := half τ hτg V hV
      refine ⟨U' + V', ⟨U', hU', V', hV', rfl⟩, ?_⟩
      rw [add_add_add_comm]
      exact add_subset_add hUU hVV)
    (by
      rintro _ ⟨U, hU, V, hV, rfl⟩
      obtain ⟨U', hU', _, hUn⟩ := half σ hσg U hU
      obtain ⟨V', hV', _, hVn⟩ := half τ hτg V hV
      refine ⟨U' + V', ⟨U', hU', V', hV', rfl⟩, ?_⟩
      rintro _ ⟨u, hu, v, hv, rfl⟩
      show -(u + v) ∈ U + V
      rw [neg_add]
      exact add_mem_add (hUn u hu) (hVn v hv))
  set μ : TopologicalSpace G := B.topology with hμ
  have hμg : @IsTopologicalAddGroup G μ _ := B.isTopologicalAddGroup
  have hμnhds : ∀ x : G, ∀ s : Set G, s ∈ @nhds G μ x ↔ ∃ W ∈ S, (fun z => x + z) '' W ⊆ s := by
    intro x s
    exact (B.nhds_hasBasis x).mem_iff
  -- translations of neighbourhoods in a group topology
  have htr : ∀ (t : TopologicalSpace G), @IsTopologicalAddGroup G t _ → ∀ x : G, ∀ s : Set G,
      s ∈ @nhds G t x ↔ (fun z => x + z) ⁻¹' s ∈ @nhds G t 0 := by
    intro t ht x s
    letI := t
    haveI := ht
    rw [← map_add_left_nhds_zero x, mem_map]
  have hle : ∀ (t : TopologicalSpace G), @IsTopologicalAddGroup G t _ →
      (∀ W ∈ S, W ∈ @nhds G t 0) → t ≤ μ := by
    intro t ht h
    refine le_of_nhds_le_nhds fun x => ?_
    intro s hs
    obtain ⟨W, hW, hsub⟩ := (hμnhds x s).1 hs
    refine (htr t ht x s).2 (mem_of_superset (h W hW) fun z hz => hsub ⟨z, hz, rfl⟩)
  have hσμ : σ ≤ μ := hle σ hσg fun W hW => by
    obtain ⟨U, hU, V, hV, rfl⟩ := hW
    exact mem_of_superset hU fun u hu => ⟨u, hu, 0, h0 τ V hV, add_zero u⟩
  have hτμ : τ ≤ μ := hle τ hτg fun W hW => by
    obtain ⟨U, hU, V, hV, rfl⟩ := hW
    exact mem_of_superset hV fun v hv => ⟨0, h0 σ U hU, v, hv, zero_add v⟩
  -- finer than `β`, with a member of the ideal
  obtain ⟨_, hσβ, A1, hA1, hA1n⟩ := hσ.2 0
  obtain ⟨_, hτβ, A2, hA2, hA2n⟩ := hτ.2 0
  have hμβ : ∀ x : G, @nhds G μ x ≤ @nhds G β x := by
    intro x s hs
    have h1 : (fun z => x + z) ⁻¹' s ∈ @nhds G β 0 := (htr β hβ x s).1 hs
    obtain ⟨Wh, hWh, hWW, _⟩ := half β hβ _ h1
    refine (hμnhds x s).2 ⟨Wh + Wh, ⟨Wh, hσβ hWh, Wh, hτβ hWh, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hWW hz
  have hμI : ∀ x : G, ∃ C ∈ J, C ∈ @nhds G μ x := by
    intro x
    refine ⟨{x} + (A1 + A2), hJ.add _ (hJ.single x) _ (hJ.add _ hA1 _ hA2), ?_⟩
    refine (hμnhds x _).2 ⟨A1 + A2, ⟨A1, hA1n, A2, hA2n, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact add_mem_add (mem_singleton x) hz
  refine ⟨μ, ⟨hμg, fun x => ⟨@nhds_neBot G μ x, hμβ x, hμI x⟩⟩, hσμ, hτμ, fun ν hν hσν hτν => ?_⟩
  refine le_of_nhds_le_nhds fun x => ?_
  intro s hs
  have h1 : (fun z => x + z) ⁻¹' s ∈ @nhds G ν 0 := (htr ν hν x s).1 hs
  obtain ⟨Wh, hWh, hWW, _⟩ := half ν hν _ h1
  refine (hμnhds x s).2 ⟨Wh + Wh, ⟨Wh, nhds_mono hσν hWh, Wh, nhds_mono hτν hWh, rfl⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hWW hz

variable {y : ℕ → G}

/-- The column topologies belong to `K`. -/
theorem top_inK (J : Set ℕ) (m r : ℕ) (hJ : V y J 0 ⊆ A y m r) : InK (top y univ) (I y) (top y J) := by
  refine ⟨top_group J, fun x => ?_⟩
  letI := top y univ
  refine ⟨?_, ?_, {x} + A y m r, ⟨{x}, finite_singleton x, m, r, subset_rfl⟩, ?_⟩
  · exact @nhds_neBot G (top y J) x
  · refine ((top_nhds _ x).le_basis_iff (top_nhds univ x)).2 fun k _ => ⟨k, trivial, ?_⟩
    exact image_mono (V_set (subset_univ _) k)
  · refine (top_nhds _ x).mem_iff.2 ⟨0, trivial, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact add_mem_add (mem_singleton x) (hJ hz)

/-- For a sparse sequence no member of `K` is minimal. -/
theorem no_minimal (hy : Sparse y) (σ : TopologicalSpace G) (hσ : InK (top y univ) (I y) σ) :
    ∃ τ : TopologicalSpace G, InK (top y univ) (I y) τ ∧ σ ≤ τ ∧ ¬ τ ≤ σ := by
  by_contra hno
  push Not at hno
  refine no_coarsest hy ⟨σ, hσ.1, hσ.2, fun τ hτg hτc => ?_⟩
  obtain ⟨μ, hμ, hσμ, hτμ, _⟩ := directed (top y univ) (top_group univ) (I y) (admissible hy) σ τ hσ ⟨hτg, hτc⟩
  exact le_trans hτμ (hno μ hμ hσμ)

/-- The topology of the first `l + 1` columns. -/
@[instance_reducible] def theta (y : ℕ → G) (l : ℕ) : TopologicalSpace G := top y {n | col n ≤ l}

theorem V_sub_A (l : ℕ) : V y {n | col n ≤ l} 0 ⊆ A y l 1 := by
  rintro z ⟨c, h1, h2, h3⟩
  refine ⟨c, fun n hn => (h1 n hn).1, fun n => ?_, h3⟩
  simpa using h2 n

theorem not_nhds_theta (hy : Sparse y) (F : Set G) (hF : F.Finite) (m r : ℕ) (l : ℕ) (hl : m < l)
    (S : Set G) (hS : S ⊆ F + A y m r) : S ∉ @nhds G (theta y l) 0 := by
  intro h
  obtain ⟨k, _, hk⟩ := (top_nhds {n | col n ≤ l} 0).mem_iff.1 h
  have hsub : {n | col n = m + 1} \ Iio k ⊆ {n | col n = m + 1 ∧ y n ∈ F + A y m r} := by
    rintro n ⟨hn, hnk⟩
    refine ⟨hn, hS (hk ⟨y n, ?_, zero_add _⟩)⟩
    refine ⟨Finsupp.single n 1, fun i hi => ?_, fun i => ?_, by rw [val_single, one_zsmul]⟩
    · have : n = i := by
        by_contra h
        exact hi (Finsupp.single_eq_of_ne (Ne.symm h))
      subst this
      refine ⟨?_, not_lt.1 hnk⟩
      show col n ≤ l
      have h1 : col n = m + 1 := hn
      omega
    · by_cases h : n = i
      · subst h
        rw [Finsupp.single_eq_same, abs_one]
        exact one_le_pow₀ (by norm_num)
      · rw [Finsupp.single_eq_of_ne (Ne.symm h), abs_zero]
        positivity
  exact (column_infinite (m + 1)).sdiff (finite_Iio k) ((few_terms hy F hF m r).subset hsub)

/-- A strictly coarsening sequence in `K` without a common coarser member of `K`. -/
theorem chain (hy : Sparse y) :
    (∀ l, InK (top y univ) (I y) (theta y l)) ∧ (∀ l, theta y l ≤ theta y (l + 1)) ∧
      (∀ l, ¬ theta y (l + 1) ≤ theta y l) ∧
      ¬ ∃ ν : TopologicalSpace G, InK (top y univ) (I y) ν ∧ ∀ l, theta y l ≤ ν := by
  have hK : ∀ l, InK (top y univ) (I y) (theta y l) := fun l => top_inK _ l 1 (V_sub_A l)
  have hmono : ∀ l, theta y l ≤ theta y (l + 1) := by
    intro l
    refine le_of_nhds_le_nhds fun x => ?_
    refine ((top_nhds {n | col n ≤ l} x).le_basis_iff (top_nhds {n | col n ≤ l + 1} x)).2
      fun k _ => ⟨k, trivial, image_mono (V_set (fun n hn => ?_) k)⟩
    exact le_trans hn (Nat.le_succ l)
  refine ⟨hK, hmono, fun l h => ?_, ?_⟩
  · have h1 : V y {n | col n ≤ l} 0 ∈ @nhds G (theta y l) 0 := by
      refine (top_nhds {n | col n ≤ l} 0).mem_iff.2 ⟨0, trivial, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      simpa using hz
    have h2 := nhds_mono h h1
    refine not_nhds_theta hy {0} (finite_singleton 0) l 1 (l + 1) (Nat.lt_succ_self l) _ ?_ h2
    intro z hz
    exact ⟨0, rfl, z, V_sub_A l hz, zero_add z⟩
  · rintro ⟨ν, hν, hle⟩
    obtain ⟨_, _, S, ⟨F, hF, m, r, hS⟩, hSn⟩ := hν.2 0
    exact not_nhds_theta hy F hF m r (m + 1) (Nat.lt_succ_self m) S hS (nhds_mono (hle (m + 1)) hSn)

end PG.NoCoreAll
