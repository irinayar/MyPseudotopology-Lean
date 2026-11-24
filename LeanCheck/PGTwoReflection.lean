import Mathlib
import LeanCheck.PGNullFilters
import LeanCheck.PGTwoGeneration
import LeanCheck.PGTwoLattice

/-!
# PGtwo: reflection of a PG into the topological groups (Lean check)

Scope. Section 5 of the second article (`PGtwo.tex`), Lemma 5.1, Theorem 5.4 and Theorem 5.2, abstract form.
Let `C` be a null family on the abelian group `G` (a PG, `PGNullFilters`).

* `vic C = sSup C` : the vicinity filter `V` (the sets belonging to every null filter); `vic_zero_mem`, `vic_neg`,
  `vic_le_add` : Lemma 5.1(a),(b);
* `IsNbhdFilter N` : `N` is the neighbourhood filter of `0` of a group topology; `exists_topology` and `nhds_zero_isNbhdFilter`
  show that the two descriptions agree (via Mathlib's `AddGroupFilterBasis`);
* `halveFilter V` : the filter of sets admitting a halving sequence in `V` (Definition 5.3);
  `isNbhdFilter_halveFilter`, `le_halveFilter`, `halveFilter_le` : Theorem 5.4 (it is the neighbourhood filter of the finest
  group topology in which the null filters converge to `0`, and it is the largest filter below `V` of this kind);
* `Elig C t` : `t` is a group topology in which every null filter converges to `0`; `IsFinest`;
  `exists_finest` : a finest such topology exists (Theorem 5.2);
* `reflector_univ` : a homomorphism `f` into a topological group sends the null filters to filters converging to `0`
  if and only if it is continuous for the finest topology (the universal property of the reflector).

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology Pointwise

namespace PG

variable {G : Type*} [AddCommGroup G]

/-- The vicinity filter: the sets belonging to every null filter. -/
def vic (C : Set (Filter G)) : Filter G := sSup C

theorem mem_vic {C : Set (Filter G)} {s : Set G} : s ∈ vic C ↔ ∀ F ∈ C, s ∈ F :=
  Filter.mem_sSup

theorem le_vic {C : Set (Filter G)} {F : Filter G} (hF : F ∈ C) : F ≤ vic C := le_sSup hF

/-- Lemma 5.1(a): every member of the vicinity filter contains `0`. -/
theorem vic_zero_mem {C : Set (Filter G)} (hC : NullFamily C) {s : Set G} (hs : s ∈ vic C) : (0 : G) ∈ s :=
  mem_vic.1 hs (pure 0) hC.pure_zero

/-- Lemma 5.1(a): the vicinity filter is symmetric. -/
theorem vic_neg {C : Set (Filter G)} (hC : NullFamily C) {s : Set G} (hs : s ∈ vic C) :
    (fun x : G => -x) ⁻¹' s ∈ vic C := by
  rw [mem_vic] at hs ⊢
  intro F hF
  exact hs _ (hC.neg F hF)

/-- Lemma 5.1(b): `V + V ⊆ V` (every member of the filter sum belongs to `V`). -/
theorem vic_le_add {C : Set (Filter G)} (hC : NullFamily C) :
    vic C ≤ Filter.map₂ (· + ·) (vic C) (vic C) := by
  intro s hs
  obtain ⟨a, ha, b, hb, hab⟩ := Filter.mem_map₂_iff.1 hs
  refine Filter.mem_of_superset ha ?_
  intro x hx
  exact hab ⟨x, hx, 0, vic_zero_mem hC hb, by simp⟩

/-- A filter that is the neighbourhood filter of `0` of a group topology. -/
structure IsNbhdFilter (N : Filter G) : Prop where
  zero_mem : ∀ A ∈ N, (0 : G) ∈ A
  neg_mem : ∀ A ∈ N, (fun x : G => -x) ⁻¹' A ∈ N
  halve : ∀ A ∈ N, ∃ B ∈ N, ∀ x ∈ B, ∀ y ∈ B, x + y ∈ A

/-- The filter basis of an `IsNbhdFilter`. -/
def basisOf (N : Filter G) (h : IsNbhdFilter N) : AddGroupFilterBasis G where
  sets := {s | s ∈ N}
  nonempty := ⟨univ, Filter.univ_mem⟩
  inter_sets := fun hx hy => ⟨_, Filter.inter_mem hx hy, subset_rfl⟩
  zero' := fun {U} hU => h.zero_mem U hU
  add' := fun {U} hU => by
    obtain ⟨B, hB, hBU⟩ := h.halve U hU
    refine ⟨B, hB, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hBU x hx y hy
  neg' := fun {U} hU => ⟨(fun x : G => -x) ⁻¹' U, h.neg_mem U hU, subset_rfl⟩
  conj' := fun x₀ {U} hU => ⟨U, hU, by
    intro x hx
    show x₀ + x + -x₀ ∈ U
    have : x₀ + x + -x₀ = x := by abel
    rw [this]; exact hx⟩

/-- A neighbourhood filter is the neighbourhood filter of `0` of a group topology. -/
theorem exists_topology {N : Filter G} (h : IsNbhdFilter N) :
    ∃ t : TopologicalSpace G, @IsTopologicalAddGroup G t _ ∧ @nhds G t 0 = N := by
  refine ⟨(basisOf N h).topology, (basisOf N h).isTopologicalAddGroup, ?_⟩
  rw [AddGroupFilterBasis.nhds_zero_eq]
  ext s
  rw [FilterBasis.mem_filter_iff]
  constructor
  · rintro ⟨t, ht, hts⟩
    exact Filter.mem_of_superset ht hts
  · intro hs
    exact ⟨s, hs, subset_rfl⟩

/-- The neighbourhood filter of `0` in a topological group is an `IsNbhdFilter`. -/
theorem nhds_zero_isNbhdFilter [TopologicalSpace G] [IsTopologicalAddGroup G] :
    IsNbhdFilter (𝓝 (0 : G)) where
  zero_mem := fun A hA => mem_of_mem_nhds hA
  neg_mem := fun A hA => by
    have hc : ContinuousAt (fun x : G => -x) 0 := continuous_neg.continuousAt
    apply hc.preimage_mem_nhds
    rw [neg_zero]; exact hA
  halve := fun A hA => exists_nhds_zero_half hA

/-- The filter of sets admitting a halving sequence in `V` (Definition 5.3). -/
def halveFilter (V : Filter G) : Filter G where
  sets := {A | ∃ S : ℕ → Set G, (∀ n, S n ∈ V) ∧ S 0 ⊆ A ∧
    ∀ n, ∀ x ∈ S (n + 1), ∀ y ∈ S (n + 1), x + y ∈ S n}
  univ_sets := ⟨fun _ => univ, fun _ => Filter.univ_mem, subset_univ _, fun _ _ _ _ _ => trivial⟩
  sets_of_superset := by
    rintro A B ⟨S, hS, h0, hh⟩ hAB
    exact ⟨S, hS, h0.trans hAB, hh⟩
  inter_sets := by
    rintro A B ⟨S, hS, h0, hh⟩ ⟨T, hT, h0', hh'⟩
    refine ⟨fun n => S n ∩ T n, fun n => Filter.inter_mem (hS n) (hT n),
      Set.inter_subset_inter h0 h0', ?_⟩
    intro n x hx y hy
    exact ⟨hh n x hx.1 y hy.1, hh' n x hx.2 y hy.2⟩

theorem mem_halveFilter {V : Filter G} {A : Set G} :
    A ∈ halveFilter V ↔ ∃ S : ℕ → Set G, (∀ n, S n ∈ V) ∧ S 0 ⊆ A ∧
      ∀ n, ∀ x ∈ S (n + 1), ∀ y ∈ S (n + 1), x + y ∈ S n := Iff.rfl

/-- The vicinity filter is below its halving filter: every set admitting a halving sequence in `V` belongs to `V`. -/
theorem le_halveFilter (V : Filter G) : V ≤ halveFilter V := by
  rintro A ⟨S, hS, h0, _⟩
  exact Filter.mem_of_superset (hS 0) h0

/-- Theorem 5.4: for a symmetric filter `V` whose members contain `0`, `halveFilter V` is the neighbourhood filter of
`0` of a group topology. -/
theorem isNbhdFilter_halveFilter {V : Filter G} (h0 : ∀ A ∈ V, (0 : G) ∈ A)
    (hneg : ∀ A ∈ V, (fun x : G => -x) ⁻¹' A ∈ V) : IsNbhdFilter (halveFilter V) where
  zero_mem := by
    rintro A ⟨S, hS, hA, _⟩
    exact hA (h0 _ (hS 0))
  neg_mem := by
    rintro A ⟨S, hS, hA, hh⟩
    refine ⟨fun n => (fun x : G => -x) ⁻¹' S n, fun n => hneg _ (hS n), ?_, ?_⟩
    · intro x hx
      exact hA hx
    · intro n x hx y hy
      show -(x + y) ∈ S n
      have : -(x + y) = -x + -y := by abel
      rw [this]
      exact hh n _ hx _ hy
  halve := by
    rintro A ⟨S, hS, hA, hh⟩
    refine ⟨S 1, ⟨fun n => S (n + 1), fun n => hS (n + 1), subset_rfl, fun n => hh (n + 1)⟩, ?_⟩
    intro x hx y hy
    exact hA (hh 0 x hx y hy)

/-- Theorem 5.4 (maximality): a filter `N` of the above kind with `V ≤ N` (every member of `N` belongs to `V`) satisfies
`halveFilter V ≤ N` (every member of `N` admits a halving sequence in `V`). -/
theorem halveFilter_le {V N : Filter G} (hN : IsNbhdFilter N) (hVN : V ≤ N) : halveFilter V ≤ N := by
  intro A hA
  classical
  let step : {B : Set G // B ∈ N} → {B : Set G // B ∈ N} := fun b =>
    ⟨Classical.choose (hN.halve b.1 b.2), (Classical.choose_spec (hN.halve b.1 b.2)).1⟩
  let seq : ℕ → {B : Set G // B ∈ N} := fun n => step^[n] ⟨A, hA⟩
  refine ⟨fun n => (seq n).1, fun n => hVN (seq n).2, ?_, ?_⟩
  · exact subset_rfl
  · intro n x hx y hy
    have hs : seq (n + 1) = step (seq n) := Function.iterate_succ_apply' step n ⟨A, hA⟩
    have hx' : x ∈ (step (seq n)).1 := by rw [← hs]; exact hx
    have hy' : y ∈ (step (seq n)).1 := by rw [← hs]; exact hy
    exact (Classical.choose_spec (hN.halve (seq n).1 (seq n).2)).2 x hx' y hy'

/-- A homomorphism between topological groups that is continuous at `0` is continuous. -/
theorem hom_continuous_of_zero {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [TopologicalSpace G] [IsTopologicalAddGroup G] (f : G →+ H)
    (h : Tendsto f (𝓝 0) (𝓝 0)) : Continuous f :=
  continuous_of_continuousAt_zero f (by rw [ContinuousAt, map_zero]; exact h)

/-- A group topology in which every null filter converges to `0`. -/
def Elig (C : Set (Filter G)) (t : TopologicalSpace G) : Prop :=
  @IsTopologicalAddGroup G t _ ∧ ∀ F ∈ C, F ≤ @nhds G t 0

/-- A finest eligible topology: every other eligible topology is coarser. -/
def IsFinest (C : Set (Filter G)) (t : TopologicalSpace G) : Prop :=
  Elig C t ∧ ∀ t' : TopologicalSpace G, Elig C t' → @Continuous G G t t' id

theorem vic_le_nhds {C : Set (Filter G)} {t : TopologicalSpace G} (h : ∀ F ∈ C, F ≤ @nhds G t 0) :
    vic C ≤ @nhds G t 0 := sSup_le h

/-- Theorem 5.2: a finest group topology in which the null filters converge to `0` exists, and its neighbourhood
filter of `0` is `halveFilter (vic C)` (Theorem 5.4). -/
theorem exists_finest {C : Set (Filter G)} (hC : NullFamily C) :
    ∃ t : TopologicalSpace G, IsFinest C t ∧ @nhds G t 0 = halveFilter (vic C) := by
  have hN : IsNbhdFilter (halveFilter (vic C)) :=
    isNbhdFilter_halveFilter (fun A hA => vic_zero_mem hC hA) (fun A hA => vic_neg hC hA)
  obtain ⟨t, ht, hnhds⟩ := exists_topology hN
  refine ⟨t, ⟨⟨ht, fun F hF => ?_⟩, fun t' ht' => ?_⟩, hnhds⟩
  · rw [hnhds]; exact (le_vic hF).trans (le_halveFilter _)
  · obtain ⟨ht'g, ht'F⟩ := ht'
    have hle : halveFilter (vic C) ≤ @nhds G t' 0 :=
      halveFilter_le (@nhds_zero_isNbhdFilter G _ t' ht'g) (vic_le_nhds ht'F)
    have h : @Tendsto G G (⇑(AddMonoidHom.id G)) (@nhds G t 0) (@nhds G t' 0) := by
      rw [hnhds]; exact hle
    exact @hom_continuous_of_zero G _ G _ t' ht'g t ht (AddMonoidHom.id G) h

/-- Theorem 5.2 (universal property of the reflector): a homomorphism `f` into a topological group sends the null
filters to filters converging to `0` if and only if it is continuous for a finest eligible topology. -/
theorem reflector_univ {C : Set (Filter G)} {t₀ : TopologicalSpace G} (h₀ : IsFinest C t₀)
    {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] (f : G →+ H) :
    (∀ F ∈ C, Filter.map f F ≤ 𝓝 (0 : H)) ↔ @Continuous G H t₀ _ f := by
  constructor
  · intro hf
    have hσg : @IsTopologicalAddGroup G (TopologicalSpace.induced f inferInstance) _ :=
      topologicalAddGroup_induced f
    have hσ : Elig C (TopologicalSpace.induced f inferInstance) := by
      refine ⟨hσg, fun F hF => ?_⟩
      rw [nhds_induced, map_zero]
      exact Filter.map_le_iff_le_comap.1 (hf F hF)
    have hid := h₀.2 _ hσ
    have hfσ : @Continuous G H (TopologicalSpace.induced f inferInstance) _ f := continuous_induced_dom
    exact @Continuous.comp G G H t₀ (TopologicalSpace.induced f inferInstance) _ _ _ hfσ hid
  · intro hf F hF
    have hF0 := h₀.1.2 F hF
    have hc : @ContinuousAt G H t₀ _ f 0 := @Continuous.continuousAt G H t₀ _ f 0 hf
    have h1 : Filter.map f (@nhds G t₀ 0) ≤ 𝓝 (0 : H) := by
      have := hc.tendsto
      rwa [map_zero] at this
    exact (Filter.map_mono hF0).trans h1

end PG
