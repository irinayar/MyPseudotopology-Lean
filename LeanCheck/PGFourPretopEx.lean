import Mathlib
import LeanCheck.PGXi

/-!
# PGfour: the two hypotheses of `PGFourPretop` cannot be omitted

`ι` is an uncountable set and `G = ι →₀ ZMod 2`.

* First example (`Countably`): the topology of pointwise convergence and the sets whose members are supported in one
  countable set. The topology has countable tightness, the ideal is not countably generated, `ξ` is not
  pretopological, and every vicinity set is a neighbourhood of `0`.
* Second example (`Bounded`): the group topology whose neighbourhoods of `0` are given by vanishing on a countable set,
  and the sets with supports of bounded size. The ideal is countably generated, `ξ` is not pretopological, and every
  vicinity set is a neighbourhood of `0`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

noncomputable section

namespace PG.PretopEx

variable {ι : Type*}

/-- Every choice of points indexed by finite sets has a countable set closed under it. -/
theorem exists_countable_closed (f : Finset ι → (ι →₀ ZMod 2)) :
    ∃ C : Set ι, C.Countable ∧ ∀ E : Finset ι, (E : Set ι) ⊆ C → ((f E).support : Set ι) ⊆ C := by
  classical
  let step : Set ι → Set ι := fun D => D ∪ ⋃ E ∈ {E : Finset ι | (E : Set ι) ⊆ D}, ((f E).support : Set ι)
  let Cn : ℕ → Set ι := fun n => step^[n] ∅
  have hsucc : ∀ n, Cn (n + 1) = step (Cn n) := fun n => Function.iterate_succ_apply' step n ∅
  have hcount : ∀ n, (Cn n).Countable := by
    intro n
    induction n with
    | zero => exact Set.countable_empty
    | succ n ih =>
      rw [hsucc]
      refine ih.union (Set.Countable.biUnion ?_ fun E _ => (f E).support.finite_toSet.countable)
      have h2 : {t : Set ι | t.Finite ∧ t ⊆ Cn n}.Countable := Set.countable_ofPred_finite_subset ih
      have h3 : {E : Finset ι | (E : Set ι) ⊆ Cn n}
          = (fun E : Finset ι => (E : Set ι)) ⁻¹' {t : Set ι | t.Finite ∧ t ⊆ Cn n} := by
        ext E
        simp
      rw [h3]
      exact h2.preimage Finset.coe_injective
  have hmono : Monotone Cn := monotone_nat_of_le_succ fun n => by
    rw [hsucc]
    exact Set.subset_union_left
  refine ⟨⋃ n, Cn n, Set.countable_iUnion hcount, fun E hE => ?_⟩
  have hfin : ∃ n, (E : Set ι) ⊆ Cn n := by
    have : ∀ F : Finset ι, (F : Set ι) ⊆ (⋃ n, Cn n) → ∃ n, (F : Set ι) ⊆ Cn n := by
      intro F
      induction F using Finset.induction with
      | empty => exact fun _ => ⟨0, by simp⟩
      | insert a F _ ih =>
        intro h
        rw [Finset.coe_insert, Set.insert_subset_iff] at h
        obtain ⟨n, hn⟩ := ih h.2
        obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h.1
        refine ⟨max n m, ?_⟩
        rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨hmono (le_max_right n m) hm, hn.trans (hmono (le_max_left n m))⟩
    exact this E hE
  obtain ⟨n, hn⟩ := hfin
  refine Set.Subset.trans ?_ (Set.subset_iUnion Cn (n + 1))
  rw [hsucc]
  refine Set.Subset.trans ?_ Set.subset_union_right
  exact Set.subset_biUnion_of_mem (u := fun F : Finset ι => ((f F).support : Set ι))
    (s := {F : Finset ι | (F : Set ι) ⊆ Cn n}) hn

/-! ### First example: countable tightness, the ideal not countably generated -/

namespace Countably

scoped instance top : TopologicalSpace (ι →₀ ZMod 2) :=
  TopologicalSpace.induced (fun x : ι →₀ ZMod 2 => (x : ι → ZMod 2)) inferInstance

scoped instance : IsTopologicalAddGroup (ι →₀ ZMod 2) :=
  isTopologicalAddGroup_induced (Finsupp.coeFnAddHom : (ι →₀ ZMod 2) →+ (ι → ZMod 2))

scoped instance : T2Space (ι →₀ ZMod 2) :=
  (Topology.IsEmbedding.mk (Topology.IsInducing.mk rfl) DFunLike.coe_injective).t2Space

theorem mem_nhds_zero (s : Set (ι →₀ ZMod 2)) :
    s ∈ 𝓝 (0 : ι →₀ ZMod 2) ↔ ∃ E : Finset ι, ∀ x : ι →₀ ZMod 2, (∀ i ∈ E, x i = 0) → x ∈ s := by
  classical
  rw [nhds_induced, Filter.mem_comap]
  constructor
  · rintro ⟨t, ht, hts⟩
    rw [nhds_pi, Filter.mem_pi] at ht
    obtain ⟨J, hJ, u, hu, hsub⟩ := ht
    refine ⟨hJ.toFinset, fun x hx => hts (hsub fun i hi => ?_)⟩
    have h0 : x i = 0 := hx i (hJ.mem_toFinset.2 hi)
    have := mem_of_mem_nhds (hu i)
    simpa [h0] using this
  · rintro ⟨E, hE⟩
    refine ⟨(E : Set ι).pi fun _ => {0}, ?_, fun x hx => hE x fun i hi => hx i hi⟩
    refine set_pi_mem_nhds E.finite_toSet fun i _ => ?_
    rw [show ((0 : ι →₀ ZMod 2) : ι → ZMod 2) i = 0 from rfl]
    exact (isOpen_discrete _).mem_nhds rfl

/-- The sets whose members are supported in one countable set. -/
def I : Set (Set (ι →₀ ZMod 2)) := {B | ∃ C : Set ι, C.Countable ∧ ∀ x ∈ B, (x.support : Set ι) ⊆ C}

theorem admissible [Uncountable ι] : AdmIdeal (I : Set (Set (ι →₀ ZMod 2))) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro A ⟨C, hC, h⟩ B hB
    exact ⟨C, hC, fun x hx => h x (hB hx)⟩
  · rintro A ⟨C, hC, h⟩ B ⟨D, hD, h'⟩
    refine ⟨C ∪ D, hC.union hD, fun x hx => ?_⟩
    rcases hx with hx | hx
    · exact (h x hx).trans Set.subset_union_left
    · exact (h' x hx).trans Set.subset_union_right
  · intro x
    refine ⟨x.support, x.support.finite_toSet.countable, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff.1 hy]
  · rintro ⟨C, hC, h⟩
    refine Set.not_countable_univ (α := ι) (hC.mono fun i _ => ?_)
    have := h (Finsupp.single i 1) (Set.mem_univ _)
    exact this (by simp)
  · rintro A ⟨C, hC, h⟩ B ⟨D, hD, h'⟩
    refine ⟨C ∪ D, hC.union hD, ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩ i hi
    rcases Finset.mem_union.1 (Finsupp.support_add hi) with hi | hi
    · exact Or.inl (h a ha hi)
    · exact Or.inr (h' b hb hi)
  · rintro A ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    simpa using h a ha

/-- Every vicinity set is a neighbourhood of `0`. -/
theorem vicinity_le_nhds [Uncountable ι] {S : Set (ι →₀ ZMod 2)} (hS : S ∈ Vxi I 0) :
    S ∈ 𝓝 (0 : ι →₀ ZMod 2) := by
  classical
  rw [mem_nhds_zero]
  by_contra hno
  push Not at hno
  choose f hf0 hfS using hno
  obtain ⟨C, hC, hcl⟩ := exists_countable_closed f
  have hB : {x : ι →₀ ZMod 2 | (x.support : Set ι) ⊆ C} ∈ (I : Set (Set (ι →₀ ZMod 2))) :=
    ⟨C, hC, fun x hx => hx⟩
  have h0 := (mem_Vxi_zero_iff admissible S).1 hS _ hB
  apply h0
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨E, hE⟩ := (mem_nhds_zero t).1 ht
  set E' := E.filter (fun i => i ∈ C) with hE'
  have hE'C : (E' : Set ι) ⊆ C := fun i hi => (Finset.mem_filter.1 hi).2
  have hsupp := hcl E' hE'C
  refine ⟨f E', hE _ fun i hi => ?_, hsupp, hfS E'⟩
  by_cases hiC : i ∈ C
  · exact hf0 E' i (Finset.mem_filter.2 ⟨hi, hiC⟩)
  · exact Finsupp.notMem_support_iff.1 fun h => hiC (hsupp h)

theorem not_pretopological [Uncountable ι] :
    ¬ xi (I : Set (Set (ι →₀ ZMod 2))) (Vxi I 0) 0 := by
  classical
  intro h
  refine not_pretopological_of_recipe (admissible (ι := ι)) ?_ ((pretopological_iff admissible).2 h)
  rintro A ⟨C, hC, hA⟩
  have hinf : (Cᶜ : Set ι).Infinite := by
    intro hfin
    refine Set.not_countable_univ (α := ι) ?_
    rw [← Set.union_compl_self C]
    exact hC.union hfin.countable
  let d : ℕ → ι := fun n => (hinf.natEmbedding _ n : ι)
  have hd : Function.Injective d := fun a b hab =>
    (hinf.natEmbedding _).injective (Subtype.ext hab)
  have hdC : ∀ n, d n ∉ C := fun n => (hinf.natEmbedding _ n).2
  refine ⟨Set.range fun n => Finsupp.single (d n) (1 : ZMod 2), ?_, ?_, ?_⟩
  · refine ⟨Set.range d, Set.countable_range d, ?_⟩
    rintro _ ⟨n, rfl⟩ i hi
    exact ⟨n, (Finset.mem_singleton.1 (Finsupp.support_single_subset hi)).symm⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hx
    exact hdC n (hA _ hx (by simp))
  · rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨E, hE⟩ := (mem_nhds_zero t).1 ht
    have : ∃ n, d n ∉ E := by
      by_contra hall
      push Not at hall
      exact Set.infinite_range_of_injective hd
        (E.finite_toSet.subset (by rintro _ ⟨n, rfl⟩; exact hall n))
    obtain ⟨n, hn⟩ := this
    refine ⟨Finsupp.single (d n) 1, hE _ fun i hi => ?_, n, rfl⟩
    exact Finsupp.single_eq_of_ne fun h => hn (h ▸ hi)

/-- The topology of the first example has countable tightness at `0`. -/
theorem tight (B : Set (ι →₀ ZMod 2)) (hB : (0 : ι →₀ ZMod 2) ∈ closure B) :
    ∃ C ⊆ B, C.Countable ∧ (0 : ι →₀ ZMod 2) ∈ closure C := by
  classical
  have hex : ∀ E : Finset ι, ∃ x ∈ B, ∀ i ∈ E, x i = 0 := by
    intro E
    have ht : {x : ι →₀ ZMod 2 | ∀ i ∈ E, x i = 0} ∈ 𝓝 (0 : ι →₀ ZMod 2) :=
      (mem_nhds_zero _).2 ⟨E, fun x hx => hx⟩
    obtain ⟨x, hx, hxB⟩ := mem_closure_iff_nhds.1 hB _ ht
    exact ⟨x, hxB, hx⟩
  choose f hfB hf0 using hex
  obtain ⟨D, hD, hcl⟩ := exists_countable_closed f
  refine ⟨f '' {E : Finset ι | (E : Set ι) ⊆ D}, ?_, ?_, ?_⟩
  · rintro _ ⟨E, _, rfl⟩
    exact hfB E
  · refine Set.Countable.image ?_ f
    have h2 : {t : Set ι | t.Finite ∧ t ⊆ D}.Countable := Set.countable_ofPred_finite_subset hD
    have h3 : {E : Finset ι | (E : Set ι) ⊆ D}
        = (fun E : Finset ι => (E : Set ι)) ⁻¹' {t : Set ι | t.Finite ∧ t ⊆ D} := by
      ext E
      simp
    rw [h3]
    exact h2.preimage Finset.coe_injective
  · rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨E, hE⟩ := (mem_nhds_zero t).1 ht
    set E' := E.filter (fun i => i ∈ D) with hE'
    have hE'D : (E' : Set ι) ⊆ D := fun i hi => (Finset.mem_filter.1 hi).2
    refine ⟨f E', hE _ fun i hi => ?_, E', hE'D, rfl⟩
    by_cases hiD : i ∈ D
    · exact hf0 E' i (Finset.mem_filter.2 ⟨hi, hiD⟩)
    · exact Finsupp.notMem_support_iff.1 fun h => hiD (hcl E' hE'D h)

end Countably

/-! ### Second example: the ideal countably generated, the topology a P-space -/

namespace Bounded

/-- The elements that vanish on `C`. -/
def vanish (C : Set ι) : Set (ι →₀ ZMod 2) := {x | ∀ i ∈ C, x i = 0}

@[instance_reducible] def basis : AddGroupFilterBasis (ι →₀ ZMod 2) :=
  addGroupFilterBasisOfComm {s | ∃ C : Set ι, C.Countable ∧ s = vanish C}
    ⟨_, ∅, Set.countable_empty, rfl⟩
    (by
      rintro _ _ ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
      refine ⟨vanish (C ∪ D), ⟨C ∪ D, hC.union hD, rfl⟩, fun x hx => ⟨?_, ?_⟩⟩
      · exact fun i hi => hx i (Or.inl hi)
      · exact fun i hi => hx i (Or.inr hi))
    (by
      rintro _ ⟨C, _, rfl⟩ i _
      rfl)
    (by
      rintro _ ⟨C, hC, rfl⟩
      refine ⟨vanish C, ⟨C, hC, rfl⟩, ?_⟩
      rintro _ ⟨a, ha, b, hb, rfl⟩ i hi
      simp [ha i hi, hb i hi])
    (by
      rintro _ ⟨C, hC, rfl⟩
      refine ⟨vanish C, ⟨C, hC, rfl⟩, fun x hx i hi => ?_⟩
      simp [hx i hi])

scoped instance top : TopologicalSpace (ι →₀ ZMod 2) := basis.topology

scoped instance : IsTopologicalAddGroup (ι →₀ ZMod 2) := basis.isTopologicalAddGroup

theorem mem_nhds_zero (s : Set (ι →₀ ZMod 2)) :
    s ∈ 𝓝 (0 : ι →₀ ZMod 2) ↔ ∃ C : Set ι, C.Countable ∧ vanish C ⊆ s := by
  rw [basis.nhds_zero_hasBasis.mem_iff]
  constructor
  · rintro ⟨_, ⟨C, hC, rfl⟩, h⟩
    exact ⟨C, hC, h⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨vanish C, ⟨C, hC, rfl⟩, h⟩

scoped instance : T2Space (ι →₀ ZMod 2) := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  refine ⟨vanish (x.support : Set ι), (mem_nhds_zero _).2 ⟨_, x.support.finite_toSet.countable, subset_rfl⟩,
    fun h => hx ?_⟩
  ext i
  by_cases hi : i ∈ x.support
  · exact h i hi
  · simpa using hi

/-- The sets with supports of bounded size. -/
def I : Set (Set (ι →₀ ZMod 2)) := {B | ∃ k : ℕ, ∀ x ∈ B, x.support.card ≤ k}

/-- The `k`-th generator of the ideal. -/
def A (k : ℕ) : Set (ι →₀ ZMod 2) := {x | x.support.card ≤ k}

theorem A_mem (k : ℕ) : A k ∈ (I : Set (Set (ι →₀ ZMod 2))) := ⟨k, fun _ hx => hx⟩

theorem A_mono : Monotone (A : ℕ → Set (ι →₀ ZMod 2)) := fun _ _ h _ hx => le_trans hx h

theorem cofinal (B : Set (ι →₀ ZMod 2)) (hB : B ∈ (I : Set (Set (ι →₀ ZMod 2)))) : ∃ k, B ⊆ A k := hB

/-- The indicator of a finite set. -/
noncomputable def ind (s : Finset ι) : ι →₀ ZMod 2 := Finsupp.indicator s fun _ _ => 1

theorem support_ind (s : Finset ι) : (ind s).support = s := by
  classical
  ext i
  by_cases hi : i ∈ s <;> simp [ind, Finsupp.indicator_apply, hi]

theorem admissible [Infinite ι] : AdmIdeal (I : Set (Set (ι →₀ ZMod 2))) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro S ⟨k, h⟩ B hB
    exact ⟨k, fun x hx => h x (hB hx)⟩
  · rintro S ⟨k, h⟩ B ⟨l, h'⟩
    refine ⟨max k l, fun x hx => ?_⟩
    rcases hx with hx | hx
    · exact le_trans (h x hx) (le_max_left _ _)
    · exact le_trans (h' x hx) (le_max_right _ _)
  · intro x
    refine ⟨x.support.card, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff.1 hy]
  · rintro ⟨k, h⟩
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq ι (k + 1)
    have := h (ind s) (Set.mem_univ _)
    rw [support_ind, hs] at this
    omega
  · rintro S ⟨k, h⟩ B ⟨l, h'⟩
    refine ⟨k + l, ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact le_trans (Finset.card_le_card Finsupp.support_add)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add (h a ha) (h' b hb)))
  · rintro S ⟨k, h⟩
    refine ⟨k, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    simpa using h a ha

/-- Every vicinity set is a neighbourhood of `0`. -/
theorem vicinity_le_nhds [Infinite ι] {S : Set (ι →₀ ZMod 2)} (hS : S ∈ Vxi I 0) :
    S ∈ 𝓝 (0 : ι →₀ ZMod 2) := by
  have hk : ∀ k : ℕ, ∃ C : Set ι, C.Countable ∧ vanish C ∩ (A k \ S) = ∅ := by
    intro k
    have h0 := (mem_Vxi_zero_iff admissible S).1 hS _ (A_mem k)
    rw [mem_closure_iff_nhds] at h0
    push Not at h0
    obtain ⟨t, ht, hempty⟩ := h0
    obtain ⟨C, hC, hsub⟩ := (mem_nhds_zero t).1 ht
    refine ⟨C, hC, Set.eq_empty_of_subset_empty fun x hx => ?_⟩
    have : x ∈ t ∩ (A k \ S) := ⟨hsub hx.1, hx.2⟩
    rwa [hempty] at this
  choose C hC hempty using hk
  refine (mem_nhds_zero S).2 ⟨⋃ k, C k, Set.countable_iUnion hC, fun x hx => ?_⟩
  by_contra hxS
  have : x ∈ vanish (C x.support.card) ∩ (A x.support.card \ S) :=
    ⟨fun i hi => hx i (Set.mem_iUnion.2 ⟨_, hi⟩), le_refl x.support.card, hxS⟩
  rw [hempty] at this
  exact this

theorem not_pretopological [Uncountable ι] :
    ¬ xi (I : Set (Set (ι →₀ ZMod 2))) (Vxi I 0) 0 := by
  classical
  intro h
  obtain ⟨S, ⟨k, hk⟩, hcl⟩ := (pretopological_zero_iff admissible).1 h
  apply hcl (A (k + 1)) (A_mem (k + 1))
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨C, hC, hsub⟩ := (mem_nhds_zero t).1 ht
  have hinf : (Cᶜ : Set ι).Infinite := by
    intro hfin
    refine Set.not_countable_univ (α := ι) ?_
    rw [← Set.union_compl_self C]
    exact hC.union hfin.countable
  obtain ⟨s, hsC, hs⟩ := hinf.exists_subset_card_eq (k + 1)
  have hcard : (ind s).support.card = k + 1 := by rw [support_ind, hs]
  refine ⟨ind s, hsub fun i hi => ?_, le_of_eq hcard, fun hmem => ?_⟩
  · refine Finsupp.notMem_support_iff.1 fun h' => ?_
    rw [support_ind] at h'
    exact hsC h' hi
  · have := hk _ hmem
    omega

end Bounded

end PG.PretopEx
