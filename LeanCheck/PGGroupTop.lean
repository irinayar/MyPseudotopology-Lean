import Mathlib
import LeanCheck.PGXi

/-!
# PG: a group topology has nested neighbourhoods; consequence for the topological modification (Lean check)

Scope. Lemma 7.7 and the reduction step of Theorem 7.9 of `PG_v8`. Notation: `G` an abelian group, `β` a (Hausdorff) group
topology, `I` an admissible ideal (`AdmIdeal`), `IsOpenXi I` the open sets of the topological modification `τ_ξ` of the PG `ξ_{β,I}`
(`PGXi`), `Vxi I 0` the filter `V_ξ(0)` (intersection of the filters converging to `0`).

* `nested_sums_family` : abstract halving lemma. If a family `𝒪` of sets containing `0` is closed under "halving"
  (`U ∈ 𝒪 ⇒ ∃ U' ∈ 𝒪, U' + U' ⊆ U`), then every `O ∈ 𝒪` contains all the sums `f 0 + ... + f (n-1)` with `f j ∈ P j`,
  for a sequence `P j ∈ 𝒪` and all `n` simultaneously;
* `nested_sums_nhds` : the case of the neighbourhoods of `0` in a topological additive group (Lemma 7.7, first half);
* `neg_mem_Vxi` : `V_ξ(0)` is closed under negation;
* `half_of_groupTop` : if the open sets of a group topology `τ` on `G` are exactly the sets of `IsOpenXi I`, then
  the family of `τ_ξ`-open sets containing `0` is closed under halving;
* `nested_sums_Vxi` : under this halving property, every `τ_ξ`-open `O ∋ 0` contains `S_0 + ... + S_{n-1}` for all `n`, with
  symmetric `S_j ∈ V_ξ(0)` (Lemma 7.7);
* `no_groupTop_of_sums` : if there is a `τ_ξ`-open `O ∋ 0` such that for all symmetric `S_j ∈ V_ξ(0)` some sum
  `x_0 + ... + x_{n-1}`, `x_j ∈ S_j`, lies outside `O`, then no group topology has `IsOpenXi I` as its family of open sets
  (this is the reduction used in Theorem 7.9).

Not formalized: the construction of the set `C` (Section 7 of `PG_v8`), the pigeonhole and congruence arguments.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG

section family

/-- Abstract halving lemma. -/
theorem nested_sums_family {H : Type*} [AddCommGroup H] (𝒪 : Set (Set H))
    (h0 : ∀ U ∈ 𝒪, (0 : H) ∈ U)
    (hhalf : ∀ U ∈ 𝒪, ∃ U' ∈ 𝒪, ∀ v ∈ U', ∀ w ∈ U', v + w ∈ U)
    {O : Set H} (hO : O ∈ 𝒪) :
    ∃ P : ℕ → Set H, (∀ j, P j ∈ 𝒪) ∧
      ∀ (n : ℕ) (f : ℕ → H), (∀ j < n, f j ∈ P j) → ∑ j ∈ Finset.range n, f j ∈ O := by
  have hex : ∀ s : Set H, ∃ t : Set H, s ∈ 𝒪 → t ∈ 𝒪 ∧ ∀ v ∈ t, ∀ w ∈ t, v + w ∈ s := by
    intro s
    by_cases hs : s ∈ 𝒪
    · obtain ⟨t, ht, hts⟩ := hhalf s hs
      exact ⟨t, fun _ => ⟨ht, hts⟩⟩
    · exact ⟨∅, fun h => (hs h).elim⟩
  choose h hh using hex
  let Q : ℕ → Set H := fun j => h^[j] O
  have hQ : ∀ j, Q j ∈ 𝒪 := by
    intro j
    induction j with
    | zero => exact hO
    | succ j ih =>
      have e : Q (j + 1) = h (Q j) := Function.iterate_succ_apply' h j O
      rw [e]
      exact (hh _ ih).1
  have hQs : ∀ j, ∀ v ∈ Q (j + 1), ∀ w ∈ Q (j + 1), v + w ∈ Q j := by
    intro j v hv w hw
    have e : Q (j + 1) = h (Q j) := Function.iterate_succ_apply' h j O
    rw [e] at hv hw
    exact (hh _ (hQ j)).2 v hv w hw
  refine ⟨fun j => Q (j + 1), fun j => hQ _, ?_⟩
  have key : ∀ n : ℕ, ∀ f : ℕ → H, (∀ j < n, f j ∈ Q (j + 1)) →
      ∀ y ∈ Q n, ∑ j ∈ Finset.range n, f j + y ∈ Q 0 := by
    intro n
    induction n with
    | zero =>
      intro f _ y hy
      simpa using hy
    | succ n ih =>
      intro f hf y hy
      rw [Finset.sum_range_succ, add_assoc]
      exact ih f (fun j hj => hf j (Nat.lt_succ_of_lt hj)) _
        (hQs n _ (hf n (Nat.lt_succ_self n)) _ hy)
  intro n f hf
  have := key n f hf 0 (h0 _ (hQ n))
  simpa [Q] using this

end family

section topgroup

variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]

/-- Lemma 7.7 (first half): nested neighbourhoods in a topological additive group. -/
theorem nested_sums_nhds {O : Set H} (hO : O ∈ 𝓝 (0 : H)) :
    ∃ P : ℕ → Set H, (∀ j, P j ∈ 𝓝 (0 : H)) ∧
      ∀ (n : ℕ) (f : ℕ → H), (∀ j < n, f j ∈ P j) → ∑ j ∈ Finset.range n, f j ∈ O :=
  nested_sums_family {s : Set H | s ∈ 𝓝 (0 : H)} (fun _ hU => mem_of_mem_nhds hU)
    (fun _ hU => by
      obtain ⟨t, ht, hts⟩ := exists_nhds_zero_half hU
      exact ⟨t, ht, hts⟩) hO

/-- Halving by open sets. -/
theorem exists_open_half {O : Set H} (hO : O ∈ 𝓝 (0 : H)) :
    ∃ U : Set H, IsOpen U ∧ (0 : H) ∈ U ∧ ∀ v ∈ U, ∀ w ∈ U, v + w ∈ O := by
  obtain ⟨t, ht, hts⟩ := exists_nhds_zero_half hO
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht, ?_⟩
  intro v hv w hw
  exact hts v (interior_subset hv) w (interior_subset hw)

end topgroup

section xi

variable {G : Type*} [AddCommGroup G] [β : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]

/-- `V_ξ(0)` is closed under negation. -/
theorem neg_mem_Vxi {I : Set (Set G)} (hI : AdmIdeal I) {A : Set G} (hA : A ∈ Vxi I 0) :
    (fun x : G => -x) ⁻¹' A ∈ Vxi I 0 := by
  rw [mem_Vxi] at hA ⊢
  intro F hF
  have h1 := xi_neg hI hF
  rw [neg_zero] at h1
  exact hA _ h1

/-- A `τ_ξ`-open set containing `0` belongs to `V_ξ(0)`. -/
theorem mem_Vxi_of_isOpenXi {I : Set (Set G)} {U : Set G} (hU : IsOpenXi I U) (h0 : (0 : G) ∈ U) :
    U ∈ Vxi I 0 := by
  rw [mem_Vxi]
  intro F hF
  exact hU 0 h0 F hF

/-- If the open sets of a group topology `τ` are the sets `IsOpenXi I`, then the `τ_ξ`-open sets containing `0`
can be halved. -/
theorem half_of_groupTop {I : Set (Set G)} {τ : TopologicalSpace G}
    (hg : @IsTopologicalAddGroup G τ (inferInstance : AddGroup G))
    (hτ : ∀ U : Set G, @IsOpen G τ U ↔ @IsOpenXi G β I U) :
    ∀ O : Set G, @IsOpenXi G β I O → (0 : G) ∈ O →
      ∃ O' : Set G, @IsOpenXi G β I O' ∧ (0 : G) ∈ O' ∧ ∀ v ∈ O', ∀ w ∈ O', v + w ∈ O := by
  intro O hO h0
  have hOn : O ∈ @nhds G τ 0 := @IsOpen.mem_nhds G τ 0 O ((hτ O).2 hO) h0
  obtain ⟨U, hU, h0U, hUs⟩ := @exists_open_half G _ τ hg O hOn
  exact ⟨U, (hτ U).1 hU, h0U, hUs⟩

/-- Lemma 7.7: nested sums for the topological modification. -/
theorem nested_sums_Vxi {I : Set (Set G)} (hI : AdmIdeal I)
    (hhalf : ∀ O : Set G, IsOpenXi I O → (0 : G) ∈ O →
      ∃ O' : Set G, IsOpenXi I O' ∧ (0 : G) ∈ O' ∧ ∀ v ∈ O', ∀ w ∈ O', v + w ∈ O)
    {O : Set G} (hO : IsOpenXi I O) (h0 : (0 : G) ∈ O) :
    ∃ S : ℕ → Set G, (∀ j, S j ∈ Vxi I 0) ∧ (∀ j, ∀ x ∈ S j, -x ∈ S j) ∧
      ∀ (n : ℕ) (f : ℕ → G), (∀ j < n, f j ∈ S j) → ∑ j ∈ Finset.range n, f j ∈ O := by
  obtain ⟨P, hP, hsum⟩ := nested_sums_family {U : Set G | IsOpenXi I U ∧ (0 : G) ∈ U}
    (fun _ hU => hU.2)
    (fun U hU => by
      obtain ⟨U', hU', h0', hs⟩ := hhalf U hU.1 hU.2
      exact ⟨U', ⟨hU', h0'⟩, hs⟩) (O := O) ⟨hO, h0⟩
  refine ⟨fun j => P j ∩ (fun x : G => -x) ⁻¹' P j, ?_, ?_, ?_⟩
  · intro j
    have h1 : P j ∈ Vxi I 0 := mem_Vxi_of_isOpenXi (hP j).1 (hP j).2
    exact Filter.inter_mem h1 (neg_mem_Vxi hI h1)
  · intro j x hx
    refine ⟨?_, ?_⟩
    · exact hx.2
    · simpa using hx.1
  · intro n f hf
    exact hsum n f (fun j hj => (hf j hj).1)

/-- The reduction used in Theorem 7.9: if some `τ_ξ`-open set `O ∋ 0` contains, for no choice of symmetric
`S_j ∈ V_ξ(0)`, all the sums `x_0 + ... + x_{n-1}` (`x_j ∈ S_j`), then no group topology has `IsOpenXi I` as its open sets. -/
theorem no_groupTop_of_sums {I : Set (Set G)} (hI : AdmIdeal I) {O : Set G}
    (hO : IsOpenXi I O) (h0 : (0 : G) ∈ O)
    (hbad : ∀ S : ℕ → Set G, (∀ j, S j ∈ Vxi I 0) → (∀ j, ∀ x ∈ S j, -x ∈ S j) →
      ∃ (n : ℕ) (f : ℕ → G), (∀ j < n, f j ∈ S j) ∧ ∑ j ∈ Finset.range n, f j ∉ O) :
    ¬ ∃ τ : TopologicalSpace G, (@IsTopologicalAddGroup G τ (inferInstance : AddGroup G)) ∧
      ∀ U : Set G, @IsOpen G τ U ↔ @IsOpenXi G β I U := by
  rintro ⟨τ, hg, hτ⟩
  obtain ⟨S, hS, hsym, hsum⟩ := @nested_sums_Vxi G _ β _ _ I hI (@half_of_groupTop G _ β _ _ I τ hg hτ) O hO h0
  obtain ⟨n, f, hf, hnot⟩ := hbad S hS hsym
  exact hnot (hsum n f hf)

end xi

end PG
