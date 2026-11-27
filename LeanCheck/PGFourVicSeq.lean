import Mathlib

/-!
# PGfour: no sequence converges for the vicinity filter of countably many generators

`F n` are filters on `G` (in the application, the finite signed filter sums of countably many ultrafilters), each with
a limit along a map `e : G → K` into a topological space (the Bohr compactification). `B0` is a set whose infinite subsets
contain two infinite sets with images having disjoint closures (an `I₀` set has this property; its existence is quoted,
not proved here). If no point of `B0` belongs to every member of any `F n`, then there are an infinite `B ⊆ B0` and a set
that belongs to every `F n` and is disjoint from `B`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set Topology

namespace PG.VicSeq

variable {G K : Type*} [TopologicalSpace K]

/-- A filter with a limit along `e` misses an infinite subset of every infinite subset of `B0`. -/
theorem exists_disjoint (e : G → K) (B0 : Set G)
    (hI : ∀ B ⊆ B0, B.Infinite → ∃ C1 ⊆ B, ∃ C2 ⊆ B, C1.Infinite ∧ C2.Infinite ∧
      Disjoint (closure (e '' C1)) (closure (e '' C2)))
    (F : Filter G) (t : K) (ht : Tendsto e F (𝓝 t)) (B : Set G) (hB : B ⊆ B0) (hBi : B.Infinite) :
    ∃ C ⊆ B, C.Infinite ∧ ∃ D ∈ F, Disjoint D C := by
  obtain ⟨C1, h1, C2, h2, i1, i2, hd⟩ := hI B hB hBi
  have key : ∀ C : Set G, t ∉ closure (e '' C) → ∃ D ∈ F, Disjoint D C := by
    intro C hC
    have hm : (closure (e '' C))ᶜ ∈ 𝓝 t := isClosed_closure.isOpen_compl.mem_nhds hC
    refine ⟨e ⁻¹' (closure (e '' C))ᶜ, ht hm, ?_⟩
    rw [Set.disjoint_left]
    intro x hx hxC
    exact hx (subset_closure (Set.mem_image_of_mem e hxC))
  by_cases h : t ∈ closure (e '' C1)
  · exact ⟨C2, h2, i2, key C2 (Set.disjoint_left.1 hd h)⟩
  · exact ⟨C1, h1, i1, key C1 h⟩

/-- The diagonal step. -/
theorem no_vicinity_sequence (e : G → K) (B0 : Set G) (hB0 : B0.Infinite)
    (hI : ∀ B ⊆ B0, B.Infinite → ∃ C1 ⊆ B, ∃ C2 ⊆ B, C1.Infinite ∧ C2.Infinite ∧
      Disjoint (closure (e '' C1)) (closure (e '' C2)))
    (F : ℕ → Filter G) (t : ℕ → K) (ht : ∀ n, Tendsto e (F n) (𝓝 (t n)))
    (hpt : ∀ n, ∀ b ∈ B0, ∃ D ∈ F n, b ∉ D) :
    ∃ B ⊆ B0, B.Infinite ∧ ∃ S : Set G, (∀ n, S ∈ F n) ∧ Disjoint S B := by
  classical
  have step : ∀ (n : ℕ) (B : Set G), B ⊆ B0 ∧ B.Infinite →
      ∃ C : Set G, (C ⊆ B0 ∧ C.Infinite) ∧ C ⊆ B ∧ ∃ D ∈ F n, Disjoint D C := by
    intro n B hB
    obtain ⟨C, hCB, hCi, hD⟩ := exists_disjoint e B0 hI (F n) (t n) (ht n) B hB.1 hB.2
    exact ⟨C, ⟨hCB.trans hB.1, hCi⟩, hCB, hD⟩
  choose nxt hgood hsub D hD hdisj using step
  -- the decreasing chain, and one new point at each stage
  let T := {p : Set G × Finset G // p.1 ⊆ B0 ∧ p.1.Infinite}
  have pick : ∀ (n : ℕ) (p : T), ∃ b, b ∈ nxt n p.1.1 p.2 ∧ b ∉ p.1.2 := fun n p =>
    ((hgood n p.1.1 p.2).2.sdiff p.1.2.finite_toSet).nonempty
  choose bp hbp hbnew using pick
  let st : ℕ → T := fun n =>
    Nat.rec (motive := fun _ => T) ⟨(B0, ∅), subset_rfl, hB0⟩
      (fun n p => ⟨(nxt n p.1.1 p.2, insert (bp n p) p.1.2), hgood n p.1.1 p.2⟩) n
  let b : ℕ → G := fun n => bp n (st n)
  have hst1 : ∀ n, (st (n + 1)).1.1 = nxt n (st n).1.1 (st n).2 := fun n => rfl
  have hst2 : ∀ n, (st (n + 1)).1.2 = insert (b n) (st n).1.2 := fun n => rfl
  have hanti : Antitone fun n => (st n).1.1 := antitone_nat_of_succ_le fun n => by
    rw [hst1]
    exact hsub n _ _
  have hbmem : ∀ n, b n ∈ (st (n + 1)).1.1 := fun n => by
    rw [hst1]
    exact hbp n (st n)
  have hb0 : ∀ n, b n ∈ B0 := fun n => (st (n + 1)).2.1 (hbmem n)
  have hrec : ∀ n m, m < n → b m ∈ (st n).1.2 := by
    intro n
    induction n with
    | zero => exact fun m hm => absurd hm (Nat.not_lt_zero m)
    | succ n ih =>
      intro m hm
      rw [hst2]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | h
      · exact Finset.mem_insert_of_mem (ih m h)
      · rw [h]
        exact Finset.mem_insert_self _ _
  have hbinj : Function.Injective b := by
    intro m n h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hbnew n (st n) (show b n ∈ (st n).1.2 from h ▸ hrec n m hlt)
    · exact hbnew m (st m) (show b m ∈ (st m).1.2 from h.symm ▸ hrec m n hlt)
  choose E hE hbE using hpt
  let D' : ℕ → Set G := fun n =>
    D n (st n).1.1 (st n).2 ∩ ⋂ m ∈ Set.Iio n, E n (b m) (hb0 m)
  have hD' : ∀ n, D' n ∈ F n := fun n =>
    Filter.inter_mem (hD n _ _) ((Filter.biInter_mem (Set.finite_Iio n)).2 fun m _ => hE n (b m) (hb0 m))
  refine ⟨Set.range b, ?_, Set.infinite_range_of_injective hbinj, ⋃ n, D' n,
    fun n => Filter.mem_of_superset (hD' n) (Set.subset_iUnion D' n), ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact hb0 n
  · rw [Set.disjoint_left]
    rintro x hx ⟨m, rfl⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    by_cases hmn : m < n
    · exact hbE n (b m) (hb0 m) (Set.mem_iInter₂.1 hn.2 m hmn)
    · have h1 : b m ∈ (st (n + 1)).1.1 := hanti (Nat.succ_le_succ (not_lt.1 hmn)) (hbmem m)
      rw [hst1] at h1
      exact Set.disjoint_left.1 (hdisj n (st n).1.1 (st n).2) hn.1 h1

end PG.VicSeq
