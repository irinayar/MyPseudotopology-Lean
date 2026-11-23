import Mathlib

/-!
# PG: the game lemma for stable ordered-union ultrafilters (Lean check)

Scope. The "game lemma" of `PG_v15` (Section 9): if `U` is a stable ordered-union ultrafilter, Player 1 has no winning
strategy in the game `G(U)`, in an abstract form. Blocks are the elements of a type `X` with a rank function
`mx : X → ℕ` (the maximum of the block) such that only finitely many blocks have rank `≤ m`, and a relation `lt a b`
(`max a < min b`) that forces `mx a < mx b`. `U` is an ultrafilter on `X` with

* `hab` : `{b | lt a b} ∈ U` for every `a`;
* `hstable` : for every relation `P` there is `H ∈ U` homogeneous for the partition of the pairs `(a, b)` with `lt a b`
  into `P` and not `P` (stability);
* `hbase` : inside every `H ∈ U` there is a `lt`-increasing sequence in `H` with the winning property `Win`
  (in the article: `FU(a) ∈ U`).

* `game_lemma` : for every strategy `Σ` (a member `Σ σ ∈ U` for every finite history `σ`) there is a `lt`-increasing
  sequence `a` with `Win a` and `a k ∈ Σ (a 0, ..., a (k-1))` for all `k`.

A Lean proof verifies its formal statement under its hypotheses; the correspondence with the article requires
mathematical review.
-/

open Filter Set

namespace PG

section game

variable {X : Type*}

theorem finite_lists (S : Set X) (hS : S.Finite) (n : ℕ) :
    {l : List X | l.length ≤ n ∧ ∀ a ∈ l, a ∈ S}.Finite := by
  induction n with
  | zero =>
    refine Set.Finite.subset (Set.finite_singleton ([] : List X)) ?_
    intro l hl
    have : l.length = 0 := Nat.le_zero.1 hl.1
    simp [List.length_eq_zero_iff.1 this]
  | succ n ih =>
    have hfin : (insert ([] : List X) ((fun p : X × List X => p.1 :: p.2) '' (S ×ˢ {l : List X | l.length ≤ n ∧ ∀ a ∈ l, a ∈ S}))).Finite :=
      (Set.Finite.image _ (hS.prod ih)).insert _
    refine Set.Finite.subset hfin ?_
    intro l hl
    cases l with
    | nil => exact Set.mem_insert _ _
    | cons a t =>
      right
      refine ⟨(a, t), ⟨hl.2 a (by simp), ?_, ?_⟩, rfl⟩
      · simpa using Nat.le_of_succ_le_succ (by simpa using hl.1)
      · intro b hb; exact hl.2 b (by simp [hb])

theorem game_lemma (mx : X → ℕ) (lt : X → X → Prop) (U : Ultrafilter X)
    (hfin : ∀ m, {a : X | mx a ≤ m}.Finite)
    (hlt : ∀ a b, lt a b → mx a < mx b)
    (hab : ∀ a, {b | lt a b} ∈ (U : Filter X))
    (hstable : ∀ P : X → X → Prop, ∃ H ∈ (U : Filter X),
      (∀ a ∈ H, ∀ b ∈ H, lt a b → P a b) ∨ (∀ a ∈ H, ∀ b ∈ H, lt a b → ¬ P a b))
    (Win : (ℕ → X) → Prop)
    (hbase : ∀ H ∈ (U : Filter X), ∃ a : ℕ → X, (∀ n, a n ∈ H) ∧ (∀ n, lt (a n) (a (n + 1))) ∧ Win a)
    (S : List X → Set X) (hS : ∀ σ, S σ ∈ (U : Filter X)) :
    ∃ a : ℕ → X, Win a ∧ (∀ n, lt (a n) (a (n + 1))) ∧ ∀ k, a k ∈ S ((List.range k).map a) := by
  -- the intersection over all short histories below rank m
  let Hist : ℕ → Set (List X) := fun m => {l | l.length ≤ m + 1 ∧ ∀ a ∈ l, mx a ≤ m}
  have hHist : ∀ m, (Hist m).Finite := fun m => finite_lists _ (hfin m) (m + 1)
  let S' : ℕ → Set X := fun m => ⋂ σ ∈ Hist m, S σ
  have hS' : ∀ m, S' m ∈ (U : Filter X) := fun m =>
    (Filter.biInter_mem (hHist m)).2 (fun σ _ => hS σ)
  obtain ⟨H, hH, hhom⟩ := hstable (fun a b => b ∈ S' (mx a))
  have hH0 : H.Nonempty := Filter.nonempty_of_mem hH
  have hcase : ∀ a ∈ H, ∀ b ∈ H, lt a b → b ∈ S' (mx a) := by
    rcases hhom with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha⟩ := hH0
      have h1 : H ∩ ({b | lt a b} ∩ S' (mx a)) ∈ (U : Filter X) :=
        Filter.inter_mem hH (Filter.inter_mem (hab a) (hS' (mx a)))
      obtain ⟨b, hbH, hlt', hbS⟩ := Filter.nonempty_of_mem h1
      exact h a ha b hbH hlt' hbS
  obtain ⟨a, haH, hach, hwin⟩ := hbase (H ∩ S []) (Filter.inter_mem hH (hS []))
  refine ⟨a, hwin, hach, ?_⟩
  have hmono : StrictMono (fun n => mx (a n)) := strictMono_nat_of_lt_succ (fun n => hlt _ _ (hach n))
  intro k
  cases k with
  | zero => simpa using (haH 0).2
  | succ k =>
    have hpair : a (k + 1) ∈ S' (mx (a k)) := hcase (a k) (haH k).1 (a (k + 1)) (haH (k + 1)).1 (hach k)
    have hmem : (List.range (k + 1)).map a ∈ Hist (mx (a k)) := by
      refine ⟨?_, ?_⟩
      · simp only [List.length_map, List.length_range]
        have : k ≤ mx (a k) := hmono.id_le k
        omega
      · intro b hb
        simp only [List.mem_map, List.mem_range] at hb
        obtain ⟨j, hj, rfl⟩ := hb
        exact hmono.monotone (by omega)
    exact (Set.mem_iInter₂.1 hpair) _ hmem

end game

end PG
