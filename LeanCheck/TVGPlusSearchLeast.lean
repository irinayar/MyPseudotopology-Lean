import LeanCheck.TVGPlusSearch

/-!
# TVGplus: least witnesses from verified searches

`LeastOn l lo hi u`: for every `m ∈ [lo, hi]`, the integer `u` is the least positive element of the shifted ball
`{k : P_p(k - s) < 1/m for all (p, s) ∈ l}`.  `least_of_search` assembles the exhaustive search of `TVGPlusSearch`
(radius `1/lo`, bound `u - 1`) with a membership certificate of `u` at radius `1/hi`.
`none_of_search` is the statement that the ball is empty up to a bound.
-/

namespace LeanCheck
namespace TVGSearch

open MixedPrime

/-- Membership certificates for all listed `(p, s)` (computable). -/
def memAll (l : List (ℕ × ℕ)) (u ca cb N : ℕ) : Bool :=
  l.all (fun t => TVGPlus.memCheck t.1 (u - t.2) ca cb N)

lemma memAll_spec {l : List (ℕ × ℕ)} {u ca cb N : ℕ} (hl : ∀ t ∈ l, 2 ≤ t.1 ∧ t.2 ≤ 1) (hu : 1 ≤ u) (hcb : 0 < cb)
    (h : memAll l u ca cb N = true) : ∀ t ∈ l, Pn (sqScales t.1) ((u : ℤ) - t.2) ≤ (ca : ℝ) / cb := by
  intro t ht
  unfold memAll at h
  rw [List.all_eq_true] at h
  have h1 := TVGPlus.memCheck_spec (hl t ht).1 hcb (h t ht)
  have e : (((u - t.2 : ℕ)) : ℤ) = (u : ℤ) - t.2 := by
    have := (hl t ht).2
    push_cast [Nat.cast_sub (show t.2 ≤ u by omega)]; ring
  rwa [e] at h1

def LeastOn (l : List (ℕ × ℕ)) (lo hi u : ℕ) : Prop :=
  1 ≤ u ∧ ∀ m, lo ≤ m → m ≤ hi → ShiftedIn l m u ∧ ∀ k : ℕ, 1 ≤ k → k < u → ¬ ShiftedIn l m k

def NoneOn (l : List (ℕ × ℕ)) (lo hi X : ℕ) : Prop :=
  ∀ m, lo ≤ m → m ≤ hi → ∀ k : ℕ, 1 ≤ k → k ≤ X → ¬ ShiftedIn l m k

lemma ShiftedIn_perm {l l' : List (ℕ × ℕ)} (h : l.Perm l') {m k : ℕ} : ShiftedIn l m k ↔ ShiftedIn l' m k := by
  unfold ShiftedIn
  constructor
  · intro H t ht; exact H t (h.mem_iff.2 ht)
  · intro H t ht; exact H t (h.mem_iff.1 ht)

lemma LeastOn_perm {l l' : List (ℕ × ℕ)} (h : l.Perm l') {lo hi u : ℕ} (H : LeastOn l lo hi u) : LeastOn l' lo hi u := by
  refine ⟨H.1, fun m h1 h2 => ?_⟩
  obtain ⟨a, b⟩ := H.2 m h1 h2
  exact ⟨(ShiftedIn_perm h).1 a, fun k hk hku => fun hh => b k hk hku ((ShiftedIn_perm h).2 hh)⟩

lemma NoneOn_perm {l l' : List (ℕ × ℕ)} (h : l.Perm l') {lo hi X : ℕ} (H : NoneOn l lo hi X) : NoneOn l' lo hi X := by
  intro m h1 h2 k hk1 hkX hh
  exact H m h1 h2 k hk1 hkX ((ShiftedIn_perm h).2 hh)

theorem none_of_search {p q sp sq : ℕ} {rest : List (ℕ × ℕ)} {lo hi X n2 n3 Pinv N : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : sp ≤ 1 ∧ sq ≤ 1 ∧ ∀ t ∈ rest, 2 ≤ t.1 ∧ t.2 ≤ 1)
    (hn : 1 ≤ n2 ∧ 1 ≤ n3) (hlohi : 0 < lo ∧ lo ≤ hi)
    (hsetup : searchSetup p q n2 n3 Pinv X = true)
    (hchunk : ChunkOK p q sp sq rest lo n2 n3 Pinv X N 0 (p ^ (n2 * n2))) :
    NoneOn ((p, sp) :: (q, sq) :: rest) lo hi X := by
  intro m h1 h2 k hk1 hkX hball
  have := search_none hp hq hs.1 hs.2.1 hs.2.2 (m := lo) hlohi.1 hn.1 hn.2 hsetup hchunk k hk1 hkX
  exact this (ShiftedIn_mono hlohi.1 h1 hball)

theorem least_of_search {p q sp sq : ℕ} {rest : List (ℕ × ℕ)} {lo hi u X n2 n3 Pinv N ca cb Nm : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : sp ≤ 1 ∧ sq ≤ 1 ∧ ∀ t ∈ rest, 2 ≤ t.1 ∧ t.2 ≤ 1)
    (hn : 1 ≤ n2 ∧ 1 ≤ n3) (hlohi : 0 < lo ∧ lo ≤ hi) (hX : X + 1 = u) (hu : 1 ≤ u)
    (hsetup : searchSetup p q n2 n3 Pinv X = true)
    (hchunk : ChunkOK p q sp sq rest lo n2 n3 Pinv X N 0 (p ^ (n2 * n2)))
    (hc : ca * hi < cb ∧ 0 < cb)
    (hmem : memAll ((p, sp) :: (q, sq) :: rest) u ca cb Nm = true) :
    LeastOn ((p, sp) :: (q, sq) :: rest) lo hi u := by
  have hl : ∀ t ∈ (p, sp) :: (q, sq) :: rest, 2 ≤ t.1 ∧ t.2 ≤ 1 := by
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | ht
    · exact ⟨hp, hs.1⟩
    · exact ⟨hq, hs.2.1⟩
    · exact hs.2.2 t ht
  have hmem' := memAll_spec hl hu hc.2 hmem
  have hnone := none_of_search (hi := hi) hp hq hs hn hlohi hsetup hchunk
  refine ⟨hu, fun m h1 h2 => ⟨?_, ?_⟩⟩
  · intro t ht
    have hcb' : (0 : ℝ) < cb := by exact_mod_cast hc.2
    have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hlt : (ca : ℝ) / cb < 1 / (m : ℝ) := by
      rw [div_lt_div_iff₀ hcb' hm']
      have : ((ca * hi : ℕ) : ℝ) < (cb : ℝ) := by exact_mod_cast hc.1
      have hmh : (m : ℝ) ≤ hi := by exact_mod_cast h2
      have hca : (0 : ℝ) ≤ ca := by positivity
      push_cast at this
      nlinarith
    exact lt_of_le_of_lt (hmem' t ht) hlt
  · intro k hk1 hku hball
    exact hnone m h1 h2 k hk1 (by omega) hball

theorem shifted_of_mem {l : List (ℕ × ℕ)} {u ca cb N lo hi : ℕ} (hl : ∀ t ∈ l, 2 ≤ t.1 ∧ t.2 ≤ 1)
    (hu : 1 ≤ u) (hlo : 0 < lo) (hc : ca * hi < cb ∧ 0 < cb) (hmem : memAll l u ca cb N = true) :
    ∀ m, lo ≤ m → m ≤ hi → ShiftedIn l m u := by
  have hmem' := memAll_spec hl hu hc.2 hmem
  intro m h1 h2 t ht
  have hcb' : (0 : ℝ) < cb := by exact_mod_cast hc.2
  have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlt : (ca : ℝ) / cb < 1 / (m : ℝ) := by
    rw [div_lt_div_iff₀ hcb' hm']
    have : ((ca * hi : ℕ) : ℝ) < (cb : ℝ) := by exact_mod_cast hc.1
    have hmh : (m : ℝ) ≤ hi := by exact_mod_cast h2
    have hca : (0 : ℝ) ≤ ca := by positivity
    push_cast at this
    nlinarith
  exact lt_of_le_of_lt (hmem' t ht) hlt

#print axioms least_of_search
#print axioms none_of_search

end TVGSearch
end LeanCheck
