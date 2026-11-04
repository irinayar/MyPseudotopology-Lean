import LeanCheck.TVGSearchDef

/-!
# Sorted CRT window search: definitions (core Lean only)

Companion of `TVGSearchDef`.  Instead of scanning all pairs `(r, ρ)` of residues modulo `P = p^(n2²)` and
`Q = q^(n3²)`, write `k = r + P t` with `0 ≤ t < Q`.  With `Pinv` an inverse of `P` modulo `Q`, put
`v = r * Pinv mod Q` and `u = ρ * Pinv mod Q`; then `u ≡ v + t (mod Q)`.  Sorting the `v`'s and the doubled list of `u`'s
(`u` and `u + Q`), the candidates are the pairs in a window `v ≤ u' ≤ v + (X - r) / P`, found by a monotone sweep.

The sorting is done by a fuel-bounded merge sort; the checker verifies sortedness of its output, so no proof that
the sort is correct is needed, only that it keeps every element (`TVGPlusWindow.lean`).
-/

namespace LeanCheck
namespace TVGSearch

/-- Merge by the first component, with fuel. -/
def mergeF : Nat → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, x :: xs, [] => x :: xs
  | f + 1, x :: xs, y :: ys =>
      if x.1 ≤ y.1 then x :: mergeF f xs (y :: ys) else y :: mergeF f (x :: xs) ys

/-- Merge sort by the first component, with fuel for the recursion depth. -/
def msortF : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, l => l
  | f + 1, l =>
      if l.length ≤ 1 then l
      else mergeF l.length (msortF f (l.take (l.length / 2))) (msortF f (l.drop (l.length / 2)))

/-- The first components are nondecreasing. -/
def sortedB : List (Nat × Nat) → Bool
  | x :: y :: t => decide (x.1 ≤ y.1) && sortedB (y :: t)
  | _ => true

/-- Monotone sweep: `rest` is the part of the doubled `u`-list not yet passed; the list of `(v, r)` is sorted by `v`. -/
def sweep (P X : Nat) : List (Nat × Nat) → List (Nat × Nat) → List Nat
  | _, [] => []
  | rest, (v, r) :: tl =>
      let rest' := rest.dropWhile (fun p => decide (p.1 < v))
      (if r ≤ X then
        (rest'.takeWhile (fun p => decide (p.1 ≤ v + (X - r) / P))).filterMap
          (fun p => if 1 ≤ r + P * (p.1 - v) then some (r + P * (p.1 - v)) else none)
      else []) ++ sweep P X rest' tl

/-- The sorted list of `(r * Pinv mod Q, r)` for the residues `r` in `TP`. -/
def sortedRL (TP : List Nat) (Q Pinv : Nat) : List (Nat × Nat) :=
  msortF 64 (TP.map (fun r => ((r * Pinv) % Q, r)))

/-- The same for the full residue tree. -/
def sortedR (p sp m n2 Q Pinv : Nat) : List (Nat × Nat) :=
  sortedRL (tree p sp m n2) Q Pinv

/-- The sorted list of `(ρ * Pinv mod Q, ρ)`. -/
def sortedU (q sq m n3 Q Pinv : Nat) : List (Nat × Nat) :=
  msortF 64 ((tree q sq m n3).map (fun ρ => ((ρ * Pinv) % Q, ρ)))

/-- The doubled `u`-list. -/
def doubled (Q : Nat) (SU : List (Nat × Nat)) : List (Nat × Nat) :=
  SU ++ SU.map (fun a => (a.1 + Q, a.2))

/-- Check a window search: both sorted lists are sorted, and every candidate fails at an explicit coordinate. -/
def windowCheckAux (P X : Nat) (ts : List (Nat × Nat × Nat)) (m N : Nat) (SR C : List (Nat × Nat)) : Bool :=
  sortedB SR && sortedB C && (sweep P X C SR).all (fun k => failsAny ts m N k)

/-- The full window check for primes `p`, `q`, shifts `sp`, `sq`, and further `(prime, shift)` pairs in `rest`. -/
def windowCheck (p q sp sq : Nat) (rest : List (Nat × Nat)) (m n2 n3 Pinv X N : Nat) : Bool :=
  windowCheckAux (p ^ (n2 * n2)) X
    ((p, sp, n2 + 1) :: (q, sq, n3 + 1) :: rest.map (fun t => (t.1, t.2, 1))) m N
    (sortedR p sp m n2 (q ^ (n3 * n3)) Pinv)
    (doubled (q ^ (n3 * n3)) (sortedU q sq m n3 (q ^ (n3 * n3)) Pinv))

/-- Level `n1 + 1` residues lifted from the level-`n1` residues in the value interval `[lo, hi)`. -/
def liftSlice (p s m n1 lo hi : Nat) : List Nat :=
  lift p s m n1 ((tree p s m n1).filter (fun r => decide (lo ≤ r ∧ r < hi)))

/-- Window check for one slice: the residues of `p` modulo `p^((n1+1)²)` coming from level-`n1` residues in `[lo, hi)`. -/
def windowSliceCheck (p q sp sq : Nat) (rest : List (Nat × Nat)) (m n1 n3 Pinv X N lo hi : Nat) : Bool :=
  windowCheckAux (p ^ ((n1 + 1) * (n1 + 1))) X
    ((p, sp, n1 + 2) :: (q, sq, n3 + 1) :: rest.map (fun t => (t.1, t.2, 1))) m N
    (sortedRL (liftSlice p sp m n1 lo hi) (q ^ (n3 * n3)) Pinv)
    (doubled (q ^ (n3 * n3)) (sortedU q sq m n3 (q ^ (n3 * n3)) Pinv))

end TVGSearch
end LeanCheck
