/-!
# Verified exhaustive search: definitions (core Lean only, so that instances load fast and run in the kernel)

For primes `p`, `q`, shifts `s_p, s_q ∈ {0, 1}` and a radius `1/m`, coordinate `n` of `p` passes for the natural number `k ≥ 1` iff
`m * idist (k + p^(n*n) - s) (p^(n*n)) < p^(n*n)` where `idist k Q` is the distance from `k` to a multiple of `Q`.

* `tree p s m n` is the list of all `x < p^(n*n)` passing the coordinates `1..n` (built by lifting level by level).
* `candidates P Q Pinv X T2 T3` lists the integers `k ∈ [1, X]` with `k mod P ∈ T2` and `k mod Q ∈ T3` (CRT with `Pinv` inverse of `P` mod `Q`).
* `searchChunk` tests every candidate of a slice of `T2` against further coordinates; if all fail, no `k ≤ X` is in the ball.

The correctness theorems are in `TVGPlusSearch.lean` (Mathlib); the instances are in `TVGSearchData*.lean`.
-/

namespace LeanCheck
namespace TVGSearch

/-- Distance from `k` to the nearest multiple of `Q`. -/
def idist (k Q : Nat) : Nat := if k % Q ≤ Q - k % Q then k % Q else Q - k % Q

/-- Coordinate `n` of the prime `p`, shift `s`, radius `1/m`, for the natural number `k`. -/
def good (p s m n k : Nat) : Bool :=
  decide (m * idist (k + p ^ (n * n) - s) (p ^ (n * n)) < p ^ (n * n))

/-- All coordinates `1..n` pass. -/
def goodUpTo (p s m : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, k => goodUpTo p s m n k && good p s m (n + 1) k

/-- Lift a list of level-`n` residues to the level-`(n+1)` residues passing coordinate `n+1`. -/
def lift (p s m n : Nat) (L : List Nat) : List Nat :=
  L.flatMap (fun r =>
    ((List.range (p ^ ((n + 1) * (n + 1)) / p ^ (n * n))).map (fun t => r + p ^ (n * n) * t)).filter
      (fun x => good p s m (n + 1) x))

/-- Residues modulo `p^(n*n)` passing the coordinates `1..n`. -/
def tree (p s m : Nat) : Nat → List Nat
  | 0 => [0]
  | n + 1 => lift p s m n (tree p s m n)

/-- The integers `k ∈ [1, X]` assembled by the Chinese remainder theorem from `T2` (mod `P`) and `T3` (mod `Q`). -/
def candidates (P Q Pinv X : Nat) (T2 T3 : List Nat) : List Nat :=
  T2.flatMap (fun r => T3.filterMap (fun ρ =>
    if 1 ≤ r + P * (((ρ + Q - r % Q) * Pinv) % Q) ∧ r + P * (((ρ + Q - r % Q) * Pinv) % Q) ≤ X then
      some (r + P * (((ρ + Q - r % Q) * Pinv) % Q))
    else none))

/-- Some coordinate `start .. start + N - 1` of `p` fails for `k`. -/
def failsFrom (p s m start N k : Nat) : Bool := (List.range N).any (fun j => !(good p s m (start + j) k))

/-- Some listed `(prime, shift, start)` has a failing coordinate. -/
def failsAny (ts : List (Nat × Nat × Nat)) (m N k : Nat) : Bool :=
  ts.any (fun t => failsFrom t.1 t.2.1 m t.2.2 N k)

/-- Setup conditions: `X < P * Q` and `Pinv` is an inverse of `P` modulo `Q`. -/
def searchSetup (p q n2 n3 Pinv X : Nat) : Bool :=
  decide (X < p ^ (n2 * n2) * q ^ (n3 * n3)) && decide ((p ^ (n2 * n2) * Pinv) % q ^ (n3 * n3) = 1 % q ^ (n3 * n3))

/-- Check the slice `lo .. lo + cnt - 1` of the level-`n2` residues of `p`: every candidate fails somewhere. -/
def searchChunk (p q sp sq : Nat) (rest : List (Nat × Nat)) (m n2 n3 Pinv X lo cnt N : Nat) : Bool :=
  (candidates (p ^ (n2 * n2)) (q ^ (n3 * n3)) Pinv X
      (((tree p sp m n2).drop lo).take cnt) (tree q sq m n3)).all
    (fun k => failsAny ((p, sp, n2 + 1) :: (q, sq, n3 + 1) :: rest.map (fun t => (t.1, t.2, 1))) m N k)

/-- The number of level-`n2` residues of `p`. -/
def treeLen (p s m n : Nat) : Nat := (tree p s m n).length

/-- All coordinates `1..N` of every listed `(prime, shift)` pass for `k` (used for membership; with the tail test). -/
def memberCheck (ps : List (Nat × Nat)) (m N k : Nat) : Bool :=
  ps.all (fun t => goodUpTo t.1 t.2 m N k && decide (m * (k - t.2) < t.1 ^ ((N + 1) * (N + 1))))

end TVGSearch
end LeanCheck
