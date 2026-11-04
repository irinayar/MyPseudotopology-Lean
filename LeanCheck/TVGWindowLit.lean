import LeanCheck.TVGPlusWindow

/-!
# Window search with a precomputed sorted 3-adic list

`windowSliceCheckC` is `windowSliceCheck` with the sorted 3-adic list `SU` passed as an argument, so that a long literal
list can be used without recomputing it in every kernel run; `slice_none_lit` needs the one-time equation
`SU = sortedU ...`, also checked by the kernel.
-/

namespace LeanCheck
namespace TVGSearch

open MixedPrime

def windowSliceCheckC (p q sp sq : Nat) (rest : List (Nat × Nat)) (m n1 n3 Pinv X N lo hi : Nat)
    (SU : List (Nat × Nat)) : Bool :=
  windowCheckAux (p ^ ((n1 + 1) * (n1 + 1))) X
    ((p, sp, n1 + 2) :: (q, sq, n3 + 1) :: rest.map (fun t => (t.1, t.2, 1))) m N
    (sortedRL (liftSlice p sp m n1 lo hi) (q ^ (n3 * n3)) Pinv)
    (doubled (q ^ (n3 * n3)) SU)

theorem slice_none_lit {p q sp sq : ℕ} {rest : List (ℕ × ℕ)} {m n1 n3 Pinv X N lo hi : ℕ}
    {SU : List (ℕ × ℕ)}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hsp : sp ≤ 1) (hsq : sq ≤ 1) (hrest : ∀ t ∈ rest, 2 ≤ t.1 ∧ t.2 ≤ 1)
    (hm : 0 < m) (hn3 : 1 ≤ n3)
    (hsetup : searchSetup p q (n1 + 1) n3 Pinv X = true)
    (hSU : SU = sortedU q sq m n3 (q ^ (n3 * n3)) Pinv)
    (hcheck : windowSliceCheckC p q sp sq rest m n1 n3 Pinv X N lo hi SU = true) :
    NoneSlice p q sp sq rest m n1 X lo hi := by
  subst hSU
  exact slice_none hp hq hsp hsq hrest hm hn3 hsetup hcheck

#print axioms slice_none_lit

end TVGSearch
end LeanCheck
