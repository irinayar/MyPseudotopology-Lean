import LeanCheck.DD3Sep

/-!
# Axiom report for `DD3Sep`

Run with `lake env lean LeanCheck/DD3SepAxioms.lean` after building `LeanCheck.DD3Sep`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3Sep.sep_easy
#print axioms LeanCheck.DD3Sep.HTT3_exists
#print axioms LeanCheck.DD3Sep.DD235_of_pairs
#print axioms LeanCheck.DD3Sep.DD235_of_pairs_A
