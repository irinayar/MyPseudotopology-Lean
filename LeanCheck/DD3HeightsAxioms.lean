import LeanCheck.DD3Heights

/-!
# Axiom report for `DD3Heights`

Run with `lake env lean LeanCheck/DD3HeightsAxioms.lean` after building `LeanCheck.DD3Heights`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3Heights.exists_level
#print axioms LeanCheck.DD3Heights.bad_unique
#print axioms LeanCheck.DD3Heights.exists_buffered3
