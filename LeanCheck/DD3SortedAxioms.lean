import LeanCheck.DD3Sorted

/-!
# Axiom report for `DD3Sorted`

Run with `lake env lean LeanCheck/DD3SortedAxioms.lean` after building `LeanCheck.DD3Sorted`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3Sorted.key_inj3
#print axioms LeanCheck.DD3Sorted.pairs3Of_nodup
#print axioms LeanCheck.DD3Sorted.sorted_strict3
#print axioms LeanCheck.DD3Sorted.exists_sorted3
#print axioms LeanCheck.DD3Sorted.arc_mass_product3
#print axioms LeanCheck.DD3Sorted.arc_mass_sorted3
