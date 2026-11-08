import LeanCheck.DD3GenSorted

/-!
# Axiom report for `DD3GenSorted`

Run with `lake env lean LeanCheck/DD3GenSortedAxioms.lean` after building `LeanCheck.DD3GenSorted`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3Gen.log_scaleE
#print axioms LeanCheck.DD3Gen.chainE_sq
#print axioms LeanCheck.DD3Gen.keyE_inj3
#print axioms LeanCheck.DD3Gen.sorted_strict3E
#print axioms LeanCheck.DD3Gen.pairs3_map_FkerE
#print axioms LeanCheck.DD3Gen.exists_sorted3E
#print axioms LeanCheck.DD3Gen.arc_mass_sorted3E
#print axioms LeanCheck.DD3Gen.same_chain_gapE
#print axioms LeanCheck.DD3Gen.GapE_sq
