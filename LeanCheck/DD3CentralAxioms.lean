import LeanCheck.DD3Central

/-!
# Axiom report for `DD3Central`

Run with `lake env lean LeanCheck/DD3CentralAxioms.lean` after building `LeanCheck.DD3Central`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3Central.S0_le3
#print axioms LeanCheck.DD3Central.final_arith3
#print axioms LeanCheck.DD3Central.central_bound3
