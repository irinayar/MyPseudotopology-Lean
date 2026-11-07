import LeanCheck.DD3Assemble

/-!
# Axiom report for `DD3Assemble`

Run with `lake env lean LeanCheck/DD3AssembleAxioms.lean` after building `LeanCheck.DD3Assemble`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3Assemble.htop3_of_large
#print axioms LeanCheck.DD3Assemble.bases_differ3
#print axioms LeanCheck.DD3Assemble.level_sep3
#print axioms LeanCheck.DD3Assemble.level_close3
#print axioms LeanCheck.DD3Assemble.non_deep_card_le_three
#print axioms LeanCheck.DD3Assemble.prod_f_bound3
