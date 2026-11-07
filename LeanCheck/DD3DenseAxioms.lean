import LeanCheck.DD3Dense

/-!
# Axiom report for `DD3Dense`

Run with `lake env lean LeanCheck/DD3DenseAxioms.lean` after building `LeanCheck.DD3Dense`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3Dense.syndeticW3_of_dense
#print axioms LeanCheck.DD3Dense.dense_step3
#print axioms LeanCheck.DD3Dense.denseDifferences3_of_energy
#print axioms LeanCheck.DD3Dense.JA3_of_energy
#print axioms LeanCheck.DD3Dense.DD_of_JA3
#print axioms LeanCheck.DD3Dense.DD235_of_energy
