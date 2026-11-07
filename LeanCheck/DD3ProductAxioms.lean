import LeanCheck.DD3Product

/-!
# Axiom report for `DD3Product`

Run with `lake env lean LeanCheck/DD3ProductAxioms.lean` after building `LeanCheck.DD3Product`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3Product.sum_inv_cube_gen
#print axioms LeanCheck.DD3Product.product_final_gen
#print axioms LeanCheck.DD3Product.product_final3
