import LeanCheck.DD3Reduction

/-!
# Axiom report for `DD3Reduction`

Run with `lake env lean LeanCheck/DD3ReductionAxioms.lean` after building `LeanCheck.DD3Reduction`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3.three_parts_zero
#print axioms LeanCheck.DD3.sum_rep3
#print axioms LeanCheck.DD3.card_V3_ge
#print axioms LeanCheck.DD3.sum_sq_rep3
#print axioms LeanCheck.DD3.energy3_eq_acf
#print axioms LeanCheck.DD3.syndetic_of_dense_difference3
#print axioms LeanCheck.DD3.merged_gap4
#print axioms LeanCheck.DD3.merged_gap_seq3
#print axioms LeanCheck.DD3.merged_gap_seq_odd3
#print axioms LeanCheck.DD3.merged_growth_exp3
#print axioms LeanCheck.DD3.window_card_le_three
