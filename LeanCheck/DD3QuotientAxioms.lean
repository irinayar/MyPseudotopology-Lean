import LeanCheck.DD3Quotient

/-!
# Axiom report for `DD3Quotient`

Run with `lake env lean LeanCheck/DD3QuotientAxioms.lean` after building `LeanCheck.DD3Quotient`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3Quotient.Jfun_lt_iff
#print axioms LeanCheck.DD3Quotient.integral_of_three
#print axioms LeanCheck.DD3Quotient.compactQuotientCriterion3
#print axioms LeanCheck.DD3Quotient.DD235_of_profile'
#print axioms LeanCheck.DD3Quotient.DD235_of_inputs'
