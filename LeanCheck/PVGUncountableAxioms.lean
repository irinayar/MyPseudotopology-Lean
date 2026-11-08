import LeanCheck.PVGUncountable

/-!
# Axiom report for `PVGUncountable`

Run with `lake env lean LeanCheck/PVGUncountableAxioms.lean` after building `LeanCheck.PVGUncountable`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms PVG.Q95.free_map_fto
#print axioms PVG.Q95.L_rep
#print axioms PVG.Q95.prop_uncountable_gen
#print axioms PVG.Q95.disjoint_span_L
#print axioms PVG.Q95.prop_uncountable
#print axioms PVG.Q95.exists_retraction_of_family
