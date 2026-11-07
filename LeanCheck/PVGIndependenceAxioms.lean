import LeanCheck.PVGIndependence

/-!
# Axiom report for `PVGIndependence`

Run with `lake env lean LeanCheck/PVGIndependenceAxioms.lean` after building `LeanCheck.PVGIndependence`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms PVG.Q95.arcs
#print axioms PVG.Q95.arcs_signed
#print axioms PVG.Q95.exists_disjoint_family
#print axioms PVG.Q95.independence
#print axioms PVG.Q95.independence_finset
#print axioms PVG.Q95.linearIndependent_L
