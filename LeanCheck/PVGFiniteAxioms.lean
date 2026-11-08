import LeanCheck.PVGFinite

/-!
# Axiom report for `PVGFinite`

Run with `lake env lean LeanCheck/PVGFiniteAxioms.lean` after building `LeanCheck.PVGFinite`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms PVG.Q95.decomp
#print axioms PVG.Q95.jointSep_fin
#print axioms PVG.Q95.thin_joint
#print axioms PVG.Q95.finite_family
#print axioms PVG.Q95.countable_family
#print axioms PVG.Q95.exists_retraction_countable
#print axioms PVG.Q95.exists_retraction_finite
