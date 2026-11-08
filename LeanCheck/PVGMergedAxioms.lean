import LeanCheck.PVGMerged

/-!
# Axiom report for `PVGMerged`

Run with `lake env lean LeanCheck/PVGMergedAxioms.lean` after building `LeanCheck.PVGMerged`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms PVG.Q95.free_map
#print axioms PVG.Q95.L_comp
#print axioms PVG.Q95.independence_merged
