import LeanCheck.PVGSequences

/-!
# Axiom report for `PVGSequences`

Run with `lake env lean LeanCheck/PVGSequencesAxioms.lean` after building `LeanCheck.PVGSequences`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms PVG.Q95.L_add
#print axioms PVG.Q95.L_smul
#print axioms PVG.Q95.L_const
#print axioms PVG.Q95.interpolation_bounded
#print axioms PVG.Q95.L_sub_ne_e
#print axioms PVG.Q95.exists_lacunary_subseq
#print axioms PVG.Q95.R1
#print axioms PVG.Q95.R1_linear
#print axioms PVG.Q95.R4
#print axioms PVG.Q95.R1_R4
#print axioms PVG.Q95.e_one_ne_zero
