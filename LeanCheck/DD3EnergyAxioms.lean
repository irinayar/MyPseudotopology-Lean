import LeanCheck.DD3Energy

/-!
# Axiom report for `DD3Energy`

Run with `lake env lean LeanCheck/DD3EnergyAxioms.lean` after building `LeanCheck.DD3Energy`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3Energy.spectral_step3
#print axioms LeanCheck.DD3Energy.spectral_window3
#print axioms LeanCheck.DD3Energy.nu_cos3
#print axioms LeanCheck.DD3Energy.energy3_le_psi
#print axioms LeanCheck.DD3Energy.energy3_le_arc
#print axioms LeanCheck.DD3Energy.energy3_normalized
#print axioms LeanCheck.DD3Energy.collision_Aset_eq_energyE3
#print axioms LeanCheck.DD3Energy.collision_support
