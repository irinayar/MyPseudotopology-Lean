import LeanCheck.TVGShiftedJump
import LeanCheck.TVGShiftedEnergy
import LeanCheck.TVGShiftedCert

/-!
# Axiom report for the shifted-height modules (jump argument, collision energy, certificates)

Run with `lake env lean LeanCheck/TVGShiftedAxioms.lean` after building the three modules. Each
declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.ShiftedJump.exists_jump
#print axioms LeanCheck.ShiftedJump.jump_abstract
#print axioms LeanCheck.ShiftedJump.Dvis_unbounded
#print axioms LeanCheck.ShiftedJump.shifted_jump
#print axioms LeanCheck.ShiftedJump.shifted_limsup_lower
#print axioms LeanCheck.ShiftedEnergy.cs_bound
#print axioms LeanCheck.ShiftedEnergy.Lbound_le_card
#print axioms LeanCheck.ShiftedEnergy.energy_criterion
#print axioms LeanCheck.ShiftedEnergy.energy_criterion_sq
#print axioms LeanCheck.ShiftedEnergy.energy_arithmetic
#print axioms LeanCheck.ShiftedEnergy.unit_target_iff
#print axioms LeanCheck.ShiftedCert.Pn_sq_le
#print axioms LeanCheck.ShiftedCert.mem_Wsh_of_cert
#print axioms LeanCheck.ShiftedCert.fwd627_mem
#print axioms LeanCheck.ShiftedCert.fwd665_mem
#print axioms LeanCheck.ShiftedCert.rev665_mem
#print axioms LeanCheck.ShiftedCert.fwd683_mem
#print axioms LeanCheck.ShiftedCert.rev683_mem
#print axioms LeanCheck.ShiftedCert.sgn715_mem
