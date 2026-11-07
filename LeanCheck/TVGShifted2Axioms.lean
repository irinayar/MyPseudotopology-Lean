import LeanCheck.TVGShiftedCert2
import LeanCheck.TVGIncomparable

/-!
# Axiom report for `TVGShiftedCert2` and `TVGIncomparable`

Run with `lake env lean LeanCheck/TVGShifted2Axioms.lean` after building both modules. Each declaration
should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.ShiftedCert.wit990_mem
#print axioms LeanCheck.ShiftedCert.wit1100_mem
#print axioms LeanCheck.ShiftedCert.wit2114_mem
#print axioms LeanCheck.ShiftedCert.wit2790_mem
#print axioms LeanCheck.ShiftedCert.wit5272_mem
#print axioms LeanCheck.Incomparable.exists_centered
#print axioms LeanCheck.Incomparable.reverse_direction
#print axioms LeanCheck.Incomparable.dvd_of_nrm_lt
#print axioms LeanCheck.Incomparable.nrm_lower_inv
#print axioms LeanCheck.Incomparable.Pn_pow_le
#print axioms LeanCheck.Incomparable.first_direction
