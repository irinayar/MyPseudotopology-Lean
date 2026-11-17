import LeanCheck.TPPQuartic
import LeanCheck.TPPFirstGap
import LeanCheck.TPPConv
import LeanCheck.TPPSep
import LeanCheck.TPPElim
import LeanCheck.TPPCross

/-!
# Axiom report for the ThreePrimePlus modules

Run with `lake env lean LeanCheck/TPPAxioms.lean` after building the six modules. Each declaration
should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms TPP.quartic_eq_prod
#print axioms TPP.quartic_eq_zero_of_dot_zero
#print axioms TPP.quartic_bound
#print axioms TPP.first_gap
#print axioms TPP.divisor_near_resonant
#print axioms TPP.mass_le
#print axioms TPP.first_large
#print axioms TPP.geom_thresholds
#print axioms TPP.exp_sub_one_lower
#print axioms TPP.not_eq_of_lt
#print axioms TPP.abs_form_eq
#print axioms TPP.sep_of_matveev
#print axioms TPP.elim_identity
#print axioms TPP.elim_bound
#print axioms TPP.proportional_of_sep
#print axioms TPP.cross_of_elim
#print axioms TPP.exists_primitive_gen
#print axioms TPP.dot_cross_eq
#print axioms TPP.cross_decomp_1
#print axioms TPP.cross_decomp_2
#print axioms TPP.cross_decomp_3
#print axioms TPP.exponent_pos
