import LeanCheck.PVGAlgebra
import LeanCheck.PVGInterpolation
import LeanCheck.PVGCharacters

/-!
# Axiom report for the PVG modules

Run with `lake env lean LeanCheck/PVGAxioms.lean` after `lake build LeanCheck.PVGAlgebra
LeanCheck.PVGInterpolation LeanCheck.PVGCharacters`. Each declaration should depend only on
`propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms PVG.maximal_admissible_iff
#print axioms PVG.exists_maximal_admissible
#print axioms PVG.no_common_admissible
#print axioms PVG.ker_isCompl
#print axioms PVG.retraction_unique
#print axioms PVG.retractionEquiv
#print axioms PVG.rank_eq_of_card
#print axioms PVG.card_retractions
#print axioms PVG.interpolation
#print axioms PVG.interpolation_round
#print axioms PVG.limits_ne
#print axioms PVG.distinct_limits
#print axioms PVG.bounded_conv_euclid
#print axioms PVG.trivial_intersection
