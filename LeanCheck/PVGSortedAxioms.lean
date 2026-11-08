import LeanCheck.PVGSorted

/-!
# Axiom report for `PVGSorted`

Run with `lake env lean LeanCheck/PVGSortedAxioms.lean` after building `LeanCheck.PVGSorted`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms PVG.Q95.exists_sort
#print axioms PVG.Q95.independence_listing
#print axioms PVG.Q95.listing_of_sep
#print axioms PVG.Q95.independence_sep
#print axioms PVG.Q95.disjoint_span_L_family
#print axioms PVG.Q95.prop_uncountable_family
#print axioms PVG.Q95.exists_retraction_of_joint_family
#print axioms PVG.Q95.lemma_separation
#print axioms PVG.Q95.depth_admissible
#print axioms PVG.Q95.corollary_indepB
