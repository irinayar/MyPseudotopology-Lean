import LeanCheck.DD3Cluster

/-!
# Axiom report for `DD3Cluster`

Run with `lake env lean LeanCheck/DD3ClusterAxioms.lean` after building `LeanCheck.DD3Cluster`.
Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms LeanCheck.DD3Cluster.geom_three
#print axioms LeanCheck.DD3Cluster.sum_tau3
#print axioms LeanCheck.DD3Cluster.sum_tau3b
#print axioms LeanCheck.DD3Cluster.far_separated3
#print axioms LeanCheck.DD3Cluster.far_beyond3
#print axioms LeanCheck.DD3Cluster.separated_factor_abs
#print axioms LeanCheck.DD3Cluster.close_factor_abs
#print axioms LeanCheck.DD3Cluster.separated_factor3
#print axioms LeanCheck.DD3Cluster.close_factor3
#print axioms LeanCheck.DD3Cluster.sep_cube3
#print axioms LeanCheck.DD3Cluster.close_cube3_G
#print axioms LeanCheck.DD3Cluster.merged_gap_fin3
#print axioms LeanCheck.DD3Cluster.hgrow3_of_merged
#print axioms LeanCheck.DD3Cluster.hmon_of_merged
