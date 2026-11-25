import LeanCheck.PGThreeSelective
import LeanCheck.PGThreeSelectiveCH
import LeanCheck.PGThreeExact
import LeanCheck.PGThreeSparse
import LeanCheck.PGThreeModification
import LeanCheck.PGThreePPoint
import LeanCheck.PGThreeNull
import LeanCheck.PGThreeGeneral

/-! Axiom check for the modules of `PGthree`: every `#print axioms` below should list only
`propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms PG.Sel.IsSel.pseudoInter
#print axioms PG.Sel.IsSel.injOn_of_finite_fibres
#print axioms PG.Sel.iso_of_injOn
#print axioms PG.Sel.separation
#print axioms PG.Sel.tuples
#print axioms PG.Sel.not_large_of_finLast
#print axioms PG.Sel.exists_avoiding
#print axioms PG.Sel.genFam_hausdorff
#print axioms PG.Sel.mem_vic_iff_of_dense
#print axioms PG.Sel.exists_selective_avoiding
#print axioms PG.Sel.exists_dense_selective
#print axioms PG.Sel.exists_hausdorff_vicinity
#print axioms PG.Sel.exists_hausdorff_cofin_int
#print axioms PG.Sel.large_snoc
#print axioms PG.Sel.exists_avoiding_general
#print axioms PG.Sel.genFam_hausdorff_general
#print axioms PG.Sel.dense_iff_supply
#print axioms PG.Sel.towerProp_of_CH
#print axioms PG.Sel.exists_selective_avoiding_of_tower
#print axioms PG.Sel.supply_of_towerProp
#print axioms PG.Sel.supply_of_CH
#print axioms PG.Sel.genFam_hausdorff_iff
#print axioms PG.Sel.finite_or_zero_of_vicinity
#print axioms PG.Sel.exists_vicinity_of_condition
#print axioms PG.Sel.not_vicinity_boolean_times_int
#print axioms PG.Sel.exists_vicinity_boolean
#print axioms PG.Sparse.exists_weight
#print axioms PG.Sparse.lt_abs_val
#print axioms PG.Sparse.val_inj
#print axioms PG.Sparse.expansion
#print axioms PG.Sparse.sparse_strict
#print axioms PG.Sel.exists_thinned
#print axioms PG.Sel.exists_basic_subset
#print axioms PG.Sel.exists_halved
#print axioms PG.Sel.modification_isGroupTopology
#print axioms PG.Sel.exists_sparse_of_selective
#print axioms PG.Sel.selective_int_strict
#print axioms PG.PPoint.IsPPoint.pseudoInter
#print axioms PG.PPoint.exists_Uset_subset
#print axioms PG.PPoint.ppoint_modification
#print axioms PG.PPoint.exists_open_not_nhds
#print axioms PG.PPoint.modification_isGroupTopology_iff
#print axioms PG.Null.mem_pw_ofFn
#print axioms PG.Null.exists_word
#print axioms PG.Null.null_free_iff
#print axioms PG.Null.pw_injective
#print axioms PG.Null.only_trivial
#print axioms PG.Null.kernel_open
#print axioms PG.Null.exists_discrete_coreflection
#print axioms PG.Null.null_free_iff_general
#print axioms PG.Null.pw_injective_general
#print axioms PG.Null.only_trivial_general
#print axioms PG.Null.kernel_open_general
#print axioms PG.Null.exists_discrete_coreflection_general
#print axioms PG.PPoint.isOpenMod_compl_singleton
#print axioms PG.PPoint.ppoint_hausdorff
