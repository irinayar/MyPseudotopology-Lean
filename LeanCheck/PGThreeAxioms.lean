import LeanCheck.PGThreeSelective
import LeanCheck.PGThreeSelectiveCH
import LeanCheck.PGThreeExact
import LeanCheck.PGThreeSparse
import LeanCheck.PGThreeModification
import LeanCheck.PGThreePPoint
import LeanCheck.PGThreeNull
import LeanCheck.PGThreeGeneral
import LeanCheck.PGThreeNonHaus
import LeanCheck.PGThreeIdem
import LeanCheck.PGThreeNormal
import LeanCheck.PGThreeHeight
import LeanCheck.PGThreeWords
import LeanCheck.PGThreeAnySel

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
#print axioms PG.Null.exists_word_any
#print axioms PG.Null.exists_decomp
#print axioms PG.Null.pure_mem_iff
#print axioms PG.Null.length_le
#print axioms PG.Null.nbhd_iff
#print axioms PG.Null.exists_coarsest_iff
#print axioms PG.Null.exists_no_coarsest
#print axioms PG.Idem.nbhd_iff_of_no_idempotent
#print axioms PG.Idem.trivial_of_no_idempotent
#print axioms PG.Idem.independent_no_idempotent
#print axioms PG.Idem.far_zero
#print axioms PG.Idem.sparse_no_idempotent
#print axioms PG.Null.normal_unique
#print axioms PG.Null.replace_letter
#print axioms PG.Null.selective_not_pretopological
#print axioms PG.Height.nsmul_map_le
#print axioms PG.Height.bounded_nbhd
#print axioms PG.Height.bounded_discrete
#print axioms PG.Height.freeAbelian_discrete
#print axioms PG.Height.digits_G
#print axioms PG.Height.digits_discrete
#print axioms PG.Words.coarsest_iff
#print axioms PG.Words.finite_torsion_closure
#print axioms PG.Words.not_pretopological
#print axioms PG.Words.ev_neg
#print axioms PG.Words.word_bounded
#print axioms PG.Words.word_no_idempotent
#print axioms PG.Words.words_no_free_idempotent
#print axioms PG.Words.words_nbhd
#print axioms PG.Words.words_coarsest_iff
#print axioms PG.Words.words_finite_family
#print axioms PG.Words.words_finite_coarsest
#print axioms PG.Words.pure_mem_of_translate
#print axioms PG.Words.ultra_mem_genFam
#print axioms PG.Words.translates_pure_iff
#print axioms PG.Words.mem_word_of_closure
#print axioms PG.Words.translates_word
#print axioms PG.Words.translates_coarsest_iff
#print axioms PG.Words.exists_countable_no_coarsest
#print axioms PG.Words.len_le
#print axioms PG.Words.exists_len
#print axioms PG.Words.abs_val_le
#print axioms PG.Words.dvd_val
#print axioms PG.Words.val_filter_add
#print axioms PG.Words.length_filter_add
#print axioms PG.Words.split_terms
#print axioms PG.Words.powers_no_idempotent
#print axioms PG.Words.D_bounded
#print axioms PG.Words.powers_trivial
#print axioms PG.Words.powers_not_pretopological
#print axioms PG.Words.freeAbelian_trivial
#print axioms PG.Words.digits_trivial
#print axioms PG.AnySel.pwf_cons
#print axioms PG.AnySel.pure_zero_add'
#print axioms PG.AnySel.add_comm_pure
#print axioms PG.AnySel.add_pure_pure
#print axioms PG.AnySel.mem_add_pure_left
#print axioms PG.AnySel.coe_add_le'
#print axioms PG.AnySel.pwf_append
#print axioms PG.AnySel.mem_pwf_cons
#print axioms PG.AnySel.mem_pwf_ofFn
#print axioms PG.AnySel.pwf_free
#print axioms PG.AnySel.disjoint_members
#print axioms PG.AnySel.ne_of_not_iso
#print axioms PG.AnySel.fun_normal_unique
#print axioms PG.AnySel.map_mem
#print axioms PG.AnySel.Hf_le_null
#print axioms PG.AnySel.pwf_mem
#print axioms PG.AnySel.translated_mem
#print axioms PG.AnySel.exists_fword
#print axioms PG.AnySel.normal_mem
#print axioms PG.AnySel.normal_free
#print axioms PG.AnySel.map_eq_pure_add
#print axioms PG.AnySel.normalize
#print axioms PG.AnySel.exists_normal
#print axioms PG.AnySel.normal_form_unique
#print axioms PG.AnySel.null_points_iff
#print axioms PG.AnySel.no_idempotent
#print axioms PG.AnySel.exists_presentation
#print axioms PG.AnySel.family_no_idempotent
#print axioms PG.AnySel.family_nbhd
#print axioms PG.AnySel.family_coarsest_iff
#print axioms PG.AnySel.family_not_pretopological
#print axioms PG.AnySel.family_finite_generators
#print axioms PG.AnySel.family_finite_coarsest
#print axioms PG.AnySel.family_torsion_coarsest
#print axioms PG.AnySel.family_torsionfree_trivial
#print axioms PG.AnySel.allTranslates_sel
#print axioms PG.AnySel.translates_all_null
#print axioms PG.AnySel.allTranslates_coarsest_iff
#print axioms PG.AnySel.all_coarsest_iff_finite_torsion
#print axioms PG.AnySel.closure_example
#print axioms PG.AnySel.closure_example_supply
