import LeanCheck.PGNullFilters
import LeanCheck.PGXi
import LeanCheck.PGDigit
import LeanCheck.PGBlock
import LeanCheck.PGLimit
import LeanCheck.PGSub
import LeanCheck.PGCompactify
import LeanCheck.PGSUnit
import LeanCheck.PGGenerated
import LeanCheck.PGIdem
import LeanCheck.PGTop
import LeanCheck.PGSumset
import LeanCheck.PGGroupTop
import LeanCheck.PGJoin
import LeanCheck.PGTwoBases
import LeanCheck.PGCompletion
import LeanCheck.PGNoGroup
import LeanCheck.PGSeparation
import LeanCheck.PGBohrGen
import LeanCheck.PGSubgroupBase
import LeanCheck.PGFSRigid
import LeanCheck.PGGameLemma
import LeanCheck.PGOpenSets

/-!
# Axiom report for the PG modules (`PGNullFilters`, `PGXi`, `PGDigit`, `PGBlock`, `PGLimit`, `PGSub`, `PGCompactify`, `PGSUnit`)

Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms PG.conv_zero
#print axioms PG.conv_pure
#print axioms PG.conv_mono
#print axioms PG.conv_ultra
#print axioms PG.conv_add
#print axioms PG.conv_neg
#print axioms PG.hausdorff_iff
#print axioms PG.conv_iff_of_conv
#print axioms PG.nullFamily_of_conv
#print axioms PG.conv_eq_of_conv
#print axioms PG.isPGConv_xi
#print axioms PG.xi_hausdorff
#print axioms PG.Vxi_eq_map
#print axioms PG.pretopological_iff
#print axioms PG.pretopological_zero_iff
#print axioms PG.not_pretopological_of_recipe
#print axioms PG.isOpenXi_iff
#print axioms PG.isOpen_isOpenXi
#print axioms PG.D_add
#print axioms PG.D_neg
#print axioms PG.Ip_admissible
#print axioms PG.Ip_pow
#print axioms PG.gap_split
#print axioms PG.split_zero
#print axioms PG.isOpenXi_iff_closed_traces
#print axioms PG.thin_set_closed
#print axioms PG.isOpenXi_translate
#print axioms PG.isOpenXi_neg
#print axioms PG.xi_converges_op
#print axioms PG.isOpenXi_of_op
#print axioms PG.closure_image_inter_range
#print axioms PG.closure_add_subset
#print axioms PG.closure_neg_subset
#print axioms PG.pow_mul_pow_inj
#print axioms PG.ratio_inj
#print axioms PG.exists_block
#print axioms PG.tuple_of_block
#print axioms PG.block_cand
#print axioms PG.Vals_finite
#print axioms PG.reach_finite
#print axioms PG.inter_finite
#print axioms PG.Ip_inter_finite
#print axioms PG.Ip_inter_eq
#print axioms PG.exists_ultra_le_map₂
#print axioms PG.u_mem_genNull
#print axioms PG.genNull_nullFamily
#print axioms PG.genNull_le
#print axioms PG.mem_of_subgroup_mem
#print axioms PG.genNull_hausdorff
#print axioms PG.int_hausdorff
#print axioms PG.Lev.genUlt
#print axioms PG.Lev.add
#print axioms PG.Lev.neg
#print axioms PG.exists_lev_of_genUlt
#print axioms PG.Pw_mem
#print axioms PG.Pw_mono
#print axioms PG.plusF_mem
#print axioms PG.not_pretopological
#print axioms PG.topNull_nullFamily
#print axioms PG.genNull_subset_topNull
#print axioms PG.genNull_subset_topNull_iff
#print axioms PG.null_le_nhds_iff
#print axioms PG.conv_le_nhds
#print axioms PG.isCompact_Pw
#print axioms PG.closure_Pw
#print axioms PG.nested_sums_family
#print axioms PG.nested_sums_nhds
#print axioms PG.exists_open_half
#print axioms PG.neg_mem_Vxi
#print axioms PG.mem_Vxi_of_isOpenXi
#print axioms PG.half_of_groupTop
#print axioms PG.nested_sums_Vxi
#print axioms PG.no_groupTop_of_sums
#print axioms PG.joinI_admissible
#print axioms PG.joinI_proper_of
#print axioms PG.left_subset_joinI
#print axioms PG.right_subset_joinI
#print axioms PG.xi_mono_ideal
#print axioms PG.joinI_Ip_iff
#print axioms PG.univ_notin_join_of_finite
#print axioms PG.Ipq_admissible
#print axioms PG.exists_nondegenerate_sub
#print axioms PG.uniformContinuous_of_group
#print axioms PG.huc_of_sub
#print axioms PG.exists_extension
#print axioms PG.denseRange_inclusion_closure
#print axioms PG.extension_compat
#print axioms PG.trace_open
#print axioms PG.trace_cont_of_contains
#print axioms PG.exists_nhds_inter_subset_of_Vxi
#print axioms PG.isOpenXi_compl_of_cover
#print axioms PG.no_groupTop_of_cover
#print axioms PG.filter_flip
#print axioms PG.separation
#print axioms PG.lev4
#print axioms PG.exists_A_of_mem_lev4
#print axioms PG.nhds_le_lev4
#print axioms PG.genNull_eq_topNull
#print axioms PG.halving4
#print axioms PG.nhds_le_of_bog
#print axioms PG.subgroup_mem_GenUlt
#print axioms PG.subgroup_mem_Vgen
#print axioms PG.exists_sum_of_mem_plusF_two
#print axioms PG.Vgen_mem_genNull
#print axioms PG.fs_rigid
#print axioms PG.no_multiple
#print axioms PG.finite_lists
#print axioms PG.game_lemma
#print axioms PG.mem_of_mem_Vgen_lev
#print axioms PG.lev_negF
#print axioms PG.negF_mem
#print axioms PG.exists_nsmul_mem
