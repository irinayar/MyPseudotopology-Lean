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
