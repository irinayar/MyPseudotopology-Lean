import LeanCheck.PGNullFilters
import LeanCheck.PGXi
import LeanCheck.PGDigit
import LeanCheck.PGBlock
import LeanCheck.PGLimit

/-!
# Axiom report for the PG modules (`PGNullFilters`, `PGXi`, `PGDigit`, `PGBlock`, `PGLimit`)

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
