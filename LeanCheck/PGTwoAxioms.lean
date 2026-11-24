import LeanCheck.PGTwoGeneration
import LeanCheck.PGTwoLattice
import LeanCheck.PGTwoReflection
import LeanCheck.PGTwoCoreflection

/-! Axiom check for the modules of `PGtwo` (Phase A): every `#print axioms` below should list only
`propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms PG.genFam_nullFamily
#print axioms PG.subset_genFam
#print axioms PG.genFam_le
#print axioms PG.map_zsmul_mem
#print axioms PG.genNull_eq_genFam
#print axioms PG.nullFamily_top
#print axioms PG.nullFamily_bot
#print axioms PG.nullFamily_sInter
#print axioms PG.nullFamily_sup
#print axioms PG.hausdorff_mono
#print axioms PG.vic_le_add
#print axioms PG.exists_topology
#print axioms PG.isNbhdFilter_halveFilter
#print axioms PG.halveFilter_le
#print axioms PG.exists_finest
#print axioms PG.reflector_univ
#print axioms PG.kmem_iff
#print axioms PG.xiCont_iff
#print axioms PG.univ_of_coarsest
#print axioms PG.kernel_open_of_trivial
#print axioms PG.finite_member_eq_pure
#print axioms PG.eligible_eq_pure
#print axioms PG.kernel_open_of_condM
#print axioms PG.coarsest_of_coreflection
