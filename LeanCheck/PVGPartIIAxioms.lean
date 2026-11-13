import LeanCheck.PVGCyclicCore
import LeanCheck.PVGDenseTrace

/-!
# Axiom report for `PVGProdLimit`, `PVGTotBdd`, `PVGDenseTrace`, `PVGBaireDigits`, `PVGNoLqcCore`, `PVGCyclicCore`

Each declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms PVG.Lac.prodLimit_K
#print axioms PVG.Lac.prodLimit_bohr
#print axioms PVG.Lac.prodLimit
#print axioms PVG.Lac.hyp_of_trace
#print axioms PVG.Lac.totbdd_seq
#print axioms PVG.Lac.totbdd
#print axioms PVG.Lac.denseTrace_core
#print axioms PVG.Lac.denseTrace
#print axioms PVG.Lac.isClosed_FdigDil
#print axioms PVG.Lac.interior_FdigDil
#print axioms PVG.Lac.baire_digits
#print axioms PVG.Lac.exists_not_mem_digits
#print axioms PVG.Lac.step5
#print axioms PVG.Lac.digit_of_trace
#print axioms PVG.Lac.nolqc_core
#print axioms PVG.Lac.bohr_precompact
#print axioms PVG.Lac.int_of_dint
#print axioms PVG.Lac.cyclic_core
