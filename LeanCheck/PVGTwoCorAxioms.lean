import LeanCheck.PVGTwoCor
import LeanCheck.PVGTwoKRAxioms

/-! Axiom report for `PVGTwoCor` and for `PVGTwoDescribe` with the explicit definition of `parTop`. -/

#print axioms PVG.Two.parTop_spec
#print axioms PVG.Two.parTop_hasBasis
#print axioms PVG.Two.gamAll_hasBasis
#print axioms PVG.Two.gamAll_le
#print axioms PVG.Two.finest_described
#print axioms PVG.Two.allserving
#print PVG.Two.parTop
#check @PVG.Two.gamAll_hasBasis
#check @PVG.Two.allserving
