import LeanCheck.PVGTwoDescribe
import LeanCheck.PVGTwoMany

/-! Axiom report for `PVGTwoStab`, `PVGTwoDescribe` and `PVGTwoMany`. `Stab.KaltonRoberts` is a hypothesis of
`real_box`, `inf_box`, `gamAll_le` and `finest_described`, not an axiom. -/

#print axioms PVG.Stab.lift
#print axioms PVG.Stab.real_box
#print axioms PVG.Stab.signed_box
#print axioms PVG.Stab.inf_box
#print axioms PVG.Two.gamAll_le
#print axioms PVG.Two.finest_described
#print axioms PVG.Two.odd_points_gen
#print axioms PVG.Two.many_embed
#print axioms PVG.Two.many_card
#check @PVG.Two.finest_described
