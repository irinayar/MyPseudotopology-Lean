import LeanCheck.PVGTwoFUGen
import LeanCheck.PVGTwoServed

/-! Axiom report for `PVGTwoFUGen`. The sequence `sT` satisfies the assumptions. -/

noncomputable def PVG.Two.Gen.lacSeq_sT : PVG.Two.Gen.LacSeq := ⟨PVG.Two.sT, PVG.Two.sT_ne, PVG.Two.sT_ratio⟩

#print axioms PVG.Two.Gen.tconv_pure
#print axioms PVG.Two.Gen.tconv_mono
#print axioms PVG.Two.Gen.tconv_of_ultra
#print axioms PVG.Two.Gen.tconv_add
#print axioms PVG.Two.Gen.tconv_mul
#print axioms PVG.Two.Gen.tconv_nhds
#print axioms PVG.Two.Gen.tconv_sT
#print axioms PVG.Two.Gen.tconv_unique
#print axioms PVG.Two.Gen.tconv_frechet
#print axioms PVG.Two.Gen.tconv_not_pretopological
#print axioms PVG.Two.Gen.xi_iff
