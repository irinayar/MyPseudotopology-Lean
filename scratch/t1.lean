import LeanCheck.ChainW2
open LeanCheck
example : T2Space Circ := inferInstance
example : True := by
  letI : TopologicalSpace Circ := circTop
  haveI : T2Space Circ := inferInstance
  trivial
example : @T2Space Circ circTop := inferInstanceAs (T2Space Circ)
example : @T2Space Circ circTop := by unfold circTop; infer_instance
