-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P7_7

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P7

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a1 a2 a3 a4 a5 : Fin 8)
    (h01 : 7 <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 7 a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a1 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P7_7.cover a2 a3 a4 a5 h12 h23 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P7
