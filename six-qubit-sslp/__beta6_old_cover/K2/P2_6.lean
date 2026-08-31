-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P2_6_6
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P2_6_7

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P2_6

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a2 a3 a4 a5 : Fin 8)
    (h12 : 6 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 6 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P2_6_6.cover a3 a4 a5 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P2_6_7.cover a3 a4 a5 h23 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P2_6
