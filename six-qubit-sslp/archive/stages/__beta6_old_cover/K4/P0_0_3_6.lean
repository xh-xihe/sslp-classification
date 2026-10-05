-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_3_6_6
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_3_6_7

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P0_0_3_6

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a4 a5 : Fin 8)
    (h34 : 6 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 6 a4.val a5.val)) 9 := by
  fin_cases a4 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_3_6_6.cover a5 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_3_6_7.cover a5 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P0_0_3_6
