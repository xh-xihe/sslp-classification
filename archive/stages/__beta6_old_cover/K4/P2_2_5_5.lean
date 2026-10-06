-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_5_5_5
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_5_5_6
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_5_5_7

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P2_2_5_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a4 a5 : Fin 8)
    (h34 : 5 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 5 5 a4.val a5.val)) 9 := by
  fin_cases a4 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_5_5_5.cover a5 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_5_5_6.cover a5 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_5_5_7.cover a5 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P2_2_5_5
