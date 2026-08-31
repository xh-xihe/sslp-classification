-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_3_3
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_3_4
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_3_5
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_3_6
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_3_7

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P0_1_1_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a4 a5 : Fin 8)
    (h34 : 3 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 3 a4.val a5.val)) 9 := by
  fin_cases a4 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_3_3.cover a5 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_3_4.cover a5 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_3_5.cover a5 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_3_6.cover a5 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_3_7.cover a5 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P0_1_1_3
