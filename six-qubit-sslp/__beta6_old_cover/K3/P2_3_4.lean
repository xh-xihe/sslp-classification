-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P2_3_4_4
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P2_3_4_5
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P2_3_4_6
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P2_3_4_7

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P2_3_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a3 a4 a5 : Fin 8)
    (h23 : 4 <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 4 a3.val a4.val a5.val)) 9 := by
  fin_cases a3 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P2_3_4_4.cover a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P2_3_4_5.cover a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P2_3_4_6.cover a4 a5 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P2_3_4_7.cover a4 a5 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P2_3_4
