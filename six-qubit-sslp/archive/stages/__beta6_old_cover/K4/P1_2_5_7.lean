-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_5_7_7

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P1_2_5_7

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a4 a5 : Fin 8)
    (h34 : 7 <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 5 7 a4.val a5.val)) 9 := by
  fin_cases a4 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_5_7_7.cover a5 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K4.P1_2_5_7
