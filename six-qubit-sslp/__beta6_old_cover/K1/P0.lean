-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_0
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_1
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_2
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_3
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_4
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_5
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_6
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_7

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P0

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a1 a2 a3 a4 a5 : Fin 8)
    (h01 : 0 <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a1 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_0.cover a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_1.cover a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_2.cover a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_3.cover a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_4.cover a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_5.cover a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_6.cover a2 a3 a4 a5 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P0_7.cover a2 a3 a4 a5 h12 h23 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P0
