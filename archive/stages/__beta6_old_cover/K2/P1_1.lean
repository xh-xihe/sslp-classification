-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_1
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_2
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_3
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_4
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_5
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_6
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_7

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P1_1

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a2 a3 a4 a5 : Fin 8)
    (h12 : 1 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_1.cover a3 a4 a5 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_2.cover a3 a4 a5 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_3.cover a3 a4 a5 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_4.cover a3 a4 a5 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_5.cover a3 a4 a5 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_6.cover a3 a4 a5 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_1_7.cover a3 a4 a5 h23 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P1_1
