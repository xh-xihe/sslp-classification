-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_4_4
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_4_5
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_4_6
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_4_7

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P1_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a2 a3 a4 a5 : Fin 8)
    (h12 : 4 <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 4 a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a2 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_4_4.cover a3 a4 a5 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_4_5.cover a3 a4 a5 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_4_6.cover a3 a4 a5 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K3.P1_4_7.cover a3 a4 a5 h23 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K2.P1_4
