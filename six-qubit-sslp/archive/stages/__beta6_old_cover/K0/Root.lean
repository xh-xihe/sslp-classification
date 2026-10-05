-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P0
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P1
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P2
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P3
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P4
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P5
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P6
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P7

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K0.Root

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a0 a1 a2 a3 a4 a5 : Fin 8)
    (h01 : a0.val <= a1.val)
    (h12 : a1.val <= a2.val)
    (h23 : a2.val <= a3.val)
    (h34 : a3.val <= a4.val)
    (h45 : a4.val <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 a0.val a1.val a2.val a3.val a4.val a5.val)) 9 := by
  fin_cases a0 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P0.cover a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P1.cover a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P2.cover a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P3.cover a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P4.cover a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P5.cover a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P6.cover a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
    | exact MainTheory.Generated.BinaryBetaSixKernel.Cover.K1.P7.cover a1 a2 a3 a4 a5 h01 h12 h23 h34 h45

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K0.Root
