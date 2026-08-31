-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard052

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_1_2_7

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 7 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard052.canonicalBound_0840

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_1_2_7
