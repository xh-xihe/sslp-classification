-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard066

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_3_3_6

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 3 6 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard066.canonicalBound_1070
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard066.canonicalBound_1071

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_3_3_6
