-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_3_3_3_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1128
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1129
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1130
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1131
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1132

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_3_3_3_3
