-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_3_3_3_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 3 3 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1133
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1134
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard070.canonicalBound_1135
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard071.canonicalBound_1136

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_3_3_3_4
