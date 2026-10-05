-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_4_4_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 4 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1345
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1346
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1347
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard084.canonicalBound_1348

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_4_4_4
