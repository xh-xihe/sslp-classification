-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard023

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_2_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 2 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0364
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0365
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0366
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard022.canonicalBound_0367
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard023.canonicalBound_0368

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_2_3
