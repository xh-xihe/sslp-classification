-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard029

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_3_3_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 3 3 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard029.canonicalBound_0470
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard029.canonicalBound_0471
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard029.canonicalBound_0472
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard029.canonicalBound_0473
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard029.canonicalBound_0474

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_3_3_3
