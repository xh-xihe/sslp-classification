-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_3_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0178
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0179
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0180

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_3_5
