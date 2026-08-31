-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_2_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 2 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0148
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0149
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0150
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0151
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0152
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard009.canonicalBound_0153

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_2_2
