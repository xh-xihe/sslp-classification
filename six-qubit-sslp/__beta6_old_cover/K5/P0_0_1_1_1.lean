-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_1_1

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 1 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 1 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0120
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0121
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0122
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0123
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0124
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0125
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0126

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_1_1
