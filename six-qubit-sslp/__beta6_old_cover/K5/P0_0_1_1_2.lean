-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_1_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard007.canonicalBound_0127
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0128
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0129
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0130
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0131
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0132

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_1_2
