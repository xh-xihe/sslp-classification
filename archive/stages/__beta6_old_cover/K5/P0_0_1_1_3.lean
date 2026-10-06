-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_1_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 1 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0133
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0134
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0135
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0136
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard008.canonicalBound_0137

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_1_3
