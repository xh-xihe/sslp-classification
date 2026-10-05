-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_3_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0169
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0170
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0171
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0172
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0173

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_3_3
