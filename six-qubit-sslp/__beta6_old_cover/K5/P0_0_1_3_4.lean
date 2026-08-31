-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_3_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 3 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0174
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard010.canonicalBound_0175
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0176
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0177

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_3_4
