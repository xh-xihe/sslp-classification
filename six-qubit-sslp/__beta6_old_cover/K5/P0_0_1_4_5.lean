-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_4_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 1 4 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0188
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0189
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard011.canonicalBound_0190

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_1_4_5
