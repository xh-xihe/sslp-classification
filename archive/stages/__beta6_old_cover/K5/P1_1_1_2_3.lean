-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard051

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_1_2_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 2 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard051.canonicalBound_0826
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard051.canonicalBound_0827
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard051.canonicalBound_0828
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard051.canonicalBound_0829
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard051.canonicalBound_0830

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_1_2_3
