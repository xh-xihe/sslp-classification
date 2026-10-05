-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard050

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_1_1_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 1 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard049.canonicalBound_0799
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard050.canonicalBound_0800
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard050.canonicalBound_0801
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard050.canonicalBound_0802
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard050.canonicalBound_0803
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard050.canonicalBound_0804

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_1_1_2
