-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_2_2_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055.canonicalBound_0882
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055.canonicalBound_0883
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055.canonicalBound_0884
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055.canonicalBound_0885
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055.canonicalBound_0886

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_2_2_3
