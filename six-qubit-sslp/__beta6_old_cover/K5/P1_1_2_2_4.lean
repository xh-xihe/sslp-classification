-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_2_2_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055.canonicalBound_0887
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055.canonicalBound_0888
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055.canonicalBound_0889
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055.canonicalBound_0890

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_2_2_4
