-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard054
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_2_2_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 2 2 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard054.canonicalBound_0876
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard054.canonicalBound_0877
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard054.canonicalBound_0878
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard054.canonicalBound_0879
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055.canonicalBound_0880
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard055.canonicalBound_0881

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_2_2_2
