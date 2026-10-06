-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard052

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_1_3_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 1 1 3 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard052.canonicalBound_0841
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard052.canonicalBound_0842
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard052.canonicalBound_0843
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard052.canonicalBound_0844
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard052.canonicalBound_0845

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_1_1_3_3
