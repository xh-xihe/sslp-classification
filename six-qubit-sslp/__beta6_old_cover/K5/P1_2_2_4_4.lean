-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard064
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard065

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_2_4_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 2 4 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard064.canonicalBound_1038
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard064.canonicalBound_1039
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard065.canonicalBound_1040
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard065.canonicalBound_1041

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_2_4_4
