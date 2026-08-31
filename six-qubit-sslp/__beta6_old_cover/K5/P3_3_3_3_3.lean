-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_3_3_3_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094.canonicalBound_1506
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094.canonicalBound_1507
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094.canonicalBound_1508
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094.canonicalBound_1509
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094.canonicalBound_1510

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_3_3_3_3
