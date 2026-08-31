-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_3_3_3_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 3 3 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094.canonicalBound_1511
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094.canonicalBound_1512
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094.canonicalBound_1513
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard094.canonicalBound_1514

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_3_3_3_4
