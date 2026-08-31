-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_3_3_3_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 3 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1380
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1381
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1382
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1383
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1384

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_3_3_3_3
