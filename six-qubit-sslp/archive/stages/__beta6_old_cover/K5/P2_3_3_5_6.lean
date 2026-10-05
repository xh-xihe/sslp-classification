-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard088

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_3_3_5_6

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 3 3 5 6 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard088.canonicalBound_1408
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard088.canonicalBound_1409

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_3_3_5_6
