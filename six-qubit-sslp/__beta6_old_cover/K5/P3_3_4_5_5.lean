-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard096
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard097

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_3_4_5_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 5 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard096.canonicalBound_1551
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard097.canonicalBound_1552
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard097.canonicalBound_1553

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_3_4_5_5
