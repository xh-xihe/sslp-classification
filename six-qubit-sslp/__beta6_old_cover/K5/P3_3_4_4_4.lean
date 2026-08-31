-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard096

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_3_4_4_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 3 4 4 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard096.canonicalBound_1541
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard096.canonicalBound_1542
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard096.canonicalBound_1543
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard096.canonicalBound_1544

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_3_4_4_4
