-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_2_4_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 4 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1290
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1291
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1292
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1293

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_2_4_4
