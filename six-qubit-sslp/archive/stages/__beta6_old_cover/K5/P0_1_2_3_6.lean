-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard027
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard028

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_2_3_6

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 3 6 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard027.canonicalBound_0447
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard028.canonicalBound_0448

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_2_3_6
