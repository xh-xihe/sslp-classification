-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_2_3_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 2 3 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1284
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1285
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard080.canonicalBound_1286

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_2_3_5
