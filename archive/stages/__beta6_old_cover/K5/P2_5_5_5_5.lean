-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard092

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_5_5_5_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 5 5 5 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard092.canonicalBound_1485
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard092.canonicalBound_1486
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard092.canonicalBound_1487

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_5_5_5_5
