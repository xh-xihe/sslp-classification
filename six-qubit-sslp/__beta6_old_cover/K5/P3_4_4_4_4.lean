-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard098

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_4_4_4_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 3 4 4 4 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard098.canonicalBound_1576
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard098.canonicalBound_1577
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard098.canonicalBound_1578
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard098.canonicalBound_1579

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P3_4_4_4_4
