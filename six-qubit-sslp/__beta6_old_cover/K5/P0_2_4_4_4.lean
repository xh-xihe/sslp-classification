-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard039

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_4_4_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 4 4 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard039.canonicalBound_0631
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard039.canonicalBound_0632
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard039.canonicalBound_0633
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard039.canonicalBound_0634

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_4_4_4
