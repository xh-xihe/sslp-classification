-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_3_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 3 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0090
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0091
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0092
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0093

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_3_4
