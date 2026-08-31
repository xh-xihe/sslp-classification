-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_2_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 2 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard004.canonicalBound_0079
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0080
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard005.canonicalBound_0081

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_2_5
