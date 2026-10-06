-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_0_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0021
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0022
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0023
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0024
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0025

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_0_3
