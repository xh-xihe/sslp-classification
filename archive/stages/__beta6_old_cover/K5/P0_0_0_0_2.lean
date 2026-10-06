-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_0_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0015
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0016
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0017
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0018
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0019
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard001.canonicalBound_0020

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_0_2
