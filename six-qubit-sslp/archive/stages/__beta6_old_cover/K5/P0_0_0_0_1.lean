-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_0_1

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 1 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 1 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0008
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0009
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0010
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0011
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0012
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0013
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0014

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_0_1
