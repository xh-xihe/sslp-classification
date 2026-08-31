-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_0_0

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 0 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 0 0 0 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0000
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0001
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0002
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0003
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0004
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0005
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0006
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard000.canonicalBound_0007

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_0_0_0
