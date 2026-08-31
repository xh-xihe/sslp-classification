-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard024
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard025

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_4_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 4 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard024.canonicalBound_0398
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard024.canonicalBound_0399
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard025.canonicalBound_0400

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_4_5
