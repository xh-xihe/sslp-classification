-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_1_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0343
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0344
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0345
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0346
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0347

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_1_3
