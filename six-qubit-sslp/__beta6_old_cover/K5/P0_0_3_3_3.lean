-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard016

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_3_3_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 0 3 3 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard016.canonicalBound_0260
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard016.canonicalBound_0261
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard016.canonicalBound_0262
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard016.canonicalBound_0263
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard016.canonicalBound_0264

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_0_3_3_3
