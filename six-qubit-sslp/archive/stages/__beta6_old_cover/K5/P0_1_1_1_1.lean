-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_1_1

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 1 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 1 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0330
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0331
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0332
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0333
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0334
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard020.canonicalBound_0335
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0336

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_1_1
