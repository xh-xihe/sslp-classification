-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard025
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_2_2_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard025.canonicalBound_0414
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard025.canonicalBound_0415
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026.canonicalBound_0416
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026.canonicalBound_0417
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026.canonicalBound_0418
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026.canonicalBound_0419

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_2_2_2
