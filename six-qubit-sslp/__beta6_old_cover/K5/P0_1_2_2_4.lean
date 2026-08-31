-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_2_2_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 2 2 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026.canonicalBound_0425
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026.canonicalBound_0426
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026.canonicalBound_0427
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard026.canonicalBound_0428

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_2_2_4
