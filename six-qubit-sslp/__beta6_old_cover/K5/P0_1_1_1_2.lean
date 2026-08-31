-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_1_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 1 1 1 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0337
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0338
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0339
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0340
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0341
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard021.canonicalBound_0342

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_1_1_1_2
