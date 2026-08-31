-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_2_2_2

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 2 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 2 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0540
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0541
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0542
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard033.canonicalBound_0543
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0544
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0545

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_2_2_2
