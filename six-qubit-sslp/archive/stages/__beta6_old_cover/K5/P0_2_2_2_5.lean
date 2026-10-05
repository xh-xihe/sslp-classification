-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_2_2_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0555
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0556
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0557

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_2_2_5
