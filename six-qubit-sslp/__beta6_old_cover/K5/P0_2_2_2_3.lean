-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_2_2_3

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 3 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 0 2 2 2 3 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0546
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0547
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0548
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0549
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard034.canonicalBound_0550

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P0_2_2_2_3
