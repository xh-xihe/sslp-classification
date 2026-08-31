-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard067

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_3_4_4

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 4 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 4 4 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard067.canonicalBound_1073
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard067.canonicalBound_1074
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard067.canonicalBound_1075
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard067.canonicalBound_1076

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_3_4_4
