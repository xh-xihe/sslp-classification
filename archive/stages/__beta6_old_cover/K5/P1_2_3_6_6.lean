-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_3_6_6

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 2 3 6 6 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1089
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard068.canonicalBound_1090

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_2_3_6_6
