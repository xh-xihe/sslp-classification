-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard072
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard073

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_3_4_4_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 4 4 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard072.canonicalBound_1167
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard073.canonicalBound_1168
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard073.canonicalBound_1169

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_3_4_4_5
