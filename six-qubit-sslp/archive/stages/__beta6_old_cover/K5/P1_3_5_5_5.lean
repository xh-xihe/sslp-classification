-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard073
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard074

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_3_5_5_5

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 5 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 1 3 5 5 5 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard073.canonicalBound_1183
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard074.canonicalBound_1184
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard074.canonicalBound_1185

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P1_3_5_5_5
