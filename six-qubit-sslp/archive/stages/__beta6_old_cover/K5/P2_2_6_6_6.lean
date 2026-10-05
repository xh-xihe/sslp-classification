-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_6_6_6

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 6 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 6 6 6 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1375
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard086.canonicalBound_1376

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_6_6_6
