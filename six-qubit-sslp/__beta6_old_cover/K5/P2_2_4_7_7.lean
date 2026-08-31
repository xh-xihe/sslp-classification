-- Generated proof-only `Fin 8` coverage node.
import MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085

namespace MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_4_7_7

open MainTheory.BinaryDetCircuit
open MainTheory.BinaryDetSymmetry
open MainTheory.OuterEnumeration

theorem cover (a5 : Fin 8)
    (h45 : 7 <= a5.val) :
    BottomDetBound
      (topOfPattern (R := ℤ) (angle6 2 2 4 7 7 a5.val)) 9 := by
  fin_cases a5 <;>
    first
    | omega
    | exact MainTheory.Generated.BinaryBetaSixKernel.Target.Shard085.canonicalBound_1364

end MainTheory.Generated.BinaryBetaSixKernel.Cover.K5.P2_2_4_7_7
